use super::*;

#[test]
fn unsigned_widening_special_certificates_expand_and_recheck() {
    let (source, _) =
        mdtest_sources("mdtests/unsigned_widening_keeps_special_certificate_results.md");
    for label in [
        "positive_is_nonzero.ensures_0",
        "widened_positive_is_unequal_to_zero.ensures_0",
    ] {
        let expanded = expand_c0_claim_source_by_label(&source, &[], label).unwrap();
        without_implicit_auto(|| verify_click_theorems(&expanded)).unwrap();
    }
    // x = 0 satisfies the weakened bound and refutes both conclusions.
    let false_claim = source.replace("1 <= to_integer", "0 <= to_integer");
    assert!(verify_click_theorems(&false_claim).is_err());
}

#[test]
#[ignore = "nightly: verifies the original descriptor proof and its rejection controls"]
fn borrowed_resource_receipts_survive_post_return_folds() {
    let (source, sources) =
        mdtest_sources("mdtests/unfold_region_then_write_a_descriptor_of_its_type.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&source, &sources)
        .expect("all borrowed resources must survive the checked post-return folds");

    let missing_owner = source.replacen("owns *other;", "", 1);
    assert_ne!(missing_owner, source);
    assert!(verify_c0_sources(&missing_owner, &sources).is_err());

    let false_result = source.replacen(
        "owns *other;",
        "owns *other;\n    ensures result != result;",
        1,
    );
    assert_ne!(false_result, source);
    assert!(verify_c0_sources(&false_result, &sources).is_err());
}

#[test]
fn borrowed_resource_receipts_do_not_hide_an_unspent_authority_member() {
    let (source, sources) =
        mdtest_sources("mdtests/authority_helper_raw_consume_without_spend_rejected.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let error = verify_c0_sources(&source, &sources)
        .expect_err("returning the borrowed authority does not establish the declared spend");
    assert!(
        error.to_string().contains("Requires consumes ticket(p)"),
        "{error}"
    );
}

#[test]
#[ignore = "nightly: generated 256-clause outcome proof and expansion controls"]
fn outcome_arithmetic_is_independent_of_postcondition_count() {
    let c_source = "int32 caller(int32 x) { return x; }";
    let sources = [("many.c", c_source)];
    let source = |count| {
        let clauses = (0..count)
            .map(|index| format!("ensures result >= x - {index};"))
            .collect::<Vec<_>>()
            .join("\n");
        format!(
            "verifying \"many.c\";\nint32 caller(int32 x) {{\nrequires 0 <= x;\nrequires x <= 1000;\n{clauses}\n}} by {{ step(); simp(); }}"
        )
    };
    for count in [4, 64, 256] {
        verify_c0_sources(&source(count), &sources).unwrap();
    }
    let expanded =
        expand_c0_claim_source(&source(4), &sources, "caller", CProofClaim::Grouped).unwrap();
    without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
    let false_source = source(64).replace("result >= x - 63", "result >= x + 1");
    assert!(verify_c0_sources(&false_source, &sources).is_err());
    let false_expansion = expanded.replacen("result >= x - 3", "result >= x + 1", 1);
    assert_ne!(false_expansion, expanded);
    assert!(verify_c0_sources(&false_expansion, &sources).is_err());
}

#[test]
fn uint64_measure_induction_expands_and_rechecks_without_narrowing() {
    let (source, _) = mdtest_sources("mdtests/uint64_measure_induction_counts_a_range_fold.md");
    let expanded =
        expand_c0_claim_source_by_label(&source, &[], "full_width_count_is_its_length.ensures_0")
            .unwrap();
    verify_click_theorems(&expanded).unwrap();
    let false_result = expanded.replacen(
        "ensures full_width_count(n) == to_integer(n)",
        "ensures full_width_count(n) == to_integer(n) + 1",
        1,
    );
    assert_ne!(false_result, expanded);
    assert!(verify_click_theorems(&false_result).is_err());
}

#[test]
fn scalar_induction_keeps_integer_parameters_and_their_guards() {
    let (source, _) = mdtest_sources("mdtests/scalar_induction_keeps_fixed_integer_parameters.md");
    let expanded = expand_c0_claim_source_by_label(
        &source,
        &[],
        "carry_seed_returns_the_same_integer.ensures_0",
    )
    .unwrap();
    verify_click_theorems(&expanded).unwrap();
    let start = expanded.find("apply(ih(").unwrap();
    let end = start + expanded[start..].find("};").unwrap() + 2;
    let application = &expanded[start..end];
    assert!(application.contains("0 < seed;"), "{expanded}");
    let missing_guard = format!(
        "{}{}{}",
        &expanded[..start],
        application.replace("0 < seed;", ""),
        &expanded[end..],
    );
    assert!(verify_click_theorems(&missing_guard).is_err());
    let wrong_result = source.replacen(
        "ensures carry_seed(n, seed) == seed",
        "ensures carry_seed(n, seed) == seed + 1",
        1,
    );
    assert_ne!(wrong_result, source);
    assert!(verify_click_theorems(&wrong_result).is_err());
}

#[test]
fn arithmetic_after_fold_rewrites_expands_and_rechecks() {
    let (source, _) = mdtest_sources("mdtests/pure_arithmetic_retains_a_rewritten_fold_goal.md");
    let position = expansion::position_at_offset(&source, source.rfind("arithmetic()").unwrap());
    let expanded =
        expand_c0_tactic_source_at(&source, &[], position.line, position.column).unwrap();
    assert!(expanded.contains("arithmetic_certificate"), "{expanded}");
    verify_click_theorems(&expanded).unwrap();
    let invalid = expanded.replacen(
        "ensures full_width_count(n) == to_integer(n)",
        "ensures full_width_count(n) == to_integer(n) + 1",
        1,
    );
    assert_ne!(invalid, expanded);
    assert!(verify_click_theorems(&invalid).is_err());
}

#[test]
fn pointer_word_certificates_keep_address_arithmetic_when_printed() {
    let (source, _) = mdtest_sources(
        "mdtests/address_arithmetic_keeps_its_c_meaning_under_integer_arithmetic.md",
    );
    verify_click_theorems(&source).unwrap();
    let expanded =
        expand_c0_claim_source_by_label(&source, &[], "packed_parent.ensures_0").unwrap();
    without_implicit_auto(|| verify_click_theorems(&expanded))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    let missing_alignment = expanded.replace("requires aligned(p, 8);", "");
    assert_ne!(missing_alignment, expanded);
    assert!(verify_click_theorems(&missing_alignment).is_err());
    let false_result = expanded.replacen(
        "ensures ((word & 1) | address(p)) == address(p) +",
        "ensures ((word & 1) | address(p)) == 1 + address(p) +",
        1,
    );
    assert_ne!(false_result, expanded);
    assert!(verify_click_theorems(&false_result).is_err());
}

#[test]
fn numeric_cast_certificates_keep_integer_default_arithmetic_when_printed() {
    let source = r#"arithmetic "integer";
theorem numeric_cast(word: uint64) {
    ensures ((uint64)word) + 1 > ((uint64)word) by { arithmetic(); }
}"#;
    let expanded = expand_c0_claim_source_by_label(source, &[], "numeric_cast.ensures_0").unwrap();
    without_implicit_auto(|| verify_click_theorems(&expanded))
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
fn bundle_and_project_expansion_check_the_selected_pure_theorem() {
    let source = r#"theorem selected(x: int32) {
    ensures x == x by { normalize(); }
}
theorem unrelated() {
    ensures 0 == 1 by { normalize(); }
}
"#;
    let position = expansion::position_at_offset(source, source.find("ensures x == x").unwrap());
    verify_c0_sources_at(source, &[], position.line, position.column).unwrap();
    let bundled = expand_c0_claim_source_by_label(source, &[], "selected.ensures_0").unwrap();
    let project = ClickProject::new(
        "proof.click",
        [ClickModuleSource::new("proof.click", source, [])],
    );
    let projected = expansion::expand_project_claim_source_by_label(
        &project,
        &ProgramInputs::Bundle(vec![]),
        "selected.ensures_0",
    )
    .unwrap();
    assert_eq!(bundled, projected);
    let position = expansion::position_at_offset(&bundled, bundled.find("ensures x == x").unwrap());
    verify_c0_sources_at(&bundled, &[], position.line, position.column).unwrap();
    assert!(verify_click_theorems(&bundled).is_err());

    let false_selected = source.replace("ensures x == x", "ensures x != x");
    let error = expand_c0_claim_source_by_label(&false_selected, &[], "selected.ensures_0")
        .expect_err("selection must still check the selected proof");
    assert!(error.message().contains("selected.ensures_0"), "{error}");
}

fn check_machine_integer_equality_chain(ty: &str) {
    let (source, _) =
        mdtest_sources("mdtests/unsigned_integer_equality_chain_keeps_its_reading.md");
    let source = source.replace("uint64", ty);
    let expanded =
        expand_c0_claim_source_by_label(&source, &[], "unsigned_equality_chain.ensures_0").unwrap();
    without_implicit_auto(|| verify_click_theorems(&expanded)).unwrap();
}

#[test]
fn unsigned_integer_equality_chains_expand_and_recheck() {
    check_machine_integer_equality_chain("uint64");
}

#[test]
fn signed_integer_equality_chains_expand_and_recheck() {
    check_machine_integer_equality_chain("int64");
}

#[test]
fn unsigned_int32_equality_chains_expand_and_recheck() {
    check_machine_integer_equality_chain("uint32");
}

#[test]
fn signed_int32_equality_chains_expand_and_recheck() {
    check_machine_integer_equality_chain("int32");
}

#[test]
fn special_integer_certificates_keep_native_premises_available() {
    let source = r#"import click::integer;
theorem native_premise(a: uint64, b: uint64) {
    requires to_integer(a) == to_integer(b);
    ensures (to_integer(a) + 1) * (to_integer(a) + 2) == to_integer(a) * (to_integer(a) + 1) + 2 * (to_integer(a) + 1) by {
        arithmetic_certificate rules {
            premise 0: to_integer(a) == to_integer(b) => to_integer(a) == to_integer(b);
            integer_polynomial_identity bounds [] => (to_integer(a) + 1) * (to_integer(a) + 2) == to_integer(a) * (to_integer(a) + 1) + 2 * (to_integer(a) + 1);
            conclusion 0;
        }
    }
}
"#;
    verify_click_theorems(source).unwrap();
    let false_identity = source.replace("+ 2 * (to_integer(a) + 1)", "+ 3 * (to_integer(a) + 1)");
    assert!(verify_click_theorems(&false_identity).is_err());
}

#[test]
fn integer_equality_does_not_identify_signed_and_unsigned_observations() {
    // seed = -1, adler = value = UINT64_MAX, specification = -1 satisfies
    // every premise and refutes the conclusion.
    let source = r#"import click::integer;
theorem mixed_observations(adler: uint64, seed: int64, value: uint64, specification: Integer) {
    requires to_integer(adler) == to_integer((uint64)seed);
    requires to_integer(adler) == to_integer(value);
    requires specification == to_integer(seed);
    ensures to_integer(value) == specification by {
        arithmetic() using {
            to_integer(adler) == to_integer((uint64)seed);
            to_integer(adler) == to_integer(value);
            specification == to_integer(seed);
        };
    }
}"#;
    assert!(verify_click_theorems(source).is_err());
}

fn check_member_pointer_address_expansion(fixture: &str, function: &str) {
    let (source, sources) = mdtest_sources(&format!("mdtests/{fixture}.md"));
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    // Expansion already verifies the input; independently check its output.
    let expanded =
        expand_c0_claim_source(&source, &sources, function, CProofClaim::Grouped).unwrap();
    without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
}

#[test]
fn member_pointer_addresses_retain_subobject_extents_through_expansion() {
    check_member_pointer_address_expansion("egraph_resource_pointer_load_alias", "check");
}

#[test]
fn member_pointer_addresses_with_equal_numeric_addresses_expand() {
    check_member_pointer_address_expansion("egraph_resource_pointer_load_same_address", "check");
}

#[test]
#[ignore = "nightly: 0.63s after reducing duplicate verification"]
fn nonzero_member_pointer_addresses_retain_subobject_extents_through_expansion() {
    check_member_pointer_address_expansion("model_pointer_alias_nonzero_field_load", "probe");
}

#[test]
fn record_pointer_identity_preserves_local_storage_in_all_proof_modes() {
    let (source, sources) =
        mdtest_sources("mdtests/c_record_pointer_identity_preserves_local_storage.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&source, &sources).unwrap();
    let expanded =
        expand_c0_claim_source(&source, &sources, "caller", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    let caller = source.find("int32 caller()").unwrap();
    let step = caller + source[caller..].find("execute();").unwrap();
    let at = expansion::position_at_offset(&source, step);
    let rewritten = expand_c0_tactic_source_at(&source, &sources, at.line, at.column).unwrap();
    verify_c0_sources(&rewritten, &sources).unwrap();
    let (session, _) = C0VerificationSession::new(&source, &sources).unwrap();
    for checked in [&expanded, &rewritten] {
        let caller = checked.find("int32 caller()").unwrap();
        let proof = caller + checked[caller..].find("by").unwrap();
        let body = proof + checked[proof..].find('{').unwrap() + 1;
        let first_step = body + checked[body..].find(|c: char| !c.is_whitespace()).unwrap();
        let at = expansion::position_at_offset(checked, first_step);
        session.verify_at(checked, at.line, at.column).unwrap();
    }
}

#[test]
fn record_pointer_identity_local_storage_keeps_values_and_alias_requirements() {
    let (source, sources) =
        mdtest_sources("mdtests/c_record_pointer_identity_preserves_local_storage.md");
    let c = &sources[0].1;
    let original = [("identity.c", c.as_str())];
    assert!(
        verify_c0_sources(
            &source.replace("ensures result == 7;", "ensures result == 8;"),
            &original
        )
        .is_err()
    );
    // A checked helper body does not export address equality unless its
    // contract states it. Mere existence of a local record grants no alias.
    assert!(verify_c0_sources(&source.replace("ensures result == pair;", ""), &original).is_err());
    // Ownership grants storage access, not initialization of an unwritten field.
    let uninitialized = c.replace(
        "struct Pair pair = { 7, 9 };",
        "struct Pair pair; pair.second = 9;",
    );
    assert!(verify_c0_sources(&source, &[("identity.c", uninitialized.as_str())]).is_err());
    // Nonzero member offsets use the same complete-object owner.
    let second = c.replace("return q->first;", "return q->second;");
    verify_c0_sources(
        &source.replace("ensures result == 7;", "ensures result == 9;"),
        &[("identity.c", second.as_str())],
    )
    .unwrap();
    let written = c.replace("return q->first;", "q->second = 11; return q->second;");
    verify_c0_sources(
        &source.replace("ensures result == 7;", "ensures result == 11;"),
        &[("identity.c", written.as_str())],
    )
    .unwrap();
}

#[test]
#[ignore = "nightly: pointer equality expansion and retained checks took 0.95s in parallel"]
fn shifted_pointer_equality_rewrites_expand_and_recheck() {
    let sources = [(
        "pointer.c",
        "int32 same_block(int32* base, int32* cursor, uint64 remaining) { return 0; }",
    )];
    let source = r#"
        verifying "pointer.c";
        int32 same_block(int32* base, int32* cursor, uint64 remaining) {
            requires ((int32)(uint32)remaining) == 4;
            requires cursor == base + (4 - ((int32)(uint32)remaining));
            ensures result == 0;
        } by {
            have cursor == base;
            execute(); simp();
        }
    "#;
    let verified_for_expansion = verify_c0_sources(source, &sources).unwrap();
    let expanded =
        expand_checked_grouped_claim(source, &verified_for_expansion, "same_block").unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    let at = expansion::position_at_offset(source, source.find("have cursor == base;").unwrap());
    let selected = expand_c0_tactic_source_at(source, &sources, at.line, at.column).unwrap();
    verify_c0_sources(&selected, &sources).unwrap();
    let (session, _) = C0VerificationSession::new(source, &sources).unwrap();
    for rewritten in [&expanded, &selected] {
        let proof = rewritten.find("by").unwrap();
        let body = proof + rewritten[proof..].find('{').unwrap() + 1;
        let first_step = body
            + rewritten[body..]
                .find(|c: char| !c.is_whitespace())
                .unwrap();
        let at = expansion::position_at_offset(rewritten, first_step);
        session.verify_at(rewritten, at.line, at.column).unwrap();
    }
}

#[test]
#[ignore = "nightly: static refold expansion and retained-session checks take 0.9s"]
fn static_return_refold_before_named_resource_rechecks_in_all_proof_modes() {
    let (source, sources) = mdtest_sources("mdtests/static_return_refold_before_named_resource.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let (session, verified_for_expansion) = C0VerificationSession::new(&source, &sources).unwrap();
    let expanded =
        expand_checked_grouped_claim(&source, &verified_for_expansion, "inspect").unwrap();
    let position =
        expansion::position_at_offset(&expanded, expanded.find("ensures tag.value").unwrap());

    session
        .verify_at(&expanded, position.line, position.column)
        .unwrap();
    drop(session);
    verify_c0_sources(&expanded, &sources).unwrap();

    let false_value = source.replace("ensures tag.value == 1;", "ensures tag.value == 2;");
    assert!(verify_c0_sources(&false_value, &sources).is_err());
    let unowned = source.replace("owns cell(p);", "views cell(p);");
    assert!(verify_c0_sources(&unowned, &sources).is_err());
}

#[test]
#[ignore = "nightly: checks two post-return unfolds through expansion and retained verification"]
fn call_produced_instances_unfold_after_return_in_all_proof_modes() {
    for fixture in [
        "mdtests/return_unfold_call_instance.md",
        "mdtests/return_unfold_call_instance_with_local.md",
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        let (session, verified_for_expansion) =
            C0VerificationSession::new(&source, &sources).unwrap();
        let expanded =
            expand_checked_grouped_claim(&source, &verified_for_expansion, "pick").unwrap();
        let position =
            expansion::position_at_offset(&expanded, expanded.find("ensures o.model").unwrap());

        session
            .verify_at(&expanded, position.line, position.column)
            .unwrap();
        drop(session);
        verify_expanded_function_source(&source, &expanded, &sources, "pick").unwrap();

        let false_frame = source.replace(
            "ensures o.model == 0;",
            "ensures o.model == 0; ensures r->top == old(r->top);",
        );
        assert!(verify_c0_sources(&false_frame, &sources).is_err());
    }
}

#[test]
fn execution_theorem_expansion_preserves_imported_tactic_interfaces() {
    let helper = include_str!("../../../mdtests/execution_theorem_imported_tactic_helpers.click");
    let fixture = crate::cli::parse_mdtest(
        std::path::Path::new("execution_theorem_imported_tactic.md"),
        include_str!("../../../mdtests/execution_theorem_imported_tactic.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(helper, &[]).expect("the provider's body is checked separately");
    let project = |source: &str| {
        ClickProject::new(
            "caller.click",
            [
                ClickModuleSource::new(
                    "caller.click",
                    source,
                    ["execution_theorem_imported_tactic_helpers.click".to_string()],
                ),
                ClickModuleSource::new(
                    "execution_theorem_imported_tactic_helpers.click",
                    helper,
                    [],
                ),
            ],
        )
    };
    verify_c0_project(&project(source), &c_sources).expect("ordinary caller verification");
    let position = expansion::position_at_offset(source, source.rfind("simp();").unwrap());
    let expanded = expand_project_tactic_source_at(
        &project(source),
        &ProgramInputs::Bundle(c_sources.clone()),
        position.line,
        position.column,
    )
    .expect("theorem-only expansion retains imported tactic interfaces");
    assert!(!expanded[expanded.find("theorem zero_contract").unwrap()..].contains("simp();"));
    verify_c0_project(&project(&expanded), &c_sources).expect("the expansion checks directly");
    let local = source.replace(
        "import \"execution_theorem_imported_tactic_helpers.click\";",
        helper,
    );
    let position = expansion::position_at_offset(&local, local.rfind("simp();").unwrap());
    let expanded = expand_c0_tactic_source_at(&local, &c_sources, position.line, position.column)
        .expect("the non-project theorem route retains local unselected tactic interfaces");
    verify_c0_sources(&expanded, &c_sources).expect("local procedure expansion checks");
}

#[test]
fn long_flat_integer_sum_expands_and_rechecks_without_parenthesis_growth() {
    let sum = std::iter::repeat_n("a", 24).collect::<Vec<_>>().join(" + ");
    let source = format!(
        "theorem sum(a: Integer) {{ ensures {sum} == 24 * a by {{ have {sum} == 24 * a by {{ arithmetic(); }} assumption(); }} }}"
    );
    verify_click_theorems(&source).unwrap();
    let position = expansion::position_at_offset(&source, source.find("arithmetic()").unwrap());
    let expanded =
        expand_c0_tactic_source_at(&source, &[], position.line, position.column).unwrap();
    assert!(!expanded.contains("arithmetic()"), "{expanded}");
    let certificate = expanded.split("arithmetic_certificate {").nth(1).unwrap();
    let body = certificate.split('}').next().unwrap();
    assert!(body.lines().all(|line| line.len() <= 100), "{expanded}");
    verify_click_theorems(&expanded).unwrap();
}

#[test]
#[ignore = "nightly: rechecks vector tactic and whole-proof certificates"]
fn vector_field_input_pointer_certificates_round_trip() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("tests/fixtures/proof-expansion/vector-field-input.md");
    let markdown = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
    let name = "composite_resource_vector_fill_loop_snapshot";
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(file, source)| (file.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    // Expand the affected `have` before any verification has initialized
    // this function's universal inputs. Its naming scope is entered first.
    let position =
        expansion::position_at_offset(source, source.find("have i < owner->cap;").unwrap());
    let expanded =
        expand_c0_tactic_source_at(source, &sources, position.line, position.column).unwrap();
    // An unchanged input can print directly as `owner`; the cold recheck
    // must resolve it without requiring one particular snapshot spelling.
    assert!(!expanded.contains("have i < owner->cap;"), "{expanded}");
    assert!(!expanded.contains("the pointer value at this program point"));
    verify_c0_sources(&expanded, &sources).unwrap();
    let false_bound = expanded.replacen("have i < owner->cap by {", "have i < 0 by {", 1);
    assert_ne!(false_bound, expanded);
    verify_c0_sources(&false_bound, &sources)
        .expect_err("the expanded bound proof must not establish a false bound");
    let expanded = expand_c0_claim_source(source, &sources, name, CProofClaim::Grouped).unwrap();
    assert!(!expanded.contains("the pointer value at this program point"));
    assert!(
        c0_smart_tactic_source_sites(&expanded, &sources)
            .unwrap()
            .is_empty()
    );
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
fn builtin_header_null_pointer_expansion_round_trips() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/c_builtin_string_and_stdlib_headers.md");
    let markdown = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded =
        expand_c0_claim_source(source, &sources, "copy_pair", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
}

// A synthesized read through a struct-pointer field must keep the scalar
// stride when printed; `p->kid[1]` would advance by an entire child record.
#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn struct_pointer_field_scalar_read_expansion_keeps_its_width() {
    let c = r#"
        struct child { int32 refs; int32 payload; };
        struct parent { struct child* kid; };
        void put(struct parent* p, struct child* kid) { p->kid = kid; }
        int32 read(struct parent* p) {
            struct child* kid = p->kid;
            return kid->payload;
        }
        int32 caller(struct parent* p, struct child* kid) {
            put(p, kid);
            int32 observed = read(p);
            return observed;
        }
    "#;
    let source = r#"
        verifying "read.c";
        void put(struct parent* p, struct child* kid) {
            owns p->kid;
            ensures p->kid == kid;
        } by { execute(); simp(); }
        int32 read(struct parent* p) {
            views p->kid;
            views p->kid->payload;
            ensures result == p->kid->payload;
        } by { execute(); simp(); }
        int32 caller(struct parent* p, struct child* kid) {
            owns p->kid;
            views kid->payload;
            ensures result == kid->payload;
        } by {
            step(put(p, kid), {});
            step();
            step(read(p), {});
            have p->kid == kid;
            have observed == kid->payload;
            execute();
            simp();
        }
    "#;
    let sources = [("read.c", c)];
    let expanded = expand_c0_claim_source(source, &sources, "caller", CProofClaim::Grouped)
        .expect("the scalar read should expand through a byte address");
    assert!(expanded.contains("load_int32("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the printed read must retain its four-byte offset");
}

// Whole-claim expansion must print hidden record ownership and fold inputs
// in the syntax the author can write, then independently verify them.
#[test]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn hidden_record_resource_expansion_round_trips() {
    for name in [
        "a_hidden_record_resource_is_held_without_a_name",
        "a_hidden_record_resource_passes_through_a_call",
        "a_resource_without_fields_names_a_child_with_fields",
    ] {
        let path =
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(format!("mdtests/{name}.md"));
        let markdown = std::fs::read_to_string(&path).unwrap();
        let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
        let source = fixture.click_source.as_deref().unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let expanded = expand_c0_claim_source(source, &sources, "get", CProofClaim::Grouped)
            .unwrap_or_else(|error| panic!("{name}: {error:?}"));
        verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| panic!("{name}: {error:?}"));
    }
}

// A fold of a resource without fields sets a hidden record that has no
// source syntax; expansion shows it as a trailing comment, and the output
// still parses and verifies.
#[test]
fn expansion_shows_a_folds_hidden_record_as_a_comment() {
    let c = "struct cell { int32 value; }; struct pair { struct cell* a; int32 n; }; \
             int32 get(struct pair* p) { return p->n; }";
    let source = "resource counted(c: struct cell*) { field v: int32; owns c->value; fact c->value == v; } \
                  resource pair(p: struct pair*) { owns p->a; owns p->n; owns first: counted(p->a); \
                  fact p->n == first.v; fact first.v >= 0; } \
                  verifying \"f.c\"; int32 get(struct pair* p) { owns pair(p); ensures result >= 0; } by { \
                  let { first: c } = unfold(pair(p)); execute(); fold(pair(p), { first: c }); simp(); }";
    let sources = [("f.c", c)];
    let expanded = expand_c0_claim_source(source, &sources, "get", CProofClaim::Grouped)
        .expect("the hidden-record proof expands");
    assert!(
        expanded.contains("fold(pair(p), { first: c }); // record { first.v: c.v }"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources).expect("the commented expansion verifies");
}

// The reconstruction rule must survive checked tactic expansion and retained
// verification, rather than working only during ordinary execution search.
#[test]
fn byte_initialized_uint32_expands_and_retains() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/byte_representation_initializes_declared_uint32.md");
    let markdown = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &sources).unwrap();
    let position = expansion::position_at_offset(source, source.find("execute();").unwrap());
    let expanded =
        expand_c0_tactic_source_at(source, &sources, position.line, position.column).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
    let claim = expansion::position_at_offset(&expanded, expanded.find("ensures result").unwrap());
    let (session, _) = C0VerificationSession::new(source, &sources).unwrap();
    session
        .verify_at(&expanded, claim.line, claim.column)
        .unwrap();
    verify_c0_sources(&expanded.replace("4293820433u32", "17u32"), &sources)
        .expect_err("a single stored byte is not the reconstructed word");
}

#[test]
fn selected_tactic_batch_uses_the_project_entry_scope() {
    let c = [("identity.c", "int32 identity(int32 x) { return x; }")];
    let source = "verifying \"identity.c\"; int32 identity(int32 x) { ensures result == x; } by { execute(); have x == x by simp(); have x + 0 == x by simp(); simp(); }";
    let project = ClickProject::new(
        "unit.click",
        [ClickModuleSource::new("unit.click", source, [])],
    );
    let sites =
        project_smart_tactic_source_sites(&project, &ProgramInputs::Bundle(c.to_vec())).unwrap();
    let positions = sites[1..3]
        .iter()
        .map(|site| site.position.clone())
        .collect::<Vec<_>>();
    let expanded =
        expand_project_tactics_source_at(&project, &ProgramInputs::Bundle(c.to_vec()), &positions)
            .unwrap();
    assert!(expanded.source.contains("execute();"));
    verify_c0_project(&project.with_entry_source(expanded.source), &c).unwrap();
}

#[test]
fn selected_tactic_batch_removes_all_sites_in_a_dropped_arm() {
    let c = [(
        "flag.c",
        "int32 flag(int32 x) { if (x > 0) { return 1; } return 0; }",
    )];
    let source = "verifying \"flag.c\"; int32 flag(int32 x) { requires x <= 0; ensures result == 0; } by { branch { step(); simp(); simp(); } else {} step(); simp(); }";
    verify_c0_sources(source, &c).unwrap();
    let sites = c0_smart_tactic_source_sites(source, &c).unwrap();
    let positions = sites[..2]
        .iter()
        .map(|site| site.position.clone())
        .collect::<Vec<_>>();
    let expanded = expand_c0_tactics_source_at(source, &c, &positions).unwrap();
    assert!(!expanded.source.contains("step(); simp(); simp();"));
    assert!(expanded.source.ends_with("step(); simp(); }"));
    verify_c0_sources(&expanded.source, &c).unwrap();
}

#[test]
fn selected_tactic_batch_captures_multiple_sites_inside_one_have() {
    let c = [("identity.c", "int32 identity(int32 x) { return x; }")];
    let source = "verifying \"identity.c\";\nint32 identity(int32 x) { ensures result == x; } by {\nexecute();\nhave x == x by { have x == x by { simp(); } simp(); }\nsimp();\n}\n";
    verify_c0_sources(source, &c).unwrap();
    let sites = c0_smart_tactic_source_sites(source, &c).unwrap();
    let positions = sites[1..3]
        .iter()
        .map(|site| site.position.clone())
        .collect::<Vec<_>>();
    assert_eq!(sites[1].source_index, sites[2].source_index);
    let expanded = expand_c0_tactics_source_at(source, &c, &positions).unwrap();
    assert!(expanded.source.contains("execute();"));
    assert!(expanded.source.ends_with("simp();\n}\n"));
    verify_c0_sources(&expanded.source, &c).unwrap();
}

#[test]
#[ignore = "nightly: 2.5s in the parallel gate"]
fn selected_tactic_batch_preserves_checked_loop_and_branch_routing() {
    for relative in [
        "mdtests/loop_after_proof_branch_expands.md",
        "mdtests/a_ranked_loop_with_no_invariant_closes_a_branching_body.md",
        "mdtests/bubble_sort3_loop_sorted.md",
        "mdtests/loop_return_closes_in_preserve_arm.md",
    ] {
        let (source, c) = mdtest_sources(relative);
        let c = c
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        verify_c0_sources(&source, &c).unwrap();
        let sites = c0_smart_tactic_source_sites(&source, &c).unwrap();
        let claim = sites
            .iter()
            .find(|site| {
                sites
                    .iter()
                    .filter(|other| other.claim_label == site.claim_label)
                    .count()
                    > 1
            })
            .unwrap();
        let positions = sites
            .iter()
            .filter(|site| site.claim_label == claim.claim_label)
            .map(|site| site.position.clone())
            .collect::<Vec<_>>();
        let expanded = expand_c0_tactics_source_at(&source, &c, &positions)
            .unwrap_or_else(|error| panic!("{relative}: {error:?}"));
        verify_c0_sources(&expanded.source, &c)
            .unwrap_or_else(|error| panic!("{relative}: {error:?}\n{}", expanded.source));
    }
}

#[test]
fn selected_tactic_batch_retains_the_unselected_prefix_and_suffix() {
    let c = [("identity.c", "int32 identity(int32 x) { return x; }")];
    let source = "verifying \"identity.c\";\nint32 identity(int32 x) { ensures result == x; } by {\nexecute();\nhave x == x by simp();\nhave x + 0 == x by simp();\nhave x - 0 == x by simp();\nsimp();\n}\n";
    verify_c0_sources(source, &c).unwrap();
    let sites = c0_smart_tactic_source_sites(source, &c).unwrap();
    let selected = sites[1..3]
        .iter()
        .map(|s| s.position.clone())
        .collect::<Vec<_>>();
    let expanded = expand_c0_tactics_source_at(source, &c, &selected).unwrap();
    assert!(expanded.source.contains("execute();"));
    assert!(expanded.source.contains("have x - 0 == x by simp();"));
    assert!(
        !expanded.source.contains("have x == x by simp();"),
        "{}",
        expanded.source
    );
    assert!(
        !expanded.source.contains("have x + 0 == x by simp();"),
        "{}",
        expanded.source
    );
    verify_c0_sources(&expanded.source, &c).unwrap();
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn post_execution_have_expansion_preserves_later_smart_proofs() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/bubble_sort3_loop_sorted.md");
    let markdown = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &sources).unwrap();
    for needle in [
        "have p[0] <= p[1] by simp();",
        "have p[1] <= p[2] by simp();",
    ] {
        let offset = source.find(needle).unwrap();
        let position = expansion::position_at_offset(source, offset);
        let expanded = expand_c0_tactic_source_at(source, &sources, position.line, position.column)
            .unwrap_or_else(|error| panic!("{needle}: {error:?}"));
        assert!(!expanded.contains(needle), "{expanded}");
        assert!(
            expanded.ends_with(&source[offset + needle.len()..]),
            "the unselected suffix stays written: {expanded}"
        );
        assert_eq!(
            expanded.matches("if ").count(),
            source.matches("if ").count()
        );
        verify_c0_sources(&expanded, &sources).unwrap();
        let claim =
            expansion::position_at_offset(&expanded, expanded.find("ensures sorted:").unwrap());
        verify_c0_sources_at(&expanded, &sources, claim.line, claim.column).unwrap();
        let (session, _) = C0VerificationSession::new(source, &sources).unwrap();
        session
            .verify_at(&expanded, claim.line, claim.column)
            .unwrap();
        let false_claim = expanded.replace(
            "ensures sorted: sorted(p, 3)",
            "ensures sorted: p[0] > p[1]",
        );
        verify_c0_sources(&false_claim, &sources)
            .expect_err("a sorted result cannot have its first cells in strict descending order");
    }
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn an_arms_invariant_closer_expands_with_that_arms_checked_body() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/c_decreases_recursive_in_loop.md");
    let markdown = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &sources).unwrap();
    let position =
        expansion::position_at_offset(source, source.find("close_invariants();").unwrap());
    let expanded = expand_c0_tactic_source_at(source, &sources, position.line, position.column)
        .expect("the first arm's closer expands with that arm's checked body");
    // Each arm of the proof `if` closes the invariants itself: the arms end
    // in different states, so nothing after the `if` is shared. Expanding
    // the first arm's closer leaves the other arm's as written.
    assert_eq!(
        expanded.matches("close_invariants();").count(),
        1,
        "{expanded}"
    );
    assert_eq!(
        expanded.matches("close_invariants() by").count(),
        1,
        "{expanded}"
    );
    assert_eq!(expanded.matches("if n > 0").count(), 1, "{expanded}");
    assert!(expanded.contains("initialize by simp();"), "{expanded}");
    assert!(
        expanded.contains("    step();\n    simp();\n}"),
        "the phase's unselected successor stays written: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap();
    let claim = expansion::position_at_offset(&expanded, expanded.find("ensures result").unwrap());
    verify_c0_sources_at(&expanded, &sources, claim.line, claim.column).unwrap();
    let (session, _) = C0VerificationSession::new(source, &sources).unwrap();
    session
        .verify_at(&expanded, claim.line, claim.column)
        .unwrap();
    verify_c0_sources(
        &expanded.replace("ensures result == 0", "ensures result == 1"),
        &sources,
    )
    .expect_err("the expansion must still reject a false result claim");
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn repeated_loop_guard_closer_expands_at_original_execution_leaves() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/bubble_sort3_loop_permutation.md");
    let markdown = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
    let source_with_suffix = fixture.click_source.as_deref().unwrap().replace(
        "        simp();",
        "        simp();\n        have 0 == 0 by { normalize(); }",
    );
    let source = source_with_suffix.as_str();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &sources).unwrap();
    let position = expansion::position_at_offset(source, source.rfind("simp();").unwrap());
    let expanded =
        expand_c0_tactic_source_at(source, &sources, position.line, position.column).unwrap();
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(
        expanded.contains("have 0 == 0 by { normalize(); }"),
        "the unselected suffix stays written"
    );
    assert_eq!(
        expanded.matches("if ").count(),
        source.matches("if ").count()
    );
    verify_c0_sources(&expanded, &sources).unwrap();
    let claim =
        expansion::position_at_offset(&expanded, expanded.find("ensures permutation:").unwrap());
    verify_c0_sources_at(&expanded, &sources, claim.line, claim.column).unwrap();
    let (session, _) = C0VerificationSession::new(source, &sources).unwrap();
    session
        .verify_at(&expanded, claim.line, claim.column)
        .unwrap();
    let false_claim = expanded.replace(
        "permutation(p, old(p), 0, 3)",
        "permutation(p, old(p), 0, 2)",
    );
    verify_c0_sources(&false_claim, &sources)
        .expect_err("sorting three cells does not preserve just the first two cells");
}

fn assert_no_legacy_arithmetic_leaves(certificate: &ProofCertificate) {
    assert!(
        !certificate.contains_arithmetic_using(),
        "expanded certificate retained source-only ArithmeticUsing: {certificate:?}"
    );
}

fn assert_no_legacy_c_arithmetic_leaves(verified: &[VerifiedCTheorem]) {
    for theorem in verified {
        assert_no_legacy_arithmetic_leaves(
            &theorem
                .expanded_proof_certificate()
                .expect("verified C claim should retain an expansion certificate"),
        );
    }
}

fn assert_no_legacy_pure_arithmetic_leaves(verified: &[VerifiedPureTheorem]) {
    for theorem in verified {
        assert_no_legacy_arithmetic_leaves(
            &theorem
                .proof_certificate()
                .expect("verified pure theorem should retain a certificate"),
        );
    }
}

#[test]
fn arithmetic_using_is_input_only_and_not_serializable_provenance() {
    let source = ProofCertificate::from_proof_tactics(&[ProofTactic::ArithmeticUsing(vec![])])
        .expect("the source smart request remains a valid input tactic");
    assert!(source.contains_arithmetic_using());
    assert!(ProofCertificate::from_steps(source.steps().to_vec()).is_err());
}

#[test]
fn source_backed_call_requirement_expands_and_reverifies() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/call_precondition_disjunction_is_an_obligation.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = r#"
verifying "either.c";

extern int32 either_positive(int32 x, int32 y) {
    requires x > 0 or y > 0;
    ensures result == 0;
}

int32 caller(int32 x, int32 y) {
    requires x > 0;
    ensures result == 0 by { execute(); }
}
"#;
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(click_source, &c_sources)
        .expect("source-backed call requirement should verify");
    let expanded =
        expand_c0_claim_source(click_source, &c_sources, "caller", CProofClaim::Ensure(0))
            .expect("source-backed call requirement should expand");
    assert!(!expanded.contains("have x > 0 or y > 0 by"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources)
        .expect("expanded direct call requirement should reverify");

    let without_premise = expanded.replace("    requires x > 0;", "");
    let (result, planning_transitions) =
        count_planning_statement_transitions(|| verify_c0_sources(&without_premise, &c_sources));
    let error = result.expect_err("removing the known arm must reject the call");
    assert_eq!(
        planning_transitions, 0,
        "a simple call must not invoke planning"
    );
    assert!(
        error.unresolved_requirement().is_some(),
        "{}",
        error.message()
    );
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn reordered_cstr_requirement_expands_without_planning_and_reverifies() {
    let c_source = r#"
        uint64 read_terminator(uint8 haystack[], uint64 known_len) {
            uint64 length;
            length = strlen(haystack);
            return length;
        }
    "#;
    let click_source = r#"import click::cstr;

        verifying "source_identity.c";

        uint64 read_terminator(uint8 haystack[], uint64 known_len) {
            requires known_len < 18446744073709551615u64;
            requires defined(known_len + 1u64);
            requires viewable(haystack[0..known_len + 1u64]);
            views str: cstr_at(haystack, _);
            views haystack[0..known_len + 1u64];
            ensures result < 18446744073709551615u64;
        } by {
            execute();
            simp();
        }
    "#;
    let sources = [("source_identity.c", c_source)];

    let (verified, planning_transitions) =
        count_planning_statement_transitions(|| verify_c0_sources(click_source, &sources));
    let verified = verified.expect("the reordered borrowed string should verify");
    assert_eq!(
        planning_transitions, 0,
        "the source-identity retry must not enter hidden statement planning"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the source-identity retry should retain an expansion");
    assert!(
        expanded.iter().all(|tactic| !matches!(
            tactic,
            ProofTactic::SmartExecute | ProofTactic::ExecuteUntil(_) | ProofTactic::Simp
        )),
        "the top-level expansion must contain only retained simple tactics: {expanded:#?}"
    );

    let expanded_source = expand_c0_claim_source(
        click_source,
        &sources,
        "read_terminator",
        CProofClaim::Grouped,
    )
    .expect("the source-identity retry should expand into source");
    assert!(
        expanded_source.contains("views str: cstr_at(haystack, _);"),
        "the expansion should keep the reordered string clause: {expanded_source}"
    );
    assert!(!expanded_source.contains("execute();"));
    assert!(!expanded_source.contains("simp();"));
    verify_c0_sources(&expanded_source, &sources)
        .expect("the ordinary expanded source-identity proof should independently reverify");
}

fn assert_quantified_range_call_requirement_expands_and_deletion_rejects(fixture: &str) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(fixture);
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("quantified-range mdtest should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion = verify_c0_sources(click_source, &c_sources)
        .expect("quantified-range call requirement should verify");
    let expanded =
        expand_checked_grouped_claim(click_source, &verified_for_expansion, "range_probe")
            .expect("quantified-range call requirement should expand");
    assert!(
        expanded.contains("step() by {") || expanded.contains("step() {"),
        "expanded proof should prove the quantified-range requirement on its step: {expanded}"
    );
    crate::surface::proof::without_implicit_auto(|| verify_c0_sources(&expanded, &c_sources))
        .expect("expanded quantified-range proof should cold reverify");

    let without_have = without_first_step_obligation_proofs(&expanded);
    let error = crate::surface::proof::without_implicit_auto(|| {
        verify_c0_sources(&without_have, &c_sources)
    })
    .expect_err("deleting the step's quantified-range proof must reject the call");
    assert!(
        error.unresolved_requirement().is_some(),
        "deleted quantified-range Have should expose the structured call requirement: {}",
        error.message()
    );
}

#[test]
fn forall_loadable_range_call_requirement_expands_and_deletion_rejects() {
    assert_quantified_range_call_requirement_expands_and_deletion_rejects(
        "mdtests/forall_viewable_range.md",
    );
}

#[test]
fn exists_loadable_range_call_requirement_expands_and_deletion_rejects() {
    assert_quantified_range_call_requirement_expands_and_deletion_rejects(
        "mdtests/exists_viewable_range.md",
    );
}

/// Six null-checked allocations expand to six proof `if`s, each nested in
/// the previous one's `else` arm. The structural driver used to charge each
/// arm's continuation a level of its own, so this rewrite reached the region
/// bound at six and was declined as an unimplemented shape.
#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn nested_null_check_chain_expands_and_reverifies() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/nested_null_check_chain_expands.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("the null-check chain mdtest should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion =
        verify_c0_sources(click_source, &c_sources).expect("the smart proof verifies");
    let expanded = expand_checked_grouped_claim(click_source, &verified_for_expansion, "f")
        .unwrap_or_else(|error| panic!("the null-check chain should expand: {}", error.message()));
    assert_eq!(expanded.matches("\n    if ").count(), 1, "{expanded}");
    assert_eq!(expanded.matches(" if at(").count(), 6, "{expanded}");
    assert!(!expanded.contains("execute()"), "{expanded}");
    if let Err(error) = verify_c0_sources(&expanded, &c_sources) {
        panic!(
            "the expanded chain should re-verify: {}\n{expanded}",
            error.message()
        );
    }
}

#[test]
#[ignore = "nightly: descriptor-backed loop across all proof modes"]
fn descriptor_backing_range_loop_survives_all_proof_modes() {
    let (source, sources) =
        mdtest_sources("mdtests/loop_resource_backing_range_fold_after_write.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let (session, verified_for_expansion) = C0VerificationSession::new(&source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(&source, &verified_for_expansion, "probe").unwrap();
    let position =
        expansion::position_at_offset(&expanded, expanded.find("owns cells(h->data, n);").unwrap());

    session
        .verify_at(&expanded, position.line, position.column)
        .unwrap();
    drop(session);
    verify_c0_sources(&expanded, &sources).unwrap();
}

fn mdtest_sources(relative: &str) -> (String, Vec<(String, String)>) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(relative);
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .clone()
        .unwrap_or_else(|| panic!("`{relative}` should contain Click source"));
    (click_source, mdtest.c_sources.clone())
}

/// A proof `if` after `execute()` reaches its `result == 0` arm from both
/// arms of the C `if`, with different closers on each. Claim expansion places
/// the proof cases inside each C arm instead of refusing for want of a
/// proof-level condition between those outcomes.
#[test]
fn proof_cases_after_c_branch_expand_and_reverify() {
    let (click_source, c_sources) = mdtest_sources("mdtests/proof_cases_after_c_branch_expands.md");
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion =
        verify_c0_sources(&click_source, &c_sources).expect("the smart proof verifies");
    let expanded = expand_checked_grouped_claim(&click_source, &verified_for_expansion, "use_pick")
        .unwrap_or_else(|error| panic!("the caller proof should expand: {}", error.message()));
    assert!(
        expanded.contains(" if at(statement(2).entry, copied)"),
        "{expanded}"
    );
    assert_eq!(
        expanded.matches(" if result == 0 {").count(),
        1,
        "{expanded}"
    );
    assert!(
        expanded.contains("result == 18 => {") && expanded.contains("result == -1 => {"),
        "{expanded}"
    );
    let caller = &expanded[expanded.find("int use_pick").expect("caller proof")..];
    assert!(!caller.contains("execute()"), "{expanded}");
    assert!(!caller.contains("simp()"), "{expanded}");
    if let Err(error) = verify_c0_sources(&expanded, &c_sources) {
        panic!(
            "the expanded caller proof should re-verify: {}\n{expanded}",
            error.message()
        );
    }
}

/// A postcondition `result == 1 implies forall (k: int32) { ... }` closed by
/// `simp()` after execution expands to a `have` of the claim and
/// `assumption()`. The `have` and the claim lower the guarded quantifier with
/// independent fresh binders; the rewrite re-verifies only because
/// `assumption` matches that guarded quantifier up to its binders.
#[test]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn guarded_quantified_postcondition_expands_and_reverifies() {
    for (relative, function) in [
        (
            "mdtests/guarded_quantified_postcondition_expands.md",
            "vacuous",
        ),
        (
            "mdtests/guarded_quantified_postcondition_after_loop_expands.md",
            "fill",
        ),
    ] {
        let (click_source, c_sources) = mdtest_sources(relative);
        let c_sources = c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let verified_for_expansion = verify_c0_sources(&click_source, &c_sources)
            .unwrap_or_else(|error| panic!("`{relative}` should verify: {}", error.message()));
        let expanded =
            expand_checked_grouped_claim(&click_source, &verified_for_expansion, function)
                .unwrap_or_else(|error| panic!("`{relative}` should expand: {}", error.message()));
        let claim = &expanded[expanded
            .find(&format!("int {function}("))
            .expect("claim proof")..];
        let claim = &claim[claim.find("} by {").expect("claim proof body")..];
        let claim = &claim[..claim[1..].find("\n}").expect("claim end")];
        assert!(!claim.contains("execute()"), "{expanded}");
        assert!(!claim.contains("simp()"), "{expanded}");
        assert!(
            claim.contains("have result == 1 implies forall (k: int32)"),
            "{expanded}"
        );
        if let Err(error) = verify_c0_sources(&expanded, &c_sources) {
            panic!(
                "the expanded `{relative}` should re-verify: {}\n{expanded}",
                error.message()
            );
        }
    }
}

/// A guarded call postcondition closed by `simp` expands to the discharge
/// it performed: a `have` of the definedness guard, the checked `extract`
/// of the consequent, and the rewrite that uses it. The rewrite re-verifies
/// with no smart tactic left in the claim.
#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn guarded_postcondition_consequent_expands_and_reverifies() {
    let relative = "mdtests/guarded_postcondition_closes_after_call.md";
    let (click_source, c_sources) = mdtest_sources(relative);
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    for function in ["caller", "restricted"] {
        let expanded =
            expand_c0_claim_source(&click_source, &c_sources, function, CProofClaim::Grouped)
                .unwrap_or_else(|error| panic!("`{function}` should expand: {}", error.message()));
        let claim = &expanded[expanded
            .find(&format!("int32 {function}("))
            .expect("claim proof")..];
        let claim = &claim[claim.find("} by {").expect("claim proof body")..];
        let claim = &claim[..claim[1..].find("\n}").expect("claim end")];
        assert!(!claim.contains("execute()"), "{expanded}");
        assert!(!claim.contains("simp()"), "{expanded}");
        assert!(claim.contains("have defined((1 + "), "{expanded}");
        assert!(claim.contains("extract(st.live == "), "{expanded}");
        if let Err(error) = verify_c0_sources(&expanded, &c_sources) {
            panic!(
                "the expanded `{function}` should re-verify: {}\n{expanded}",
                error.message()
            );
        }
    }
}

/// Scoped equality chains and loaded pointer fields expand to checked
/// certificates that verify. The array case can transport its entry contract
/// directly; pointer chains use explicit rewrites.
#[test]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn scope_equality_chain_and_loaded_pointer_rewrite_expand_and_reverify() {
    for (relative, function, expected) in [
        (
            "mdtests/simp_chains_equalities_stated_in_a_scope.md",
            "caller",
            "transport(at(function.entry, occ[k] == 0), occ[k] == 0)",
        ),
        (
            "mdtests/rewrite_through_a_loaded_pointer_field.md",
            "same",
            "rewrite(",
        ),
        (
            "mdtests/simp_composes_a_pointer_field_chain_across_a_call.md",
            "caller",
            "rewrite(",
        ),
    ] {
        let (click_source, c_sources) = mdtest_sources(relative);
        let c_sources = c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let expanded =
            expand_c0_claim_source(&click_source, &c_sources, function, CProofClaim::Grouped)
                .unwrap_or_else(|error| panic!("`{relative}` should expand: {}", error.message()));
        let claim = &expanded[expanded
            .find(&format!("int32 {function}("))
            .expect("claim proof")..];
        let claim = &claim[claim.find("} by {").expect("claim proof body")..];
        let claim = &claim[..claim[1..].find("\n}").expect("claim end")];
        assert!(!claim.contains("simp()"), "{expanded}");
        assert!(
            claim.contains(expected) || claim.contains("assumption();"),
            "{expanded}"
        );
        if let Err(error) = verify_c0_sources(&expanded, &c_sources) {
            panic!(
                "the expanded `{relative}` should re-verify: {}\n{expanded}",
                error.message()
            );
        }
    }
}

/// The `int64` form: `simp` proves the guard with the checked
/// `int64_defined` certificate rule, citing the operands' indexed bounds, and
/// the expansion re-verifies with no smart tactic left in the claim.
#[test]
fn int64_guarded_postcondition_expands_to_int64_defined_and_reverifies() {
    let relative = "mdtests/guarded_postcondition_int64_bounds.md";
    let (click_source, c_sources) = mdtest_sources(relative);
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded =
        expand_c0_claim_source(&click_source, &c_sources, "caller", CProofClaim::Grouped)
            .unwrap_or_else(|error| panic!("`caller` should expand: {}", error.message()));
    let claim = &expanded[expanded.find("int64 caller(").expect("claim proof")..];
    let claim = &claim[claim.find("} by {").expect("claim proof body")..];
    let claim = &claim[..claim[1..].find("\n}").expect("claim end")];
    assert!(!claim.contains("execute()"), "{expanded}");
    assert!(!claim.contains("simp()"), "{expanded}");
    assert!(
        claim.contains("have defined((old(st.total) + "),
        "{expanded}"
    );
    assert!(
        claim.contains("arithmetic_certificate rules {"),
        "{expanded}"
    );
    assert!(
        claim.contains(
            "premise 0: at(function.entry, st.total < 100) => at(function.entry, st.total < 100);"
        ),
        "{expanded}"
    );
    assert!(
        claim.contains("int64_defined bounds [0, 1] => defined(("),
        "{expanded}"
    );
    assert!(claim.contains("extract(st.total == "), "{expanded}");
    if let Err(error) = verify_c0_sources(&expanded, &c_sources) {
        panic!(
            "the expanded `caller` should re-verify: {}\n{expanded}",
            error.message()
        );
    }
}

/// The `int32` form: the guard's nested `simp` proves it with the checked
/// `int32_defined` certificate rule citing the operands' constant bounds,
/// and the expansion re-verifies with no smart tactic left in the claim.
#[test]
fn int32_guarded_postcondition_expands_to_int32_defined_and_reverifies() {
    let relative = "mdtests/int32_defined_from_bounds.md";
    let (click_source, c_sources) = mdtest_sources(relative);
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded =
        expand_c0_claim_source(&click_source, &c_sources, "caller", CProofClaim::Grouped)
            .unwrap_or_else(|error| panic!("`caller` should expand: {}", error.message()));
    let claim = &expanded[expanded.find("int32 caller(").expect("claim proof")..];
    let claim = &claim[claim.find("} by {").expect("claim proof body")..];
    let claim = &claim[..claim[1..].find("\n}").expect("claim end")];
    assert!(!claim.contains("execute()"), "{expanded}");
    assert!(!claim.contains("simp()"), "{expanded}");
    assert!(
        claim.contains("have defined((old(st.total) + "),
        "{expanded}"
    );
    assert!(
        claim.contains("arithmetic_certificate rules {"),
        "{expanded}"
    );
    assert!(claim.contains("st.total < 100"), "{expanded}");
    assert!(
        claim.contains("int32_defined bounds [0, 1] => defined(("),
        "{expanded}"
    );
    assert!(claim.contains("extract(st.total == "), "{expanded}");
    if let Err(error) = verify_c0_sources(&expanded, &c_sources) {
        panic!(
            "the expanded `caller` should re-verify: {}\n{expanded}",
            error.message()
        );
    }
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn branch_continuation_match_expands_and_reverifies() {
    for relative in [
        "mdtests/branch_continuation_nested_match.md",
        "mdtests/branch_continuation_top_level_match.md",
    ] {
        let (click_source, c_sources) = mdtest_sources(relative);
        let c_sources = c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let verified_for_expansion = verify_c0_sources(&click_source, &c_sources)
            .unwrap_or_else(|error| panic!("`{relative}` should verify: {}", error.message()));
        let expanded = expand_checked_grouped_claim(&click_source, &verified_for_expansion, "f")
            .unwrap_or_else(|error| panic!("`{relative}` should expand: {}", error.message()));
        let claim = &expanded[expanded.find("int32 f(").expect("claim proof")..];
        assert!(!claim.contains("execute()"), "{expanded}");
        assert!(!claim.contains("simp()"), "{expanded}");
        if let Err(error) = verify_c0_sources(&expanded, &c_sources) {
            panic!(
                "the expanded `{relative}` should re-verify: {}\n{expanded}",
                error.message()
            );
        }
    }
}

/// Expands the smart tactic that starts at `anchor` (plus `skip` bytes) in
/// an mdtest's Click source and re-verifies the rewrite.
fn expand_mdtest_site_and_reverify(relative: &str, anchor: &str, skip: usize) -> String {
    let (click_source, c_sources) = mdtest_sources(relative);
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&click_source, &c_sources).expect("the smart proof verifies");
    let offset = click_source
        .find(anchor)
        .unwrap_or_else(|| panic!("`{relative}` should contain `{anchor}`"))
        + skip;
    let position = expansion::position_at_offset(&click_source, offset);
    let expanded =
        expand_c0_tactic_source_at(&click_source, &c_sources, position.line, position.column)
            .unwrap_or_else(|error| panic!("the site should expand: {}", error.message()));
    assert_ne!(expanded, click_source);
    if let Err(error) = verify_c0_sources(&expanded, &c_sources) {
        panic!(
            "the expanded proof should re-verify: {}\n{expanded}",
            error.message()
        );
    }
    expanded
}

/// A loop's `initialize` tactic after a proof-level `branch` is numbered
/// inside the loop tactic. The structural driver's search for the selected
/// tactic in the rest of the proof used to miss it and decline the `branch`,
/// so expansion refused a proof `click verify` accepts.
#[test]
fn loop_initialize_after_proof_branch_expands_and_reverifies() {
    let expanded = expand_mdtest_site_and_reverify(
        "mdtests/loop_after_proof_branch_expands.md",
        "initialize by simp();",
        "initialize by ".len(),
    );
    assert!(!expanded.contains("initialize by simp();"), "{expanded}");
    assert_eq!(expanded.matches("branch ").count(), 1, "{expanded}");
}

/// A `simp` in an arm of a `match` nested in a post-execution `if` arm is
/// checked per outcome path. The expansion capture searched only `if` arms
/// for the selected tactic, so it reported `has no source tactic` for it.
#[test]
fn simp_in_a_nested_post_execution_match_arm_expands_and_reverifies() {
    let expanded = expand_mdtest_site_and_reverify(
        "mdtests/a_match_in_a_post_execution_if_arm_takes_each_paths_arm.md",
        "Tri::One => { simp(); }",
        "Tri::One => { ".len(),
    );
    assert!(!expanded.contains("Tri::One => { simp(); }"), "{expanded}");
    assert!(expanded.contains("Tri::Zero => { simp(); }"), "{expanded}");
}

/// A ranked loop with no invariant has nothing to initialize. Its expansion
/// used to print that phase as `initialize by { }`, which is not Click; the
/// phase keeps `assumption();` and the rewrite re-verifies.
#[test]
fn ranked_loops_with_no_invariant_expand_and_reverify() {
    for fixture in [
        "mdtests/a_ranked_loop_with_no_invariant_closes_a_branching_body.md",
        "mdtests/a_ranked_unsigned_loop_with_no_invariant_closes_a_branching_body.md",
    ] {
        let expanded = expand_mdtest_site_and_reverify(fixture, "loop {", 0);
        assert!(
            expanded.contains("initialize by {\n            assumption();\n        }"),
            "{expanded}"
        );
        assert!(expanded.contains("preserve by {"), "{expanded}");
    }
}

/// An element of a multidimensional array field keeps one subscript per
/// dimension when a proof about it is expanded. The parser used to keep only
/// the flattened index, so the expansion printed `p->words[((1 * 2) + 1)]`,
/// which the parser itself rejects for a two-dimensional field.
#[test]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn multidimensional_array_field_expands_with_every_subscript() {
    let anchor = "ensures p->words[1][1] == value by ";
    let expanded = expand_mdtest_site_and_reverify(
        "mdtests/struct_wide_integer_arrays.md",
        anchor,
        anchor.len(),
    );
    assert!(
        expanded.contains("have p->words[1][1] == value by {"),
        "{expanded}"
    );
    assert!(!expanded.contains("words[(("), "{expanded}");
}

/// The same for an element the expansion spells from the checked state
/// rather than from the written clause: a local struct's field is a flat
/// array there, and its layout carries the declared dimensions so the
/// element reads `copy->values[1][2]`, not `copy->values[5]`.
#[test]
fn multidimensional_local_array_field_expands_with_every_subscript() {
    let anchor = "ensures result == 75;\n} by {\n    execute();\n    ";
    let expanded = expand_mdtest_site_and_reverify(
        "mdtests/struct_multidimensional_scalar_array.md",
        anchor,
        anchor.len(),
    );
    // Equality closure can finish without printing an interior read at all.
    assert!(
        expanded.contains("copy->values[1][2]") || expanded.contains("assumption();"),
        "{expanded}"
    );
    assert!(!expanded.contains("values[5]"), "{expanded}");
}

/// A `produces` clause naming a struct member is one ensure per field of
/// that member, all sharing the proof the author wrote once. They are one
/// claim, labelled by that written clause, and resolve to it: the locator
/// used to count written clauses by claim index, so the later claims pointed
/// past the last clause and `click audit` stopped with `could not locate
/// source ensure 2`.
#[test]
fn flattened_aggregate_claims_resolve_to_their_written_clause() {
    let (click_source, c_sources) = mdtest_sources("mdtests/struct_aggregate_resources.md");
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let file = expansion::parse_source_with_c_layouts(&click_source, &c_sources).unwrap();
    let write_inner = file
        .function_blocks()
        .iter()
        .find(|block| block.signature().name() == "write_inner")
        .unwrap();
    let produced = (0..write_inner.ensures().len())
        .filter(|index| write_inner.ensure_claim_label(*index) == "write_inner.owns_0")
        .count();
    assert!(produced >= 2, "the member should flatten to several claims");
    assert_eq!(write_inner.ensure_claim_label(0), "write_inner.owns_0");
    let sites = expansion::c0_smart_tactic_source_sites(&click_source, &c_sources).unwrap();
    let written = click_source
        .find("owns packet->inner by auto();")
        .expect("the fixture states the aggregate clause");
    let written = expansion::position_at_offset(&click_source, written);
    let produced_sites = sites
        .iter()
        .filter(|site| site.claim_label == "write_inner.owns_0")
        .collect::<Vec<_>>();
    assert_eq!(
        produced_sites.len(),
        1,
        "the written clause's one proof is one site"
    );
    let position = expansion::c0_tactic_source_position(
        &click_source,
        &c_sources,
        "write_inner.owns_0",
        produced_sites[0].source_index,
    )
    .unwrap_or_else(|error| panic!("{}", error.message()));
    assert_eq!(position.line, written.line);
}

/// A `produces` clause written in a contract `if` block is a claim of its
/// own, numbered among the written clauses in its place. The source locator
/// used to count only top-level clauses, so every later clause resolved to
/// the clause after it, the last to none, and selecting any line of the
/// file by `--claim FILE:LINE` stopped with `could not locate source
/// ensure 2`.
#[test]
fn a_conditional_produces_clause_is_located_in_its_place() {
    let (click, sources) = mdtest_sources("mdtests/population_initialized_cleanup.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let start = click.find("    if old(obj->refs) > 1 {").unwrap();
    let end = click.find("int32 cleanup(int32 payload) {").unwrap();
    let inputs = ProgramInputs::Bundle(sources.clone());
    for produces_proof in ["", " by auto()"] {
        let click = format!(
            "{}    if old(obj->refs) > 1 {{
        produces child_control(obj){produces_proof};
    }}
    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1 by auto();
    ensures obj->refs >= 0 by auto();
}}

{}",
            &click[..start],
            &click[end..]
        );
        for (text, label) in [
            ("produces child_control(obj)", "child_release.produces_0"),
            ("ensures count(child_ref(obj))", "child_release.ensures_0"),
            ("ensures obj->refs >= 0", "child_release.ensures_1"),
        ] {
            for scope in [ClaimLocationScope::Innermost, ClaimLocationScope::ProofUnit] {
                let selected = claim_at(
                    None,
                    &click,
                    &inputs,
                    line_containing(&click, text),
                    None,
                    scope,
                )
                .unwrap_or_else(|error| panic!("{text}: {error:?}"));
                assert_eq!(selected.label, label, "{text} ({produces_proof:?})");
            }
        }
    }
}

/// A `simp()` closing an `initialize` script that several invariants share
/// expands to one step per invariant, each holding the whole script. Those
/// steps stand for the tactics written before the closer too, so the rewrite
/// replaces from the first of them: left in place, the leading `unfold` ran
/// before every generated step and the phase no longer closed its goal.
#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn shared_initialize_closer_expansion_replaces_the_script_before_it() {
    let anchor = "initialize by { unfold(head(box)); ";
    let expanded = expand_mdtest_site_and_reverify(
        "mdtests/loop_decreases_pure_expression.md",
        anchor,
        anchor.len(),
    );
    assert!(
        expanded.contains("initialize by { have 0 <= box[0] by {"),
        "{expanded}"
    );
    assert!(
        expanded.contains("have head(box) == box[0] by {"),
        "{expanded}"
    );
    assert!(
        !expanded.contains("initialize by { unfold(head(box)); have"),
        "{expanded}"
    );
}

/// An invariant owes its side conditions as entry goals of their own beside
/// its body: a quantified `viewable` invariant owes the extent bound too.
/// The closer's expansion states one `have` per owed goal, so that
/// invariant is named twice. The script layout used to accept only one
/// `have` per invariant, fell back to running the whole script against
/// every goal, and checked the bound's arithmetic step against the
/// `viewable` body.
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn initialize_closer_expansion_names_an_invariant_once_per_owed_goal() {
    let anchor = "            }\n            simp();\n        }\n        preserve";
    let quantified = "have forall (k: int32) { 0 <= k and k <= n implies viewable(a[0..k]) } by {\n                have";
    for fixture in [
        "mdtests/loop_initialize_narrows_a_held_range_under_a_universal.md",
        "mdtests/loop_quantified_viewable_invariant_bounded_by_its_views_clause.md",
    ] {
        let expanded =
            expand_mdtest_site_and_reverify(fixture, anchor, "            }\n            ".len());
        assert_eq!(expanded.matches(quantified).count(), 2, "{expanded}");
    }
}

/// An element of a struct array keeps its subscript in an expanded proof.
/// The parser used to keep only the element's byte address, so the expansion
/// spelled `entries[0].x` as `(entries + (0 * 4))->x`, which lowers to a
/// different term than the fact it was meant to rewrite with.
#[test]
fn struct_array_element_expands_with_its_subscript() {
    let anchor = "ensures result == 19 by ";
    let expanded = expand_mdtest_site_and_reverify(
        "mdtests/data_only_translation_unit.md",
        anchor,
        anchor.len(),
    );
    assert!(expanded.contains("entries[0]"), "{expanded}");
    assert!(!expanded.contains("(entries + "), "{expanded}");
}

/// Verifying one proof unit treats the functions it does not select as
/// assumptions, and must not refuse the selected function's termination for
/// what those functions would owe in a run that selects them. `even` ranks
/// a recursion that runs through `odd`; `run` calls a `static inline`
/// helper whose loop measure only the helper's own run verifies. Both used
/// to be refused when verified alone, while the whole file verified.
#[test]
fn targeted_termination_assumes_unselected_callees() {
    for (fixture, anchor) in [
        (
            "mdtests/c_decreases_mutual_recursion.md",
            "int32 even(int32 n) {\n    ",
        ),
        (
            "mdtests/inline_helper_ranked_loop.md",
            "int32 run(int32 n) {\n    ",
        ),
    ] {
        let (click_source, c_sources) = mdtest_sources(fixture);
        let c_sources = c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let offset = click_source
            .find(anchor)
            .unwrap_or_else(|| panic!("`{fixture}` should contain `{anchor}`"))
            + anchor.len();
        let position = expansion::position_at_offset(&click_source, offset);
        verify_c0_sources_at(&click_source, &c_sources, position.line, position.column)
            .unwrap_or_else(|error| panic!("{fixture}: {}", error.message()));
        // A retained session keeps the baseline's rules; the unselected
        // helper's must not survive under its executing name.
        let (session, _) = crate::surface::C0VerificationSession::new(&click_source, &c_sources)
            .unwrap_or_else(|error| panic!("{fixture}: {}", error.message()));
        session
            .verify_at(&click_source, position.line, position.column)
            .unwrap_or_else(|error| panic!("{fixture} in a session: {}", error.message()));
    }
}

/// A `simp()` after `execute(); intro(); intro();` closes a claim proof the
/// `intro`s opened, and expands to only the steps it adds there. It used to
/// expand to the whole claim's certificate, `have <claim> by { ... };
/// assumption();`, and a deferred `normalize()` or `assumption()` ignored
/// the opened proof, so neither form re-verified.
#[test]
fn post_execution_closer_continues_the_proof_intros_opened() {
    let anchor = "intro();\n        simp();";
    let expanded = expand_mdtest_site_and_reverify(
        "mdtests/post_execution_intro_quantified_ensure.md",
        anchor,
        "intro();\n        ".len(),
    );
    assert!(
        expanded.contains("intro();\n        intro();\n        normalize();"),
        "{expanded}"
    );
    assert!(!expanded.contains("have forall"), "{expanded}");
}

/// The same for a proof a `witness` opened: the `simp()` expands to the steps
/// it adds after the witness, checked inside that proof, so a changed
/// witness cannot be closed from the claims instead
/// (`post_execution_choose_and_witness_share_the_retained_outcome_proof`).
#[test]
fn post_execution_closer_continues_the_proof_a_witness_opened() {
    let anchor = "witness { len: found_len };\n        simp();";
    let expanded = expand_mdtest_site_and_reverify(
        "mdtests/cstr_stdlib.md",
        anchor,
        "witness { len: found_len };\n        ".len(),
    );
    assert!(!expanded.contains("have exists (len: int32)"), "{expanded}");
}

/// The `simp()` closing the loop's `preserve` proof in `arena_init` expands
/// in parseable source spelling. It once cited the function-entry alignment
/// fact, rendered as a pointer cast Click cannot parse; it now separates the
/// loop's store from the earlier cells by their indices alone, and
/// `snapshot_read_alignment_fact_renders_as_aligned` covers the rendering.
#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn entry_alignment_premise_expands_in_source_spelling() {
    let expanded = expand_mdtest_site_and_reverify(
        "mdtests/entry_alignment_premise_expands.md",
        "simp();\n        }\n    }\n    have i == capacity",
        0,
    );
    assert!(!expanded.contains("(uint64)arena"), "{expanded}");
}

/// Written else nesting is not recursive driver depth: a failed allocation
/// returns, so twelve null checks can expand and re-verify just like eleven.
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn expansion_reverifies_terminal_cases_past_the_old_nesting_bound() {
    let (click_source, c_sources) = mdtest_sources("mdtests/expand_sequential_null_checks.md");
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion =
        verify_c0_sources(&click_source, &c_sources).expect("both smart proofs verify");
    let expansions = [("eleven", 11), ("twelve", 12)].map(|(name, count)| {
        let expanded = expand_checked_grouped_claim(&click_source, &verified_for_expansion, name)
            .unwrap_or_else(|error| panic!("{name} should expand: {}", error.message()));
        (name, count, expanded)
    });
    for (name, count, expanded) in expansions {
        assert_eq!(expanded.matches(" if at(").count(), count, "{expanded}");
        verify_c0_sources(&expanded, &c_sources)
            .unwrap_or_else(|error| panic!("{name} rewrite should verify: {}", error.message()));
    }
}

#[test]
fn symbolic_branch_direct_call_requirement_expands_and_checks_its_known_arm() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/c_named_function_contract_source_refusal_in_symbolic_branch.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("symbolic-branch mdtest should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion = verify_c0_sources(click_source, &c_sources)
        .expect("symbolic-branch source requirement should verify");
    let expanded = expand_checked_grouped_claim(click_source, &verified_for_expansion, "apply")
        .expect("symbolic-branch source requirement should expand");
    assert!(
        !expanded.contains("have value >= 0 or value == -1 by"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &c_sources)
        .expect("expanded direct branch call requirement should reverify");
    let stronger = expanded.replace(
        "requires value >= 0 or value == -1;",
        "requires value >= 2 or value == -1;",
    );
    assert_ne!(stronger, expanded);
    let error = verify_c0_sources(&stronger, &c_sources)
        .expect_err("a positive value alone does not establish the stronger call requirement");
    assert!(
        error.unresolved_requirement().is_some(),
        "{}",
        error.message()
    );
}

#[test]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn integer_sum_range_fold_expands_and_reverifies() {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/integer_sum_range_fold.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("summation mdtest should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion =
        verify_c0_sources(click_source, &c_sources).unwrap_or_else(|error| {
            panic!(
                "summation ordinary verification failed: {}",
                error.message()
            )
        });
    let expanded = expand_checked_grouped_claim(click_source, &verified_for_expansion, "sum")
        .expect("the summation grouped proof should expand");
    verify_c0_sources(&expanded, &c_sources)
        .expect("the expanded summation proof should reverify independently");
}

#[test]
fn integer_quantifier_smart_proofs_expand_and_recheck() {
    let source = r#"
theorem integer_forall_simp() {
    ensures ordered: forall (z: Integer) { z + 1 > z } by { simp(); }
}
theorem integer_exists_simp(x: Integer) {
    ensures witnessed: exists (z: Integer) { z == x } by {
        witness { z: x };
        simp();
    }
}
theorem integer_forall_logical_simp() {
    ensures logical: forall (z: Integer) { z == z and z == z } by { simp(); }
}
theorem integer_exists_choose() {
    requires exists (z: Integer) { z == z };
    ensures chosen: exists (k: Integer) { k == k } by {
        obtain (candidate: Integer) { candidate == candidate };
        witness { k: candidate };
        assumption();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("Integer quantifier smart proofs should verify");

    for label in [
        "integer_forall_simp.ordered",
        "integer_exists_simp.witnessed",
        "integer_forall_logical_simp.logical",
        "integer_exists_choose.chosen",
    ] {
        let expanded = expand_c0_claim_source_by_label(source, &[], label)
            .expect("the Integer quantifier claim should expand");
        if label.ends_with("ordered") {
            assert!(
                expanded.contains("arithmetic_certificate"),
                "{label}: {expanded}"
            );
        } else if label.ends_with("witnessed") {
            assert!(expanded.contains("normalize();"), "{label}: {expanded}");
        } else if label.ends_with("logical") {
            assert!(expanded.contains("intro();"), "{label}: {expanded}");
            // Equality closure can discharge this reflexive conjunction
            // directly. The expanded claim must still verify below.
        } else {
            assert!(
                expanded.contains("obtain (candidate: Integer) { candidate == candidate }"),
                "{label}: {expanded}"
            );
            assert!(
                expanded.contains("witness { k: candidate }"),
                "{label}: {expanded}"
            );
        }
        verify_c0_sources(&expanded, &[]).unwrap_or_else(|error| {
            panic!("{label} expansion should recheck: {}", error.message())
        });
    }
}

#[test]
fn integer_existential_keeps_definedness_under_one_witness() {
    let source = r#"
theorem guarded_integer_exists(value: int32) {
    requires defined(value + 1);
    requires exists (z: Integer) {
        z == to_integer(if value > 0 { value } else { value + 1 })
    };
    ensures branched: exists (k: Integer) {
        k == to_integer(if value > 0 { value } else { value + 1 })
    } by {
        obtain (candidate: Integer) {
            candidate == to_integer(if value > 0 { value } else { value + 1 })
        };
        witness { k: candidate };
        assumption();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("guarded Integer existentials should verify");
    let expanded = expand_c0_claim_source_by_label(source, &[], "guarded_integer_exists.branched")
        .expect("guarded Integer existential should expand");
    verify_c0_sources(&expanded, &[]).expect("expanded guarded Integer existential should recheck");

    let fixed_witness = r#"
theorem fixed_integer_witness(value: int32) {
    requires defined(value + 1);
    ensures witness_fixed: exists (z: Integer) {
        z == 0 and to_integer(value + 1) == to_integer(value + 1)
    } by {
        witness { z: 0 };
        both {
            both {
                assumption();
            } and {
                assumption();
            }
        } and {
            both {
                normalize();
            } and {
                normalize();
            }
        }
    }
}
"#;
    verify_c0_sources(fixed_witness, &[])
        .expect("a fixed Integer witness should retain its definedness obligation");
    let fixed_expanded =
        expand_c0_claim_source_by_label(fixed_witness, &[], "fixed_integer_witness.witness_fixed")
            .expect("fixed Integer witness should expand");
    assert!(fixed_expanded.contains("both {"), "{fixed_expanded}");
    verify_c0_sources(&fixed_expanded, &[]).expect("expanded fixed Integer witness should recheck");

    let missing_definedness = r#"
theorem missing_integer_definedness(value: int32) {
    ensures exists (z: Integer) {
        z == 0 and to_integer(value + 1) == to_integer(value + 1)
    } by {
        witness { z: 0 };
        simp();
    }
}
"#;
    let missing_error = verify_c0_sources(missing_definedness, &[])
        .expect_err("an Integer existential may not discard its definedness obligation");
    assert!(
        missing_error
            .message()
            .contains("checked `simp` after witness/choose"),
        "the checked post-witness failure should identify the remaining proof step: {}",
        missing_error.message()
    );
    assert!(
        !missing_error
            .message()
            .contains("witness` is not available"),
        "legacy fallback must not misreport a successful witness: {}",
        missing_error.message()
    );
}

#[test]
fn integer_range_fold_array_contract_verifies_expands_and_rechecks() {
    let c_source = r#"int32 array_fold_append_at_zero(int32 a[]) {
    return 0;
}"#;
    let click_source = r#"verifying "integer_range_fold_array_body.c";

int32 array_fold_append_at_zero(int32 a[]) {
    views a[0..1];
    ensures (0..1).fold(0, |acc, k| { acc + to_integer(a[k]) }) ==
        (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) }) + to_integer(a[0]) by {
        execute();
        have 0 <= 0 by { simp(); }
        have 0 < 2147483647 by { simp(); }
        apply(integer_range_fold_append(
            (0..0).fold(0, |acc, k| { acc + to_integer(a[k]) })
        )) using {
            0 <= 0;
            0 < 2147483647;
        }
        simp();
    }
}"#;

    let sources = [("integer_range_fold_array_body.c", c_source)];
    let verified_for_label = verify_c0_sources(click_source, &sources)
        .expect("the array range-fold append contract should verify");
    let expanded = expand_checked_function_claim(
        click_source,
        &verified_for_label,
        "array_fold_append_at_zero.ensures_0",
    )
    .expect("the array range-fold append contract should expand");
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded array range-fold append contract should recheck");
}

#[test]
fn integer_pure_function_array_argument_expands_and_rechecks() {
    let source = r#"
function first_integer(values: int32[]) -> Integer {
    to_integer(values[0])
}

theorem first_integer_unfolds(values: int32[]) {
    requires defined(values[0]);
    ensures first_integer(values) == to_integer(values[0]) by {
        unfold(first_integer(values));
        normalize();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("Integer array arguments should lower");
    let expanded = expand_c0_claim_source_by_label(source, &[], "first_integer_unfolds.ensures_0")
        .expect("Integer array argument function should expand");
    verify_c0_sources(&expanded, &[])
        .expect("expanded Integer array argument function should recheck");
}

#[test]
fn integer_existential_rewrites_array_index_through_to_int32() {
    let source = r#"
theorem indexed_integer_exists(values: int32[]) {
    requires defined(values[0]);
    requires values[0] == 0;
    ensures exists (z: Integer) {
        z == to_integer(values[to_int32(z)])
    } by {
        witness { z: 0 };
        both {
            both { simp(); } and { simp(); }
        } and {
            both {
                both { simp(); } and { simp(); }
            } and {
                rewrite(values[0] == 0);
                simp();
            }
        }
    }
}
"#;
    verify_c0_sources(source, &[])
        .expect("Integer witness substitution should reach an array index");
    let expanded = expand_c0_claim_source_by_label(source, &[], "indexed_integer_exists.ensures_0")
        .expect("indexed Integer existential should expand");
    verify_c0_sources(&expanded, &[]).expect("expanded indexed Integer existential should recheck");
}

#[test]
#[ignore = "nightly: 2.2s in the parallel gate"]
fn c_valued_range_fold_rejects_unsupported_carriers_before_lowering() {
    // Keep the report's original C body and proof, including its array reads.
    let c_source = r#"int32 g(uint8 p[], uint8 x) {
    int32 count;
    count = 0;
    if (p[0] == x) { count = count + 1; }
    if (p[1] == x) { count = count + 1; }
    return count;
}"#;
    let source = r#"verifying "g.c";
function my_count(bytes: uint8[], lo: uint64, hi: uint64, value: uint8) -> int32 {
    (lo..hi).fold(0, |acc, k| { acc + if bytes[k] == value { 1 } else { 0 } })
}
int32 g(uint8 p[], uint8 x) {
    views p[0..2];
    ensures result == my_count(p, 0u64, 2u64, x) by {
        execute();
        unfold(my_count(p, 0u64, 2u64, x));
        simp();
    }
}
"#;
    let error = verify_c0_sources(source, &[("g.c", c_source)])
        .expect_err("uint64 C-valued fold must be refused during validation");
    assert!(
        error
            .message()
            .contains("range fold with uint64 bounds requires an Integer accumulator"),
        "{}",
        error.message()
    );
    assert!(error.message().contains("my_count"), "{}", error.message());
    assert!(!error.message().contains("produced 0 paths"));

    // Reject the same unsupported carrier for symbolic, concrete,
    // and empty bounds: support must not depend on unfolding a call.
    for bounds in ["lo..hi", "0u64..2u64", "lo..lo"] {
        let source = format!(
            "function wide(lo: uint64, hi: uint64) -> int32 {{ ({bounds}).fold(0, |acc, k| {{ acc + 1 }}) }}"
        );
        let error =
            verify_c0_sources(&source, &[]).expect_err("wide C-valued fold must be rejected");
        assert!(
            error
                .message()
                .contains("range fold with uint64 bounds requires an Integer accumulator"),
            "{}",
            error.message()
        );
    }
    for (ty, initial, body) in [
        ("uint64", "0u64", "acc + 1u64"),
        ("int64", "0i64", "acc + 1i64"),
        ("uint32", "z", "acc"),
        ("uint8", "z", "acc"),
        ("bool", "z", "acc"),
    ] {
        let source = format!(
            "function unsupported(lo: int32, hi: int32, z: {ty}) -> {ty} {{ (lo..hi).fold({initial}, |acc, k| {{ {body} }}) }}"
        );
        let error =
            verify_c0_sources(&source, &[]).expect_err("non-int32 C accumulator must be rejected");
        assert!(
            error
                .message()
                .contains("C-valued range fold requires an int32 accumulator"),
            "{ty}: {}",
            error.message()
        );
    }

    // C-valued subfolds inside Integer expressions also need a named refusal.
    let wrapped = r#"
function wrapped(lo: uint64, hi: uint64) -> Integer {
    to_integer((lo..hi).fold(0, |acc, k| { acc + 1 }))
}
theorem check_wrapped(lo: uint64, hi: uint64) {
    ensures wrapped(lo, hi) == 0 by { unfold(wrapped(lo, hi)); simp(); }
}
"#;
    let error = verify_c0_sources(wrapped, &[]).expect_err("unsupported subfold must be refused");
    assert!(
        error.message().contains("Integer accumulator"),
        "{}",
        error.message()
    );
    assert!(!error.message().contains("produced 0 paths"));

    // The same program's supported int32 fold still verifies and expands.
    let supported = source
        .replace("uint64", "int32")
        .replace("0u64", "0")
        .replace("2u64", "2");
    let sources = [("g.c", c_source)];
    let verified_for_label =
        verify_c0_sources(&supported, &sources).expect("int32 count fold should verify");
    let expanded = expand_checked_function_claim(&supported, &verified_for_label, "g.ensures_0")
        .expect("int32 count proof should expand");
    verify_c0_sources(&expanded, &sources).expect("expanded int32 count proof should recheck");
}

#[test]
fn integer_range_fold_surface_typing_and_unfolding() {
    let source = r#"
function sum_machine_range(n: int32) -> Integer {
    (0..(n + 1)).fold(0, |acc, k| { acc + to_integer(k) })
}

function sum_integer_range(lo: Integer, hi: Integer) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + k })
}

function sum_integer_range_captured(lo: Integer, hi: Integer, z: Integer) -> Integer {
    (lo + 1..hi + 1).fold(z, |acc, k| { acc + z + k })
}

theorem machine_range_unfolds(n: int32) {
    requires defined(n + 1);
    ensures sum_machine_range(n) == (0..(n + 1)).fold(0, |acc, k| { acc + to_integer(k) }) by {
        unfold(sum_machine_range(n));
        normalize();
    }
}

theorem integer_range_unfolds(lo: Integer, hi: Integer) {
    ensures sum_integer_range(lo, hi) == (lo..hi).fold(0, |acc, k| { acc + k }) by {
        unfold(sum_integer_range(lo, hi));
        normalize();
    }
}

theorem integer_range_captured_unfolds(lo: Integer, hi: Integer, z: Integer) {
    ensures sum_integer_range_captured(lo, hi, z) ==
        (lo + 1..hi + 1).fold(z, |acc, k| { acc + z + k }) by {
        unfold(sum_integer_range_captured(lo, hi, z));
        normalize();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("machine and Integer range folds should unfold");
    for label in [
        "machine_range_unfolds.ensures_0",
        "integer_range_unfolds.ensures_0",
        "integer_range_captured_unfolds.ensures_0",
    ] {
        let expanded = expand_c0_claim_source_by_label(source, &[], label)
            .unwrap_or_else(|error| panic!("{label} should expand: {}", error.message()));
        verify_c0_sources(&expanded, &[]).unwrap_or_else(|error| {
            panic!("{label} expansion should recheck: {}", error.message())
        });
    }
}

#[test]
fn integer_range_fold_mixed_match_typing_expands_and_rechecks() {
    let source = r#"
spec enum FoldInput { Empty, Wrapped(Integer), Machine(int32) }

function fold_match(value: FoldInput) -> Integer {
    (0..1).fold(0, |acc, k| {
        acc + match value {
            FoldInput::Empty => 0,
            FoldInput::Wrapped(inner) => inner,
            FoldInput::Machine(raw) => to_integer(raw),
        }
    })
}

function match_fold(value: FoldInput) -> Integer {
    match value {
        FoldInput::Empty => (0..1).fold(0, |acc, k| { acc + to_integer(k) }),
        FoldInput::Wrapped(inner) => inner,
        FoldInput::Machine(raw) => to_integer(raw),
    }
}

theorem fold_match_unfolds(value: Integer) {
    ensures fold_match(FoldInput::Wrapped(value)) ==
        (0..1).fold(0, |acc, k| { acc + value }) by {
        unfold(fold_match(FoldInput::Wrapped(value)));
        normalize();
    }
}

theorem match_fold_unfolds() {
    ensures match_fold(FoldInput::Empty) ==
        (0..1).fold(0, |acc, k| { acc + to_integer(k) }) by {
        unfold(match_fold(FoldInput::Empty));
        normalize();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("folds and algebraic matches should compose");
    for label in [
        "fold_match_unfolds.ensures_0",
        "match_fold_unfolds.ensures_0",
    ] {
        let expanded = expand_c0_claim_source_by_label(source, &[], label)
            .unwrap_or_else(|error| panic!("{label} should expand: {}", error.message()));
        verify_c0_sources(&expanded, &[]).unwrap_or_else(|error| {
            panic!("{label} expansion should recheck: {}", error.message())
        });
    }

    let bad_source = r#"
spec enum FoldInput { Empty, Wrapped(Integer), Machine(int32) }

function bad_fold_match(value: FoldInput) -> Integer {
    (0..1).fold(0, |acc, k| {
        acc + match value {
            FoldInput::Empty => 0,
            FoldInput::Wrapped(inner) => inner,
            FoldInput::Machine(raw) => raw,
        }
    })
}

theorem force_bad_fold_match() {
    ensures bad_fold_match(FoldInput::Machine(0)) == 0 by {
        unfold(bad_fold_match(FoldInput::Machine(0)));
        normalize();
    }
}
"#;
    let error = verify_c0_sources(bad_source, &[])
        .expect_err("a C match field must not enter Integer fold arithmetic");
    assert!(
        error
            .message()
            .contains("match for `FoldInput` has incompatible arm result types Integer and int32"),
        "unexpected mixed match/fold diagnostic: {}",
        error.message()
    );
}

#[test]
fn integer_range_fold_surface_typing_rejects_mixed_bodies() {
    for (source, expected) in [
        (
            r#"
theorem bad_machine_body_direct(n: int32) {
    ensures (0..n).fold(0, |acc, k| { acc + k }) == to_integer(0);
}
"#,
            "mathematical Integer arithmetic cannot mix with C values",
        ),
        (
            r#"
function bad_machine_body(n: int32) -> Integer {
    (0..n).fold(0, |acc, k| { acc + k })
}
theorem force_bad_machine_body(n: int32) {
    ensures bad_machine_body(n) == to_integer(0) by {
        unfold(bad_machine_body(n));
        normalize();
    }
}
"#,
            "function `bad_machine_body` returns Integer, but its body can produce `k` of type int32",
        ),
        (
            r#"
theorem bad_integer_conversion_direct(lo: Integer, hi: Integer) {
    ensures (lo..hi).fold(0, |acc, k| { acc + to_integer(k) }) == 0;
}
"#,
            "to_integer expects a machine integer or Nat",
        ),
        (
            r#"
function bad_integer_conversion(lo: Integer, hi: Integer) -> Integer {
    (lo..hi).fold(0, |acc, k| { acc + to_integer(k) })
}
theorem force_bad_integer_conversion(lo: Integer, hi: Integer) {
    ensures bad_integer_conversion(lo, hi) == 0 by {
        unfold(bad_integer_conversion(lo, hi));
        normalize();
    }
}
"#,
            "to_integer expects a machine integer or Nat",
        ),
        (
            r#"
theorem bad_c_body_direct(x: int32, z: Integer) {
    ensures (0..3).fold(z, |acc, k| { x }) == z;
}
"#,
            "range fold body must preserve Integer accumulator",
        ),
        (
            r#"
function bad_c_body(x: int32, z: Integer) -> Integer {
    (0..3).fold(z, |acc, k| { x })
}
theorem force_bad_c_body(x: int32, z: Integer) {
    ensures bad_c_body(x, z) == z by {
        unfold(bad_c_body(x, z));
        normalize();
    }
}
"#,
            "function `bad_c_body` returns Integer, but its body can produce `x` of type int32",
        ),
    ] {
        let error = verify_c0_sources(source, &[])
            .expect_err("invalid fold body should be rejected by scoped typing");
        assert!(
            error.message().contains(expected),
            "expected `{expected}` for invalid fold body, got: {}",
            error.message()
        );
    }
}

#[test]
fn integer_range_fold_law_application_positive() {
    let law_source = r#"
theorem machine_fold_empty(start: int32, end: int32) {
    requires end <= start;
    ensures (start..end).fold(0, |acc, k| { acc + to_integer(k) }) == 0 by {
        apply(integer_range_fold_empty((start..end).fold(0, |acc, k| { acc + to_integer(k) }))) using {
            end <= start;
        }
    }
}

theorem machine_fold_append(end: int32) {
    requires 0 <= end;
    requires end < 2147483647;
    ensures (0..(end + 1)).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (0..end).fold(0, |acc, k| { acc + to_integer(k) }) + to_integer(end) by {
        apply(integer_range_fold_append((0..end).fold(0, |acc, k| { acc + to_integer(k) }))) using {
            0 <= end;
            end < 2147483647;
        }
    }
}

theorem integer_fold_empty(start: Integer, end: Integer) {
    requires end <= start;
    ensures (start..end).fold(0, |acc, k| { acc + k }) == 0 by {
        apply(integer_range_fold_empty((start..end).fold(0, |acc, k| { acc + k }))) using {
            end <= start;
        }
    }
}

theorem integer_fold_append(start: Integer, end: Integer) {
    requires start <= end;
    ensures (start..(end + 1)).fold(0, |acc, k| { acc + k }) ==
        (start..end).fold(0, |acc, k| { acc + k }) + end by {
        apply(integer_range_fold_append((start..end).fold(0, |acc, k| { acc + k }))) using {
            start <= end;
        }
    }
}
"#;
    verify_c0_sources(law_source, &[]).expect("checked Integer fold laws should verify");
    for label in [
        "machine_fold_empty.ensures_0",
        "machine_fold_append.ensures_0",
        "integer_fold_empty.ensures_0",
        "integer_fold_append.ensures_0",
    ] {
        let expanded = expand_c0_claim_source_by_label(law_source, &[], label)
            .unwrap_or_else(|error| panic!("{label} should expand: {}", error.message()));
        verify_c0_sources(&expanded, &[]).unwrap_or_else(|error| {
            panic!("{label} expansion should recheck: {}", error.message())
        });
    }
}

#[test]
fn integer_range_fold_law_application_rejects_missing_guards_or_shape() {
    for (source, expected) in [
        (
            r#"
theorem machine_fold_append_missing_guard(end: int32) {
    requires 0 <= end;
    requires end < 2147483647;
    ensures (0..(end + 1)).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (0..end).fold(0, |acc, k| { acc + to_integer(k) }) + to_integer(end) by {
        apply(integer_range_fold_append((0..end).fold(0, |acc, k| { acc + to_integer(k) }))) using {
            0 <= end;
        }
    }
}
"#,
            "required exact fold guard is unavailable",
        ),
        (
            r#"
theorem machine_fold_append_wrong_guard(end: int32) {
    requires end <= 0;
    requires end < 2147483647;
    ensures (0..(end + 1)).fold(0, |acc, k| { acc + to_integer(k) }) ==
        (0..end).fold(0, |acc, k| { acc + to_integer(k) }) + to_integer(end) by {
        apply(integer_range_fold_append((0..end).fold(0, |acc, k| { acc + to_integer(k) }))) using {
            end <= 0;
            end < 2147483647;
        }
    }
}
"#,
            "required exact fold guard is unavailable",
        ),
        (
            r#"
theorem machine_fold_argument_missing_definedness(divisor: int32) {
    ensures 0 == 0 by {
        apply(integer_range_fold_append((0..1).fold(0, |acc, k| {
            acc + to_integer(k / divisor)
        }))) using { }
    }
}
"#,
            "this Integer expression does not denote one symbolic value here",
        ),
        (
            r#"
theorem machine_fold_law_wrong_arity(end: int32) {
    requires end <= 0;
    ensures (0..end).fold(0, |acc, k| { acc + to_integer(k) }) == 0 by {
        apply(integer_range_fold_empty()) using { end <= 0; }
    }
}
"#,
            "expects exactly one Integer fold argument",
        ),
        (
            r#"
theorem machine_fold_law_non_fold() {
    ensures 0 == 0 by {
        apply(integer_range_fold_empty(0)) using { }
    }
}
"#,
            "requires one Integer range-fold argument",
        ),
    ] {
        let error = verify_c0_sources(source, &[])
            .expect_err("fold laws must reject omitted or mismatched checked evidence");
        assert!(
            error.message().contains(expected),
            "expected `{expected}` for rejected fold law, got: {}",
            error.message()
        );
    }
}

#[test]
fn integer_range_fold_law_applies_after_execution() {
    let c_source = r#"
            int32 fold_context(int32 end) {
                return end;
            }
        "#;
    let click_source = r#"
            verifying "fold_context.c";

            int32 fold_context(int32 end) {
                requires 0 <= end;
                requires end < 2147483647;
                ensures result == end by {
                    execute();
                    have (0..(end + 1)).fold(0, |acc, k| { acc + to_integer(k) }) ==
                        (0..end).fold(0, |acc, k| { acc + to_integer(k) }) + to_integer(end) by {
                        apply(integer_range_fold_append((0..end).fold(0, |acc, k| {
                            acc + to_integer(k)
                        }))) using {
                            0 <= end;
                            end < 2147483647;
                        }
                    }
                    simp();
                }
            }
        "#;

    verify_c0_sources(click_source, &[("fold_context.c", c_source)])
        .expect("a checked fold law should apply in the retained execution context");
}

#[test]
fn context_free_implication_simp_expands_intro_and_rechecks() {
    let source = r#"
theorem reflexive_implication(x: int32) {
    ensures x == 0 implies x == 0 by { simp(); }
}
"#;
    verify_c0_sources(source, &[]).expect("smart implication proof should verify");
    let offset = source.find("simp();").expect("expected smart tactic");
    let position = expansion::position_at_offset(source, offset);
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column).unwrap();
    assert!(expanded.contains("intro();"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &[])
        .expect("expanded implication introduction should independently recheck");
    let missing_intro = expanded.replacen("intro();", "", 1);
    verify_c0_sources(&missing_intro, &[])
        .expect_err("removing the retained introduction must invalidate the proof");
}

/// A `have` with no written proof is `have P by simp();`. Expansion addresses
/// a proof's tactics through source positions, so a default proof must not
/// leave it without a block to rewrite: the `have` gains one, and a smart
/// tactic beside it still expands and rechecks.
#[test]
fn expansion_rewrites_a_have_with_a_default_proof() {
    let source = r#"
theorem default_have(x: int32) {
    requires 0 <= x;
    ensures 0 <= x and x == x by {
        have x == x;
        simp();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("the default `have` proof should verify");
    for needle in ["have x == x;", "simp();"] {
        let offset = source.find(needle).expect("expected tactic");
        let position = expansion::position_at_offset(source, offset);
        let expanded =
            expand_c0_tactic_source_at(source, &[], position.line, position.column).unwrap();
        assert!(expanded.contains("have x == x by {"), "{expanded}");
        assert!(!expanded.contains("have x == x;"), "{expanded}");
        verify_c0_sources(&expanded, &[]).expect("the expanded proof should recheck");
    }
}

/// `by T(args);` is `by { T(args); }` without its braces. The source tools
/// address a proof's tactics through its block, so each of them must see the
/// one-tactic form as that block: every smart tactic in the proof below
/// expands and rechecks, wherever the one-tactic proofs stand.
#[test]
fn batch_expansion_wraps_one_tactic_arithmetic_proofs() {
    let c = "int nested(int x) { return x; }";
    let source = r#"
verifying "short.c";
int32 nested(int32 x) {
    requires 0 <= to_integer(x);
    ensures result == x;
} by {
    execute();
    have 0 <= to_integer(x) + 1 by arithmetic() using { 0 <= to_integer(x); };
    have 0 <= to_integer(x) + 2 by arithmetic() using { 0 <= to_integer(x); };
    have x == x by normalize();
    simp();
}
"#;
    let sources = [("short.c", c)];
    verify_c0_sources(source, &sources).expect("the short arithmetic proofs verify");
    let positions = source
        .match_indices("arithmetic()")
        .map(|(offset, _)| expansion::position_at_offset(source, offset))
        .collect::<Vec<_>>();
    let expanded = expansion::expand_tactics_source_at(
        source,
        &ProgramInputs::Bundle(sources.to_vec()),
        &positions,
    )
    .expect("the batch expands both arithmetic proofs");
    assert!(
        expanded.source.contains("arithmetic_certificate"),
        "{}",
        expanded.source
    );
    assert!(expanded.source.contains("have x == x by normalize();"));
    verify_c0_sources(&expanded.source, &sources)
        .expect("the batch's structured certificates must parse and recheck");
}

#[test]
fn expansion_reads_a_one_tactic_proof_as_its_block() {
    let source = r#"
theorem helper(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by assumption();
}

theorem one_tactic_proofs(x: int32) {
    requires 0 <= x;
    ensures 0 <= x and x == x by simp();
    ensures 0 <= x by apply(helper(x));
    ensures 0 <= x and x == x by {
        have x == x by normalize();
        have 0 <= x by apply(helper(x));
        have 0 <= x and x == x by simp();
        simp();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("the one-tactic proofs should verify");
    let smart = [
        "simp();\n    ensures 0 <= x by apply",
        "apply(helper(x));\n    ensures 0 <= x and x == x by {",
        "apply(helper(x));\n        have 0 <= x and x == x",
        "simp();\n        simp();",
        "simp();\n    }",
    ];
    for needle in smart {
        let offset = source
            .find(needle)
            .unwrap_or_else(|| panic!("expected `{needle}` in the source"));
        let position = expansion::position_at_offset(source, offset);
        let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column)
            .unwrap_or_else(|error| panic!("expanding at `{needle}`: {}", error.message()));
        assert_ne!(expanded, source, "expanding at `{needle}` changed nothing");
        verify_c0_sources(&expanded, &[]).unwrap_or_else(|error| {
            panic!(
                "the proof expanded at `{needle}` must recheck: {}\n{expanded}",
                error.message()
            )
        });
    }

    // An in-place expansion of a one-tactic proof writes the braces the
    // expanded form needs, and leaves the other one-tactic proofs as written.
    let offset = source.find("apply(helper(x));\n    ensures").unwrap();
    let position = expansion::position_at_offset(source, offset);
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column).unwrap();
    assert!(
        expanded.contains("ensures 0 <= x by {\n        apply(helper(x)) using {"),
        "{expanded}"
    );
    assert!(
        expanded.contains("have x == x by normalize();"),
        "{expanded}"
    );
}

/// The inventory `click audit` walks is the same whether a one-tactic proof
/// is written with its braces or without.
#[test]
fn smart_site_inventory_is_the_same_for_a_one_tactic_proof_and_its_block() {
    let without = r#"
theorem helper(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by assumption();
}

theorem one_tactic_proofs(x: int32) {
    requires 0 <= x;
    ensures 0 <= x and x == x by simp();
    ensures 0 <= x by apply(helper(x));
    ensures 0 <= x and x == x by {
        have 0 <= x and x == x by simp();
        simp();
    }
}
"#;
    let with = without
        .replace("by assumption();", "by { assumption(); }")
        .replace("by simp();", "by { simp(); }")
        .replace("by apply(helper(x));", "by { apply(helper(x)); }");
    assert_ne!(with, without);
    let inventory = |source: &str| {
        c0_smart_tactic_source_sites(source, &[])
            .unwrap()
            .into_iter()
            .map(|site| (site.claim_label, site.source_index, site.tactic_name))
            .collect::<Vec<_>>()
    };
    let sites = inventory(without);
    assert!(!sites.is_empty(), "the proof has smart tactics to find");
    assert_eq!(sites, inventory(&with));
}

#[test]
fn smart_site_inventory_includes_nested_have_bodies_without_container_aliases() {
    let source = r#"
theorem helper(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by { assumption(); }
}
theorem nested_sites(x: int32) {
    requires 0 <= x;
    ensures 0 <= x by { apply(helper(x)); }
    ensures 0 <= x by {
        have 0 <= x by {
            have 0 <= x by { apply(helper(x)); }
            apply(helper(x));
            assumption();
        }
        assumption();
    }
    ensures 0 <= x and x == x by {
        have 0 <= x and x == x by { simp(); }
        simp();
    }
}
"#;
    verify_c0_sources(source, &[]).unwrap();
    let sites = c0_smart_tactic_source_sites(source, &[]).unwrap();
    assert_eq!(
        sites
            .iter()
            .map(|site| (site.claim_label.as_str(), site.tactic_name.as_str()))
            .collect::<Vec<_>>(),
        vec![
            ("nested_sites.ensures_0", "apply"),
            ("nested_sites.ensures_1", "apply"),
            ("nested_sites.ensures_1", "apply"),
            ("nested_sites.ensures_2", "have"),
            ("nested_sites.ensures_2", "simp"),
        ]
    );
    // Both nested applications belong to the same claim-level `have`, but
    // each must have its own selectable source position.
    assert_eq!(sites[1].source_index, sites[2].source_index);
    assert_ne!(sites[1].position, sites[2].position);
    for site in sites {
        let expanded =
            expand_c0_tactic_source_at(source, &[], site.position.line, site.position.column)
                .unwrap_or_else(|error| {
                    panic!(
                        "{} at {:?}: {}",
                        site.tactic_name,
                        site.position,
                        error.message()
                    )
                });
        assert_ne!(expanded, source);
        verify_c0_sources(&expanded, &[])
            .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    }
}

/// A user tactic's proof is checked with an ending the checker supplies: one
/// step over the empty procedure's `return` and an `assumption` per claim.
/// That ending cannot be written in a tactic's proof, so whole-claim
/// expansion must leave it out; with it, the expanded proof is refused for
/// using `step`.
#[test]
fn whole_claim_expansion_of_a_user_tactic_omits_the_supplied_ending() {
    let (click, sources) = mdtest_sources("mdtests/user_tactic_reshapes_owned_resources.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source_by_label(&click, &sources, "divide.contract")
        .unwrap_or_else(|error| panic!("{}", error.message()));
    let tactic = &expanded[expanded.find("tactic divide(").unwrap()..];
    let proof = &tactic[..tactic.find("\n}\n").unwrap()];
    assert!(!proof.contains("step();"), "{proof}");
    assert!(proof.contains("have y.tag == 7 by {"), "{proof}");
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

/// Refuted helper arms have no generated return/postcondition suffix. Both
/// certification and whole-claim expansion must preserve their contradiction.
#[test]
fn whole_claim_expansion_of_a_user_tactic_preserves_refuted_arms() {
    let (click, sources) = mdtest_sources("mdtests/user_tactic_match_refutes_impossible_arm.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source_by_label(&click, &sources, "keep.contract")
        .unwrap_or_else(|error| panic!("{}", error.message()));
    assert!(expanded.contains("contradiction("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

/// Whole-claim expansion rebuilds a proof `match` from the paths through its
/// arms. Each claim here verifies, and its expansion must too.
#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn whole_claim_expansion_of_proof_matches_rechecks() {
    for (mdtest, claim) in [
        ("proof_match_after_c_step", "read_after_step.contract"),
        ("loop_decreases_strict_descendant", "countdown.contract"),
        (
            "loop_preserve_branch_tactic",
            "chain_countdown_decided.contract",
        ),
        ("loop_preserve_branch_tactic", "chain_countdown.contract"),
        (
            "loop_body_proof_match_ensuring_inside_a_proof_if",
            "spin.contract",
        ),
    ] {
        let (click, sources) = mdtest_sources(&format!("mdtests/{mdtest}.md"));
        let sources = sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let expanded = expand_c0_claim_source_by_label(&click, &sources, claim)
            .unwrap_or_else(|error| panic!("expanding `{claim}`: {}", error.message()));
        verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
            panic!(
                "expanded `{claim}` must recheck: {}\n{expanded}",
                error.message()
            )
        });
        if claim == "chain_countdown.contract" {
            let position = expansion::position_at_offset(
                &expanded,
                expanded
                    .find("ensures 1 == 1;")
                    .expect("the selected contract"),
            );
            let (checked, planning) =
                crate::surface::proof::count_planning_statement_transitions(|| {
                    verify_c0_sources_at(&expanded, &sources, position.line, position.column)
                });
            checked.expect("the scoped preservation certificate must cold recheck");
            assert_eq!(
                planning, 0,
                "expanded preservation must not invoke planning"
            );
            let forged = expanded.replacen("ensures 1 == 1;", "ensures 1 == 2;", 1);
            verify_c0_sources(&forged, &sources)
                .expect_err("retaining proof cases cannot certify a false contract");
        }
    }
}

/// The tactics written after execution inside a match arm read the arm's
/// bindings, so the expansion keeps them inside that arm.
#[test]
fn whole_claim_expansion_keeps_post_execution_tactics_in_their_match_arm() {
    let (click, sources) = mdtest_sources("mdtests/proof_match_after_c_step.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded =
        expand_c0_claim_source_by_label(&click, &sources, "read_after_step.contract").unwrap();
    let proof = &expanded[expanded.rfind("} by {").unwrap()..];
    let arm = proof.find("Maybe::Some(value) => {").expect("the live arm");
    let fold = proof
        .find("let c = fold(cell(node), { model: Maybe::Some(value) });")
        .expect("the arm's fold");
    let arm_end = arm + proof[arm..].find("\n        }\n").expect("the arm closes");
    assert!(arm < fold && fold < arm_end, "{proof}");
}

/// A nested proof `match` is rebuilt where its own path took it. The arms of
/// an enclosing match are checked one after another on one proof, so the
/// position must count the steps of this arm's path, not those of the arms
/// checked before it; otherwise the tactic that binds the nested scrutinee
/// lands inside the nested match.
#[test]
fn whole_claim_expansion_keeps_tactics_before_a_nested_match() {
    let (click, sources) = mdtest_sources("mdtests/loop_decreases_strict_descendant.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source_by_label(&click, &sources, "countdown.contract").unwrap();
    let proof = &expanded[expanded.rfind("} by {").unwrap()..];
    let binds = proof
        .find("let { rest: r } = unfold(c);")
        .expect("the tactic that binds `r`");
    let nested = proof.find("match r.model {").expect("the nested match");
    assert!(binds < nested, "{proof}");
    assert_eq!(
        proof.matches("let { rest: r } = unfold(c);").count(),
        1,
        "{proof}"
    );
}

/// A call step that lends no resource instance is written with an empty
/// binder map. The map is what makes it a call step: printed without it,
/// `step(inner(holder))` reads as a named-contract step and the expanded
/// proof no longer parses.
#[test]
fn whole_claim_expansion_keeps_a_call_steps_empty_binder_map() {
    let (click, sources) = mdtest_sources("mdtests/mutex_live_contract.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    for claim in ["keep.contract", "run.contract"] {
        let expanded = expand_c0_claim_source_by_label(&click, &sources, claim)
            .unwrap_or_else(|error| panic!("expanding `{claim}`: {}", error.message()));
        verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
            panic!(
                "expanded `{claim}` must recheck: {}\n{expanded}",
                error.message()
            )
        });
    }
    let expanded = expand_c0_claim_source_by_label(&click, &sources, "keep.contract").unwrap();
    assert!(expanded.contains("step(inner(holder), {});"), "{expanded}");
}

/// A theorem with a type parameter is checked at a rigid type standing for
/// any type. Expanding one of its tactics verifies that theorem alone, and
/// must check it the same way; without the rigid type the proof cannot be
/// lowered at all.
#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn a_tactic_in_a_generic_theorem_expands() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("examples/modeled-binary-tree/modeled_binary_tree.click");
    let source = std::fs::read_to_string(&path).unwrap();
    let sources = crate::cli::read_verifying_sources(&path, &source).unwrap();
    let c_sources = crate::cli::source_refs(&sources);
    let theorem = source.find("theorem tree_mirror_twice<T>(").unwrap();
    for needle in ["simp();", "apply(ih(left));"] {
        let offset = theorem + source[theorem..].find(needle).unwrap();
        let position = expansion::position_at_offset(&source, offset);
        let expanded =
            expand_c0_tactic_source_at(&source, &c_sources, position.line, position.column)
                .unwrap_or_else(|error| panic!("expanding `{needle}`: {}", error.message()));
        assert_ne!(expanded, source, "expanding `{needle}` changed nothing");
    }
}

/// A proof `if` written after `execute()` in a claim's own proof must be in
/// the whole-claim expansion: each arm closes the disjunction from its own
/// case fact, and without the `if` neither side is a fact.
#[test]
fn whole_claim_expansion_keeps_a_proof_if_after_execution() {
    let (click, sources) = mdtest_sources("mdtests/proof_if_cases.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded =
        expand_c0_claim_source_by_label(&click, &sources, "sign_after_execution.ensures_0")
            .unwrap_or_else(|error| panic!("{}", error.message()));
    let function = &expanded[expanded
        .find("int32 sign_after_execution(int32 x) {")
        .unwrap()..];
    let proof = &function[..function.find("\n}\n").unwrap()];
    assert!(proof.contains("if result <= 0 {"), "{proof}");
    assert!(!proof.contains("simp();"), "{proof}");
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

/// After execution, `witness` or `intro` opens a claim's own proof and the
/// closing `simp` continues it. A grouped proof's expansion must include what
/// that `simp` added, or it stops at the tactic that opened the claim.
#[test]
fn whole_claim_expansion_closes_a_claim_opened_after_execution() {
    for (mdtest, claim, opener) in [
        (
            "grouped_top_level_existentials",
            "identity.contract",
            "witness { j: k }",
        ),
        (
            "intro_as_in_a_function_proof",
            "keep.contract",
            "intro() as below;",
        ),
    ] {
        let (click, sources) = mdtest_sources(&format!("mdtests/{mdtest}.md"));
        let sources = sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let expanded = expand_c0_claim_source_by_label(&click, &sources, claim)
            .unwrap_or_else(|error| panic!("expanding `{claim}`: {}", error.message()));
        let after_opener = &expanded[expanded.find(opener).expect("the opening tactic")..];
        let rest = &after_opener[opener.len()..after_opener.find("\n}").unwrap()];
        assert!(
            !rest.trim().is_empty(),
            "the expanded proof of `{claim}` stops at `{opener}`:\n{expanded}"
        );
        verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
            panic!(
                "expanded `{claim}` must recheck: {}\n{expanded}",
                error.message()
            )
        });
    }
}

/// A C `if` with one reachable arm is expanded as a branch whose other arm is
/// empty, and the proof continues after it. Entering the continuation there
/// must record its first statement's entry as a step onto it would, because
/// the expanded branch that follows names that point in its condition.
#[test]
fn whole_claim_expansion_continues_after_a_branch_with_one_reachable_arm() {
    let c_source = r#"
int early(int x) {
    if (x == 0) {
        return 0;
    }
    if (x == 1) {
        return 0;
    }
    return 1;
}
"#;
    let click = r#"
verifying "early.c";

int32 early(int32 x) {
    requires x != 0;
    ensures result == 0 or result == 1;
} by {
    branch {
        step();
        simp();
    } else {}
    branch {
        step();
        simp();
    } else {}
    step();
    simp();
}
"#;
    let sources = [("early.c", c_source)];
    let verified_for_label =
        verify_c0_sources(click, &sources).expect("the proof with an unreachable arm verifies");
    let expanded = expand_checked_function_claim(click, &verified_for_label, "early.contract")
        .unwrap_or_else(|error| panic!("{}", error.message()));
    assert!(
        expanded.contains("if at(statement(3).entry, x) == at(statement(3).entry, 1) {"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn whole_claim_expansion_retains_logical_steps_after_terminal_c_steps() {
    let (click, sources) = mdtest_sources("mdtests/sort3_sorted.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let verified_for_label =
        verify_c0_sources(&click, &sources).expect("the original sorting proof verifies");
    let expanded = expand_checked_function_claim(&click, &verified_for_label, "sort3.sorted")
        .unwrap_or_else(|error| panic!("{}", error.message()));
    assert!(expanded.contains("unfold(sorted_range);"), "{expanded}");
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c0_sources(&expanded, &sources)
    });
    result.unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    assert_eq!(
        planning, 0,
        "the expansion must cold recheck without planning"
    );
    let last_step = expanded.rfind("step();").expect("expanded C return step");
    let mut incomplete = expanded.clone();
    incomplete.replace_range(last_step..last_step + "step();".len(), "");
    verify_c0_sources(&incomplete, &sources)
        .expect_err("logical steps cannot replace an omitted C transition");
    let false_contract = expanded.replace("p[i] <= p[j]", "p[i] > p[j]");
    verify_c0_sources(&false_contract, &sources)
        .expect_err("a false sorting postcondition must remain rejected");
}

#[test]
fn context_free_disjunction_simp_expands_choice_and_rechecks() {
    for (goal, choice) in [
        ("1 == 1 or 2 == 3", "assumption();"),
        ("2 == 3 or 1 == 1", "assumption();"),
    ] {
        let source = format!(
            r#"
theorem choose_reflexive_arm() {{
    ensures {goal} by {{ simp(); }}
}}
"#
        );
        verify_c0_sources(&source, &[]).expect("smart disjunction proof should verify");
        let offset = source.find("simp();").expect("expected smart tactic");
        let position = expansion::position_at_offset(&source, offset);
        let expanded =
            expand_c0_tactic_source_at(&source, &[], position.line, position.column).unwrap();
        assert!(expanded.contains("have 1 == 1 by"), "{expanded}");
        assert!(expanded.contains(choice), "{expanded}");
        assert!(!expanded.contains("simp();"), "{expanded}");
        verify_c0_sources(&expanded, &[])
            .expect("expanded disjunction choice should independently recheck");
    }
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn deferred_preservation_simp_expands_at_its_original_source_site() {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/owned-vector/vector.click");
    let source = std::fs::read_to_string(&path).unwrap();
    let sources = crate::cli::read_verifying_sources(&path, &source).unwrap();
    let c_sources = crate::cli::source_refs(&sources);
    verify_c0_sources_functions(&source, &c_sources, vec!["vector_copy".into()]).unwrap();
    let function = source.find("int32 vector_copy(").unwrap();
    let preserve = function + source[function..].find("preserve by {").unwrap();
    let offset = preserve + source[preserve..].find("simp();").unwrap();
    let position = expansion::position_at_offset(&source, offset);
    let expanded =
        expand_c0_tactic_source_at(&source, &c_sources, position.line, position.column).unwrap();
    assert_ne!(source, expanded);
    verify_c0_sources_functions(&expanded, &c_sources, vec!["vector_copy".into()]).unwrap();
}

#[test]
fn signed_unsigned_compound_arithmetic_expands_and_rechecks() {
    let source = r#"
theorem unsigned_compound(n: int32) {
    requires 0 <= n + 1;
    requires n + 1 <= 536870911;
    ensures ((uint32)(n + 1)) <= 1073741823u32 by {
        arithmetic() using {
            0 <= n + 1;
            n + 1 <= 536870911;
        }
    }
}
"#;
    let verified =
        verify_c0_sources(source, &[]).expect("compound unsigned arithmetic should verify");
    for theorem in &verified {
        assert_no_legacy_arithmetic_leaves(
            &theorem
                .expanded_proof_certificate()
                .expect("compound arithmetic should retain an expanded certificate"),
        );
    }
    let expanded = expand_c0_claim_source_by_label(source, &[], "unsigned_compound.ensures_0")
        .expect("compound unsigned arithmetic should expand to a source certificate");
    assert!(
        expanded.contains("arithmetic_certificate signed_int32"),
        "{expanded}"
    );
    assert!(
        expanded.contains("interval_from_affine_direct"),
        "{expanded}"
    );

    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c0_sources(&expanded, &[])
    });
    result.expect("expanded vector_grow should independently recheck");
    assert_eq!(
        planning, 0,
        "explicit certificate recheck must not plan: {expanded}"
    );

    let tampered = expanded.replacen("interval_from_affine_direct", "interval_from_affine", 1);
    verify_c0_sources(&tampered, &[])
        .expect_err("removing the direct compound-evidence rule must invalidate the proof");
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn arithmetic_producers_retain_only_structural_certificates() {
    let pure = r#"
theorem pure_arithmetic_producer(n: int32) {
    requires n <= 10;
    ensures n <= 10 by { arithmetic() using { n <= 10; } }
}
"#;
    let verified = verify_click_theorems(pure).expect("pure arithmetic should verify");
    assert_no_legacy_pure_arithmetic_leaves(&verified);

    for (fixture_name, claim, replacement) in [
        (
            "mdtests/c_grouped_contract_arithmetic_closer.md",
            "bump",
            None,
        ),
        (
            "mdtests/c_pointer_local_loop_invariant.md",
            "last_element",
            None,
        ),
        (
            "mdtests/aligned_symbolic_displacement.md",
            "element_is_aligned",
            Some((
                "    simp();\n}",
                "    have aligned(p + i, 8) by { simp(); }\n    simp();\n}",
            )),
        ),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(fixture_name);
        let source = std::fs::read_to_string(&path).unwrap();
        let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let click_source = fixture.click_source.as_deref().unwrap();
        let click_source = replacement.map_or_else(
            || click_source.to_string(),
            |(from, to)| click_source.replace(from, to),
        );
        let verified = verify_c0_sources(&click_source, &sources)
            .unwrap_or_else(|error| panic!("{fixture_name}: {}", error.message()));
        assert_no_legacy_c_arithmetic_leaves(&verified);
        let expanded = expand_c0_claim_source(&click_source, &sources, claim, CProofClaim::Grouped)
            .unwrap_or_else(|error| panic!("{fixture_name}: {}", error.message()));
        assert!(
            !expanded.contains("arithmetic()"),
            "{fixture_name}: {expanded}"
        );
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{fixture_name}: {}", error.message()));
    }
}

// The join's exported fact must remain writable after proof-local resolution:
// the old metadata made this valid snapshot rewrite expand to a literal `…`.
#[test]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn branch_interface_model_pointer_snapshot_rewrite_expands_and_rechecks() {
    let (source, c) = mdtest_sources("mdtests/branch_interface_keeps_model_pointer_names.md");
    let c = c
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source(&source, &c, "put", CProofClaim::Grouped)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    verify_c0_sources(&expanded, &c).unwrap_or_else(|error| panic!("{}", error.message()));
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn branch_interface_fixture_proofs_verify_expand_and_recheck() {
    for name in [
        "frontier_branch_return.md",
        "proof_branch_memory_continuation.md",
        "proof_branch_pointer_local.md",
        "step_nested_branches.md",
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(name);
        let fixture = crate::cli::read_mdtest(&path).unwrap();
        let source = fixture.click_source.as_deref().unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        verify_c0_sources(source, &sources)
            .unwrap_or_else(|error| panic!("{name}: {}", error.message()));
        // The nested-branch fixture is already fully expanded. For the others,
        // expand their closing tactic and reparse/recheck the full proof.
        if let Some(offset) = source.rfind("simp();") {
            let position = expansion::position_at_offset(source, offset);
            let expanded =
                expand_c0_tactic_source_at(source, &sources, position.line, position.column)
                    .unwrap();
            verify_c0_sources(&expanded, &sources)
                .unwrap_or_else(|error| panic!("{name}: {}", error.message()));
        }
    }
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn branch_interface_service_simp_expands_and_rechecks() {
    let source = include_str!("../../../examples/perpetual-service/perpetual_service.click");
    let sources = [
        (
            "service_init.c",
            include_str!("../../../examples/perpetual-service/service_init.c"),
        ),
        (
            "service_step.c",
            include_str!("../../../examples/perpetual-service/service_step.c"),
        ),
        (
            "service_run.c",
            include_str!("../../../examples/perpetual-service/service_run.c"),
        ),
    ];
    verify_c0_sources(source, &sources).unwrap();
    let start = source.find("int32 service_step").unwrap();
    let offset = start + source[start..].find("simp();").unwrap();
    let position = expansion::position_at_offset(source, offset);
    let expanded =
        expand_c0_tactic_source_at(source, &sources, position.line, position.column).unwrap();
    verify_expanded_function_source(source, &expanded, &sources, "service_step").unwrap_or_else(
        |error| {
            panic!(
                "{}\n{}",
                error.message(),
                expanded
                    .lines()
                    .skip(position.line - 1)
                    .take(8)
                    .collect::<Vec<_>>()
                    .join("\n")
            )
        },
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn callback_branch_ground_premises_verify_expand_and_recheck() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/c_step_contract_frontier_branch.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion = verify_c0_sources(source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(source, &verified_for_expansion, "invoke").unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn serialized_loop_premises_reject_a_changed_snapshot_or_polarity() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/loop_stable_invariant_export.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded =
        expand_c0_claim_source(source, &sources, "fill_tail", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).expect("serialized loop proof must reverify");

    let original = "extract(at(statement(3).entry, i) <= at(statement(3).entry, n));";
    assert!(expanded.contains(original), "{expanded}");
    for corrupted in [
        expanded.replacen(
            original,
            "extract(at(loop(0).exit, i) <= at(statement(3).entry, n));",
            1,
        ),
        expanded.replacen(
            original,
            "extract(not at(statement(3).entry, i) <= at(statement(3).entry, n));",
            1,
        ),
    ] {
        verify_c0_sources(&corrupted, &sources)
            .expect_err("a changed serialized premise cannot reverify");
    }
}

#[test]
#[ignore = "nightly: 5.3s in the parallel gate"]
fn machine_population_count_rewrites_keep_their_type_in_integer_files() {
    let (source, sources) =
        mdtest_sources("mdtests/a_consumed_member_bound_on_an_entry_count_is_cited.md");
    let source_refs = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&source, &source_refs).unwrap();
    let expanded = expand_claim_by_label(
        None,
        &source,
        &ProgramInputs::Bundle(source_refs.clone()),
        "pool_checkout.contract",
        None,
    )
    .unwrap();
    without_implicit_auto(|| verify_c0_sources(&expanded.source, &source_refs)).unwrap();
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn return_population_proofs_expand_without_effect_clauses() {
    for (fixture_name, functions) in [
        (
            "counted_resource_refcount_transitions.md",
            vec!["object_retain", "object_release_nonfinal"],
        ),
        (
            "counted_resource_population_lifetime.md",
            vec!["object_init", "object_finish"],
        ),
        (
            "consumed_population_count_in_ensured_predicate.md",
            vec!["consume_population"],
        ),
        (
            "population_cleanup_consumes_whole_quantity.md",
            vec!["cleanup"],
        ),
        (
            "resource_count_predicate_snapshot.md",
            vec!["object_retain"],
        ),
        (
            "resource_pattern_counts_cross_contracts.md",
            vec!["pool_checkout", "pool_return", "pool_roundtrip"],
        ),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(fixture_name);
        let fixture = crate::cli::read_mdtest(&path).unwrap();
        let source = fixture.click_source.as_deref().unwrap();
        let inputs = crate::cli::prepare_mdtest_inputs(&fixture).unwrap();
        let project = crate::cli::read_mdtest_project_if_needed(&path, source, &inputs).unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        project
            .as_ref()
            .map_or_else(
                || verify_c0_sources(source, &sources),
                |project| verify_c0_project(project, &sources),
            )
            .unwrap_or_else(|error| panic!("{fixture_name}: {}", error.message()));
        for function in functions {
            let expanded = project
                .as_ref()
                .map_or_else(
                    || expand_c0_claim_source(source, &sources, function, CProofClaim::Grouped),
                    |project| {
                        expand_project_claim_source_by_label(
                            project,
                            &ProgramInputs::Bundle(sources.to_vec()),
                            &format!("{function}.contract"),
                        )
                    },
                )
                .unwrap();
            project
                .as_ref()
                .map_or_else(
                    || verify_c0_sources(&expanded, &sources),
                    |project| verify_c0_project(&project.with_entry_source(&expanded), &sources),
                )
                .unwrap_or_else(|error| panic!("{fixture_name}: {}\n{expanded}", error.message()));
        }
    }
}

#[test]
fn return_population_count_is_not_an_assumed_invariant() {
    let c_source =
        "struct object { int32 refs; }; struct object* retain(struct object* obj) { return obj; }";
    for proof in [
        "execute(); simp();",
        "unfold(reference(obj)); execute(); simp();",
        "unfold(reference(obj)); execute(); fold(reference(obj)); simp();",
        "open(reference(obj)) { execute(); } simp();",
    ] {
        let source = format!(
            r#"
authorized resource reference(obj: struct object*) {{
    owns obj->refs;
    fact obj->refs == count(reference(obj));
}}
verifying "retain.c";
struct object* retain(struct object* obj) {{
    requires count(reference(obj)) < 2147483647;
    owns reference(obj);
    produces reference(obj);
    ensures obj->refs == count(reference(obj));
    ensures result == obj;
}} by {{ {proof} }}
"#
        );
        assert!(
            verify_c0_sources(&source, &[("retain.c", c_source)]).is_err(),
            "accepted an unchanged stored count with {proof}"
        );
    }
}

#[test]
fn signed_antisymmetry_simp_expands_to_checked_arithmetic() {
    let source = "theorem bounded_equal(i: int32) { requires 0 <= i; requires i <= 0; ensures i == 0 by { simp(); } }";
    verify_c0_sources(source, &[]).unwrap();
    let position = expansion::position_at_offset(source, source.find("simp();").unwrap());
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column).unwrap();
    assert!(
        expanded.contains("equal_from_bounds 0, 1 => i == 0;"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[]).unwrap();
    let tampered = expanded.replace("requires i <= 0;", "requires i <= 1;");
    assert!(verify_c0_sources(&tampered, &[]).is_err());
}

#[test]
fn program_entry_signed_resource_shadowing_expands() {
    let sources = [(
        "main.c",
        "int p = 7; int read_cell(int *p) { return *p; } int main(void) { return read_cell(&p); }",
    )];
    let helper = "by { unfold(cell(p)); execute(); fold(cell(p)); simp(); }";
    let main = "by { fold(cell(&p)); execute(); simp(); }";
    let source = format!(
        r#"resource cell(p: int32*) {{ owns p[0..1]; }}
verifying "main.c";
int read_cell(int *p) {{ owns cell(p); ensures result == old(p[0]); }} {helper}
int main() {{ ensures result == 7; }} {main}"#
    );
    let verified = verify_c0_sources(&source, &sources).unwrap();
    let mut expanded = source.clone();
    for (name, original) in [("read_cell", helper), ("main", main)] {
        let theorem = verified
            .iter()
            .find(|theorem| theorem.function_block.signature().name() == name)
            .unwrap();
        expanded = expanded.replacen(original, &theorem.expanded_proof_source().unwrap(), 1);
    }
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn program_entry_resource_bindings_expand_and_reverify() {
    for (c_type, click_type, suffix) in [("unsigned int", "uint32", "u32")] {
        let c_source = format!(
            "{c_type} state[2] = {{7,9}}; {c_type} read_pair({c_type} *p) {{ return p[0] + p[1]; }} int main(void) {{ return read_pair(state); }}"
        );
        let helper_proof = "by { unfold(pair(p)); execute(); fold(pair(p)); simp(); }";
        let main_proof = "by { fold(pair(state)); execute(); simp(); }";
        let click_source = format!(
            r#"
resource pair(p: {click_type}*) {{ owns p[0..2]; }}
verifying "main.c";
{c_type} read_pair({c_type} *p) {{
    requires viewable(p[0..2]); owns pair(p);
    ensures result == old(p[0]) + old(p[1]);
}} {helper_proof}
int main() {{ ensures result == 16; }} {main_proof}
"#
        );
        let sources = [("main.c", c_source.as_str())];
        let verified = verify_c0_sources(&click_source, &sources).unwrap();
        let mut rewritten = click_source.clone();
        for (name, original) in [("read_pair", helper_proof), ("main", main_proof)] {
            let theorem = verified
                .iter()
                .find(|theorem| theorem.function_block.signature().name() == name)
                .unwrap();
            rewritten = rewritten.replacen(original, &theorem.expanded_proof_source().unwrap(), 1);
        }
        verify_c0_sources(&rewritten, &sources).unwrap();
        // Repeated folding may be idempotent; requiring the same exclusive
        // resource twice must still be rejected.
        let duplicate = click_source.replace("owns pair(p);", "owns pair(p); owns pair(p);");
        assert!(verify_c0_sources(&duplicate, &sources).is_err());
        let mismatched = click_source.replace("pair(p: uint32*)", "pair(p: int32*)");
        assert!(verify_c0_sources(&mismatched, &sources).is_err());
        let wrong = click_source.replace("result == 16", "result == 17");
        assert!(verify_c0_sources(&wrong, &sources).is_err(), "{suffix}");
    }
}

#[test]
fn composite_uint64_range_expansion_preserves_type() {
    let c_source = "unsigned long read_pair(unsigned long *p) { return p[0] + p[1]; }";
    let click_source = r#"resource pair(p: uint64*) { owns p[0..2]; }
verifying "main.c";
unsigned long read_pair(unsigned long *p) {
    requires viewable(p[0..2]); owns pair(p);
    ensures result == old(p[0]) + old(p[1]);
} by { unfold(pair(p)); execute(); fold(pair(p)); simp(); }"#;
    let sources = [("main.c", c_source)];
    let verified = verify_c0_sources(click_source, &sources).unwrap();
    let expanded = click_source.replacen(
        "by { unfold(pair(p)); execute(); fold(pair(p)); simp(); }",
        &verified[0].expanded_proof_source().unwrap(),
        1,
    );
    verify_c0_sources(&expanded, &sources).unwrap();
    let mismatched = click_source.replace("pair(p: uint64*)", "pair(p: uint32*)");
    assert!(verify_c0_sources(&mismatched, &sources).is_err());
}

#[test]
fn program_entry_typed_dereference_snapshots_expand_and_reverify() {
    for (c_type, suffix) in [("unsigned int", "u32"), ("unsigned long", "u64")] {
        let c_source = format!("{c_type} bump({c_type} *p) {{ *p += 1; return *p; }}");
        let click_source = format!(
            r#"verifying "main.c";
{c_type} bump({c_type} *p) {{
    requires viewable(p[0..1]); owns p[0..1];
    ensures *p == old(*p) + 1{suffix};
    ensures *p == p[0];
    ensures old(*p) == old(p[0]);
}} by {{ execute(); simp(); }}"#
        );
        let sources = [("main.c", c_source.as_str())];
        let verified = verify_c0_sources(&click_source, &sources).unwrap();
        let rewritten = click_source.replacen(
            "by { execute(); simp(); }",
            &verified[0].expanded_proof_source().unwrap(),
            1,
        );
        verify_c0_sources(&rewritten, &sources).unwrap();
        let wrong = click_source.replace(&format!("*p == old(*p) + 1{suffix}"), "*p == old(*p)");
        assert!(verify_c0_sources(&wrong, &sources).is_err());
    }
}

#[test]
fn program_entry_expansion_reverifies() {
    let c_source = "int state = 7; int main(void) { state += 1; return state; }";
    let click_source =
        "verifying \"main.c\"; int main() { ensures result == 8; } by { execute(); simp(); }";
    let sources = [("main.c", c_source)];
    let verified = verify_c0_sources(click_source, &sources).unwrap();
    let expanded = verified[0].expanded_proof_source().unwrap();
    let rewritten = click_source.replacen("by { execute(); simp(); }", &expanded, 1);
    verify_c0_sources(&rewritten, &sources).unwrap();
}

#[test]
fn program_entry_collects_data_only_private_and_uncalled_local_storage() {
    let sources = [
        ("data.c", "static int private_state = 11; int zero;"),
        (
            "main.c",
            "extern int zero; int unused(void) { static int local = 5; return local; } int main(void) { return zero; }",
        ),
    ];
    let click_source = "verifying \"data.c\"; verifying \"main.c\"; int main() { ensures result == 0; } by { execute(); simp(); }";
    let file = crate::surface::verification::parse_c0_click_file(click_source, &sources).unwrap();
    let parsed =
        crate::surface::verification::parse_verified_sources(&file, &sources.into_iter().collect())
            .unwrap();
    let startup = parsed["main"].1.program_entry_state.as_ref().unwrap();
    assert_eq!(startup.resources().facts().len(), 3);
    assert!(parsed["unused"].1.program_entry_state.is_none());
    verify_c0_sources(click_source, &sources).unwrap();
}

#[test]
fn const_char_return_expansion_preserves_target_and_qualification() {
    let c_source = "const char *version(void) { return \"0.17\"; }";
    let click_source = r#"verifying "version.c";
const char *version() {
    ensures viewable(result[0..5]);
    ensures result[0] == '0';
    ensures result[4] == '\0';
} by { execute(); simp(); }"#;
    let sources = [("version.c", c_source)];
    let verified = verify_c0_sources(click_source, &sources).unwrap();
    let proof = verified[0].expanded_proof_source().unwrap();
    let expanded = click_source.replacen("by { execute(); simp(); }", &proof, 1);
    let checked = verify_c0_sources(&expanded, &sources).unwrap();
    assert!(
        checked
            .iter()
            .all(|theorem| { theorem.target() == crate::languages::c::target::CTarget::SUPPORTED })
    );
}

#[test]
fn source_locator_ignores_line_comments_and_preserves_literals() {
    let source =
        "// Click's ü } verifying \"fake.c\"\r\nverifying \"real#file.c\"; // \"unterminated";
    assert_eq!(
        verifying_source_paths(source).expect("comments must not become source tokens"),
        vec!["real#file.c"]
    );
}

#[test]
fn source_locator_line_comments_preserve_proof_expansion_offsets() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"// Click's proof: ü } identity() { "
verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
} by {
    execute(); // unmatched ' } "
    simp();
}
// trailing comment without newline: '"#;
    let sources = [("identity.c", c_source)];
    verify_c0_sources(click_source, &sources).expect("commented proof should verify");
    let offset = click_source.find("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("comments must not disturb proof source offsets");
    assert_eq!(&expanded[..offset], &click_source[..offset]);
    assert!(expanded.ends_with("// trailing comment without newline: '"));
    verify_c0_sources(&expanded, &sources).expect("expanded commented proof should verify");
}

#[test]
fn contract_refinement_expands_ordinary_helper_proofs() {
    let source = r#"
        theorem nonnegative_equal(x: int32, y: int32) {
            requires x >= 0;
            ensures y == x implies y >= 0 by { simp(); }
        }
        contract int32 Source(int32 x) {
            requires x >= 0;
            ensures result == x;
        }
        contract int32 Target(int32 x) {
            requires x >= 0;
            ensures result >= 0;
        }
        theorem lift(callback: int32 (*)(int32)) {
            requires Source(callback);
            ensures Target(callback) by {
                unfold(Source);
                unfold(Target);
                intro();
                have result == x implies result >= 0 by {
                    apply(nonnegative_equal(x, result));
                }
                simp();
            }
        }
    "#;
    verify_c0_sources(source, &[]).expect("ordinary refinement proof should verify");
    let position = expansion::position_at_offset(source, source.rfind("simp();").unwrap());
    let expanded = expand_c0_tactic_source_at(source, &[], position.line, position.column)
        .expect("refinement simp should emit its ordinary proof certificate");
    assert!(
        expanded.contains("apply(nonnegative_equal(x, result)) using"),
        "{expanded}"
    );
    assert_eq!(expanded.matches("simp();").count(), 1, "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("expanded refinement proof should verify");
}

#[test]
fn unsigned_narrowing_snapshot_expansion_reverifies() {
    let c_source = "struct state { unsigned long value; }; unsigned int take(struct state *p) { unsigned int result = p->value; p->value += 1; return result; }";
    let click_source = r#"
        verifying "take.c";
        unsigned int take(struct state *p) {
            requires viewable(p->value);
            owns p->value;
            ensures result == old((uint32)p->value);
            ensures p->value == old(p->value) + 1u64;
        } by { execute(); simp(); }
    "#;
    let verified =
        verify_c0_sources(click_source, &[("take.c", c_source)]).expect("narrowing proof verifies");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("narrowing proof has a printable certificate");
    let rewritten = click_source.replacen("by { execute(); simp(); }", &expanded, 1);
    verify_c0_sources(&rewritten, &[("take.c", c_source)])
        .unwrap_or_else(|error| panic!("{error:?}\n{rewritten}"));
}

#[test]
fn selected_post_execution_simp_waits_for_its_surface_closer() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                simp();
            }
        "#;
    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected simp");
    let line = click_source[..simp_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = simp_offset
        - click_source[..simp_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("selected post-execution simp should expand after finalization");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(
        expanded.contains("assumption();") || expanded.contains("normalize();"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("selected post-execution simp expansion should check");
}

#[test]
fn selected_post_execution_simp_keeps_the_surviving_execution_branch() {
    let c_source = r#"
            struct node {
                int32 value;
                struct node* next;
            };

            struct node* prepend(int32 value, struct node* tail) {
                struct node* node = malloc(sizeof(struct node));
                if (node == 0) {
                    return tail;
                }
                node->value = value;
                node->next = tail;
                return node;
            }
        "#;
    let click_source = r#"
            resource allocated_list(node: struct node*) {
                if node != 0 {
                    owns allocation(node, sizeof(struct node));
                    owns *node;
                    owns allocated_list(node->next);
                }
            }

            verifying "prepend.c";

            struct node* prepend(int32 value, struct node* tail) {
                consumes allocated_list(tail);
                produces allocated_list(result);
                ensures result == tail or result != 0;
                ensures result != tail implies result->value == value;
                ensures result != tail implies result->next == tail;
            } by {
                execute();
                if result == tail {
                    simp();
                } else {
                    fold(allocated_list(result));
                    simp();
                }
            }
        "#;
    let selected_simp = click_source
        .rfind("simp();")
        .expect("success branch should contain a simp");
    let position = expansion::position_at_offset(click_source, selected_simp);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("prepend.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the selected success-branch simp should expand");
    verify_c0_sources(&expanded, &[("prepend.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the selected success-branch simp expansion should check: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn returning_malloc_result_expands_to_checkable_statement_steps() {
    let c_source = r#"
            int32* allocate_int32s(int32 count) {
                int32* data;
                data = malloc(count * 4);
                return data;
            }
        "#;
    let click_source = r#"
            resource maybe_allocated_int32s(data: int32*, count: int32) {
                if data != 0 {
                    owns allocation(data, count * 4);
                    owns data[0..count];
                }
            }

            verifying "allocate_int32s.c";

            int32* allocate_int32s(int32 count) {
                requires 1 <= count;
                requires count <= 536870911;
                produces maybe_allocated_int32s(result, count);
            } by {
                execute();
                fold(maybe_allocated_int32s(result, count));
                simp();
            }
        "#;
    let execute = click_source
        .find("execute();")
        .expect("proof should contain the selected execute");
    let position = expansion::position_at_offset(click_source, execute);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("allocate_int32s.c", c_source)],
        position.line,
        position.column,
    )
    .expect("malloc-return execution should expand");
    assert!(!expanded.contains("execute();"), "{expanded}");
    assert!(expanded.contains("step()"), "{expanded}");
    verify_c0_sources(&expanded, &[("allocate_int32s.c", c_source)])
        .expect("expanded malloc-return statement steps should check");
}

#[test]
#[ignore = "nightly: 1.9s in the parallel gate"]
fn opaque_reallocation_execute_does_not_invent_an_identity_if() {
    let callee_source = r#"
            struct cell_owner {
                int32* data;
            };

            int32 replace_allocated_cell(struct cell_owner* owner) {
                int32* old_data;
                int32* new_data;

                old_data = owner->data;
                new_data = malloc(4);
                if (new_data == 0) {
                    return 0;
                }
                new_data[0] = 7;
                owner->data = new_data;
                free(old_data);
                return 1;
            }
        "#;
    let caller_source = r#"
            struct cell_owner {
                int32* data;
            };

            int32 replace_after_scoped_open(struct cell_owner* owner) {
                int32 replaced;

                replaced = replace_allocated_cell(owner);
                return replaced;
            }
        "#;
    let click_source = r#"
            resource allocated_cell(owner: struct cell_owner*) {
                owns owner->data;
                owns allocation(owner->data, 4);
                owns owner->data[0..1];
            }

            verifying "replace_allocated_cell.c";
            verifying "replace_after_scoped_open.c";

            int32 replace_allocated_cell(struct cell_owner* owner) {
                owns allocated_cell(owner);

                ensures result == 0 or result == 1;
                ensures result == 0 implies owner->data == old(owner->data);
            } by {
                unfold(allocated_cell(owner));
                execute();
                fold(allocated_cell(owner));
                simp();
            }

            int32 replace_after_scoped_open(struct cell_owner* owner) {
                owns allocated_cell(owner);

                ensures result == 0 or result == 1;
            } by {
                open(allocated_cell(owner)) {
                }
                execute();
                simp();
            }
        "#;
    let sources = [
        ("replace_allocated_cell.c", callee_source),
        ("replace_after_scoped_open.c", caller_source),
    ];
    let caller_execute = click_source
        .rfind("execute();")
        .expect("the caller proof should contain its execute tactic");
    let position = expansion::position_at_offset(click_source, caller_execute);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the straight-line opaque call should expand");
    let caller_expansion = expanded
        .rsplit_once("int32 replace_after_scoped_open")
        .map(|(_, caller)| caller)
        .expect("the expanded source should retain the caller proof");
    assert!(
        !caller_expansion.contains("execute();"),
        "{caller_expansion}"
    );
    assert!(caller_expansion.contains("step();"), "{caller_expansion}");
    assert!(
        !caller_expansion
            .lines()
            .any(|line| line.trim_start().starts_with("if ")),
        "a straight-line opaque call must not expand through a synthetic proof case: {caller_expansion}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded single-successor call should check independently");
}

#[test]
fn selected_post_execution_smart_have_uses_its_path_certificate() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                have result == x by simp();
                simp();
            }
        "#;
    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("checked post-execution smart have should verify");

    let have_offset = click_source
        .find("have result")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("selected post-execution smart have should expand after finalization");
    assert!(
        !expanded.contains("have result == x by simp()"),
        "{expanded}"
    );
    assert!(expanded.contains("have result == x by {"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("selected post-execution have certificate should check");
}

#[test]
fn post_execution_smart_have_applies_a_theorem_to_result_through_proof() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            theorem int32_reflexive(value: int32) {
                ensures value == value by {
                    normalize();
                }
            }

            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                have result == result by {
                    apply(int32_reflexive(result));
                    simp();
                }
                simp();
            }
        "#;
    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("result-aware theorem application should verify through Proof");

    let have_offset = click_source
        .find("have result == result")
        .expect("proof should contain the result-aware have");
    let position = expansion::position_at_offset(click_source, have_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained result-aware Proof should expand");
    let expanded_have_start = expanded
        .find("have result == result")
        .expect("expanded proof should retain the selected have");
    let expanded_have_end = expanded[expanded_have_start..]
        .find("\n                simp();")
        .map(|offset| expanded_have_start + offset)
        .expect("expanded proof should retain its outer closer");
    let expanded_have = &expanded[expanded_have_start..expanded_have_end];
    assert!(
        expanded_have.contains("apply(int32_reflexive(result)) using"),
        "{expanded_have}"
    );
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the expanded result-aware theorem application should independently verify");
}

#[test]
fn selected_post_execution_capture_ignores_nested_certificate_indices() {
    let c_source = r#"
            int32 set(int32* data, int32 value) {
                data[0] = value;
                return value;
            }
        "#;
    let click_source = r#"
            verifying "set.c";

            int32 set(int32 data[], int32 value) {
                owns data[0..1];
                ensures result == value;
                ensures data[0] == value;
            } by {
                execute();
                have value == value by { normalize(); }
                have result == value by { normalize(); }
                have data[0] == value by simp();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have data[0]")
        .expect("proof should contain the selected have");
    let position = expansion::position_at_offset(click_source, have_offset);

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("set.c", c_source)],
        position.line,
        position.column,
    )
    .expect("nested certificate validation must not leak later deferred tactics into the capture");
    verify_c0_sources(&expanded, &[("set.c", c_source)])
        .expect("the selected post-execution have expansion should check");
}

#[test]
fn post_execution_transport_observes_a_preceding_have() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                have result == x by {
                    normalize();
                }
                transport(result == x, result == x) using {
                    result == x;
                }
                assumption();
            }
        "#;

    verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("post-execution tactics should check in source order");
}

#[test]
fn selected_post_execution_transport_emits_an_explicit_certificate() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                execute();
                have result == x by {
                    normalize();
                }
                transport(result == x, result == x);
                assumption();
            }
        "#;
    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("checked post-execution transport should verify");

    let transport_offset = click_source
        .find("transport(")
        .expect("proof should contain the selected transport");
    let line = click_source[..transport_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = transport_offset
        - click_source[..transport_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("selected post-execution transport should expand after finalization");
    assert!(expanded.contains("transport(result == x, result == x) using {"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("post-execution transport certificate should check");
}

#[test]
fn grouped_post_execution_unfold_retains_its_checked_proof_step() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        predicate selected(x: int32) {
            x == x
        }

        verifying "identity.c";

        int32 identity(int32 x) {
            requires selected(x);
            ensures selected(x);
        } by {
            execute();
            unfold(selected);
            assumption();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("the grouped outcome unfold should verify through Proof");
}

#[test]
fn grouped_post_execution_closers_use_independent_checked_proofs() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            requires x == 0;
            ensures retained: x == 0;
            ensures reflexive: result == result;
        } by {
            execute();
            assumption();
            normalize();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("grouped outcome closers should verify through focused Proof roots");
}

#[test]
fn post_execution_rewrite_retains_its_checked_proof_step() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            requires x == 0;
            ensures successor: x + 1 == 1;
        } by {
            execute();
            rewrite(x == 0);
            normalize();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("outcome rewrite should advance its focused Proof goal");
}

#[test]
fn grouped_post_execution_simp_publishes_checked_obligations_through_proof() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            ensures first: result == result;
            ensures second: result == result;
        } by {
            execute();
            simp();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("grouped simp should retain its checked obligation scopes");

    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected grouped simp");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained grouped simp certificate should expand");
    // The first `simp` acts on the first open goal; the second keeps its own.
    assert_eq!(expanded.matches("have result == result by {").count(), 1);
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the serialized grouped obligation scopes should verify independently");
}

#[test]
fn grouped_post_execution_arithmetic_rejects_unavailable_irrelevant_extra() {
    let c_source = r#"
        int32 bump(int32 n) { return n + 1; }
    "#;
    let click_source = r#"
        verifying "bump.c";

        int32 bump(int32 n) {
            requires 0 <= n;
            requires n <= 100;
            ensures result <= 101;
        } by {
            execute();
            arithmetic() using { 0 <= n; n <= 100; n <= 99; }
        }
    "#;
    let error = verify_c0_sources(click_source, &[("bump.c", c_source)])
        .expect_err("an unavailable irrelevant post-execution premise must be rejected");
    assert!(
        error
            .message()
            .contains("post-execution `arithmetic using` premise 2 is not exactly available"),
        "{error:?}"
    );
}

#[test]
fn grouped_post_execution_simp_applies_planned_steps_once_through_proof() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            requires x == 0;
            ensures successor: x + 1 == 1;
        } by {
            execute();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("grouped simp should apply its planned rewrite through Proof");

    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected grouped simp");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the planner-selected grouped certificate should expand");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the retained planner-selected steps should verify independently");
}

#[test]
fn post_execution_simp_builds_disjunction_cases_on_proof() {
    let c_source = r#"
        int32 choose(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "choose.c";

        int32 choose(int32 x) {
            requires x == 0 or x == 1;
            ensures 0 <= result;
        } by {
            execute();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("choose.c", c_source)]);
    verified.expect("the two-value result should prove nonnegative by cases");

    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected grouped simp");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("choose.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the checked case split should expand");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(
        expanded.contains("at(function.entry, x == 0) => {")
            && expanded.contains("at(function.entry, x == 1) => {"),
        "{expanded}"
    );
    assert_eq!(expanded.matches("rewrite(").count(), 2, "{expanded}");
    assert_eq!(expanded.matches("normalize();").count(), 2, "{expanded}");
    verify_c0_sources(&expanded, &[("choose.c", c_source)])
        .expect("the retained case split should verify independently");
}

#[test]
fn symbolic_max_outcomes_retain_selected_branch_order_paths() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join("max_symbolic.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("max_symbolic should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let verified = verify_c0_sources(click_source, &c_sources);
    verified.expect("both symbolic max claims should verify through Proof");

    for claim in [CProofClaim::Ensure(0), CProofClaim::Ensure(1)] {
        let expanded = expand_c0_claim_source(click_source, &c_sources, "max", claim)
            .expect("the retained branch order proof should expand");
        verify_c0_sources(&expanded, &c_sources)
            .expect("the expanded branch order proof should check independently");
    }
}

#[test]
fn outcome_arithmetic_normalization_retains_selected_equality_paths() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join("later_loop_preserve.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("later_loop_preserve should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let verified = verify_c0_sources(click_source, &c_sources);
    verified.expect("the return expression should normalize through retained equalities");

    let expanded = expand_c0_claim_source(
        click_source,
        &c_sources,
        "later_loop_preserve",
        CProofClaim::Ensure(0),
    )
    .expect("the retained equality paths should expand");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources)
        .expect("the expanded equality paths should check independently");
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn outcome_quantified_cells_retain_selected_instantiations() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join("fill3_array_loop.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("fill3_array_loop should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let verified = verify_c0_sources(click_source, &c_sources);
    verified.expect("all three concrete cells should specialize the retained loop invariant");

    for claim in [
        CProofClaim::Ensure(0),
        CProofClaim::Ensure(1),
        CProofClaim::Ensure(2),
    ] {
        let expanded = expand_c0_claim_source(click_source, &c_sources, "fill3_array_loop", claim)
            .expect("the retained universal instance should expand");
        assert!(expanded.contains("instantiate("), "{expanded}");
        verify_c0_sources(&expanded, &c_sources)
            .expect("the expanded universal instance should check independently");
    }
}

#[test]
fn post_execution_simp_builds_recursive_conjunction_on_proof() {
    let c_source = r#"
        int32 first(int32 x, int32 y) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "first.c";

        int32 first(int32 x, int32 y) {
            requires 0 < x;
            requires 0 < y;
            ensures 0 <= x and 0 <= y;
        } by {
            execute();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("first.c", c_source)]);
    verified.expect("the conjunction should retain both recursively checked child proofs");

    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected grouped simp");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("first.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained conjunction should expand");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert_eq!(
        expanded
            .matches("apply(int32_positive_is_nonnegative(")
            .count(),
        2,
        "{expanded}"
    );
    assert!(expanded.contains("both {"), "{expanded}");
    verify_c0_sources(&expanded, &[("first.c", c_source)])
        .expect("the retained conjunction should verify independently");
}

#[test]
fn post_execution_simp_uses_the_introduced_antecedent_for_contradiction() {
    let c_source = r#"
        int32 branch_value(int32 x) {
            if (x != 0) {
                return 0;
            }
            return 1;
        }
    "#;
    let click_source = r#"
        verifying "branch.c";

        int32 branch_value(int32 x) {
            ensures x == 0 implies result == 1;
        } by {
            execute();
            simp();
        }
    "#;
    let sources = [("branch.c", c_source)];

    let verified = verify_c0_sources(click_source, &sources);
    verified.expect("the vacuous path implication should close through Proof");

    let expanded =
        expand_c0_claim_source(click_source, &sources, "branch_value", CProofClaim::Grouped)
            .expect("the retained introduced contradiction should expand");
    assert!(expanded.contains("intro();"), "{expanded}");
    assert!(expanded.contains("contradiction("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the introduced contradiction should check independently");
}

#[test]
fn post_execution_smart_have_builds_recursive_conjunction_on_proof() {
    let c_source = r#"
        int32 first(int32 x, int32 y) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "first.c";

        int32 first(int32 x, int32 y) {
            requires 0 < x;
            requires 0 < y;
            ensures 0 <= x and 0 <= y;
        } by {
            execute();
            have 0 <= x and 0 <= y by simp();
            assumption();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("first.c", c_source)]);
    verified.expect("the smart have should retain its recursively checked conjunction");

    let have_offset = click_source
        .find("have 0 <= x and 0 <= y")
        .expect("proof should contain the selected smart have");
    let position = expansion::position_at_offset(click_source, have_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("first.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained smart have should expand");
    assert!(!expanded.contains("by simp()"), "{expanded}");
    assert_eq!(
        expanded
            .matches("apply(int32_positive_is_nonnegative(")
            .count(),
        2,
        "{expanded}"
    );
    assert!(expanded.contains("both {"), "{expanded}");
    verify_c0_sources(&expanded, &[("first.c", c_source)])
        .expect("the retained smart have should verify independently");
}

#[test]
fn post_execution_existential_simp_retains_its_checked_scope() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            ensures exists (j: int32) { j == result } by {
                execute();
                witness { j: result };
                simp();
            }
        }
    "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("exit witness should refine its checked obligation scope");
    assert_eq!(flat_units, 1, "the function proof should retain Proof");

    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected existential simp");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the checked existential obligation should expand");
    assert!(expanded.contains("witness { j: result };"), "{expanded}");
    assert!(expanded.contains("normalize();"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the retained witness/normalize scope should verify independently");
}

#[test]
fn post_execution_choose_and_witness_share_the_retained_outcome_proof() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            requires exists (k: int32) { k == x };
            ensures exists (j: int32) { j == result } by {
                execute();
                obtain (k: int32) { k == x };
                witness { j: k };
                simp();
            }
        }
    "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("choose and witness should advance one retained outcome Proof");
    assert_eq!(flat_units, 1, "the function proof should retain Proof");

    let simp_offset = click_source.rfind("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained choose/witness Proof should serialize");
    assert!(
        expanded.contains("obtain (k: int32) { k == x };"),
        "{expanded}"
    );
    assert!(expanded.contains("witness { j: k };"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the serialized choose/witness proof should independently verify");

    let witness_offset = expanded
        .rfind("witness { j: k };")
        .expect("the extracted nested proof should retain its witness");
    let mut corrupted = expanded.clone();
    corrupted.replace_range(
        witness_offset..witness_offset + "witness { j: k };".len(),
        "witness { j: k + 1 };",
    );
    assert_ne!(
        corrupted, expanded,
        "the expansion should expose its witness"
    );
    verify_c0_sources(&corrupted, &[("identity.c", c_source)])
        .expect_err("tampering with the extracted witness must invalidate the proof");
}

#[test]
fn bounded_range_witness_closes_on_the_checked_outcome_scope() {
    let c_source = r#"
        int32 witness_zero(int32 n) {
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "witness.c";

        int32 witness_zero(int32 n) {
            requires 0 < n;
            ensures found_zero: (0..n).any(|k| { k == result }) by {
                execute();
                witness { k: 0 };
                simp();
            }
        }
    "#;
    let sources = [("witness.c", c_source)];

    let verified = verify_c0_sources(click_source, &sources);
    verified.expect("the bounded witness body should close through Proof");

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "witness_zero",
        CProofClaim::Ensure(0),
    )
    .expect("the retained bounded witness should expand");
    assert!(expanded.contains("witness { k: 0 }"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained bounded witness should check independently");
}

#[test]
fn selected_post_execution_smart_apply_uses_exact_path_premises() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            theorem int32_equality_symmetric(first: int32, second: int32) {
                requires first == second;
                ensures second == first by {
                    simp();
                }
            }

            verifying "identity.c";

            int32 identity(int32 x) {
                ensures x == result;
            } by {
                execute();
                apply(int32_equality_symmetric(result, x));
                simp();
            }
        "#;
    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("post-execution smart apply should verify through Proof");

    let apply_offset = click_source
        .find("apply(int32")
        .expect("proof should contain the selected apply");
    let line = click_source[..apply_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = apply_offset
        - click_source[..apply_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("selected post-execution smart apply should expand after finalization");
    assert!(!expanded.contains("apply(int32_equality_symmetric(result, x));"));
    assert!(
        expanded.contains("apply(int32_equality_symmetric(result, x)) using {"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("selected post-execution apply certificate should check");
}

#[test]
fn smart_apply_surfaces_a_framed_comparison_after_an_immutable_call() {
    let peek_c_source = r#"
            int32 peek(int32* data) {
                return data[0];
            }
        "#;
    let pipeline_c_source = r#"
            int32 pipeline(int32* data, int32 expected) {
                int32 observed;
                observed = peek(data);
                return observed;
            }
        "#;
    let click_source = r#"
            theorem int32_equality_transitive(first: int32, second: int32, third: int32) {
                requires first == second;
                requires second == third;
                ensures first == third by {
                    simp();
                }
            }

            resource equal_cell(data: int32*, expected: int32) {
                owns data[0..1];
                fact data[0] == expected;
            }

            verifying "pipeline.c";
            verifying "peek.c";

            int32 peek(int32* data) {
                views data[0..1];
                ensures result == data[0] by auto();
            }

            int32 pipeline(int32* data, int32 expected) {
                views equal_cell(data, expected);
                ensures result == expected;
            } by {
                observe(equal_cell(data, expected));
                execute_until(statement(2));
                apply(int32_equality_transitive(observed, data[0], expected));
                execute();
                simp();
            }
        "#;

    verify_c0_sources(
        click_source,
        &[("peek.c", peek_c_source), ("pipeline.c", pipeline_c_source)],
    )
    .expect("smart apply should surface the framed array equality after the call");
}

#[test]
fn smart_apply_preserves_statement_snapshots_in_explicit_premises() {
    let c_source = r#"
            int32 decrement(int32* p) {
                p[0] = 0;
                return p[0];
            }
        "#;
    let click_source = r#"
            theorem changed_one_to_zero(before: int32, after: int32) {
                requires before == 1;
                requires after == 0;
                ensures after == 0 by {
                    assumption();
                }
            }

            resource one_cell(p: int32*) {
                owns p[0..1];
                fact p[0] == 1;
            }

            verifying "decrement.c";

            int32 decrement(int32* p) {
                consumes one_cell(p);
                produces p[0..1];
                ensures result == 0;
            } by {
                unfold(one_cell(p));
                step();
                have at(statement(0).entry, p[0]) == 1 by simp();
                have at(statement(0).exit, p[0]) == 0 by simp();
                apply(changed_one_to_zero(
                    at(statement(0).entry, p[0]),
                    at(statement(0).exit, p[0])
                ));
                execute();
                simp();
            }
        "#;
    let apply_offset = click_source
        .find("apply(changed_one_to_zero")
        .expect("proof should contain the selected apply");
    let line = click_source[..apply_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = apply_offset
        - click_source[..apply_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("decrement.c", c_source)], line, column)
            .expect("the snapshot theorem application should expand");
    assert!(
        expanded.contains("at(statement(0).entry, p[0]) == 1;"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("decrement.c", c_source)])
        .expect("the explicit snapshot premises should check");
}

#[test]
fn source_expansion_preserves_proof_marks() {
    let c_source = r#"
        int32 increment(int32 x) {
            x = x + 1;
            return x;
        }
    "#;
    let click_source = r#"
        verifying "increment.c";

        int32 increment(int32 x) {
            requires x < 2147483647;
            ensures result == at(before_increment, x) + 1 by {
                mark before_increment;
                execute();
                simp();
            }
        }
    "#;
    verify_c0_sources(click_source, &[("increment.c", c_source)])
        .expect("the marked proof should verify before expansion");

    let selected = click_source.rfind("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the smart tactic after a mark should expand");
    assert!(expanded.contains("mark before_increment;"));
    assert!(!expanded.contains("simp();"));
    verify_c0_sources(&expanded, &[("increment.c", c_source)])
        .expect("the expansion should check through the named snapshot");
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn marked_constant_store_transport_retains_load_identity() {
    let touch_c = r#"
        struct cell { int32 value; int32 other; };

        void touch_other(struct cell* owner) {
            owner->other = 0;
        }
    "#;
    let pipeline_c = r#"
        struct cell { int32 value; int32 other; };

        int32 pipeline(struct cell* owner) {
            owner->value = 11;
            touch_other(owner);
            return owner->value;
        }
    "#;
    let click_source = r#"
        verifying "touch_other.c";
        verifying "pipeline.c";

        void touch_other(struct cell* owner) {
            owns owner->other;
            ensures owner->other == 0;
        } by {
            execute();
            simp();
        }

        int32 pipeline(struct cell* owner) {
            owns *owner;
            ensures result == 11;
        } by {
            step();
            mark after_write;
            execute();
            transport(
                at(after_write, owner->value == 11),
                owner->value == 11
            );
            simp();
        }
    "#;
    let sources = [("touch_other.c", touch_c), ("pipeline.c", pipeline_c)];

    let ((verified, events), flat_units) = proof::count_flat_proof_units(|| {
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources))
    });
    verified.expect("the smart marked transport should verify before expansion");
    assert_eq!(flat_units, 2, "both function proofs should retain Proof");

    let transport_checks = events
        .iter()
        .filter_map(|event| {
            let crate::instrumentation::VerificationEvent::TacticStarted(tactic) = event else {
                return None;
            };
            (tactic.claim == "pipeline.contract" && tactic.tactic_name == "transport")
                .then_some(tactic)
        })
        .collect::<Vec<_>>();
    let check_operations = events
        .iter()
        .filter_map(|event| {
            let crate::instrumentation::VerificationEvent::OperationFinished {
                function, name, ..
            } = event
            else {
                return None;
            };
            (function == "pipeline" && name.contains("check")).then_some(name)
        })
        .collect::<Vec<_>>();
    assert_eq!(
        transport_checks.len(),
        1,
        "ordinary verification should check the selected transport exactly once: {transport_checks:#?}; check operations: {check_operations:#?}"
    );
    let selected = click_source.find("transport(").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the marked transport should expand and check");
    assert!(
        expanded
            .contains("transport(at(after_write, owner->value == 11), owner->value == 11) using {")
    );
    verify_c0_sources(&expanded, &sources).expect("the expanded marked transport should check");

    let corrupted = expanded.replacen(
        "owner->value == 11) using {",
        "owner->value == 12) using {",
        1,
    );
    assert_ne!(
        corrupted, expanded,
        "the expansion should expose its target"
    );
    let corrupted_result = { verify_c0_sources(&corrupted, &sources) };
    corrupted_result.expect_err("tampering with the transport target must invalidate the proof");

    let mutating_c = touch_c.replace("owner->other = 0;", "owner->value = 0;");
    let mutating_click = click_source.replace(
        "owns owner->other;\n            ensures owner->other == 0;",
        "owns owner->value;\n            ensures owner->value == 0;",
    );
    let error = verify_c0_sources(
        &mutating_click,
        &[
            ("touch_other.c", mutating_c.as_str()),
            ("pipeline.c", pipeline_c),
        ],
    )
    .expect_err("transport across mutation of the marked field must fail");
    assert!(
        error
            .message()
            .contains("found no frame evidence carrying its source fact to the target's state")
            && error.message().contains("owner->value == 11")
            && error
                .message()
                .contains("at(after_write, owner->value == 11)"),
        "{}",
        error.message()
    );
}

#[test]
fn post_execution_store_transport_expands_from_the_recorded_store_equation() {
    let c_source = r#"
        int32 store_both(int32 p[2]) {
            p[0] = 7;
            p[1] = 9;
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "store_both.c";

        int32 store_both(int32 p[2]) {
            owns p[0..2];
            ensures p[0] == 7;
        } by {
            execute();
            transport(
                at(statement(0).exit, p[0]) == 7,
                p[0] == 7
            );
            simp();
        }
    "#;
    let sources = [("store_both.c", c_source)];

    verify_c0_sources(click_source, &sources)
        .expect("the post-execution store transport should verify");
    let selected = click_source.find("transport(").unwrap();
    let position = expansion::position_at_offset(click_source, selected);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the store transport should expand from its recorded equation");
    assert!(expanded.contains("transport(") && expanded.contains("using {"));
    assert_eq!(
        expanded.matches("at(statement(0).exit, p[0]) == 7").count(),
        1,
        "the transport source must not be duplicated as an auxiliary premise:\n{expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded store transport certificate should check from a fresh parse");
}

#[test]
fn statement_snapshots_support_complete_loadability_propositions() {
    let c_source = r#"
            int32 store_second_return_first(int32 p[2]) {
                p[1] = 9;
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "snapshot_loadable.c";

            int32 store_second_return_first(int32 p[2]) {
                owns p[0..2];
                ensures result == p[0];
            } by {
                step();
                have at(statement(0).entry, viewable(p[0..2])) by {
                    assumption();
                }
                transport(
                    at(statement(0).entry, viewable(p[0..2])),
                    viewable(p[0..2])
                ) using {
                    at(statement(0).entry, viewable(p[0..2]));
                }
                execute();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("snapshot_loadable.c", c_source)])
        .expect("a complete viewability proposition should lower and transport from a snapshot");
}

#[test]
fn statement_snapshots_preserve_declared_resource_argument_types() {
    let c_source = r#"
            int32 preserve_owner(int32* owner) {
                return owner[0];
            }
        "#;
    let click_source = r#"
            resource owner_cell(owner: int32*) {
                owns owner[0..1];
            }

            verifying "snapshot_resource.c";

            int32 preserve_owner(int32* owner) {
                owns owner_cell(owner);
                ensures result == owner[0];
            } by {
                unfold(owner_cell(owner));
                execute();
                have at(
                    statement(0).entry,
                    contains(owner_cell(owner), memory(owner[0..1]))
                ) by {
                    assumption();
                }
                fold(owner_cell(owner));
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("snapshot_resource.c", c_source)])
        .expect("a historical resource proposition should retain declared argument types");
}

#[test]
fn source_expander_locates_frontier_local_have_proofs() {
    let c_source = r#"
            int32 preserve_value(int32 x) {
                x = x;
                return x;
            }
        "#;
    let click_source = r#"
            verifying "statement_assert.c";

            int32 preserve_value(int32 x) {
                ensures result == x;
            } by {
                have x == x by simp();
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have x == x by simp()")
        .expect("frontier-local proof should exist");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("statement_assert.c", c_source)],
        line,
        column,
    )
    .expect("the frontier-local `have` proof should expand");
    assert_ne!(expanded, click_source);
    verify_c0_sources(&expanded, &[("statement_assert.c", c_source)])
        .expect("the expanded frontier-local proof should check");
}

#[test]
fn smart_apply_uses_ambient_loadability_only_for_argument_lowering() {
    let c_source = r#"
            struct pointer_pair {
                int32* first;
                int32* second;
            };

            int32 pointer_pipeline(struct pointer_pair* pair, int32* data) {
                return 0;
            }
        "#;
    let click_source = r#"
            theorem pointer_equality_transitive(
                first: int32*,
                second: int32*,
                third: int32*
            ) {
                requires first == second;
                requires second == third;
                ensures first == third by {
                    simp();
                }
            }

            resource linked_pair(pair: struct pointer_pair*, data: int32*) {
                owns *pair;
                fact pair->first == pair->second;
                fact pair->second == data;
            }

            verifying "pointer_pipeline.c";

            int32 pointer_pipeline(struct pointer_pair* pair, int32* data) {
                views linked_pair(pair, data);
                ensures result == 0;
            } by {
                observe(linked_pair(pair, data));
                apply(pointer_equality_transitive(
                    pair->first,
                    pair->second,
                    data
                ));
                execute();
                simp();
            }
        "#;
    let apply_offset = click_source
        .find("apply(pointer_equality_transitive")
        .expect("proof should contain the selected apply");
    let line = click_source[..apply_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = apply_offset
        - click_source[..apply_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("pointer_pipeline.c", c_source)],
        line,
        column,
    )
    .expect("pointer theorem arguments should lower from the ambient viewability context");
    assert!(
        expanded.contains("apply(pointer_equality_transitive(") && expanded.contains(" using {"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("pointer_pipeline.c", c_source)])
        .expect("explicit theorem premises should check with ambient argument lowering");
}

#[test]
fn selected_branched_post_execution_apply_shares_identical_path_certificates() {
    let c_source = r#"
            int32 choose(int32 flag) {
                if (flag) {
                    return 1;
                } else {
                    return 2;
                }
            }
        "#;
    let click_source = r#"
            theorem retain_one_or_two(value: int32) {
                requires value == 1 or value == 2;
                ensures value == 1 or value == 2 by {
                    assumption();
                }
            }

            verifying "choose.c";

            int32 choose(int32 flag) {
                ensures result == 1 or result == 2;
            } by {
                execute();
                apply(retain_one_or_two(result));
                simp();
            }
        "#;
    let apply_offset = click_source
        .find("apply(retain_one")
        .expect("proof should contain the selected apply");
    let line = click_source[..apply_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = apply_offset
        - click_source[..apply_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("choose.c", c_source)], line, column)
            .expect("branched post-execution apply should produce path certificates");
    verify_c0_sources(&expanded, &[("choose.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "expanded apply must verify before checking its formatting: {}\n{expanded}",
            error.message()
        )
    });
    assert!(!expanded.contains("apply(retain_one_or_two(result));"));
    assert!(
        !expanded.contains("if at(statement(0).entry, flag) != at(statement(0).entry, 0) {"),
        "{expanded}"
    );
    assert_eq!(
        expanded
            .matches("apply(retain_one_or_two(result)) using {")
            .count(),
        1,
        "{expanded}"
    );
}

#[test]
fn selected_branched_post_execution_have_shares_identical_path_certificates() {
    let c_source = r#"
            int32 choose(int32 flag) {
                if (flag) {
                    return 1;
                } else {
                    return 2;
                }
            }
        "#;
    let click_source = r#"
            verifying "choose.c";

            int32 choose(int32 flag) {
                ensures result == 1 or result == 2;
            } by {
                execute();
                have result == 1 or result == 2 by simp();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have result")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("choose.c", c_source)], line, column)
            .expect("branched post-execution have should produce path certificates");
    verify_c0_sources(&expanded, &[("choose.c", c_source)])
        .expect("expanded have must verify before checking its formatting");
    assert!(!expanded.contains("have result == 1 or result == 2 by simp()"));
    assert!(
        !expanded.contains("if at(statement(0).entry, flag) != at(statement(0).entry, 0) {"),
        "{expanded}"
    );
    assert_eq!(
        expanded
            .matches("have result == 1 or result == 2 by {")
            .count(),
        1,
        "{expanded}"
    );
}

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn selected_pure_case_split_simp_expands_by_removal() {
    // A smart exit `simp` whose claims all close by exact checks contributes
    // no surface tactics of its own. Its expansion must remove the tactic —
    // NOT graft the enclosing branch skeleton as an `if` tree with empty
    // leaves: that tree would re-split every already-merged execution path at
    // path end and lose the execution-path/branch-trace pairing certificate
    // check keeps (git history (case-split expansion merge, 2026-07-31)).
    let c_source = r#"
            int32 sort3(int32 p[3]) {
                int32 tmp;
                if (p[1] < p[0]) {
                    tmp = p[0];
                    p[0] = p[1];
                    p[1] = tmp;
                }
                if (p[2] < p[1]) {
                    tmp = p[1];
                    p[1] = p[2];
                    p[2] = tmp;
                }
                if (p[1] < p[0]) {
                    tmp = p[0];
                    p[0] = p[1];
                    p[1] = tmp;
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "sort3.c";

            predicate sorted_range(p: int32[], lo: int32, hi: int32) {
                forall (i: int32) {
                    forall (j: int32) {
                        0 <= i and 0 <= j and lo <= i and i < j and j < hi implies p[i] <= p[j]
                    }
                }
            }

            int32 sort3(int32 p[3]) {
                consumes p[0..3];
                ensures sorted: sorted_range(p, 0, 3) by {
                    execute();
                    unfold(sorted_range);
                    simp();
                }
            }
        "#;
    let simp_offset = click_source
        .find("simp();")
        .expect("proof should contain the selected simp");
    let line = click_source[..simp_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = simp_offset
        - click_source[..simp_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[("sort3.c", c_source)], line, column)
        .expect("a pure case-split simp should expand");
    assert!(!expanded.contains("simp()"), "{expanded}");
    assert!(!expanded.contains("if p[1] < p[0] {"), "{expanded}");
    verify_c0_sources(&expanded, &[("sort3.c", c_source)])
        .expect("the removed closer's paths should close via the ordinary path-end check");
}

#[test]
fn smart_tactic_in_an_infeasible_branch_arm_expands_by_removal() {
    // The `then` arm's C path contradicts the contract, so checked execution
    // drops that arm without running its tactics. The `simp` written there
    // contributes no checked operation to any retained certificate, so its
    // expansion is the empty rewrite. Before this was recorded, `click
    // verify` accepted the proof while `click expand` and `click audit`
    // reported `has no source tactic 2` for the same sidecar — the
    // audit/verify disagreement first seen on `tree_contains` in
    // `examples/modeled-binary-tree`.
    let c_source = r#"
            int32 flag(int32 x) {
                if (x > 0) {
                    return 1;
                }
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "flag.c";

            int32 flag(int32 x) {
                requires x <= 0;
                ensures result == 0;
            } by {
                branch { step(); simp(); } else {}
                step();
                simp();
            }
        "#;
    let sources = [("flag.c", c_source)];
    verify_c0_sources(click_source, &sources).expect("the infeasible-arm proof should verify");

    let selected = click_source
        .find("step(); simp();")
        .expect("proof should contain the arm's selected simp")
        + "step(); ".len();
    let line = click_source[..selected]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = selected
        - click_source[..selected]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &sources, line, column)
        .expect("a smart tactic on a dropped C path should expand");
    assert!(!expanded.contains("step(); simp();"), "{expanded}");
    assert!(expanded.contains("branch { step();"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("removing the dropped arm's closer should still verify");
}

#[test]
fn source_expander_lowers_smart_simp_inside_have() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                have x == x by simp();
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have x == x")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("the selected smart have should expand");
    let expanded_have = &expanded[expanded
        .find("have x == x")
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("execute()")
            .expect("expanded proof should retain its suffix")];
    assert!(expanded_have.contains("normalize();"), "{expanded_have}");
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the expanded smart have should check");
}

/// The `simp` written in a smart `have` body selects the `have` site, as
/// the `have` keyword does, for a bare `by simp()` and for a block body.
#[test]
fn source_expander_selects_a_smart_have_by_the_simp_in_its_body() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = "verifying \"identity.c\";\n\
        int32 identity(int32 x) {\n\
        \x20   ensures result == x;\n\
        } by {\n\
        \x20   have x == x by simp();\n\
        \x20   have x <= x by {\n\
        \x20       simp();\n\
        \x20   }\n\
        \x20   execute();\n\
        \x20   simp();\n\
        }\n";
    let sources = [("identity.c", c_source)];
    for (have, nested) in [((5, 5), (5, 20)), ((6, 5), (7, 9))] {
        let from_have = expand_c0_tactic_source_at(click_source, &sources, have.0, have.1)
            .expect("the have keyword should select the smart have");
        let from_nested = expand_c0_tactic_source_at(click_source, &sources, nested.0, nested.1)
            .expect("the simp in the body should select the smart have");
        assert_eq!(from_nested, from_have);
        assert_ne!(from_nested, click_source);
        verify_c0_sources(&from_nested, &sources).expect("the expanded smart have should check");
    }
}

/// A `have` whose body mixes a smart `have` and a smart `simp` is no smart
/// site itself, but each smart tactic in its body is: expansion rewrites
/// exactly that tactic's source and leaves its neighbors as written.
#[test]
fn source_expander_rewrites_one_smart_tactic_inside_a_mixed_have_body() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = "verifying \"identity.c\";\n\
        int32 identity(int32 x) {\n\
        \x20   ensures result == x;\n\
        } by {\n\
        \x20   have x <= x by {\n\
        \x20       have x == x by { simp(); }\n\
        \x20       simp();\n\
        \x20   }\n\
        \x20   execute();\n\
        \x20   simp();\n\
        }\n";
    let sources = [("identity.c", c_source)];
    verify_c0_sources(click_source, &sources).expect("the fixture should verify");
    let lines = click_source.lines().collect::<Vec<_>>();

    let body_simp = expand_c0_tactic_source_at(click_source, &sources, 7, 9)
        .expect("the simp in the mixed have body should expand");
    let rewritten = body_simp.lines().collect::<Vec<_>>();
    assert_eq!(rewritten[..6], lines[..6], "{body_simp}");
    assert_eq!(rewritten[6], "        normalize();", "{body_simp}");
    assert!(
        body_simp.ends_with("    }\n    execute();\n    simp();\n}\n"),
        "{body_simp}"
    );
    verify_c0_sources(&body_simp, &sources).expect("the rewritten body simp should check");

    // The inner smart `have` is one site, selected by its keyword, by the
    // `simp` in its body, or by any column inside it.
    let inner_have = expand_c0_tactic_source_at(click_source, &sources, 6, 9)
        .expect("the nested smart have should expand");
    for column in [26, 18, 34] {
        assert_eq!(
            expand_c0_tactic_source_at(click_source, &sources, 6, column)
                .expect("a column inside the nested smart have should select it"),
            inner_have
        );
    }
    assert!(
        inner_have.contains(
            "    have x <= x by {\n        have x == x by {\n            normalize();\n        }\n        simp();\n    }\n"
        ),
        "{inner_have}"
    );
    verify_c0_sources(&inner_have, &sources).expect("the rewritten nested have should check");

    // Neither the brace closing the non-smart outer `have` nor the space
    // before it lies in a smart tactic.
    for (line, column) in [(8, 5), (5, 1)] {
        let error = expand_c0_tactic_source_at(click_source, &sources, line, column)
            .expect_err("a location outside every smart tactic selects nothing");
        assert!(
            error
                .message()
                .contains("no smart tactic's source contains this location"),
            "{line}:{column}: {}",
            error.message()
        );
    }
}

/// Expands the smart `simp` written at `line` inside a mixed `have` body,
/// checks that only that line was replaced (by one or more lines), and
/// re-verifies the rewrite.
fn assert_mixed_have_body_simp_expands(
    click_source: &str,
    sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> String {
    verify_c0_sources(click_source, sources).expect("the fixture should verify");
    let expanded = expand_c0_tactic_source_at(click_source, sources, line, column)
        .unwrap_or_else(|error| panic!("{line}:{column}: {}", error.message()));
    let original = click_source.lines().collect::<Vec<_>>();
    let rewritten = expanded.lines().collect::<Vec<_>>();
    assert!(rewritten.len() >= original.len(), "{expanded}");
    assert_eq!(rewritten[..line - 1], original[..line - 1], "{expanded}");
    let kept_after = original.len() - line;
    let replaced = &rewritten[line - 1..rewritten.len() - kept_after];
    assert_eq!(
        rewritten[rewritten.len() - kept_after..],
        original[line..],
        "{expanded}"
    );
    assert!(
        !replaced.contains(&original[line - 1]),
        "the selected line was kept: {expanded}"
    );
    verify_c0_sources(&expanded, sources).expect("the rewritten body tactic should check");
    expanded
}

/// A mixed `have` in a proof `if` arm after execution is checked per
/// outcome; its body `simp` expands on its own there too.
#[test]
fn source_expander_rewrites_a_have_body_tactic_in_a_post_execution_if_arm() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = "verifying \"identity.c\";\n\
        int32 identity(int32 x) {\n\
        \x20   ensures result == x;\n\
        } by {\n\
        \x20   execute();\n\
        \x20   if x > 0 {\n\
        \x20       simp();\n\
        \x20   } else {\n\
        \x20       have x <= x by {\n\
        \x20           have x == x by simp();\n\
        \x20           simp();\n\
        \x20       }\n\
        \x20       simp();\n\
        \x20   }\n\
        }\n";
    assert_mixed_have_body_simp_expands(click_source, &[("identity.c", c_source)], 11, 13);
}

/// A mixed `have` in a C `branch` arm is checked on the execution frontier;
/// its body `simp` expands on its own there.
#[test]
fn source_expander_rewrites_a_have_body_tactic_in_a_branch_arm() {
    let c_source = "int32 early_exit(int32 c) {\n\
        \x20   int32 x;\n\
        \x20   x = 0;\n\
        \x20   if (c != 0) {\n\
        \x20       return 1;\n\
        \x20   }\n\
        \x20   x = 2;\n\
        \x20   return x;\n\
        }\n";
    let click_source = "verifying \"early_exit.c\";\n\
        int32 early_exit(int32 c) {\n\
        \x20   ensures result >= 0;\n\
        } by {\n\
        \x20   step();\n\
        \x20   step();\n\
        \x20   branch {\n\
        \x20       have c != 0 by {\n\
        \x20           have c == c by simp();\n\
        \x20           simp();\n\
        \x20       }\n\
        \x20       step();\n\
        \x20       simp();\n\
        \x20   } else {}\n\
        \x20   step();\n\
        \x20   step();\n\
        \x20   simp();\n\
        }\n";
    assert_mixed_have_body_simp_expands(click_source, &[("early_exit.c", c_source)], 10, 13);
}

/// A mixed `have` in a frontier-local loop's `preserve` phase is checked by
/// the preservation proof; its body `simp` expands on its own there.
#[test]
fn source_expander_rewrites_a_have_body_tactic_in_a_loop_preserve_phase() {
    let c_source = "int32 count_to_n(int32 n) {\n\
        \x20   int32 i;\n\
        \x20   i = 0;\n\
        \x20   while (i < n) {\n\
        \x20       i++;\n\
        \x20   }\n\
        \x20   return i;\n\
        }\n";
    let click_source = "verifying \"count_up.c\";\n\
        int32 count_to_n(int32 n) {\n\
        \x20   requires n >= 0 and n <= 2147483647;\n\
        \x20   ensures result == n;\n\
        } by {\n\
        \x20   step();\n\
        \x20   step();\n\
        \x20   loop {\n\
        \x20       decreases n - i;\n\
        \x20       invariant i >= 0;\n\
        \x20       invariant i <= n;\n\
        \x20       initialize by simp();\n\
        \x20       preserve by {\n\
        \x20           have i <= n by {\n\
        \x20               have i == i by simp();\n\
        \x20               simp();\n\
        \x20           }\n\
        \x20           step();\n\
        \x20           close_invariants();\n\
        \x20       }\n\
        \x20   }\n\
        \x20   step();\n\
        \x20   simp();\n\
        }\n";
    assert_mixed_have_body_simp_expands(click_source, &[("count_up.c", c_source)], 16, 17);
}

const COUNT_UP_C: &str = "int32 count_to_n(int32 n) {\n\
    \x20   int32 i;\n\
    \x20   i = 0;\n\
    \x20   while (i < n) {\n\
    \x20       i++;\n\
    \x20   }\n\
    \x20   return i;\n\
    }\n";

/// A frontier-local counting loop whose `initialize` phase is `phase`.
fn count_up_with_initialize(phase: &str) -> String {
    format!(
        "verifying \"count_up.c\";\n\
        int32 count_to_n(int32 n) {{\n\
        \x20   requires n >= 0 and n <= 2147483647;\n\
        \x20   ensures result == n;\n\
        }} by {{\n\
        \x20   step();\n\
        \x20   step();\n\
        \x20   loop {{\n\
        \x20       decreases n - i;\n\
        \x20       invariant i >= 0;\n\
        \x20       invariant i <= n;\n\
        \x20       initialize by {{\n\
        {phase}\
        \x20       }}\n\
        \x20       preserve by {{\n\
        \x20           step();\n\
        \x20           close_invariants();\n\
        \x20       }}\n\
        \x20   }}\n\
        \x20   step();\n\
        \x20   simp();\n\
        }}\n"
    )
}

/// A loop `initialize` phase addresses the tactics written in a helper
/// `have`'s body as other phases do, so the smart `simp` there expands on
/// its own.
#[test]
fn source_expander_rewrites_a_have_body_tactic_in_a_loop_initialize_helper() {
    let click_source = count_up_with_initialize(
        "\x20           have 0 <= n by {\n\
        \x20               have n == n by simp();\n\
        \x20               simp();\n\
        \x20           }\n\
        \x20           simp();\n",
    );
    assert_mixed_have_body_simp_expands(&click_source, &[("count_up.c", COUNT_UP_C)], 15, 17);
}

/// The same holds for the body of the `have` that is one invariant's own
/// initialization proof.
#[test]
fn source_expander_rewrites_a_have_body_tactic_in_an_initialize_invariant_body() {
    let click_source = count_up_with_initialize(
        "\x20           have i >= 0 by simp();\n\
        \x20           have i <= n by {\n\
        \x20               have n == n by simp();\n\
        \x20               simp();\n\
        \x20           }\n",
    );
    assert_mixed_have_body_simp_expands(&click_source, &[("count_up.c", COUNT_UP_C)], 16, 17);
}

/// A smart tactic in a proof `if` arm, or a `cases` arm, written inside a
/// `have` body expands on its own: the arm is part of its source path, so no
/// other tactic's checked delta is recorded for it.
#[test]
fn source_expander_rewrites_a_tactic_in_an_arm_inside_a_have_body() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let sources = [("identity.c", c_source)];
    let if_source = "verifying \"identity.c\";\n\
        int32 identity(int32 x) {\n\
        \x20   ensures result == x;\n\
        } by {\n\
        \x20   have x <= x by {\n\
        \x20       have x == x by simp();\n\
        \x20       if x > 0 {\n\
        \x20           have x > 0 by simp();\n\
        \x20           simp();\n\
        \x20       } else {\n\
        \x20           have x == x by simp();\n\
        \x20           simp();\n\
        \x20       }\n\
        \x20   }\n\
        \x20   execute();\n\
        \x20   simp();\n\
        }\n";
    for (line, column) in [(9, 13), (12, 13)] {
        assert_mixed_have_body_simp_expands(if_source, &sources, line, column);
    }
    let cases_source = "verifying \"identity.c\";\n\
        int32 identity(int32 x) {\n\
        \x20   ensures result == x;\n\
        } by {\n\
        \x20   have x <= x by {\n\
        \x20       have x > 0 or not (x > 0) by {\n\
        \x20           if x > 0 {\n\
        \x20               assumption();\n\
        \x20           } else {\n\
        \x20               assumption();\n\
        \x20           }\n\
        \x20       }\n\
        \x20       cases {\n\
        \x20           x > 0 => {\n\
        \x20               have x > 0 by simp();\n\
        \x20               simp();\n\
        \x20           }\n\
        \x20           not (x > 0) => {\n\
        \x20               simp();\n\
        \x20           }\n\
        \x20       }\n\
        \x20   }\n\
        \x20   execute();\n\
        \x20   simp();\n\
        }\n";
    for (line, column) in [(16, 17), (19, 17)] {
        assert_mixed_have_body_simp_expands(cases_source, &sources, line, column);
    }
}

/// A tactic after a proof `if` in a `have` body is checked once per arm and
/// keeps its own position in the body. Before arms were part of the source
/// path, the second tactic of an arm reported the same path as the tactic
/// after the `if`, so selecting that tactic recorded the arm tactic's delta.
#[test]
fn source_expander_rewrites_the_continuation_after_an_if_in_a_have_body() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = "verifying \"identity.c\";\n\
        int32 identity(int32 x) {\n\
        \x20   ensures result == x;\n\
        } by {\n\
        \x20   have x <= x by {\n\
        \x20       if x > 0 {\n\
        \x20           have x == x by simp();\n\
        \x20           have x > 0 by simp();\n\
        \x20       } else {\n\
        \x20           have x == x by simp();\n\
        \x20       }\n\
        \x20       simp();\n\
        \x20   }\n\
        \x20   execute();\n\
        \x20   simp();\n\
        }\n";
    let expanded =
        assert_mixed_have_body_simp_expands(click_source, &[("identity.c", c_source)], 12, 9);
    // The arm's `have x > 0` is not the continuation's expansion.
    assert_eq!(
        expanded.matches("x > 0").count(),
        click_source.matches("x > 0").count(),
        "{expanded}"
    );
}

/// A line without a column selects the one smart tactic starting on it and
/// lists the candidates when there are several.
#[test]
fn smart_tactic_selection_by_line_is_unique_or_lists_candidates() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = "verifying \"identity.c\";\n\
        int32 identity(int32 x) {\n\
        \x20   ensures result == x;\n\
        } by {\n\
        \x20   have x <= x by {\n\
        \x20       have x == x by { simp(); }\n\
        \x20       simp();\n\
        \x20   }\n\
        \x20   have x >= x by { have x == x by simp(); simp(); }\n\
        \x20   execute();\n\
        \x20   simp();\n\
        }\n";
    let sources = [("identity.c", c_source)];
    let select = |line, column| c0_select_smart_tactic(click_source, &sources, line, column);
    for (line, column, name) in [(6, 9, "have"), (7, 9, "simp"), (11, 5, "simp")] {
        let selected = select(line, None).expect("the line starts one smart tactic");
        assert_eq!(
            (selected.position.line, selected.position.column),
            (line, column)
        );
        assert_eq!(selected.tactic_name, name);
        assert_eq!(selected.claim_label, "identity.contract");
    }
    let ambiguous = select(9, None).expect_err("line 9 starts two smart tactics");
    assert!(
        ambiguous.reason.contains("2 smart tactics"),
        "{}",
        ambiguous.reason
    );
    assert_eq!(
        ambiguous
            .candidates
            .iter()
            .map(|candidate| (candidate.position.line, candidate.position.column))
            .collect::<Vec<_>>(),
        [(9, 22), (9, 45)]
    );
    let selected = select(9, Some(45)).expect("a column disambiguates the line");
    assert_eq!((selected.position.line, selected.position.column), (9, 45));
    let none = select(5, None).expect_err("line 5 starts only a non-smart have");
    assert!(none.reason.contains("no smart tactic starts on this line"));
}

#[test]
fn pure_structural_simp_builds_recursive_conjunction_on_proof() {
    let click_source = r#"
        theorem nonnegative_pair_direct(x: int32, y: int32) {
            requires 0 < x;
            requires 0 < y;
            ensures 0 <= x and 0 <= y by simp();
        }

        theorem nonnegative_pair_script(x: int32, y: int32) {
            requires 0 < x;
            requires 0 < y;
            ensures 0 <= x and 0 <= y by {
                simp();
            }
        }

        theorem nonnegative_pair_branches(flag: int32, x: int32, y: int32) {
            requires 0 < x;
            requires 0 < y;
            ensures 0 <= x and 0 <= y by {
                if flag == 0 {
                    simp();
                } else {
                    simp();
                }
            }
        }
    "#;

    let verified = verify_click_theorems(click_source);
    verified.expect("pure structural simp should retain both recursively checked child proofs");

    let script_start = click_source
        .find("theorem nonnegative_pair_script")
        .expect("the script theorem should be present");
    let branch_start = click_source
        .find("theorem nonnegative_pair_branches")
        .expect("the branch theorem should be present");
    for (offset, expected_applications) in [
        (
            click_source
                .find("simp();")
                .expect("the direct theorem should contain smart simp"),
            2,
        ),
        (
            script_start
                + click_source[script_start..]
                    .find("simp();")
                    .expect("the script theorem should contain smart simp"),
            2,
        ),
        (
            branch_start
                + click_source[branch_start..]
                    .find("simp();")
                    .expect("the branch theorem should contain smart simp"),
            4,
        ),
    ] {
        let position = expansion::position_at_offset(click_source, offset);
        let expanded =
            expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
                .expect("the retained pure conjunction should expand");
        assert_eq!(
            expanded
                .matches("apply(int32_positive_is_nonnegative(")
                .count(),
            expected_applications,
            "{expanded}"
        );
        assert!(expanded.contains("both {"), "{expanded}");
        verify_click_theorems(&expanded)
            .expect("the retained pure conjunction should verify independently");
    }
}

#[test]
fn post_execution_restricted_simp_retains_selected_premises_and_expansion() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"
        verifying "identity.c";
        int32 identity(int32 x) {
            requires 0 <= x;
            ensures 0 <= result;
        } by {
            execute();
            have 0 <= result by { simp(); }
            simp() using { 0 <= result; }
        }
    "#;
    let sources = [("identity.c", c_source)];
    verify_c0_sources(click_source, &sources)
        .expect("restricted exit simp should see the preceding have");
    let position =
        expansion::position_at_offset(click_source, click_source.find("simp() using").unwrap());
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("restricted exit simp should retain its checked certificate");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    verify_c0_sources(&expanded, &sources).expect("the expansion should check independently");
    for replacement in [
        "simp() using { x == x; }",
        "simp() using { result < 0; }",
        "simp() using { 0 <= result; x < 0; }",
    ] {
        let invalid = click_source.replace("simp() using { 0 <= result; }", replacement);
        let error = verify_c0_sources(&invalid, &sources)
            .expect_err("only listed, available premises may be used");
        assert!(error.message().contains("simp() using"), "{error:?}");
        assert!(
            error.message().contains("only the listed premises"),
            "{error:?}"
        );
        assert!(!error.message().contains("not implemented"), "{error:?}");
    }
}

#[test]
fn post_execution_restricted_simp_checks_each_return_path() {
    let sources = [(
        "choose.c",
        "int32 choose(int32 flag, int32 x, int32 y) { if (flag) { return x; } else { return y; } }",
    )];
    let click_source = r#"
        verifying "choose.c";
        int32 choose(int32 flag, int32 x, int32 y) {
            requires 0 <= x;
            requires 0 <= y;
            ensures 0 <= result;
        } by {
            execute();
            have 0 <= result by { simp(); }
            simp() using { 0 <= result; }
        }
    "#;
    verify_c0_sources(click_source, &sources)
        .expect("each return path must carry its selected premise");
    for premise in ["requires 0 <= x;", "requires 0 <= y;"] {
        assert!(verify_c0_sources(&click_source.replace(premise, ""), &sources).is_err());
    }
}

#[test]
fn post_execution_restricted_simp_continues_an_introduced_claim() {
    let sources = [("forall_scope.c", "int32 forall_scope(void) { return 0; }")];
    let click_source = r#"
        verifying "forall_scope.c";
        int32 forall_scope() {
            ensures forall (k: int32) { 0 <= k implies 0 <= k } by {
                execute();
                intro();
                intro();
                simp() using { 0 <= k; }
            }
        }
    "#;
    verify_c0_sources(click_source, &sources)
        .expect("restricted simp must continue the claim's introduced binder");
    let position =
        expansion::position_at_offset(click_source, click_source.find("simp() using").unwrap());
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column).unwrap();
    verify_c0_sources(&expanded, &sources)
        .expect("the closer's expansion must stay inside the introduced proof");
    assert!(
        verify_c0_sources(
            &click_source.replace("simp() using { 0 <= k; }", "simp() using { k == k; }"),
            &sources
        )
        .is_err()
    );
}

#[test]
fn post_execution_restricted_simp_checks_grouped_ownership_and_value_claims() {
    let sources = [("put.c", "void put(int32* p, int32 x) { *p = x; }")];
    let click_source = r#"
        verifying "put.c";
        void put(int32* p, int32 x) {
            requires 0 <= x;
            owns p[0..1];
            ensures *p == x;
            ensures 0 <= *p;
        } by {
            execute();
            have *p == x by { simp(); }
            have 0 <= *p by { simp(); }
            simp() using { *p == x; 0 <= *p; }
        }
    "#;
    verify_c0_sources(click_source, &sources)
        .expect("the checked resource transition and restricted propositions must agree");
    let position =
        expansion::position_at_offset(click_source, click_source.find("simp() using").unwrap());
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column).unwrap();
    verify_c0_sources(&expanded, &sources)
        .expect("grouped restricted expansion must return the owned cell");
    assert!(
        verify_c0_sources(
            &click_source.replace("owns p[0..1];", "views p[0..1];"),
            &sources
        )
        .is_err()
    );
}

#[test]
fn restricted_simp_expands_to_graph_normalization() {
    let click_source = r#"
            theorem equality_transitive(x: int32, y: int32, z: int32) {
                requires x == y;
                requires y == z;
                ensures x == z by {
                    simp() using {
                        x == y;
                        y == z;
                    }
                }
            }
        "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("restricted equality simp should build its typed path through Proof");
    let offset = click_source
        .find("simp() using")
        .expect("proof should contain restricted simp");
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("restricted simp should expand");
    assert!(expanded.contains("normalize() using"), "{expanded}");
    assert!(expanded.contains("x == y;"), "{expanded}");
    assert!(expanded.contains("y == z;"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("explicit equality certificate should check");
    for premise in ["requires x == y;", "requires y == z;"] {
        let missing = expanded.replace(premise, "");
        assert_ne!(missing, expanded);
        assert!(verify_c0_sources(&missing, &[]).is_err());
    }
}

#[test]
fn uint64_bit_test_inequality_expands_to_rewrite_and_normalize() {
    let click_source = r#"
        theorem set_low_bit_is_nonzero(word: uint64) {
            requires 1u64 == (word & 1u64);

            ensures (word & 1u64) != 0u64 by {
                simp();
            }
        }
    "#;
    verify_click_theorems(click_source)
        .expect("the reversed set-bit premise should prove the masked word is nonzero");

    let offset = click_source.find("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("the smart uint64 inequality should expand");
    assert!(
        expanded.contains("rewrite((word & 1u64) == 1u64);"),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_click_theorems(&expanded)
        .expect("the explicit uint64 inequality certificate should independently reverify");
}

#[test]
fn uint64_bit_test_inequality_rejects_missing_false_and_malformed_evidence() {
    let insufficient = r#"
        theorem low_bits_match_is_not_enough(word: uint64, other: uint64) {
            requires (word & 1u64) == (other & 1u64);
            ensures (word & 1u64) != 0u64 by { simp(); }
        }
    "#;
    verify_click_theorems(insufficient)
        .expect_err("equal low bits do not establish that either low bit is set");

    let false_claim = r#"
        theorem clear_low_bit_is_not_nonzero(word: uint64) {
            requires (word & 1u64) == 0u64;
            ensures (word & 1u64) != 0u64 by { simp(); }
        }
    "#;
    verify_click_theorems(false_claim)
        .expect_err("a premise that clears the bit must refute the nonzero claim");

    let unavailable_rewrite = r#"
        theorem unproved_set_bit_cannot_be_a_certificate(word: uint64) {
            ensures (word & 1u64) != 0u64 by {
                rewrite((word & 1u64) == 1u64);
                normalize();
            }
        }
    "#;
    let error = verify_click_theorems(unavailable_rewrite)
        .expect_err("an explicit certificate may not cite an unavailable set-bit equality");
    assert!(
        error
            .message()
            .contains("`rewrite` requires its equality to be an exact available fact"),
        "unexpected malformed-certificate error: {}",
        error.message()
    );
}

#[test]
fn pure_rewrite_retains_a_structural_surface_successor_for_simp() {
    let click_source = r#"
        theorem rewrite_pair(x: int32, y: int32, z: int32) {
            requires x == y;
            requires y == 0;
            requires z == 0;
            ensures x <= 0 and z <= 0 by {
                rewrite(x == y);
                simp();
            }
        }
    "#;

    let verified = verify_click_theorems(click_source);
    verified.expect("rewrite followed by structural simp should remain on Proof");

    let simp_offset = click_source
        .find("simp();")
        .expect("source should contain the structural smart step");
    let position = expansion::position_at_offset(click_source, simp_offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("the retained rewrite successor should expand");
    assert_eq!(expanded.matches("rewrite(").count(), 3, "{expanded}");
    assert!(expanded.contains("both {"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_click_theorems(&expanded)
        .expect("the expanded rewrite and structural child proofs should verify independently");
}

#[test]
fn restricted_simp_after_unfold_expands_explicit_conjunction_extraction() {
    let click_source = r#"
            predicate equality_chain(x: int32, y: int32, z: int32) {
                x == y and y == z
            }

            theorem equality_transitive_after_unfold(x: int32, y: int32, z: int32) {
                requires equality_chain(x, y, z);
                ensures x == z by {
                    unfold(equality_chain);
                    simp() using {
                        x == y;
                        y == z;
                    }
                }
            }
        "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    verify_c0_sources(click_source, &[]).expect("conjunction elimination should verify");
    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("conjunction elimination should have an explicit expansion");
    assert!(expanded.contains("extract(x == y);"), "{expanded}");
    assert!(expanded.contains("extract(y == z);"), "{expanded}");
    assert!(expanded.contains("normalize() using"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[])
        .expect("explicit conjunction-elimination certificate should check");
    // Delete the supporting equality itself: removing an extract step alone
    // leaves the true conjunction available in the checked context.
    for retained in ["x == y", "y == z"] {
        let missing = expanded.replace("x == y and y == z", retained);
        assert_ne!(missing, expanded);
        assert!(verify_c0_sources(&missing, &[]).is_err());
    }
}

#[test]
fn restricted_simp_expands_strict_order_to_nonstrict_theorem_application() {
    let click_source = r#"
            theorem strict_order_implies_nonstrict(x: int32, y: int32) {
                requires x < y;
                ensures x <= y by {
                    simp() using {
                        x < y;
                    }
                }
            }
        "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("strict-to-nonstrict simp should have an explicit certificate");
    assert!(
        expanded.contains("apply(int32_less_than_implies_less_equal(x, y)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded strict-order proof should check");
}

#[test]
fn post_execution_simp_applies_strict_order_rule() {
    let c_source = r#"
        int32 identity(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x) {
            requires x < 10;
            ensures result <= 10;
        } by {
            execute();
            simp();
        }
    "#;
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("post-execution strict-order simp should expand");
    assert!(
        expanded.contains("apply(int32_less_than_implies_less_equal("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("expanded post-execution strict-order proof should check");
}

#[test]
fn restricted_simp_expands_negated_strict_order_to_greater_equal() {
    let click_source = r#"
        theorem not_negative_is_nonnegative(x: int32) {
            requires not (x < 0);
            ensures x >= 0 by {
                simp() using {
                    not (x < 0);
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("negated strict-order simp should expand");
    assert!(
        expanded.contains("apply(int32_not_less_than_implies_greater_equal(x, 0)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded negated-order proof should check");
}

#[test]
fn post_execution_simp_expands_successor_strict_increase() {
    let c_source = r#"
        int32 increment(int32 x) {
            return x + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment.c";

        int32 increment(int32 x) {
            requires x < 2147483647;
            ensures x < result;
        } by {
            execute();
            simp();
        }
    "#;
    let verified = verify_c0_sources(click_source, &[("increment.c", c_source)]);
    verified.expect("the typed strict-increment rule should verify through the fixed-state Proof");
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("increment.c", c_source)], line, column)
            .expect("post-execution successor proof should expand");
    assert!(
        expanded.contains("apply(int32_increment_strictly_increases("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment.c", c_source)])
        .expect("expanded successor proof should check");
}

#[test]
fn post_execution_simp_expands_increment_definedness() {
    let c_source = r#"
        int32 increment(int32 x) {
            return x + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment.c";

        int32 increment(int32 x) {
            requires 2147483647 > x;
            ensures defined(x + 1);
        } by {
            execute();
            simp();
        }
    "#;
    let verified = verify_c0_sources(click_source, &[("increment.c", c_source)]);
    verified
        .expect("the typed increment-definedness rule should verify through the fixed-state Proof");
    let offset = click_source.rfind("simp()").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment.c", c_source)],
        position.line,
        position.column,
    )
    .expect("post-execution increment-definedness proof should expand");
    assert!(
        expanded.contains("apply(int32_increment_below_max_is_defined("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment.c", c_source)])
        .expect("expanded increment-definedness proof should check");
}

#[test]
fn post_execution_simp_expands_increment_lower_bound() {
    let c_source = r#"
        int32 increment_nonnegative(int32 x) {
            return x + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment_nonnegative.c";

        int32 increment_nonnegative(int32 x) {
            requires 0 <= x;
            requires x < 2147483647;
            ensures 0 <= result;
        } by {
            execute();
            simp();
        }
    "#;
    let verified = verify_c0_sources(click_source, &[("increment_nonnegative.c", c_source)]);
    verified
        .expect("the typed increment-lower-bound rule should verify through the fixed-state Proof");
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment_nonnegative.c", c_source)],
        line,
        column,
    )
    .expect("post-execution increment lower bound should expand");
    assert!(
        expanded.contains("apply(int32_increment_lower_bound("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment_nonnegative.c", c_source)])
        .expect("expanded increment lower-bound proof should check");
}

#[test]
fn post_execution_simp_expands_order_equality_closure() {
    let c_source = r#"
        int32 identity_at_bound(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity_at_bound.c";

        int32 identity_at_bound(int32 x) {
            requires x <= 1;
            requires not (x < 1);
            ensures result == 1;
        } by {
            execute();
            simp();
        }
    "#;
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity_at_bound.c", c_source)],
        line,
        column,
    )
    .expect("post-execution order equality should expand");
    assert!(
        expanded.contains("apply(int32_less_equal_and_not_less_than_implies_equal("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity_at_bound.c", c_source)])
        .expect("expanded order-equality proof should check");
}

#[test]
fn restricted_simp_expands_nonstrict_unequal_order() {
    let click_source = r#"
        theorem nonstrict_unequal_is_strict(left: int32, right: int32) {
            requires left <= right;
            requires not (left == right);
            ensures left < right by {
                simp();
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("nonstrict unequal order should verify through Proof");
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("nonstrict unequal order should expand");
    assert!(
        expanded
            .contains("apply(int32_less_equal_and_not_equal_implies_less_than(left, right)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_click_theorems(&expanded).expect("nonstrict unequal certificate should check");
}

#[test]
fn post_execution_simp_expands_increment_upper_bound() {
    let c_source = r#"
        int32 increment_below(int32 x) {
            return x + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment_below.c";

        int32 increment_below(int32 x) {
            requires x < 10;
            ensures result <= 10;
        } by {
            execute();
            simp();
        }
    "#;
    let verified = verify_c0_sources(click_source, &[("increment_below.c", c_source)]);
    verified.expect("the typed increment bound should verify through the fixed-state Proof");
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("increment_below.c", c_source)],
        line,
        column,
    )
    .expect("post-execution increment upper bound should expand");
    assert!(
        expanded.contains("apply(int32_increment_upper_bound("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment_below.c", c_source)])
        .expect("expanded increment upper-bound proof should check");
}

#[test]
fn post_execution_simp_expands_strict_transitivity() {
    let c_source = r#"
        int32 return_first(int32 first, int32 middle, int32 last) {
            return first;
        }
    "#;
    let click_source = r#"
        verifying "return_first.c";

        int32 return_first(int32 first, int32 middle, int32 last) {
            requires first < middle;
            requires middle < last;
            ensures result < last;
        } by {
            execute();
            simp();
        }
    "#;
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("return_first.c", c_source)], line, column)
            .expect("post-execution strict transitivity should expand");
    assert!(
        expanded.contains("apply(int32_less_than_transitive("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("return_first.c", c_source)])
        .expect("expanded strict-transitivity proof should check");
}

#[test]
fn post_execution_simp_expands_greater_equal_transitivity() {
    let c_source = r#"
        int32 return_last(int32 first, int32 middle, int32 last) {
            return last;
        }
    "#;
    let click_source = r#"
        verifying "return_last.c";

        int32 return_last(int32 first, int32 middle, int32 last) {
            requires first <= middle;
            requires middle <= last;
            ensures result >= first;
        } by {
            execute();
            simp();
        }
    "#;
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("return_last.c", c_source)], line, column)
            .expect("post-execution non-strict transitivity should expand");
    assert!(
        expanded.contains("apply(int32_greater_equal_transitive("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("return_last.c", c_source)])
        .expect("expanded non-strict-transitivity proof should check");
}

#[test]
fn post_execution_simp_expands_greater_equal_increment_bound() {
    let c_source = r#"
        int32 increment_ge(int32 value) {
            return value + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment_ge.c";

        int32 increment_ge(int32 value) {
            requires value >= 0;
            requires value < 2147483647;
            ensures result >= 0;
        } by {
            execute();
            simp();
        }
    "#;
    let verified = verify_c0_sources(click_source, &[("increment_ge.c", c_source)]);
    verified.expect(
        "the typed greater-equal increment rule should verify through the fixed-state Proof",
    );
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("increment_ge.c", c_source)], line, column)
            .expect("post-execution greater-equal increment bound should expand");
    assert!(
        expanded.contains("apply(int32_increment_greater_equal_lower_bound("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment_ge.c", c_source)])
        .expect("expanded greater-equal increment proof should check");
}

#[test]
fn post_execution_simp_expands_strict_greater_increment_bound() {
    let c_source = r#"
        int32 increment_gt(int32 value) {
            return value + 1;
        }
    "#;
    let click_source = r#"
        verifying "increment_gt.c";

        int32 increment_gt(int32 value) {
            requires value >= 0;
            requires value < 2147483647;
            ensures result > 0;
        } by {
            execute();
            simp();
        }
    "#;
    let verified = verify_c0_sources(click_source, &[("increment_gt.c", c_source)]);
    verified.expect(
        "the typed strict-greater increment rule should verify through the fixed-state Proof",
    );
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("increment_gt.c", c_source)], line, column)
            .expect("post-execution strict-greater increment bound should expand");
    assert!(
        expanded.contains("apply(int32_increment_greater_than_lower_bound("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("increment_gt.c", c_source)])
        .expect("expanded strict-greater increment proof should check");
}

#[test]
fn post_execution_simp_expands_greater_order_equality() {
    let c_source = r#"
        int32 identity_zero(int32 value) {
            return value;
        }
    "#;
    let click_source = r#"
        verifying "identity_zero.c";

        int32 identity_zero(int32 value) {
            requires value >= 0;
            requires not (value > 0);
            ensures result == 0;
        } by {
            execute();
            simp();
        }
    "#;
    let verified = verify_c0_sources(click_source, &[("identity_zero.c", c_source)]);
    verified.expect("post-execution >=/not-> equality should verify through Proof");

    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity_zero.c", c_source)], line, column)
            .expect("post-execution greater-order equality should expand");
    assert!(
        expanded.contains("apply(int32_greater_equal_and_not_greater_than_implies_equal("),
        "{expanded}"
    );
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity_zero.c", c_source)])
        .expect("expanded greater-order equality should check");
}

#[test]
fn post_execution_simp_composes_negated_successor_bound() {
    let c_source = r#"
        int32 identity_at_least_one(int32 value) {
            return value;
        }
    "#;
    let click_source = r#"
        verifying "identity_at_least_one.c";

        int32 identity_at_least_one(int32 value) {
            requires not (value < 2);
            ensures result >= 1;
        } by {
            execute();
            simp();
        }
    "#;
    let verified = verify_c0_sources(click_source, &[("identity_at_least_one.c", c_source)]);
    verified.expect("the typed successor-bound Proof should verify");
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("identity_at_least_one.c", c_source)],
        line,
        column,
    )
    .expect("post-execution successor lower bound should expand");
    // The negated bound is the kernel's condition with the other value, so
    // the successor bound is an available fact and the chain needs only the
    // transitive step.
    assert!(
        expanded.contains("apply(int32_greater_equal_transitive("),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity_at_least_one.c", c_source)])
        .expect("expanded successor lower-bound proof should check");
}

#[test]
fn restricted_simp_composes_negated_successor_bound() {
    let click_source = r#"
        theorem not_below_two_is_at_least_one(value: int32) {
            requires not (value < 2);
            ensures value >= 1 by {
                simp() using {
                    not (value < 2);
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the restricted successor-bound Proof should verify");
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("restricted successor lower bound should expand");
    assert!(
        expanded.contains("apply(int32_not_less_than_implies_greater_equal("),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_greater_equal_transitive("),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded restricted successor proof should check");
}

#[test]
fn post_execution_simp_unfolds_predicate_goal_explicitly() {
    let c_source = r#"
        int32 compare_swap2(int32* p) {
            int32 tmp;
            if (p[1] < p[0]) {
                tmp = p[0];
                p[0] = p[1];
                p[1] = tmp;
            } else {
                tmp = 0;
            }
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "compare_swap2.c";

        predicate sorted_pair(p: int32*) {
            p[0] <= p[1]
        }

        int32 compare_swap2(int32* p) {
            consumes p[0..2];
            ensures sorted_pair(p);
        } by {
            execute();
            simp();
        }
    "#;
    let offset = click_source.rfind("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("compare_swap2.c", c_source)], line, column);
    let expanded = expanded.expect("post-execution predicate goal should expand");
    assert!(expanded.contains("unfold(sorted_pair);"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_less_than_implies_less_equal("),
        "{expanded}"
    );
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    let reverified = { verify_c0_sources(&expanded, &[("compare_swap2.c", c_source)]) };
    reverified.expect("expanded predicate-goal proof should independently reverify");

    let corrupted = expanded.replacen("unfold(sorted_pair);", "unfold(missing);", 1);
    assert_ne!(
        corrupted, expanded,
        "the expansion should expose its checked predicate unfold"
    );
    let corrupted_result = { verify_c0_sources(&corrupted, &[("compare_swap2.c", c_source)]) };
    corrupted_result.expect_err("a corrupted branched predicate expansion must be rejected");

    let condition = "at(statement(1).entry, p[1]) < at(statement(1).entry, p[0])";
    let wrong_condition = "at(statement(1).entry, p[0]) < at(statement(1).entry, p[1])";
    let corrupted = expanded.replacen(condition, wrong_condition, 1);
    assert_ne!(
        corrupted, expanded,
        "the expansion should expose its checked outcome condition"
    );
    let corrupted_result = { verify_c0_sources(&corrupted, &[("compare_swap2.c", c_source)]) };
    corrupted_result.expect_err("a corrupted outcome condition must be rejected");
}

#[test]
fn pure_simp_retains_one_selected_equality_rewrite_before_normalize() {
    let click_source = r#"
        theorem predecessor_of_one_is_nonnegative(value: int32) {
            requires value == 1;

            ensures 0 <= value - 1 by {
                simp();
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the selected equality rewrite should close on the pure Proof");

    let offset = click_source.find("simp()").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("the retained equality-refinement path should expand");
    assert!(expanded.contains("rewrite(value == 1);"), "{expanded}");
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_click_theorems(&expanded).expect("the expanded rewrite path should check");
}

#[test]
fn restricted_simp_expands_increment_upper_bound_to_theorem_application() {
    let click_source = r#"
        theorem increment_stays_bounded(value: int32, upper: int32) {
            requires value < upper;
            ensures value + 1 <= upper by {
                simp() using {
                    value < upper;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the typed increment rule should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("increment upper-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_increment_upper_bound(value, upper)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("value < upper;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should check");
}

#[test]
fn restricted_simp_expands_positive_to_nonnegative_theorem_application() {
    let click_source = r#"
        theorem positive_is_nonnegative(value: int32) {
            requires 0 < value;
            ensures 0 <= value by {
                simp() using {
                    0 < value;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("positive-to-nonnegative simp should verify through Proof");
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("positive-to-nonnegative simp should expand");
    assert!(
        expanded.contains("apply(int32_positive_is_nonnegative(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("0 < value;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should check");
}

#[test]
fn restricted_simp_expands_positive_predecessor_to_theorem_application() {
    let click_source = r#"
        theorem positive_predecessor_is_nonnegative(value: int32) {
            requires 0 < value;
            ensures 0 <= value - 1 by {
                simp() using {
                    0 < value;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the typed predecessor-nonnegative rule should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("positive-predecessor simp should expand");
    assert!(
        expanded.contains("apply(int32_positive_predecessor_is_nonnegative(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("0 < value;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should check");
}

#[test]
fn restricted_simp_expands_positive_predecessor_decrease_to_theorem_application() {
    let click_source = r#"
        theorem positive_predecessor_decreases(value: int32) {
            requires 0 < value;
            ensures value - 1 < value by {
                simp() using {
                    0 < value;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the typed predecessor-decrease rule should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("positive-predecessor decrease simp should expand");
    assert!(
        expanded.contains("apply(int32_positive_predecessor_strictly_decreases(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("0 < value;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should check");
}

#[test]
fn restricted_simp_expands_predecessor_upper_bound_to_theorem_application() {
    let click_source = r#"
        theorem predecessor_keeps_upper_bound(value: int32, bound: int32) {
            requires 0 <= value;
            requires value <= bound;
            ensures value - 1 <= bound by {
                simp() using {
                    0 <= value;
                    value <= bound;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the typed predecessor-upper-bound rule should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("predecessor upper-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_nonnegative_predecessor_upper_bound(value, bound)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("0 <= value;"), "{expanded}");
    assert!(expanded.contains("value <= bound;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded predecessor theorem should check");
}

#[test]
fn restricted_simp_retains_nested_one_le_predecessor_nonnegative_proof() {
    let click_source = r#"
        theorem one_le_predecessor_is_nonnegative(value: int32) {
            requires 1 <= value;
            ensures 0 <= value - 1 by {
                simp() using {
                    1 <= value;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the nested predecessor proof should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("one-le predecessor proof should expand");
    assert!(expanded.contains("have 0 < value"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_increment_less_equal_implies_less_than(0, value)) using"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_positive_predecessor_is_nonnegative(value)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded nested predecessor proof should check");
}

#[test]
fn restricted_simp_retains_nested_one_le_predecessor_decrease_proof() {
    let click_source = r#"
        theorem one_le_predecessor_decreases(value: int32) {
            requires 1 <= value;
            ensures value - 1 < value by {
                simp() using {
                    1 <= value;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the nested predecessor-decrease proof should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("one-le predecessor-decrease proof should expand");
    assert!(expanded.contains("have 0 < value"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_increment_less_equal_implies_less_than(0, value)) using"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_positive_predecessor_strictly_decreases(value)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded)
        .expect("expanded nested predecessor-decrease proof should check");
}

#[test]
fn restricted_simp_retains_equal_one_predecessor_path() {
    let click_source = r#"
        theorem equal_one_predecessor_is_nonnegative(value: int32) {
            requires 1 == value;
            ensures 0 <= value - 1 by {
                simp() using {
                    1 == value;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the equal-one predecessor proof should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("equal-one predecessor proof should expand");
    assert!(expanded.contains("have 1 <= value"), "{expanded}");
    assert!(expanded.contains("rewrite(value == 1)"), "{expanded}");
    assert!(expanded.contains("have 0 < value"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_positive_predecessor_is_nonnegative(value)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded equal-one predecessor proof should check");
}

#[test]
fn restricted_simp_retains_equal_one_predecessor_zero_path() {
    let click_source = r#"
        theorem equal_one_predecessor_is_zero(value: int32) {
            requires 1 == value;
            ensures value - 1 == 0 by {
                simp() using {
                    1 == value;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the predecessor-zero proof should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("equal-one predecessor-zero proof should expand");
    // Shared class folding closes this with the selected premise directly;
    // an intermediate rewrite is no longer required.
    assert!(expanded.contains("normalize() using"), "{expanded}");
    assert!(expanded.contains("normalize()"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded predecessor-zero proof should check");
}

#[test]
fn restricted_simp_expands_strict_increment_to_theorem_application() {
    let click_source = r#"
            theorem increment_is_greater(value: int32, upper: int32) {
                requires value < upper;
                ensures value < value + 1 by {
                    simp() using {
                        value < upper;
                    }
                }
            }
        "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the typed strict-increment rule should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("strict increment should expand");
    assert!(
        expanded.contains("apply(int32_increment_strictly_increases(value, upper)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("value < upper;"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("strict increment certificate should check");
}

#[test]
fn simp_expands_increment_definedness_to_theorem_application() {
    let click_source = r#"
        theorem increment_is_defined(value: int32) {
            requires value < 2147483647;
            ensures defined(value + 1) by {
                simp();
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the typed increment-definedness rule should verify through the pure Proof");
    let offset = click_source.find("simp()").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("increment-definedness simp should expand");
    assert!(
        expanded.contains("apply(int32_increment_below_max_is_defined(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("value < 2147483647;"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded increment-definedness proof should check");
}

#[test]
fn restricted_simp_expands_increment_lower_bound_to_theorem_application() {
    let click_source = r#"
        theorem increment_preserves_lower_bound(
            value: int32,
            lower: int32,
            upper: int32
        ) {
            requires lower <= value;
            requires value < upper;
            ensures lower <= value + 1 by {
                simp() using {
                    lower <= value;
                    value < upper;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the typed increment-lower-bound rule should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("increment lower-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_increment_lower_bound(value, lower, upper)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("lower <= value;"), "{expanded}");
    assert!(expanded.contains("value < upper;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should check");
}

#[test]
fn restricted_simp_expands_increment_order_to_theorem_application() {
    let click_source = r#"
        theorem increment_preserves_order(
            value: int32,
            lower: int32,
            upper: int32
        ) {
            requires lower <= value;
            requires value < upper;
            ensures lower + 1 <= value + 1 by {
                simp() using {
                    lower <= value;
                    value < upper;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the typed increment-order rule should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("increment order simp should expand");
    assert!(
        expanded.contains("apply(int32_increment_preserves_order(value, lower, upper)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("lower <= value;"), "{expanded}");
    assert!(expanded.contains("value < upper;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should check");
}

#[test]
fn restricted_simp_rewrites_a_named_successor_before_increment_order() {
    let c_source = r#"
        int32 named_successor(int32 value) {
            int32 successor;
            successor = value + 1;
            return successor;
        }
    "#;
    let click_source = r#"
        verifying "named_successor.c";

        int32 named_successor(int32 value) {
            requires 0 <= value;
            requires value < 2147483647;
            ensures 1 <= result by {
                execute();
                simp();
            }
        }
    "#;
    let offset = click_source.find("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("named_successor.c", c_source)],
        line,
        column,
    )
    .expect("named successor order should lower to an explicit rewrite and increment rule");
    assert!(
        expanded.contains("apply(int32_increment_preserves_order("),
        "{expanded}"
    );
    assert!(expanded.contains("at(function.entry, value)"), "{expanded}");
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_c0_sources(&expanded, &[("named_successor.c", c_source)])
        .expect("named successor certificate should check");
}

#[test]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn restricted_simp_certifies_unchanged_prefix_after_indexed_store() {
    let c_source = r#"
        struct vector {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 vector_push(struct vector* owner, int32 value) {
            int32 index;
            int32* data;
            index = owner->len;
            data = owner->data;
            data[index] = value;
            owner->len = index + 1;
            return owner->len;
        }
    "#;
    let click_source = r#"
        resource vector_storage(owner: struct vector*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns owner->data[0..owner->cap];
            fact 0 <= owner->len;
            fact owner->len <= owner->cap;
            fact owner->cap <= 1073741823;
            fact viewable(owner->data[0..owner->len]);
            fact separate(memory(*owner), memory(owner->data[0..owner->cap]));
        }

        verifying "vector_push.c";

        int32 vector_push(struct vector* owner, int32 value) {
            requires owner->len < owner->cap;
            owns vector_storage(owner);
            ensures result == old(owner->len) + 1;
            ensures owner->len == old(owner->len) + 1;
            ensures owner->data[old(owner->len)] == value;
            ensures owner->cap == old(owner->cap);
            ensures owner->data == old(owner->data);
            ensures forall (k: int32) {
                0 <= k and k < old(owner->len) implies
                    owner->data[k] == old(owner->data[k])
            };
        } by {
            unfold(vector_storage(owner));
            execute();
            fold(vector_storage(owner));
            simp();
        }
    "#;
    // The first goal at `simp` can already be an available fact. Expand
    // the whole contract so this checks the quantified prefix as well.
    let expanded = expand_c0_claim_source_by_label(
        click_source,
        &[("vector_push.c", c_source)],
        "vector_push.contract",
    )
    .expect("unchanged-prefix simp should expand to a checkable frame transport");
    assert!(
        expanded.contains("transport(old(owner->data[k])"),
        "{expanded}"
    );
    assert!(expanded.contains("k < old(owner->len)"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(!expanded.contains("auto();"), "{expanded}");
    verify_c0_sources(&expanded, &[("vector_push.c", c_source)])
        .expect("unchanged-prefix certificate should check");
    let includes_store = expanded.replacen(
        "k < old(owner->len) implies",
        "k <= old(owner->len) implies",
        1,
    );
    assert_ne!(includes_store, expanded);
    verify_c0_sources(&includes_store, &[("vector_push.c", c_source)])
        .expect_err("the unchanged prefix must exclude the overwritten element");
}

#[test]
fn restricted_simp_expands_adjacent_order_to_theorem_application() {
    let click_source = r#"
        theorem two_at_most_implies_one_below(value: int32) {
            requires 2 <= value;
            ensures 1 < value by {
                simp() using {
                    2 <= value;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the typed adjacent-order rule should verify through the pure Proof");
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("adjacent order simp should expand");
    assert!(
        expanded.contains("apply(int32_increment_less_equal_implies_less_than(1, value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("2 <= value;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should check");
}

#[test]
fn smart_simp_transcribes_a_three_edge_signed_order_path() {
    let click_source = r#"
        theorem three_edge_order_chain(
            first: int32,
            second: int32,
            third: int32,
            last: int32
        ) {
            requires first <= second;
            requires second < third;
            requires third <= last;
            ensures first < last by {
                simp();
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the checked order-path Proof should verify");
    let offset = click_source.find("simp();").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("the retained three-edge order path should expand");
    assert!(
        expanded
            .contains("apply(int32_less_equal_less_than_transitive(first, second, third)) using"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_less_than_less_equal_transitive(first, third, last)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_click_theorems(&expanded).expect("the transcribed order path should check");
}

#[test]
fn smart_simp_transcribes_a_three_edge_bitvector_equality_path() {
    let click_source = r#"
        theorem three_edge_equality_chain(
            first: int32,
            second: int32,
            third: int32,
            last: int32
        ) {
            requires second == first;
            requires second == third;
            requires third == last;
            ensures first == last by {
                simp();
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the checked equality-path Proof should verify");

    let offset = click_source.find("simp();").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("the retained three-edge equality path should expand");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_click_theorems(&expanded).expect("the transcribed equality path should check");
}

#[test]
fn smart_simp_retains_both_signed_equality_rules_as_named_steps() {
    let click_source = r#"
        theorem le_and_not_lt_are_equal(left: int32, right: int32) {
            requires left <= right;
            requires not (left < right);
            ensures left == right by {
                simp();
            }
        }

        theorem ge_and_not_gt_are_equal(left: int32, right: int32) {
            requires left >= right;
            requires not (left > right);
            ensures left == right by {
                simp();
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the typed <=/not-< equality rule should verify through Proof");

    let offset = click_source.find("simp();").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("the retained equality theorem should expand");
    assert!(
        expanded
            .contains("apply(int32_less_equal_and_not_less_than_implies_equal(left, right)) using"),
        "{expanded}"
    );
    verify_click_theorems(&expanded).expect("the named equality step should independently check");

    let offset = click_source.rfind("simp();").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("the retained >=/not-> equality theorem should expand");
    assert!(
        expanded.contains(
            "apply(int32_greater_equal_and_not_greater_than_implies_equal(left, right)) using"
        ),
        "{expanded}"
    );
    verify_click_theorems(&expanded)
        .expect("the named >=/not-> equality step should independently check");
}

#[test]
fn outcome_simp_consumes_its_recorded_bitvector_equality_path() {
    let c_source = r#"
        int32 choose_first(int32 first, int32 second, int32 third, int32 last) {
            return first;
        }
    "#;
    let click_source = r#"
        verifying "choose_first.c";

        int32 choose_first(int32 first, int32 second, int32 third, int32 last) {
            requires second == first;
            requires second == third;
            requires third == last;
            ensures result == last;
        } by {
            execute();
            simp();
        }
    "#;
    let verified = verify_c0_sources(click_source, &[("choose_first.c", c_source)]);
    verified.expect("the outcome equality path should verify");

    let offset = click_source.rfind("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("choose_first.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained outcome equality path should expand");
    assert!(!expanded.contains("simp();"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &[("choose_first.c", c_source)])
        .expect("the transcribed outcome equality path should check");
}

#[test]
fn outcome_simp_applies_theorems_through_its_recorded_order_path() {
    let c_source = r#"
        int32 validate_chain(int32 first, int32 second, int32 third, int32 last) {
            return first;
        }
    "#;
    let click_source = r#"
        verifying "validate_chain.c";

        int32 validate_chain(int32 first, int32 second, int32 third, int32 last) {
            requires first <= second;
            requires second < third;
            requires third <= last;
            ensures first < last;
        } by {
            execute();
            simp();
        }
    "#;
    let verified = verify_c0_sources(click_source, &[("validate_chain.c", c_source)]);
    verified.expect("the outcome order path should verify through the fixed-state Proof");

    let offset = click_source.rfind("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("validate_chain.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained outcome theorem path should expand");
    assert!(
        expanded.contains(
            "apply(int32_less_equal_less_than_transitive(at(function.entry, first), at(function.entry, second), at(function.entry, third))) using"
        ),
        "{expanded}"
    );
    assert!(
        expanded.contains(
            "apply(int32_less_than_less_equal_transitive(at(function.entry, first), at(function.entry, third), at(function.entry, last))) using"
        ),
        "{expanded}"
    );
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &[("validate_chain.c", c_source)])
        .expect("the transcribed outcome theorem path should check");
}

#[test]
fn restricted_simp_expands_constant_order_weakening_to_theorem_application() {
    let click_source = r#"
        theorem three_at_least_implies_nonnegative(value: int32) {
            requires 3 <= value;
            ensures 0 <= value by {
                simp() using {
                    3 <= value;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the constant lower-bound weakening should verify");
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("constant order weakening simp should expand");
    assert!(
        expanded.contains("apply(int32_less_equal_transitive(0, 3, value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("3 <= value;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should check");
}

#[test]
fn restricted_simp_expands_constant_strict_upper_bound_to_theorem_application() {
    let click_source = r#"
        theorem three_at_most_implies_below_five(value: int32) {
            requires value <= 3;
            ensures value < 5 by {
                simp() using {
                    value <= 3;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the constant strict upper-bound weakening should verify");
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("constant strict upper-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_less_equal_less_than_transitive(value, 3, 5)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("value <= 3;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded strict upper-bound proof should check");
}

#[test]
fn restricted_simp_retains_increment_under_a_larger_constant() {
    let click_source = r#"
        theorem increment_three_at_most_is_five_at_most(value: int32) {
            requires value <= 3;
            ensures value + 1 <= 5 by {
                simp() using {
                    value <= 3;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the increment constant-bound rule should verify through Proof");
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("increment constant-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_less_equal_less_than_transitive(value, 3, 5)) using"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_increment_upper_bound(value, 5)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("value <= 3;"), "{expanded}");
    assert!(expanded.contains("value < 5;"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded increment constant-bound proof should check");
}

#[test]
fn restricted_simp_retains_symbolic_add_definedness_theorem() {
    let click_source = r#"
        theorem symbolic_add_is_defined(value: int32, amount: int32) {
            requires amount >= 0;
            requires 2147483647 - amount >= value;
            ensures defined(value + amount) by {
                simp() using {
                    amount >= 0;
                    2147483647 - amount >= value;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the symbolic-add definedness rule should verify through Proof");
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("symbolic-add definedness simp should expand");
    assert!(
        expanded
            .contains("apply(int32_nonnegative_add_within_max_is_defined(value, amount)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("amount >= 0;"), "{expanded}");
    assert!(
        expanded.contains("2147483647 - amount >= value;"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp() using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded symbolic-add definedness proof should check");
}

#[test]
fn restricted_simp_retains_symbolic_subtract_definedness_theorem() {
    let click_source = r#"
        theorem symbolic_subtract_is_defined(value: int32, amount: int32) {
            requires amount >= 0;
            requires value >= amount;
            ensures defined(value - amount) by {
                simp() using {
                    amount >= 0;
                    value >= amount;
                }
            }
        }
    "#;
    let verified = verify_click_theorems(click_source);
    verified.expect("the symbolic-subtract definedness rule should verify through Proof");
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("symbolic-subtract definedness simp should expand");
    assert!(
        expanded.contains(
            "apply(int32_nonnegative_subtract_within_value_is_defined(value, amount)) using"
        ),
        "{expanded}"
    );
    assert!(expanded.contains("amount >= 0;"), "{expanded}");
    assert!(expanded.contains("value >= amount;"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    verify_click_theorems(&expanded)
        .expect("expanded symbolic-subtract definedness proof should check");
}

#[test]
fn restricted_simp_retains_one_plus_operand_specific_theorems() {
    let cases = [
        (
            r#"
                theorem one_plus_is_defined(value: int32) {
                    requires 2147483647 > value;
                    ensures defined(1 + value) by {
                        simp() using { 2147483647 > value; }
                    }
                }
            "#,
            "one_plus_is_defined.ensures_0",
            "apply(int32_increment_left_below_max_is_defined(value)) using",
        ),
        (
            r#"
                theorem one_plus_increases(value: int32) {
                    requires 2147483647 > value;
                    ensures value < 1 + value by {
                        simp() using { 2147483647 > value; }
                    }
                }
            "#,
            "one_plus_increases.ensures_0",
            "apply(int32_increment_left_strictly_increases(value)) using",
        ),
    ];
    for (click_source, _, application) in cases {
        let verified = verify_click_theorems(click_source);
        verified.expect("the operand-order-specific one-plus rule should verify through Proof");
        let offset = click_source.find("simp() using").unwrap();
        let position = expansion::position_at_offset(click_source, offset);
        let expanded =
            expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
                .expect("one-plus simp should expand");
        assert!(expanded.contains(application), "{expanded}");
        assert!(expanded.contains("2147483647 > value;"), "{expanded}");
        assert!(!expanded.contains("simp() using"), "{expanded}");
        verify_click_theorems(&expanded).expect("expanded one-plus proof should check");
    }
}

#[test]
fn restricted_simp_composes_equalities_with_adjacent_order() {
    let click_source = r#"
        theorem aliased_positive_bound(
            position: int32,
            bound: int32,
            length: int32
        ) {
            requires 1 <= length;
            requires bound == length;
            requires position == 0;
            ensures position < bound by {
                simp() using {
                    1 <= length;
                    bound == length;
                    position == 0;
                }
            }
        }
    "#;
    let offset = click_source.find("simp() using").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("rewrites followed by adjacent order should expand");
    // The equalities and the order are each one Integer fact, so one
    // certificate combines them without rewriting first.
    for cited in [
        "premise 0: bound == length",
        "premise 1: position == 0",
        "premise 2: 1 <= length",
    ] {
        assert!(expanded.contains(cited), "{cited}\n{expanded}");
    }
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("composed explicit certificate should check");
}

#[test]
fn restricted_simp_inside_have_expands_to_graph_normalization() {
    let c_source = r#"
            int32 identity(int32 x, int32 y, int32 z) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x, int32 y, int32 z) {
                requires x == y;
                requires y == z;
                ensures result == x;
            } by {
                have x == z by {
                    simp() using {
                        x == y;
                        y == z;
                    }
                }
                execute();
                simp();
            }
        "#;
    let offset = click_source
        .find("have x == z")
        .expect("proof should contain restricted simp have");
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("restricted have should verify");
    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("restricted simp have should expand");
    let expanded_have =
        &expanded[expanded.find("have x == z").unwrap()..expanded.find("execute();").unwrap()];
    assert!(expanded_have.contains("x == y;"), "{expanded_have}");
    assert!(
        expanded_have.contains("normalize() using"),
        "{expanded_have}"
    );
    assert!(expanded_have.contains("y == z;"), "{expanded_have}");
    assert!(!expanded_have.contains("simp() using"), "{expanded_have}");
    assert!(!expanded_have.contains("derive using"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("explicit equality have certificate should check");
    for premise in ["requires x == y;", "requires y == z;"] {
        let missing = expanded.replace(premise, "");
        assert_ne!(missing, expanded);
        assert!(verify_c0_sources(&missing, &[("identity.c", c_source)]).is_err());
    }
}

#[test]
fn restricted_simp_expands_loadable_subrange_to_explicit_transport() {
    let c_source = r#"
        int32 read_at(int32 data[], int32 index, int32 length) {
            return data[index];
        }
    "#;
    let click_source = r#"
        verifying "read_at.c";

        int32 read_at(int32 data[], int32 index, int32 length) {
            requires 0 <= index;
            requires index < length;
            views data[0..length];
            ensures result == old(data[index]);
        } by {
            have viewable(data[index..index + 1]) by {
                simp() using {
                    viewable(data[0..length]);
                    0 <= index;
                    index < length;
                }
            }
            execute();
            simp();
        }
    "#;
    let offset = click_source
        .find("have viewable(data[index..index + 1])")
        .unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let sources = [("read_at.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(click_source, &sources));
    verified.expect("the leading viewability have should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    let expanded = expand_c0_tactic_source_at(click_source, &sources, line, column)
        .expect("restricted simp viewability proof should expand");
    let expanded_have_start = expanded.find("have viewable(").unwrap();
    let expanded_have_end = expanded[expanded_have_start..]
        .find("execute();")
        .map(|relative| expanded_have_start + relative)
        .unwrap();
    let expanded_have = &expanded[expanded_have_start..expanded_have_end];
    assert!(
        expanded_have.contains(
            "transport(viewable(data[0..length]), viewable(data[index..(index + 1)])) using"
        ),
        "{expanded_have}"
    );
    assert!(expanded_have.contains("0 <= index;"), "{expanded_have}");
    assert!(expanded_have.contains("index < length;"), "{expanded_have}");
    let normalized_have = expanded_have
        .lines()
        .map(str::trim)
        .filter(|line| !line.is_empty())
        .collect::<Vec<_>>()
        .join("\n");
    assert_eq!(
        normalized_have,
        "have viewable(data[index..(index + 1)]) by {\n\
         transport(viewable(data[0..length]), viewable(data[index..(index + 1)])) using {\n\
         viewable(data[0..length]);\n\
         0 <= index;\n\
         index < length;\n\
         };\n\
         }"
    );
    assert!(!expanded_have.contains("simp() using"), "{expanded_have}");
    assert!(!expanded_have.contains("derive using"), "{expanded_have}");
    verify_c0_sources(&expanded, &sources).expect("explicit viewability transport should check");
}

#[test]
fn restricted_simp_rewrites_pointer_aliases_inside_memory_loads() {
    let c_source = r#"
        int32 alias_value(
            int32 original[],
            int32 alias[],
            int32 index,
            int32 length,
            int32 value
        ) {
            return value;
        }
    "#;
    let click_source = r#"
        verifying "alias_value.c";

        resource valued_array(data: int32*, length: int32, value: int32) {
            owns data[0..length];
            fact 1 <= length;
            fact data[0] == value;
        }

        int32 alias_value(
            int32 original[],
            int32 alias[],
            int32 index,
            int32 length,
            int32 value
        ) {
            requires index == 0;
            requires alias == original;
            owns valued_array(original, length, value);
            ensures alias[index] == value;
        } by {
            unfold(valued_array(original, length, value));
            step();
            have alias[index] == value by {
                simp() using {
                    original[0] == value;
                    alias == original;
                    index == 0;
                }
            }
            fold(valued_array(original, length, value));
            simp();
        }
    "#;
    let offset = click_source.find("have alias[index] == value").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let sources = [("alias_value.c", c_source)];

    let expanded = expand_c0_tactic_source_at(click_source, &sources, line, column)
        .expect("pointer-alias restricted simp should expand");
    let expanded_have_start = expanded.find("have alias[index] == value").unwrap();
    let expanded_have_end = expanded[expanded_have_start..]
        .find("fold(valued_array")
        .map(|relative| expanded_have_start + relative)
        .unwrap();
    let expanded_have = &expanded[expanded_have_start..expanded_have_end];
    // Indexed read congruence constructs a normalization certificate from
    // the selected premises without spelling intermediate rewrites.
    for selected in [
        "normalize() using {",
        "original[0] == value;",
        "alias == original;",
        "index == 0;",
    ] {
        assert!(expanded_have.contains(selected), "{expanded_have}");
    }
    assert!(!expanded_have.contains("simp() using"), "{expanded_have}");
    assert!(!expanded_have.contains("derive using"), "{expanded_have}");
    verify_c0_sources(&expanded, &sources)
        .expect("expanded pointer-alias certificate should check");
    // Normalization may query the maintained graph, so withdraw each
    // relation from the context as well as its explicit citation.
    for (clause, premise) in [
        ("fact data[0] == value;", "original[0] == value;"),
        ("requires alias == original;", "alias == original;"),
        ("requires index == 0;", "index == 0;"),
    ] {
        assert!(expanded.contains(clause));
        let missing_premise = expanded_have.replacen(premise, "", 1);
        let incomplete = expanded
            .replacen(expanded_have, &missing_premise, 1)
            .replacen(clause, "", 1);
        assert!(
            verify_c0_sources(&incomplete, &sources).is_err(),
            "the read-alias certificate must reject a context without `{clause}`"
        );
    }
}

#[test]
fn post_execution_restricted_simp_expands_without_derive() {
    let c_source = r#"
        int32 identity(int32 x, int32 y, int32 z) {
            return x;
        }
    "#;
    let click_source = r#"
        verifying "identity.c";

        int32 identity(int32 x, int32 y, int32 z) {
            requires x + 1 == y;
            requires y == z;
            ensures result + 1 == z;
        } by {
            execute();
            have x + 1 == z by {
                simp() using {
                    x + 1 == y;
                    y == z;
                }
            }
            simp();
        }
    "#;
    let offset = click_source.find("have x + 1 == z").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let sources = [("identity.c", c_source)];
    verify_c0_sources(click_source, &sources).expect("restricted simp should verify");
    let expanded = expand_c0_tactic_source_at(click_source, &sources, line, column).unwrap();
    let selected = &expanded[offset..];
    assert!(selected.contains("normalize() using"), "{selected}");
    assert!(selected.contains("(x + 1) == y;"), "{selected}");
    assert!(selected.contains("y == z;"), "{selected}");
    assert!(!selected.contains("derive using"), "{selected}");
    verify_c0_sources(&expanded, &sources).expect("explicit post-execution proof should check");
    for premise in ["requires x + 1 == y;", "requires y == z;"] {
        let missing = expanded.replace(premise, "");
        assert_ne!(missing, expanded);
        assert!(verify_c0_sources(&missing, &sources).is_err());
    }
}

#[test]
fn source_expander_lowers_smart_apply_inside_have() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            theorem int32_reflexive(value: int32) {
                ensures value == value by {
                    simp();
                }
            }

            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                have x == x by {
                    apply(int32_reflexive(x));
                }
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have x == x")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("the selected smart apply inside have should expand");
    let expanded_have = &expanded[expanded
        .find("have x == x")
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("execute()")
            .expect("expanded proof should retain its suffix")];
    assert!(expanded_have.contains("apply(int32_reflexive(x)) using {"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the expanded smart apply inside have should check");
}

#[test]
fn fixed_state_have_bare_apply_retains_and_checks_its_exact_premise() {
    let c_source = r#"
            int32 choose_second(int32 first, int32 second) {
                return second;
            }
        "#;
    let click_source = r#"
            theorem equality_symmetric(first: int32, second: int32) {
                requires first == second;
                ensures second == first by {
                    simp() using { first == second; }
                }
            }

            verifying "choose.c";

            int32 choose_second(int32 first, int32 second) {
                requires first == second;
                ensures second == first;
            } by {
                have second == first by {
                    apply(equality_symmetric(first, second));
                }
                step();
                assumption();
            }
        "#;
    let verified = verify_c0_sources(click_source, &[("choose.c", c_source)]);
    verified
        .expect("checked fixed-state apply should verify without ordinary certificate validation");
    let have_offset = click_source
        .find("have second == first")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("choose.c", c_source)], line, column)
            .expect("checked fixed-state apply should expand");
    let apply_offset = expanded
        .find("apply(equality_symmetric(first, second)) using {")
        .expect("expansion should retain the selected explicit step");
    let premise_relative = expanded[apply_offset..]
        .find("first == second;")
        .expect("explicit step should retain the theorem premise");
    let premise_offset = apply_offset + premise_relative;
    verify_c0_sources(&expanded, &[("choose.c", c_source)])
        .expect("the retained fixed-state proof should independently check");

    let mut corrupted = expanded.clone();
    corrupted.replace_range(
        premise_offset..premise_offset + "first == second;".len(),
        "",
    );
    let error = verify_c0_sources(&corrupted, &[("choose.c", c_source)])
        .expect_err("omitting the selected premise must invalidate the explicit proof");
    assert!(
        error.message().contains("required exact fact")
            || error.message().contains("unavailable exact premise"),
        "unexpected corrupted-certificate error: {}",
        error.message()
    );
}

#[test]
fn fixed_state_have_mixed_linear_smart_script_continues_on_checked_successors() {
    let c_source = r#"
            int32 choose_second(int32 first, int32 second) {
                return second;
            }
        "#;
    let click_source = r#"
            theorem equality_symmetric(first: int32, second: int32) {
                requires first == second;
                ensures second == first by {
                    simp() using { first == second; }
                }
            }

            verifying "choose.c";

            int32 choose_second(int32 first, int32 second) {
                requires (first == second) and (first >= 0);
                ensures result == second;
            } by {
                have second == first and first == second by {
                    extract(first == second);
                    apply(equality_symmetric(first, second));
                    simp();
                }
                step();
                simp();
            }
        "#;
    let verified = verify_c0_sources(click_source, &[("choose.c", c_source)]);
    verified.expect("smart apply should continue from its checked Proof successor");

    let have_offset = click_source
        .find("have second == first and first == second")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let expanded =
        expand_c0_tactic_source_at(click_source, &[("choose.c", c_source)], line, column)
            .expect("the retained apply-then-simp path should expand");
    let expanded_have = &expanded[expanded
        .find("have second == first and first == second")
        .or_else(|| expanded.find("have (second == first) and (first == second)"))
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("step()")
            .expect("expanded proof should retain its suffix")];
    assert!(
        expanded_have.contains("apply(equality_symmetric(first, second)) using {"),
        "{expanded_have}"
    );
    assert!(
        expanded_have.contains("extract(first == second);"),
        "{expanded_have}"
    );
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("choose.c", c_source)])
        .expect("the serialized retained proof should independently reverify");
}

#[test]
fn execution_bare_apply_selects_and_retains_its_step_through_proof() {
    let c_source = r#"
            int32 keep(int32 value, int32 upper) {
                return value;
            }
        "#;
    let click_source = r#"import click::machine_integer;

            verifying "keep.c";

            int32 keep(int32 value, int32 upper) {
                requires value < upper;
                ensures result <= upper;
            } by {
                apply(int32_less_than_implies_less_equal(value, upper));
                step();
                assumption();
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("keep.c", c_source)]);
    let verified = verified.expect("checked execution apply should verify");
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked execution apply should retain an expansion");
    assert!(matches!(
        expanded.first(),
        Some(ProofTactic::ApplyTheoremUsing { application, premises })
            if application.name == "click::machine_integer::int32_less_than_implies_less_equal" && premises.len() == 1
    ));
    let retained_source = verified[0]
        .expanded_proof_source()
        .expect("the checked execution apply should have canonical source");
    assert!(
        retained_source.contains(
            "apply(click::machine_integer::int32_less_than_implies_less_equal(value, upper)) using {"
        ),
        "the canonical source cites the library theorem by its qualified identity: {retained_source}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("keep.c", c_source)],
        "keep",
        CProofClaim::Ensure(0),
    )
    .expect("the checked execution apply should expand into source");
    verify_c0_sources(&expanded, &[("keep.c", c_source)])
        .expect("the retained execution theorem step should independently reverify");
}

#[test]
fn post_return_resource_exchange_accepts_a_preceding_pure_have() {
    let c_source = "int32 identity(int32 x) { return x; }";
    // A macro refold may change only the logical presentation. The second
    // unfold must use that current goal rather than an older C-body event.
    let click_source = r#"
        resource marker(x: int32) { fact x == x; }
        verifying "identity.c";
        int32 identity(int32 x) {
            owns marker(x);
            ensures result == x;
        } by {
            execute();
            have 1000 == 1000 by { normalize(); }
            unfold(marker(x));
            fold(marker(x));
            unfold(marker(x));
            fold(marker(x));
            simp();
        }
    "#;
    let sources = [("identity.c", c_source)];
    let verified_for_expansion = verify_c0_sources(click_source, &sources)
        .expect("a pure have must preserve the return resource presentation");
    let expanded = expand_checked_grouped_claim(click_source, &verified_for_expansion, "identity")
        .expect("the return resource exchange should expand");
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded return resource exchange should check independently");
}

#[test]
fn execution_resource_unfold_is_recorded_once_and_checks() {
    let c_source = r#"
        int32 discard(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "discard.c";

        int32 discard(int32 x) {
            consumes marker(x);
            ensures result == x;
        } by {
            unfold(marker(x));
            execute();
            assumption();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("discard.c", c_source)])
        .expect("the explicit resource unfold should verify through Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its simple expansion");
    assert_eq!(
        tactics
            .iter()
            .filter(|tactic| matches!(tactic, ProofTactic::UnfoldResource(_)))
            .count(),
        1,
        "one source unfold must produce exactly one retained step"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("discard.c", c_source)],
        "discard",
        CProofClaim::Grouped,
    )
    .expect("the grouped resource proof should expand");
    assert_eq!(expanded.matches("unfold(marker(x));").count(), 1);
    verify_c0_sources(&expanded, &[("discard.c", c_source)])
        .expect("the one retained unfold should independently check");
}

#[test]
fn execution_resource_observe_is_recorded_once_and_checks() {
    let c_source = r#"
        int32 inspect(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "inspect.c";

        int32 inspect(int32 x) {
            views marker(x);
            ensures result == x;
        } by {
            observe(marker(x));
            execute();
            assumption();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("inspect.c", c_source)])
        .expect("the explicit resource observation should verify through Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its simple expansion");
    assert_eq!(
        tactics
            .iter()
            .filter(|tactic| matches!(tactic, ProofTactic::ObserveResource(_)))
            .count(),
        1,
        "one source observation must produce exactly one retained step"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("inspect.c", c_source)],
        "inspect",
        CProofClaim::Grouped,
    )
    .expect("the grouped resource proof should expand");
    assert_eq!(expanded.matches("observe(marker(x));").count(), 1);
    verify_c0_sources(&expanded, &[("inspect.c", c_source)])
        .expect("the one retained observation should independently check");
}

#[test]
fn execution_resource_fold_is_recorded_once_and_checks() {
    let c_source = r#"
        int32 preserve(int32 x) {
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "preserve.c";

        int32 preserve(int32 x) {
            owns marker(x);
            ensures result == x;
        } by {
            unfold(marker(x));
            fold(marker(x));
            execute();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("preserve.c", c_source)])
        .expect("the explicit resource fold should verify through Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its simple expansion");
    assert_eq!(
        tactics
            .iter()
            .filter(|tactic| matches!(tactic, ProofTactic::FoldResource(_)))
            .count(),
        1,
        "one source fold must produce exactly one retained step"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("preserve.c", c_source)],
        "preserve",
        CProofClaim::Grouped,
    )
    .expect("the grouped resource proof should expand");
    assert_eq!(
        expanded
            .lines()
            .filter(|line| line.trim() == "fold(marker(x));")
            .count(),
        1
    );
    verify_c0_sources(&expanded, &[("preserve.c", c_source)])
        .expect("the one retained fold should independently check");
}

#[test]
fn linear_execution_open_retains_one_checked_scope_and_checks() {
    let c_source = r#"
        int32 two_steps(int32 x) {
            x = x;
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "two_steps.c";

        int32 two_steps(int32 x) {
            owns marker(x);
            ensures result == x;
        } by {
            open(marker(x)) {
                step();
            }
            step();
            simp();
        }
    "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("two_steps.c", c_source)])
    });
    let verified = verified.expect("the linear open scope should verify through Proof");
    assert_eq!(
        flat_units, 1,
        "the complete open proof should retain one Proof"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its simple expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(open.tactics.as_slice(), [ProofTactic::Step])
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("two_steps.c", c_source)],
        "two_steps",
        CProofClaim::Grouped,
    )
    .expect("the grouped open proof should expand");
    verify_c0_sources(&expanded, &[("two_steps.c", c_source)])
        .expect("the retained open scope should independently check");
}

#[test]
fn linear_execution_open_retains_checked_prefix_on_one_proof() {
    let c_source = r#"
        int32 add_once(int32 x, int32 y) {
            x = x + y;
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "add_once.c";

        int32 add_once(int32 x, int32 y) {
            requires defined(x + y);
            owns marker(x);
            ensures result == x + y;
        } by {
            step();
            open(marker(x)) {
                step();
            }
            simp();
        }
    "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("add_once.c", c_source)])
    });
    verified.expect("the leading statement and open scope should verify on one Proof");
    assert_eq!(flat_units, 1, "the scoped prefix should retain one Proof");

    let expanded = expand_c0_claim_source(
        click_source,
        &[("add_once.c", c_source)],
        "add_once",
        CProofClaim::Grouped,
    )
    .expect("the prefixed open proof should expand");
    assert!(!expanded.contains("execute();"), "{expanded}");
    verify_c0_sources(&expanded, &[("add_once.c", c_source)])
        .expect("the rewritten prefixed open proof should verify normally");
}

#[test]
fn linear_execute_inside_open_retains_checked_statement_steps() {
    let c_source = r#"
        int32 two_steps(int32 x) {
            x = x;
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "two_steps.c";

        int32 two_steps(int32 x) {
            owns marker(x);
            ensures result == x;
        } by {
            open(marker(x)) {
                execute();
            }
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("two_steps.c", c_source)]);
    let verified = verified.expect("linear execute should advance inside the open Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its scoped execution");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::Step, ProofTactic::Step]
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("two_steps.c", c_source)],
        "two_steps",
        CProofClaim::Grouped,
    )
    .expect("the grouped scoped execute should expand");
    verify_c0_sources(&expanded, &[("two_steps.c", c_source)])
        .expect("the retained scoped statement steps should independently check");
}

#[test]
fn grouped_post_execution_rewrite_and_apply_before_frame_stay_on_proof() {
    let apply_c = r#"
        int32 apply_write(int32 p[], int32 x) {
            p[0] = x;
            return x;
        }
    "#;
    let rewrite_c = r#"
        int32 rewrite_write(int32 p[]) {
            p[0] = 9;
            return p[0];
        }
    "#;
    let click_source = r#"
        theorem int32_sign_split(value: int32) {
            ensures value <= 0 or value > 0 by {
                if value <= 0 {
                    simp();
                } else {
                    simp();
                }
            }
        }

        verifying "apply_write.c";
        verifying "rewrite_write.c";

        int32 apply_write(int32 p[], int32 x) {
            consumes p[0..1];
            ensures result <= 0 or result > 0;
        } by {
            execute();
            apply(int32_sign_split(result)) using {}
            assumption();
        }

        int32 rewrite_write(int32 p[]) {
            consumes p[0..1];
            ensures result == 9;
        } by {
            execute();
            rewrite(result == 9);
            normalize();
        }
    "#;
    let sources = [("apply_write.c", apply_c), ("rewrite_write.c", rewrite_c)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(click_source, &sources));
    let verified = verified.expect("the ordered outcome operations should verify on Proof");
    assert_eq!(flat_units, 2, "both grouped proofs should retain Proof");

    let retained = verified
        .iter()
        .flat_map(|theorem| theorem.expanded_proof_tactics().unwrap_or_default())
        .collect::<Vec<_>>();
    assert!(
        retained.iter().any(|tactic| matches!(
            tactic,
            ProofTactic::ApplyTheoremUsing { application, .. }
                if application.name == "int32_sign_split"
        )),
        "the retained proofs lost the explicit theorem application: {retained:#?}"
    );
    assert!(
        retained
            .iter()
            .any(|tactic| matches!(tactic, ProofTactic::Rewrite(_))),
        "the retained proofs lost the rewrite: {retained:#?}"
    );

    let expanded_apply =
        expand_c0_claim_source(click_source, &sources, "apply_write", CProofClaim::Grouped)
            .expect("the ordered theorem application should serialize");
    verify_c0_sources(&expanded_apply, &sources)
        .expect("the serialized theorem application should independently reverify");
    let expanded_rewrite = expand_c0_claim_source(
        click_source,
        &sources,
        "rewrite_write",
        CProofClaim::Grouped,
    )
    .expect("the ordered rewrite should serialize");
    verify_c0_sources(&expanded_rewrite, &sources)
        .expect("the serialized rewrite should independently reverify");

    for (corrupted, description) in [
        (
            expanded_apply.replacen(
                "int32_sign_split(result)) using {",
                "int32_sign_split(result + 1)) using {",
                1,
            ),
            "theorem application",
        ),
        (
            expanded_rewrite.replacen("rewrite(result == 9);", "rewrite(result == 8);", 1),
            "rewrite",
        ),
    ] {
        let original = if description == "rewrite" {
            &expanded_rewrite
        } else {
            &expanded_apply
        };
        assert_ne!(
            &corrupted, original,
            "the expansion should expose {description}"
        );
        let result = { verify_c0_sources(&corrupted, &sources) };
        result.expect_err("tampering with an ordered outcome operation must invalidate the proof");
    }
}

#[test]
fn grouped_post_execution_predicate_unfold_before_frame_stays_on_proof() {
    let c_source = r#"
        int32 write_first(int32 p[]) {
            p[0] = 9;
            return p[0];
        }
    "#;
    let click_source = r#"
        predicate is_nine(value: int32) {
            value == 9
        }

        predicate is_eight(value: int32) {
            value == 8
        }

        verifying "write_first.c";

        int32 write_first(int32 p[]) {
            consumes p[0..1];
            ensures is_nine(result);
        } by {
            execute();
            unfold(is_nine);
            normalize();
        }
    "#;
    let sources = [("write_first.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(click_source, &sources));
    let verified = verified.expect("the ordered predicate unfold should verify on Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the predicate unfold should retain provenance");
    assert!(
        tactics.iter().any(|tactic| matches!(
            tactic,
            ProofTactic::UnfoldPredicate(name) if name == "is_nine"
        )),
        "the retained proof lost its predicate unfold: {tactics:#?}"
    );

    let rewritten =
        expand_c0_claim_source(click_source, &sources, "write_first", CProofClaim::Grouped)
            .expect("the ordered predicate unfold should serialize");
    verify_c0_sources(&rewritten, &sources)
        .expect("the serialized predicate unfold should independently reverify");

    let corrupted = rewritten.replacen("unfold(is_nine);", "unfold(is_eight);", 1);
    assert_ne!(
        corrupted, rewritten,
        "the expansion should expose the unfold"
    );
    let result = { verify_c0_sources(&corrupted, &sources) };
    result.expect_err("tampering with the predicate unfold must invalidate the proof");
}

#[test]
fn quantified_contract_resource_open_stays_on_one_proof() {
    let c_source = "int32 preserve_markers(int32 x, int32 amount) { return x; }";
    let click_source = r#"
        resource marker(x: int32) {}

        verifying "preserve_markers.c";

        int32 preserve_markers(int32 x, int32 amount) {
            requires 1 <= amount;
            owns amount of marker(x);
            ensures result == x;
        } by {
            open(marker(x)) {
                execute();
            }
            simp();
        }
    "#;
    let sources = [("preserve_markers.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(click_source, &sources));
    let verified = verified.expect("the quantified resource scope should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the quantified resource scope should retain provenance");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(open.resource, ResourceClause::Declared { ref name, .. } if name == "marker")
        ),
        "the retained proof lost the checked open scope: {tactics:#?}"
    );

    let rewritten = expand_c0_claim_source(
        click_source,
        &sources,
        "preserve_markers",
        CProofClaim::Grouped,
    )
    .expect("the quantified resource scope should serialize");
    verify_c0_sources(&rewritten, &sources)
        .expect("the serialized quantified resource scope should independently reverify");

    let corrupted = rewritten.replacen("open(marker(x))", "open(marker(x + 1))", 1);
    assert_ne!(
        corrupted, rewritten,
        "the expansion should expose the checked resource selection"
    );
    let result = { verify_c0_sources(&corrupted, &sources) };
    let error =
        result.expect_err("tampering with the resource selection must invalidate the proof");
    assert!(
        error
            .message()
            .contains("`open(marker((x + 1)))` Requires owns marker((x + 1))"),
        "the checked resource-entry operation should reject the tamper directly: {error:?}"
    );
}

#[test]
fn linear_execute_until_inside_open_stops_on_checked_frontier() {
    let c_source = r#"
        int32 three_steps(int32 x) {
            int32 value = x;
            value = value;
            return value;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "three_steps.c";

        int32 three_steps(int32 x) {
            owns marker(x);
            ensures result == x;
        } by {
            open(marker(x)) {
                execute_until(statement(2));
                step();
            }
            step();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("three_steps.c", c_source)]);
    let verified = verified.expect("execute_until should advance the checked open frontier");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its stopped frontier path");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::Step, ProofTactic::Step, ProofTactic::Step]
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("three_steps.c", c_source)],
        "three_steps",
        CProofClaim::Grouped,
    )
    .expect("the grouped scoped execute_until should expand");
    verify_c0_sources(&expanded, &[("three_steps.c", c_source)])
        .expect("the retained stopped-frontier steps should independently check");
}

#[test]
fn linear_open_have_retains_the_selected_theorem_application() {
    let c_source = r#"
        int32 two_steps(int32 x) {
            x = x;
            return x;
        }
    "#;
    let click_source = r#"
        theorem int32_reflexive(value: int32) {
            ensures value == value by {
                normalize();
            }
        }

        resource marker(x: int32) {
            fact x == x;
        }

        verifying "two_steps.c";

        int32 two_steps(int32 x) {
            owns marker(x);
            ensures result == x;
        } by {
            open(marker(x)) {
                have x == x by {
                    apply(int32_reflexive(x));
                }
                step();
            }
            step();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("two_steps.c", c_source)]);
    let verified = verified.expect("the nested theorem application should advance the open Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its nested expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::Have(have), ProofTactic::Step]
                        if matches!(
                            &have.proof,
                            SourceProof::Script(body)
                                if matches!(
                                    body.as_slice(),
                                    [ProofTactic::ApplyTheoremUsing { application, premises }]
                                        if application.name == "int32_reflexive" && premises.is_empty()
                                )
                        )
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("two_steps.c", c_source)],
        "two_steps",
        CProofClaim::Grouped,
    )
    .expect("the grouped nested open proof should expand");
    verify_c0_sources(&expanded, &[("two_steps.c", c_source)])
        .expect("the retained nested theorem application should independently check");
}

#[test]
fn nested_composite_resource_scopes_stay_on_one_proof() {
    let c_source = "int32 read_cell(int32 p[]) { return p[0]; }";
    let click_source = r#"
        resource cell(p: int32*) {
            owns p[0..1];
        }

        resource wrapped_cell(p: int32*) {
            owns cell(p);
        }

        verifying "read_cell.c";

        int32 read_cell(int32 p[]) {
            owns wrapped_cell(p);
            ensures result == old(p[0]);
        } by {
            open(wrapped_cell(p)) {
                open(cell(p)) {
                    execute();
                }
            }
            simp();
        }
    "#;
    let sources = [("read_cell.c", c_source)];

    let _ = crate::kernel::take_checked_function_body_execution_count();
    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(click_source, &sources));
    let verified = verified.expect("the nested resource scopes should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "closing nested post-execution resource scopes should not rerun the C body"
    );

    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the nested resource scopes should retain provenance");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(outer))
                if matches!(
                    outer.tactics.as_slice(),
                    [ProofTactic::Open(inner)]
                        if matches!(inner.resource, ResourceClause::Declared { ref name, .. } if name == "cell")
                )
        ),
        "the retained proof lost the nested checked scope: {tactics:#?}"
    );

    let rewritten =
        expand_c0_claim_source(click_source, &sources, "read_cell", CProofClaim::Grouped)
            .expect("the nested resource scopes should serialize");
    verify_c0_sources(&rewritten, &sources)
        .expect("the serialized nested scopes should independently reverify");

    let corrupted = rewritten.replacen("open(cell(p))", "open(cell(p + 1))", 1);
    assert_ne!(
        corrupted, rewritten,
        "the expansion should expose the nested resource selection"
    );
    let result = { verify_c0_sources(&corrupted, &sources) };
    let error =
        result.expect_err("tampering with the nested resource selection must invalidate the proof");
    assert!(
        error
            .message()
            .contains("`open(cell((p + 1)))` Requires owns cell((p + 1))"),
        "the nested checked resource entry should reject the tamper directly: {error:?}"
    );
}

#[test]
fn linear_open_retains_a_direct_bare_theorem_application() {
    let c_source = r#"
        int32 retain_lower(int32 lower, int32 upper) {
            return lower;
        }
    "#;
    let click_source = r#"import click::machine_integer;

        resource ordered(lower: int32, upper: int32) {
            fact lower < upper;
        }

        verifying "retain_lower.c";

        int32 retain_lower(int32 lower, int32 upper) {
            owns ordered(lower, upper);
            ensures lower <= upper;
        } by {
            open(ordered(lower, upper)) {
                apply(int32_less_than_implies_less_equal(lower, upper));
                step();
            }
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("retain_lower.c", c_source)]);
    let verified = verified.expect("the direct theorem application should advance the open Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked open proof should retain its expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [
                        ProofTactic::ApplyTheoremUsing { application, premises },
                        ProofTactic::Step,
                    ] if application.name == "click::machine_integer::int32_less_than_implies_less_equal" && premises.len() == 1
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("retain_lower.c", c_source)],
        "retain_lower",
        CProofClaim::Grouped,
    )
    .expect("the retained open-scope theorem application should expand");
    verify_c0_sources(&expanded, &[("retain_lower.c", c_source)])
        .expect("the explicit open-scope theorem step should independently re-derive");
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn linear_open_retains_a_direct_bare_fact_transport() {
    let c_source = r#"
        int32 set_second_return_first(int32 p[2]) {
            p[1] = 9;
            return p[0];
        }
    "#;
    let click_source = r#"
        resource first_is_seven(p: int32[]) {
            owns p[0..2];
            fact p[0] == 7;
        }

        verifying "set_second_return_first.c";

        int32 set_second_return_first(int32 p[2]) {
            owns first_is_seven(p);
            ensures result == 7;
        } by {
            open(first_is_seven(p)) {
                step();
                transport(old(p[0]) == 7, p[0] == 7);
                step();
            }
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("set_second_return_first.c", c_source)]);
    let verified = verified.expect("the direct transport should advance the open Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked open transport should retain its expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [
                        ProofTactic::Step,
                        ProofTactic::TransportUsing { premises, .. },
                        ProofTactic::Step,
                    ] if !premises.is_empty()
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("set_second_return_first.c", c_source)],
        "set_second_return_first",
        CProofClaim::Grouped,
    )
    .expect("the retained open-scope transport should expand");
    verify_c0_sources(&expanded, &[("set_second_return_first.c", c_source)])
        .expect("the explicit open-scope transport should independently re-derive");
}

#[test]
fn execution_branch_arm_resource_scope_stays_on_one_proof() {
    let c_source = r#"
        int32 read_if(int32 p[], int32 flag) {
            int32 value;
            if (flag) {
                value = p[0];
            } else {
                value = 0;
            }
            return value;
        }
    "#;
    let click_source = r#"
        resource cell(p: int32*) {
            views p[0..1];
        }

        verifying "read_if.c";

        int32 read_if(int32 p[], int32 flag) {
            owns cell(p);
            ensures result == old(p[0]) or result == 0;
        } by {
            step();
            branch ensuring {
                fact value == old(p[0]) or value == 0;
                owns cell(p);
            } then {
                open(cell(p)) {
                    step();
                    have value == old(p[0]) or value == 0 by {
                        have value == old(p[0]) by { normalize(); }
                        assumption();
                    }
                }
            } else {
                step();
                have value == old(p[0]) or value == 0 by {
                    have value == 0 by { normalize(); }
                    assumption();
                }
            }
            step();
            simp();
        }
    "#;
    let sources = [("read_if.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(click_source, &sources));
    let verified = verified.expect("the branch-arm resource scope should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the branch-arm resource scope should retain provenance");
    assert!(
        tactics.iter().any(|tactic| matches!(
            tactic,
            ProofTactic::Branch(branch)
                if matches!(
                    branch.then_tactics.first(),
                    Some(ProofTactic::Open(open))
                        if matches!(open.resource, ResourceClause::Declared { ref name, .. } if name == "cell")
                )
        )),
        "the retained branch lost its checked resource scope: {tactics:#?}"
    );

    let rewritten = expand_c0_claim_source(click_source, &sources, "read_if", CProofClaim::Grouped)
        .expect("the branch-arm resource scope should serialize");
    verify_c0_sources(&rewritten, &sources)
        .expect("the serialized branch-arm scope should independently reverify");

    let corrupted = rewritten.replacen("open(cell(p))", "open(cell(p + 1))", 1);
    assert_ne!(
        corrupted, rewritten,
        "the expansion should expose the branch-arm resource selection"
    );
    let result = { verify_c0_sources(&corrupted, &sources) };
    let error =
        result.expect_err("tampering with the branch-arm resource must invalidate the proof");
    assert!(
        error
            .message()
            .contains("`open(cell((p + 1)))` Requires owns cell((p + 1))"),
        "the checked branch-arm resource entry should reject the tamper directly: {error:?}"
    );
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn scoped_execution_branch_arm_resource_scope_stays_on_one_proof() {
    let c_source = r#"
        int32 read_if(int32 p[], int32 flag) {
            int32 value;
            if (flag) {
                value = p[0];
            } else {
                value = 0;
            }
            return value;
        }
    "#;
    let click_source = r#"
        resource cell(p: int32*) {
            views p[0..1];
        }

        resource marker(x: int32) {
            fact x == x;
        }

        resource wrapped_cell(p: int32*, flag: int32) {
            owns cell(p);
            owns marker(flag);
        }

        verifying "read_if.c";

        int32 read_if(int32 p[], int32 flag) {
            owns wrapped_cell(p, flag);
            ensures result == old(p[0]) or result == 0;
        } by {
            open(wrapped_cell(p, flag)) {
                open(cell(p)) {
                    step();
                    branch ensuring {
                        fact value == old(p[0]) or value == 0;
                        views p[0..1];
                    } then {
                        open(marker(flag)) {
                            step();
                            have value == old(p[0]) or value == 0 by {
                                have value == old(p[0]) by { normalize(); }
                                assumption();
                            }
                        }
                    } else {
                        step();
                        have value == old(p[0]) or value == 0 by {
                            have value == 0 by { normalize(); }
                            assumption();
                        }
                    }
                }
            }
            step();
            simp();
        }
    "#;
    let sources = [("read_if.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(click_source, &sources));
    let verified = verified.expect("the nested branch-arm scope should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the nested branch-arm scope should retain provenance");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(outer))
                if matches!(
                    outer.tactics.as_slice(),
                    [ProofTactic::Open(cell)]
                        if matches!(
                            cell.tactics.get(1),
                            Some(ProofTactic::Branch(branch))
                                if matches!(
                                    branch.then_tactics.first(),
                                    Some(ProofTactic::Open(marker))
                                        if matches!(marker.resource, ResourceClause::Declared { ref name, .. } if name == "marker")
                                )
                        )
                )
        ),
        "the retained outer scope lost its checked branch-arm scope: {tactics:#?}"
    );

    let rewritten = expand_c0_claim_source(click_source, &sources, "read_if", CProofClaim::Grouped)
        .expect("the nested branch-arm scope should serialize");
    verify_c0_sources(&rewritten, &sources)
        .expect("the serialized nested branch-arm scope should independently reverify");

    let corrupted = rewritten.replacen("open(marker(flag))", "open(marker(flag + 1))", 1);
    assert_ne!(
        corrupted, rewritten,
        "the expansion should expose the nested branch-arm resource selection"
    );
    let result = { verify_c0_sources(&corrupted, &sources) };
    let error = result
        .expect_err("tampering with the nested branch-arm resource must invalidate the proof");
    assert!(
        error
            .message()
            .contains("`open(marker((flag + 1)))` Requires owns marker((flag + 1))"),
        "the checked nested branch-arm entry should reject the tamper directly: {error:?}"
    );
}

#[test]
fn execution_branch_arm_terminal_proof_if_stays_on_one_proof() {
    let c_source = r#"
        int32 choose_x_or_zero(int32 x, int32 flag) {
            if (flag) {
                return x;
            } else {
                return 0;
            }
        }
    "#;
    let click_source = r#"
        verifying "choose_x_or_zero.c";

        int32 choose_x_or_zero(int32 x, int32 flag) {
            ensures result == x or result == 0;
        } by {
            branch {
                if x >= 0 {
                    execute();
                    simp();
                } else {
                    execute();
                    simp();
                }
            } else {
                execute();
                simp();
            }
        }
    "#;
    let sources = [("choose_x_or_zero.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(click_source, &sources));
    let verified = verified.expect("the nested terminal proof if should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the nested terminal proof if should retain provenance");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::If(outer))
                if outer.then_tactics.iter().any(|tactic| matches!(
                    tactic,
                    ProofTactic::If(inner) if inner.condition == ClickProposition::Comparison {
                        left: ContractExpression::CFragment(CExpression::Variable("x".to_string())),
                        operator: ComparisonOperator::GreaterEqual,
                        right: ContractExpression::IntegerLiteral("0".into()),
                    }
                ))
        ),
        "the retained execution branch lost its nested logical split: {tactics:#?}"
    );

    let rewritten = expand_c0_claim_source(
        click_source,
        &sources,
        "choose_x_or_zero",
        CProofClaim::Grouped,
    )
    .expect("the nested terminal proof if should serialize");
    let (reverified, rewritten_flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(&rewritten, &sources));
    reverified.expect("the serialized nested terminal proof if should independently reverify");
    assert_eq!(
        rewritten_flat_units, 1,
        "the rewritten nested proof if should retain one Proof"
    );

    let nested_if = click_source
        .find("if x >= 0")
        .expect("the nested proof if should be present");
    let selected_simp = click_source[nested_if..]
        .find("simp();")
        .map(|offset| nested_if + offset)
        .expect("the nested then arm should contain a simp");
    let position = expansion::position_at_offset(click_source, selected_simp);
    let (selected_expansion, selected_flat_units) = proof::count_flat_proof_units(|| {
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
    });
    let selected_expansion = selected_expansion
        .expect("the selected terminal-arm simp should expand from retained provenance");
    assert_eq!(
        selected_flat_units, 1,
        "selected expansion should retain one Proof"
    );

    assert_eq!(
        selected_expansion.matches("simp();").count(),
        2,
        "selected expansion should replace only the attributed nested-arm simp"
    );
    let selected_reverified = verify_c0_sources(&selected_expansion, &sources);
    selected_reverified
        .expect("the selected terminal-arm simp expansion should independently reverify");

    let corrupted = rewritten.replacen("if x >= 0 {", "if result >= 0 {", 1);
    assert_ne!(
        corrupted, rewritten,
        "the expansion should expose the nested proof-if condition"
    );
    let result = { verify_c0_sources(&corrupted, &sources) };
    result.expect_err("an unavailable result condition must invalidate the nested proof if");
}

#[test]
fn branch_interface_retains_its_checked_abstract_join() {
    let c_source = r#"
        int32 nonnegative(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        verifying "nonnegative.c";

        int32 nonnegative(int32 x) {
            ensures result >= 0;
        } by {
            branch ensuring {
                fact x >= 0;
            } then { step(); } else { step(); }
            step();
            simp();
        }
    "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("nonnegative.c", c_source)])
    });
    let verified = verified.expect("the checked branch interface should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "a pure checked branch interface must seal from retained outcome evidence"
    );
    assert_eq!(flat_units, 1, "the branch proof should retain one Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked branch interface should retain an expansion");
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::Branch(branch),
                ProofTactic::Step,
                ..
            ] if matches!(
                branch.ensuring.as_deref(),
                Some([ProofAssertion::Fact(ClickProposition::Comparison {
                    operator: ComparisonOperator::GreaterEqual,
                    ..
                })])
            ) && matches!(branch.then_tactics.as_slice(), [ProofTactic::Step])
                && matches!(branch.else_tactics.as_slice(), [ProofTactic::Step])
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("nonnegative.c", c_source)],
        "nonnegative",
        CProofClaim::Grouped,
    )
    .expect("the retained branch interface should expand");
    verify_c0_sources(&expanded, &[("nonnegative.c", c_source)])
        .expect("the retained branch-interface certificate should independently re-derive");
}

#[test]
fn branch_interface_retains_exact_unchanged_ownership() {
    let c_source = r#"
        int32 preserve_marker(int32 x, int32 flag) {
            int32 y;
            if (flag != 0) {
                y = 1;
            } else {
                y = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        abstract resource marker(x: int32);

        verifying "preserve_marker.c";

        int32 preserve_marker(int32 x, int32 flag) {
            owns marker(x);
            ensures result == x;
        } by {
            step();
            branch ensuring {
                fact y >= 0;
                owns marker(x);
            } then { step(); } else { step(); }
            step();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("preserve_marker.c", c_source)]);
    let verified = verified.expect("the exact owned interface should stay on Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the exact owned interface should retain an expansion");
    assert!(
        matches!(
            tactics.get(1),
            Some(ProofTactic::Branch(branch))
                if matches!(
                    branch.ensuring.as_deref(),
                    Some([
                        ProofAssertion::Fact(_),
                        ProofAssertion::Resource(ResourceClause::Declared {
                            access: ResourceAccessMode::Own,
                            name,
                            ..
                        }),
                    ]) if name == "marker"
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("preserve_marker.c", c_source)],
        "preserve_marker",
        CProofClaim::Grouped,
    )
    .expect("the retained exact owned interface should expand");
    verify_c0_sources(&expanded, &[("preserve_marker.c", c_source)])
        .expect("the exact owned interface should independently re-derive");
}

#[test]
fn branch_interface_normalizes_an_entailed_owned_quantity_on_proof() {
    let c_source = r#"
        int32 preserve_two_markers(int32 x, int32 flag) {
            int32 y;
            if (flag != 0) {
                y = 1;
            } else {
                y = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        abstract resource marker(x: int32);

        verifying "preserve_two_markers.c";

        int32 preserve_two_markers(int32 x, int32 flag) {
            owns 2 of marker(x);
            ensures result == x;
        } by {
            step();
            branch ensuring {
                fact y >= 0;
                owns marker(x);
            } then { step(); } else { step(); }
            step();
            simp();
        }
    "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    let (verified, checked_interface_joins) =
        crate::surface::proof::count_checked_execution_interface_joins(|| {
            verify_c0_sources(click_source, &[("preserve_two_markers.c", c_source)])
        });
    let verified = verified.expect("the entailed quantity interface should stay on Proof");
    assert!(
        checked_interface_joins > 0,
        "the quantity interface must reach the checked two-arm Proof join"
    );
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "a checked `branch ensuring` must seal from its retained arm evidence"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the quantity interface should retain an expansion");
    assert!(matches!(
        tactics.get(1),
        Some(ProofTactic::Branch(branch))
            if matches!(
                branch.ensuring.as_deref(),
                Some([
                    ProofAssertion::Fact(_),
                    ProofAssertion::Resource(ResourceClause::Declared {
                        access: ResourceAccessMode::Own,
                        name,
                        ..
                    }),
                ]) if name == "marker"
            )
    ));

    let expanded = expand_c0_claim_source(
        click_source,
        &[("preserve_two_markers.c", c_source)],
        "preserve_two_markers",
        CProofClaim::Grouped,
    )
    .expect("the retained quantity interface should expand");
    verify_c0_sources(&expanded, &[("preserve_two_markers.c", c_source)])
        .expect("the normalized quantity interface should independently re-derive");
}

#[test]
fn branch_arms_retain_bare_theorem_applications_on_proof() {
    let c_source = r#"
        int32 retain_order(int32 lower, int32 upper, int32 flag) {
            int32 choice;
            if (flag != 0) {
                choice = lower;
            } else {
                choice = upper;
            }
            return choice;
        }
    "#;
    let click_source = r#"import click::machine_integer;

        verifying "retain_order.c";

        int32 retain_order(int32 lower, int32 upper, int32 flag) {
            requires lower < upper;
            ensures lower <= upper;
        } by {
            step();
            branch ensuring {
                fact lower <= upper;
            } then {
                step();
                apply(int32_less_than_implies_less_equal(lower, upper));
            } else {
                step();
                apply(int32_less_than_implies_less_equal(lower, upper));
            }
            step();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("retain_order.c", c_source)]);
    let verified = verified.expect("bare arm applications should advance the branch Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked theorem applications should retain an expansion");
    assert!(
        matches!(
            tactics.get(1),
            Some(ProofTactic::Branch(branch))
                if matches!(
                    branch.then_tactics.as_slice(),
                    [ProofTactic::Step, ProofTactic::ApplyTheoremUsing { application, premises }]
                        if application.name == "click::machine_integer::int32_less_than_implies_less_equal" && premises.len() == 1
                ) && matches!(
                    branch.else_tactics.as_slice(),
                    [ProofTactic::Step, ProofTactic::ApplyTheoremUsing { application, premises }]
                        if application.name == "click::machine_integer::int32_less_than_implies_less_equal" && premises.len() == 1
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("retain_order.c", c_source)],
        "retain_order",
        CProofClaim::Grouped,
    )
    .expect("the retained branch applications should expand");
    verify_c0_sources(&expanded, &[("retain_order.c", c_source)])
        .expect("the explicit branch applications should independently re-derive");
}

#[test]
fn branch_join_retains_a_bare_theorem_application_in_its_continuation() {
    let c_source = r#"
        int32 choose_bound(int32 lower, int32 upper, int32 flag) {
            int32 choice;
            if (flag != 0) {
                choice = lower;
            } else {
                choice = upper;
            }
            return choice;
        }
    "#;
    let click_source = r#"import click::machine_integer;

        verifying "choose_bound.c";

        int32 choose_bound(int32 lower, int32 upper, int32 flag) {
            requires lower < upper;
            ensures lower <= upper;
        } by {
            step();
            branch ensuring {
                fact lower < upper;
            } then { step(); } else { step(); }
            apply(int32_less_than_implies_less_equal(lower, upper));
            step();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("choose_bound.c", c_source)]);
    let verified =
        verified.expect("the common theorem application should advance the joined Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked common theorem application should retain an expansion");
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::Step,
                ProofTactic::Branch(branch),
                ProofTactic::ApplyTheoremUsing { application, premises },
                ProofTactic::Step,
                ..
            ] if matches!(
                    branch.ensuring.as_deref(),
                    Some([ProofAssertion::Fact(ClickProposition::Comparison {
                        operator: ComparisonOperator::LessThan,
                        ..
                    })])
                )
                && matches!(branch.then_tactics.as_slice(), [ProofTactic::Step])
                && matches!(branch.else_tactics.as_slice(), [ProofTactic::Step])
                && application.name == "click::machine_integer::int32_less_than_implies_less_equal"
                && premises.len() == 1
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("choose_bound.c", c_source)],
        "choose_bound",
        CProofClaim::Grouped,
    )
    .expect("the retained common theorem application should expand");
    verify_c0_sources(&expanded, &[("choose_bound.c", c_source)])
        .expect("the explicit common theorem step should independently re-derive");
}

#[test]
fn branch_join_retains_a_bare_fact_transport_in_its_continuation() {
    let c_source = r#"
        int32 choose_bound_transport(int32 lower, int32 upper, int32 flag) {
            int32 choice;
            if (flag != 0) {
                choice = lower;
            } else {
                choice = upper;
            }
            return choice;
        }
    "#;
    let click_source = r#"
        verifying "choose_bound_transport.c";

        int32 choose_bound_transport(int32 lower, int32 upper, int32 flag) {
            requires lower < upper;
            ensures lower < upper;
        } by {
            step();
            branch ensuring {
                fact old(lower) < old(upper);
            } then { step(); } else { step(); }
            transport(old(lower) < old(upper), lower < upper);
            step();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("choose_bound_transport.c", c_source)]);
    let verified = verified.expect("the common fact transport should advance the joined Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked common fact transport should retain an expansion");
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::Step,
                ProofTactic::Branch(branch),
                ProofTactic::TransportUsing { premises, .. },
                ProofTactic::Step,
                ..
            ] if matches!(
                    branch.ensuring.as_deref(),
                    Some([ProofAssertion::Fact(ClickProposition::Comparison {
                        operator: ComparisonOperator::LessThan,
                        ..
                    })])
                )
                && matches!(branch.then_tactics.as_slice(), [ProofTactic::Step])
                && matches!(branch.else_tactics.as_slice(), [ProofTactic::Step])
                && !premises.is_empty()
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("choose_bound_transport.c", c_source)],
        "choose_bound_transport",
        CProofClaim::Grouped,
    )
    .expect("the retained common fact transport should expand");
    verify_c0_sources(&expanded, &[("choose_bound_transport.c", c_source)])
        .expect("the explicit common transport step should independently re-derive");
}

#[test]
fn branch_join_retains_a_nested_have_in_its_continuation() {
    let c_source = r#"
        int32 select_positive(int32 flag) {
            int32 selected;
            if (flag != 0) {
                selected = 1;
            } else {
                selected = 2;
            }
            selected = selected + 1;
            return selected;
        }
    "#;
    let click_source = r#"import click::machine_integer;

        verifying "select_positive.c";

        int32 select_positive(int32 flag) {
            ensures result >= 0;
        } by {
            step();
            branch ensuring {
                fact selected > 0;
                fact selected < 2147483647;
            } then { step(); } else { step(); }
            have selected >= 0 by {
                apply(int32_positive_is_nonnegative(selected));
            }
            execute_until(statement(5));
            step();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("select_positive.c", c_source)]);
    let verified = verified.expect("the common nested have should advance the joined Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked common nested have should retain an expansion");
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::Step,
                ProofTactic::Branch(branch),
                ProofTactic::Have(ProofHave {
                    proof: SourceProof::Script(body),
                    ..
                }),
                ProofTactic::Step,
                ProofTactic::Step,
                ..
            ] if matches!(
                    branch.ensuring.as_deref(),
                    Some([
                        ProofAssertion::Fact(ClickProposition::Comparison {
                            operator: ComparisonOperator::GreaterThan,
                            ..
                        }),
                        ProofAssertion::Fact(ClickProposition::Comparison {
                            operator: ComparisonOperator::LessThan,
                            ..
                        }),
                    ])
                )
                && matches!(branch.then_tactics.as_slice(), [ProofTactic::Step])
                && matches!(branch.else_tactics.as_slice(), [ProofTactic::Step])
                && matches!(
                    body.as_slice(),
                    // The theorem concludes `0 <= selected`; the mirrored
                    // `selected >= 0` closes by `assumption`.
                    [
                        ProofTactic::ApplyTheoremUsing { application, premises },
                        ProofTactic::Assumption,
                    ] if application.name == "click::machine_integer::int32_positive_is_nonnegative"
                            && premises.len() == 1
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("select_positive.c", c_source)],
        "select_positive",
        CProofClaim::Grouped,
    )
    .expect("the retained common nested have should expand");
    verify_c0_sources(&expanded, &[("select_positive.c", c_source)])
        .expect("the explicit common nested proof should independently re-derive");
}

#[test]
fn branch_join_retains_linear_execute_on_its_common_successor() {
    let c_source = r#"
        int32 select_and_increment(int32 flag) {
            int32 selected;
            if (flag != 0) {
                selected = 1;
            } else {
                selected = 2;
            }
            selected = selected + 1;
            return selected;
        }
    "#;
    let click_source = r#"
        verifying "select_and_increment.c";

        int32 select_and_increment(int32 flag) {
            ensures result == result;
        } by {
            step();
            branch ensuring {
                fact selected > 0;
                fact selected < 2147483647;
            } then { step(); } else { step(); }
            execute();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("select_and_increment.c", c_source)]);
    let verified = verified.expect("common execute should advance the joined Proof to exit");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("common execute should retain its checked expansion");
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::Step,
                ProofTactic::Branch(branch),
                ProofTactic::Step,
                ProofTactic::Step,
                ..
            ] if matches!(
                    branch.ensuring.as_deref(),
                    Some([
                        ProofAssertion::Fact(ClickProposition::Comparison {
                            operator: ComparisonOperator::GreaterThan,
                            ..
                        }),
                        ProofAssertion::Fact(ClickProposition::Comparison {
                            operator: ComparisonOperator::LessThan,
                            ..
                        }),
                    ])
                )
                && matches!(branch.then_tactics.as_slice(), [ProofTactic::Step])
                && matches!(branch.else_tactics.as_slice(), [ProofTactic::Step])
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("select_and_increment.c", c_source)],
        "select_and_increment",
        CProofClaim::Grouped,
    )
    .expect("the retained common execute should expand");
    verify_c0_sources(&expanded, &[("select_and_increment.c", c_source)])
        .expect("the explicit common execute path should independently re-derive");
}

#[test]
fn incremented_strict_lower_bound_retains_its_theorem_path() {
    let c_source = r#"
        int32 select_and_increment_positive(int32 flag) {
            int32 selected;
            if (flag != 0) {
                selected = 1;
            } else {
                selected = 2;
            }
            selected = selected + 1;
            return selected;
        }
    "#;
    let click_source = r#"
        verifying "select_and_increment_positive.c";

        int32 select_and_increment_positive(int32 flag) {
            ensures result > 0;
        } by {
            step();
            branch ensuring {
                fact selected > 0;
                fact selected < 2147483647;
            } then { step(); } else { step(); }
            execute();
            simp();
        }
    "#;

    let verified = verify_c0_sources(
        click_source,
        &[("select_and_increment_positive.c", c_source)],
    );
    verified.expect("strict positivity should retain a composed theorem path on Proof");

    let expanded = expand_c0_claim_source(
        click_source,
        &[("select_and_increment_positive.c", c_source)],
        "select_and_increment_positive",
        CProofClaim::Grouped,
    )
    .expect("the strict-positive increment proof should expand");
    assert!(
        expanded.contains("apply(int32_less_than_implies_less_equal("),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_increment_greater_than_lower_bound("),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("select_and_increment_positive.c", c_source)])
        .expect("the retained strict-positive theorem path should independently reverify");
}

#[test]
fn post_execution_have_anchors_strict_increment_theorem_premises() {
    let c_source = r#"
        int32 select_and_increment_positive_have(int32 flag) {
            int32 selected;
            if (flag != 0) {
                selected = 1;
            } else {
                selected = 2;
            }
            selected = selected + 1;
            return selected;
        }
    "#;
    let click_source = r#"
        verifying "select_and_increment_positive_have.c";

        int32 select_and_increment_positive_have(int32 flag) {
            ensures result > 0;
        } by {
            step();
            branch ensuring {
                fact selected > 0;
                fact selected < 2147483647;
            } then { step(); } else { step(); }
            execute();
            have result > 0 by simp();
            simp();
        }
    "#;

    let verified = verify_c0_sources(
        click_source,
        &[("select_and_increment_positive_have.c", c_source)],
    );
    verified.expect("the post-execution have should retain its composed Proof path");

    let have_offset = click_source
        .find("have result > 0")
        .expect("proof should contain the selected have");
    let position = expansion::position_at_offset(click_source, have_offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("select_and_increment_positive_have.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained strict-positive have should expand");
    assert!(
        !expanded.contains("have result > 0 by simp()"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_less_than_implies_less_equal("),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_increment_greater_than_lower_bound("),
        "{expanded}"
    );
    verify_c0_sources(
        &expanded,
        &[("select_and_increment_positive_have.c", c_source)],
    )
    .expect("the expanded strict-positive have should independently reverify");
}

#[test]
fn branch_arms_retain_bare_fact_transports_on_proof() {
    let c_source = r#"
        int32 set_choice_return_first(int32 p[2], int32 flag) {
            if (flag != 0) {
                p[1] = 1;
            } else {
                p[1] = 2;
            }
            return p[0];
        }
    "#;
    let click_source = r#"
        predicate first_is_seven(p: int32[]) {
            p[0] == 7
        }

        verifying "set_choice_return_first.c";

        int32 set_choice_return_first(int32 p[2], int32 flag) {
            requires first_is_seven(p);
            owns p[0..2];
            ensures result == 7;
        } by {
            unfold(first_is_seven);
            branch ensuring {
                fact p[0] == 7;
                owns p[0..2];
            } then {
                step();
                transport(old(p[0]) == 7, p[0] == 7);
            } else {
                step();
                transport(old(p[0]) == 7, p[0] == 7);
            }
            step();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("set_choice_return_first.c", c_source)]);
    let verified = verified.expect("bare arm transports should advance the branch Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked arm transports should retain an expansion");
    assert!(
        matches!(
            tactics.get(1),
            Some(ProofTactic::Branch(branch))
                if matches!(
                    branch.then_tactics.as_slice(),
                    [ProofTactic::Step, ProofTactic::TransportUsing { premises, .. }]
                        if !premises.is_empty()
                ) && matches!(
                    branch.else_tactics.as_slice(),
                    [ProofTactic::Step, ProofTactic::TransportUsing { premises, .. }]
                        if !premises.is_empty()
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("set_choice_return_first.c", c_source)],
        "set_choice_return_first",
        CProofClaim::Grouped,
    )
    .expect("the retained branch transports should expand");
    verify_c0_sources(&expanded, &[("set_choice_return_first.c", c_source)])
        .expect("the explicit branch transports should independently re-derive");
}

#[test]
fn branch_arms_retain_nested_have_proofs() {
    let c_source = r#"
        int32 select_nonnegative(int32 flag) {
            int32 selected;
            if (flag != 0) {
                selected = 1;
            } else {
                selected = 2;
            }
            return selected;
        }
    "#;
    let click_source = r#"
        theorem int32_reflexive(value: int32) {
            ensures value == value by {
                normalize();
            }
        }

        verifying "select_nonnegative.c";

        int32 select_nonnegative(int32 flag) {
            ensures result >= 0;
        } by {
            step();
            branch ensuring {
                fact selected >= 0;
            } then {
                step();
                have selected == selected by {
                    apply(int32_reflexive(selected));
                }
            } else {
                step();
                have selected == selected by {
                    apply(int32_reflexive(selected));
                }
            }
            step();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("select_nonnegative.c", c_source)]);
    let verified = verified.expect("nested arm haves should advance the branch Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked branch haves should retain an expansion");
    let retained_have = |tactics: &[ProofTactic]| {
        matches!(
            tactics,
            [ProofTactic::Step, ProofTactic::Have(have)]
                if matches!(
                    &have.proof,
                    SourceProof::Script(body)
                        if matches!(
                            body.as_slice(),
                            [ProofTactic::ApplyTheoremUsing { application, premises }]
                                if application.name == "int32_reflexive" && premises.is_empty()
                        )
                )
        )
    };
    assert!(
        matches!(
            tactics.get(1),
            Some(ProofTactic::Branch(branch))
                if retained_have(&branch.then_tactics)
                    && retained_have(&branch.else_tactics)
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("select_nonnegative.c", c_source)],
        "select_nonnegative",
        CProofClaim::Grouped,
    )
    .expect("the retained branch haves should expand");
    verify_c0_sources(&expanded, &[("select_nonnegative.c", c_source)])
        .expect("the explicit nested arm proofs should independently re-derive");
}

#[test]
fn explicit_branch_arms_retain_terminal_execute_search() {
    let c_source = r#"
        int32 choose_one_or_two(int32 flag) {
            if (flag != 0) {
                return 1;
            } else {
                return 2;
            }
        }
    "#;
    let click_source = r#"
        verifying "choose_one_or_two.c";

        int32 choose_one_or_two(int32 flag) {
            ensures result == 1 or result == 2;
        } by {
            branch {
                execute();
            } else {
                execute();
            }
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("choose_one_or_two.c", c_source)]);
    let verified = verified.expect("terminal arm execution should advance the branch Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked terminal arms should retain an expansion");
    let Some(ProofTactic::If(proof_if)) = tactics.first() else {
        panic!("terminal execution branch should retain a logical if: {tactics:#?}");
    };
    for arm in [&proof_if.then_tactics, &proof_if.else_tactics] {
        assert!(
            matches!(arm.get(..2), Some([ProofTactic::Step, ProofTactic::Step])),
            "each terminal arm should begin with its checked entry and return steps: {arm:#?}"
        );
        assert!(
            arm.iter()
                .all(|tactic| !matches!(tactic, ProofTactic::SmartExecute)),
            "terminal arm expansion must not retain smart execution: {arm:#?}"
        );
        assert!(
            arm.iter()
                .all(|tactic| !matches!(tactic, ProofTactic::Simp)),
            "each terminal arm must retain only checked operations: {arm:#?}"
        );
    }
    let expanded = expand_c0_claim_source(
        click_source,
        &[("choose_one_or_two.c", c_source)],
        "choose_one_or_two",
        CProofClaim::Grouped,
    )
    .expect("the retained terminal branch should expand");
    verify_c0_sources(&expanded, &[("choose_one_or_two.c", c_source)])
        .expect("the explicit terminal arm steps should independently re-derive");
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn callback_status_proofs_expand_at_every_smart_site() {
    let markdown = include_str!("../../../mdtests/c_contract_executes_status.md");
    let mdtest = crate::cli::parse_mdtest(std::path::Path::new("status.md"), markdown).unwrap();
    let source = mdtest.click_source.as_deref().unwrap();
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &c_sources).expect("ordinary status proofs verify");
    for site in c0_smart_tactic_source_sites(source, &c_sources).unwrap() {
        let position =
            c0_tactic_source_position(source, &c_sources, &site.claim_label, site.source_index)
                .unwrap();
        let expanded =
            expand_c0_tactic_source_at(source, &c_sources, position.line, position.column).unwrap();
        if let Err(error) = verify_c0_sources(&expanded, &c_sources) {
            panic!(
                "{}:{}: {}\n{expanded}",
                position.line,
                position.column,
                error.message()
            );
        }
    }
}

fn nested_callback_status_sources() -> (String, Vec<(String, String)>) {
    let markdown = include_str!("../../../mdtests/c_contract_executes_status_nested.md");
    let mdtest =
        crate::cli::parse_mdtest(std::path::Path::new("nested-status.md"), markdown).unwrap();
    let source = mdtest.click_source.as_deref().unwrap().to_string();
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.clone(), source.clone()))
        .collect::<Vec<_>>();
    (source, c_sources)
}

/// The `lift.` theorem sites of the nested status fixture, grouped so each
/// expansion test below stays independently bounded. The ordinary verification
/// test asserts this inventory; update the groups when it changes.
fn nested_callback_status_lift_site_groups() -> Vec<Vec<usize>> {
    vec![vec![6, 7], vec![8, 10, 11], vec![13, 16]]
}

fn expand_nested_callback_lift_site(source: &str, c_sources: &[(&str, &str)], source_index: usize) {
    let position =
        c0_tactic_source_position(source, c_sources, "lift.ensures_0", source_index).unwrap();
    let expanded =
        expand_c0_tactic_source_at(source, c_sources, position.line, position.column).unwrap();
    verify_c0_sources(&expanded, c_sources).unwrap_or_else(|error| {
        panic!(
            "{}:{}: {}\n{expanded}",
            position.line,
            position.column,
            error.message()
        );
    });
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn nested_callback_status_cases_verify() {
    let (source, c_sources) = nested_callback_status_sources();
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&source, &c_sources).expect("nested status proofs verify");
    let sites = c0_smart_tactic_source_sites(&source, &c_sources).unwrap();
    let lift = sites
        .iter()
        .filter(|site| site.claim_label.starts_with("lift."))
        .map(|site| (site.source_index, site.tactic_name.clone()))
        .collect::<Vec<_>>();
    let expected = [
        (6, "have"),
        (7, "have"),
        (8, "have"),
        (10, "have"),
        (11, "have"),
        (13, "simp"),
        (16, "simp"),
    ];
    assert_eq!(
        lift.iter()
            .map(|(index, tactic)| (*index, tactic.as_str()))
            .collect::<Vec<_>>(),
        expected,
        "the split expansion tests must cover every `lift.` theorem site",
    );
    let grouped = nested_callback_status_lift_site_groups();
    assert_eq!(
        grouped
            .iter()
            .flatten()
            .collect::<std::collections::BTreeSet<_>>(),
        expected
            .iter()
            .map(|(index, _)| index)
            .collect::<std::collections::BTreeSet<_>>(),
        "each `lift.` site must belong to exactly one expansion group",
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn nested_callback_status_item_zero_cases_expand_and_reverify() {
    let (source, c_sources) = nested_callback_status_sources();
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&source, &c_sources).expect("nested status proofs verify");
    for source_index in nested_callback_status_lift_site_groups()[0].clone() {
        expand_nested_callback_lift_site(&source, &c_sources, source_index);
    }
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn nested_callback_status_item_branch_cases_expand_and_reverify() {
    let (source, c_sources) = nested_callback_status_sources();
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&source, &c_sources).expect("nested status proofs verify");
    for source_index in nested_callback_status_lift_site_groups()[1].clone() {
        expand_nested_callback_lift_site(&source, &c_sources, source_index);
    }
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn nested_callback_status_closer_cases_expand_and_reverify() {
    let (source, c_sources) = nested_callback_status_sources();
    let c_sources = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(&source, &c_sources).expect("nested status proofs verify");
    for source_index in nested_callback_status_lift_site_groups()[2].clone() {
        expand_nested_callback_lift_site(&source, &c_sources, source_index);
    }
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn acquired_callback_ownership_expands_at_every_smart_site() {
    let markdown = include_str!("../../../mdtests/c_contract_executes_acquire.md");
    let mdtest = crate::cli::parse_mdtest(std::path::Path::new("acquire.md"), markdown).unwrap();
    let source = mdtest.click_source.as_deref().unwrap();
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &c_sources).expect("acquisition proof verifies");
    let sites = c0_smart_tactic_source_sites(source, &c_sources).unwrap();
    assert!(!sites.is_empty());
    for site in sites {
        let position =
            c0_tactic_source_position(source, &c_sources, &site.claim_label, site.source_index)
                .unwrap();
        let expanded =
            expand_c0_tactic_source_at(source, &c_sources, position.line, position.column).unwrap();
        verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
            panic!(
                "{}:{}: {}\n{expanded}",
                position.line,
                position.column,
                error.message()
            );
        });
    }
}

#[test]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn callback_pool_cycle_expands_at_every_smart_site() {
    let markdown = include_str!("../../../mdtests/c_callback_pool_cycle.md");
    let mdtest = crate::cli::parse_mdtest(std::path::Path::new("cycle.md"), markdown).unwrap();
    let source = mdtest.click_source.as_deref().unwrap();
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &c_sources).expect("pool cycle verifies");
    let sites = c0_smart_tactic_source_sites(source, &c_sources).unwrap();
    assert!(!sites.is_empty());
    for site in sites {
        let position =
            c0_tactic_source_position(source, &c_sources, &site.claim_label, site.source_index)
                .unwrap();
        let expanded =
            expand_c0_tactic_source_at(source, &c_sources, position.line, position.column).unwrap();
        verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
            panic!(
                "{}:{}: {}\n{expanded}",
                position.line,
                position.column,
                error.message()
            )
        });
    }
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn callback_counter_refinement_expands_at_every_smart_site() {
    let markdown = include_str!("../../../mdtests/c_contract_executes_counter.md");
    let mdtest = crate::cli::parse_mdtest(std::path::Path::new("counter.md"), markdown).unwrap();
    let source = mdtest.click_source.as_deref().unwrap();
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &c_sources).expect("counter refinement verifies");
    let sites = c0_smart_tactic_source_sites(source, &c_sources).unwrap();
    assert!(!sites.is_empty());
    for site in sites {
        let position =
            c0_tactic_source_position(source, &c_sources, &site.claim_label, site.source_index)
                .unwrap();
        let expanded =
            expand_c0_tactic_source_at(source, &c_sources, position.line, position.column).unwrap();
        verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
            panic!(
                "{}:{}: {}\n{expanded}",
                position.line,
                position.column,
                error.message()
            )
        });
    }
}

#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn const_callback_contract_expands_at_every_smart_site() {
    let markdown = include_str!("../../../mdtests/const_callback_contract.md");
    let mdtest =
        crate::cli::parse_mdtest(std::path::Path::new("const_callback.md"), markdown).unwrap();
    let source = mdtest.click_source.as_deref().unwrap();
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &c_sources).unwrap();
    let sites = c0_smart_tactic_source_sites(source, &c_sources).unwrap();
    assert!(!sites.is_empty());
    for site in sites {
        let position =
            c0_tactic_source_position(source, &c_sources, &site.claim_label, site.source_index)
                .unwrap();
        let expanded =
            expand_c0_tactic_source_at(source, &c_sources, position.line, position.column).unwrap();
        verify_c0_sources(&expanded, &c_sources).unwrap();
    }
}

#[test]
fn transformed_resource_branch_interface_retains_its_common_descendant() {
    let markdown = include_str!("../../../mdtests/proof_branch_composite_resource_transform.md");
    let mdtest = crate::cli::parse_mdtest(
        std::path::Path::new("proof_branch_composite_resource_transform.md"),
        markdown,
    )
    .expect("the transformed-resource regression should parse");
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("the regression should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let (verified, checked_interface_joins) =
        crate::surface::proof::count_checked_execution_interface_joins(|| {
            verify_c0_sources(click_source, &c_sources)
        });
    let verified = verified.expect("the transformed resource branch should stay on Proof");
    assert!(
        checked_interface_joins > 0,
        "the source branch must reach the checked two-arm Proof join"
    );
    let tactics = verified
        .last()
        .expect("select_ready should be the final verified function")
        .expanded_proof_tactics()
        .expect("the transformed interface should retain an expansion");
    let arm_retains_fold =
        |arm: &[ProofTactic]| matches!(arm, [ProofTactic::Step, ProofTactic::FoldResource(_)]);
    assert!(
        matches!(
            tactics.as_slice(),
            [
                ProofTactic::Step,
                ProofTactic::Branch(branch),
                ProofTactic::ObserveResource(_),
                ..
            ] if matches!(
                branch.ensuring.as_deref(),
                Some([
                    ProofAssertion::Fact(_),
                    ProofAssertion::Resource(ResourceClause::Declared {
                        access: ResourceAccessMode::Own,
                        name,
                        ..
                    }),
                ]) if name == "ready_bundle"
            ) && arm_retains_fold(&branch.then_tactics)
                && arm_retains_fold(&branch.else_tactics)
        ),
        "{tactics:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &c_sources,
        "select_ready",
        CProofClaim::Ensure(0),
    )
    .expect("the transformed resource branch should expand");
    verify_c0_sources(&expanded, &c_sources)
        .expect("the retained changed-resource interface should independently re-derive");
}

#[test]
fn decided_branch_interface_retains_the_surviving_checked_state() {
    let c_source = r#"
        int32 selected_nonnegative(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        verifying "selected_nonnegative.c";

        int32 selected_nonnegative(int32 x) {
            requires x < 0;
            ensures result == 1;
        } by {
            branch ensuring {
                fact x == 1;
            } then { step(); } else { step(); }
            step();
            simp();
        }
    "#;

    let verified = verify_c0_sources(click_source, &[("selected_nonnegative.c", c_source)]);
    let verified = verified.expect("the sole feasible interface arm should stay on Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the decided interface should retain an expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Branch(branch))
                if branch.ensuring.is_some()
                    && matches!(branch.then_tactics.as_slice(), [ProofTactic::Step])
                    && branch.else_tactics.is_empty()
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("selected_nonnegative.c", c_source)],
        "selected_nonnegative",
        CProofClaim::Grouped,
    )
    .expect("the decided interface should expand");
    verify_c0_sources(&expanded, &[("selected_nonnegative.c", c_source)])
        .expect("the decided retained interface should independently re-derive");
}

#[test]
fn open_scope_retains_its_checked_branch_interface() {
    let c_source = r#"
        int32 scoped_nonnegative(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "scoped_nonnegative.c";

        int32 scoped_nonnegative(int32 x) {
            owns marker(x);
            ensures result >= 0;
        } by {
            open(marker(x)) {
                branch ensuring {
                    fact x >= 0;
                } then { step(); } else { step(); }
                step();
            }
            simp();
        }
    "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("scoped_nonnegative.c", c_source)])
    });
    let verified = verified.expect("the scoped branch interface should stay on Proof");
    assert_eq!(
        flat_units, 1,
        "the scoped interface should retain one Proof"
    );
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the scoped branch interface should retain its expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::Branch(branch), ProofTactic::Step]
                        if branch.ensuring.is_some()
                            && matches!(branch.then_tactics.as_slice(), [ProofTactic::Step])
                            && matches!(branch.else_tactics.as_slice(), [ProofTactic::Step])
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("scoped_nonnegative.c", c_source)],
        "scoped_nonnegative",
        CProofClaim::Grouped,
    )
    .expect("the scoped branch interface should expand");
    verify_c0_sources(&expanded, &[("scoped_nonnegative.c", c_source)])
        .expect("the scoped retained interface should independently re-derive");
}

#[test]
fn open_scope_retains_its_checked_execution_branch() {
    let c_source = r#"
        int32 empty_branch(int32 x) {
            if (x < 0) {
            } else {
            }
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "empty_branch.c";

        int32 empty_branch(int32 x) {
            owns marker(x);
            ensures result == x;
        } by {
            open(marker(x)) {
                branch {
                } else {
                }
                step();
            }
            simp();
        }
    "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("empty_branch.c", c_source)])
    });
    let verified = verified.expect("the execution branch should join inside the open Proof");
    assert_eq!(flat_units, 1, "the scoped branch should retain one Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the checked grouped proof should retain its scoped branch");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::Branch(branch), ProofTactic::Step]
                        if branch.ensuring.is_none()
                            && branch.then_tactics.is_empty()
                            && branch.else_tactics.is_empty()
                )
        ),
        "{tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("empty_branch.c", c_source)],
        "empty_branch",
        CProofClaim::Grouped,
    )
    .expect("the grouped scoped branch should expand");
    verify_c0_sources(&expanded, &[("empty_branch.c", c_source)])
        .expect("the retained scoped branch should independently check");
}

#[test]
fn open_scope_retains_a_decided_execution_branch_and_its_continuation() {
    let c_source = r#"
        int32 selected_branch(int32 x) {
            if (x < 0) {
                x = 1;
            } else {
                x = 2;
            }
            return x;
        }
    "#;
    let click_source = r#"
        resource marker(x: int32) {
            fact x == x;
        }

        verifying "selected_branch.c";

        int32 selected_branch(int32 x) {
            requires x < 0;
            owns marker(x);
            ensures result == 1;
        } by {
            open(marker(x)) {
                branch { step(); } else { step(); }
                step();
            }
            simp();
        }
    "#;

    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("selected_branch.c", c_source)])
    });
    let verified = verified.expect("the decided execution path should stay inside the open Proof");
    assert_eq!(flat_units, 1, "the decided scope should retain one Proof");
    let tactics = verified[0]
        .expanded_proof_tactics()
        .expect("the scoped decided branch should retain its expansion");
    assert!(
        matches!(
            tactics.first(),
            Some(ProofTactic::Open(open))
                if matches!(
                    open.tactics.as_slice(),
                    [ProofTactic::If(proof_if), ProofTactic::Step]
                        if proof_if.then_tactics.len() == 2
                            && proof_if.else_tactics.is_empty()
                            && matches!(
                                proof_if.then_tactics.first(),
                                Some(ProofTactic::Step)
                            )
                )
        ),
        "the open child should retain the closed decided node followed by its continuation: {tactics:#?}"
    );
    let expanded = expand_c0_claim_source(
        click_source,
        &[("selected_branch.c", c_source)],
        "selected_branch",
        CProofClaim::Grouped,
    )
    .expect("the scoped decided branch should expand");
    let (reverified, checked_ifs) = proof::count_checked_expanded_execution_ifs(|| {
        verify_c0_sources(&expanded, &[("selected_branch.c", c_source)])
    });
    reverified.expect("the scoped decided expansion should independently re-derive the proof");
    assert_eq!(
        checked_ifs, 1,
        "the expanded C `if` should use its Proof operation"
    );

    let mut corrupted_tactics = tactics.clone();
    let Some(ProofTactic::Open(open)) = corrupted_tactics.first_mut() else {
        unreachable!()
    };
    let Some(ProofTactic::If(proof_if)) = open.tactics.first_mut() else {
        unreachable!()
    };
    // A checked C-branch entry is a bare `step();` deciding the `if` from
    // the case its proof `if` assumed; removing it leaves the arm outside the
    // branch it claims to prove.
    let Some(ProofTactic::Step) = proof_if.then_tactics.first() else {
        unreachable!()
    };
    proof_if.then_tactics.remove(0);
    let corrupted_proof = crate::surface::printing::format_proof_tactics(&corrupted_tactics)
        .expect("the corrupted tactics should remain surface-expressible");
    let proof_start = expanded
        .find("} by {")
        .map(|index| index + 2)
        .expect("the expanded claim should retain its proof block");
    let proof_end = expanded
        .rfind('}')
        .map(|index| index + 1)
        .expect("the expanded claim should close its proof block");
    let mut corrupted = expanded.clone();
    corrupted.replace_range(proof_start..proof_end, &corrupted_proof);
    let corrupted_result = verify_c0_sources(&corrupted, &[("selected_branch.c", c_source)]);
    corrupted_result
        .expect_err("tampering with the checked C-branch entry must invalidate the expansion");
}

#[test]
fn automatic_terminal_branch_retains_its_checked_proof_outcomes() {
    let c_source = r#"
            int32 choose(int32 value) {
                if (value < 0) {
                    return 1;
                } else {
                    return 2;
                }
            }
        "#;
    let click_source = r#"
            verifying "choose.c";

            int32 choose(int32 value) {
                ensures result == 1 or result == 2;
            } by {
                execute();
                simp();
            }
        "#;

    let (verified, planning_transitions) = count_planning_statement_transitions(|| {
        verify_c0_sources(click_source, &[("choose.c", c_source)])
    });
    let verified = verified.expect("automatic terminal branch should verify");
    assert_eq!(
        planning_transitions, 0,
        "the automatic terminal branch must search only on checked Proof descendants"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("terminal branch should retain an expansion");
    let Some(ProofTactic::If(proof_if)) = expanded.first() else {
        panic!("terminal branch should expand as a logical if: {expanded:#?}");
    };
    for (name, arm) in [
        ("then", &proof_if.then_tactics),
        ("else", &proof_if.else_tactics),
    ] {
        assert!(
            matches!(arm.first(), Some(ProofTactic::Step)),
            "{name} arm should retain its checked C-branch entry step: {arm:#?}"
        );
        assert!(
            matches!(arm.get(1), Some(ProofTactic::Step)),
            "{name} arm should retain its checked return step: {arm:#?}"
        );
        assert!(
            arm.iter().all(|tactic| !matches!(
                tactic,
                ProofTactic::SmartExecute | ProofTactic::ExecuteUntil(_) | ProofTactic::Simp
            )),
            "{name} arm expansion must contain only retained simple tactics: {arm:#?}"
        );
    }
    let expanded_source = expand_c0_claim_source(
        click_source,
        &[("choose.c", c_source)],
        "choose",
        CProofClaim::Grouped,
    )
    .expect("terminal branch should expand into source");
    verify_c0_sources(&expanded_source, &[("choose.c", c_source)])
        .expect("the retained terminal branch should independently reverify");
}

#[test]
fn fixed_state_smart_have_retains_a_checked_simple_closer() {
    let c_source = r#"
            int32 identity(int32 value) {
                return value;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 value) {
                requires value >= 0;
                ensures result >= 0;
            } by {
                have value >= 0 by simp();
                step();
                assumption();
            }
        "#;
    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("checked fixed-state smart have should verify");
}

#[test]
fn fixed_state_smart_have_retains_a_checked_theorem_application() {
    let c_source = r#"
            int32 first(int32 x, int32 y, int32 z) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "first.c";

            int32 first(int32 x, int32 y, int32 z) {
                requires x <= y;
                requires y < z;
                ensures result < z;
            } by {
                have x < z by simp();
                execute();
                simp();
            }
        "#;
    let verified = verify_c0_sources(click_source, &[("first.c", c_source)]);
    verified.expect("checked fixed-state smart have should apply signed-order transitivity");

    let expanded = expand_c0_claim_source(
        click_source,
        &[("first.c", c_source)],
        "first",
        CProofClaim::Grouped,
    )
    .expect("the theorem-backed have should expand into proof steps");
    assert!(!expanded.contains("have x < z by simp()"), "{expanded}");
    assert!(expanded.contains("have x < z by {"), "{expanded}");
    assert!(expanded.contains("apply"), "{expanded}");
    verify_c0_sources(&expanded, &[("first.c", c_source)])
        .expect("the retained theorem-backed have should independently reverify");
}

#[test]
fn explicit_linear_fixed_state_have_uses_the_checked_proof_path() {
    let c_source = r#"
            int32 identity(int32 value) {
                return value;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 value) {
                requires value >= 0;
                ensures result >= 0;
            } by {
                have value >= 0 by {
                    assumption();
                }
                step();
                assumption();
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("explicit fixed-state have should advance through its checked proof step");
    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
    )
    .expect("explicit checked fixed-state have should remain expandable");
    assert!(expanded.contains("have value >= 0 by {"));
    assert!(expanded.matches("assumption();").count() >= 2);
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("expanded explicit fixed-state have should independently check");
}

#[test]
fn explicit_post_execution_have_uses_the_checked_outcome_proof_path() {
    let c_source = r#"
            int32 identity(int32 value) {
                return value;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 value) {
                requires value >= 0;
                ensures result >= 0;
            } by {
                execute();
                have result >= 0 by {
                    assumption();
                }
                assumption();
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)]);
    verified.expect("explicit post-execution have should advance through its outcome Proof");

    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
    )
    .expect("explicit checked outcome have should remain expandable");
    assert!(expanded.contains("have result >= 0 by {"), "{expanded}");
    assert!(expanded.matches("assumption();").count() >= 2, "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("expanded explicit outcome have should independently check");
}

#[test]
fn quantified_outcome_simp_keeps_its_binder_on_the_checked_goal() {
    let c_source = r#"
            int32 bounded(int32 value) {
                return value;
            }
        "#;
    let click_source = r#"
            verifying "bounded.c";

            int32 bounded(int32 value) {
                requires forall (k: int32) {
                    0 <= k and k < 3 implies k <= value
                };
                ensures narrow: forall (k: int32) {
                    0 <= k and k < 2 implies k <= value
                };
            } by {
                execute();
                simp();
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("bounded.c", c_source)]);
    verified.expect("the quantified outcome should verify through Proof");
    let expanded = expand_c0_claim_source(
        click_source,
        &[("bounded.c", c_source)],
        "bounded",
        CProofClaim::Grouped,
    )
    .expect("the quantified outcome proof should expand");
    assert!(expanded.contains("intro();"), "{expanded}");
    assert!(expanded.contains("instantiate("), "{expanded}");
    verify_c0_sources(&expanded, &[("bounded.c", c_source)])
        .expect("the retained binder-aware certificate should check");
}

#[test]
fn outcome_simp_with_no_open_claims_is_an_empty_proof_transition() {
    let c_source = r#"
        struct object { int32 refs; };

        void release(struct object* obj) {
            obj->refs = 0;
        }
    "#;
    let click_source = r#"
        resource object_cell(obj: struct object*) {
            owns *obj;
            fact obj->refs == 1;
        }

        verifying "release.c";

        void release(struct object* obj) {
            consumes object_cell(obj);
        } by {
            unfold(object_cell(obj));
            execute();
            simp();
        }
    "#;
    let sources = [("release.c", c_source)];

    let verified = verify_c0_sources(click_source, &sources);
    verified.expect("a final simp with no open claims should be a no-op");
    let expanded = expand_c0_claim_source(click_source, &sources, "release", CProofClaim::Grouped)
        .expect("the empty outcome transition should expand");
    let release_proof = expanded
        .split("void release")
        .nth(1)
        .expect("expanded release proof should exist");
    assert!(!release_proof.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the expansion without the empty simp should check");
}

#[test]
fn outcome_predicate_unfold_relowers_resource_counts_on_the_checked_proof() {
    let c_source = r#"
        struct pool { int32 checked_out; int32 capacity; };

        void init(struct pool* pool, int32 capacity) {
            pool->checked_out = 0;
            pool->capacity = capacity;
        }
    "#;
    let click_source = r#"
        authorized resource pool_object(pool: struct pool*) {}

        authorized resource pool_slot(pool: struct pool*) {}

        predicate valid_pool(pool: struct pool*) {
            0 <= pool->checked_out and
            pool->checked_out == count(pool_object(pool)) and
            pool->capacity == pool->checked_out + count(pool_slot(pool))
        }

        verifying "init.c";

        void init(struct pool* pool, int32 capacity) {
            requires 0 < capacity;
            owns *pool;
            owns authority(pool_object(pool));
            owns authority(pool_slot(pool));
            requires count(pool_object(pool)) == 0;
            requires count(pool_slot(pool)) == 0;
            produces capacity of pool_slot(pool);
            ensures valid_pool(pool);
        } by {
            fold(capacity of pool_slot(pool));
            execute();
            simp();
        }
    "#;
    let sources = [("init.c", c_source)];

    let verified = verify_c0_sources(click_source, &sources);
    verified.expect("the unfolded resource-count goal should close through Proof");

    let expanded = expand_c0_claim_source(click_source, &sources, "init", CProofClaim::Grouped)
        .expect("the retained predicate closure should expand");
    assert!(
        expanded.contains("have valid_pool(pool) by {"),
        "{expanded}"
    );
    assert!(expanded.contains("unfold(valid_pool);"), "{expanded}");
    assert!(expanded.contains("normalize();"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained predicate closure should check independently");
}

#[test]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn outcome_predicate_unfold_provenance_survives_nested_have_expansion() {
    let c_source = r#"
        int32 sort_three_cells(int32 p[3]) {
            int32 tmp;
            if (p[1] < p[0]) {
                tmp = p[0];
                p[0] = p[1];
                p[1] = tmp;
            }
            if (p[2] < p[1]) {
                tmp = p[1];
                p[1] = p[2];
                p[2] = tmp;
            }
            if (p[1] < p[0]) {
                tmp = p[0];
                p[0] = p[1];
                p[1] = tmp;
            }
            return 0;
        }
    "#;
    let click_source = r#"
        import click::permutation;

        verifying "sort_three_cells.c";

        int32 sort_three_cells(int32 p[3]) {
            consumes p[0..3];
            ensures permutation::permutation(p, old(p), 0, 3) by {
                execute();
                unfold(permutation::permutation);
                simp();
            }
        }
    "#;
    let sources = [("sort_three_cells.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(click_source, &sources));
    verified.expect("the surviving unfold-owned universal should close through Proof");
    assert_eq!(
        flat_units, 1,
        "the nested outcome tree should retain one Proof"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "sort_three_cells",
        CProofClaim::Ensure(0),
    )
    .expect("the retained nested predicate proof should expand");
    assert!(
        expanded.contains("have permutation::permutation(p, old(p), 0, 3) by {"),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(
        expanded.contains("unfold(permutation::permutation);"),
        "{expanded}"
    );
    let (reverified, expanded_flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(&expanded, &sources));
    assert_eq!(
        expanded_flat_units, 1,
        "the rewritten nested proof should retain one Proof"
    );
    reverified.expect("the retained nested predicate proof should check independently");

    let corrupted = expanded.replace("statement(1).entry", "statement(6).entry");
    assert_ne!(
        corrupted, expanded,
        "the expansion should expose its checked root branch anchor"
    );
    let corrupted_result = { verify_c0_sources(&corrupted, &sources) };
    let error = corrupted_result
        .expect_err("tampering with the nested execution branch anchor must invalidate the proof");
    assert!(
        error
            .message()
            .contains("expanded execution branch condition does not match the checked C branch")
            || error
                .message()
                .contains("no state snapshot was recorded for `statement(6).entry`"),
        "the checked Proof split should reject the tamper directly: {error:?}"
    );
}

#[test]
fn post_execution_if_expansion_retains_earlier_have_facts() {
    for filename in [
        "post_execution_if_uses_earlier_have.md",
        "post_execution_if_uses_nested_have_and_continuation.md",
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(filename);
        let markdown = std::fs::read_to_string(&path).unwrap();
        let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
        let source = fixture.click_source.as_deref().unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        verify_c0_sources(source, &sources).unwrap();
        for needle in ["have old(a) >= old(b);", "have result == a;"] {
            let offset = source.find(needle).unwrap();
            let position = expansion::position_at_offset(source, offset);
            let expanded =
                expand_c0_tactic_source_at(source, &sources, position.line, position.column)
                    .unwrap_or_else(|error| panic!("{filename}, {needle}: {error:?}"));
            assert_ne!(expanded, source, "{filename}, {needle} was not expanded");
            verify_c0_sources(&expanded, &sources)
                .unwrap_or_else(|error| panic!("{filename}, {needle}: {error:?}"));
        }
    }
}

#[test]
fn successive_post_execution_ifs_stay_on_one_proof() {
    let c_source = r#"
        int32 two_decisions(int32 x, int32 y) {
            int32 result = 0;
            if (x > 0) {
                result = result + 1;
            }
            if (y > 0) {
                result = result + 2;
            }
            return result;
        }
    "#;
    let click_source = r#"
        verifying "two_decisions.c";

        int32 two_decisions(int32 x, int32 y) {
            ensures 0 <= result and result <= 3 by {
                execute();
                if at(statement(2).entry, x) > at(statement(2).entry, 0) {
                    have result == result by simp();
                } else {
                    have result == result by simp();
                }
                if at(statement(5).entry, y) > at(statement(5).entry, 0) {
                    have result == result by simp();
                } else {
                    have result == result by simp();
                }
                simp();
            }
        }
    "#;
    let sources = [("two_decisions.c", c_source)];

    let (verified, flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(click_source, &sources));
    verified.expect("successive outcome splits should verify");
    assert_eq!(flat_units, 1, "the outcome splits should retain one Proof");

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "two_decisions",
        CProofClaim::Ensure(0),
    )
    .expect("successive outcome splits should expand");
    assert!(expanded.contains("statement(2).entry"), "{expanded}");
    assert!(expanded.contains("statement(5).entry"), "{expanded}");
    let (reverified, expanded_flat_units) =
        proof::count_flat_proof_units(|| verify_c0_sources(&expanded, &sources));
    reverified.expect("the rewritten outcome splits should verify normally");
    assert_eq!(
        expanded_flat_units, 1,
        "the rewritten outcome splits should retain one Proof"
    );

    let corrupted = expanded.replace("statement(2).entry", "statement(5).entry");
    assert_ne!(
        corrupted, expanded,
        "the expansion should expose the first C branch"
    );
    let corrupted_result = { verify_c0_sources(&corrupted, &sources) };
    let error = corrupted_result.expect_err("the corrupted branch anchor must be rejected");
    // The corrupted anchor names a statement that has not been executed
    // where the split is stated; the Proof rejects it at lowering.
    assert!(
        error
            .message()
            .contains("does not match the checked C branch")
            || error
                .message()
                .contains("no state snapshot was recorded for `statement(5).entry`"),
        "the Proof-owned C split should reject the corruption directly: {error:?}"
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn bound_universal_outcome_retains_instantiation_and_transport() {
    let c_source = r#"
        int32 bubble_pass3(int32 p[3]) {
            int32 j;
            int32 tmp;
            j = 0;
            while (j < 2) {
                if (p[j + 1] < p[j]) {
                    tmp = p[j];
                    p[j] = p[j + 1];
                    p[j + 1] = tmp;
                }
                j = j + 1;
            }
            return 0;
        }
    "#;
    let click_source = r#"
        verifying "bubble_pass3.c";

        predicate all_le_range(p: int32[], lo: int32, hi: int32, x: int32) {
            forall (k: int32) {
                0 <= k and lo <= k and k < hi implies p[k] <= x
            }
        }

        int32 bubble_pass3(int32 p[3]) {
            consumes p[0..3];
            ensures all_le_range(p, 0, 2, p[2]);
        } by {
            step();
            step();
            step();
            loop {
                decreases 2 - j;
                invariant j >= 0 and j <= 2;
                invariant all_le_range(p, 0, j, p[j]);
                initialize by {
                    unfold(all_le_range);
                    simp();
                }
                preserve by {
                    branch ensuring {
                        fact p[j] <= p[j + 1];
                        fact all_le_range(p, 0, j, p[j + 1]);
                    } then {
                        step();
                        step();
                        step();
                        have defined(j + 1) by { simp(); }
                        have p[j] <= p[j + 1] by { simp(); }
                        have all_le_range(p, 0, j, p[j + 1]) by {
                            unfold(all_le_range);
                            simp();
                        }
                    } else {
                        have defined(j + 1) by { simp(); }
                        have p[j] <= p[j + 1] by { simp(); }
                        have all_le_range(p, 0, j, p[j + 1]) by {
                            unfold(all_le_range);
                            simp();
                        }
                    }
                    step();
                    unfold(all_le_range);
                    close_invariants();
                }
            }
            step();
            unfold(all_le_range);
            simp();
        }
    "#;
    let sources = [("bubble_pass3.c", c_source)];

    let verified = verify_c0_sources(click_source, &sources);
    verified.expect("the bound universal outcome should close through Proof");

    let expanded =
        expand_c0_claim_source(click_source, &sources, "bubble_pass3", CProofClaim::Grouped)
            .expect("the retained bound universal proof should expand");
    assert!(expanded.contains("instantiate("), "{expanded}");
    assert!(expanded.contains("transport("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained bound universal proof should check independently");
}

const BOUND_UNIVERSAL_FIXTURE_CASES: &[(&str, &str)] = &[
    ("bubble_pass3_max_suffix.md", "bubble_pass3"),
    ("bubble_sort3_two_pass_sorted.md", "bubble_sort3_two_pass"),
];

fn assert_bound_universal_fixture_has_no_outcome_fallbacks(filename: &str, function: &str) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join(filename);
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .unwrap_or_else(|| panic!("`{}` has no Click source", path.display()));
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    // Expansion verifies the original smart proof while retaining its event
    // stream; collect that one pass rather than verifying the same source
    // once solely for the fallback census and again for expansion.
    let expanded = expand_c0_claim_source(click_source, &c_sources, function, CProofClaim::Grouped);
    let expanded =
        expanded.unwrap_or_else(|error| panic!("failed to expand `{}`: {error:?}", path.display()));

    assert!(
        expanded.contains("if k < (j - 1)"),
        "expanded proof from `{}` omitted the checked upper-bound split",
        path.display()
    );
    // Expansion spells the library theorem by its bare name and imports its
    // module.
    assert!(
        expanded.contains("int32_less_than_increment_implies_less_equal("),
        "expanded proof from `{}` omitted the split's explicit bound theorem",
        path.display()
    );
    assert!(
        expanded.contains("import click::machine_integer;"),
        "expanded proof from `{}` does not import the bound theorem's module",
        path.display()
    );
    verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
        panic!(
            "expanded proof from `{}` failed independent verification: {error:?}",
            path.display()
        )
    });
}

#[test]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn bound_universal_bubble_pass3_max_suffix_has_no_outcome_fallbacks() {
    let (filename, function) = BOUND_UNIVERSAL_FIXTURE_CASES[0];
    assert_bound_universal_fixture_has_no_outcome_fallbacks(filename, function);
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn bound_universal_bubble_sort3_two_pass_sorted_has_no_outcome_fallbacks() {
    let (filename, function) = BOUND_UNIVERSAL_FIXTURE_CASES[1];
    assert_bound_universal_fixture_has_no_outcome_fallbacks(filename, function);
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn matched_resource_quantified_fact_expands_and_reverifies() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/resource_match_quantified_fact_round_trip.md");
    let markdown = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &markdown)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("matched quantified fact fixture should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let verified_for_expansion = verify_c0_sources(click_source, &c_sources)
        .expect("the matched quantified resource fact should verify");
    let expanded =
        expand_checked_grouped_claim(click_source, &verified_for_expansion, "write_zero")
            .expect("the matched quantified resource proof should expand");
    assert!(expanded.contains("match prefix.tag"), "{expanded}");
    assert!(expanded.contains("instantiate(forall"), "{expanded}");
    assert!(expanded.contains("fold(zero_prefix(buffer)"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources)
        .expect("the expanded matched quantified resource proof should reverify");

    let selected =
        "instantiate(forall (k: int32) { 0 <= k and k < end implies buffer->data[k] == 0 }, 0)";
    assert!(expanded.contains(selected), "{expanded}");
    let changed_binder_body = expanded.replacen(
        selected,
        "instantiate(forall (k: int32) { 0 <= k and k < end implies buffer->data[0] == 0 }, 0)",
        1,
    );
    verify_c0_sources(&changed_binder_body, &c_sources)
        .expect_err("a serialized instantiation must retain the selected universal body");
}

#[test]
fn matched_resource_dependent_clauses_expand_and_reverify() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/resource_match_dependent_clauses.md");
    let markdown = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &markdown)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("dependent clause fixture should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let verified_for_expansion = verify_c0_sources(click_source, &c_sources)
        .expect("the matched dependent resource clauses should verify");
    let expanded = expand_checked_grouped_claim(click_source, &verified_for_expansion, "unchanged")
        .expect("the matched dependent resource proof should expand");
    assert!(expanded.contains("instantiate(forall"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources)
        .expect("the expanded dependent resource proof should reverify");

    let missing_bound = click_source.replacen("fact prefix <= capacity;", "", 1);
    assert_ne!(missing_bound, click_source);
    let refusal = verify_c0_sources(&missing_bound, &c_sources)
        .expect_err("a dependent load must not borrow a missing scalar bound");
    assert!(
        refusal
            .message
            .contains("without a covering contained memory resource with current read authority"),
        "missing scalar bound failed for an unrelated reason: {refusal:?}"
    );
}

#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn early_return_postcondition_path_selection_expands_and_reverifies() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/early_return_indexed_postcondition_path_selection.md");
    let markdown = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &markdown)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("early-return path fixture should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let verified_for_expansion = verify_c0_sources(click_source, &c_sources)
        .expect("the selected early-return postcondition path should verify");
    let expanded =
        expand_checked_grouped_claim(click_source, &verified_for_expansion, "write_selected")
            .expect("the selected early-return postcondition path should expand");
    assert!(expanded.contains("match before.shape"), "{expanded}");
    assert!(
        expanded.contains("selected_index(WriteShape::At(position))"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &c_sources)
        .expect("the expanded selected postcondition path should reverify");
}

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn snapshot_and_post_call_transport_fixtures_have_no_outcome_fallbacks() {
    for (filename, function, claim, retained_step, corrupted_step) in [
        (
            "execute_expands_certified_post_call_fact.md",
            "restore_one",
            CProofClaim::Grouped,
            "have cell->value == 1",
            "have cell->value == 0",
        ),
        (
            "separate_symbolic_unwritten_read.md",
            "write_i_read_j",
            CProofClaim::Ensure(0),
            "normalize();",
            "normalize() using { 0u32 == 1u32; };",
        ),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(filename);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
        let mdtest = crate::cli::parse_mdtest(&path, &source)
            .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
        let click_source = mdtest
            .click_source
            .as_deref()
            .unwrap_or_else(|| panic!("`{}` has no Click source", path.display()));
        let c_sources = mdtest
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let verified = verify_c0_sources(click_source, &c_sources);
        verified.unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));

        let expanded = expand_c0_claim_source(click_source, &c_sources, function, claim)
            .unwrap_or_else(|error| panic!("failed to expand `{}`: {error:?}", path.display()));
        assert!(expanded.contains(retained_step), "{expanded}");
        verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
            panic!(
                "expanded proof from `{}` failed independent verification: {error:?}",
                path.display()
            )
        });

        // Corrupt a checked step even when C evaluation already establishes
        // the final value, so a fallback cannot hide an invalid certificate.
        let corrupted = expanded.replacen(retained_step, corrupted_step, 1);
        assert_ne!(corrupted, expanded);
        expansion::parse_source_with_c_layouts(&corrupted, &c_sources)
            .expect("the corrupted proof must remain well formed");
        verify_c0_sources(&corrupted, &c_sources)
            .expect_err("a corrupted retained proof step must be rejected");
    }
}

/// A stated `separate(..)` the proof consumed is load-bearing: deleting it
/// breaks the proof.
///
/// `separate_symbolic_unwritten_read` used to carry this check inside the
/// loop above, and stopped being able to when the entry partition
/// (`kernel::contract_entry_partition_facts`) made its own
/// `consumes p[i..i + 1]` / `views p[j..j + 1]` pair imply the separation it
/// states. This fixture declares no resource for `a` at all -- it is read
/// under a bare `viewable(..)` requirement -- so nothing implies its
/// separation from the owned global, and deleting it must still break the
/// proof.
#[test]
fn a_stated_separation_is_load_bearing() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join("a_separated_array_argument_survives_a_global_store.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .unwrap_or_else(|| panic!("`{}` has no Click source", path.display()));
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(click_source, &c_sources)
        .unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));
    let without_separation = click_source
        .lines()
        .filter(|line| !line.contains("separate(memory("))
        .collect::<Vec<_>>()
        .join("\n");
    assert_ne!(
        without_separation, click_source,
        "the fixture no longer states a separation"
    );
    assert!(
        verify_c0_sources(&without_separation, &c_sources).is_err(),
        "`{}` checked after deleting its required separation premise",
        path.display()
    );
}

const RESOURCE_EXAMPLE_PIPELINE_CASES: &[(&str, &str, &str, &str)] = &[
    (
        "linked-list",
        "linked_list.click",
        "list_roundtrip",
        "have node->next == tail by {\n        assumption();\n    }",
    ),
    (
        "input-cursor",
        "input_cursor.click",
        "input_cursor_shared_pipeline",
        "have right->data[right->pos] == data[0] by {\n        normalize() using {",
    ),
    (
        "owned-segmented-buffer",
        "owned_segmented_buffer.click",
        "owned_segmented_buffer_swap",
        "apply(int32_increment_less_equal_implies_less_than(0, owner->first_len)) using {",
    ),
    (
        "owned-string",
        "owned_string.click",
        "owned_string_init",
        "rewrite(owner->cap == capacity);",
    ),
    (
        "recursive-zero-list",
        "recursive_zero_list.click",
        "zero_list_pipeline",
        "fold(zero_list(first));",
    ),
    (
        "vector-push",
        "vector_push.click",
        "vector_push",
        "have 1 <= owner->len by {\n        arithmetic_certificate {",
    ),
];

// These fixtures put a function's outer closing brace at column zero.
// Compare both surrounding byte ranges so scoped checking cannot silently
// omit a rewrite to a helper, contract, import, or another declaration.
pub(super) fn only_function_proof_changed(before: &str, after: &str, function: &str) -> bool {
    let extent = |text: &str| {
        let signature = format!(" {function}(");
        assert_eq!(
            text.matches(&signature).count(),
            1,
            "ambiguous function: {function}"
        );
        let start = text.find(&signature).unwrap();
        let body = start + text[start..].find("} by {").unwrap() + "} by {".len();
        let end = body + text[body..].find("\n}").unwrap() + "\n}".len();
        (body, end)
    };
    let (before_start, before_end) = extent(before);
    let (after_start, after_end) = extent(after);
    before[..before_start] == after[..after_start] && before[before_end..] == after[after_end..]
}

pub(super) fn assert_only_function_proof_changed(before: &str, after: &str, function: &str) {
    assert!(
        only_function_proof_changed(before, after, function),
        "{function}: changed outside the selected proof"
    );
}

pub(super) fn verify_expanded_function_source(
    before: &str,
    after: &str,
    sources: &[(&str, &str)],
    function: &str,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if !only_function_proof_changed(before, after, function) {
        return verify_c0_sources(after, sources);
    }
    let checked = verify_c0_sources_functions(after, sources, [function.to_string()])?;
    assert!(!checked.is_empty());
    assert!(
        checked
            .iter()
            .all(|proof| proof.function_block.signature().name() == function)
    );
    Ok(checked)
}

// Use the same project API/profile as the complete original check. Every
// rewritten function is cold-checked, including all claims and paths; a
// declaration/import rewrite falls back to the complete project.
pub(super) fn verify_expanded_project_function_source(
    before: &str,
    after: &str,
    project: &ClickProject,
    c: &[(&str, &str)],
    owner: &str,
) -> Result<Vec<VerifiedCTheorem>, ClickError> {
    if !only_function_proof_changed(before, after, owner) {
        return verify_c0_project(project, c);
    }
    let checked = verify_project_functions(
        project,
        &ProgramInputs::Bundle(c.to_vec()),
        [owner.to_string()],
    )?;
    assert!(!checked.is_empty());
    assert!(
        checked
            .iter()
            .all(|proof| proof.function_block.signature().name() == owner)
    );
    Ok(checked)
}

fn assert_resource_example_pipeline_has_no_outcome_fallbacks(
    project: &str,
    sidecar: &str,
    function: &str,
    retained_step: &str,
) {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = manifest.join("examples").join(project).join(sidecar);
    let click_source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let sources = crate::cli::read_verifying_sources(&path, &click_source)
        .unwrap_or_else(|error| panic!("failed to load `{}`: {error}", path.display()));
    let c_sources = crate::cli::source_refs(&sources);

    let verified = verify_c0_sources(&click_source, &c_sources);
    verified.unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));

    let expanded =
        expand_c0_claim_source(&click_source, &c_sources, function, CProofClaim::Grouped)
            .unwrap_or_else(|error| panic!("failed to expand `{}`: {error:?}", path.display()));
    assert!(expanded.contains(retained_step), "{expanded}");
    // An added import can affect every declaration, so retain the full-file
    // output check whenever anything outside this proof changes.
    if !only_function_proof_changed(&click_source, &expanded, function) {
        verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
            panic!(
                "expanded proof from `{}` failed independent verification: {error:?}",
                path.display()
            )
        });
        return;
    }
    // The complete original project above checks every unchanged declaration.
    // Cold-check the complete rewritten function, including every claim/path,
    // rather than its untouched helpers again.
    let checked =
        crate::surface::verify_c0_sources_functions(&expanded, &c_sources, [function.to_string()])
            .unwrap_or_else(|error| {
                panic!(
                    "expanded proof from `{}` failed independent verification: {error:?}",
                    path.display()
                )
            });
    assert!(!checked.is_empty());
    assert!(
        checked
            .iter()
            .all(|proof| proof.function_block.signature().name() == function)
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn linked_list_pipeline_has_no_outcome_fallbacks() {
    let (project, sidecar, function, retained_step) = RESOURCE_EXAMPLE_PIPELINE_CASES[0];
    assert_resource_example_pipeline_has_no_outcome_fallbacks(
        project,
        sidecar,
        function,
        retained_step,
    );
}

#[test]
#[ignore = "nightly: 13s in the parallel gate"]
fn input_cursor_pipeline_has_no_outcome_fallbacks() {
    let (project, sidecar, function, retained_step) = RESOURCE_EXAMPLE_PIPELINE_CASES[1];
    assert_resource_example_pipeline_has_no_outcome_fallbacks(
        project,
        sidecar,
        function,
        retained_step,
    );
}

#[test]
#[ignore = "nightly: 10s in the parallel gate"]
fn owned_segmented_buffer_pipeline_has_no_outcome_fallbacks() {
    let (project, sidecar, function, retained_step) = RESOURCE_EXAMPLE_PIPELINE_CASES[2];
    assert_resource_example_pipeline_has_no_outcome_fallbacks(
        project,
        sidecar,
        function,
        retained_step,
    );
}

#[test]
#[ignore = "nightly: whole-pipeline expansion rechecks measured 12s"]
fn owned_string_pipeline_has_no_outcome_fallbacks() {
    let (project, sidecar, function, retained_step) = RESOURCE_EXAMPLE_PIPELINE_CASES[3];
    assert_resource_example_pipeline_has_no_outcome_fallbacks(
        project,
        sidecar,
        function,
        retained_step,
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn recursive_zero_list_pipeline_has_no_outcome_fallbacks() {
    let (project, sidecar, function, retained_step) = RESOURCE_EXAMPLE_PIPELINE_CASES[4];
    assert_resource_example_pipeline_has_no_outcome_fallbacks(
        project,
        sidecar,
        function,
        retained_step,
    );
}

#[test]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn vector_push_pipeline_has_no_outcome_fallbacks() {
    let (project, sidecar, function, retained_step) = RESOURCE_EXAMPLE_PIPELINE_CASES[5];
    assert_resource_example_pipeline_has_no_outcome_fallbacks(
        project,
        sidecar,
        function,
        retained_step,
    );
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn smart_have_expansion_plans_against_the_ordinary_surface_goal() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = manifest
        .join("examples")
        .join("ring-buffer")
        .join("ring_buffer.click");
    let project_source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    // The example no longer needs this intermediate have. Keep the
    // regression's ordinary surface goal explicit in its own test input.
    let anchor = "    have owner->tail == 4 by {";
    assert_eq!(project_source.matches(anchor).count(), 1);
    let explicit = project_source.replacen(
        anchor,
        "    have owner->head == old(owner->head) by {\n        normalize();\n    }\n    have owner->tail == 4 by {",
        1,
    );
    let smart = explicit.replacen(
        "have owner->head == old(owner->head) by {\n        normalize();\n    }",
        "have owner->head == old(owner->head) by {\n        simp();\n    }",
        1,
    );
    assert_ne!(
        smart, explicit,
        "the regression must select the intended have"
    );
    let sources = crate::cli::read_verifying_sources(&path, &smart)
        .unwrap_or_else(|error| panic!("failed to load `{}`: {error}", path.display()));
    let c_sources = crate::cli::source_refs(&sources);

    verify_c0_sources(&smart, &c_sources).expect("the smart have should verify");
    let expanded = expand_c0_claim_source(
        &smart,
        &c_sources,
        "ring_buffer_pipeline",
        CProofClaim::Grouped,
    )
    .expect("the smart have should expand against its ordinary lowered goal");
    assert!(
        expanded.contains("have owner->head == old(owner->head) by {\n        normalize();\n    }"),
        "the expansion used a different internal goal:\n{expanded}"
    );
    verify_c0_sources(&expanded, &c_sources)
        .expect("the expanded smart have should independently reverify");
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn negative_outcome_diagnostic_manifests_have_no_fallbacks() {
    let manifests = [
        (
            "pure/type",
            &[
                "c_multiplication.md",
                "c_nonzero_integer_rejected_as_pointer.md",
                "contract_let_type_mismatch.md",
                "max_bad_ensure.md",
                "grouped_post_tactics_respect_order.md",
            ][..],
        ),
        (
            "memory/mutation",
            &[
                "fill3_bad_memory_postcondition.md",
                "fill_tail_rejects_tail_segment_unchanged.md",
                "forall_array_segment_rejects_overwritten_cell.md",
                "loop_rejects_stale_address_escaped_local.md",
                "loop_rejects_stale_pre_loop_store.md",
                "pointer_params_may_alias_without_separate.md",
                "proof_branch_hides_arm_facts.md",
                "write_second_old_rejects_overwritten_cell.md",
            ][..],
        ),
        (
            "resource/call",
            &[
                "composite_resource_folded_nested_fact_projection.md",
                "composite_resource_nested_observe_not_automatic.md",
                "grouped_post_tactics_respect_order.md",
                "grouped_unfold_respects_order.md",
                "opaque_call_does_not_preserve_overlapping_field.md",
                "opaque_call_rejects_weak_postcondition.md",
                "permission_call_consumes_write_without_return.md",
                "resource_summary_requires_returned_write.md",
            ][..],
        ),
    ];
    let mdtests = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests");
    let mut checked = BTreeSet::new();
    for (class, filenames) in manifests {
        for filename in filenames {
            if !checked.insert(*filename) {
                continue;
            }
            let path = mdtests.join(filename);
            let source = std::fs::read_to_string(&path)
                .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
            let mdtest = crate::cli::parse_mdtest(&path, &source)
                .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
            let click_source = mdtest
                .click_source
                .as_deref()
                .unwrap_or_else(|| panic!("`{}` has no Click source", path.display()));
            let c_sources = mdtest
                .c_sources
                .iter()
                .map(|(name, source)| (name.as_str(), source.as_str()))
                .collect::<Vec<_>>();
            let crate::cli::MdTestExpectation::FailContains(expected) = mdtest
                .expectation
                .as_ref()
                .unwrap_or_else(|| panic!("`{}` has no expectation", path.display()))
            else {
                panic!("`{}` is not an expected failure", path.display());
            };

            let result = verify_c0_sources(click_source, &c_sources);
            let error = match result {
                Ok(_) => panic!("`{}` unexpectedly verified", path.display()),
                Err(error) => error,
            };
            assert!(
                error.message().contains(expected),
                "{class} fixture `{}` expected `{expected}`, got `{}`",
                path.display(),
                error.message()
            );
            assert!(
                error.message().len() < 16 * 1024,
                "{class} fixture `{}` produced an unbounded diagnostic ({} bytes)",
                path.display(),
                error.message().len()
            );
        }
    }
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn branch_continuation_claims_retain_their_selected_outcome_step() {
    for (filename, function, claim, _) in [
        (
            "proof_branch_continuation.md",
            "joined_increment",
            CProofClaim::Ensure(1),
            "joined_increment.ensures_1",
        ),
        (
            "proof_branch_interface_continuation.md",
            "advance_nested_join",
            CProofClaim::Ensure(0),
            "advance_nested_join.ensures_0",
        ),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(filename);
        let source = std::fs::read_to_string(&path)
            .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
        let mdtest = crate::cli::parse_mdtest(&path, &source)
            .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
        let click_source = mdtest
            .click_source
            .as_deref()
            .unwrap_or_else(|| panic!("`{}` has no Click source", path.display()));
        let c_sources = mdtest
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let verified = verify_c0_sources(click_source, &c_sources);
        verified.unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));
        if filename == "proof_branch_continuation.md" {
            let captured = crate::surface::proof::capture_c0_tactic_expansion(
                click_source,
                &c_sources,
                crate::surface::expansion::ProofSite::FunctionClaim {
                    function_name: function.to_string(),
                    claim: CProofClaim::Ensure(1),
                },
                0,
                &[],
            )
            .expect("the selected pre-branch step should have one stable expansion");
            assert!(
                matches!(captured.as_slice(), [ProofTactic::Step]),
                "the selected step absorbed a later structured branch: {captured:#?}"
            );
        }

        let retained_step = "apply(int32_increment_greater_than_lower_bound(";
        let expanded = expand_c0_claim_source(click_source, &c_sources, function, claim)
            .unwrap_or_else(|error| panic!("failed to expand `{}`: {error:?}", path.display()));
        assert!(expanded.contains(retained_step), "{expanded}");
        verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
            panic!(
                "expanded proof from `{}` failed independent verification: {error:?}",
                path.display()
            )
        });

        let without_retained_step = expanded
            .lines()
            .filter(|line| !line.contains(retained_step))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            verify_c0_sources(&without_retained_step, &c_sources).is_err(),
            "`{}` checked after deleting its selected retained theorem step",
            path.display()
        );
    }
}

#[test]
fn outcome_simp_transports_loadability_on_the_checked_proof() {
    let summarize_c = r#"
        int32 summarize(int32* p) {
            return 0;
        }
    "#;
    let use_c = r#"
        int32 use_summary(int32* p) {
            int32 result;
            result = summarize(p);
            return result;
        }
    "#;
    let click_source = r#"
        verifying "summarize.c";
        verifying "use_summary.c";

        int32 summarize(int32* p) {
            requires viewable(p[0..1]);
            ensures viewable(p[0..1]);
        } by {
            execute();
            simp();
        }

        int32 use_summary(int32* p) {
            requires viewable(p[0..1]);
            ensures viewable(p[0..1]);
        } by {
            execute();
            simp();
        }
    "#;
    let sources = [("summarize.c", summarize_c), ("use_summary.c", use_c)];

    let verified = verify_c0_sources(click_source, &sources);
    verified.expect("the call-preserved viewability should transport through Proof");

    let expanded =
        expand_c0_claim_source(click_source, &sources, "use_summary", CProofClaim::Grouped)
            .expect("the retained viewability transport should expand");
    assert!(expanded.contains("transport"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained viewability transport should check independently");
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn outcome_simp_retains_checked_unchanged_old_equality_on_the_proof() {
    let c_source = r#"
        int32 shifted_loop_effect_preserves_prefix(int32 p[], int32 n) {
            int32 i;
            i = 1;
            while (i < n) {
                p[i] = i;
                i = i + 1;
            }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "shifted.c";

        int32 shifted_loop_effect_preserves_prefix(int32 p[], int32 n) {
            requires n >= 1;
            requires n <= 2147483647;
            consumes p[0..n];
            ensures keeps_first: p[0] == old(p[0]);
            ensures returns_n: result == n;
        } by {
            step();
            step();
            loop {
                decreases n - i;
                owns (p + 1)[0..n - 1];
                invariant i >= 1;
                invariant i <= n;
            }
            step();
            simp();
        }
    "#;
    let sources = [("shifted.c", c_source)];

    let verified_for_expansion = verify_c0_sources(click_source, &sources)
        .expect("the unchanged old equality should advance Proof");

    let expanded = expand_checked_grouped_claim(
        click_source,
        &verified_for_expansion,
        "shifted_loop_effect_preserves_prefix",
    )
    .expect("the retained old equality should expand");
    assert!(
        expanded.contains("have p[0] == old(p[0]) by {\n                normalize();"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the retained old equality should check independently");
}

#[test]
fn outcome_simp_instantiates_an_unfolded_byte_predicate_on_the_checked_proof() {
    let c_source = r#"
        int32 byte_prefix(uint8 p[], int32 n) {
            return 0;
        }
    "#;
    let click_source = r#"import click::bytes;

        verifying "byte_prefix.c";

        int32 byte_prefix(uint8 p[], int32 n) {
            requires viewable(p[0..3]);
            requires bytes::all_not_equal(p, 0, 3, 'y');
            ensures p[1] != 'y' by {
                execute();
                unfold(bytes::all_not_equal);
                simp();
            }
        }
    "#;
    let sources = [("byte_prefix.c", c_source)];

    let verified = verify_c0_sources(click_source, &sources);
    verified.expect("the unfolded byte universal should instantiate through Proof");

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "byte_prefix",
        CProofClaim::Ensure(0),
    )
    .expect("the retained universal specialization should expand");
    assert!(expanded.contains("instantiate("), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the unfolded universal specialization should check independently");
}

#[test]
#[ignore = "nightly: 1.3s in the parallel gate"]
fn outcome_simp_materializes_selected_composite_separation_on_the_checked_proof() {
    let c_source = r#"
        struct owner {
            int32 len;
            int32 cap;
            int32* data;
        };

        int32 observe_nested_separate_contains(struct owner* owner) {
            return 0;
        }
    "#;
    let click_source = r#"
        resource backing_buffer(owner: struct owner*) {
            owns owner->data[0..owner->cap];
        }

        resource nested_owned_buffer(owner: struct owner*) {
            owns owner->len;
            owns owner->cap;
            owns owner->data;
            owns backing_buffer(owner);
            fact 0 <= owner->len;
            fact owner->len <= owner->cap;
        }

        verifying "observe.c";

        int32 observe_nested_separate_contains(struct owner* owner) {
            consumes nested_owned_buffer(owner);
            ensures separate(
                memory(*owner),
                memory(owner->data[0..owner->cap])
            ) by {
                observe(nested_owned_buffer(owner));
                observe(backing_buffer(owner));
                execute();
                simp();
            }
        }
    "#;
    let sources = [("observe.c", c_source)];

    let verified = verify_c0_sources(click_source, &sources);
    verified
        .expect("the observed composition should certify its selected separation through Proof");

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "observe_nested_separate_contains",
        CProofClaim::Ensure(0),
    )
    .expect("the retained resource separation should expand");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the selected resource separation should check independently");
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn quantified_old_transport_substitutes_its_introduced_binder_on_the_checked_proof() {
    let c_source = r#"
        int32 shifted_copy(int32 dst[], int32 src[], int32 n) {
            int32 i;
            i = 1;
            while (i < n) {
                dst[i] = src[i];
                i = i + 1;
            }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "shifted_copy.c";

        int32 shifted_copy(int32 dst[], int32 src[], int32 n) {
            requires n >= 1;
            requires n <= 2147483647;
            consumes dst[0..n];
            views src[0..n];
            requires separate(memory(dst[0..n]), memory(src[0..n]));
            ensures forall (k: int32) {
                0 <= k and k < n implies src[k] == old(src[k])
            };
            ensures result == n;
        } by {
            step();
            step();
            loop {
                decreases n - i;
                invariant i >= 1;
                invariant i <= n;
            }
            step();
            have forall (k: int32) {
                0 <= k and k < n implies src[k] == old(src[k])
            } by {
                intro();
                intro();
                simp();
            }
            simp();
        }
    "#;
    let sources = [("shifted_copy.c", c_source)];

    let verified = verify_c0_sources(click_source, &sources);
    verified.expect("the quantified old equality should transport through Proof");

    let expanded =
        expand_c0_claim_source(click_source, &sources, "shifted_copy", CProofClaim::Grouped)
            .expect("the retained quantified transport should expand");
    // The goal's own entry snapshot would carry the whole quantified fact
    // in one frame (`quantified_old_transport_expands_to_one_quantified_frame`),
    // so the proof introduces the binder and its guard itself: the
    // expansion must then name the introduced `k`.
    assert!(expanded.contains("intro();"), "{expanded}");
    assert!(
        expanded.contains(
            "transport(at(function.entry, src[k] == old(src[k])), src[k] == old(src[k])) using {"
        ),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the quantified old transport should check independently");
}

#[test]
fn guarded_definedness_transport_expands_and_reverifies() {
    let (source, sources) =
        mdtest_sources("mdtests/guarded_definedness_survives_a_disjoint_store.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source_by_label(&source, &sources, "fill_t.contract").unwrap();
    assert!(expanded.contains("transport("), "{expanded}");
    assert!(expanded.contains("defined("), "{expanded}");
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn quantified_old_transport_expands_to_one_quantified_frame() {
    let c_source = r#"
        int32 shifted_copy(int32 dst[], int32 src[], int32 n) {
            int32 i;
            i = 1;
            while (i < n) {
                dst[i] = src[i];
                i = i + 1;
            }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "shifted_copy.c";

        int32 shifted_copy(int32 dst[], int32 src[], int32 n) {
            requires n >= 1;
            requires n <= 2147483647;
            consumes dst[0..n];
            views src[0..n];
            requires separate(memory(dst[0..n]), memory(src[0..n]));
            ensures forall (k: int32) {
                0 <= k and k < n implies src[k] == old(src[k])
            };
            ensures result == n;
        } by {
            step();
            step();
            loop {
                decreases n - i;
                invariant i >= 1;
                invariant i <= n;
            }
            step();
            simp();
        }
    "#;
    let sources = [("shifted_copy.c", c_source)];

    let verified = verify_c0_sources(click_source, &sources);
    verified.expect("the quantified old equality should transport through Proof");

    let expanded =
        expand_c0_claim_source(click_source, &sources, "shifted_copy", CProofClaim::Grouped)
            .expect("the retained quantified transport should expand");
    // The entry snapshot of the goal is a reflexive fact, and the quantified
    // frame carries it across the loop's checked write set in one step.
    assert!(
        expanded.contains("transport(at(function.entry, forall (k: int32) { 0 <= k and k < n implies src[k] == old(src[k]) }), forall (k: int32) { 0 <= k and k < n implies src[k] == old(src[k]) })"),
        "{expanded}"
    );
    assert!(!expanded.contains("extract(0 <= k);"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the quantified old transport should check independently");
}

#[test]
fn source_expander_lowers_smart_simp_after_unfold_inside_have() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            predicate reflexive(x: int32) {
                x == x
            }

            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            } by {
                have reflexive(x) by {
                    unfold(reflexive);
                    simp();
                }
                execute();
                simp();
            }
        "#;
    let (verified, flat_units) = proof::count_flat_proof_units(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("the unfold-then-simp have should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");

    let have_offset = click_source
        .find("have reflexive(x)")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("the selected unfolded smart have should expand");
    let expanded_have = &expanded[expanded
        .find("have reflexive(x)")
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("execute()")
            .expect("expanded proof should retain its suffix")];
    assert!(
        expanded_have.contains("unfold(reflexive);"),
        "{expanded_have}"
    );
    assert!(expanded_have.contains("normalize();"), "{expanded_have}");
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the expanded unfolded smart have should check");
}

#[test]
fn source_expander_extracts_unfolded_conjuncts_inside_have() {
    let c_source = r#"
            int32 identity(int32 x, int32 y, int32 z) {
                return x;
            }
        "#;
    let click_source = r#"
            predicate equality_chain(x: int32, y: int32, z: int32) {
                x == y and y == z
            }

            verifying "identity.c";

            int32 identity(int32 x, int32 y, int32 z) {
                requires equality_chain(x, y, z);
                ensures result == x;
            } by {
                have x == z by {
                    unfold(equality_chain);
                    simp() using {
                        x == y;
                        y == z;
                    }
                }
                execute();
                simp();
            }
        "#;
    let offset = click_source.find("have x == z").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("restricted simp should extract its unfolded conjunct premises");
    assert!(expanded.contains("extract(x == y);"), "{expanded}");
    assert!(expanded.contains("extract(y == z);"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("expanded fixed-state proof conjunction extraction should check");
}

#[test]
fn source_expander_preserves_pointer_field_form_inside_smart_have() {
    let c_source = r#"
            struct holder {
                int32* data;
            };

            int32 holder_zero(struct holder* owner, int32 data[]) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "holder.c";

            resource holder_storage(p: struct holder*) {
                owns *p;
            }

            int32 holder_zero(struct holder* owner, int32 data[]) {
                requires owner->data == data;
                views holder_storage(owner);
                ensures result == 0;
            } by {
                have owner->data == data by simp();
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have owner->data == data")
        .expect("proof should contain the selected pointer have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("holder.c", c_source)], line, column)
            .expect("the pointer-valued smart have should expand");
    assert!(
        expanded.contains("have owner->data == data by {"),
        "{expanded}"
    );
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &[("holder.c", c_source)])
        .expect("the expanded pointer-valued have should check");
}

#[test]
fn source_expander_synthesizes_an_indexed_load_through_a_pointer_field() {
    let c_source = r#"
            struct holder {
                int32* data;
            };

            int32 holder_read(struct holder* owner, int32 data[], int32 value) {
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "holder.c";

            resource holder_storage(p: struct holder*) {
                owns *p;
            }

            predicate second_is(owner: struct holder*, value: int32) {
                owner->data[1] == value
            }

            int32 holder_read(
                struct holder* owner,
                int32 data[],
                int32 value
            ) {
                requires owner->data == data;
                requires separate(memory(*owner), memory(data[1..2]));
                requires second_is(owner, value);
                views holder_storage(owner);
                views data[1..2];
                ensures result == 0;
            } by {
                unfold(second_is);
                have data[1] == value by simp();
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have data[1] == value")
        .expect("proof should contain the selected indexed have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("holder.c", c_source)], line, column)
            .expect("the indexed pointer-field fact should have a surface form");
    assert!(expanded.contains("owner->data[1] == value"), "{expanded}");
    verify_c0_sources(&expanded, &[("holder.c", c_source)])
        .expect("the indexed pointer-field expansion should check");
}

#[test]
fn smart_have_uses_transport_planned_at_the_mutation_boundary() {
    let c_source = r#"
            int32 set_second_return_first(int32 p[2]) {
                p[1] = 9;
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "transport.c";

            predicate first_is_seven(p: int32[]) {
                p[0] == 7
            }

            int32 set_second_return_first(int32 p[2]) {
                requires first_is_seven(p);
                owns p[0..2];
            } by {
                unfold(first_is_seven);
                step();
                have p[0] == 7 by simp();
                step();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have p[0] == 7")
        .expect("proof should contain the selected have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("transport.c", c_source)], line, column)
            .expect("the transported current-state fact should expand as an assumption");
    let expanded_have = &expanded[expanded
        .find("have p[0] == 7")
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("step();\n                simp();")
            .expect("expanded proof should retain its suffix")];
    assert!(expanded_have.contains("assumption();"), "{expanded_have}");
    assert!(!expanded_have.contains("transport("), "{expanded_have}");
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("transport.c", c_source)])
        .expect("the expansion should check using the transport planned by the prior statement");
}

#[test]
fn source_expander_recalls_a_fact_at_a_recorded_statement_entry() {
    let preserve_c_source = r#"
            int32 preserve(int32 p[1]) {
                return p[0];
            }
        "#;
    let pipeline_c_source = r#"
            int32 pipeline(int32 p[1]) {
                int32 ignored;
                ignored = preserve(p);
                return p[0];
            }
        "#;
    let click_source = r#"
            verifying "preserve.c";
            verifying "snapshot.c";

            resource one(p: int32*) {
                owns p[0..1];
                fact p[0] == 1;
            }

            int32 preserve(int32 p[1]) {
                views one(p);
                ensures result == 1;
            } by {
                observe(one(p));
                execute();
                simp();
            }

            int32 pipeline(int32 p[1]) {
                views one(p);
                ensures result == 1;
            } by {
                observe(one(p));
                execute_until(statement(2));
                have at(statement(1).entry, p[0]) == 1 by simp();
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have at(statement(1).entry")
        .expect("proof should contain the selected snapshot have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let c_sources = [
        ("preserve.c", preserve_c_source),
        ("snapshot.c", pipeline_c_source),
    ];
    let expanded = expand_c0_tactic_source_at(click_source, &c_sources, line, column)
        .expect("the snapshot have should expand");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources).expect("the expanded snapshot have should check");
}

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn source_expander_derives_separation_from_call_postconditions() {
    let init_c_source = r#"
            struct cursor {
                int32 pos;
                int32 len;
                int32* data;
            };

            int32 init(struct cursor* owner, int32 data[], int32 length) {
                owner->pos = 0;
                owner->len = length;
                owner->data = data;
                return 0;
            }
        "#;
    let pipeline_c_source = r#"
            struct cursor {
                int32 pos;
                int32 len;
                int32* data;
            };

            int32 pipeline(
                struct cursor* left,
                struct cursor* right,
                int32 data[],
                int32 length
            ) {
                int32 ignored;
                ignored = init(left, data, length);
                return 0;
            }
        "#;
    let click_source = r#"
            verifying "init.c";
            verifying "pipeline.c";

            int32 init(
                struct cursor* owner,
                int32 data[],
                int32 length
            ) {
                requires 0 <= length;
                requires ((uint32)length) <= 1073741823u32;
                requires separate(memory(*owner), memory(data[0..length]));
                owns *owner;
                views data[0..length];
                ensures result == 0;
                ensures owner->pos == 0;
                ensures owner->len == length;
                ensures owner->data == data;
            } by {
                execute();
                simp();
            }

            int32 pipeline(
                struct cursor* left,
                struct cursor* right,
                int32 data[],
                int32 length
            ) {
                requires 1 <= length;
                requires ((uint32)length) <= 1073741823u32;
                requires separate(memory(*left), memory(data[0..length]));
                requires separate(memory(*right), memory(data[0..length]));
                owns *left;
                owns *right;
                views data[0..length];
                ensures result == 0;
            } by {
                execute_until(statement(2));
                have separate(
                    memory(*right),
                    memory(left->data[0..left->len])
                ) by {
                    simp();
                }
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have separate(")
        .expect("proof should contain the selected separation have");
    let line = click_source[..have_offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = have_offset
        - click_source[..have_offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;
    let c_sources = [("init.c", init_c_source), ("pipeline.c", pipeline_c_source)];

    verify_c0_sources(click_source, &c_sources)
        .expect("bounded call ranges should verify before expansion");
    let expanded = expand_c0_tactic_source_at(click_source, &c_sources, line, column)
        .expect("call postconditions should expand into an explicit separation derivation");
    // The call postconditions are written against the snapshots where they were read:
    // anchored rewrites, not unanchored equalities that would re-read the
    // fields in the proof's current state.
    assert!(
        expanded.contains(
            "rewrite(at(statement(2).entry, left->len) == at(statement(2).entry, length));"
        ),
        "{expanded}"
    );
    assert!(
        expanded.contains(
            "rewrite(at(statement(2).entry, left->data) == at(statement(2).entry, data));"
        ),
        "{expanded}"
    );
    assert!(!expanded.contains("load_int32_pointer"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources)
        .expect("the expanded separation derivation should check");
}

#[test]
fn branched_smart_simp_expansion_checks_as_surface_click() {
    let c_source = r#"
            int32 choose(int32 flag) {
                if (flag) {
                    return 1;
                } else {
                    return 2;
                }
            }
        "#;
    let click_source = r#"
            verifying "choose.c";

            int32 choose(int32 flag) {
                ensures result == 1 or result == 2 by { execute(); simp(); }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("choose.c", c_source)])
        .expect("branched smart simp should verify");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("branched smart simp should lower to surface tactics");
    let expanded_source = click_source.replacen("by { execute(); simp(); }", &expanded, 1);
    verify_c0_sources(&expanded_source, &[("choose.c", c_source)])
        .expect("printed branched smart simp expansion should check");
}

#[test]
fn source_expander_replaces_only_the_selected_claim_proof() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures first: result == x by { execute(); simp(); }
                ensures second: result == x + 0 by { execute(); simp(); }
            }
        "#;

    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Ensure(1),
    )
    .expect("selected smart proof should expand");
    assert_eq!(expanded.matches("by { execute(); simp(); }").count(), 1);
    assert!(expanded.contains("ensures first: result == x by { execute(); simp(); }"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "source-expanded sidecar should re-verify: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn source_expander_replaces_and_checks_grouped_proof() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures first: result == x;
                ensures second: result == x + 0;
            } by {
                execute();
                simp();
            }
        "#;

    let expanded = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
    )
    .expect("grouped proof should expand");
    assert!(!expanded.contains("execute();"));
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("expanded grouped proof should re-verify");
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn qualified_static_ownership_verifies_and_expands() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/qualified_static_ownership.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion = verify_c0_sources(source, &sources).unwrap();
    for (_, expanded) in expand_checked_grouped_claims(
        source,
        &verified_for_expansion,
        ["reset", "read_cache", "main"],
    ) {
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{error:?}\n{expanded}"));
    }
    let wrong = source.replace("result == 12", "result == 7");
    assert!(verify_c0_sources(&wrong, &sources).is_err());
}

#[test]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn qualified_function_statics_verify_and_expand() {
    for (fixture_name, functions) in [
        (
            "qualified_function_static_ownership.md",
            vec!["increment", "other", "twice", "main"],
        ),
        ("qualified_function_static_shapes.md", vec!["clear", "main"]),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests")
            .join(fixture_name);
        let fixture = crate::cli::read_mdtest(&path).unwrap();
        let source = fixture.click_source.as_deref().unwrap();
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let verified_for_expansion = verify_c0_sources(source, &sources).unwrap();
        for (_, expanded) in expand_checked_grouped_claims(
            source,
            &verified_for_expansion,
            functions.iter().copied(),
        ) {
            verify_c0_sources(&expanded, &sources)
                .unwrap_or_else(|error| panic!("{fixture_name}: {}\n{expanded}", error.message()));
        }
    }
}

#[test]
fn qualified_function_statics_reject_invalid_declarations() {
    let c_source =
        "void f(int parameter) { static int stored; int automatic = 0; stored = automatic; }";
    for name in [
        "f::parameter",
        "f::automatic",
        "f::missing",
        "missing::stored",
        "f",
        "f::stored::extra",
    ] {
        let source = format!(
            "verifying \"storage.c\" as storage; void f(int parameter) {{ owns storage::{name}[0..1]; }}"
        );
        assert!(
            verify_c0_sources(&source, &[("storage.c", c_source)]).is_err(),
            "accepted {name}"
        );
    }
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn qualified_function_statics_do_not_grant_ownership() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/qualified_function_static_ownership.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let original = "uint32 twice() {\n    owns counter_file::increment::calls;";
    assert!(source.contains(original));
    for replacement in [
        "uint32 twice() {",
        "uint32 twice() { views counter_file::increment::calls;",
        "uint32 twice() { owns counter_file::other::calls;",
        "uint32 twice() { owns counter_file::calls;",
    ] {
        let invalid = source.replace(original, replacement);
        let error = verify_c0_sources(&invalid, &sources)
            .expect_err("caller must transfer the exact owned object");
        assert!(
            error.message().contains("missing resource"),
            "{}",
            error.message()
        );
    }
    let invalid = source.replace("increment::calls == 7u32", "increment::calls == 6u32");
    assert!(
        verify_c0_sources(&invalid, &sources).is_err(),
        "a repeated call must not reset the static initializer"
    );
}

#[test]
fn qualified_static_ownership_rejects_missing_and_wrong_resources() {
    let sources = [
        (
            "left.c",
            "static int count = 7; void write_zero(int *p) { *p = 0; } void clear(void) { write_zero(&count); }",
        ),
        ("right.c", "static int count = 19;"),
        (
            "main.c",
            "void clear(void); int main(void) { clear(); return 0; }",
        ),
    ];
    let source = r#"
verifying "left.c" as left;
verifying "right.c" as right;
verifying "main.c";
void write_zero(int *p) {
    owns p[0..1];
    ensures p[0] == 0;
} by { execute(); simp(); }
void clear() {
    owns left::count;
    ensures left::count == 0;
} by { execute(); simp(); }
int main() { ensures result == 0; } by { execute(); simp(); }
"#;
    verify_c0_sources(source, &sources).unwrap();
    for invalid in [
        source.replace("owns left::count;", ""),
        source.replace("owns left::count", "owns right::count"),
        source.replace("owns left::count", "owns missing::count"),
        source.replace("owns left::count", "owns left::missing"),
        source.replace("as right", "as left"),
        source.replace("owns left::count;", "owns left::count[0..2];"),
    ] {
        assert!(
            verify_c0_sources(&invalid, &sources).is_err(),
            "accepted {invalid}"
        );
    }
}

#[test]
fn qualified_static_direct_assignment_requires_effect_or_ownership() {
    let sources = [(
        "left.c",
        "static int count = 7; void clear(void) { count = 0; }",
    )];
    let unqualified = r#"verifying "left.c";
void clear() { ensures count == 0; } by { execute(); simp(); }"#;
    let error = verify_c0_sources(unqualified, &sources)
        .expect_err("a direct static write needs an effect or owned resource");
    assert!(error.message().contains("outside the mutable footprint"));
    let qualified = unqualified
        .replace("\"left.c\";", "\"left.c\" as left;")
        .replace("ensures count", "ensures left::count");
    let error = verify_c0_sources(&qualified, &sources)
        .expect_err("qualification must not grant an implicit effect");
    assert!(error.message().contains("outside the mutable footprint"));
}

#[test]
fn qualified_static_helper_requires_transferred_ownership() {
    let sources = [(
        "counter.c",
        "static int count = 7; void write_zero(int *p) { *p = 0; } void clear(void) { write_zero(&count); }",
    )];
    let source = r#"verifying "counter.c" as counter;
void write_zero(int *p) {
    owns p[0..1];
    ensures p[0] == 0;
} by { execute(); simp(); }
void clear() {
    owns counter::count;
    ensures counter::count == 0;
} by { execute(); simp(); }"#;
    verify_c0_sources(source, &sources).unwrap();
    let missing = source.replace("owns counter::count;", "");
    assert!(
        verify_c0_sources(&missing, &sources).is_err(),
        "a helper call cannot manufacture ownership"
    );
}

#[test]
#[ignore = "nightly: 1.2s in the parallel gate"]
fn qualified_static_struct_startup_and_expansion() {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/qualified_static_struct.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let file = super::super::verification::parse_c0_click_file(source, &sources).unwrap();
    let map = sources.iter().copied().collect();
    let parsed = super::super::verification::parse_verified_sources(&file, &map).unwrap();
    let state = parsed["main"].1.program_entry_state.as_ref().unwrap();
    assert_eq!(
        state
            .memory()
            .load(&CMemory::global_pointer("state#file-static:counter.c")),
        CExpressionOutcome::Value(CValue::UInt64(Bitvector32Term::UInt64Constant(7)))
    );
    let verified_for_expansion = verify_c0_sources(source, &sources).unwrap();
    for (_, expanded) in expand_checked_grouped_claims(
        source,
        &verified_for_expansion,
        ["read_value", "current", "main"],
    ) {
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{error:?}\n{expanded}"));
    }

    // A valid helper contract that changes the cell must not let the caller
    // fold its old invariant merely because its source spelling is unchanged.
    let changed_counter = sources[0].1.replace(
        "return p->value;",
        "unsigned long old_value = p->value; p->value = 9; return old_value;",
    );
    let changed_sources = [(sources[0].0, changed_counter.as_str()), sources[1]];
    let changed_proof = source.replace(
        "ensures p->value == old(p->value);",
        "ensures p->value == 9u64;",
    );
    let error = verify_c0_sources(&changed_proof, &changed_sources)
        .expect_err("fold must establish the current 64-bit invariant");
    assert!(
        error.message().contains("fold(counter_state())"),
        "{error:?}"
    );
}

fn check_private_state_expansion(fixture_name: &str, name: &str) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join(fixture_name);
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &sources).unwrap();
    let expanded = expand_c0_claim_source(source, &sources, name, CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("{name}: {error:?}\n{expanded}"));
}

#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn private_state_bump_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "bump");
}
#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn private_state_reset_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "reset");
}
#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn private_state_left_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "left");
}
#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn private_state_right_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "right");
}
#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn private_state_reset_left_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "reset_left");
}
#[test]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn private_state_main_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "main");
}
#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn private_state_wide_return_expands() {
    check_private_state_expansion("private_state_wide_return.md", "main");
}
#[test]
fn private_state_narrowing_call_expands() {
    check_private_state_expansion("private_state_narrowing_call.md", "main");
}
#[test]
fn wide_signed_low_word_narrowing_expands() {
    check_private_state_expansion("wide_values_narrow_to_their_low_word.md", "signed_value");
}
#[test]
fn wide_unsigned_low_word_narrowing_expands() {
    check_private_state_expansion("wide_values_narrow_to_their_low_word.md", "unsigned_value");
}

#[test]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn private_state_wrappers_reject_invalid_ownership_and_effects() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/private_state_mutation_reset.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &sources).unwrap();
    for (old, new) in [
        ("owns left_file::state.value;", ""),
        (
            "owns left_file::state.value;",
            "owns right_file::state.value;",
        ),
        (
            "owns left_file::state.value;",
            "owns left_file::state.value; owns left_file::state.value;",
        ),
        (
            "ensures left_file::state.value == old(left_file::state.value) + 1u64;",
            "ensures left_file::state.value == old(left_file::state.value);",
        ),
        (
            "ensures right_file::state.value == 41u64;",
            "ensures right_file::state.value == 40u64;",
        ),
        ("ensures result == 1;", "ensures result == 2;"),
    ] {
        let invalid = source.replacen(old, new, 1);
        assert_ne!(invalid, source);
        assert!(
            verify_c0_sources(&invalid, &sources).is_err(),
            "incorrect change accepted: {old} -> {new}"
        );
    }
}

#[test]
fn wide_values_narrow_to_their_low_word_without_bounds() {
    let fixture_name = "wide_values_narrow_to_their_low_word.md";
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests")
        .join(fixture_name);
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &sources).unwrap();
    for claim in [
        "ensures result == 0;",
        "ensures result == (uint32)value + 1u32;",
    ] {
        assert!(
            verify_c0_sources(
                &source.replacen("ensures result == (uint32)value;", claim, 1),
                &sources
            )
            .is_err(),
            "wrong low word accepted: {claim}"
        );
    }
}

#[test]
#[ignore = "nightly: 1.8s in the parallel gate"]
fn grouped_residual_normalization_expansion_checks_original_claims() {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/qualified_static_struct.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let repeated_rewrite = source.replace(
        "rewrite(result == old(counter::state.value));",
        "rewrite(result == old(counter::state.value));\n    rewrite(old(counter::state.value) == 7u64);",
    );
    assert_ne!(repeated_rewrite, source);
    for source in [source, repeated_rewrite.as_str()] {
        verify_c0_sources(source, &sources).unwrap();
        let expanded =
            expand_c0_claim_source(source, &sources, "current", CProofClaim::Grouped).unwrap();
        assert!(expanded.contains("    normalize();"));
        assert!(expanded.contains("    assumption();"));
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{error:?}\n{expanded}"));
        for proof in [source, expanded.as_str()] {
            assert!(
                verify_c0_sources(
                    &proof.replace("ensures result == 7u64;", "ensures result == 8u64;"),
                    &sources
                )
                .is_err()
            );
        }
    }
}

#[test]
fn source_expander_replaces_and_checks_default_ensure_proof() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            }
        "#;

    let expanded_once = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Ensure(0),
    )
    .expect("default proof should expand");
    let expanded_twice = expand_c0_claim_source(
        &expanded_once,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Ensure(0),
    )
    .expect("explicit expansion should expand again");

    assert!(expanded_once.contains("ensures result == x by {"));
    assert_eq!(expanded_once, expanded_twice);
    verify_c0_sources(&expanded_once, &[("identity.c", c_source)])
        .expect("expanded default ensure should re-verify");
}

#[test]
fn source_expander_reports_missing_grouped_proof_precisely() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x;
            }
        "#;

    let error = expand_c0_claim_source(
        click_source,
        &[("identity.c", c_source)],
        "identity",
        CProofClaim::Grouped,
    )
    .expect_err("independent claims do not have a grouped proof");

    assert!(
        error
            .message()
            .contains("grouped verification but has no source `by` clause")
    );
}

#[test]
fn pure_pointer_add_zero_simp_expands_to_a_checked_certificate() {
    let click_source = r#"
            theorem pointer_add_zero_equals(
                base: int32*,
                offset: int32,
                target: int32*
            ) {
                requires base == target;
                requires offset == 0;

                ensures base + offset == target by {
                    simp();
                }
            }
        "#;
    let offset = click_source.find("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("the pointer-offset identity simp should have an explicit certificate");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded pointer identity proof should check");
}

#[test]
fn pure_branching_disjunction_simp_expands_to_left_right() {
    let click_source = r#"
            theorem int32_sign_split(x: int32) {
                ensures x <= 0 or x > 0 by {
                    if x <= 0 {
                        simp();
                    } else {
                        simp();
                    }
                }
            }
        "#;
    let offset = click_source.find("if x <= 0").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("the branching disjunction proof should have an explicit certificate");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded branching disjunction proof should check");
}

#[test]
fn pure_folded_constant_successor_simp_expands_to_successor_bound() {
    let click_source = r#"
            theorem successor_of_zero_below_bound(x: int32, bound: int32) {
                requires x == 0;
                requires 2 <= bound;

                ensures x + 1 < bound by {
                    simp();
                }
            }
        "#;
    let offset = click_source.find("simp()").unwrap();
    let line = click_source[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset
        - click_source[..offset]
            .rfind('\n')
            .map(|offset| offset + 1)
            .unwrap_or(0)
        + 1;

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("the folded constant successor simp should have an explicit certificate");
    assert!(expanded.contains("rewrite(x == 0);"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_increment_less_equal_implies_less_than("),
        "{expanded}"
    );
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded constant successor proof should check");
}

#[test]
fn unfolded_conjunction_have_simp_expands_to_both_scopes() {
    let c_source = r#"
            struct pair {
                int32 low;
                int32 high;
            };

            void set_pair(struct pair* pair, int32 bound) {
                pair->low = 0;
                pair->high = bound;
            }
        "#;
    let click_source = r#"
            predicate ordered_pair(pair: struct pair*) {
                0 <= pair->low and pair->low <= pair->high
            }

            verifying "set_pair.c";

            void set_pair(struct pair* pair, int32 bound) {
                requires 0 <= bound;
                owns *pair;

                ensures ordered_pair(pair);
            } by {
                execute();
                have ordered_pair(pair) by {
                    unfold(ordered_pair);
                    simp();
                }
                simp();
            }
        "#;
    let verified = verify_c0_sources(click_source, &[("set_pair.c", c_source)]);
    verified.expect("the unfolded conjunction should verify on the checked Proof path");
    let offset = click_source.find("have ordered_pair").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("set_pair.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the unfolded conjunction have simp should expand to exact child scopes");
    assert!(expanded.contains("both {"), "{expanded}");
    assert!(expanded.contains("} and {"), "{expanded}");
    assert!(!expanded.contains("have 0 <= pair->low"), "{expanded}");
    assert!(
        !expanded.contains("have pair->low <= pair->high"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &[("set_pair.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the expanded split certificate should check: {}\n{expanded}",
            error.message()
        )
    });
}

#[test]
fn outcome_predecessor_bound_simp_expands_to_the_named_rule() {
    let c_source = r#"
            struct pair {
                int32 low;
                int32 high;
            };

            void drop_one(struct pair* pair) {
                pair->low = pair->low - 1;
            }
        "#;
    let click_source = r#"
            predicate ordered_pair(pair: struct pair*) {
                0 <= pair->low and pair->low <= pair->high
            }

            verifying "drop_one.c";

            void drop_one(struct pair* pair) {
                requires ordered_pair(pair);
                requires pair->low == 1;
                owns *pair;

                ensures ordered_pair(pair);
            } by {
                unfold(ordered_pair);
                execute();
                assumption();
                simp();
            }
        "#;
    let offset = click_source.rfind("simp()").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("drop_one.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the predecessor bound simp should expand to the named rule");
    assert!(expanded.contains("both {"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_nonnegative_predecessor_upper_bound("),
        "{expanded}"
    );
    assert!(!expanded.contains("simp()"), "{expanded}");
    verify_c0_sources(&expanded, &[("drop_one.c", c_source)]).unwrap_or_else(|error| {
        panic!(
            "the expanded predecessor bound certificate should check: {}\n{expanded}",
            error.message()
        )
    });
}

/// A statement transition sees the complete proof context while checking its
/// frame.
/// `borrowed_slice_buffer_pipeline` carries `data[start] == replacement`
/// across the `return` call's `*owner` effect: the frame check locates
/// `data + start` inside the composite buffer's owned range through the
/// contract bounds without encoding them in the emitted statement step.
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn expanded_step_uses_the_whole_context_for_frame_evidence() {
    let click_source = include_str!("../../../examples/borrowed-slice/borrowed_slice.click");
    let c_sources = [
        (
            "buffer_init.c",
            include_str!("../../../examples/borrowed-slice/buffer_init.c"),
        ),
        (
            "buffer_borrow.c",
            include_str!("../../../examples/borrowed-slice/buffer_borrow.c"),
        ),
        (
            "slice_set.c",
            include_str!("../../../examples/borrowed-slice/slice_set.c"),
        ),
        (
            "buffer_return.c",
            include_str!("../../../examples/borrowed-slice/buffer_return.c"),
        ),
        (
            "buffer_get.c",
            include_str!("../../../examples/borrowed-slice/buffer_get.c"),
        ),
        (
            "buffer_pipeline.c",
            include_str!("../../../examples/borrowed-slice/buffer_pipeline.c"),
        ),
    ];
    let expanded = expand_c0_claim_source_by_label(
        click_source,
        &c_sources,
        "borrowed_slice_buffer_pipeline.contract",
    )
    .expect("the pipeline proof should expand");
    // Every statement runs in the whole context: the return call's slice
    // fact and bounds are visible to it without being listed.
    let pipeline = expanded
        .split("borrowed_slice_buffer_pipeline(")
        .nth(1)
        .expect("the expanded source should retain the pipeline");
    assert!(pipeline.contains("step();"), "{pipeline}");
    verify_c0_sources(&expanded, &c_sources).expect("the expanded pipeline proof should check");
}

#[test]
fn loop_preservation_case_after_step_expands_in_place() {
    let c_source = r#"
        int32 count_once(int32 flag) {
            int32 i;
            i = 0;
            while (i < 1) { i = i + 1; }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "count_once.c";
        int32 count_once(int32 flag) {
            ensures result == 1;
        } by {
            step();
            step();
            loop {
                decreases 1 - i;
                invariant i >= 0;
                invariant i <= 1;
                initialize by simp();
                preserve by {
                    step();
                    if flag == i {
                        have flag == i by { assumption(); }
                    } else {
                        have not (flag == i) by { assumption(); }
                    }
                    close_invariants();
                }
            }
            step();
            simp();
        }
    "#;
    let sources = [("count_once.c", c_source)];
    let verified_for_expansion = verify_c0_sources(click_source, &sources)
        .expect("the preservation case after a step verifies");
    let expanded =
        expand_checked_grouped_claim(click_source, &verified_for_expansion, "count_once")
            .expect("the loop proof expands");
    let preserve = expanded
        .find("preserve by")
        .expect("the expansion keeps the preservation proof");
    let body = &expanded[preserve..];
    let step = body.find("step();").expect("the body step is retained");
    let case = body
        .find("if flag == i")
        .expect("the proof case is retained");
    assert!(
        step < case,
        "the case must stay after the step it follows: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("expanded proof failed independent verification: {error:?}\n{expanded}")
    });
}

#[test]
fn loop_preservation_case_before_step_expands_in_place() {
    let c_source = r#"
        int32 count_once(int32 flag) {
            int32 i;
            i = 0;
            while (i < 1) { i = i + 1; }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "count_once.c";
        int32 count_once(int32 flag) {
            ensures result == 1;
        } by {
            step();
            step();
            loop {
                decreases 1 - i;
                invariant i >= 0;
                invariant i <= 1;
                initialize by simp();
                preserve by {
                    if flag == i {
                        have flag == i by { assumption(); }
                    } else {
                        have not (flag == i) by { assumption(); }
                    }
                    step();
                    close_invariants();
                }
            }
            step();
            simp();
        }
    "#;
    let sources = [("count_once.c", c_source)];
    let verified_for_expansion = verify_c0_sources(click_source, &sources)
        .expect("the preservation case before a step verifies");
    let expanded =
        expand_checked_grouped_claim(click_source, &verified_for_expansion, "count_once")
            .expect("the loop proof expands");
    let preserve = expanded
        .find("preserve by")
        .expect("the expansion keeps the preservation proof");
    let body = &expanded[preserve..];
    let case = body
        .find("if flag == i")
        .expect("the proof case is retained");
    let step = body.find("step();").expect("the body step is retained");
    assert!(
        case < step,
        "the case must stay before the step it precedes: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("expanded proof failed independent verification: {error:?}\n{expanded}")
    });
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn loop_preservation_if_retains_its_enclosing_match_binding() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/loop_preserve_if_reads_match_binding.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("the regression should contain Click source");
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();

    let verified_for_expansion = verify_c0_sources(click_source, &c_sources)
        .expect("the preservation `if` should read its enclosing match binding");
    let expanded = expand_checked_grouped_claim(click_source, &verified_for_expansion, "count_to")
        .expect("the loop proof should expand");
    let preserve = expanded
        .find("preserve by")
        .expect("the expansion should retain the preservation phase");
    let body = &expanded[preserve..];
    assert!(
        body.contains("match m.model") && body.contains("if i < end"),
        "the generated certificate must keep `end` inside its match arm: {expanded}"
    );
    verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
        panic!("expanded proof failed independent verification: {error:?}\n{expanded}")
    });
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn loop_entry_logical_read_expands_without_hidden_introductions() {
    let c_source = r#"
        int32 fill3_entry_guard(int32 p[3]) {
            int32 i;
            i = 0;
            while (i < 3) {
                p[i] = i;
                i = i + 1;
            }
            return p[2];
        }
    "#;
    let click_source = r#"
        verifying "fill3_entry_guard.c";
        int32 fill3_entry_guard(int32 p[3]) {
            consumes p[0..3];
            ensures returns_third: result == 2;
        } by {
            step();
            step();
            loop {
                decreases 3 - i;
                invariant i >= 0 and i <= 3;
                invariant forall (k: int32) { 0 <= k and k < i implies p[k] == k };
                initialize by simp();
                preserve by simp();
            }
            step();
            simp();
        }
    "#;
    let sources = [("fill3_entry_guard.c", c_source)];
    let verified_for_expansion = verify_c0_sources(click_source, &sources)
        .expect("the entry-guard loop proof should verify");
    let expanded =
        expand_checked_grouped_claim(click_source, &verified_for_expansion, "fill3_entry_guard")
            .expect("the entry-guard loop proof should expand");
    let initialize = expanded
        .find("initialize by")
        .expect("the expansion keeps the initialization proof");
    let preserve = expanded
        .find("preserve by")
        .expect("the expansion keeps the preservation proof");
    assert!(initialize < preserve, "{expanded}");
    assert!(
        !expanded[initialize..preserve].contains("intro();"),
        "the initialization certificate must not invent a read guard: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("expanded entry-guard proof failed independent verification: {error:?}\n{expanded}")
    });
}

/// A specification `if` whose condition holds only under an ambient fact.
///
/// Lowering does not consult that fact: it folds a literally constant
/// condition and otherwise lowers both branches, so the checked goal still
/// carries the conditional. The branch is therefore chosen by a proof step,
/// and expansion prints that step together with the exact ambient premise it
/// cites. Dropping the citation must invalidate the proof, which is what
/// makes the choice explicit rather than rediscovered.
#[test]
fn specification_conditional_branch_is_an_expanded_proof_step() {
    let click_source = r#"verifying "select_when_positive.c";

int32 select_when_positive(int32 limit, int32 left, int32 right) {
    requires limit > 0;
    ensures result == (if limit > 0 { left } else { right });
} by { execute(); simp(); }
"#;
    let sources = [(
        "select_when_positive.c",
        "int32 select_when_positive(int32 limit, int32 left, int32 right) {\n    return left;\n}\n",
    )];
    verify_c0_sources(click_source, &sources).expect("smart conditional proof should verify");
    let offset = click_source.find("simp();").expect("expected smart tactic");
    let position = expansion::position_at_offset(click_source, offset);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column).unwrap();
    assert!(
        expanded.contains("have result == (if limit > 0 { left } else { right }) by"),
        "lowering decided the branch instead of keeping the conditional: {expanded}"
    );
    assert!(
        expanded.contains("limit > 0;"),
        "the expansion must cite the ambient fact the branch choice rests on: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("expanded conditional proof failed independent verification: {error:?}\n{expanded}")
    });
    let uncited = expanded.replacen(
        "normalize() using {\n        limit > 0;\n    }",
        "normalize();",
        1,
    );
    assert_ne!(uncited, expanded, "{expanded}");
    verify_c0_sources(&uncited, &sources)
        .expect_err("dropping the cited premise must leave the branch unresolved");
    let wrong_branch = click_source.replace(
        "if limit > 0 { left } else { right }",
        "if limit > 0 { right } else { left }",
    );
    assert_ne!(wrong_branch, click_source);
    verify_c0_sources(&wrong_branch, &sources)
        .expect_err("the arm the ambient fact selects is checked, not assumed");
}

#[test]
fn integer_quantifiers_substitute_checked_mixed_atoms_and_expand() {
    let source = r#"
function combine(n: Nat, z: Integer) -> Integer { to_integer(n) + z }
theorem mixed_integer_atoms(x: int32, n: Nat) {
    ensures function_atom: forall (z: Integer) { combine(n, z) + 1 > combine(n, z) } by { simp(); }
    ensures machine_atom: forall (z: Integer) { z + to_integer(x) == to_integer(x) + z } by { simp(); }
    ensures mixed_clause: forall (z: Integer) { x == x and combine(n, z) == combine(n, z) } by { simp(); }
    ensures witnessed: exists (z: Integer) { z == to_integer(x) } by {
        witness { z: to_integer(x) };
        normalize();
    }
}
"#;
    verify_c0_sources(source, &[]).expect("mixed Integer atoms should verify");
    for label in ["function_atom", "machine_atom", "mixed_clause", "witnessed"] {
        let expanded =
            expand_c0_claim_source_by_label(source, &[], &format!("mixed_integer_atoms.{label}"))
                .expect("mixed Integer atom should expand");
        verify_c0_sources(&expanded, &[])
            .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
    }
    for invalid in [
        "function f(z: Integer) -> Integer { z } theorem bad() { ensures forall(z: Integer) { f(z) == 0 } by { simp(); } }",
        "theorem bad(x: int32) { ensures exists(z: Integer) { z == to_integer(x + 1) } by { witness { z: to_integer(x + 1) }; simp(); } }",
        "theorem bad(x: int32) { ensures forall(z: Integer) { to_integer(x + 1) == to_integer(x + 1) } by { simp(); } }",
    ] {
        assert!(
            verify_c0_sources(invalid, &[]).is_err(),
            "invalid quantified domain or opaque equality verified: {invalid}"
        );
    }
}

/// The source shape behind `arena_region_length` in `examples/arena`: the
/// function returns inside an `open(...)` body and the scope's closer runs
/// after that return.
const OPEN_SCOPE_RETURN_C: &str = r#"
struct span {
    int32 start;
    int32 end;
};

int32 span_length(struct span* span) {
    return span->end - span->start;
}
"#;

const OPEN_SCOPE_RETURN_CLICK: &str = r#"import click::machine_integer;

resource span_bounds(span: struct span*) {
    owns *span;
}

verifying "span.c";

int32 span_length(struct span* span) {
    requires 0 <= span->start;
    requires span->start <= span->end;
    views span_bounds(span);

    ensures result == span->end - span->start;
} by {
    open(span_bounds(span)) {
        have defined(span->end - span->start) by {
            apply(int32_nonnegative_subtract_within_value_is_defined(
                span->end,
                span->start
            )) using {
                0 <= span->start;
                span->start <= span->end;
            }
        }
        step();
        simp();
    }
}
"#;

#[test]
fn smart_closer_after_a_return_inside_an_open_scope_expands_and_reverifies() {
    // Reduced from `arena_region_length` in `examples/arena`, which `click
    // verify` accepted while `click audit` reported `the kernel lowering
    // produced 0 paths` for the expanded proof. The closer's certificate
    // names `result`, which only a function outcome binds; a `have` written
    // after the return inside the scope has to reach that outcome the same
    // way the scope's other post-exit operations do.
    let sources = [("span.c", OPEN_SCOPE_RETURN_C)];
    verify_c0_sources(OPEN_SCOPE_RETURN_CLICK, &sources)
        .expect("the open-scope return proof should verify");

    let closer = OPEN_SCOPE_RETURN_CLICK
        .rfind("simp();")
        .expect("proof should contain the scope's closer");
    let position = expansion::position_at_offset(OPEN_SCOPE_RETURN_CLICK, closer);
    let expanded = expand_c0_tactic_source_at(
        OPEN_SCOPE_RETURN_CLICK,
        &sources,
        position.line,
        position.column,
    )
    .expect("the scope's post-return closer should expand");
    assert!(
        expanded.contains("have result =="),
        "the expansion should state the outcome `have` it checked: {expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded post-return closer should independently reverify");
}

/// `object_retain_many` from `examples/refcount`, whose proof folds the
/// produced references inside an `open(...)` body and closes the produced
/// resource claim with a grouped `simp`.
const PRODUCED_RESOURCE_C: &str = r#"
struct object {
    int32 refs;
};

void object_retain_many(struct object* obj, int32 amount) {
    obj->refs = obj->refs + amount;
}
"#;

const PRODUCED_RESOURCE_CLICK: &str = r#"
authorized resource reference(obj: struct object*) {}

resource control(obj: struct object*) {
    owns allocation(obj, sizeof(struct object));
    owns *obj;
    owns authority(reference(obj));
    fact obj->refs == count(reference(obj));
}

verifying "object_retain_many.c";

void object_retain_many(struct object* obj, int32 amount) {
    requires 0 <= amount;
    requires defined(obj->refs + amount);
    owns control(obj);
    produces amount of reference(obj);
    ensures defined(obj->refs);
} by {
    open(control(obj)) {
        step();
        fold(amount of reference(obj));
    }
    execute();
    simp();
}
"#;

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn grouped_closer_with_a_produced_resource_claim_expands_and_reverifies() {
    // Reduced from `pool_transfer` in `examples/bounded-pool` and
    // `object_retain_many` in `examples/refcount`. The closer's certificate
    // spells a produced resource claim's closure `assumption`, which reads
    // the outcome through the contract's checked resource transition exactly
    // as the `simp` it replaces does. Without that reading the expansion
    // failed with `assumption did not match any current proposition goal`.
    let sources = [("object_retain_many.c", PRODUCED_RESOURCE_C)];
    verify_c0_sources(PRODUCED_RESOURCE_CLICK, &sources)
        .expect("the produced-resource proof should verify");

    let closer = PRODUCED_RESOURCE_CLICK
        .rfind("simp();")
        .expect("proof should contain the grouped closer");
    let position = expansion::position_at_offset(PRODUCED_RESOURCE_CLICK, closer);
    let expanded = expand_c0_tactic_source_at(
        PRODUCED_RESOURCE_CLICK,
        &sources,
        position.line,
        position.column,
    )
    .expect("the grouped closer should expand");
    assert!(
        expanded.contains("assumption();"),
        "the closer's claim closures should be retained: {expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded grouped closer should independently reverify");
}

/// The two-constructor analogue of `mdtests/proof_match_three_constructors.md`:
/// each arm refolds its instance and closes the contract with `simp()`.
const MATCH_ARM_OLD_MODEL_C: &str = "int read(int* p) { return *p; }";

const MATCH_ARM_OLD_MODEL_CLICK: &str = r#"
verifying "read.c";

spec enum Bi { Zero, Other(int) }

function bi_code(t: Bi) -> int {
    match t {
        Bi::Zero => 0,
        Bi::Other(value) => value,
    }
}

resource cell(p: int*) {
    field model: Bi;
    match model {
        Bi::Zero => { owns p[0..1]; fact p[0] == 0; },
        Bi::Other(value) => { owns p[0..1]; fact p[0] == value; },
    }
}

int read(int* p) {
    owns c: cell(p);
    ensures c.model == old(c.model);
    ensures result == bi_code(old(c.model));
} by {
    match c.model {
        Bi::Zero => {
            unfold(c);
            execute();
            let c = fold(cell(p), { model: Bi::Zero }, {});
            have bi_code(old(c.model)) == 0 by {
                rewrite(old(c.model) == Bi::Zero);
                unfold(bi_code(Bi::Zero));
                normalize();
            }
            simp();
        },
        Bi::Other(value) => {
            unfold(c);
            execute();
            let c = fold(cell(p), { model: Bi::Other(value) }, {});
            have bi_code(old(c.model)) == value by {
                rewrite(old(c.model) == Bi::Other(value));
                unfold(bi_code(Bi::Other(value)));
                normalize();
            }
            simp();
        },
    }
}
"#;

#[test]
fn match_arm_closer_anchors_the_case_fact_at_entry_and_reverifies() {
    // The arm's case fact is a statement about the scrutinee at unchanged
    // function entry, but its recorded spelling was the unanchored
    // `c.model == Bi::Other(value)`. After the arm refolds the instance that
    // spelling denotes the fold's own equation instead, so the generated
    // `have c.model == old(c.model)` cited the wrong fact and its `normalize`
    // left `Bi::Other(value) = <entry model>` open in the rewritten source.
    let sources = [("read.c", MATCH_ARM_OLD_MODEL_C)];
    verify_c0_sources(MATCH_ARM_OLD_MODEL_CLICK, &sources)
        .expect("the two-constructor match proof should verify");

    let closer = MATCH_ARM_OLD_MODEL_CLICK
        .rfind("simp();")
        .expect("proof should contain the second arm's closer");
    let position = expansion::position_at_offset(MATCH_ARM_OLD_MODEL_CLICK, closer);
    let expanded = expand_c0_tactic_source_at(
        MATCH_ARM_OLD_MODEL_CLICK,
        &sources,
        position.line,
        position.column,
    )
    .expect("the arm's closer should expand");
    assert!(
        expanded.contains("rewrite(old(c.model) == Bi::Other(value));"),
        "the generated closer should cite the entry-anchored case fact: {expanded}"
    );
    assert!(
        !expanded.contains("rewrite(c.model == Bi::Other(value));"),
        "the written spelling now denotes the fold's own equation, so a \
         certificate must not cite it for the case fact: {expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded match-arm closer should independently reverify");
}

/// The shape of `sequence_contains3` in `examples/sequence-transform`: four
/// returns, so the grouped closer has four execution paths under one surface
/// leaf skeleton.
const FOUR_RETURN_C: &str = r#"
int contains3(int values[3], int target) {
    if (values[0] == target) {
        return 1;
    }
    if (values[1] == target) {
        return 1;
    }
    if (values[2] == target) {
        return 1;
    }
    return 0;
}
"#;

const FOUR_RETURN_CLICK: &str = r#"
verifying "contains3.c";

int32 contains3(int32 values[], int32 target) {
    views values[0..3];

    ensures result != 0 implies target in old([values[0], values[1], values[2]]);
    ensures target in old([values[0], values[1], values[2]]) implies result != 0;
} by {
    execute();
    simp();
}
"#;

#[test]
#[ignore = "nightly: 2.7s in the parallel gate"]
fn grouped_leaf_implications_preserve_constant_false_premises() {
    let (source, sources) = mdtest_sources("mdtests/leaf_flag_grouped_simp.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion = verify_c0_sources(&source, &sources).unwrap();
    let expanded =
        expand_checked_grouped_claim(&source, &verified_for_expansion, "leaf_flag").unwrap();
    without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
}

#[test]
#[ignore = "nightly: 0.56s after reducing duplicate verification"]
fn grouped_closer_over_four_paths_places_each_leafs_own_expansion() {
    // Every path but the first reported no surface branch path, because the
    // retained branch decisions were consumed innermost-first while the
    // surface skeleton is walked outermost-first. Each of those paths was
    // then stitched onto every leaf, and the one path needing a different
    // closer conflicted with the leaves the others had already filled.
    let sources = [("contains3.c", FOUR_RETURN_C)];
    let closer = FOUR_RETURN_CLICK
        .rfind("simp();")
        .expect("proof should contain the grouped closer");
    let position = expansion::position_at_offset(FOUR_RETURN_CLICK, closer);
    let expanded =
        expand_c0_tactic_source_at(FOUR_RETURN_CLICK, &sources, position.line, position.column)
            .expect("the four-path closer should expand");
    // Cold verification checks every leaf's own certificate. Constant
    // false premises can close the falling-through leaf directly, so a
    // particular number of transport steps is not part of this guarantee.
    verify_c0_sources(&expanded, &sources)
        .expect("the expanded four-path closer should independently reverify");
}

/// A composite resource whose body binds an existential witness. The witness
/// has no declared source name, but the checked return value can name it.
const WITNESS_RESOURCE_C: &str = r#"
struct node {
    int32 value;
    unsigned long word;
};

struct node* unpack(struct node* node) {
    return (struct node*)(node->word & ~1);
}
"#;

const WITNESS_RESOURCE_CLICK: &str = r#"
resource packed(node: struct node*) {
    owns *node;
    let next: struct node* where aligned(next, 8) and node->word == address(next) + (node->word & 1);
}

verifying "unpack.c";

struct node* unpack(struct node* node) {
    requires node != 0;
    owns packed(node);
    ensures address(result) == (node->word & ~1);
} by {
    unfold(packed(node));
    execute();
    fold(packed(node));
    assumption();
    arithmetic() using {
        aligned(result, 8);
        node->word == address(result) + (node->word & 1);
    };
}
"#;

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn expansion_names_a_resource_witness_through_the_checked_return_pointer() {
    let sources = [("unpack.c", WITNESS_RESOURCE_C)];
    verify_c0_sources(WITNESS_RESOURCE_CLICK, &sources)
        .expect("the witness fold/unfold proof should verify");

    let closer = WITNESS_RESOURCE_CLICK
        .rfind("arithmetic() using {")
        .expect("proof should contain the closer");
    let position = expansion::position_at_offset(WITNESS_RESOURCE_CLICK, closer);
    let expanded = expand_c0_tactic_source_at(
        WITNESS_RESOURCE_CLICK,
        &sources,
        position.line,
        position.column,
    )
    .expect("the checked return pointer should name the witness");
    assert!(!expanded.contains('…'), "{expanded}");
    verify_c0_sources(&expanded, &sources).expect("the named expansion must independently verify");
    let changed_pointer = expanded.replace("address(result)", "address(node)");
    assert_ne!(changed_pointer, expanded);
    verify_c0_sources(&changed_pointer, &sources)
        .expect_err("a different pointer cannot establish the witness premises");
}

#[test]
fn omitted_preservation_over_two_sibling_c_ifs_expands_and_reverifies() {
    // The automatic preservation the `loop` keyword owns walks this body
    // once: each of the two sibling C `if`s has both arms fall through to
    // more of the body, so its arms are joined as a `branch` and the rest is
    // not walked once per arm. It used to split each `if` into its own proof
    // case and walk four paths, which is what first exposed the
    // certificate-offset bug this test was written for; the expansion is now
    // two `branch` steps and must still reverify on its own.
    let c_source = r#"
        int32 two_ifs(int32 n) {
            int32 i = 0;
            int32 x = 0;
            int32 y = 0;

            while (i < n) {
                if (x == 0) {
                    x = 1;
                }
                if (y == 0) {
                    y = 1;
                }
                i = i + 1;
            }
            return i;
        }
    "#;
    let click_source = r#"
        verifying "two_ifs.c";

        int32 two_ifs(int32 n) {
            requires n >= 0;
            ensures result >= 0;
        } by {
            step();
            step();
            step();
            step();
            step();
            step();
            loop {
                decreases n - i;
                invariant i >= 0;
            }
            step();
            simp();
        }
    "#;
    let sources = [("two_ifs.c", c_source)];
    verify_c0_sources(click_source, &sources)
        .expect("an omitted-phase preservation over two sibling `if`s should verify");

    let loop_offset = click_source
        .find("loop {")
        .expect("the proof should contain the loop tactic");
    let position = expansion::position_at_offset(click_source, loop_offset);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the automatic preservation should expand");
    assert_eq!(
        expanded.matches("branch ").count(),
        2,
        "both sibling C `if`s should expand to joined branches: {expanded}"
    );
    assert!(
        !expanded.contains("if x == 0") && !expanded.contains("if y == 0"),
        "neither `if` should be walked as separate proof cases: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("the expanded preservation should independently reverify: {error:?}\n{expanded}")
    });
}

const LOOP_INITIALIZE_PHASE_C: &str = r#"int spin(int n) {
    int i;
    i = 0;
    while (i < n) {
        i = i + 1;
    }
    return i;
}
"#;

const LOOP_INITIALIZE_SMART_HAVE_CLICK: &str = r#"
verifying "spin.c";

int spin(int n) {
    requires n >= 0;
    ensures n >= 0;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;

        initialize by {
            have i >= 0 by simp();
            have i <= n by simp();
            assumption();
        }
        preserve by simp();
    }
    step();
    simp();
}
"#;

const LOOP_INITIALIZE_HELPER_HAVE_CLICK: &str = r#"
verifying "spin.c";

int spin(int n) {
    requires n >= 0;
    ensures n >= 0;
} by {
    step();
    step();
    loop {
        decreases n - i;
        invariant i >= 0;
        invariant i <= n;

        initialize by {
            have n + 0 == n by { normalize(); }
            simp();
        }
        preserve by {
            step();
            close_invariants();
        }
    }
    step();
    simp();
}
"#;

#[test]
fn each_smart_have_in_a_loop_initialize_script_expands_on_its_own() {
    // Reduced from the insert fixup loop in `examples/rbtree/rbtree-model`. The
    // per-invariant entry planner was handed the whole phase script as every
    // invariant's proof, so the second `have` had no expansion at all and
    // audit reported `Grouped proof has no source tactic 4` for a sidecar
    // `click verify` accepted.
    let sources = [("spin.c", LOOP_INITIALIZE_PHASE_C)];
    verify_c0_sources(LOOP_INITIALIZE_SMART_HAVE_CLICK, &sources)
        .expect("the initialize script should verify");

    for have in ["have i >= 0 by simp();", "have i <= n by simp();"] {
        let offset = LOOP_INITIALIZE_SMART_HAVE_CLICK
            .find(have)
            .unwrap_or_else(|| panic!("the proof should contain `{have}`"));
        let position = expansion::position_at_offset(LOOP_INITIALIZE_SMART_HAVE_CLICK, offset);
        let expanded = expand_c0_tactic_source_at(
            LOOP_INITIALIZE_SMART_HAVE_CLICK,
            &sources,
            position.line,
            position.column,
        )
        .unwrap_or_else(|error| panic!("`{have}` should expand: {error:?}"));
        assert!(
            !expanded.contains(have),
            "`{have}` should be replaced by its checked body: {expanded}"
        );
        verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
            panic!("the expanded initialize script should reverify: {error:?}\n{expanded}")
        });
    }
}

#[test]
fn a_smart_loop_preserve_phase_tactic_expands_and_reverifies() {
    // `preserve by simp();` is one smart tactic standing for the whole phase,
    // like `initialize by simp();`. Every driver step under it is generated, so
    // none claimed the source occurrence and audit reported
    // `Grouped proof has no source tactic 4`.
    let sources = [("spin.c", LOOP_INITIALIZE_PHASE_C)];
    for phase in ["preserve by simp();", "preserve by { simp(); }"] {
        let source = LOOP_INITIALIZE_SMART_HAVE_CLICK.replace("preserve by simp();", phase);
        let offset = source.find(phase).expect("the proof contains the phase");
        let position = expansion::position_at_offset(&source, offset + phase.find("simp").unwrap());
        let expanded =
            expand_c0_tactic_source_at(&source, &sources, position.line, position.column)
                .expect("a smart `preserve` phase should expand");
        assert!(
            !expanded.contains(phase),
            "the smart preserve phase should be replaced by its certificate: {expanded}"
        );
        verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
            panic!("the expanded preserve phase should reverify: {error:?}\n{expanded}")
        });
    }
}

#[test]
fn a_helper_have_in_a_loop_initialize_script_is_expanded_once() {
    // The entry planner nested every sibling step inside every invariant's
    // proof, so expanding the closing `simp()` printed the helper once per
    // invariant and the rewrite failed round-trip validation.
    let sources = [("spin.c", LOOP_INITIALIZE_PHASE_C)];
    verify_c0_sources(LOOP_INITIALIZE_HELPER_HAVE_CLICK, &sources)
        .expect("the helper initialize script should verify");

    let offset = LOOP_INITIALIZE_HELPER_HAVE_CLICK
        .find("            simp();")
        .expect("the proof should contain the phase closer");
    let position = expansion::position_at_offset(LOOP_INITIALIZE_HELPER_HAVE_CLICK, offset + 12);
    let expanded = expand_c0_tactic_source_at(
        LOOP_INITIALIZE_HELPER_HAVE_CLICK,
        &sources,
        position.line,
        position.column,
    )
    .expect("the initialize closer should expand");
    assert_eq!(
        expanded.matches("have n + 0 == n").count(),
        1,
        "the helper `have` should be kept once, where it was written: {expanded}"
    );
    assert!(
        expanded.contains("have i >= 0 by") && expanded.contains("have i <= n by"),
        "the closer should expand to one `have` per invariant: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("the expanded initialize closer should reverify: {error:?}\n{expanded}")
    });
}

#[test]
fn loop_initialization_duplicate_clauses_keep_distinct_bodies() {
    let click_source = LOOP_INITIALIZE_HELPER_HAVE_CLICK
        .replace("invariant i <= n;", "invariant i >= 0;")
        .replace(
            "            simp();",
            r#"            have i >= 0 by { arithmetic() using { n >= 0; } }
            have i >= 0 by { normalize(); }"#,
        );
    let sources = [("spin.c", LOOP_INITIALIZE_PHASE_C)];
    verify_c0_sources(&click_source, &sources).expect("mixed entry bodies should verify");
    let invalid_second = click_source.replace(
        "have i >= 0 by { normalize(); }",
        "have i >= 0 by { apply(missing_entry_theorem()); }",
    );
    let error = verify_c0_sources(&invalid_second, &sources)
        .expect_err("the second declaration's body must be checked independently");
    assert!(
        error.message().contains("missing_entry_theorem"),
        "{error:?}"
    );

    let expanded = expand_c0_claim_source(&click_source, &sources, "spin", CProofClaim::Grouped)
        .expect("entry proof should expand");
    verify_c0_sources(&expanded, &sources).expect("expanded entry proof should verify");
    assert_eq!(
        expanded.matches("have (n + 0) == n").count(),
        1,
        "{expanded}"
    );
    let initialize = expanded
        .split("initialize by")
        .nth(1)
        .unwrap()
        .split("preserve by")
        .next()
        .unwrap();
    assert_eq!(initialize.matches("have i >= 0").count(), 2, "{expanded}");
    assert!(!initialize.contains("arithmetic() using"), "{expanded}");
    let expanded_again = expand_c0_claim_source(&expanded, &sources, "spin", CProofClaim::Grouped)
        .expect("explicit entry proof should remain checkable on a second expansion");
    assert_eq!(expanded_again, expanded);
}

#[test]
fn a_consumed_arm_instance_equation_is_cited_at_entry_after_its_unfold() {
    // A proof `match` arm's constructor equation is recorded under its
    // written spelling, `t.model == Tree::Node(..)`. Once the arm has
    // unfolded the consumed `t` and folded the produced instance under
    // another name, that spelling lowers to nothing, and a certificate that
    // cited it failed its recheck with `the kernel lowering hit Paths`. The
    // entry-anchored `old(t.model) == Tree::Node(..)` is what the expansion
    // must print.
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/consumed_arm_equation_expands_at_entry.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("the fixture has a click block");
    let sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let offset = click_source
        .rfind("simp();")
        .expect("the arm closes with a smart simp");
    let position = expansion::position_at_offset(click_source, offset);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("the closing simp should expand");
    // Shared model closure can now close this equality by assumption. If
    // a rewrite is emitted, it must still use the readable entry snapshot.
    assert!(!expanded.contains("rewrite(t.model =="), "{expanded}");
    assert!(
        expanded.contains("assumption();")
            || expanded.contains("rewrite(old(t.model) == Tree::Node(id, color, left_model));"),
        "the model equality needs checked closure: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("the expanded closing simp should reverify: {error:?}\n{expanded}")
    });
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn local_job_views_expand_and_reverify_without_ownership_annotations() {
    let path =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("mdtests/stable_view_local_job.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let mut click = fixture.click_source.unwrap();
    verify_c0_sources(&click, &sources).expect("local job must verify before expansion");
    for function in ["read_local_job", "relay_local_job", "use_local_job"] {
        click = expand_c0_claim_source(&click, &sources, function, CProofClaim::Grouped)
            .expect("local loan and lifetime certificates should expand");
    }
    assert!(!click.contains("execute();"), "{click}");
    assert!(!click.contains("simp();"), "{click}");
    verify_c0_sources(&click, &sources).expect("expanded local job must independently reverify");
}

#[test]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn an_unfold_bound_scalar_field_expands_and_reverifies() {
    // `let { prefix: p } = unfold(before)` names the folded field value that
    // the scan loop's invariant and measure, the post-loop facts, and the
    // refold read after the instance is consumed. The whole claim expands to
    // explicit steps that keep the binding pattern and verify on their own.
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/resource_unfold_binds_scalar_field.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("the fixture has a click block");
    let sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source_by_label(click_source, &sources, "claim.contract")
        .expect("the claim should expand");
    assert!(
        expanded.contains("let { prefix: p } = unfold(before);"),
        "the expansion should keep the field binding: {expanded}"
    );
    assert!(
        !expanded.contains("simp();") && !expanded.contains("close_invariants();"),
        "every smart site should be replaced: {expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("the expansion should reverify: {error:?}\n{expanded}"));
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn a_decided_branch_in_a_loop_body_expands_and_reverifies() {
    // The certificate records the decided C branch as a logical `if` with an
    // empty infeasible arm. The preservation driver must read that expanded
    // `if` as the checked execution split, or the continuation runs on the
    // refuted arm and the expanded claim does not verify.
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/loop_preserve_decided_branch_expands.md");
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("the fixture has a click block");
    let sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded =
        expand_c0_claim_source_by_label(click_source, &sources, "count_zero_run.contract")
            .expect("the claim should expand");
    assert!(
        !expanded.contains("branch "),
        "the decided branch should be printed as its checked split: {expanded}"
    );
    assert!(
        !expanded.contains("simp();") && !expanded.contains("close_invariants();"),
        "every smart site should be replaced: {expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("the expansion should reverify: {error:?}\n{expanded}"));
}

/// Expands every smart site of one claim in an iterated-ownership fixture and
/// reverifies the result, checking that the explicit `take`/`give` steps
/// survive expansion as written.
fn expand_iterated_ownership_claim(fixture: &str, claim: &str, kept: &[&str]) {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(fixture);
    let source = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = crate::cli::parse_mdtest(&path, &source)
        .unwrap_or_else(|error| panic!("failed to parse `{}`: {error}", path.display()));
    let click_source = mdtest
        .click_source
        .as_deref()
        .expect("the fixture has a click block");
    let sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source_by_label(click_source, &sources, claim)
        .unwrap_or_else(|error| panic!("`{claim}` should expand: {error:?}"));
    for step in kept {
        assert!(
            expanded.contains(step),
            "the expansion should keep `{step}` as written: {expanded}"
        );
    }
    assert!(
        !expanded.contains("simp();") && !expanded.contains("close_invariants();"),
        "every smart site should be replaced: {expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("the expansion should reverify: {error:?}\n{expanded}"));
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn the_iterated_ownership_allocation_protocol_expands_and_reverifies() {
    // `take` is a simple step: the expansion prints it unchanged, and the
    // closers around it become explicit steps that verify on their own.
    expand_iterated_ownership_claim(
        "mdtests/iterated_ownership_allocate_one.md",
        "claim.contract",
        &["take(data[index..(index + 1)]);"],
    );
}

#[test]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn the_iterated_ownership_claim_loop_expands_and_reverifies() {
    // The loop takes one element per iteration from the iterated fact inside
    // its window; the expanded preservation proof still takes it explicitly.
    expand_iterated_ownership_claim(
        "mdtests/iterated_ownership_claim_loop.md",
        "claim_run.contract",
        &["take(data[i..(i + 1)]);"],
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn the_iterated_ownership_release_loop_expands_and_reverifies() {
    expand_iterated_ownership_claim(
        "mdtests/iterated_ownership_release_loop.md",
        "release_run.contract",
        &["give(data[i..(i + 1)]);"],
    );
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn conditional_call_witness_expansion_keeps_empty_binder_map() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/conditional_call_existential_historical_read.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let mdtest = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(mdtest.click_source.as_deref().unwrap(), &sources)
        .expect("the original witness proof verifies");
    let expanded = expand_c0_claim_source(
        mdtest.click_source.as_deref().unwrap(),
        &sources,
        "parent",
        CProofClaim::Grouped,
    )
    .expect("the let-bound call must remain parseable");
    assert!(
        expanded.contains("let { result: r } = step(child(a, b, n, a[i]), {});"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources).expect("the expanded witness proof certifies");
}

#[test]
fn conditional_algebraic_universal_expands_and_reverifies() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/conditional_algebraic_universal_contract.md");
    let source = std::fs::read_to_string(&path).unwrap();
    let mdtest = crate::cli::parse_mdtest(&path, &source).unwrap();
    let sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let original = mdtest.click_source.as_deref().unwrap();
    verify_c0_sources(original, &sources).expect("conditional universal verifies");
    let expanded = expand_c0_claim_source(original, &sources, "report", CProofClaim::Grouped)
        .expect("quantifier braces must remain inside the have proposition");
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    let expanded_again =
        expand_c0_claim_source(&expanded, &sources, "report", CProofClaim::Grouped)
            .expect("printed quantified haves retain their source mapping");
    verify_c0_sources(&expanded_again, &sources).expect("reexpanded universal certifies");
}

#[test]
fn normalize_using_ambient_pointer_equality_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/normalize_using_ambient_pointer_equality.md");
    let text = std::fs::read_to_string(&path).expect("read ambient equality fixture");
    let fixture = crate::cli::parse_mdtest(&path, &text).expect("parse ambient equality fixture");
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let source = fixture.click_source.as_deref().expect("Click source");
    verify_c0_sources(source, &c_sources).expect("ambient graph should close normalization");
    let position = expansion::position_at_offset(source, source.find("normalize() using").unwrap());
    let expanded = expand_c0_tactic_source_at(source, &c_sources, position.line, position.column)
        .expect("ambient equality should expand");
    assert!(expanded.contains("normalize() using"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources).expect("expanded equality should recheck");
    let missing = expanded.replace("b == c implies", "b == b implies");
    assert!(
        verify_c0_sources(&missing, &c_sources).is_err(),
        "expanded query must still depend on its ambient equality premises"
    );
}

#[test]
fn normalize_using_c_pointer_equality_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/normalize_using_c_pointer_equality.md");
    let text = std::fs::read_to_string(&path).expect("read C pointer equality fixture");
    let fixture = crate::cli::parse_mdtest(&path, &text).expect("parse C pointer equality fixture");
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let source = fixture.click_source.as_deref().expect("Click source");
    verify_c0_sources(source, &c_sources).expect("C pointer transitivity should verify");
    let expanded = expand_c0_claim_source(source, &c_sources, "keep", CProofClaim::Ensure(0))
        .expect("C pointer transitivity should expand");
    assert!(expanded.contains("normalize() using"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources).expect("expanded C pointer equality should recheck");
    for missing in ["requires a == b;", "requires b == c;"] {
        assert!(verify_c0_sources(&expanded.replace(missing, ""), &c_sources).is_err());
    }
    let reversed = source.replace("ensures a == c;", "ensures c == a;");
    verify_c0_sources(&reversed, &c_sources).expect("symmetric transitivity should verify");
    let derived = source.replace("using { }", "using { a == c; }");
    verify_c0_sources(&derived, &c_sources).expect("a cited pointer congruence is known");
    let unavailable = source.replace("using { }", "using { a != c; }");
    assert!(verify_c0_sources(&unavailable, &c_sources).is_err());
    let false_goal = source.replace("ensures a == c;", "ensures a != c;");
    assert!(verify_c0_sources(&false_goal, &c_sources).is_err());
}

#[test]
fn normalize_using_pointer_addition_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/normalize_using_pointer_addition.md");
    let text = std::fs::read_to_string(&path).expect("read pointer addition fixture");
    let fixture = crate::cli::parse_mdtest(&path, &text).expect("parse pointer addition fixture");
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let source = fixture.click_source.as_deref().expect("Click source");
    verify_c0_sources(source, &c_sources).expect("pointer addition congruence should verify");
    let expanded = expand_c0_claim_source(source, &c_sources, "keep", CProofClaim::Ensure(0))
        .expect("pointer addition congruence should expand");
    assert!(expanded.contains("normalize() using"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources).expect("expanded pointer addition should recheck");
    assert!(verify_c0_sources(&expanded.replace("requires a == b;", ""), &c_sources).is_err());
    assert!(verify_c0_sources(&expanded.replace("b + 1;", "b + 2;"), &c_sources).is_err());
}

#[test]
fn normalize_using_graph_conditions_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/normalize_using_graph_conditions.md");
    let text = std::fs::read_to_string(&path).expect("read graph condition fixture");
    let fixture = crate::cli::parse_mdtest(&path, &text).expect("parse graph condition fixture");
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let source = fixture.click_source.as_deref().expect("Click source");
    verify_c0_sources(source, &c_sources).expect("graph conditions should normalize");
    let expanded = expand_c0_claim_source(source, &c_sources, "keep", CProofClaim::Ensure(0))
        .expect("graph condition normalization should expand");
    assert!(expanded.contains("normalize() using"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources).expect("expanded graph condition should recheck");
    let (keep_only, _) = expanded
        .split_once("theorem mixed")
        .expect("mixed theorem retained");
    let missing = keep_only.replace("requires a == b;", "");
    assert!(verify_c0_sources(&missing, &c_sources).is_err());
    // Unknown equality proves neither choice of branch.
    assert!(
        verify_c0_sources(
            &missing.replace("{ 7 } else { 0 }) == 7", "{ 7 } else { 0 }) == 0"),
            &c_sources
        )
        .is_err()
    );
    // This congruence is known from a == b even when it was not separately
    // recorded. A cited premise uses the same scoped equality lookup.
    let derived = source.replacen("using { }", "using { a + 1 == b + 1; }", 1);
    verify_c0_sources(&derived, &c_sources).expect("cited congruence is already known");
    let unavailable = source.replacen("using { }", "using { a + 1 == b + 2; }", 1);
    assert!(verify_c0_sources(&unavailable, &c_sources).is_err());
    let negated = source.replace("== b + 1 { 7 } else { 0 }", "!= b + 1 { 0 } else { 7 }");
    verify_c0_sources(&negated, &c_sources)
        .expect("known equality should also decide a negated guard");
    let uncited = source.replace("using { x < 0; }", "using { }");
    assert!(
        verify_c0_sources(&uncited, &c_sources).is_err(),
        "uncited order conditions stay unavailable"
    );
}

#[test]
fn normalize_using_int32_equality_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/normalize_using_int32_equality.md");
    let text = std::fs::read_to_string(&path).expect("read int32 equality fixture");
    let fixture = crate::cli::parse_mdtest(&path, &text).expect("parse int32 equality fixture");
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let source = fixture.click_source.as_deref().expect("Click source");
    verify_c0_sources(source, &c_sources).expect("int32 transitivity and guards should verify");
    let expanded = expand_c0_claim_source(source, &c_sources, "keep", CProofClaim::Ensure(0))
        .expect("int32 transitivity should expand");
    assert!(expanded.contains("normalize() using"), "{expanded}");
    verify_c0_sources(&expanded, &c_sources).expect("expanded int32 equality should recheck");
    let (keep, _) = expanded
        .split_once("theorem choose")
        .expect("choose retained");
    for missing in ["requires a == b;", "requires b == c;"] {
        assert!(verify_c0_sources(&keep.replace(missing, ""), &c_sources).is_err());
    }
    verify_c0_sources(
        &source.replace("ensures a == c;", "ensures c == a;"),
        &c_sources,
    )
    .expect("symmetry");
    assert!(
        verify_c0_sources(
            &keep.replace("ensures a == c;", "ensures a != c;"),
            &c_sources
        )
        .is_err()
    );
    let derived = source.replacen("using { }", "using { a == c; }", 1);
    assert_ne!(derived, source);
    verify_c0_sources(&derived, &c_sources).expect("a cited int32 congruence is known");
    let unavailable = source.replacen("using { }", "using { a != c; }", 1);
    assert!(verify_c0_sources(&unavailable, &c_sources).is_err());
    let (_, choose) = source.split_once("theorem choose").unwrap();
    let choose = format!("theorem choose{choose}");
    let unknown = choose.replace("requires b == c;", "");
    assert!(verify_c0_sources(&unknown, &[]).is_err());
    assert!(verify_c0_sources(&unknown.replace(") == 7", ") == 0"), &[]).is_err());
    verify_c0_sources(
        &choose.replace("c == a { 7 } else { 0 }", "c != a { 0 } else { 7 }"),
        &[],
    )
    .expect("negated equality guard");
}

#[test]
fn restricted_simp_does_not_borrow_the_ambient_equality_graph() {
    let source = r#"
        theorem restricted(a: int32, b: int32, c: int32) {
            requires a == b;
            requires b == c;
            ensures a == c by { simp() using { a == b; } }
        }
    "#;
    for source in [source.to_string(), source.replace("int32", "int32*")] {
        for goal in ["a == c", "(if a == c { 7 } else { 0 }) == 7"] {
            let omitted = source.replace("ensures a == c", &format!("ensures {goal}"));
            assert!(verify_c0_sources(&omitted, &[]).is_err());
            let selected = omitted.replace("using { a == b; }", "using { a == b; b == c; }");
            verify_c0_sources(&selected, &[]).expect("the selected graph establishes transitivity");
            // The simple tactic deliberately has broader ambient semantics.
            let ambient = omitted.replace("simp()", "normalize()");
            verify_c0_sources(&ambient, &[])
                .expect("explicit normalization may use the ambient graph");
        }
    }
}

#[test]
fn normalize_using_scaled_int32_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/normalize_using_scaled_int32.md");
    let text = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &text).unwrap();
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let source = fixture.click_source.as_deref().unwrap();
    verify_c0_sources(source, &c_sources).expect("scaled indices and literal should verify");
    let expanded = expand_c0_claim_source(source, &c_sources, "keep", CProofClaim::Ensure(0))
        .expect("scaled equality should expand");
    assert!(expanded.contains("normalize() using"));
    verify_c0_sources(&expanded, &c_sources).expect("expanded proof should recheck");
    let (keep, _) = expanded.split_once("theorem choose").unwrap();
    for missing in ["requires i == j;", "requires j == k;"] {
        let changed = keep.replace(missing, "");
        assert_ne!(changed, keep);
        assert!(verify_c0_sources(&changed, &c_sources).is_err());
    }
    let false_goal = source.replace("ensures p + i == p + k;", "ensures p + i != p + k;");
    assert_ne!(false_goal, source);
    assert!(verify_c0_sources(&false_goal, &c_sources).is_err());
    let restricted = source.replacen("normalize() using { }", "simp() using { i == j; }", 1);
    assert_ne!(restricted, source);
    assert!(verify_c0_sources(&restricted, &c_sources).is_err());
}

#[test]
fn normalize_using_int32_addition_expands_and_rechecks_without_proving_definedness() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/normalize_using_int32_addition.md");
    let text = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &text).unwrap();
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let source = fixture.click_source.as_deref().unwrap();
    verify_c0_sources(source, &c_sources).expect("addition and offset congruence should verify");
    let expanded = expand_c0_claim_source(source, &c_sources, "keep", CProofClaim::Ensure(0))
        .expect("addition congruence should expand");
    assert!(expanded.contains("normalize() using"));
    verify_c0_sources(&expanded, &c_sources).expect("expanded proof should recheck");
    let (keep, _) = expanded.split_once("theorem offsets").unwrap();
    let missing = keep.replace("requires a == b;", "");
    assert_ne!(missing, keep);
    assert!(verify_c0_sources(&missing, &c_sources).is_err());
    let false_goal = source.replace("ensures a + c == b + c;", "ensures a + c != b + c;");
    assert_ne!(false_goal, source);
    assert!(verify_c0_sources(&false_goal, &c_sources).is_err());
    let restricted = source.replacen(
        "normalize() using { }",
        "simp() using { defined(a + c); defined(b + c); }",
        1,
    );
    assert_ne!(restricted, source);
    assert!(verify_c0_sources(&restricted, &c_sources).is_err());
    let overflow = r#"
        theorem overflow(a: int32, b: int32) {
            requires a == b;
            requires a == 2147483647;
            ensures defined(b + 1) by { normalize() using { } }
        }
    "#;
    assert!(
        verify_c0_sources(overflow, &[]).is_err(),
        "equality cannot discharge signed overflow"
    );
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn normalize_using_int32_loads_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/normalize_using_int32_loads.md");
    let fixture =
        crate::cli::parse_mdtest(&path, &std::fs::read_to_string(&path).unwrap()).unwrap();
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let source = fixture.click_source.as_deref().unwrap();
    verify_c0_sources(source, &c_sources).expect("same-snapshot int32 loads should verify");
    let expanded = expand_c0_claim_source(source, &c_sources, "keep", CProofClaim::Ensure(0))
        .expect("load congruence should expand");
    assert!(expanded.contains("normalize() using"));
    verify_c0_sources(&expanded, &c_sources).expect("expanded loads should recheck");
    let (keep, _) = expanded.split_once("theorem same_read").unwrap();
    let missing = keep.replace("requires i == j;", "");
    assert_ne!(missing, keep);
    assert!(verify_c0_sources(&missing, &c_sources).is_err());
    let false_goal = source.replace("ensures p[i] == p[j];", "ensures p[i] != p[j];");
    assert_ne!(false_goal, source);
    assert!(verify_c0_sources(&false_goal, &c_sources).is_err());
    let restricted = source.replacen(
        "normalize() using { }",
        "simp() using { 0 <= i; i < n; 0 <= j; j < n; }",
        1,
    );
    assert_ne!(restricted, source);
    assert!(verify_c0_sources(&restricted, &c_sources).is_err());
    let store_c = [("store.c", "void store(int32 p[]) { p[0] = 9; }")];
    let store = r#"
        verifying "store.c";
        void store(int32 p[]) {
            owns p[0..1];
            ensures p[0] == old(p[0]);
        } by { execute(); simp(); }
    "#;
    verify_c0_sources(&store.replace("old(p[0])", "9"), &store_c)
        .expect("the store itself verifies");
    assert!(
        verify_c0_sources(store, &store_c).is_err(),
        "a relevant store must invalidate the old read"
    );
    let read_c = [(
        "read.c",
        "int32 read(int32 p[], int32 i, int32 j) { return p[i]; }",
    )];
    let read = r#"
        verifying "read.c";
        int32 read(int32 p[], int32 i, int32 j) {
            requires i == j;
            ensures result == result;
        } by { execute(); simp(); }
    "#;
    assert!(
        verify_c0_sources(read, &read_c).is_err(),
        "equal offsets do not grant read permission"
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn normalize_using_transported_int32_loads_expands_and_rechecks() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/normalize_using_transported_int32_loads.md");
    let fixture =
        crate::cli::parse_mdtest(&path, &std::fs::read_to_string(&path).unwrap()).unwrap();
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let source = fixture.click_source.as_deref().unwrap();
    verify_c0_sources(source, &c_sources)
        .expect("checked transport should compose with load congruence");
    let expanded =
        expand_c0_claim_source(source, &c_sources, "write_other", CProofClaim::Ensure(1))
            .expect("transport composition should expand");
    verify_c0_sources(&expanded, &c_sources)
        .expect("expanded transport composition should recheck");
    assert!(expanded.contains("transport("));
    assert!(expanded.contains("normalize() using"));
    let omitted_indices = source.replace("requires i == j;", "");
    assert_ne!(omitted_indices, source);
    assert!(verify_c0_sources(&omitted_indices, &c_sources).is_err());
    let overlap = source.replace("i != k", "i == k");
    assert_ne!(overlap, source);
    assert!(verify_c0_sources(&overlap, &c_sources).is_err());
    let missing_separation = source
        .replace("requires i != k;", "")
        .replace("using { i != k; }", "using { }");
    assert_ne!(missing_separation, source);
    assert!(verify_c0_sources(&missing_separation, &c_sources).is_err());
    let bridge_start = source
        .find("    have p[i] == at(entry, p[i]) by {")
        .unwrap();
    let bridge_end = source
        .find("    have p[j] == at(entry, p[i]) by {")
        .unwrap();
    let mut no_bridge = source.to_owned();
    no_bridge.replace_range(bridge_start..bridge_end, "");
    assert!(
        verify_c0_sources(&no_bridge, &c_sources).is_err(),
        "the equality graph must not perform frame search"
    );
}

#[test]
fn authority_callback_count_refinement_expands_every_smart_site() {
    let fixture = crate::cli::parse_mdtest(
        std::path::Path::new("authority_callback_count_refinement.md"),
        include_str!("../../../mdtests/authority_callback_count_refinement.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let c_sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let project_for = |source: &str| {
        ClickProject::new(
            "population.click",
            [ClickModuleSource::new("population.click", source, [])],
        )
        .with_c_profile(CProjectProfile {
            target: None,
            runtime: None,
        })
    };
    let project = project_for(source);
    verify_c0_project(&project, &c_sources).expect("the callback Count refinement verifies");
    let sites =
        project_smart_tactic_source_sites(&project, &ProgramInputs::Bundle(c_sources.to_vec()))
            .unwrap();
    assert!(!sites.is_empty());
    for site in sites {
        let position = project_tactic_source_position(
            &project,
            &ProgramInputs::Bundle(c_sources.to_vec()),
            &site.claim_label,
            site.source_index,
        )
        .unwrap();
        let expanded = expand_project_tactic_source_at(
            &project,
            &ProgramInputs::Bundle(c_sources.to_vec()),
            position.line,
            position.column,
        )
        .unwrap();
        verify_c0_project(&project_for(&expanded), &c_sources).unwrap_or_else(|error| {
            panic!(
                "{} site {} ({}) lost its checked resource transition: {}",
                site.claim_label,
                site.source_index,
                site.tactic_name,
                error.message()
            )
        });
    }
}

#[test]
fn resource_closers_cannot_return_one_unit_as_both_borrowed_and_produced() {
    let valid_source = "resource cell(p: int32*) { owns p[0..1]; }
        verifying \"keep.c\";
        void keep(int32* p) { owns cell(p); } by { execute(); simp(); }";
    let valid_project = ClickProject::new(
        "duplicate.click",
        [ClickModuleSource::new("duplicate.click", valid_source, [])],
    )
    .with_c_profile(CProjectProfile {
        target: None,
        runtime: None,
    });
    verify_c0_project(&valid_project, &[("keep.c", "void keep(int32* p) {}")])
        .expect("the same C body returns one borrowed exclusive unit");
    let mut accepted_closers = Vec::new();
    for (produced, closer) in [
        ("cell", "simp();"),
        ("cell", "assumption(); assumption();"),
        ("other_cell", "simp();"),
        ("other_cell", "assumption(); assumption();"),
    ] {
        let source = format!(
            "resource cell(p: int32*) {{ owns p[0..1]; }}\n\
             resource other_cell(p: int32*) {{ owns p[0..1]; }}\n\
             verifying \"keep.c\";\n\
             void keep(int32* p) {{ owns cell(p); produces {produced}(p); }}\n\
             by {{ execute(); {closer} }}"
        );
        let project = ClickProject::new(
            "duplicate.click",
            [ClickModuleSource::new("duplicate.click", &source, [])],
        )
        .with_c_profile(CProjectProfile {
            target: None,
            runtime: None,
        });
        if verify_c0_project(&project, &[("keep.c", "void keep(int32* p) {}")]).is_ok() {
            accepted_closers.push((produced, closer));
        }
    }
    assert!(
        accepted_closers.is_empty(),
        "these closers returned one exclusive unit twice: {accepted_closers:?}"
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn authority_named_parent_keeps_actual_fields_across_unrelated_owned_call() {
    let source = r#"
spec enum ParentLink { Empty, Linked(struct child*) }
resource parent(p: struct parent*) {
    field link: ParentLink;
    match link {
        ParentLink::Empty => {},
        ParentLink::Linked(kid) => {
            owns p->kid;
            fact defined(p->kid);
            fact p->kid == kid;
            fact kid != 0;
        },
    }
}
verifying "named.c";
void attach(struct parent* p, struct child* kid) {
    requires kid != 0;
    consumes p->kid;
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
    ensures p->kid == kid;
} by {
    execute();
    let link = fold(parent(p), { link: ParentLink::Linked(kid) });
    simp();
}
void clear_payload(struct child* kid) {
    owns kid->payload;
    ensures kid->payload == 0;
} by {
    execute();
    simp();
}
void caller(struct parent* p, struct child* kid) {
    requires kid != 0;
    consumes p->kid;
    owns kid->payload;
    produces link: parent(p);
    ensures link.link == ParentLink::Linked(kid);
    ensures p->kid == kid;
} by {
    let { link: link } = step(attach(p, kid), {});
    have p->kid == kid by simp();
    step();
    have p->kid == kid by simp();
    execute();
    simp();
}
"#;
    let c_source = r#"
struct child { int32 payload; };
struct parent { struct child* kid; };
void attach(struct parent* p, struct child* kid) { p->kid = kid; }
void clear_payload(struct child* kid) { kid->payload = 0; }
void caller(struct parent* p, struct child* kid) {
    attach(p, kid);
    clear_payload(kid);
}
"#;
    let project_for = |source: &str| {
        ClickProject::new(
            "named.click",
            [ClickModuleSource::new("named.click", source, [])],
        )
        .with_c_profile(CProjectProfile {
            target: None,
            runtime: None,
        })
    };
    let c = [("named.c", c_source)];
    let project = project_for(source);
    verify_c0_project(&project, &c)
        .expect("a named parent's actual field identity survives the unrelated call");
    for site in
        project_smart_tactic_source_sites(&project, &ProgramInputs::Bundle(c.to_vec())).unwrap()
    {
        let position = site.position;
        let expanded = expand_project_tactic_source_at(
            &project,
            &ProgramInputs::Bundle(c.to_vec()),
            position.line,
            position.column,
        )
        .unwrap();
        let owner = site.claim_label.rsplit_once('.').unwrap().0;
        verify_expanded_project_function_source(
            source,
            &expanded,
            &project_for(&expanded),
            &c,
            owner,
        )
        .expect("the explicit proof preserves actual instance fields and the caller frame");
    }
}

#[test]
fn composite_fold_argument_read_retains_checked_address_and_bounds() {
    let c_source = "int32 keep(int32* p, int32* q, int32 i, int32 n) { return 0; }";
    let click_source = r#"
resource tag(value: int32) {}
verifying "fold_context.c";
int32 keep(int32* p, int32* q, int32 i, int32 n) {
    requires p == q;
    requires 0 <= i;
    requires i < n;
    views p[0..n];
    ensures result == 0;
} by {
    fold(tag(q[i]));
    execute();
    simp();
}
"#;
    let c_sources = [("fold_context.c", c_source)];
    verify_c0_sources(click_source, &c_sources)
        .expect("fold argument reads should retain checked equality and bounds");
    for required in ["requires p == q;", "requires 0 <= i;", "requires i < n;"] {
        let missing = click_source.replace(required, "");
        let error = verify_c0_sources(&missing, &c_sources)
            .expect_err("fold must not invent missing address equality or bounds");
        assert!(
            error
                .message()
                .contains("could not lower resource `tag` argument 0"),
            "missing {required}: {}",
            error.message()
        );
    }
    let expanded = expand_c0_claim_source(click_source, &c_sources, "keep", CProofClaim::Ensure(0))
        .expect("fold argument reads should expand");
    verify_c0_sources(&expanded, &c_sources)
        .expect("expanded fold argument reads should independently reverify");
}

#[test]
fn published_symbolic_owner_store_expands_and_rechecks() {
    let c = "void put(int32* p, int32 i, int32 n) { p[i] = 7; }";
    let source = r#"
verifying "symbolic_write.c";
void put(int32* p, int32 i, int32 n) {
    requires 1 <= i;
    requires i < n;
    owns p[1..n];
    ensures p[i] == 7;
} by { execute(); simp(); }
"#;
    let inputs = [("symbolic_write.c", c)];
    verify_c0_sources(source, &inputs)
        .expect("the published symbolic owner should authorize the store");
    let expanded = expand_c0_claim_source(source, &inputs, "put", CProofClaim::Ensure(0))
        .expect("the symbolic owner store should expand");
    verify_c0_sources(&expanded, &inputs)
        .expect("the expanded store should independently reverify");
    for premise in ["requires 1 <= i;", "requires i < n;"] {
        let missing = source.replace(premise, "");
        assert!(
            verify_c0_sources(&missing, &inputs).is_err(),
            "missing {premise} must not authorize the store"
        );
    }
    let views = source.replace("owns p[1..n];", "views p[1..n];");
    assert!(
        verify_c0_sources(&views, &inputs).is_err(),
        "a published view is not write authority"
    );
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn published_aliased_symbolic_owner_store_expands_and_rechecks() {
    let c = "void put(int32* p, int32* q, int32 i, int32 n) { q[i] = 7; }";
    let source = r#"
verifying "symbolic_write.c";
void put(int32* p, int32* q, int32 i, int32 n) {
    requires p == q;
    requires 1 <= i;
    requires i < n;
    owns p[1..n];
    ensures q[i] == 7;
} by { execute(); simp(); }
"#;
    let inputs = [("symbolic_write.c", c)];
    verify_c0_sources(source, &inputs)
        .expect("the published symbolic owner should authorize the store");
    let expanded = expand_c0_claim_source(source, &inputs, "put", CProofClaim::Ensure(0))
        .expect("the symbolic owner store should expand");
    verify_c0_sources(&expanded, &inputs)
        .expect("the expanded store should independently reverify");
    for premise in ["requires p == q;", "requires 1 <= i;", "requires i < n;"] {
        let missing = source.replace(premise, "");
        assert!(
            verify_c0_sources(&missing, &inputs).is_err(),
            "missing {premise} must not authorize the store"
        );
    }
    let views = source.replace("owns p[1..n];", "views p[1..n];");
    assert!(
        verify_c0_sources(&views, &inputs).is_err(),
        "a published view is not write authority"
    );
}

/// A loop with no invariant has nothing to initialize, so a `simp` that is
/// its `initialize` block's only tactic contributes no step. A `by { ... }`
/// block must hold a tactic, so the expansion keeps `assumption();` there
/// rather than emptying the block, and the rewritten proof verifies.
#[test]
fn expanding_the_only_tactic_of_an_empty_initialize_phase_keeps_a_step() {
    let c_source =
        "int32 drain(uint32 x) {\n    while (x > 0u) {\n        x--;\n    }\n    return 0;\n}\n";
    let click_source = "verifying \"drain.c\";\n\
        int32 drain(uint32 x) {\n\
        \x20   ensures result == 0;\n\
        } by {\n\
        \x20   loop {\n\
        \x20       decreases x;\n\
        \x20       initialize by { simp(); }\n\
        \x20       preserve by {\n\
        \x20           step();\n\
        \x20           close_invariants();\n\
        \x20       }\n\
        \x20   }\n\
        \x20   execute();\n\
        \x20   simp();\n\
        }\n";
    let c_sources = [("drain.c", c_source)];
    for proof in ["simp();", "{ simp(); }", "auto();", "{ auto(); }"] {
        let source = click_source.replace(
            "initialize by { simp(); }",
            &format!("initialize by {proof}"),
        );
        let name = if proof.contains("auto") {
            "auto"
        } else {
            "simp"
        };
        let column = source.lines().nth(6).unwrap().find(name).unwrap() + 1;
        let expanded = expand_c0_tactic_source_at(&source, &c_sources, 7, column)
            .expect("the initialize call expands");
        assert!(
            expanded.contains("initialize by { assumption(); }"),
            "{expanded}"
        );
        verify_c0_sources(&expanded, &c_sources).expect("the expanded proof verifies");
        let batch = expand_c0_tactics_source_at(
            &source,
            &c_sources,
            &[expansion::position_at_offset(
                &source,
                source.find("initialize by").unwrap()
                    + "initialize by ".len()
                    + proof.find(name).unwrap(),
            )],
        )
        .expect("the initialize call expands in a batch");
        assert!(batch.source.contains("assumption();"));
        verify_c0_sources(&batch.source, &c_sources).expect("the batch expansion verifies");
    }
}

/// Omitted proofs of several claims share one implicit `} by auto();`, which
/// `click expand` at the contract's closing brace writes out after it; a
/// claim with its own proof keeps it unchanged.
#[test]
fn the_implicit_grouped_proof_expands_after_the_contract_and_reverifies() {
    let c_source = r#"
        int32 inc(int32 x) {
            return x + 1;
        }
    "#;
    let click_source = r#"
        verifying "inc.c";

        int32 inc(int32 x) {
            requires x >= 0 and x <= 100;
            ensures result >= 1 by auto();
            ensures result <= 101;
            ensures result <= 200;
        }
    "#;
    let c_sources = [("inc.c", c_source)];
    verify_c0_sources(click_source, &c_sources).expect("the omitted proofs should verify");
    let close = click_source
        .rfind('}')
        .expect("the contract should end with a closing brace");
    let position = expansion::position_at_offset(click_source, close);
    let expanded =
        expand_c0_tactic_source_at(click_source, &c_sources, position.line, position.column)
            .expect("the implicit grouped proof should expand");
    assert!(
        expanded.contains("ensures result >= 1 by auto();"),
        "{expanded}"
    );
    assert!(
        expanded.contains("ensures result <= 200;\n        } by {"),
        "{expanded}"
    );
    assert_eq!(expanded.matches("step();").count(), 1, "{expanded}");
    verify_c0_sources(&expanded, &c_sources).expect("the expanded grouped proof should verify");
}

/// A maybe-throwing call is a fork wherever it sits, so the closers of its
/// threw path go in that call's own `outcomes` arm. Straight-line, after a C
/// `if`, and inside one arm of a C `if`, every proof shape of every claim
/// expands to source that re-verifies.
#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn throwing_call_forks_expand_and_reverify_in_every_position() {
    let c_source = r#"
        int32 helper(int32 x) { return x; }
        int32 straight(int32 x) {
            int32 y = helper(x);
            int32 z = helper(y);
            return z;
        }
        int32 after(int32 x) {
            int32 y = 0;
            if (x > 0) {
                y = 1;
            }
            y = helper(x);
            return y;
        }
        int32 inside(int32 x) {
            int32 y = 0;
            if (x > 0) {
                y = helper(x);
            }
            return y;
        }
    "#;
    let contract = |name: &str, normal: &str, proofs: [&str; 3]| {
        format!(
            "int32 {name}(int32 x) throws int32 {{\n    ensures {normal}{};\n    exceptional ensures exception == 7{};\n}}{}\n",
            proofs[0], proofs[1], proofs[2]
        )
    };
    let c_sources = [("forks.c", c_source)];
    for proofs in [
        ["", "", ""],
        [" by auto()", " by auto()", ""],
        ["", "", " by auto();"],
    ] {
        let click_source = format!(
            "verifying \"forks.c\";\nint32 helper(int32 x) throws int32 {{\n    ensures result == x by auto();\n    exceptional ensures exception == 7 by auto();\n}}\n{}{}{}",
            contract("straight", "result == x", proofs),
            contract("after", "result == x", proofs),
            contract("inside", "result >= 0", proofs),
        );
        verify_c0_sources(&click_source, &c_sources)
            .unwrap_or_else(|error| panic!("{proofs:?} should verify: {}", error.message()));
        for function in ["straight", "after", "inside"] {
            let claims = if proofs[0].is_empty() {
                vec![CProofClaim::Grouped]
            } else {
                vec![CProofClaim::Ensure(0), CProofClaim::ExceptionalEnsure(0)]
            };
            for claim in claims {
                let expanded = expand_c0_claim_source(&click_source, &c_sources, function, claim)
                    .unwrap_or_else(|error| {
                        panic!(
                            "{function} {claim:?} {proofs:?} should expand: {}",
                            error.message()
                        )
                    });
                assert!(expanded.contains("outcomes {"), "{expanded}");
                verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
                    panic!(
                        "{function} {claim:?} {proofs:?} expansion should re-verify: {}\n{expanded}",
                        error.message()
                    )
                });
            }
        }
    }
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn selected_deferred_closer_freezes_computed_guards_before_parameter_mutation() {
    for (c_source, expected) in [
        (
            "int32 choose(int32 x) { x = x + 1; int32 flag = x < 7; if (flag) { x = x + 1; return x; } else { return 7; } }",
            "if old(x) + 1 < 7 { (old(x) + 1) + 1 } else { 7 }",
        ),
        (
            "int32 choose(int32 x) { x = x + 1; int32 flag = x < 7; if (flag) { int32 inner = x < 4; if (inner) { x = x + 2; return x; } else { x = x + 1; return x; } } else { return 7; } }",
            "if old(x) + 1 < 7 { if old(x) + 1 < 4 { (old(x) + 1) + 2 } else { (old(x) + 1) + 1 } } else { 7 }",
        ),
    ] {
        let source = format!(
            "verifying \"choose.c\";\nint32 choose(int32 x) {{ requires 0 <= x; requires x <= 100; ensures result == ({expected}); }} by {{\nexecute();\nsimp();\n}}"
        );
        verify_c0_sources(&source, &[("choose.c", c_source)]).unwrap();
        let expanded = expand_c0_tactic_source_at(&source, &[("choose.c", c_source)], 4, 1)
            .unwrap_or_else(|error| panic!("{}\nC source: {c_source}", error.message()));
        verify_c0_sources(&expanded, &[("choose.c", c_source)]).unwrap_or_else(|error| {
            panic!(
                "deferred closer must reverify: {}\n{expanded}",
                error.message()
            )
        });
    }
}

#[test]
fn uint32_arithmetic_bound_weakening_expands_and_rechecks() {
    let (source, _) = mdtest_sources("mdtests/uint32_arithmetic_bound_weakening.md");
    verify_c0_sources(&source, &[]).expect("unsigned weakened bounds should verify");
    for name in [
        "lane_ceiling",
        "crossing_sign_bit",
        "high_unsigned_ceiling",
        "high_unsigned_floor",
        "crossing_sign_bit_floor",
    ] {
        let expanded = expand_c0_claim_source_by_label(&source, &[], &format!("{name}.ensures_0"))
            .expect("unsigned weakening should expand");
        // An unsigned bound is the Integer bound of its observation, so the
        // step is an Integer certificate with no sign-bit encoding.
        assert!(expanded.contains("arithmetic_certificate {"), "{expanded}");
        assert!(!expanded.contains("signed_int32"), "{expanded}");
        let (result, planning) =
            crate::surface::proof::count_planning_statement_transitions(|| {
                verify_c0_sources(&expanded, &[])
            });
        result.expect("unsigned certificate should independently recheck");
        assert_eq!(planning, 0, "explicit recheck must not plan");
        if name == "lane_ceiling" {
            let forged = expanded.replace("1073741823u32", "65519u32");
            verify_c0_sources(&forged, &[])
                .expect_err("a strengthened conclusion must not reuse the original certificate");
        }
    }
    for (premise, goal) in [
        ("lane <= 1073741823u32", "lane <= 65520u32"),
        ("lane <= 2147483648u32", "lane <= 2147483647u32"),
        ("2147483647u32 <= lane", "2147483648u32 <= lane"),
        ("lane <= 65520u32", "1073741823u32 <= lane"),
    ] {
        let invalid = format!(
            "theorem invalid(lane: uint32) {{ requires {premise}; \
             ensures {goal} by {{ arithmetic() using {{ {premise}; }} }} }}"
        );
        verify_c0_sources(&invalid, &[]).expect_err("insufficient unsigned bounds must fail");
    }
    let missing = source.replacen(
        "arithmetic() using { lane <= 65520u32; }",
        "arithmetic() using {};",
        1,
    );
    verify_c0_sources(&missing, &[]).expect_err("unlisted bounds must not prove the ceiling");
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn uint32_mul_observations_and_true_disjunction_expand_and_recheck() {
    let (guarded, _) =
        mdtest_sources("mdtests/true_disjunction_skips_undefined_right_requirement.md");
    let (products, _) = mdtest_sources("mdtests/integer_uint32_checked_product_observations.md");
    let source = format!("{guarded}\n{products}");
    verify_c0_sources(&source, &[]).expect("zero-factor and checked products should verify");
    for claim in [
        "zero_instance.ensures_0",
        "known_zero_instance.ensures_0",
        "zero_factor.ensures_0",
        "known_zero_factor.ensures_0",
        "reduced_lane_ceiling.ensures_0",
    ] {
        let expanded = expand_c0_claim_source_by_label(&source, &[], claim)
            .expect("checked multiplication/zero-factor proof should expand");
        verify_c0_sources(&expanded, &[])
            .expect("expanded multiplication/zero-factor certificate should recheck");
    }
    let (invalid, _) =
        mdtest_sources("mdtests/false_disjunction_requires_defined_right_requirement.md");
    verify_c0_sources(&invalid, &[])
        .expect_err("a false left disjunct must not hide division by zero");
    let forged = guarded.replace("ensures 1 == 1", "ensures 1 == 2");
    verify_c0_sources(&forged, &[]).expect_err("a true guard must not prove a false conclusion");
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn integer_observed_product_identity_rewrites_expand_and_recheck() {
    let (source, _) = mdtest_sources("mdtests/integer_observed_product_identity_rewrite.md");
    verify_c0_sources(&source, &[]).expect("observed product identity rewrites should verify");
    for name in [
        "zero_product",
        "zero_left_product",
        "unit_product",
        "unit_left_product",
        "full_unsigned_zero",
        "full_unsigned_unit",
    ] {
        let expanded = expand_c0_claim_source_by_label(&source, &[], &format!("{name}.ensures_0"))
            .expect("observed product identity rewrite should expand");
        assert!(expanded.contains("arithmetic_certificate {"), "{expanded}");
        let (result, planning) =
            crate::surface::proof::count_planning_statement_transitions(|| {
                verify_c0_sources(&expanded, &[])
            });
        result.expect("expanded product identity should independently recheck");
        assert_eq!(planning, 0, "explicit identity certificate must not plan");
        if name == "zero_product" {
            let forged = expanded.replace(
                "trivial => (to_integer(a) * 0) == 0;",
                "trivial => (to_integer(a) * 0) == 1;",
            );
            assert_ne!(
                forged, expanded,
                "the expanded zero claim should be present"
            );
            verify_c0_sources(&forged, &[]).expect_err("a false trivial certificate must fail");
        }
        let missing = expanded
            .replace("requires to_integer(b) == 0;", "")
            .replace("requires to_integer(b) == 1;", "");
        verify_c0_sources(&missing, &[]).expect_err("missing identity evidence must fail");
    }
    for invalid in [
        source.replacen(
            "ensures to_integer(a) * to_integer(b) == 0",
            "ensures to_integer(a) * to_integer(b) == 1",
            1,
        ),
        source.replacen(
            "rewrite(to_integer(b) == 0)",
            "rewrite(to_integer(a) == 0)",
            1,
        ),
        source.replacen(
            "ensures to_integer(a) * to_integer(b) == 0",
            "ensures to_integer(a) * to_integer(a) == 0",
            1,
        ),
        source.replace("== 4294967295 by", "== -1 by"),
    ] {
        verify_c0_sources(&invalid, &[])
            .expect_err("false products and altered unsigned observations must fail");
    }
    let c_source = "uint32 identity(uint32 a, uint32 b) { return a; }";
    let click_source = r#"
verifying "identity.c";
uint32 identity(uint32 a, uint32 b) {
    requires to_integer(b) == 0;
    ensures to_integer(result) * to_integer(b) == 0;
} by {
    have to_integer(a) * to_integer(b) == 0 by {
        rewrite(to_integer(b) == 0);
        arithmetic() using {};
    }
    execute();
    rewrite(to_integer(b) == 0);
    arithmetic() using {};
}
"#;
    let inputs = [("identity.c", c_source)];
    let verified_for_label = verify_c0_sources(click_source, &inputs)
        .expect("execution and outcome identity rewrites should verify");
    let expanded =
        expand_checked_function_claim(click_source, &verified_for_label, "identity.ensures_0")
            .unwrap();
    verify_c0_sources(&expanded, &inputs)
        .expect("expanded outcome identity rewrite should recheck");
}

#[test]
fn integer_equality_rewrite_expands_rechecks_and_rejects_forged_claims() {
    let (source, _) = mdtest_sources("mdtests/integer_equality_rewrite.md");
    verify_c0_sources(&source, &[]).expect("Integer compound rewrites should verify");
    for claim in 0..4 {
        let expanded = expand_c0_claim_source_by_label(
            &source,
            &[],
            &format!("integer_compound_rewrite.ensures_{claim}"),
        )
        .expect("Integer rewrite should expand");
        assert!(expanded.contains("rewrite("));
        verify_c0_sources(&expanded, &[]).expect("expanded Integer rewrite should recheck");
        let forged = expanded.replace("requires a == b;", "");
        let error = verify_c0_sources(&forged, &[]).expect_err("erased Integer evidence must fail");
        assert!(error.message().len() < 8000);
    }
    for hostile in [
        source.replace("rewrite(a == b);", "rewrite(a == d);"),
        source.replace(
            "ensures a * d + a == b * d + b",
            "ensures a * d + a == b * d + b + 1",
        ),
        source.replace("requires d != 0;", "requires d == 0;"),
    ] {
        let error =
            verify_c0_sources(&hostile, &[]).expect_err("hostile Integer rewrite must fail");
        assert!(error.message().len() < 8000);
    }
    let c_source = "int64 identity(int64 x, int64 y) { return x; }";
    let source = r#"
verifying "identity.c";
int64 identity(int64 x, int64 y) {
    requires to_integer(x) == to_integer(y);
    ensures to_integer(result) * 3 + to_integer(result) == to_integer(y) * 3 + to_integer(y);
} by {
    execute();
    rewrite(to_integer(x) == to_integer(y));
    simp();
}
"#;
    let inputs = [("identity.c", c_source)];
    let verified_for_label = verify_c0_sources(source, &inputs)
        .expect("fixed-state observed Integer rewrite should verify");
    let expanded =
        expand_checked_function_claim(source, &verified_for_label, "identity.ensures_0").unwrap();
    verify_c0_sources(&expanded, &inputs)
        .expect("fixed-state observed Integer rewrite should recheck");
}

#[test]
fn symbolic_upper_arithmetic_premises_expand_and_cold_recheck() {
    for (name, premise, extra) in [
        ("difference", "a <= 1000 - b", ""),
        ("equality", "a == 1000 - b", ""),
        (
            "sum",
            "a + b <= 1000",
            "requires a >= 0; requires a <= 1000;",
        ),
        (
            "both_roots",
            "a + b <= 999 + b",
            "requires a >= 0; requires a <= 1000;",
        ),
    ] {
        let extra_using = if extra.is_empty() {
            ""
        } else {
            "a >= 0; a <= 1000;"
        };
        let source = format!("theorem {name}(a: int32, b: int32) {{
            requires b >= 1; requires b <= 1000; requires {premise}; {extra}
            ensures a <= 999 by {{ arithmetic() using {{ {premise}; b >= 1; b <= 1000; {extra_using} }} }}
        }}");
        verify_c0_sources(&source, &[]).expect("symbolic upper bound should verify");
        let expanded = expand_c0_claim_source_by_label(&source, &[], &format!("{name}.ensures_0"))
            .expect("symbolic upper bound should expand");
        assert!(expanded.contains("affine_premise"), "{expanded}");
        let (result, planning) =
            crate::surface::proof::count_planning_statement_transitions(|| {
                verify_c0_sources(&expanded, &[])
            });
        result.unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
        assert_eq!(planning, 0, "explicit certificate recheck must not plan");
        let conversion = expanded
            .lines()
            .find(|line| line.contains("affine_premise"))
            .unwrap();
        let (prefix, _) = conversion.trim().split_once("=>").unwrap();
        let source = prefix.split_whitespace().nth(1).unwrap();
        let forged = expanded.replacen(
            prefix,
            &format!("affine_premise {source} {source} {source} "),
            1,
        );
        verify_c0_sources(&forged, &[])
            .expect_err("affine values cannot replace checked interval evidence");
        let forged = expanded.replace("a <= 999", "a <= 998");
        verify_c0_sources(&forged, &[]).expect_err("a false tighter bound must be refused");
    }
}

fn check_counted_pthread_whole_claim_expansion(fixture: &str, claim: &str) {
    let (source, sources) = mdtest_sources(&format!("mdtests/{fixture}.md"));
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let project_for = |source: &str| {
        ClickProject::new(
            "population.click",
            [ClickModuleSource::new("population.click", source, [])],
        )
        .with_c_profile(CProjectProfile {
            target: None,
            runtime: None,
        })
    };
    let project = project_for(&source);
    verify_c0_project(&project, &sources).expect("the original counted pthread proof verifies");
    let expanded = expand_project_claim_source_by_label(
        &project,
        &ProgramInputs::Bundle(sources.to_vec()),
        claim,
    )
    .unwrap();
    verify_c0_project(&project_for(&expanded), &sources)
        .unwrap_or_else(|error| panic!("{fixture}: {}\n{expanded}", error.message()));
    if fixture == "modeled_pthread_counted_join" {
        let position = expansion::position_at_offset(
            &expanded,
            expanded
                .find("ensures result == 0 or result == 1;")
                .unwrap(),
        );
        let (result, planning) =
            crate::surface::proof::count_planning_statement_transitions(|| {
                verify_project_at(
                    &project_for(&expanded),
                    &ProgramInputs::Bundle(sources.to_vec()),
                    position.line,
                    position.column,
                )
            });
        result.expect("the complete expanded claim must cold recheck");
        assert_eq!(
            planning, 0,
            "expanded create branches must not invoke planning"
        );
        let forged = expanded.replacen(
            "have ((int32)count(ticket(p))) == 1",
            "have ((int32)count(ticket(p))) == 0",
            1,
        );
        assert_ne!(forged, expanded);
        verify_c0_project(&project_for(&forged), &sources)
            .expect_err("a failed create retains one ticket, not zero");
        let false_contract = expanded.replace(
            "ensures result == 0 or result == 1;",
            "ensures result == 0;",
        );
        verify_c0_project(&project_for(&false_contract), &sources)
            .expect_err("the successful create path must not disappear");
    }
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn counted_pthread_whole_claim_expansion_join() {
    check_counted_pthread_whole_claim_expansion("modeled_pthread_counted_join", "run.contract");
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn counted_pthread_whole_claim_expansion_reverse_join() {
    check_counted_pthread_whole_claim_expansion(
        "modeled_pthread_counted_reverse_join",
        "run.contract",
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn counted_pthread_whole_claim_expansion_shared_forward_join() {
    check_counted_pthread_whole_claim_expansion(
        "modeled_pthread_counted_shared_forward_join",
        "run.contract",
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn counted_pthread_whole_claim_expansion_shared_join() {
    check_counted_pthread_whole_claim_expansion(
        "modeled_pthread_counted_shared_join",
        "run.contract",
    );
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn counted_pthread_whole_claim_expansion_partial_then_create() {
    check_counted_pthread_whole_claim_expansion(
        "modeled_pthread_counted_shared_partial_then_create",
        "run.contract",
    );
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn counted_pthread_whole_claim_expansion_retained() {
    check_counted_pthread_whole_claim_expansion(
        "modeled_pthread_counted_shared_retained",
        "run.contract",
    );
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn counted_pthread_whole_claim_expansion_symbolic() {
    check_counted_pthread_whole_claim_expansion(
        "modeled_pthread_counted_shared_symbolic",
        "run.contract",
    );
}

#[test]
fn counted_pthread_whole_claim_expansion_retire() {
    check_counted_pthread_whole_claim_expansion(
        "modeled_pthread_retire_after_join",
        "run.contract",
    );
}

#[test]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn counted_pthread_whole_claim_expansion_mutex() {
    check_counted_pthread_whole_claim_expansion(
        "mutex_population_separate_body",
        "increment_twice.contract",
    );
}

#[test]
fn whole_claim_expansion_routes_return_closers_only_to_checked_branches() {
    let (original, sources) = mdtest_sources("mdtests/pruned_returning_branch_expansion.md");
    let c = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let tail = "branch { step(); simp(); } else {}\n    step(); simp();";
    let original_branch = "branch { step(); simp(); } else { step(); simp(); }";
    for (case, source) in [
        ("then only", original.clone()),
        (
            "else only",
            original
                .replace("requires n == 5;", "requires n == 0;")
                .replace(original_branch, tail),
        ),
        (
            "both reachable",
            original
                .replace("    requires n == 5;\n", "")
                .replace(original_branch, tail),
        ),
    ] {
        let verified_for_label = verify_c0_sources(&source, &c)
            .unwrap_or_else(|error| panic!("{case}: {}", error.message()));
        let expanded = expand_checked_function_claim(&source, &verified_for_label, "f.contract")
            .unwrap_or_else(|error| panic!("{case}: {}", error.message()));
        assert!(
            c0_smart_tactic_source_sites(&expanded, &c)
                .unwrap()
                .is_empty(),
            "{case}: {expanded}"
        );
        verify_c0_sources(&expanded, &c)
            .unwrap_or_else(|error| panic!("{case}: {}\n{expanded}", error.message()));
        if case == "then only" {
            let file = crate::surface::parse(&expanded).unwrap();
            let SourceProof::Script(tactics) = file.function_blocks()[0].covering_proof().unwrap()
            else {
                panic!("expanded grouped proof should be a script");
            };
            let branch = tactics
                .iter()
                .find_map(|tactic| match tactic {
                    ProofTactic::If(branch) => Some(branch),
                    _ => None,
                })
                .unwrap();
            assert!(
                branch.else_tactics.is_empty(),
                "pruned arm received outcome tactics: {expanded}"
            );
            let missing_entry = expanded.replace("step();", "");
            assert_ne!(missing_entry, expanded);
            let result = verify_c0_sources(&missing_entry, &c);
            assert!(result.is_err(), "expanded arm accepted missing entry steps");
            let false_closer = expanded.replace("result == 5 or result == 7", "result == 99");
            assert!(verify_c0_sources(&false_closer, &c).is_err());
        }
    }
}

#[test]
fn nested_pruned_return_expansion_cold_reverifies() {
    let c = "int32 f(int32 n) { if (n > 0) { if (n > 1) { return 5; } return 6; } return 7; }";
    let source = r#"verifying "nested.c";
int32 f(int32 n) {
    requires n == 5;
    ensures result == 5;
} by {
    branch {
        branch { step(); simp(); } else { step(); simp(); }
    } else { step(); simp(); }
}
"#;
    verify_c0_sources(source, &[("nested.c", c)]).unwrap();
    let expanded = expand_c0_claim_source_by_label(source, &[("nested.c", c)], "f.contract")
        .unwrap_or_else(|error| panic!("{}", error.message()));
    assert!(
        c0_smart_tactic_source_sites(&expanded, &[("nested.c", c)])
            .unwrap()
            .is_empty()
    );
    verify_c0_sources(&expanded, &[("nested.c", c)])
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn pruned_empty_c_arm_expansion_walks_the_tail_iteratively() {
    for count in [4, 16, 64] {
        let mut c = String::from("int32 f(int32 n) {\n");
        for value in 0..count {
            c.push_str(&format!("if (n == {value}) return {value};\n"));
        }
        c.push_str(&format!("return {count}; }}"));
        let source = format!(
            r#"verifying "tail.c";
int32 f(int32 n) {{
    requires n == {count};
    ensures result == {count};
}} by {{ execute(); simp(); }}
"#
        );
        let sources = [("tail.c", c.as_str())];
        let verified_for_label = verify_c0_sources(&source, &sources).unwrap();
        let expanded = expand_checked_function_claim(&source, &verified_for_label, "f.contract")
            .unwrap_or_else(|error| panic!("{count} branches: {}", error.message()));
        assert!(
            c0_smart_tactic_source_sites(&expanded, &sources)
                .unwrap()
                .is_empty()
        );
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{count} branches: {}\n{expanded}", error.message()));
    }
}

fn check_exceptional_claim_label_expansion(fixture: &str) {
    let (source, sources) = mdtest_sources(&format!("mdtests/{fixture}.md"));
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded =
        expand_c0_claim_source_by_label(&source, &sources, "helper.exceptional_ensures_0")
            .unwrap_or_else(|error| panic!("{fixture}: {}", error.message()));
    assert!(
        expanded.contains("ensures result == x by auto();"),
        "the normal claim remains unselected: {expanded}"
    );
    assert!(
        !expanded.contains("exceptional ensures exception == 7 by auto();"),
        "the selected exceptional proof is expanded: {expanded}"
    );
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("{fixture}: {}\n{expanded}", error.message()));
}

#[test]
fn exceptional_claim_label_expands_inside_c_if_fixture() {
    check_exceptional_claim_label_expansion("execute_splits_a_throwing_call_inside_a_c_if");
}

#[test]
fn exceptional_claim_label_expands_two_throwing_calls_fixture() {
    check_exceptional_claim_label_expansion(
        "grouped_proof_closes_claims_across_two_throwing_calls",
    );
}

#[test]
fn exceptional_claim_label_expands_grouped_outcomes_fixture() {
    check_exceptional_claim_label_expansion("grouped_proof_closes_normal_and_exceptional_claims");
}

#[test]
fn exceptional_claim_label_expands_routed_throw_fixture() {
    check_exceptional_claim_label_expansion("outcomes_routes_a_throw_that_leaves_the_function");
}

#[test]
fn exceptional_claim_labels_preserve_names_and_covering_proofs_in_projects() {
    let c_sources = [("helper.c", "int32 helper(int32 x) { return x; }")];
    for proof in [" by auto()", ""] {
        let source = format!(
            "verifying \"helper.c\"; int32 helper(int32 x) throws int32 {{ ensures result == x by auto(); exceptional ensures threw: exception == 7{proof}; }}"
        );
        let project = |source: &str| {
            ClickProject::new(
                "helper.click",
                [ClickModuleSource::new("helper.click", source, [])],
            )
        };
        let expanded = expand_project_claim_source_by_label(
            &project(&source),
            &ProgramInputs::Bundle(c_sources.to_vec()),
            "helper.threw",
        )
        .unwrap();
        assert_ne!(expanded, source);
        verify_c0_project(&project(&expanded), &c_sources).unwrap();
        expand_project_claim_source_by_label(
            &project(&source),
            &ProgramInputs::Bundle(c_sources.to_vec()),
            "helper.exceptional_ensures_0",
        )
        .expect_err("an explicitly named claim does not acquire a default label");
    }
}

#[test]
fn whole_function_expansion_validates_against_imported_pure_declarations() {
    let source = "import \"spec.click\"; verifying \"identity.c\"; int32 identity(int32 x) { ensures result == spec(x); } by { execute(); unfold(spec(x)); simp(); }";
    let project = ClickProject::new(
        "identity.click",
        [
            ClickModuleSource::new("identity.click", source, ["spec.click".to_owned()]),
            ClickModuleSource::new("spec.click", "function spec(x: int32) -> int32 { x }", []),
        ],
    );
    let sources = [("identity.c", "int32 identity(int32 x) { return x; }")];
    let expanded = expand_project_claim_source_by_label(
        &project,
        &ProgramInputs::Bundle(sources.to_vec()),
        "identity.contract",
    )
    .unwrap();
    verify_c0_project(&project.with_entry_source(&expanded), &sources).unwrap();
    let false_claim = expanded.replace("result == spec(x)", "result == spec(x) + 1");
    verify_c0_project(&project.with_entry_source(false_claim), &sources)
        .expect_err("import resolution must not bypass the expanded claim check");
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn loaded_struct_field_loop_expansion_names_fields_and_reverifies() {
    let (source, sources) =
        mdtest_sources("mdtests/loop_invariant_through_loaded_pointer_field.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    // The old whole-prefix search exhausted the ordinary 2,000,000-unit
    // allowance. Keep the repaired proof comfortably below it.
    crate::instrumentation::with_tactic_work_limits(
        crate::instrumentation::TacticWorkLimits {
            smart: 100_000,
            ..Default::default()
        },
        || verify_c0_sources(&source, &sources),
    )
    .unwrap();
    let expanded =
        expand_c0_claim_source_by_label(&source, &sources, "probe_contract.contract").unwrap();
    assert!(
        expanded.contains("at(statement(3).entry, j->lo)"),
        "{expanded}"
    );
    assert!(!expanded.contains("j[2..3]"), "{expanded}");
    crate::surface::proof::without_implicit_auto(|| verify_c0_sources(&expanded, &sources))
        .unwrap();
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn padded_struct_field_loop_expansion_reverifies() {
    let (source, sources) =
        mdtest_sources("mdtests/loop_invariant_through_padded_pointer_field.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    // The old whole-prefix search exhausted the ordinary 2,000,000-unit
    // allowance. Keep the repaired proof comfortably below it.
    crate::instrumentation::with_tactic_work_limits(
        crate::instrumentation::TacticWorkLimits {
            smart: 100_000,
            ..Default::default()
        },
        || verify_c0_sources(&source, &sources),
    )
    .unwrap();
    let expanded =
        expand_c0_claim_source_by_label(&source, &sources, "probe_contract.contract").unwrap();
    crate::surface::proof::without_implicit_auto(|| verify_c0_sources(&expanded, &sources))
        .unwrap();
}

#[test]
fn c_style_click_comments_preserve_loading_and_expansion_offsets() {
    let c_source = "int32 identity(int32 x) { return x; }";
    for (leading, inner, trailing) in [
        (
            "// ü } verifying \"fake.c\"\n",
            "// unmatched ' } \"\n",
            "// trailing '",
        ),
        (
            "/* ü } verifying \"fake.c\" */\n",
            "/* unmatched ' } \" */\n",
            "/* trailing ' */",
        ),
    ] {
        let source = format!(
            "{leading}verifying \"identity.c\";\nint32 identity(int32 x) {{\n ensures result == x;\n}} by {{\n execute(); {inner} simp();\n}}\n{trailing}"
        );
        assert_eq!(verifying_source_paths(&source).unwrap(), vec!["identity.c"]);
        let sources = [("identity.c", c_source)];
        verify_c0_sources(&source, &sources).unwrap();
        let offset = source.find("simp();").unwrap();
        let position = expansion::position_at_offset(&source, offset);
        let expanded =
            expand_c0_tactic_source_at(&source, &sources, position.line, position.column).unwrap();
        assert_eq!(&expanded[..offset], &source[..offset]);
        assert!(expanded.ends_with(trailing));
        verify_c0_sources(&expanded, &sources).unwrap();
    }
    let error = verifying_source_paths("\n /* missing close").unwrap_err();
    assert!(error.message().contains("unterminated block comment"));
}

fn empty_fold_difference_source() -> &'static str {
    r#"function marks(end: int32, value: int32) -> Integer {
 (0..end).fold(0, |acc, k| { acc + to_integer(value) })
}
theorem empty_difference(end: int32, x: int32, y: int32) {
 requires end <= 0;
 ensures marks(end, x) - marks(end, y) == 0 by {
  peel(marks(end, x)) using { end <= 0; }
  peel(marks(end, y)) using { end <= 0; }
  arithmetic() using { }
 }
}
theorem empty_product(end: int32, x: int32, y: int32, z: int32) {
 requires end <= 0;
 ensures marks(end, x) - marks(end, y) == (to_integer(y) - to_integer(z)) * marks(end, z) by {
  peel(marks(end, x)) using { end <= 0; }
  peel(marks(end, y)) using { end <= 0; }
  peel(marks(end, z)) using { end <= 0; }
  arithmetic() using { }
 }
}
"#
}

// Peeling the last fold must leave a checked spelling for arithmetic expansion.
#[test]
fn peeled_empty_fold_differences_keep_checked_integer_spelling() {
    let source = empty_fold_difference_source();
    verify_c0_sources(source, &[]).unwrap();
    for claim in ["empty_difference.ensures_0", "empty_product.ensures_0"] {
        let expanded = expand_c0_claim_source_by_label(source, &[], claim).unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
    }
}

#[test]
#[ignore = "nightly: empty-fold result mutation"]
fn peeled_empty_fold_differences_reject_nonzero_results() {
    let source = empty_fold_difference_source();
    let invalid = source.replace("marks(end, y) == 0 by", "marks(end, y) == 1 by");
    assert_ne!(invalid, source);
    let error = verify_c0_sources(&invalid, &[]).expect_err("false empty difference was accepted");
    assert!(
        !error.message().contains("budget exhausted"),
        "{}",
        error.message()
    );
}

fn empty_fold_order_source() -> &'static str {
    r#"function marks(end: int32) -> Integer {
 (0..end).fold(0, |acc, k| { acc + to_integer(k) })
}
theorem empty_order(end: int32) {
 requires end <= 0;
 ensures 0 <= marks(end) by {
  peel(marks(end)) using { end <= 0; }
  arithmetic() using { marks(end) == 0; }
 }
 ensures marks(end) <= 0 by {
  peel(marks(end)) using { end <= 0; }
  arithmetic() using { }
 }
}
"#
}

// A constant order after peeling must retain its relation at the conclusion,
// rather than print the generic equality certificate for Boolean truth.
#[test]
fn peeled_empty_fold_order_keeps_its_checked_conclusion() {
    let source = empty_fold_order_source();
    verify_c0_sources(source, &[]).unwrap();
    for claim in ["empty_order.ensures_0", "empty_order.ensures_1"] {
        let expanded = expand_c0_claim_source_by_label(source, &[], claim).unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
    }
}

#[test]
#[ignore = "nightly: empty-fold order and certificate mutations"]
fn peeled_empty_fold_order_rejects_false_comparisons() {
    let source = empty_fold_order_source();
    for (before, after) in [
        ("0 <= marks(end)", "1 <= marks(end)"),
        ("marks(end) <= 0", "marks(end) <= -1"),
    ] {
        let invalid = source.replacen(before, after, 1);
        assert_ne!(invalid, source);
        let error = verify_c0_sources(&invalid, &[]).expect_err("false empty order accepted");
        assert!(
            !error.message().contains("budget exhausted"),
            "{}",
            error.message()
        );
    }
    let expanded = expand_c0_claim_source_by_label(source, &[], "empty_order.ensures_0").unwrap();
    let invalid = expanded.replacen("trivial => 0 <= 0", "trivial => 0 == 0", 1);
    assert_ne!(invalid, expanded);
    assert!(
        verify_c0_sources(&invalid, &[]).is_err(),
        "changed conclusion relation accepted"
    );
}

// The arithmetic planner's affine sum is constant even though this goal
// retains signed subexpressions. Its generated Add node must still recheck.
#[test]
fn signed_bounded_subtraction_preserves_generated_child_sum() {
    let (source, sources) = mdtest_sources("mdtests/signed_arithmetic_bounded_subtraction.md");
    let borrowed = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let verified_for_expansion = verify_c0_sources(&source, &borrowed).unwrap();
    let expanded = expand_checked_grouped_claim(&source, &verified_for_expansion, "f").unwrap();
    let (result, planning) = crate::surface::proof::count_planning_statement_transitions(|| {
        verify_c0_sources(&expanded, &borrowed)
    });
    result.unwrap();
    assert_eq!(planning, 0, "expanded child sums must check without search");
}

#[test]
#[ignore = "nightly: whole-proof arithmetic mutations and certificate rechecks"]
fn signed_bounded_subtraction_refuses_false_or_undefined_sums() {
    let (source, sources) = mdtest_sources("mdtests/signed_arithmetic_bounded_subtraction.md");
    let borrowed = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    for invalid in [
        source.replace("(8 - x) <= (8 - x) + 4", "(8 - x) + 4 <= (8 - x)"),
        source.replace("requires 4 <= x;", ""),
        source.replace("requires x <= 8;", ""),
    ] {
        verify_c0_sources(&invalid, &borrowed)
            .expect_err("false or undefined subtraction must be refused");
    }
    let expanded = expand_c0_claim_source(&source, &borrowed, "f", CProofClaim::Grouped).unwrap();
    // Changing only the generated constant sum must not change the checked
    // children, even if its replacement is itself a true inequality.
    let forged = expanded.replacen("-4 <= 0", "-3 <= 0", 1);
    assert_ne!(forged, expanded, "expected the nonzero cancellation node");
    verify_c0_sources(&forged, &borrowed)
        .expect_err("a different generated child sum must be refused");
}

#[test]
fn algebraic_integer_match_bindings_expand_and_recheck() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/algebraic_integer_match_bindings.md");
    let markdown = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    verify_c0_sources(source, &[]).expect("Integer match fixture should verify");
    for name in [
        "preserves",
        "concrete",
        "nested_fields",
        "shadows",
        "captures",
        "swaps",
    ] {
        let label = format!("{name}.ensures_0");
        let expanded = expand_c0_claim_source_by_label(source, &[], &label)
            .unwrap_or_else(|error| panic!("{label} should expand: {}", error.message()));
        verify_c0_sources(&expanded, &[]).unwrap_or_else(|error| {
            panic!("{label} expansion should recheck: {}", error.message())
        });
    }
}

/// The Click line, 1-based, of the first line of `source` containing `text`.
fn line_containing(source: &str, text: &str) -> usize {
    source
        .lines()
        .position(|line| line.contains(text))
        .unwrap_or_else(|| panic!("no line contains `{text}`"))
        + 1
}

/// A loop phase written in a grouped proof's `loop` tactic is a claim of its
/// own: its label, and a line of its proof, select just that phase, and the
/// expansion replaces only the phase's `by` clause with its checked
/// certificate. The rest of the contract proof, including the other phase
/// and the `simp()` after the loop, is untouched.
#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn a_written_loop_phase_expands_alone_by_label_and_by_line() {
    let (click, sources) = mdtest_sources("mdtests/loop_entry_guard_before_written_implication.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let function = "loop_entry_guard_before_written_implication";
    let label = format!("{function}.loop(0).preserve");
    let expanded = expand_c0_claim_source_by_label(&click, &sources, &label).unwrap();
    // The written-out phase cites `click::machine_integer` theorems, so
    // expansion adds that import ahead of the otherwise unchanged source.
    let body = expanded
        .strip_prefix("import click::machine_integer;\n")
        .unwrap_or_else(|| panic!("expansion adds the cited import\n{expanded}"));
    let written = "preserve by simp();";
    let start = click.find(written).unwrap();
    let end = start + written.len();
    assert!(body.starts_with(&click[..start]), "{expanded}");
    assert!(body.ends_with(&click[end..]), "{expanded}");
    let phase = &body[start..body.len() - (click.len() - end)];
    assert!(phase.starts_with("preserve by {"), "{phase}");
    assert!(!phase.contains("simp"), "{phase}");
    verify_c0_sources(&expanded, &sources).unwrap();

    let inputs = ProgramInputs::Bundle(sources.clone());
    let at = |text: &str, scope| {
        claim_at(
            None,
            &click,
            &inputs,
            line_containing(&click, text),
            None,
            scope,
        )
        .unwrap()
    };
    let selected = at(written, ClaimLocationScope::Innermost);
    assert_eq!(selected.label, label);
    assert_eq!(selected.owner, function);
    assert_eq!(
        at("initialize by {", ClaimLocationScope::Innermost).label,
        format!("{function}.loop(0).initialize")
    );
    // A line of the phase inside the loop tactic, past its first line.
    assert_eq!(
        at("intro();", ClaimLocationScope::Innermost).label,
        format!("{function}.loop(0).initialize")
    );
    // The proof unit that checks the phase is the contract proof writing it,
    // which is what audit and proof tracing select, without verifying.
    assert_eq!(
        at(written, ClaimLocationScope::ProofUnit).label,
        format!("{function}.contract")
    );
    // The `loop` keyword's own line belongs to the contract proof.
    assert_eq!(
        at("loop {", ClaimLocationScope::Innermost).label,
        format!("{function}.contract")
    );
    let by_line = expand_claim_by_label(
        None,
        &click,
        &inputs,
        &selected.label,
        Some(selected.position),
    )
    .unwrap();
    assert_eq!(by_line.source, expanded);
    assert_eq!(by_line.proof_unit, format!("{function}.contract"));
}

const OMITTED_PHASE_C: &str = "int32 f(int32 a, int32 b) {
    while (a > 0) {
        a = 0;
        b = 0;
    }
    return a;
}
";

const OMITTED_PHASE_CLICK: &str = r#"verifying "omitted.c";

int32 f(int32 a, int32 b) {
    requires a <= 0;
    ensures result <= 0;
} by {
    loop {
        decreases a + 1;
        invariant a <= 0;
    }
    step();
    simp();
}
"#;

/// A `loop` tactic that writes neither phase leaves both to automation.
/// Expanding one by its label writes it out as an explicit phase proof in
/// the tactic's body, and changes nothing else.
#[test]
fn an_omitted_loop_phase_expands_to_an_explicit_phase_proof() {
    let sources = [("omitted.c", OMITTED_PHASE_C)];
    verify_c0_sources(OMITTED_PHASE_CLICK, &sources).unwrap();
    let insertion = OMITTED_PHASE_CLICK.find("}\n    step();").unwrap();
    for phase in ["initialize", "preserve"] {
        let expanded = expand_c0_claim_source_by_label(
            OMITTED_PHASE_CLICK,
            &sources,
            &format!("f.loop(0).{phase}"),
        )
        .unwrap();
        assert!(
            expanded.starts_with(&OMITTED_PHASE_CLICK[..insertion]),
            "{expanded}"
        );
        assert!(
            expanded.ends_with(&OMITTED_PHASE_CLICK[insertion..]),
            "{expanded}"
        );
        let inserted =
            &expanded[insertion..expanded.len() - (OMITTED_PHASE_CLICK.len() - insertion)];
        assert!(
            inserted.starts_with(&format!("    {phase} by {{\n")),
            "{inserted}"
        );
        assert!(inserted.ends_with("        }\n    "), "{inserted}");
        verify_c0_sources(&expanded, &sources).unwrap();
    }
    let error =
        expand_c0_claim_source_by_label(OMITTED_PHASE_CLICK, &sources, "f.loop(1).preserve")
            .unwrap_err();
    assert!(
        error
            .message()
            .contains("no `loop` tactic in `f`'s proofs proves loop(1)"),
        "{}",
        error.message()
    );
}

/// A loop phase is expanded by its label over compiler-prepared C exactly as
/// over a source bundle, through the prepared entry point and through the
/// input-generic one `click expand --claim` uses, and the rewrite checks
/// over the same prepared import.
#[test]
fn a_loop_phase_expands_by_label_over_a_prepared_c_import() {
    use crate::languages::c::compiler_import::PreparedCImport;

    let sources = [("omitted.c", OMITTED_PHASE_C)];
    let imports = [PreparedCImport::for_test("omitted.c", OMITTED_PHASE_C)];
    let inputs = ProgramInputs::Prepared(&imports);
    for phase in ["initialize", "preserve"] {
        let label = format!("f.loop(0).{phase}");
        let bundled = expand_c0_claim_source_by_label(OMITTED_PHASE_CLICK, &sources, &label)
            .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
        let prepared =
            expand_c0_prepared_claim_source_by_label(OMITTED_PHASE_CLICK, &imports, &label)
                .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
        assert_eq!(prepared, bundled, "{label}");
        let generic = expand_claim_by_label(None, OMITTED_PHASE_CLICK, &inputs, &label, None)
            .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
        assert_eq!(generic.source, bundled, "{label}");
        assert_eq!(generic.proof_unit, "f.contract", "{label}");
        verify_c0_prepared_sources(&prepared, &imports)
            .unwrap_or_else(|error| panic!("{label}: {}", error.message()));
    }
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn early_return_arms_transport_result_goals_from_function_exit() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/byte_representation_roundtrip.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source(source, &sources, "f", CProofClaim::Grouped).unwrap();
    // `result` does not exist at function entry. Each failure arm states
    // its `result` goal at function exit, where the arm has returned.
    assert!(!expanded.contains("at(function.entry"), "{expanded}");
    assert!(
        expanded.contains("transport(at(function.exit, result == 18 or result == -1)"),
        "{expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn guarded_resource_disjoint_store_and_unconditional_control_expand_and_recheck() {
    let c = r#"struct base { struct base* left; struct base* right; uint64 padding; };
struct cell { struct base base; int32 value; };
int32 f(struct cell* root) {
    struct base* child = root->base.left;
    int32 value = ((struct cell*)(void*)child)->value;
    root->value = value;
    return value;
}"#;
    let guarded = r#"verifying "guarded.c";
resource child_value(p: struct base*) {
    field number: int32;
    if p != 0 {
        owns ((struct cell*)(void*)p)->value;
        fact ((struct cell*)(void*)p)->value == number;
    }
}
int32 f(struct cell* root) {
    requires root != 0;
    views root->base.left;
    owns child: child_value(root->base.left);
    owns root->value;
    requires root->base.left != 0;
    requires root->base.left != (struct base*)(void*)root;
    ensures result == old(child.number);
    ensures child.number == old(child.number);
    ensures root->value == old(child.number);
} by {
    unfold(child);
    execute();
    fold(child);
    simp();
}"#;
    let control = guarded
        .replace("    if p != 0 {\n", "")
        .replace("    }\n}\nint32 f", "}\nint32 f");
    for proof in [guarded, control.as_str()] {
        verify_c0_sources(proof, &[("guarded.c", c)]).unwrap();
        let line = proof
            .lines()
            .position(|line| line.contains("execute();"))
            .unwrap()
            + 1;
        let expanded = expand_c0_tactic_source_at(proof, &[("guarded.c", c)], line, 5).unwrap();
        verify_c0_sources(&expanded, &[("guarded.c", c)]).unwrap();
    }
}

#[test]
fn unfolding_proof_bound_integer_arguments_expands_and_rechecks() {
    for (path, label) in [
        (
            "mdtests/unfold_function_after_integer_intro.md",
            "unfold_an_introduced_integer.ensures_0",
        ),
        (
            "mdtests/unfold_function_after_integer_obtain.md",
            "unfold_an_obtained_integer.ensures_0",
        ),
    ] {
        let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(path);
        let text = std::fs::read_to_string(&path).unwrap();
        let fixture = crate::cli::parse_mdtest(&path, &text).unwrap();
        let source = fixture
            .click_source
            .unwrap()
            .replace("unfold(black", "have d == d by auto(); unfold(black");
        verify_c0_sources(&source, &[]).unwrap();
        let expanded = expand_c0_claim_source_by_label(&source, &[], label).unwrap();
        verify_c0_sources(&expanded, &[]).unwrap();
    }
}

/// A step's written obligation proofs expand in place: each `requires` entry
/// keeps its proposition and prints its body's checked steps, the expansion
/// reverifies, and deleting an entry leaves its obligation unproved.
#[test]
fn step_requires_entries_expand_in_place_and_are_needed() {
    let c_source = r#"
        int32 first(int32 x, int32 y) {
            return x;
        }

        int32 caller(int32 a, int32 b) {
            return first(a, b);
        }
    "#;
    let click_source = r#"
verifying "pair.c";

function is_positive(value: int32) -> int32 { if value > 0 { 1 } else { 0 } }

int32 first(int32 x, int32 y) {
    requires is_positive(x) == 1 or is_positive(y) == 1;
    requires is_positive(y) == 1 or is_positive(x) == 1;
    ensures 1 == 1 by auto();
}

int32 caller(int32 a, int32 b) {
    requires a > 0;
    ensures 1 == 1 by {
        step() {
            requires is_positive(a) == 1 or is_positive(b) == 1 by {
                have is_positive(a) == 1 by {
                    unfold(is_positive(a)); normalize() using { a > 0; }
                }
                assumption();
            }
            requires is_positive(b) == 1 or is_positive(a) == 1 by {
                have is_positive(a) == 1 by {
                    unfold(is_positive(a)); normalize() using { a > 0; }
                }
                assumption();
            }
        }
        step();
        simp();
    }
}
"#;
    let c_sources = [("pair.c", c_source)];
    verify_c0_sources(click_source, &c_sources).expect("the written entries should verify");
    let expanded =
        expand_c0_claim_source(click_source, &c_sources, "caller", CProofClaim::Ensure(0))
            .expect("the step's entries should expand");
    assert!(
        expanded.contains("step() {")
            && expanded.contains("requires is_positive(a) == 1 or is_positive(b) == 1 by {")
            && expanded.contains("requires is_positive(b) == 1 or is_positive(a) == 1 by {")
            && !expanded.contains("by simp()"),
        "the expansion should keep both entries with checked bodies: {expanded}"
    );
    verify_c0_sources(&expanded, &c_sources).expect("the expansion should reverify");

    let second = expanded
        .find("requires is_positive(b) == 1 or is_positive(a) == 1 by {")
        .expect("the expansion keeps the second entry");
    let second_end = expanded[second..]
        .find("\n            }\n")
        .map(|offset| second + offset + "\n            }\n".len())
        .expect("the second entry's body closes");
    let mut without_second = expanded.clone();
    without_second.replace_range(second..second_end, "");
    let error = crate::surface::proof::without_implicit_auto(|| {
        verify_c0_sources(&without_second, &c_sources)
    })
    .expect_err("with the implicit `auto` off, deleting an entry leaves its obligation unproved");
    // Compare without grouping parentheses, which the diagnostic renderer may
    // or may not print around each disjunct.
    assert!(
        error
            .message()
            .replace(['(', ')'], "")
            .contains("is_positiveb == 1 or is_positivea == 1"),
        "the refusal should name the unproved obligation: {}",
        error.message()
    );
}

#[test]
fn a_bare_fold_expands_its_body_fact_proof_and_needs_it() {
    let c_source = "void make(int32 x, int32 y) { }\n";
    let click_source = r#"
verifying "make.c";
resource either(n: int32, m: int32) { fact n > 0 or m > 0; }
void make(int32 x, int32 y) {
    requires x > 0;
    produces either(x, y);
} by {
    fold(either(x, y));
    execute();
    simp();
}
"#;
    let c_sources = [("make.c", c_source)];
    let expanded = expand_c0_claim_source(click_source, &c_sources, "make", CProofClaim::Grouped)
        .expect("the bare fold should expand");
    assert!(
        expanded.contains("fold(either(x, y)) by {"),
        "the implicit `auto`'s proof of the open body fact should print as the fold's `by`: {expanded}"
    );
    crate::surface::proof::without_implicit_auto(|| verify_c0_sources(&expanded, &c_sources))
        .expect("the expansion should reverify cold");
    let start = expanded
        .find("fold(either(x, y)) by {")
        .expect("the expanded fold");
    let body_end = expanded[start..]
        .find("\n    }\n")
        .map(|offset| start + offset + "\n    }\n".len())
        .expect("the fold's `by` closes");
    let mut without_proof = expanded.clone();
    without_proof.replace_range(start..body_end, "fold(either(x, y));\n");
    let error = crate::surface::proof::without_implicit_auto(|| {
        verify_c0_sources(&without_proof, &c_sources)
    })
    .expect_err("with the implicit `auto` off, the fold refuses its unproved body fact");
    assert!(
        error
            .message()
            .replace(['(', ')'], "")
            .contains("x > 0 or y > 0"),
        "the refusal should name the body fact: {}",
        error.message()
    );
}

#[test]
fn a_bare_open_expands_its_close_proof_and_needs_it() {
    let c_source = "void set(int32* p, int32* q, int32 x) { p[0] = x; q[0] = 1; }\n";
    let click_source = r#"
verifying "set.c";
resource cell(p: int32*) { owns p[0..1]; fact p[0] > 0 or p[0] < -1; }
void set(int32* p, int32* q, int32 x) {
    requires x > 0;
    owns cell(p);
    owns q[0..1];
} by {
    open(cell(p)) { step(); }
    execute();
    simp();
}
"#;
    let c_sources = [("set.c", c_source)];
    let expanded = expand_c0_claim_source(click_source, &c_sources, "set", CProofClaim::Grouped)
        .expect("the bare open should expand");
    let start = expanded.find("open(cell(p)) {").expect("the expanded open");
    let by = start + expanded[start..].find("} by {").unwrap_or_else(|| {
        panic!(
            "the implicit `auto`'s proof of the close should print as the open's `by`: {expanded}"
        )
    });
    crate::surface::proof::without_implicit_auto(|| verify_c0_sources(&expanded, &c_sources))
        .expect("the expansion should reverify cold");
    let by_end = by
        + expanded[by..]
            .find("\n    }\n")
            .expect("the open's `by` closes");
    let mut without_proof = expanded.clone();
    without_proof.replace_range(by..by_end + "\n    }".len(), "}");
    let error = crate::surface::proof::without_implicit_auto(|| {
        verify_c0_sources(&without_proof, &c_sources)
    })
    .expect_err("with the implicit `auto` off, the close refuses its unproved body fact");
    assert!(
        error.message().contains("fold(cell(p))"),
        "the refusal should name the closing fold: {}",
        error.message()
    );
}

/// `expanded` with its first step's obligation proofs removed:
/// `step() by { ... }` or `step() { requires ... }` becomes `step();`.
fn without_first_step_obligation_proofs(expanded: &str) -> String {
    let start = ["step() by {", "step() {"]
        .iter()
        .filter_map(|head| expanded.find(head))
        .min()
        .unwrap_or_else(|| panic!("an expanded step with obligation proofs: {expanded}"));
    let open = start
        + expanded[start..]
            .find('{')
            .expect("the proofs open a block");
    let mut depth = 0usize;
    let mut close = None;
    for (offset, character) in expanded[open..].char_indices() {
        match character {
            '{' => depth += 1,
            '}' => {
                depth -= 1;
                if depth == 0 {
                    close = Some(open + offset);
                    break;
                }
            }
            _ => {}
        }
    }
    let close = close.expect("the proofs close their block");
    format!("{}step();{}", &expanded[..start], &expanded[close + 1..])
}

#[test]
#[ignore = "nightly: checks whole global object ownership through expansion and retained verification"]
fn whole_global_objects_keep_their_extent_and_field_types() {
    let (source, sources) =
        mdtest_sources("mdtests/whole_global_struct_covers_addressed_object.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    for source in [
        source.clone(),
        source
            .replace(
                "verifying \"whole_global.c\";",
                "verifying \"whole_global.c\" as unit;",
            )
            .replace("owns state;", "owns unit::state;"),
    ] {
        verify_c0_sources(&source, &sources).unwrap();
        let expanded =
            expand_c0_claim_source(&source, &sources, "set_global", CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources).unwrap();
        let position = expansion::position_at_offset(
            &expanded,
            expanded.find("ensures result == 18u64").unwrap(),
        );
        let (session, _) = C0VerificationSession::new(&source, &sources).unwrap();
        session
            .verify_at(&expanded, position.line, position.column)
            .unwrap();
    }
    let missing = source.replace("owns state;", "");
    let error = verify_c0_sources(&missing, &sources).unwrap_err();
    assert!(
        error
            .message()
            .contains("missing resource fact `owns state`"),
        "{error:?}"
    );
    for insufficient in ["views state;", "owns state.left;"] {
        assert!(verify_c0_sources(&source.replace("owns state;", insufficient), &sources).is_err());
    }
}

/// Qualified pointer slots must select the same memory in fresh, expanded,
/// and retained proofs, including entry reads after a store.
#[test]
#[ignore = "nightly: checks global and static pointer snapshots across proof modes"]
fn qualified_pointer_slots_keep_selected_memory_in_all_proof_modes() {
    for (fixture, functions) in [
        (
            "mdtests/qualified_pointer_global_store_reads_current_value.md",
            &["clear_slot"][..],
        ),
        (
            "mdtests/qualified_pointer_global_store_keeps_old_snapshot.md",
            &["exchange_global", "exchange_static"][..],
        ),
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        let verified_for_expansion = verify_c0_sources(&source, &sources).unwrap();
        for (function, expanded) in expand_checked_grouped_claims(
            &source,
            &verified_for_expansion,
            functions.iter().copied(),
        ) {
            verify_c0_sources(&expanded, &sources).unwrap();
            let offset = expanded.find(&format!("{function}(")).unwrap();
            let claim = offset + expanded[offset..].find("ensures ").unwrap();
            let position = expansion::position_at_offset(&expanded, claim);
            let (session, _) = C0VerificationSession::new(&source, &sources).unwrap();
            session
                .verify_at(&expanded, position.line, position.column)
                .unwrap();
        }
        let without_slot = source
            .lines()
            .filter(|line| !line.trim_start().starts_with("owns "))
            .collect::<Vec<_>>()
            .join("\n");
        assert!(
            verify_c0_sources(&without_slot, &sources).is_err(),
            "a pointer read requires its slot permission"
        );
    }
}

#[test]
#[ignore = "nightly: checks global field coverage through expansion and retained verification"]
fn whole_object_call_effects_combine_global_fields_in_all_proof_modes() {
    let (source, sources) =
        mdtest_sources("mdtests/whole_object_call_effect_combines_global_fields.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let (session, verified_for_expansion) = C0VerificationSession::new(&source, &sources).unwrap();
    let expanded =
        expand_checked_grouped_claim(&source, &verified_for_expansion, "caller").unwrap();
    let position =
        expansion::position_at_offset(&expanded, expanded.find("owns unit::state.left;").unwrap());

    session
        .verify_at(&expanded, position.line, position.column)
        .unwrap();
    drop(session);
    verify_c0_sources(&expanded, &sources).unwrap();

    for missing in ["", "views unit::state.right;"] {
        assert!(
            verify_c0_sources(
                &source.replace("owns unit::state.right;", missing),
                &sources
            )
            .is_err()
        );
    }
}

/// Keep the original rotation's imported struct-pointer/model applications
/// through a selected smart-tactic expansion and a retained project session.
#[test]
#[ignore = "nightly: full rotation theorem across fresh, expanded, and retained proofs"]
fn returned_struct_pointer_lemmas_survive_expansion_and_retained_verification() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let fixture = root.join("tests/fixtures/proof-expansion/rbtree-return-pointer-lemma.click");
    let (source, project, inputs) = crate::cli::load_sidecar_inputs(&fixture, Some(root)).unwrap();
    let crate::cli::CInput::Bundle(sources) = inputs else {
        panic!("the original C reproduction uses source-bundle inputs");
    };
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    verify_c0_project(&project, &sources).unwrap();
    let position = expansion::position_at_offset(&source, source.rfind("simp();").unwrap());
    let expanded = expand_project_tactic_source_at(
        &project,
        &ProgramInputs::Bundle(sources.clone()),
        position.line,
        position.column,
    )
    .unwrap();
    assert_eq!(expanded.matches("apply(sized_parent_is_shape(").count(), 8);
    verify_c0_project(&project.with_entry_source(expanded.clone()), &sources).unwrap();
    let claim = expansion::position_at_offset(
        &expanded,
        expanded
            .find("ensures RotateTreeLeft(&sized_rotate)")
            .unwrap(),
    );
    let (session, _) = C0VerificationSession::new_project(&project, &sources).unwrap();
    session
        .verify_at_project(&expanded, claim.line, claim.column)
        .unwrap();
}

#[test]
fn claim_expansion_that_adds_a_library_import_rechecks_in_its_session() {
    // The written-out certificate cites a `machine_integer` theorem, so
    // expansion adds its import. Only the proof changed; the session must
    // recheck it rather than report a change outside the proof unit.
    let source = r#"verifying "caller.c";

int32 clamp(int32 x) {
    ensures 0 <= result and result <= 100;
} by { execute(); simp(); }

int32 caller(int32 x) {
    ensures 1 <= result and result <= 101;
} by { execute(); simp(); }
"#;
    let sources = [(
        "caller.c",
        "int32 clamp(int32 x) {\n    if (x < 0) {\n        return 0;\n    }\n    if (x > 100) {\n        return 100;\n    }\n    return x;\n}\n\nint32 caller(int32 x) {\n    return clamp(x) + 1;\n}\n",
    )];
    let expanded =
        expand_c0_claim_source(source, &sources, "caller", CProofClaim::Grouped).unwrap();
    assert!(
        expanded.starts_with("import click::machine_integer;\n"),
        "{expanded}"
    );
    let position = expansion::position_at_offset(&expanded, expanded.rfind("ensures").unwrap());
    let (session, _) = C0VerificationSession::new(source, &sources).unwrap();
    session
        .verify_at(&expanded, position.line, position.column)
        .unwrap();
    let changed = expanded.replace("result <= 100;", "result <= 99;");
    let error = session
        .verify_at(&changed, position.line, position.column)
        .unwrap_err();
    assert!(
        error
            .to_string()
            .contains("outside the selected proof unit"),
        "{error}"
    );
}

#[test]
#[ignore = "nightly: checks byte-field ownership through expansion and retained verification"]
fn whole_struct_byte_fields_reassemble_in_all_proof_modes() {
    for fixture in [
        "mdtests/whole_struct_reassembles_from_byte_fields.md",
        "mdtests/whole_struct_reassembles_from_padded_byte_field.md",
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        let (session, verified_for_expansion) =
            C0VerificationSession::new(&source, &sources).unwrap();
        let expanded =
            expand_checked_grouped_claim(&source, &verified_for_expansion, "mixed_fields").unwrap();
        let position =
            expansion::position_at_offset(&expanded, expanded.find("owns p->a;").unwrap());

        session
            .verify_at(&expanded, position.line, position.column)
            .unwrap();
        drop(session);
        verify_c0_sources(&expanded, &sources).unwrap();
        let field_clause = if source.contains("owns p->f;") {
            "owns p->f;"
        } else {
            "owns p->c;"
        };
        for replacement in [String::new(), field_clause.replace("owns", "views")] {
            assert!(
                verify_c0_sources(&source.replace(field_clause, &replacement), &sources).is_err()
            );
        }
    }
}

#[test]
#[ignore = "nightly: callback read across fresh, expanded, and retained proofs"]
fn callback_reads_keep_the_initialized_target_contract_in_all_proof_modes() {
    let (source, sources) =
        mdtest_sources("mdtests/function_pointer_read_uses_checked_address_equality.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let (session, verified_for_expansion) = C0VerificationSession::new(&source, &sources).unwrap();
    let expanded =
        expand_checked_grouped_claim(&source, &verified_for_expansion, "symbolic").unwrap();
    let position =
        expansion::position_at_offset(&expanded, expanded.rfind("ensures true;").unwrap());

    session
        .verify_at(&expanded, position.line, position.column)
        .unwrap();
    drop(session);
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
#[ignore = "nightly: unknown-pointer bounds across fresh, expanded, and retained proofs"]
fn unknown_pointer_bounds_survive_expansion_and_retained_verification() {
    for (fixture, claim, postcondition) in [
        (
            "mdtests/unknown_pointer_formation_keeps_zero_offsets_one_past_and_full_aliases.md",
            "alias.contract",
            "ensures result == q + 1;",
        ),
        (
            "mdtests/an_allocation_supplies_formation_bounds_without_read_authority.md",
            "field.contract",
            "ensures result == &p->second;",
        ),
        (
            "mdtests/loop_entry_memory_capture_cursor.md",
            "cursor.contract",
            "ensures result == 0;",
        ),
        (
            "mdtests/member_pointers_stay_usable_inside_their_subobject.md",
            "nested.contract",
            "ensures result == o->inner.second;",
        ),
        (
            "mdtests/native_bounds_survive_refolding_their_memory_resource.md",
            "end.contract",
            "ensures result == p + n;",
        ),
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        let (session, verified) = C0VerificationSession::new(&source, &sources).unwrap();
        let expanded = expand_verified_function_claim_source_by_label(&source, &verified, claim)
            .unwrap()
            .expect("the verified function claim is declared in this fixture");
        let position =
            expansion::position_at_offset(&expanded, expanded.find(postcondition).unwrap());
        session
            .verify_at(&expanded, position.line, position.column)
            .unwrap();
        let hostile = source
            .contains("requires p == q;")
            .then(|| source.replace("requires p == q;", "requires address(p) == address(q);"));
        if let Some(hostile) = &hostile {
            let position =
                expansion::position_at_offset(hostile, hostile.find(postcondition).unwrap());
            assert!(
                session
                    .verify_at(hostile, position.line, position.column)
                    .is_err()
            );
        }
        // Finish retained checks before cold verification resets kernel tables.
        drop(session);
        verify_c0_sources(&expanded, &sources).unwrap();
        if let Some(hostile) = hostile {
            assert!(verify_c0_sources(&hostile, &sources).is_err());
        }
    }
}

#[test]
#[ignore = "nightly: packed-pointer contracts across fresh, expanded, and retained proofs"]
fn packed_pointer_cast_contracts_survive_expansion_and_retained_verification() {
    for (fixture, claim, postcondition) in [
        (
            "mdtests/a_saved_pointer_link_keeps_its_bounds_through_an_outer_alias_update.md",
            "caller.contract",
            "ensures p->left == old(root->left->left);",
        ),
        (
            "mdtests/a_bounded_native_word_tag_can_precede_its_pointer.md",
            "stamp.ensures_0",
            "ensures ((int32*)(slot->word & ~3)) == p;",
        ),
        (
            "mdtests/a_checked_low_tag_add_preserves_an_incoming_word_relationship.md",
            "blacken.ensures_0",
            "ensures ((struct node*)(result & ~3)) == old((struct node*)(word & ~3));",
        ),
        (
            "mdtests/a_bounded_variable_tag_keeps_a_stored_pointer_relationship.md",
            "stamp.ensures_0",
            "ensures ((int32*)(slot->word & ~3)) == p;",
        ),
        (
            "mdtests/a_bounded_variable_tag_preserves_an_incoming_word_relationship.md",
            "recolor.ensures_0",
            "ensures ((struct node*)(result & ~3)) == old((struct node*)(word & ~3));",
        ),
        (
            "mdtests/tagged_pointer_from_field_fact.md",
            "parent_value.ensures_0",
            "ensures result == next->value;",
        ),
        (
            "mdtests/a_cast_contract_crosses_a_call_with_an_explicit_postcondition.md",
            "read_packed.ensures_0",
            "ensures result == p->value;",
        ),
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        let (session, verified) = C0VerificationSession::new(&source, &sources).unwrap();
        let expanded = expand_verified_function_claim_source_by_label(&source, &verified, claim)
            .unwrap()
            .expect("the verified function claim is declared in this fixture");
        let position =
            expansion::position_at_offset(&expanded, expanded.find(postcondition).unwrap());
        session
            .verify_at(&expanded, position.line, position.column)
            .unwrap();
        drop(session);
        verify_c0_sources(&expanded, &sources).unwrap();
    }
}

#[test]
#[ignore = "nightly: array-bound call across expansion and retained verification"]
fn call_step_keeps_snapshot_bound_through_expansion_and_retained_check() {
    let (source, sources) = mdtest_sources("mdtests/call_step_retains_old_array_bound.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let (session, verified) = C0VerificationSession::new(&source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(&source, &verified, "probe").unwrap();
    let position =
        expansion::position_at_offset(&expanded, expanded.find("ensures result >= 0;").unwrap());
    session
        .verify_at(&expanded, position.line, position.column)
        .unwrap();
    drop(session);
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
fn terminal_model_match_in_open_keeps_expanded_outcome_steps_in_its_arms() {
    let (click, sources) = mdtest_sources("mdtests/open_scope_model_match_terminal.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source_by_label(&click, &sources, "read.contract").unwrap();
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    let open = expanded
        .find("open(table")
        .expect("the resource scope is retained");
    let first = expanded[open..].find("Pair::First(value) =>").unwrap() + open;
    let second = expanded[first..].find("Pair::Second(value) =>").unwrap() + first;
    assert!(
        expanded[first..second].contains("model: Pair::First(value)"),
        "{expanded}"
    );
    assert!(
        expanded[second..].contains("model: Pair::Second(value)"),
        "{expanded}"
    );
    assert!(
        !expanded.contains("if match c.model"),
        "arm suffixes escaped their lexical match: {expanded}"
    );
}

#[test]
fn rejoined_model_match_in_open_expands_without_moving_the_continuation_inside() {
    let (click, sources) = mdtest_sources("mdtests/open_scope_model_match_rejoins.md");
    let sources = sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source_by_label(&click, &sources, "read.contract").unwrap();
    verify_c0_sources(&expanded, &sources)
        .unwrap_or_else(|error| panic!("{}\n{expanded}", error.message()));
    assert_eq!(expanded.matches("open(table").count(), 2, "{expanded}");
    assert!(
        expanded.contains("ensuring"),
        "the nonterminal match must retain its interface: {expanded}"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/tests/expansion_tests.rs");
}

#[test]
fn retained_project_recheck_ignores_shifted_import_positions_but_checks_paths() {
    let source = r#"import "helper.click";
theorem selected(x: int32) { ensures x == x by { normalize(); } }
theorem untouched() { ensures 1 == 1 by { normalize(); } }
"#;
    let project = ClickProject::new(
        "main.click",
        [
            ClickModuleSource::new("main.click", source, ["helper.click".to_owned()]),
            ClickModuleSource::new("helper.click", "spec enum Helper { Empty }", []),
        ],
    );
    let expanded = format!("import click::integer;\n{source}");
    let position = expansion::position_at_offset(&expanded, expanded.find("ensures x").unwrap());
    let (session, _) = C0VerificationSession::new_project(&project, &[]).unwrap();
    session
        .verify_at_project(&expanded, position.line, position.column)
        .expect("an added library import only shifts the file import's source position");
    let changed_contract = expanded.replace("ensures 1 == 1", "ensures 1 == 2");
    assert!(
        session
            .verify_at_project(&changed_contract, position.line, position.column)
            .unwrap_err()
            .to_string()
            .contains("outside the selected proof unit")
    );
    let changed_path = expanded.replace("helper.click", "other.click");
    assert!(
        session
            .verify_at_project(&changed_path, position.line, position.column)
            .is_err(),
        "a changed import path must still be rejected"
    );
}

#[test]
#[ignore = "nightly: string resource expansion and retained rechecking"]
fn expanded_string_witness_preserves_its_qualified_resource_module() {
    let (source, sources) = mdtest_sources("mdtests/cstr_readable_witness_stated_before_call.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let (session, verified) = C0VerificationSession::new(&source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(&source, &verified, "fixed_string_length").unwrap();
    assert!(expanded.contains("import click::cstr;"), "{expanded}");
    let at = expansion::position_at_offset(&expanded, expanded.find("ensures result").unwrap());
    session.verify_at(&expanded, at.line, at.column).unwrap();
    let changed = expanded.replace("ensures result == 2u64", "ensures result == 1u64");
    assert!(session.verify_at(&changed, at.line, at.column).is_err());
    drop(session);
    parse(&expanded).expect("the written resource must resolve without implicit C call imports");
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
#[ignore = "nightly: signed byte conditions across fresh, expanded, and retained proofs"]
fn known_unsigned_byte_decides_signed_comparison_in_all_proof_modes() {
    for (fixture, function) in [
        ("known_byte_decides_signed_char_comparison", "first_is_nul"),
        (
            "known_byte_decides_signed_char_comparison_cstr",
            "terminator",
        ),
    ] {
        let (source, sources) = mdtest_sources(&format!("mdtests/{fixture}.md"));
        let sources = sources
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        let (session, verified_for_expansion) =
            C0VerificationSession::new(&source, &sources).unwrap();
        let expanded =
            expand_checked_grouped_claim(&source, &verified_for_expansion, function).unwrap();
        let position = expansion::position_at_offset(
            &expanded,
            expanded.find("ensures result == 1;").unwrap(),
        );

        session
            .verify_at(&expanded, position.line, position.column)
            .unwrap();
        drop(session);
        verify_c0_sources(&expanded, &sources).unwrap();
    }
}

#[test]
#[ignore = "nightly: modular buffer ranges across fresh, expanded, and retained proofs"]
fn modular_buffer_ranges_rejoin_in_all_proof_modes() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let (source, sources) =
        mdtest_sources("mdtests/modular_buffer_ranges_rejoin_after_field_preserving_calls.md");
    let mut cases = vec![(source, sources, "probe")];
    for (project, sidecar, function) in [
        (
            "owned-segmented-buffer",
            "owned_segmented_buffer.click",
            "owned_segmented_buffer_pipeline",
        ),
        (
            "owned-split-buffer",
            "owned_split_buffer.click",
            "owned_split_buffer_pipeline",
        ),
    ] {
        let path = manifest.join("examples").join(project).join(sidecar);
        let source = std::fs::read_to_string(&path).unwrap();
        let sources = crate::cli::read_verifying_sources(&path, &source).unwrap();
        cases.push((source, sources, function));
    }
    for (source, sources, function) in cases {
        let sources = crate::cli::source_refs(&sources);

        let expanded = expand_c0_claim_source(&source, &sources, function, CProofClaim::Grouped)
            .unwrap_or_else(|error| panic!("{function}: {}", error.report()));
        verify_expanded_function_source(&source, &expanded, &sources, function)
            .unwrap_or_else(|error| panic!("expanded {function}: {}", error.report()));
        let position = expansion::c0_tactic_source_position(
            &expanded,
            &sources,
            &format!("{function}.contract"),
            0,
        )
        .unwrap();
        // Construction cold-verifies the complete original source before
        // capturing its baseline. It supplies the original positive check
        // once; all cold expansion checks stay before this retained session.
        let (session, original) = C0VerificationSession::new(&source, &sources).unwrap();
        assert!(
            original
                .iter()
                .any(|proof| proof.function_block.signature().name() == function)
        );
        session
            .verify_at(&expanded, position.line, position.column)
            .unwrap_or_else(|error| panic!("retained {function}: {}", error.report()));
    }
}

#[test]
#[ignore = "nightly: repeated-retain whole-proof and four selected-call expansions took 11.4s in parallel"]
fn repeated_retains_expand_with_checked_count_bounds() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/repeated_child_retains_keep_the_entry_count_bound.md");
    let markdown = std::fs::read_to_string(&path).unwrap();
    let fixture = crate::cli::parse_mdtest(&path, &markdown).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let sources = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &sources).expect("the four original retain calls verify");
    let expanded = expand_c0_claim_source(source, &sources, "retain_many", CProofClaim::Grouped)
        .expect("retain bounds should expand as checked obligation proofs");
    verify_expanded_function_source(source, &expanded, &sources, "retain_many")
        .expect("the expanded retain proof rechecks");
    for (offset, _) in source.match_indices("step(child_retain(obj), {});") {
        let position = expansion::position_at_offset(source, offset);
        let expanded = expand_c0_tactic_source_at(source, &sources, position.line, position.column)
            .expect("each retained call's implicit proof should expand");
        verify_expanded_function_source(source, &expanded, &sources, "retain_many")
            .expect("the selected call expansion rechecks");
    }
}

#[test]
fn branch_arm_source_selection_and_batch_expansion_follow_the_interface_rule() {
    let c = [(
        "split.c",
        "int32 split(int32 x) { if (x > 0) { x = 1; } else { x = 2; } return 0; }",
    )];
    for head in ["branch", "branch ensuring { fact x >= 1; } then"] {
        let source = format!(
            "verifying \"split.c\";
            int32 split(int32 x) {{ ensures result == 0; }} by {{
                {head} {{
                    step();
                    have x >= 1 by {{ simp(); }}
                }} else {{
                    step();
                    have x >= 1 by {{ simp(); }}
                }}
                step();
                simp();
            }}"
        );
        verify_c0_sources(&source, &c).unwrap();
        let positions = source
            .match_indices("simp();")
            .map(|(offset, _)| expansion::position_at_offset(&source, offset))
            .collect::<Vec<_>>();
        for position in &positions {
            let expanded =
                expand_c0_tactic_source_at(&source, &c, position.line, position.column).unwrap();
            verify_c0_sources(&expanded, &c).unwrap();
        }
        let batch = expand_c0_tactics_source_at(&source, &c, &positions).unwrap();
        verify_c0_sources(&batch.source, &c).unwrap();
    }
}

#[test]
fn address_only_model_constructor_cast_expands_and_checks() {
    let (source, c) = mdtest_sources("mdtests/model_pointer_address_constructor_preserves_cast.md");
    let c = c
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source(&source, &c, "caller", CProofClaim::Grouped)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    verify_c0_sources(&expanded, &c).unwrap_or_else(|error| panic!("{}", error.message()));
}

#[test]
fn address_only_model_implicit_view_expands_and_checks() {
    let (source, c) =
        mdtest_sources("mdtests/model_pointer_address_constructor_preserves_implicit_view.md");
    let c = c
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source(&source, &c, "caller", CProofClaim::Grouped)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    verify_c0_sources(&expanded, &c).unwrap_or_else(|error| panic!("{}", error.message()));
}

#[test]
fn void_pointer_helper_selected_view_expands_and_checks() {
    let (source, c) =
        mdtest_sources("mdtests/model_pointer_void_helper_preserves_selected_view.md");
    let c = c
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c0_claim_source(&source, &c, "keep", CProofClaim::Grouped)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    verify_c0_sources(&expanded, &c).unwrap_or_else(|error| panic!("{}", error.message()));
}

#[test]
fn tidied_expansion_closers_prove_normalized_claims_in_goal_order() {
    let original = "int32 f() {\n    ensures result == 0;\n} by {\n    step();\n}\n";
    let expanded = "int32 f() {\n    ensures result == 0;\n} by {\n    step();\n    have result == 0 by {\n        normalize();\n    }\n    have p == q by {\n        assumption();\n    }\n    have r == s by {\n        normalize();\n    }\n    assumption();\n    assumption();\n    assumption();\n    assumption();\n}\n";
    assert_eq!(
        tidy_expansion_closers(original, expanded).as_deref(),
        Some(
            "int32 f() {\n    ensures result == 0;\n} by {\n    step();\n    have p == q by {\n        assumption();\n    }\n    assumption();\n    normalize();\n    assumption();\n    normalize();\n}\n"
        )
    );
}

#[test]
fn tidied_expansion_closers_leave_other_closers_alone() {
    let original = "f by {\n    step();\n}\n";
    // Fewer closers than claims.
    let short = "f by {\n    have a by {\n        normalize();\n    }\n    have b by {\n        normalize();\n    }\n    assumption();\n}\n";
    // A closer run that does not end its block.
    let continued =
        "f by {\n    have a by {\n        normalize();\n    }\n    assumption();\n    step();\n}\n";
    // No claim proved by `normalize();` alone.
    let simplified = "f by {\n    have a by {\n        simp();\n    }\n    assumption();\n}\n";
    for expanded in [short, continued, simplified] {
        assert_eq!(
            tidy_expansion_closers(original, expanded),
            None,
            "{expanded}"
        );
    }
    // Text the expansion left as it was is never rewritten.
    let written = "f by {\n    have a by {\n        normalize();\n    }\n    assumption();\n}\n";
    assert_eq!(tidy_expansion_closers(written, written), None);
}

#[test]
#[ignore = "nightly: original C fixture expansion and checking take 0.9s"]
fn integer_count_authority_retirement_expands_and_rechecks() {
    let (source, sources) =
        mdtest_sources("mdtests/an_integer_count_equality_retires_its_authority.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let verified = verify_c0_sources(&source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(&source, &verified, "pool_destroy").unwrap();
    without_implicit_auto(|| verify_c0_sources(&expanded, &sources)).unwrap();
}

/// A structural `both` numbers as one claim-level tactic; the smart tactics
/// in its arms are selected at their own locations and expand the claim
/// that owns them.
#[test]
fn arithmetic_in_each_both_arm_is_selected_at_its_location() {
    let source = "theorem pair(a: Integer, b: Integer) {
 requires 0 <= a;
 requires 0 <= b;
 ensures 0 <= a and 0 <= b by {
  both {
   arithmetic() using { 0 <= a; };
  } and {
   arithmetic() using { 0 <= b; };
  }
 }
}
";
    verify_click_theorems(source).unwrap();
    for premise in ["0 <= a;", "0 <= b;"] {
        let written = format!("arithmetic() using {{ {premise} }}");
        let at = expansion::position_at_offset(source, source.find(&written).unwrap());
        let expanded = expand_c0_tactic_source_at(source, &[], at.line, at.column)
            .unwrap_or_else(|error| panic!("{premise}: {}", error.message()));
        assert!(!expanded.contains(&written), "{expanded}");
        verify_click_theorems(&expanded).unwrap();
    }
    let requirement =
        expansion::position_at_offset(source, source.find("requires 0 <= a").unwrap());
    let error = expand_c0_tactic_source_at(source, &[], requirement.line, requirement.column)
        .expect_err("a requirement is no smart tactic");
    assert!(
        error
            .message()
            .contains("no smart tactic's source contains this location"),
        "{}",
        error.message()
    );
}

#[test]
fn signed_loop_certificate_keeps_its_native_type_in_integer_default_source() {
    let (source, inputs) =
        mdtest_sources("mdtests/signed_loop_certificate_keeps_its_native_type.md");
    let sources = inputs
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let verified = verify_c0_sources(&source, &sources).unwrap();
    let expanded = expand_checked_grouped_claim(&source, &verified, "f").unwrap();
    without_implicit_auto(|| verify_c0_sources(&expanded, &sources))
        .expect("generated sums retain their native int32 type after parsing");
}
