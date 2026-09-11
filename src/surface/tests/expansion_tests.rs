use super::*;

#[test]
fn integer_quantifier_smart_proofs_expand_and_recheck() {
    let source = r#"
theorem integer_forall_simp() {
    ensures ordered: forall (z: Integer) { z + 1 > z } by { simp(); }
}
theorem integer_exists_simp(x: Integer) {
    ensures witnessed: exists (z: Integer) { z == x } by {
        witness(z = x);
        simp();
    }
}
theorem integer_forall_logical_simp() {
    ensures logical: forall (z: Integer) { z == z and z == z } by { simp(); }
}
theorem integer_exists_choose() {
    requires exists (z: Integer) { z == z };
    ensures chosen: exists (k: Integer) { k == k } by {
        choose(candidate from requirement 0);
        witness(k = candidate);
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
                expanded.contains("integer_certificate"),
                "{label}: {expanded}"
            );
        } else if label.ends_with("witnessed") {
            assert!(expanded.contains("normalize();"), "{label}: {expanded}");
        } else if label.ends_with("logical") {
            assert!(expanded.contains("intro();"), "{label}: {expanded}");
            assert!(expanded.contains("both {"), "{label}: {expanded}");
        } else {
            assert!(
                expanded.contains("choose(candidate from requirement 0);"),
                "{label}: {expanded}"
            );
            assert!(
                expanded.contains("witness(k = candidate);"),
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
    requires candidate: exists (z: Integer) {
        z == to_integer(if value > 0 { value } else { value + 1 })
    };
    ensures branched: exists (k: Integer) {
        k == to_integer(if value > 0 { value } else { value + 1 })
    } by {
        choose(candidate from requirement 1);
        witness(k = candidate);
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
        witness(z = 0);
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
        witness(z = 0);
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
    requires loadable(a[0..1]);
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
    verify_c0_sources(click_source, &sources)
        .expect("the array range-fold append contract should verify");
    let expanded = expand_c0_claim_source_by_label(
        click_source,
        &sources,
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
        witness(z = 0);
        both {
            both {
                both { simp(); } and { simp(); }
            } and {
                both { assumption(); } and {
                    both { simp(); } and {
                        both { simp(); } and { assumption(); }
                    }
                }
            }
        } and {
            rewrite(values[0] == 0);
            simp();
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
            "mathematical Integer expressions cannot be compared with C values",
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
            "expected a specification-side Integer expression",
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
            "Integer initializer has unproved evaluation obligations",
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

#[test]
fn context_free_disjunction_simp_expands_choice_and_rechecks() {
    for (goal, choice) in [
        ("1 == 1 or 2 == 3", "left();"),
        ("2 == 3 or 1 == 1", "right();"),
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
        let wrong_choice = if choice == "left();" {
            expanded.replacen("left();", "right();", 1)
        } else {
            expanded.replacen("right();", "left();", 1)
        };
        verify_c0_sources(&wrong_choice, &[])
            .expect_err("changing the retained disjunct choice must invalidate the proof");
    }
}

#[test]
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
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
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
    });
}

#[test]
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
    verify_c0_sources(source, &sources).unwrap();
    let expanded =
        expand_c0_claim_source(source, &sources, "invoke", CProofClaim::Grouped).unwrap();
    verify_c0_sources(&expanded, &sources).unwrap();
}

#[test]
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
        let sources = fixture
            .c_sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        verify_c0_sources(source, &sources)
            .unwrap_or_else(|error| panic!("{fixture_name}: {}", error.message()));
        for function in functions {
            let expanded =
                expand_c0_claim_source(source, &sources, function, CProofClaim::Grouped).unwrap();
            verify_c0_sources(&expanded, &sources)
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
        "open(reference(obj)) { execute(); } simp();",
    ] {
        let source = format!(
            r#"
resource reference(obj: struct object*) {{
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
    assert!(expanded.contains("arithmetic() using"), "{expanded}");
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
int read_cell(int *p) {{ consumes cell(p); produces cell(p); ensures result == old(p[0]); }} {helper}
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
    requires loadable(p[0..2]); consumes pair(p); produces pair(p);
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
        let duplicate =
            click_source.replace("consumes pair(p);", "consumes pair(p); consumes pair(p);");
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
    requires loadable(p[0..2]); consumes pair(p); produces pair(p);
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
    requires loadable(p[0..1]); consumes p[0..1]; produces p[0..1];
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
    ensures loadable(result[0..5]);
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
fn source_locator_ignores_hash_comments_and_preserves_literals() {
    let source =
        "# Click's ü } verifying \"fake.c\"\r\nverifying \"real#file.c\"; # \"unterminated";
    assert_eq!(
        verifying_source_paths(source).expect("comments must not become source tokens"),
        vec!["real#file.c"]
    );
}

#[test]
fn source_locator_hash_comments_preserve_proof_expansion_offsets() {
    let c_source = "int32 identity(int32 x) { return x; }";
    let click_source = r#"# Click's proof: ü } identity() { "
verifying "identity.c";
int32 identity(int32 x) {
    ensures result == x;
} by {
    execute(); # unmatched ' } "
    simp();
}
# trailing comment without newline: '"#;
    let sources = [("identity.c", c_source)];
    verify_c0_sources(click_source, &sources).expect("commented proof should verify");
    let offset = click_source.find("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
            .expect("comments must not disturb proof source offsets");
    assert_eq!(&expanded[..offset], &click_source[..offset]);
    assert!(expanded.ends_with("# trailing comment without newline: '"));
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
fn smart_simp_expansion_checks_as_surface_click() {
    let c_source = r#"
            int32 identity(int32 x, int32 y, int32 z) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x, int32 y, int32 z) {
                ensures result == x by { execute(); simp(); }
            }
        "#;

    let verified = verify_c0_sources(click_source, &[("identity.c", c_source)])
        .expect("smart simp should verify");
    let expanded = verified[0]
        .expanded_proof_source()
        .expect("smart simp should lower to surface tactics");
    let expanded_source = click_source.replacen("by { execute(); simp(); }", &expanded, 1);
    verify_c0_sources(&expanded_source, &[("identity.c", c_source)])
        .expect("printed smart simp expansion should check");
}

#[test]
fn unsigned_narrowing_snapshot_expansion_reverifies() {
    let c_source = "struct state { unsigned long value; }; unsigned int take(struct state *p) { unsigned int result = p->value; p->value += 1; return result; }";
    let click_source = r#"
        verifying "take.c";
        unsigned int take(struct state *p) {
            requires loadable(p->value);
            consumes p->value;
            produces p->value;
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
                    contains allocation(node, sizeof(struct node));
                    owns object(node);
                    contains allocated_list(node->next);
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
                    contains allocation(data, count * 4);
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
                contains allocation(owner->data, 4);
                owns owner->data[0..1];
            }

            verifying "replace_allocated_cell.c";
            verifying "replace_after_scoped_open.c";

            int32 replace_allocated_cell(struct cell_owner* owner) {
                consumes allocated_cell(owner);
                produces allocated_cell(owner);

                ensures result == 0 or result == 1;
                ensures result == 0 implies owner->data == old(owner->data);
            } by {
                unfold(allocated_cell(owner));
                execute();
                fold(allocated_cell(owner));
                simp();
            }

            int32 replace_after_scoped_open(struct cell_owner* owner) {
                consumes allocated_cell(owner);
                produces allocated_cell(owner);

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
                have result == x by simp;
                simp();
            }
        "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("checked post-execution smart have should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "the result-aware smart have must retain its checked Proof: {events:#?}"
    );

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
    assert!(!expanded.contains("have result == x by simp"), "{expanded}");
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("result-aware theorem application should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "the result-aware theorem application must not reconstruct and check a certificate: {events:#?}"
    );

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
                have data[0] == value by simp;
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("checked post-execution transport should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "the smart transport must retain its checked Proof: {events:#?}"
    );

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

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("the grouped outcome unfold should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "the grouped outcome unfold must retain its checked Proof: {events:#?}"
    );
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
            requires selected: x == 0;
            ensures retained: x == 0;
            ensures reflexive: result == result;
        } by {
            execute();
            assumption();
            normalize();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("grouped outcome closers should verify through focused Proof roots");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "grouped outcome closers must retain their checked Proof steps: {events:#?}"
    );
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
            requires zero: x == 0;
            ensures successor: x + 1 == 1;
        } by {
            execute();
            rewrite(x == 0);
            normalize();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("outcome rewrite should advance its focused Proof goal");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "outcome rewrite must retain its checked Proof step: {events:#?}"
    );
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
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("grouped simp should retain its checked obligation scopes");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "grouped direct simp must not construct and check a second certificate: {events:#?}"
    );

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
    assert_eq!(expanded.matches("have result == result by {").count(), 2);
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(expanded.contains("assumption();"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the serialized grouped obligation scopes should verify independently");
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
            requires zero: x == 0;
            ensures successor: x + 1 == 1;
        } by {
            execute();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("grouped simp should apply its planned rewrite through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "a planner-selected grouped candidate must be checked once and retained: {events:#?}"
    );

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
    assert!(
        expanded.contains("rewrite(at(function.entry, x == 0));"),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
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

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose.c", c_source)])
    });
    verified.expect("the two-value result should prove nonnegative by cases");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
        )),
        "the checked Proof case split must bypass compatibility construction: {events:#?}"
    );

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
        expanded.contains("cases (at(function.entry, x == 0 or x == 1))"),
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

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
    verified.expect("both symbolic max claims should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
                    || name == "outcome simp legacy exit planning"
        )),
        "selected branch order paths must bypass outcome fallbacks: {events:#?}"
    );

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

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
    verified.expect("the return expression should normalize through retained equalities");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
                    || name == "outcome simp legacy exit planning"
        )),
        "selected equality paths must bypass outcome fallbacks: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &c_sources,
        "later_loop_preserve",
        CProofClaim::Ensure(0),
    )
    .expect("the retained equality paths should expand");
    assert!(expanded.matches("rewrite(").count() >= 2, "{expanded}");
    verify_c0_sources(&expanded, &c_sources)
        .expect("the expanded equality paths should check independently");
}

#[test]
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

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
    verified.expect("all three concrete cells should specialize the retained loop invariant");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
                    || name == "outcome simp legacy exit planning"
        )),
        "selected universal instances must bypass outcome fallbacks: {events:#?}"
    );

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
            requires 1 <= x;
            requires 1 <= y;
            ensures 0 <= x and 0 <= y;
        } by {
            execute();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("first.c", c_source)])
    });
    verified.expect("the conjunction should retain both recursively checked child proofs");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
        )),
        "recursive conjunction closure must bypass compatibility construction: {events:#?}"
    );

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

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the vacuous path implication should close through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "introduced contradiction closure must bypass outcome compatibility planning: {events:#?}"
    );

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
            requires 1 <= x;
            requires 1 <= y;
            ensures 0 <= x and 0 <= y;
        } by {
            execute();
            have 0 <= x and 0 <= y by simp;
            assumption();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("first.c", c_source)])
    });
    verified.expect("the smart have should retain its recursively checked conjunction");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name.starts_with("post-execution simple have check")
                    || name == "post-execution smart have compatibility construction"
        )),
        "the checked smart have must not construct or check a second proof: {events:#?}"
    );

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
    assert!(!expanded.contains("by simp"), "{expanded}");
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
                witness(j = result);
                simp();
            }
        }
    "#;

    let ((((verified, events), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        crate::instrumentation::collect(|| {
                            verify_c0_sources(click_source, &[("identity.c", c_source)])
                        })
                    })
                })
            }
        });
    verified.expect("exit witness should refine its checked obligation scope");
    assert_eq!(flat_units, 1, "the function proof should retain Proof");
    assert_eq!(context_exports, 0, "the existential Proof exported state");
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked source certificate"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.ensures_0" && name == "generated certificate validation"
        )),
        "exit witness refinement must retain the accepted Proof path: {events:#?}"
    );

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
    assert!(expanded.contains("witness(j = result);"), "{expanded}");
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
            requires has_k: exists (k: int32) { k == x };
            ensures exists (j: int32) { j == result } by {
                execute();
                choose(k from requirement has_k);
                witness(j = k);
                simp();
            }
        }
    "#;

    let (((verified, certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, &[("identity.c", c_source)])
                    })
                })
            }
        });
    verified.expect("choose and witness should advance one retained outcome Proof");
    assert_eq!(flat_units, 1, "the function proof should retain Proof");
    assert_eq!(
        context_exports, 0,
        "the existential operations exported state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );

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
        expanded.contains("choose(k from requirement has_k);"),
        "{expanded}"
    );
    assert!(expanded.contains("witness(j = k);"), "{expanded}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("the serialized choose/witness proof should independently verify");

    let witness_offset = expanded
        .rfind("witness(j = k);")
        .expect("the extracted nested proof should retain its witness");
    let mut corrupted = expanded.clone();
    corrupted.replace_range(
        witness_offset..witness_offset + "witness(j = k);".len(),
        "witness(j = k + 1);",
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
                witness(k = 0);
                simp();
            }
        }
    "#;
    let sources = [("witness.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the bounded witness body should close through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "the checked bounded witness must not enter legacy outcome planning"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "witness_zero",
        CProofClaim::Ensure(0),
    )
    .expect("the retained bounded witness should expand");
    assert!(expanded.contains("witness(k = 0);"), "{expanded}");
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("post-execution smart apply should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "the post-execution smart apply must retain its checked Proof: {events:#?}"
    );

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
                ensures result == data[0] by auto;
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
                have at(statement(0).entry, p[0]) == 1 by simp;
                have at(statement(0).exit, p[0]) == 0 by simp;
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
            owns object(owner);
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

    let (
        ((((verified, events), explicit_fallbacks), certificate_checks), context_exports),
        flat_units,
    ) = proof::count_flat_proof_units(|| {
        {
            proof::count_execution_context_exports(|| {
                proof::count_source_certificate_checks(|| {
                    proof::count_explicit_linear_fallbacks(|| {
                        crate::instrumentation::collect(|| {
                            verify_c0_sources(click_source, &sources)
                        })
                    })
                })
            })
        }
    });
    verified.expect("the smart marked transport should verify before expansion");
    assert_eq!(flat_units, 2, "both function proofs should retain Proof");
    assert_eq!(
        context_exports, 0,
        "the marked transport exported Proof state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );
    assert_eq!(explicit_fallbacks, 0, "the marked transport fell back");
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
    let (corrupted_result, corrupted_fallbacks) =
        { proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, &sources)) };
    corrupted_result.expect_err("tampering with the transport target must invalidate the proof");
    assert_eq!(
        corrupted_fallbacks, 0,
        "an invalid migrated transport must not become a compatibility miss"
    );

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
            .contains("no certified frame transport applies to the exact source fact"),
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
            consumes p[0..2];
            produces p[0..2];
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
                consumes p[0..2];
                produces p[0..2];
                ensures result == p[0];
            } by {
                step();
                have at(statement(0).entry, loadable(p[0..2])) by {
                    assumption();
                }
                transport(
                    at(statement(0).entry, loadable(p[0..2])),
                    loadable(p[0..2])
                ) using {
                    at(statement(0).entry, loadable(p[0..2]));
                }
                execute();
                simp();
            }
        "#;

    verify_c0_sources(click_source, &[("snapshot_loadable.c", c_source)])
        .expect("a complete loadability proposition should lower and transport from a snapshot");
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
                consumes owner_cell(owner);
                produces owner_cell(owner);
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
                have x == x by auto;
                execute();
                simp();
            }
        "#;
    let have_offset = click_source
        .find("have x == x by auto")
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
                owns pair[0..4];
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
    .expect("pointer theorem arguments should lower from the ambient loadability context");
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
                have result == 1 or result == 2 by simp;
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
    assert!(!expanded.contains("have result == 1 or result == 2 by simp"));
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
                requires loadable(p[0..3]);
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
                have x == x by simp;
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

#[test]
fn pure_structural_simp_builds_recursive_conjunction_on_proof() {
    let click_source = r#"
        theorem nonnegative_pair_direct(x: int32, y: int32) {
            requires 1 <= x;
            requires 1 <= y;
            ensures 0 <= x and 0 <= y by simp;
        }

        theorem nonnegative_pair_script(x: int32, y: int32) {
            requires 1 <= x;
            requires 1 <= y;
            ensures 0 <= x and 0 <= y by {
                simp();
            }
        }

        theorem nonnegative_pair_branches(flag: int32, x: int32, y: int32) {
            requires 1 <= x;
            requires 1 <= y;
            ensures 0 <= x and 0 <= y by {
                if flag == 0 {
                    simp();
                } else {
                    simp();
                }
            }
        }
    "#;

    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("pure structural simp should retain both recursively checked child proofs");
    for claim in [
        "nonnegative_pair_direct.ensures_0",
        "nonnegative_pair_script.ensures_0",
        "nonnegative_pair_branches.ensures_0",
    ] {
        assert!(
            events.iter().all(|event| !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished {
                    claim: event_claim,
                    name,
                    ..
                } if event_claim == claim && name == "generated certificate validation"
            )),
            "{claim} must retain its structural Proof descendant: {events:#?}"
        );
    }

    let script_start = click_source
        .find("theorem nonnegative_pair_script")
        .expect("the script theorem should be present");
    let branch_start = click_source
        .find("theorem nonnegative_pair_branches")
        .expect("the branch theorem should be present");
    for (offset, expected_applications) in [
        (
            click_source
                .find("simp;")
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
fn restricted_simp_expands_to_explicit_equality_rewrites() {
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("restricted equality simp should build its typed path through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "equality_transitive.ensures_0"
                    && name == "generated certificate validation"
        )),
        "restricted equality simp must retain its checked Proof descendant: {events:#?}"
    );
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
    assert!(expanded.contains("rewrite(x == y);"), "{expanded}");
    assert!(expanded.contains("rewrite(y == z);"), "{expanded}");
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[]).expect("explicit equality certificate should check");
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

    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("rewrite followed by structural simp should remain on Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "rewrite_pair.ensures_0" && name == "generated certificate validation"
        )),
        "the rewrite successor must not reconstruct and check a second proof: {events:#?}"
    );

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

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("conjunction elimination should have an explicit expansion");
    assert!(expanded.contains("extract(x == y);"), "{expanded}");
    assert!(expanded.contains("extract(y == z);"), "{expanded}");
    assert!(expanded.contains("rewrite(x == y);"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_c0_sources(&expanded, &[])
        .expect("explicit conjunction-elimination certificate should check");
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
        expanded.contains("apply(int32_lt_implies_le(x, y)) using"),
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
        expanded.contains("apply(int32_lt_implies_le("),
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
        expanded.contains("apply(int32_not_lt_implies_ge(x, 0)) using"),
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment.c", c_source)])
    });
    verified.expect("the typed strict-increment rule should verify through the fixed-state Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment.contract"
                    && (name == "generated certificate validation"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained strict-increment rule must not enter legacy certificate search: {events:#?}"
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment.c", c_source)])
    });
    verified
        .expect("the typed increment-definedness rule should verify through the fixed-state Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment.contract"
                    && (name == "generated certificate validation"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained increment-definedness rule must not enter legacy certificate search: {events:#?}"
    );
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment_nonnegative.c", c_source)])
    });
    verified
        .expect("the typed increment-lower-bound rule should verify through the fixed-state Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_nonnegative.contract"
                    && (name == "generated certificate validation"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained increment-lower-bound rule must not enter legacy certificate search: {events:#?}"
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
        expanded.contains("apply(int32_le_and_not_lt_implies_eq("),
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("nonstrict unequal order should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "nonstrict_unequal_is_strict.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the named <=/!= strict-order step must not use construction check: {events:#?}"
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

    let expanded = expand_c0_tactic_source_at(click_source, &[], line, column)
        .expect("nonstrict unequal order should expand");
    assert!(
        expanded.contains("apply(int32_le_and_neq_implies_lt(left, right)) using"),
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment_below.c", c_source)])
    });
    verified.expect("the typed increment bound should verify through the fixed-state Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_below.contract"
                    && (name == "generated certificate validation"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained increment rule must not enter legacy certificate search: {events:#?}"
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
        expanded.contains("apply(int32_lt_transitive("),
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
        expanded.contains("apply(int32_ge_transitive("),
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment_ge.c", c_source)])
    });
    verified.expect(
        "the typed greater-equal increment rule should verify through the fixed-state Proof",
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_ge.contract"
                    && (name == "generated certificate validation"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained greater-equal increment rule must not enter legacy certificate search: {events:#?}"
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("increment_gt.c", c_source)])
    });
    verified.expect(
        "the typed strict-greater increment rule should verify through the fixed-state Proof",
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_gt.contract"
                    && (name == "generated certificate validation"
                        || name == "derivation lowering: ambient rewrite harvest")
        )),
        "the retained strict-greater increment rule must not enter legacy certificate search: {events:#?}"
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
        expanded.contains("apply(int32_increment_strict_greater_lower_bound("),
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity_zero.c", c_source)])
    });
    verified.expect("post-execution >=/not-> equality should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity_zero.ensures_0" && name == "generated certificate validation"
        )),
        "the outcome equality theorem must not use construction check: {events:#?}"
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
        expand_c0_tactic_source_at(click_source, &[("identity_zero.c", c_source)], line, column)
            .expect("post-execution greater-order equality should expand");
    assert!(
        expanded.contains("apply(int32_ge_and_not_gt_implies_eq("),
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity_at_least_one.c", c_source)])
    });
    verified.expect("the typed successor-bound Proof should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity_at_least_one.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained successor-bound proof must not use construction check: {events:#?}"
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
        expanded.contains("apply(int32_ge_transitive("),
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the restricted successor-bound Proof should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "not_below_two_is_at_least_one.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained restricted successor-bound proof must not use construction check: {events:#?}"
    );
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
        expanded.contains("apply(int32_not_lt_implies_ge("),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_ge_transitive("),
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
            requires loadable(p[0..2]);
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

    let ((expanded, certificate_checks), context_exports) = {
        proof::count_execution_context_exports(|| {
            proof::count_source_certificate_checks(|| {
                expand_c0_tactic_source_at(
                    click_source,
                    &[("compare_swap2.c", c_source)],
                    line,
                    column,
                )
            })
        })
    };
    let expanded = expanded.expect("post-execution predicate goal should expand");
    assert_eq!(
        context_exports, 0,
        "branched predicate expansion must not export semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "branched predicate expansion must not check a certificate"
    );
    assert!(expanded.contains("unfold(sorted_pair);"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_lt_implies_le("),
        "{expanded}"
    );
    assert!(expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    let (reverified, reverify_fallbacks) = {
        proof::count_explicit_linear_fallbacks(|| {
            verify_c0_sources(&expanded, &[("compare_swap2.c", c_source)])
        })
    };
    reverified.expect("expanded predicate-goal proof should independently reverify");
    assert_eq!(
        reverify_fallbacks, 0,
        "the expanded predicate proof must use only authoritative Proof operations"
    );

    let corrupted = expanded.replacen("unfold(sorted_pair);", "unfold(missing);", 1);
    assert_ne!(
        corrupted, expanded,
        "the expansion should expose its checked predicate unfold"
    );
    let (corrupted_result, corrupted_fallbacks) = {
        proof::count_explicit_linear_fallbacks(|| {
            verify_c0_sources(&corrupted, &[("compare_swap2.c", c_source)])
        })
    };
    corrupted_result.expect_err("a corrupted branched predicate expansion must be rejected");
    assert_eq!(
        corrupted_fallbacks, 0,
        "a corrupted predicate unfold must be rejected by Proof, not compatibility"
    );

    let condition = "at(statement(1).entry, p[1]) < at(statement(1).entry, p[0])";
    let wrong_condition = "at(statement(1).entry, p[0]) < at(statement(1).entry, p[1])";
    let corrupted = expanded.replacen(condition, wrong_condition, 1);
    assert_ne!(
        corrupted, expanded,
        "the expansion should expose its checked outcome condition"
    );
    let (corrupted_result, corrupted_fallbacks) = {
        proof::count_explicit_linear_fallbacks(|| {
            verify_c0_sources(&corrupted, &[("compare_swap2.c", c_source)])
        })
    };
    corrupted_result.expect_err("a corrupted outcome condition must be rejected");
    assert_eq!(
        corrupted_fallbacks, 0,
        "a corrupted outcome condition must be rejected by Proof, not compatibility"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the selected equality rewrite should close on the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "predecessor_of_one_is_nonnegative.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the selected rewrite path must not use construction check: {events:#?}"
    );

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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed increment rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_stays_bounded.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained pure increment rule must not use construction check: {events:#?}"
    );
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
            requires 1 <= value;
            ensures 0 <= value by {
                simp() using {
                    1 <= value;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("positive-to-nonnegative simp should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "positive_is_nonnegative.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the named positive-to-nonnegative step must not use construction check: {events:#?}"
    );
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
    assert!(expanded.contains("1 <= value;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("expanded theorem application should check");
}

#[test]
fn restricted_simp_expands_strictly_positive_to_nonnegative_theorem_application() {
    let click_source = r#"
        theorem strictly_positive_is_nonnegative(value: int32) {
            requires 0 < value;
            ensures value >= 0 by {
                simp() using {
                    0 < value;
                }
            }
        }
    "#;
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("strictly-positive-to-nonnegative simp should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "strictly_positive_is_nonnegative.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the named strictly-positive-to-nonnegative step must not use construction check: {events:#?}"
    );
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
        .expect("strictly-positive-to-nonnegative simp should expand");
    assert!(
        expanded.contains("apply(int32_strictly_positive_is_nonnegative(value)) using"),
        "{expanded}"
    );
    assert!(expanded.contains("0 < value;"), "{expanded}");
    assert!(!expanded.contains("assumption();"), "{expanded}");
    assert!(!expanded.contains("simp() using"), "{expanded}");
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed predecessor-nonnegative rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "positive_predecessor_is_nonnegative.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained predecessor-nonnegative rule must not use construction check: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed predecessor-decrease rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "positive_predecessor_decreases.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained predecessor-decrease rule must not use construction check: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed predecessor-upper-bound rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "predecessor_keeps_upper_bound.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained predecessor-upper-bound rule must not use construction check: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the nested predecessor proof should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "one_le_predecessor_is_nonnegative.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained nested predecessor proof must not use construction check: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("one-le predecessor proof should expand");
    assert!(expanded.contains("have 0 < value"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_successor_le_implies_lt(0, value)) using"),
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the nested predecessor-decrease proof should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "one_le_predecessor_decreases.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained nested predecessor-decrease proof must not use construction check: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("one-le predecessor-decrease proof should expand");
    assert!(expanded.contains("have 0 < value"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_successor_le_implies_lt(0, value)) using"),
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the equal-one predecessor proof should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "equal_one_predecessor_is_nonnegative.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained equal-one path must not use construction check: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the predecessor-zero proof should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "equal_one_predecessor_is_zero.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained predecessor-zero path must not use construction check: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("equal-one predecessor-zero proof should expand");
    assert!(expanded.contains("rewrite(value == 1)"), "{expanded}");
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed strict-increment rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_is_greater.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained pure strict-increment rule must not use construction check: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed increment-definedness rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_is_defined.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained pure increment-definedness rule must not use construction check: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed increment-lower-bound rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_preserves_lower_bound.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained pure increment-lower-bound rule must not use construction check: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed increment-order rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_preserves_order.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained increment-order rule must not use construction check: {events:#?}"
    );
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
            fact loadable(owner->data[0..owner->len]);
            fact separate(memory(object(owner)), memory(owner->data[0..owner->cap]));
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

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("vector_push.c", c_source)], line, column)
            .expect("unchanged-prefix simp should expand to a checkable frame transport");
    assert!(
        expanded.contains("transport(old(owner->data[k])"),
        "{expanded}"
    );
    assert!(expanded.contains("k < old(owner->len)"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
    verify_c0_sources(&expanded, &[("vector_push.c", c_source)])
        .expect("unchanged-prefix certificate should check");
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed adjacent-order rule should verify through the pure Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "two_at_most_implies_one_below.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the retained adjacent-order proof must not use construction check: {events:#?}"
    );
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
        expanded.contains("apply(int32_successor_le_implies_lt(1, value)) using"),
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the checked order-path Proof should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "three_edge_order_chain.ensures_0"
                    && name == "generated certificate validation"
        )),
        "signed-order simp should construct its Proof through checked theorem applications: {events:#?}"
    );
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
        expanded.contains("apply(int32_le_lt_transitive(first, second, third)) using"),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_lt_le_transitive(first, third, last)) using"),
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the checked equality-path Proof should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "three_edge_equality_chain.ensures_0"
                    && name == "generated certificate validation"
        )),
        "equality simp should construct its Proof through checked rewrites: {events:#?}"
    );

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
    assert!(expanded.contains("rewrite(first == second);"), "{expanded}");
    assert!(expanded.contains("rewrite(second == third);"), "{expanded}");
    assert!(expanded.contains("rewrite(third == last);"), "{expanded}");
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the typed <=/not-< equality rule should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if (claim == "le_and_not_lt_are_equal.ensures_0"
                    || claim == "ge_and_not_gt_are_equal.ensures_0")
                    && name == "generated certificate validation"
        )),
        "the named equality step must not use construction check: {events:#?}"
    );

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
        expanded.contains("apply(int32_le_and_not_lt_implies_eq(left, right)) using"),
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
        expanded.contains("apply(int32_ge_and_not_gt_implies_eq(left, right)) using"),
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose_first.c", c_source)])
    });
    verified.expect("the outcome equality path should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_first.contract"
                    && name == "derivation lowering: ambient rewrite harvest"
        )),
        "the typed outcome path must not scan ambient equalities: {events:#?}"
    );

    let offset = click_source.rfind("simp();").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(
        click_source,
        &[("choose_first.c", c_source)],
        position.line,
        position.column,
    )
    .expect("the retained outcome equality path should expand");
    assert!(
        expanded.contains("rewrite(at(function.entry, first == second));"),
        "{expanded}"
    );
    assert!(
        expanded.contains("rewrite(at(function.entry, second == third));"),
        "{expanded}"
    );
    assert!(
        expanded.contains("rewrite(at(function.entry, third == last));"),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(!expanded.contains("simp();"), "{expanded}");
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("validate_chain.c", c_source)])
    });
    verified.expect("the outcome order path should verify through the fixed-state Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "validate_chain.contract"
                    && name == "generated certificate validation"
        )),
        "the outcome theorem path must retain its checked Proof successor: {events:#?}"
    );

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
            "apply(int32_le_lt_transitive(at(function.entry, first), at(function.entry, second), at(function.entry, third))) using"
        ),
        "{expanded}"
    );
    assert!(
        expanded.contains(
            "apply(int32_lt_le_transitive(at(function.entry, first), at(function.entry, third), at(function.entry, last))) using"
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the constant lower-bound weakening should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "three_at_least_implies_nonnegative.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the constant lower-bound proof should retain its checked Proof successor: {events:#?}"
    );
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
        expanded.contains("apply(int32_le_transitive(0, 3, value)) using"),
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the constant strict upper-bound weakening should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "three_at_most_implies_below_five.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the constant upper-bound proof should retain its checked Proof successor: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("constant strict upper-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_le_lt_transitive(value, 3, 5)) using"),
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the increment constant-bound rule should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "increment_three_at_most_is_five_at_most.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the increment constant-bound proof must retain both checked theorem steps: {events:#?}"
    );
    let offset = click_source.find("simp() using").unwrap();
    let position = expansion::position_at_offset(click_source, offset);
    let expanded = expand_c0_tactic_source_at(click_source, &[], position.line, position.column)
        .expect("increment constant-bound simp should expand");
    assert!(
        expanded.contains("apply(int32_le_lt_transitive(value, 3, 5)) using"),
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the symbolic-add definedness rule should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "symbolic_add_is_defined.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the symbolic-add proof must retain its checked theorem application: {events:#?}"
    );
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
    let (verified, events) =
        crate::instrumentation::collect(|| verify_click_theorems(click_source));
    verified.expect("the symbolic-subtract definedness rule should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "symbolic_subtract_is_defined.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the symbolic-subtract proof must retain its checked theorem application: {events:#?}"
    );
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
            "apply(int32_one_plus_below_max_is_defined(value)) using",
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
            "apply(int32_one_plus_strictly_increases(value)) using",
        ),
    ];
    for (click_source, claim, application) in cases {
        let (verified, events) =
            crate::instrumentation::collect(|| verify_click_theorems(click_source));
        verified.expect("the operand-order-specific one-plus rule should verify through Proof");
        assert!(
            events.iter().all(|event| !matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished {
                    claim: event_claim,
                    name,
                    ..
                } if event_claim == claim && name == "generated certificate validation"
            )),
            "the one-plus proof must retain its checked theorem application: {events:#?}"
        );
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
fn restricted_simp_composes_equality_rewrites_with_adjacent_order() {
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
    assert!(expanded.contains("rewrite(bound == length);"), "{expanded}");
    assert!(expanded.contains("rewrite(position == 0);"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_successor_le_implies_lt(0, length)) using"),
        "{expanded}"
    );
    assert!(!expanded.contains("simp() using"), "{expanded}");
    assert!(!expanded.contains("derive using"), "{expanded}");
    verify_click_theorems(&expanded).expect("composed explicit certificate should check");
}

#[test]
fn restricted_simp_inside_have_expands_to_explicit_equality_rewrites() {
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

    let expanded =
        expand_c0_tactic_source_at(click_source, &[("identity.c", c_source)], line, column)
            .expect("restricted simp have should expand");
    let expanded_have =
        &expanded[expanded.find("have x == z").unwrap()..expanded.find("execute();").unwrap()];
    assert!(
        expanded_have.contains("rewrite(x == y);"),
        "{expanded_have}"
    );
    assert!(expanded_have.contains("normalize();"), "{expanded_have}");
    assert!(!expanded_have.contains("simp() using"), "{expanded_have}");
    assert!(!expanded_have.contains("derive using"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("identity.c", c_source)])
        .expect("explicit equality have certificate should check");
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
            requires loadable(data[0..length]);
            views data[0..length];
            ensures result == old(data[index]);
        } by {
            have loadable(data[index..index + 1]) by {
                simp() using {
                    loadable(data[0..length]);
                    0 <= index;
                    index < length;
                }
            }
            execute();
            simp();
        }
    "#;
    let offset = click_source
        .find("have loadable(data[index..index + 1])")
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

    let (((verified, certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, &sources)
                    })
                })
            }
        });
    verified.expect("the leading loadability have should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(context_exports, 0, "the loadability Proof exported state");
    assert_eq!(
        certificate_checks, 0,
        "ordinary loadability verification checked a certificate"
    );

    let expanded = expand_c0_tactic_source_at(click_source, &sources, line, column)
        .expect("restricted simp loadability proof should expand");
    let expanded_have_start = expanded.find("have loadable(").unwrap();
    let expanded_have_end = expanded[expanded_have_start..]
        .find("execute();")
        .map(|relative| expanded_have_start + relative)
        .unwrap();
    let expanded_have = &expanded[expanded_have_start..expanded_have_end];
    assert!(
        expanded_have.contains(
            "transport(loadable(data[0..length]), loadable(data[index..(index + 1)])) using"
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
        "have loadable(data[index..(index + 1)]) by {\n\
         transport(loadable(data[0..length]), loadable(data[index..(index + 1)])) using {\n\
         loadable(data[0..length]);\n\
         0 <= index;\n\
         index < length;\n\
         }\n\
         }"
    );
    assert!(!expanded_have.contains("simp() using"), "{expanded_have}");
    assert!(!expanded_have.contains("derive using"), "{expanded_have}");
    verify_c0_sources(&expanded, &sources).expect("explicit loadability transport should check");
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
    assert!(
        expanded_have.contains("rewrite(alias == original);"),
        "{expanded_have}"
    );
    assert!(
        expanded_have.contains("rewrite(index == 0);"),
        "{expanded_have}"
    );
    assert!(
        expanded_have.contains("rewrite(value == original[0]);"),
        "{expanded_have}"
    );
    assert!(expanded_have.contains("normalize();"), "{expanded_have}");
    assert!(!expanded_have.contains("derive using"), "{expanded_have}");
    verify_c0_sources(&expanded, &sources)
        .expect("expanded pointer-alias certificate should check");
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
    let expanded = expand_c0_tactic_source_at(click_source, &sources, line, column).unwrap();
    let selected = &expanded[offset..];
    assert!(selected.contains("rewrite((x + 1) == y);"), "{selected}");
    assert!(!selected.contains("derive using"), "{selected}");
    verify_c0_sources(&expanded, &sources).expect("explicit post-execution proof should check");
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose.c", c_source)])
    });
    verified
        .expect("checked fixed-state apply should verify without ordinary certificate validation");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_second.contract" && name == "generated certificate validation"
        )),
        "the migrated smart fixed-state proof must not pass through the ordinary construction/check gateway: {events:#?}"
    );
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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose.c", c_source)])
    });
    verified.expect("smart apply should continue from its checked Proof successor");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_second.contract" && name == "generated certificate validation"
        )),
        "the migrated apply-then-simp proof must not use construction check: {events:#?}"
    );

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
    assert!(
        expanded_have.contains("normalize();") || expanded_have.contains("split();"),
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
    let click_source = r#"
            verifying "keep.c";

            int32 keep(int32 value, int32 upper) {
                requires value < upper;
                ensures result <= upper;
            } by {
                apply(int32_lt_implies_le(value, upper));
                step();
                assumption();
            }
        "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("keep.c", c_source)])
    });
    let verified = verified.expect("checked execution apply should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "keep.contract" && name == "generated certificate validation"
        )),
        "the migrated execution apply must not pass through ordinary certificate validation: {events:#?}"
    );
    let expanded = verified[0]
        .expanded_proof_tactics()
        .expect("the checked execution apply should retain an expansion");
    assert!(matches!(
        expanded.first(),
        Some(ProofTactic::ApplyTheoremUsing { application, premises })
            if application.name == "int32_lt_implies_le" && premises.len() == 1
    ));
    let retained_source = verified[0]
        .expanded_proof_source()
        .expect("the checked execution apply should have canonical source");
    assert!(retained_source.contains("apply(int32_lt_implies_le(value, upper)) using {"));
    let expanded = expand_c0_claim_source(
        click_source,
        &[("keep.c", c_source)],
        "keep",
        CProofClaim::Grouped,
    )
    .expect("the checked execution apply should expand into source");
    verify_c0_sources(&expanded, &[("keep.c", c_source)])
        .expect("the retained execution theorem step should independently reverify");
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

    let ((((verified, events), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        crate::instrumentation::collect(|| {
                            verify_c0_sources(click_source, &[("two_steps.c", c_source)])
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the linear open scope should verify through Proof");
    assert_eq!(
        flat_units, 1,
        "the complete open proof should retain one Proof"
    );
    assert_eq!(context_exports, 0, "the open Proof exported semantic state");
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "two_steps.contract" && name == "generated certificate validation"
        )),
        "ordinary linear open construction must retain its checked Proof scope: {events:#?}"
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

    let (((verified, certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        verify_c0_sources(click_source, &[("add_once.c", c_source)])
                    })
                })
            }
        });
    verified.expect("the leading statement and open scope should verify on one Proof");
    assert_eq!(flat_units, 1, "the scoped prefix should retain one Proof");
    assert_eq!(
        context_exports, 0,
        "the scoped prefix exported semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );

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

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("two_steps.c", c_source)])
    });
    let verified = verified.expect("linear execute should advance inside the open Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "two_steps.contract" && name == "generated certificate validation"
        )),
        "ordinary scoped execute must retain its checked statement steps: {events:#?}"
    );
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
            requires loadable(p[0..1]);
            consumes p[0..1];
            ensures result <= 0 or result > 0;
        } by {
            execute();
            apply(int32_sign_split(result)) using {}
            assumption();
        }

        int32 rewrite_write(int32 p[]) {
            requires loadable(p[0..1]);
            consumes p[0..1];
            ensures result == 9;
        } by {
            execute();
            rewrite(result == 9);
            normalize();
        }
    "#;
    let sources = [("apply_write.c", apply_c), ("rewrite_write.c", rewrite_c)];

    let ((((verified, explicit_fallbacks), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        proof::count_explicit_linear_fallbacks(|| {
                            verify_c0_sources(click_source, &sources)
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the ordered outcome operations should verify on Proof");
    assert_eq!(flat_units, 2, "both grouped proofs should retain Proof");
    assert_eq!(context_exports, 0, "an outcome Proof exported state");
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "an ordered outcome operation fell back"
    );

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
        let (result, fallbacks) =
            { proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, &sources)) };
        result.expect_err("tampering with an ordered outcome operation must invalidate the proof");
        assert_eq!(fallbacks, 0, "invalid {description} must not fall back");
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
            requires loadable(p[0..1]);
            consumes p[0..1];
            ensures is_nine(result);
        } by {
            execute();
            unfold(is_nine);
            normalize();
        }
    "#;
    let sources = [("write_first.c", c_source)];

    let ((((verified, explicit_fallbacks), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        proof::count_explicit_linear_fallbacks(|| {
                            verify_c0_sources(click_source, &sources)
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the ordered predicate unfold should verify on Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(context_exports, 0, "the outcome Proof exported state");
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "the ordered predicate unfold fell back"
    );

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
    let (result, fallbacks) =
        { proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, &sources)) };
    result.expect_err("tampering with the predicate unfold must invalidate the proof");
    assert_eq!(fallbacks, 0, "an invalid unfold must not fall back");
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

    let ((((verified, explicit_fallbacks), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        proof::count_explicit_linear_fallbacks(|| {
                            verify_c0_sources(click_source, &sources)
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the quantified resource scope should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(context_exports, 0, "the resource scope exported state");
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "the quantified resource scope fell back"
    );

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
    let (result, fallbacks) =
        { proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, &sources)) };
    let error =
        result.expect_err("tampering with the resource selection must invalidate the proof");
    assert!(
        error.message().contains("`unfold(marker((x + 1)))` failed"),
        "the checked resource-entry operation should reject the tamper directly: {error:?}"
    );
    assert_eq!(fallbacks, 0, "an invalid open must not fall back");
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

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("three_steps.c", c_source)])
    });
    let verified = verified.expect("execute_until should advance the checked open frontier");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "three_steps.contract" && name == "generated certificate validation"
        )),
        "scoped execute_until must retain its checked statement path: {events:#?}"
    );
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

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("two_steps.c", c_source)])
    });
    let verified = verified.expect("the nested theorem application should advance the open Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "two_steps.contract" && name == "generated certificate validation"
        )),
        "ordinary nested-scope construction must not check its retained theorem step: {events:#?}"
    );
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
            contains cell(p);
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
    let ((((verified, explicit_fallbacks), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        proof::count_explicit_linear_fallbacks(|| {
                            verify_c0_sources(click_source, &sources)
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the nested resource scopes should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(context_exports, 0, "the nested scopes exported state");
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "the nested resource scopes fell back"
    );
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
    let (result, fallbacks) =
        { proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, &sources)) };
    let error =
        result.expect_err("tampering with the nested resource selection must invalidate the proof");
    assert!(
        error.message().contains("`unfold(cell((p + 1)))` failed"),
        "the nested checked resource entry should reject the tamper directly: {error:?}"
    );
    assert_eq!(fallbacks, 0, "an invalid nested open must not fall back");
}

#[test]
fn linear_open_retains_a_direct_bare_theorem_application() {
    let c_source = r#"
        int32 retain_lower(int32 lower, int32 upper) {
            return lower;
        }
    "#;
    let click_source = r#"
        resource ordered(lower: int32, upper: int32) {
            fact lower < upper;
        }

        verifying "retain_lower.c";

        int32 retain_lower(int32 lower, int32 upper) {
            owns ordered(lower, upper);
            ensures lower <= upper;
        } by {
            open(ordered(lower, upper)) {
                apply(int32_lt_implies_le(lower, upper));
                step();
            }
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("retain_lower.c", c_source)])
    });
    let verified = verified.expect("the direct theorem application should advance the open Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "retain_lower.contract" && name == "generated certificate validation"
        )),
        "ordinary open-scope theorem search must not check its retained step: {events:#?}"
    );
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
                    ] if application.name == "int32_lt_implies_le" && premises.len() == 1
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

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("set_second_return_first.c", c_source)])
    });
    let verified = verified.expect("the direct transport should advance the open Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "set_second_return_first.contract"
                    && name == "generated certificate validation"
        )),
        "ordinary open-scope transport search must not check its retained step: {events:#?}"
    );
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
            branch {
                ensuring {
                    fact value == old(p[0]) or value == 0;
                    owns cell(p);
                }
                then {
                    open(cell(p)) {
                        step();
                        have value == old(p[0]) or value == 0 by {
                            have value == old(p[0]) by { normalize(); }
                            left();
                        }
                    }
                }
                else {
                    step();
                    have value == old(p[0]) or value == 0 by {
                        have value == 0 by { normalize(); }
                        right();
                    }
                }
            }
            step();
            simp();
        }
    "#;
    let sources = [("read_if.c", c_source)];

    let ((((verified, explicit_fallbacks), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        proof::count_explicit_linear_fallbacks(|| {
                            verify_c0_sources(click_source, &sources)
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the branch-arm resource scope should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(context_exports, 0, "the branch-arm scope exported state");
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "the branch-arm resource scope fell back"
    );

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
    let (result, fallbacks) =
        { proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, &sources)) };
    let error =
        result.expect_err("tampering with the branch-arm resource must invalidate the proof");
    assert!(
        error.message().contains("`unfold(cell((p + 1)))` failed"),
        "the checked branch-arm resource entry should reject the tamper directly: {error:?}"
    );
    assert_eq!(
        fallbacks, 0,
        "an invalid branch-arm open must not fall back"
    );
}

#[test]
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
            contains cell(p);
            contains marker(flag);
        }

        verifying "read_if.c";

        int32 read_if(int32 p[], int32 flag) {
            owns wrapped_cell(p, flag);
            ensures result == old(p[0]) or result == 0;
        } by {
            open(wrapped_cell(p, flag)) {
                open(cell(p)) {
                    step();
                    branch {
                        ensuring {
                            fact value == old(p[0]) or value == 0;
                            views p[0..1];
                        }
                        then {
                            open(marker(flag)) {
                                step();
                                have value == old(p[0]) or value == 0 by {
                                    have value == old(p[0]) by { normalize(); }
                                    left();
                                }
                            }
                        }
                        else {
                            step();
                            have value == old(p[0]) or value == 0 by {
                                have value == 0 by { normalize(); }
                                right();
                            }
                        }
                    }
                }
            }
            step();
            simp();
        }
    "#;
    let sources = [("read_if.c", c_source)];

    let ((((verified, explicit_fallbacks), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        proof::count_explicit_linear_fallbacks(|| {
                            verify_c0_sources(click_source, &sources)
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the nested branch-arm scope should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(
        context_exports, 0,
        "the nested branch-arm scope exported state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "the nested branch-arm scope fell back"
    );

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
    let (result, fallbacks) =
        { proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, &sources)) };
    let error = result
        .expect_err("tampering with the nested branch-arm resource must invalidate the proof");
    assert!(
        error
            .message()
            .contains("`unfold(marker((flag + 1)))` failed"),
        "the checked nested branch-arm entry should reject the tamper directly: {error:?}"
    );
    assert_eq!(
        fallbacks, 0,
        "an invalid nested branch-arm open must not fall back"
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
                then {
                    if x >= 0 {
                        execute();
                        simp();
                    } else {
                        execute();
                        simp();
                    }
                }
                else {
                    execute();
                    simp();
                }
            }
        }
    "#;
    let sources = [("choose_x_or_zero.c", c_source)];

    let ((((verified, explicit_fallbacks), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        proof::count_explicit_linear_fallbacks(|| {
                            verify_c0_sources(click_source, &sources)
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the nested terminal proof if should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(
        context_exports, 0,
        "the nested terminal proof if exported state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary verification checked a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "the nested terminal proof if fell back"
    );

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
    let ((selected_expansion, selected_fallbacks), selected_flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_explicit_linear_fallbacks(|| {
                    expand_c0_tactic_source_at(
                        click_source,
                        &sources,
                        position.line,
                        position.column,
                    )
                })
            }
        });
    let selected_expansion = selected_expansion
        .expect("the selected terminal-arm simp should expand from retained provenance");
    assert_eq!(
        selected_flat_units, 1,
        "selected expansion should retain one Proof"
    );
    assert_eq!(
        selected_fallbacks, 0,
        "selected nested-arm expansion fell back from a checked operation"
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
    let (result, fallbacks) =
        { proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, &sources)) };
    result.expect_err("an unavailable result condition must invalidate the nested proof if");
    assert_eq!(
        fallbacks, 0,
        "an invalid nested proof if must not fall back"
    );
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
            branch {
                ensuring {
                    fact x >= 0;
                }
                then { step(); }
                else { step(); }
            }
            step();
            simp();
        }
    "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    let ((((verified, events), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        crate::instrumentation::collect(|| {
                            verify_c0_sources(click_source, &[("nonnegative.c", c_source)])
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the checked branch interface should verify");
    assert_eq!(
        crate::kernel::take_checked_function_body_execution_count(),
        0,
        "a pure checked branch interface must seal from retained outcome evidence"
    );
    assert_eq!(flat_units, 1, "the branch proof should retain one Proof");
    assert_eq!(
        context_exports, 0,
        "the branch proof must not export semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary branch verification must not check a certificate"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "nonnegative.contract"
                    && matches!(name.as_str(), "generated certificate validation" | "frame exact effect check")
        )),
        "the branch, common return, and frame must retain one checked Proof: {events:#?}"
    );
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
            branch {
                ensuring {
                    fact y >= 0;
                    owns marker(x);
                }
                then { step(); }
                else { step(); }
            }
            step();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("preserve_marker.c", c_source)])
    });
    let verified = verified.expect("the exact owned interface should stay on Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "preserve_marker.contract"
                    && name == "generated certificate validation"
        )),
        "an unchanged exact ownership export must retain its checked Proof: {events:#?}"
    );
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
            branch {
                ensuring {
                    fact y >= 0;
                    owns marker(x);
                }
                then { step(); }
                else { step(); }
            }
            step();
            simp();
        }
    "#;

    let _ = crate::kernel::take_checked_function_body_execution_count();
    let ((verified, events), checked_interface_joins) =
        crate::surface::proof::count_checked_execution_interface_joins(|| {
            crate::instrumentation::collect(|| {
                verify_c0_sources(click_source, &[("preserve_two_markers.c", c_source)])
            })
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
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "preserve_two_markers.contract"
                    && name == "generated certificate validation"
        )),
        "quantity-interface construction must not check its surface certificate: {events:#?}"
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
    let click_source = r#"
        verifying "retain_order.c";

        int32 retain_order(int32 lower, int32 upper, int32 flag) {
            requires lower < upper;
            ensures lower <= upper;
        } by {
            step();
            branch {
                ensuring {
                    fact lower <= upper;
                }
                then {
                    step();
                    apply(int32_lt_implies_le(lower, upper));
                }
                else {
                    step();
                    apply(int32_lt_implies_le(lower, upper));
                }
            }
            step();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("retain_order.c", c_source)])
    });
    let verified = verified.expect("bare arm applications should advance the branch Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "retain_order.contract" && name == "generated certificate validation"
        )),
        "ordinary branch theorem search must not check its retained applications: {events:#?}"
    );
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
                        if application.name == "int32_lt_implies_le" && premises.len() == 1
                ) && matches!(
                    branch.else_tactics.as_slice(),
                    [ProofTactic::Step, ProofTactic::ApplyTheoremUsing { application, premises }]
                        if application.name == "int32_lt_implies_le" && premises.len() == 1
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
    let click_source = r#"
        verifying "choose_bound.c";

        int32 choose_bound(int32 lower, int32 upper, int32 flag) {
            requires lower < upper;
            ensures lower <= upper;
        } by {
            step();
            branch {
                ensuring {
                    fact lower < upper;
                }
                then { step(); }
                else { step(); }
            }
            apply(int32_lt_implies_le(lower, upper));
            step();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose_bound.c", c_source)])
    });
    let verified =
        verified.expect("the common theorem application should advance the joined Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_bound.contract"
                    && matches!(name.as_str(), "generated certificate validation" | "frame exact effect check")
        )),
        "the branch, theorem, return, and frame must retain one checked Proof: {events:#?}"
    );
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
                && application.name == "int32_lt_implies_le"
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
            branch {
                ensuring {
                    fact old(lower) < old(upper);
                }
                then { step(); }
                else { step(); }
            }
            transport(old(lower) < old(upper), lower < upper);
            step();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose_bound_transport.c", c_source)])
    });
    let verified = verified.expect("the common fact transport should advance the joined Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_bound_transport.contract"
                    && matches!(name.as_str(), "generated certificate validation" | "frame exact effect check")
        )),
        "the branch, transport, return, and frame must retain one checked Proof: {events:#?}"
    );
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
    let click_source = r#"
        verifying "select_positive.c";

        int32 select_positive(int32 flag) {
            ensures result >= 0;
        } by {
            step();
            branch {
                ensuring {
                    fact selected > 0;
                    fact selected < 2147483647;
                }
                then { step(); }
                else { step(); }
            }
            have selected >= 0 by {
                apply(int32_strictly_positive_is_nonnegative(selected));
            }
            execute_until(statement(5));
            step();
            simp();
        }
    "#;

    let (verified, _events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("select_positive.c", c_source)])
    });
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
                    [ProofTactic::ApplyTheoremUsing { application, premises }]
                        if application.name == "int32_strictly_positive_is_nonnegative"
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
            branch {
                ensuring {
                    fact selected > 0;
                    fact selected < 2147483647;
                }
                then { step(); }
                else { step(); }
            }
            execute();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("select_and_increment.c", c_source)])
    });
    let verified = verified.expect("common execute should advance the joined Proof to exit");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_and_increment.contract"
                    && matches!(name.as_str(), "generated certificate validation" | "frame exact effect check")
        )),
        "the branch, execute, and frame must retain one checked Proof: {events:#?}"
    );
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
            branch {
                ensuring {
                    fact selected > 0;
                    fact selected < 2147483647;
                }
                then { step(); }
                else { step(); }
            }
            execute();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(
            click_source,
            &[("select_and_increment_positive.c", c_source)],
        )
    });
    verified.expect("strict positivity should retain a composed theorem path on Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_and_increment_positive.contract"
                    && name == "generated certificate validation"
        )),
        "the typed outcome simp must not ordinarily check its theorem path: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &[("select_and_increment_positive.c", c_source)],
        "select_and_increment_positive",
        CProofClaim::Grouped,
    )
    .expect("the strict-positive increment proof should expand");
    assert!(
        expanded.contains("apply(int32_lt_implies_le("),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_increment_strict_greater_lower_bound("),
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
            branch {
                ensuring {
                    fact selected > 0;
                    fact selected < 2147483647;
                }
                then { step(); }
                else { step(); }
            }
            execute();
            have result > 0 by simp;
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(
            click_source,
            &[("select_and_increment_positive_have.c", c_source)],
        )
    });
    verified.expect("the post-execution have should retain its composed Proof path");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_and_increment_positive_have.contract"
                    && name == "generated certificate validation"
        )),
        "the smart have must not reconstruct and check its theorem path: {events:#?}"
    );

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
    assert!(!expanded.contains("have result > 0 by simp"), "{expanded}");
    assert!(
        expanded.contains("apply(int32_lt_implies_le("),
        "{expanded}"
    );
    assert!(
        expanded.contains("apply(int32_increment_strict_greater_lower_bound("),
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
            consumes p[0..2];
            produces p[0..2];
            ensures result == 7;
        } by {
            unfold(first_is_seven);
            branch {
                ensuring {
                    fact p[0] == 7;
                    owns p[0..2];
                }
                then {
                    step();
                    transport(old(p[0]) == 7, p[0] == 7);
                }
                else {
                    step();
                    transport(old(p[0]) == 7, p[0] == 7);
                }
            }
            step();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("set_choice_return_first.c", c_source)])
    });
    let verified = verified.expect("bare arm transports should advance the branch Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "set_choice_return_first.contract"
                    && name == "generated certificate validation"
        )),
        "ordinary branch transport search must not check its retained steps: {events:#?}"
    );
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
            branch {
                ensuring {
                    fact selected >= 0;
                }
                then {
                    step();
                    have selected == selected by {
                        apply(int32_reflexive(selected));
                    }
                }
                else {
                    step();
                    have selected == selected by {
                        apply(int32_reflexive(selected));
                    }
                }
            }
            step();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("select_nonnegative.c", c_source)])
    });
    let verified = verified.expect("nested arm haves should advance the branch Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_nonnegative.contract"
                    && name == "generated certificate validation"
        )),
        "ordinary branch-have construction must not check its retained scopes: {events:#?}"
    );
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
                then {
                    execute();
                }
                else {
                    execute();
                }
            }
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("choose_one_or_two.c", c_source)])
    });
    let verified = verified.expect("terminal arm execution should advance the branch Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "choose_one_or_two.contract"
                    && matches!(name.as_str(), "generated certificate validation" | "frame exact effect check")
        )),
        "terminal arm execution and framing must retain their checked Proof operations: {events:#?}"
    );
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
            arm.iter().all(|tactic| !matches!(
                tactic,
                ProofTactic::SmartExecute | ProofTactic::SmartExecuteAllPaths
            )),
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

#[test]
fn nested_callback_status_cases_expand_at_every_theorem_site() {
    let markdown = include_str!("../../../mdtests/c_contract_executes_status_nested.md");
    let mdtest =
        crate::cli::parse_mdtest(std::path::Path::new("nested-status.md"), markdown).unwrap();
    let source = mdtest.click_source.as_deref().unwrap();
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    verify_c0_sources(source, &c_sources).expect("nested status proofs verify");
    let sites = c0_smart_tactic_source_sites(source, &c_sources).unwrap();
    let sites = sites
        .iter()
        .filter(|site| site.claim_label.starts_with("lift."))
        .collect::<Vec<_>>();
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

    let (((verified, events), checked_interface_joins), source_certificate_checks) =
        crate::surface::proof::count_source_certificate_checks(|| {
            crate::surface::proof::count_checked_execution_interface_joins(|| {
                crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources))
            })
        });
    let verified = verified.expect("the transformed resource branch should stay on Proof");
    assert!(
        checked_interface_joins > 0,
        "the source branch must reach the checked two-arm Proof join"
    );
    assert_eq!(
        source_certificate_checks, 0,
        "the checked branch and explicit observation must seal without executing the C body again"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "select_ready.ensures_0"
                    && name == "generated certificate validation"
        )),
        "the common changed-resource descendant must not be reconstructed by check: {events:#?}"
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
            branch {
                ensuring {
                    fact x == 1;
                }
                then { step(); }
                else { step(); }
            }
            step();
            simp();
        }
    "#;

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("selected_nonnegative.c", c_source)])
    });
    let verified = verified.expect("the sole feasible interface arm should stay on Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "selected_nonnegative.contract" && name == "generated certificate validation"
        )),
        "decided interface construction must retain its checked state directly: {events:#?}"
    );
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
                branch {
                    ensuring {
                        fact x >= 0;
                    }
                    then { step(); }
                    else { step(); }
                }
                step();
            }
            simp();
        }
    "#;

    let ((((verified, events), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        crate::instrumentation::collect(|| {
                            verify_c0_sources(click_source, &[("scoped_nonnegative.c", c_source)])
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the scoped branch interface should stay on Proof");
    assert_eq!(
        flat_units, 1,
        "the scoped interface should retain one Proof"
    );
    assert_eq!(
        context_exports, 0,
        "the scoped interface exported semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "the scoped interface checked a certificate"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "scoped_nonnegative.contract" && name == "generated certificate validation"
        )),
        "scoped branch-interface construction must retain checked structure: {events:#?}"
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
                    then {
                    }
                    else {
                    }
                }
                step();
            }
            simp();
        }
    "#;

    let ((((verified, events), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        crate::instrumentation::collect(|| {
                            verify_c0_sources(click_source, &[("empty_branch.c", c_source)])
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the execution branch should join inside the open Proof");
    assert_eq!(flat_units, 1, "the scoped branch should retain one Proof");
    assert_eq!(
        context_exports, 0,
        "the scoped branch exported semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "the scoped branch checked a certificate"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "empty_branch.contract" && name == "generated certificate validation"
        )),
        "ordinary scoped branch construction must retain its checked structure: {events:#?}"
    );
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
                branch {
                    then { step(); }
                    else { step(); }
                }
                step();
            }
            simp();
        }
    "#;

    let ((((verified, events), certificate_checks), context_exports), flat_units) =
        proof::count_flat_proof_units(|| {
            {
                proof::count_execution_context_exports(|| {
                    proof::count_source_certificate_checks(|| {
                        crate::instrumentation::collect(|| {
                            verify_c0_sources(click_source, &[("selected_branch.c", c_source)])
                        })
                    })
                })
            }
        });
    let verified = verified.expect("the decided execution path should stay inside the open Proof");
    assert_eq!(flat_units, 1, "the decided scope should retain one Proof");
    assert_eq!(
        context_exports, 0,
        "the decided scope exported semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "the decided scope checked a certificate"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "selected_branch.contract" && name == "generated certificate validation"
        )),
        "the scoped decided branch must retain its searched proof steps directly: {events:#?}"
    );
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
    let (corrupted_result, corrupted_checks) = proof::count_source_certificate_checks(|| {
        verify_c0_sources(&corrupted, &[("selected_branch.c", c_source)])
    });
    corrupted_result
        .expect_err("tampering with the checked C-branch entry must invalidate the expansion");
    assert_eq!(
        corrupted_checks, 0,
        "the invalid C `if` checked a certificate"
    );
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

    let ((verified, _events), planning_transitions) = count_planning_statement_transitions(|| {
        crate::instrumentation::collect(|| {
            verify_c0_sources(click_source, &[("choose.c", c_source)])
        })
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
                ProofTactic::SmartExecute
                    | ProofTactic::SmartExecuteAllPaths
                    | ProofTactic::ExecuteUntil(_)
                    | ProofTactic::Simp
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
                have value >= 0 by auto;
                step();
                assumption();
            }
        "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("checked fixed-state smart have should verify");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "the migrated smart have must not pass through ordinary certificate validation: {events:#?}"
    );
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
                have x < z by simp;
                execute();
                simp();
            }
        "#;
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("first.c", c_source)])
    });
    verified.expect("checked fixed-state smart have should apply signed-order transitivity");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "first.contract" && name == "generated certificate validation"
        )),
        "the migrated theorem-backed have must not ordinarily check its certificate: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &[("first.c", c_source)],
        "first",
        CProofClaim::Grouped,
    )
    .expect("the theorem-backed have should expand into proof steps");
    assert!(!expanded.contains("have x < z by simp"), "{expanded}");
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

    let (verified, certificate_checks) = proof::count_source_certificate_checks(|| {
        verify_c0_sources(click_source, &[("identity.c", c_source)])
    });
    verified.expect("explicit fixed-state have should advance through its checked proof step");
    assert_eq!(
        certificate_checks, 0,
        "the admitted explicit fixed-state have should apply directly to Proof"
    );
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

    let ((verified, events), certificate_checks) = proof::count_source_certificate_checks(|| {
        crate::instrumentation::collect(|| {
            verify_c0_sources(click_source, &[("identity.c", c_source)])
        })
    });
    verified.expect("explicit post-execution have should advance through its outcome Proof");
    assert_eq!(
        certificate_checks, 0,
        "the admitted explicit outcome have should apply directly to Proof"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name.starts_with("post-execution simple have check")
        )),
        "the explicit outcome have must retain its checked Proof without fallback validation: {events:#?}"
    );

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
                requires wide: forall (k: int32) {
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

    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("bounded.c", c_source)])
    });
    verified.expect("the quantified outcome should verify through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
        )),
        "the binder-aware outcome certificate must not use compatibility construction: {events:#?}"
    );
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
        resource object_ref(obj: struct object*) {
            owns object(obj);
            fact obj->refs == count(object_ref(obj));
        }

        verifying "release.c";

        void release(struct object* obj) {
            requires obj->refs == 1;
            consumes object_ref(obj);
        } by {
            unfold(object_ref(obj));
            execute();
            simp();
        }
    "#;
    let sources = [("release.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("a final simp with no open claims should be a no-op");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
        )),
        "an empty claim set must not enter legacy exit planning: {events:#?}"
    );
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
        resource pool_object(pool: struct pool*) {}

        resource pool_slot(pool: struct pool*) {
            views object(pool);
        }

        predicate valid_pool(pool: struct pool*) {
            0 <= pool->checked_out and
            pool->checked_out == count(pool_object(pool)) and
            pool->capacity == pool->checked_out + count(pool_slot(pool))
        }

        verifying "init.c";

        void init(struct pool* pool, int32 capacity) {
            requires 0 < capacity;
            owns object(pool);
            produces capacity of pool_slot(pool);
            ensures valid_pool(pool);
        } by {
            execute();
            fold(capacity of pool_slot(pool));
            simp();
        }
    "#;
    let sources = [("init.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the unfolded resource-count goal should close through Proof");
    let compatibility_events = events
        .iter()
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "outcome simp legacy exit planning"
                        || name == "outcome simp compatibility construction"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        compatibility_events.is_empty(),
        "predicate closure must not enter outcome compatibility planning: {compatibility_events:#?}"
    );

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
fn outcome_predicate_unfold_uses_the_checked_frame_population_transition() {
    let c_source = r#"
        struct pool { int32 checked_out; };
        struct object { int32 value; };

        void give_back(struct pool* pool, struct object* object) {
            pool->checked_out = pool->checked_out - 1;
        }
    "#;
    let click_source = r#"
        resource pool_object(pool: struct pool*, object: struct object*) {
            owns object(object);
        }

        predicate valid_pool(pool: struct pool*) {
            0 <= pool->checked_out and
            pool->checked_out == count(pool_object(pool, _))
        }

        verifying "give_back.c";

        void give_back(struct pool* pool, struct object* object) {
            requires valid_pool(pool);
            requires count(pool_object(pool, object)) == 1;
            owns object(pool);
            consumes pool_object(pool, object);
            produces object(object);
            ensures valid_pool(pool);
        } by {
            unfold(valid_pool);
            unfold(pool_object(pool, object));
            execute();
            simp();
        }
    "#;
    let sources = [("give_back.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the checked frame population transition should reach the outcome Proof");
    let compatibility_events = events
        .iter()
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "outcome simp legacy exit planning"
                        || name == "outcome simp compatibility construction"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        compatibility_events.is_empty(),
        "the live population goal must not enter outcome compatibility planning: {compatibility_events:#?}"
    );

    let expanded =
        expand_c0_claim_source(click_source, &sources, "give_back", CProofClaim::Grouped)
            .expect("the retained population transition should expand");
    assert!(
        expanded.contains(
            "have 0 <= pool->checked_out and pool->checked_out == count(pool_object(pool, _)) by {"
        ),
        "{expanded}"
    );
    assert!(expanded.contains("unfold(valid_pool);"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained population transition should check independently");
}

#[test]
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
        verifying "sort_three_cells.c";

        int32 sort_three_cells(int32 p[3]) {
            requires loadable(p[0..3]);
            consumes p[0..3];
            ensures permutation(p, old(p), 0, 3) by {
                execute();
                unfold(permutation);
                simp();
            }
        }
    "#;
    let sources = [("sort_three_cells.c", c_source)];

    let ((verified, events), flat_units) = proof::count_flat_proof_units(|| {
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources))
    });
    verified.expect("the surviving unfold-owned universal should close through Proof");
    assert_eq!(
        flat_units, 1,
        "the nested outcome tree should retain one Proof"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "the retained predicate body must not enter outcome compatibility planning: {events:#?}"
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "sort_three_cells",
        CProofClaim::Ensure(0),
    )
    .expect("the retained nested predicate proof should expand");
    assert!(
        expanded.contains("have permutation(p, old(p), 0, 3) by {"),
        "{expanded}"
    );
    assert!(expanded.contains("normalize();"), "{expanded}");
    assert!(expanded.contains("unfold(permutation);"), "{expanded}");
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
    let (corrupted_result, corrupted_fallbacks) =
        { proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, &sources)) };
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
    assert_eq!(
        corrupted_fallbacks, 0,
        "an invalid nested branch anchor must not become a compatibility miss"
    );
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
                    have result == result by simp;
                } else {
                    have result == result by simp;
                }
                if at(statement(5).entry, y) > at(statement(5).entry, 0) {
                    have result == result by simp;
                } else {
                    have result == result by simp;
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
    let (corrupted_result, corrupted_fallbacks) =
        { proof::count_explicit_linear_fallbacks(|| verify_c0_sources(&corrupted, &sources)) };
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
    assert_eq!(corrupted_fallbacks, 0, "the corruption entered a fallback");
}

#[test]
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
            requires loadable(p[0..3]);
            consumes p[0..3];
            ensures all_le_range(p, 0, 2, p[2]);
        } by {
            step();
            step();
            step();
            loop {
                invariant j >= 0 and j <= 2;
                invariant all_le_range(p, 0, j, p[j]);
                initialize by {
                    unfold(all_le_range);
                    simp();
                }
                preserve by {
                    unfold(all_le_range);
                }
            }
            step();
            unfold(all_le_range);
            simp();
        }
    "#;
    let sources = [("bubble_pass3.c", c_source)];

    let ((verified, events), certificate_checks) = proof::count_source_certificate_checks(|| {
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources))
    });
    verified.expect("the bound universal outcome should close through Proof");
    assert_eq!(
        certificate_checks, 0,
        "universal candidate search must apply checked operations directly to Proof"
    );
    let fallback_events = events
        .iter()
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "outcome simp legacy exit planning"
                        || name == "outcome simp compatibility construction"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        fallback_events.is_empty(),
        "bound universal closure must not enter outcome compatibility planning: {fallback_events:#?}"
    );

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
    let (expanded, events) = crate::instrumentation::collect(|| {
        expand_c0_claim_source(click_source, &c_sources, function, CProofClaim::Grouped)
    });
    let expanded =
        expanded.unwrap_or_else(|error| panic!("failed to expand `{}`: {error:?}", path.display()));
    let fallback_events = events
        .iter()
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "outcome simp legacy exit planning"
                        || name == "outcome simp compatibility construction"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        fallback_events.is_empty(),
        "`{}` entered outcome fallback planning: {fallback_events:#?}",
        path.display()
    );

    assert!(
        expanded.contains("if k < (j - 1)"),
        "expanded proof from `{}` omitted the checked upper-bound split",
        path.display()
    );
    assert!(
        expanded.contains("int32_lt_successor_implies_le"),
        "expanded proof from `{}` omitted the split's explicit bound theorem",
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
fn bound_universal_bubble_pass3_max_suffix_has_no_outcome_fallbacks() {
    let (filename, function) = BOUND_UNIVERSAL_FIXTURE_CASES[0];
    assert_bound_universal_fixture_has_no_outcome_fallbacks(filename, function);
}

#[test]
fn bound_universal_bubble_sort3_two_pass_sorted_has_no_outcome_fallbacks() {
    let (filename, function) = BOUND_UNIVERSAL_FIXTURE_CASES[1];
    assert_bound_universal_fixture_has_no_outcome_fallbacks(filename, function);
}

#[test]
fn bound_universal_fixture_split_covers_original_census() {
    assert_eq!(
        BOUND_UNIVERSAL_FIXTURE_CASES,
        &[
            ("bubble_pass3_max_suffix.md", "bubble_pass3"),
            ("bubble_sort3_two_pass_sorted.md", "bubble_sort3_two_pass"),
        ]
    );
}

#[test]
fn snapshot_and_post_call_transport_fixtures_have_no_outcome_fallbacks() {
    for (filename, function, claim, retained_step) in [
        (
            "execute_expands_certified_post_call_fact.md",
            "restore_one",
            CProofClaim::Grouped,
            "rewrite(at(function.entry, cell->value",
        ),
        (
            "separate_symbolic_unwritten_read.md",
            "write_i_read_j",
            CProofClaim::Ensure(0),
            "normalize();",
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
        let (verified, events) =
            crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
        verified.unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));
        let fallback_events = events
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                        if name == "outcome simp legacy exit planning"
                            || name == "outcome simp compatibility construction"
                )
            })
            .collect::<Vec<_>>();
        assert!(
            fallback_events.is_empty(),
            "`{}` entered outcome fallback planning: {fallback_events:#?}",
            path.display()
        );

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
            "`{}` checked after deleting its selected retained step",
            path.display()
        );
        if filename == "separate_symbolic_unwritten_read.md" {
            let without_separation = expanded
                .lines()
                .filter(|line| !line.contains("separate(memory("))
                .collect::<Vec<_>>()
                .join("\n");
            assert!(
                verify_c0_sources(&without_separation, &c_sources).is_err(),
                "`{}` checked after deleting its required separation premises",
                path.display()
            );
        }
    }
}

const RESOURCE_EXAMPLE_PIPELINE_CASES: &[(&str, &str, &str, &str)] = &[
    (
        "linked-list",
        "linked_list.click",
        "list_roundtrip",
        "rewrite(at(statement(5).entry, observed) == at(statement(5).entry, node->value));",
    ),
    (
        "input-cursor",
        "input_cursor.click",
        "input_cursor_shared_pipeline",
        "have right->data[right->pos] == data[0] by {\n        rewrite(",
    ),
    (
        "owned-segmented-buffer",
        "owned_segmented_buffer.click",
        "owned_segmented_buffer_swap",
        "apply(int32_successor_le_implies_lt(0, owner->first_len)) using {",
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
        "apply(int32_increment_preserves_order(",
    ),
];

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

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(&click_source, &c_sources));
    verified.unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));
    let fallback_events = events
        .iter()
        .filter(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "outcome simp legacy exit planning"
                        || name == "outcome simp compatibility construction"
            )
        })
        .collect::<Vec<_>>();
    assert!(
        fallback_events.is_empty(),
        "`{}` entered outcome fallback planning: {fallback_events:#?}",
        path.display()
    );

    let expanded =
        expand_c0_claim_source(&click_source, &c_sources, function, CProofClaim::Grouped)
            .unwrap_or_else(|error| panic!("failed to expand `{}`: {error:?}", path.display()));
    assert!(expanded.contains(retained_step), "{expanded}");
    verify_c0_sources(&expanded, &c_sources).unwrap_or_else(|error| {
        panic!(
            "expanded proof from `{}` failed independent verification: {error:?}",
            path.display()
        )
    });
}

#[test]
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
fn resource_example_pipeline_split_covers_original_census() {
    assert_eq!(
        RESOURCE_EXAMPLE_PIPELINE_CASES,
        &[
            (
                "linked-list",
                "linked_list.click",
                "list_roundtrip",
                "rewrite(at(statement(5).entry, observed) == at(statement(5).entry, node->value));",
            ),
            (
                "input-cursor",
                "input_cursor.click",
                "input_cursor_shared_pipeline",
                "have right->data[right->pos] == data[0] by {\n        rewrite(",
            ),
            (
                "owned-segmented-buffer",
                "owned_segmented_buffer.click",
                "owned_segmented_buffer_swap",
                "apply(int32_successor_le_implies_lt(0, owner->first_len)) using {",
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
                "apply(int32_increment_preserves_order(",
            ),
        ]
    );
}

#[test]
fn smart_have_expansion_plans_against_the_ordinary_surface_goal() {
    let manifest = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let path = manifest
        .join("examples")
        .join("ring-buffer")
        .join("ring_buffer.click");
    let explicit = std::fs::read_to_string(&path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
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

            let (result, events) =
                crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
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
            let fallback_events = events
                .iter()
                .filter(|event| {
                    matches!(
                        event,
                        crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                            if name == "outcome simp legacy exit planning"
                                || name == "outcome simp compatibility construction"
                    )
                })
                .collect::<Vec<_>>();
            assert!(
                fallback_events.is_empty(),
                "{class} fixture `{}` entered outcome fallback planning: {fallback_events:#?}",
                path.display()
            );
        }
    }
}

#[test]
fn branch_continuation_claims_retain_their_selected_outcome_step() {
    for (filename, function, claim, claim_label) in [
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
        let (verified, events) =
            crate::instrumentation::collect(|| verify_c0_sources(click_source, &c_sources));
        verified.unwrap_or_else(|error| panic!("`{}` failed: {error:?}", path.display()));
        let fallback_events = events
            .iter()
            .filter(|event| {
                matches!(
                    event,
                    crate::instrumentation::VerificationEvent::OperationFinished {
                        claim,
                        name,
                        ..
                    } if claim == claim_label
                        && (name == "outcome simp legacy exit planning"
                            || name == "outcome simp compatibility construction")
                )
            })
            .collect::<Vec<_>>();
        assert!(
            fallback_events.is_empty(),
            "`{claim_label}` entered outcome fallback planning: {fallback_events:#?}"
        );
        if filename == "proof_branch_continuation.md" {
            let captured = crate::surface::proof::capture_c0_tactic_expansion(
                click_source,
                &c_sources,
                crate::surface::expansion::ProofSite::FunctionClaim {
                    function_name: function.to_string(),
                    claim: CProofClaim::Ensure(1),
                },
                0,
            )
            .expect("the selected pre-branch step should have one stable expansion");
            assert!(
                matches!(captured.as_slice(), [ProofTactic::Step]),
                "the selected step absorbed a later structured branch: {captured:#?}"
            );
        }

        let retained_step = "apply(int32_increment_strict_greater_lower_bound(";
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
            requires loadable(p[0..1]);
            ensures loadable(p[0..1]);
        } by {
            execute();
            simp();
        }

        int32 use_summary(int32* p) {
            requires loadable(p[0..1]);
            ensures loadable(p[0..1]);
        } by {
            execute();
            simp();
        }
    "#;
    let sources = [("summarize.c", summarize_c), ("use_summary.c", use_c)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the call-preserved loadability should transport through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
        )),
        "outcome loadability transport must bypass compatibility construction: {events:#?}"
    );

    let expanded =
        expand_c0_claim_source(click_source, &sources, "use_summary", CProofClaim::Grouped)
            .expect("the retained loadability transport should expand");
    assert!(expanded.contains("transport"), "{expanded}");
    verify_c0_sources(&expanded, &sources)
        .expect("the retained loadability transport should check independently");
}

#[test]
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
            requires loadable(p[0..n]);
            consumes p[0..n];
            ensures keeps_first: p[0] == old(p[0]);
            ensures returns_n: result == n;
        } by {
            step();
            step();
            loop {
                owns (p + 1)[0..n - 1];
                invariant i >= 1;
                invariant i <= n;
            }
            step();
            simp();
        }
    "#;
    let sources = [("shifted.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the unchanged old equality should advance Proof");
    let simp_start = events
        .iter()
        .rposition(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::TacticStarted(tactic)
                    if tactic.claim == "shifted_loop_effect_preserves_prefix.contract"
                        && tactic.tactic_name == "simp"
            )
        })
        .expect("the final smart simp should be instrumented");
    let simp_end = events[simp_start..]
        .iter()
        .position(|event| {
            matches!(
                event,
                crate::instrumentation::VerificationEvent::TacticFinished { tactic, .. }
                    if tactic.claim == "shifted_loop_effect_preserves_prefix.contract"
                        && tactic.tactic_name == "simp"
            )
        })
        .map(|offset| simp_start + offset)
        .expect("the final smart simp should finish");
    assert!(
        events[simp_start..=simp_end].iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp compatibility construction"
        )),
        "outcome old equality must bypass compatibility construction during the final simp: {:#?}",
        &events[simp_start..=simp_end]
    );

    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "shifted_loop_effect_preserves_prefix",
        CProofClaim::Grouped,
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
    let click_source = r#"
        verifying "byte_prefix.c";

        int32 byte_prefix(uint8 p[], int32 n) {
            requires loadable(p[0..3]);
            requires no_y: bytes_all_not_eq(p, 0, 3, 'y');
            ensures p[1] != 'y' by {
                execute();
                unfold(bytes_all_not_eq);
                simp();
            }
        }
    "#;
    let sources = [("byte_prefix.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the unfolded byte universal should instantiate through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "unfolded universal closure must not enter outcome compatibility planning: {events:#?}"
    );

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
            contains backing_buffer(owner);
            fact 0 <= owner->len;
            fact owner->len <= owner->cap;
        }

        verifying "observe.c";

        int32 observe_nested_separate_contains(struct owner* owner) {
            consumes nested_owned_buffer(owner);
            ensures separate(
                memory(owner[0..3]),
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

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified
        .expect("the observed composition should certify its selected separation through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "selected resource separation must not enter outcome compatibility planning: {events:#?}"
    );

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
            requires loadable(dst[0..n]);
            requires loadable(src[0..n]);
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
                invariant i >= 1;
                invariant i <= n;
            }
            step();
            simp();
        }
    "#;
    let sources = [("shifted_copy.c", c_source)];

    let (verified, events) =
        crate::instrumentation::collect(|| verify_c0_sources(click_source, &sources));
    verified.expect("the quantified old equality should transport through Proof");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "outcome simp legacy exit planning"
                    || name == "outcome simp compatibility construction"
        )),
        "quantified old transport must not enter outcome compatibility planning: {events:#?}"
    );

    let expanded =
        expand_c0_claim_source(click_source, &sources, "shifted_copy", CProofClaim::Grouped)
            .expect("the retained quantified transport should expand");
    assert!(expanded.contains("intro();"), "{expanded}");
    assert!(expanded.contains("extract(0 <= k);"), "{expanded}");
    assert!(expanded.contains("extract(k < n);"), "{expanded}");
    assert!(
        expanded.contains("transport(old(src[k]) == old(src[k]), src[k] == old(src[k])) using {"),
        "{expanded}"
    );
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
    let (
        ((((verified, events), explicit_fallbacks), certificate_checks), context_exports),
        flat_units,
    ) = proof::count_flat_proof_units(|| {
        {
            proof::count_execution_context_exports(|| {
                proof::count_source_certificate_checks(|| {
                    proof::count_explicit_linear_fallbacks(|| {
                        crate::instrumentation::collect(|| {
                            verify_c0_sources(click_source, &[("identity.c", c_source)])
                        })
                    })
                })
            })
        }
    });
    verified.expect("the unfold-then-simp have should verify through Proof");
    assert_eq!(flat_units, 1, "the grouped proof should retain one Proof");
    assert_eq!(
        context_exports, 0,
        "the leading predicate have exported semantic state"
    );
    assert_eq!(
        certificate_checks, 0,
        "ordinary predicate-have verification checked a certificate"
    );
    assert_eq!(
        explicit_fallbacks, 0,
        "the explicit predicate proof used the compatibility driver"
    );
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { claim, name, .. }
                if claim == "identity.contract" && name == "generated certificate validation"
        )),
        "the migrated unfold-then-simp path must retain its checked Proof: {events:#?}"
    );
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

            int32 holder_zero(struct holder* owner, int32 data[]) {
                requires owner->data == data;
                views object(owner);
                ensures result == 0;
            } by {
                have owner->data == data by simp;
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

            predicate second_is(owner: struct holder*, value: int32) {
                owner->data[1] == value
            }

            int32 holder_read(
                struct holder* owner,
                int32 data[],
                int32 value
            ) {
                requires owner->data == data;
                requires separate(memory(object(owner)), memory(data[1..2]));
                requires second_is(owner, value);
                views object(owner);
                views data[1..2];
                ensures result == 0;
            } by {
                unfold(second_is);
                have data[1] == value by simp;
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
                consumes p[0..2];
                produces p[0..2];
            } by {
                unfold(first_is_seven);
                step();
                have p[0] == 7 by simp;
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
fn smart_have_uses_fact_selected_by_explicit_step_at_the_mutation_boundary() {
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
                consumes p[0..2];
                produces p[0..2];
            } by {
                unfold(first_is_seven);
                step();
                have p[0] == 7 by simp;
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
            .expect("the fact retained by `step()` should reach the current snapshot");
    let expanded_have = &expanded[expanded
        .find("have p[0] == 7")
        .expect("expanded proof should retain the selected have")
        ..expanded
            .find("step();\n                simp();")
            .expect("expanded proof should retain its suffix")];
    assert!(expanded_have.contains("assumption();"), "{expanded_have}");
    assert!(!expanded_have.contains("simp();"), "{expanded_have}");
    verify_c0_sources(&expanded, &[("transport.c", c_source)])
        .expect("the explicit-step boundary transport should check");
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
                have at(statement(1).entry, p[0]) == 1 by simp;
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
                requires separate(memory(owner[0..4]), memory(data[0..length]));
                consumes owner[0..4];
                views data[0..length];
                produces owner[0..4];
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
                requires separate(memory(left[0..4]), memory(data[0..length]));
                requires separate(memory(right[0..4]), memory(data[0..length]));
                consumes left[0..4];
                consumes right[0..4];
                views data[0..length];
                produces left[0..4];
                produces right[0..4];
                ensures result == 0;
            } by {
                execute_until(statement(2));
                have separate(
                    memory(right[0..4]),
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
fn source_expander_is_idempotent() {
    let c_source = r#"
            int32 identity(int32 x) {
                return x;
            }
        "#;
    let click_source = r#"
            verifying "identity.c";

            int32 identity(int32 x) {
                ensures result == x by { execute(); simp(); }
            }
        "#;
    let sources = [("identity.c", c_source)];

    let expanded_once =
        expand_c0_claim_source(click_source, &sources, "identity", CProofClaim::Ensure(0))
            .expect("smart proof should expand");
    let expanded_twice =
        expand_c0_claim_source(&expanded_once, &sources, "identity", CProofClaim::Ensure(0))
            .expect("expanded proof should expand again");

    assert_eq!(expanded_once, expanded_twice);
}

#[test]
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
    verify_c0_sources(source, &sources).unwrap();
    for name in ["reset", "read_cache", "main"] {
        let expanded =
            expand_c0_claim_source(source, &sources, name, CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{error:?}\n{expanded}"));
    }
    let wrong = source.replace("result == 12", "result == 7");
    assert!(verify_c0_sources(&wrong, &sources).is_err());
}

#[test]
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
        verify_c0_sources(source, &sources).unwrap();
        for function in functions {
            let expanded =
                expand_c0_claim_source(source, &sources, function, CProofClaim::Grouped).unwrap();
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
            "verifying \"storage.c\" as storage; void f(int parameter) {{ owns &storage::{name}[0..1]; }}"
        );
        assert!(
            verify_c0_sources(&source, &[("storage.c", c_source)]).is_err(),
            "accepted {name}"
        );
    }
}

#[test]
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
    let original = "uint32 twice() {\n    owns &counter_file::increment::calls[0..1];";
    assert!(source.contains(original));
    for replacement in [
        "uint32 twice() {",
        "uint32 twice() { views &counter_file::increment::calls[0..1];",
        "uint32 twice() { owns &counter_file::other::calls[0..1];",
        "uint32 twice() { owns &counter_file::calls[0..1];",
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
    requires loadable(p[0..1]);
    owns p[0..1];
    ensures p[0] == 0;
} by { execute(); simp(); }
void clear() {
    owns &left::count[0..1];
    ensures left::count == 0;
} by { execute(); simp(); }
int main() { ensures result == 0; } by { execute(); simp(); }
"#;
    verify_c0_sources(source, &sources).unwrap();
    for invalid in [
        source.replace("owns &left::count[0..1];", ""),
        source.replace("owns &left::count", "owns &right::count"),
        source.replace("owns &left::count", "owns &missing::count"),
        source.replace("owns &left::count", "owns &left::missing"),
        source.replace("as right", "as left"),
        source.replace("owns &left::count[0..1];", "owns &left::count[0..2];"),
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
    requires loadable(p[0..1]);
    owns p[0..1];
    ensures p[0] == 0;
} by { execute(); simp(); }
void clear() {
    owns &counter::count[0..1];
    ensures counter::count == 0;
} by { execute(); simp(); }"#;
    verify_c0_sources(source, &sources).unwrap();
    let missing = source.replace("owns &counter::count[0..1];", "");
    assert!(
        verify_c0_sources(&missing, &sources).is_err(),
        "a helper call cannot manufacture ownership"
    );
}

#[test]
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
    verify_c0_sources(source, &sources).unwrap();
    for name in ["read_value", "current", "main"] {
        let expanded =
            expand_c0_claim_source(source, &sources, name, CProofClaim::Grouped).unwrap();
        verify_c0_sources(&expanded, &sources)
            .unwrap_or_else(|error| panic!("{error:?}\n{expanded}"));
    }
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
fn private_state_bump_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "bump");
}
#[test]
fn private_state_reset_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "reset");
}
#[test]
fn private_state_left_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "left");
}
#[test]
fn private_state_right_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "right");
}
#[test]
fn private_state_reset_left_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "reset_left");
}
#[test]
fn private_state_main_expands() {
    check_private_state_expansion("private_state_mutation_reset.md", "main");
}
#[test]
fn private_state_wide_return_expands() {
    check_private_state_expansion("private_state_wide_return.md", "main");
}
#[test]
fn private_state_narrowing_call_expands() {
    check_private_state_expansion("private_state_narrowing_call.md", "main");
}
#[test]
fn private_state_signed_bounds_expand() {
    check_private_state_expansion("private_state_narrowing_bounds.md", "signed_value");
}
#[test]
fn private_state_unsigned_bounds_expand() {
    check_private_state_expansion("private_state_narrowing_bounds.md", "unsigned_value");
}

#[test]
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
fn private_state_narrowing_rejects_unproved_bounds() {
    let fixture_name = "private_state_narrowing_bounds.md";
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
    for bound in [
        "requires value >= -2147483648i64;",
        "requires value <= 2147483647i64;",
        "requires value <= 2147483647u64;",
    ] {
        assert!(
            verify_c0_sources(&source.replace(bound, ""), &sources).is_err(),
            "missing bound accepted: {bound}"
        );
    }
}

#[test]
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
fn pure_pointer_add_zero_simp_expands_to_rewrite_and_assumption() {
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
    assert!(expanded.contains("rewrite(offset == 0);"), "{expanded}");
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
    assert!(expanded.contains("left();"), "{expanded}");
    assert!(expanded.contains("right();"), "{expanded}");
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
        expanded.contains("apply(int32_successor_le_implies_lt("),
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
                owns object(pair);

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
    let (verified, events) = crate::instrumentation::collect(|| {
        verify_c0_sources(click_source, &[("set_pair.c", c_source)])
    });
    verified.expect("the unfolded conjunction should verify on the checked Proof path");
    assert!(
        events.iter().all(|event| !matches!(
            event,
            crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                if name == "post-execution smart have compatibility construction"
                    || name.starts_with("post-execution simple have check")
        )),
        "the checked unfold and structural simp must not reconstruct or check their proof: {events:#?}"
    );
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
                owns object(pair);

                ensures ordered_pair(pair);
            } by {
                unfold(ordered_pair);
                execute();
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
/// across the `return` call's `object(owner)` effect: the frame check locates
/// `data + start` inside the composite buffer's owned range through the
/// contract bounds without encoding them in the emitted statement step.
#[test]
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
                invariant i >= 0;
                invariant i <= 1;
                initialize by simp;
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
    verify_c0_sources(click_source, &sources).expect("the preservation case after a step verifies");
    let expanded =
        expand_c0_claim_source(click_source, &sources, "count_once", CProofClaim::Grouped)
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
                invariant i >= 0;
                invariant i <= 1;
                initialize by simp;
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
    verify_c0_sources(click_source, &sources)
        .expect("the preservation case before a step verifies");
    let expanded =
        expand_c0_claim_source(click_source, &sources, "count_once", CProofClaim::Grouped)
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
fn loop_entry_lowering_guard_expands_to_an_explicit_introduction() {
    // Lowering wraps this loop's quantified entry obligation in a loadability
    // guard that has no Surface connective. The guard is derivable at entry
    // but is not exactly available, so it stays part of the goal that planning
    // and independent validation both compute, and the retained certificate
    // must discharge it with an explicit introduction.
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
            requires loadable(p[0..3]);
            consumes p[0..3];
            ensures returns_third: result == 2;
        } by {
            step();
            step();
            loop {
                invariant i >= 0 and i <= 3;
                invariant forall (k: int32) { 0 <= k and k < i implies p[k] == k };
                initialize by simp;
                preserve by simp;
            }
            step();
            simp();
        }
    "#;
    let sources = [("fill3_entry_guard.c", c_source)];
    verify_c0_sources(click_source, &sources).expect("the entry-guard loop proof should verify");
    let expanded = expand_c0_claim_source(
        click_source,
        &sources,
        "fill3_entry_guard",
        CProofClaim::Grouped,
    )
    .expect("the entry-guard loop proof should expand");
    let initialize = expanded
        .find("initialize by")
        .expect("the expansion keeps the initialization proof");
    let preserve = expanded
        .find("preserve by")
        .expect("the expansion keeps the preservation proof");
    assert!(initialize < preserve, "{expanded}");
    assert!(
        expanded[initialize..preserve].contains("intro();"),
        "the initialization certificate must introduce the lowering guard: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("expanded entry-guard proof failed independent verification: {error:?}\n{expanded}")
    });
    let missing_intro = format!(
        "{}{}",
        expanded[..preserve].replacen("intro();", "", 1),
        &expanded[preserve..]
    );
    assert_ne!(missing_intro, expanded, "{expanded}");
    verify_c0_sources(&missing_intro, &sources)
        .expect_err("deleting the retained guard introduction must be rejected at validation");
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
        expanded.contains("at(function.entry, limit > 0);"),
        "the expansion must cite the ambient fact the branch choice rests on: {expanded}"
    );
    verify_c0_sources(&expanded, &sources).unwrap_or_else(|error| {
        panic!("expanded conditional proof failed independent verification: {error:?}\n{expanded}")
    });
    let uncited = expanded.replacen(
        "normalize() using {\n        at(function.entry, limit > 0);\n    }",
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
        witness(z = to_integer(x));
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
        "theorem bad(x: int32) { ensures exists(z: Integer) { z == to_integer(x + 1) } by { witness(z = to_integer(x + 1)); simp(); } }",
        "theorem bad(x: int32) { ensures forall(z: Integer) { to_integer(x + 1) == to_integer(x + 1) } by { simp(); } }",
    ] {
        assert!(
            verify_c0_sources(invalid, &[]).is_err(),
            "invalid quantified domain or opaque equality verified: {invalid}"
        );
    }
}
