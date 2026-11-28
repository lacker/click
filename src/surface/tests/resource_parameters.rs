use super::expansion_tests::mdtest_sources;
use super::*;

const ABSTRACT_PROOF: &str = r#"
import click::separation;
theorem restrict_again(A: Resource, B: Resource, a: Resource, b: Resource) {
    requires separate(A, B);
    requires contains(A, a);
    requires contains(B, b);
    ensures separate(a, b) by {
        apply(separation::separate_restrict(A, B, a, b));
        close();
    }
}
"#;

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_00"
)]
fn resource_parameters_apply_explicit_axiom_and_expand() {
    without_implicit_solve(|| verify_click_theorems(ABSTRACT_PROOF)).unwrap();
    let expanded =
        expand_c_claim_source_by_label(ABSTRACT_PROOF, &[], "restrict_again.ensures_0").unwrap();
    assert!(expanded.contains("Resource"));
    without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_00"
)]
fn resource_parameters_require_every_theorem_premise() {
    for premise in ["separate(A, B);", "contains(A, a);", "contains(B, b);"] {
        let missing = ABSTRACT_PROOF.replace(&format!("requires {premise}"), "");
        assert_ne!(missing, ABSTRACT_PROOF);
        assert!(
            without_implicit_solve(|| verify_click_theorems(&missing)).is_err(),
            "{premise}"
        );
    }
    let wrong = ABSTRACT_PROOF.replace("restrict(A, B, a, b)", "restrict(A, B, A, b)");
    assert!(without_implicit_solve(|| verify_click_theorems(&wrong)).is_err());
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_00"
)]
fn resource_parameters_refuse_numeric_arguments() {
    let wrong = ABSTRACT_PROOF.replace("restrict(A, B, a, b)", "restrict(0, B, a, b)");
    assert!(verify_click_theorems(&wrong).is_err());
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_00"
)]
fn resource_parameters_prove_field_separation_without_search() {
    let (source, sources) = mdtest_sources("mdtests/resource_theorem_parameters.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    without_implicit_solve(|| verify_c_sources(&source, &sources)).unwrap();
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_01"
)]
fn resource_parameters_capture_simultaneously() {
    let client = r#"
    theorem swapped(B: Resource, A: Resource, b: Resource, a: Resource) {
        requires separate(B, A);
        requires contains(B, b);
        requires contains(A, a);
        ensures separate(b, a) by {
            apply(restrict_again(B, A, b, a));
            close();
        }
    }
    "#;
    without_implicit_solve(|| verify_click_theorems(&format!("{ABSTRACT_PROOF}{client}"))).unwrap();
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_01"
)]
fn resource_parameters_accept_declared_descriptors() {
    let source = r#"
    abstract resource ticket(id: int32);
    resource cell(p: int32*) { owns *p; }
    theorem transport(A: Resource, B: Resource) {
        requires separate(A, B);
        ensures separate(A, B) by { close(); }
    }
    theorem declared(p: int32*, id: int32) {
        requires separate(cell(p), ticket(id));
        ensures separate(cell(p), ticket(id)) by {
            apply(transport(cell(p), ticket(id)));
            close();
        }
    }
    "#;
    without_implicit_solve(|| verify_click_theorems(source)).unwrap();
    let expanded = expand_c_claim_source_by_label(source, &[], "declared.ensures_0").unwrap();
    without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_01"
)]
fn resource_parameters_do_not_grant_ownership_or_numeric_values() {
    for source in [
        "theorem invalid(A: Resource) { owns A; ensures true; }",
        "theorem invalid(A: Resource) { produces A; ensures true; }",
        "theorem invalid(A: Resource) { ensures A == 0; }",
        "theorem numeric(x: int32) { ensures x == x; }\n\
         theorem invalid(A: Resource) { ensures 0 == 0 by { apply(numeric(A)); } }",
        "theorem invalid(A: Resource) { ensures separate(A, A) by { let A: int32 = 0; } }",
    ] {
        assert!(verify_click_theorems(source).is_err(), "{source}");
    }
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_01"
)]
fn generic_pointer_parameters_subrange_and_expansion() {
    let (source, sources) = mdtest_sources("mdtests/generic_pointer_theorem_parameters.md");
    assert!(sources.is_empty());
    without_implicit_solve(|| verify_click_theorems(&source)).unwrap();
    for label in [
        "integers.ensures_0",
        "bytes.ensures_0",
        "pointers.ensures_0",
    ] {
        let expanded = expand_c_claim_source_by_label(&source, &[], label).unwrap();
        without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
    }
    let (definitions, callers) = source.split_once("theorem integers").unwrap();
    for premise in ["lo <= a;", "a <= b;", "b <= hi;"] {
        let caller_without_premise = callers.replacen(&format!("requires {premise}"), "", 1);
        assert_ne!(caller_without_premise, callers);
        let missing = format!("{definitions}theorem integers{caller_without_premise}");
        assert!(without_implicit_solve(|| verify_click_theorems(&missing)).is_err());
    }
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_02"
)]
fn generic_pointer_parameters_require_consistent_element_types() {
    let source = r#"
        theorem same<T>(p: T*, q: T*) {
            ensures true by { close(); }
        }
        theorem wrong(p: int32*, q: uint8*) {
            ensures true by {
                apply(same(p, q));
            }
        }
    "#;
    let error = verify_click_theorems(source).unwrap_err();
    assert!(
        error.report().contains("type parameter"),
        "{}",
        error.report()
    );
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_02"
)]
fn generic_pointer_struct_parameters_apply_and_expand() {
    let (source, sources) = mdtest_sources("mdtests/generic_pointer_struct_parameters.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    without_implicit_solve(|| verify_c_sources(&source, &sources)).unwrap();
    for label in ["inspect.contract", "padded.ensures_0"] {
        let expanded = expand_c_claim_source_by_label(&source, &sources, label).unwrap();
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
    let context = crate::surface::verification::ProgramSourceContext::bundle(&sources);
    let verified = without_implicit_solve(|| {
        crate::surface::verification::verify_click_theorem_context(&source, &context, "padded")
    })
    .unwrap();
    let padded = verified
        .iter()
        .find(|theorem| theorem.theorem_definition.name() == "padded")
        .unwrap();
    let Proposition::ResourceContains { parent, child } = &padded.conclusion else {
        panic!("expected containment");
    };
    for resource in [parent, child] {
        let crate::kernel::Resource::Memory(range) = resource.as_ref() else {
            panic!("expected memory");
        };
        assert_eq!(
            range.element_width(),
            16,
            "the padded struct keeps its physical stride"
        );
    }

    let no_origin = source.replace("theorem identity<T>", "theorem requires_item(p: struct item*) { ensures p == p by { close(); } }\ntheorem identity<T>")
        .replace("have p == p by { apply(identity(p)); close(); }", "have p == p by { apply(identity(p)); close(); }\n    have p == p by { apply(requires_item(p)); }");
    assert!(no_origin.contains("apply(requires_item(p));"));
    let error = without_implicit_solve(|| verify_c_sources(&no_origin, &sources)).unwrap_err();
    assert!(
        error.report().contains("requires original object class"),
        "{}",
        error.report()
    );

    let wrong = source
        .replace(
            "theorem identity<T>(p: T*)",
            "theorem identity<T>(p: T*, q: T*)",
        )
        .replace("apply(identity(p))", "apply(identity(p, q))");
    let error = without_implicit_solve(|| verify_c_sources(&wrong, &sources)).unwrap_err();
    assert!(
        error.report().contains("type parameter"),
        "{}",
        error.report()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 2.6s in the parallel gate"]
fn elements_separation_applies_and_expands_without_implicit_search() {
    for (fixture, labels) in [
        ("mdtests/separation_elements.md", vec!["keep.contract"]),
        (
            "mdtests/separation_elements_signed_store.md",
            vec!["keep.contract"],
        ),
        (
            "mdtests/separation_elements_signed.md",
            vec![
                "signed_bytes.ensures_0",
                "signed_words.ensures_0",
                "negative_byte.ensures_0",
                "unsigned_zero.ensures_0",
            ],
        ),
        (
            "mdtests/separation_elements_types.md",
            vec!["words.ensures_0", "pointers.ensures_0", "inspect.contract"],
        ),
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        without_implicit_solve(|| verify_c_sources(&source, &sources)).unwrap();
        for label in labels {
            let expanded = expand_c_claim_source_by_label(&source, &sources, label).unwrap();
            without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
        }
    }
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_02"
)]
fn elements_separation_requires_distinct_indices() {
    for ty in ["int32", "int64", "uint64"] {
        for (requirement, arguments) in [("", "i, j"), ("requires i != j;", "i, i")] {
            let source = format!(
                r#"
            import click::separation;
            theorem invalid(p: uint8*, i: {ty}, j: {ty}) {{
                {requirement}
                ensures separate(memory(p[i]), memory(p[j])) by {{
                    apply(separation::separate_elements(p, {arguments}));
                }}
            }}
        "#
            );
            assert!(without_implicit_solve(|| verify_click_theorems(&source)).is_err());
        }
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6.8s in the parallel gate"]
fn equal_array_base_separation_restricts_and_replays_without_search() {
    let (source, sources) = mdtest_sources("mdtests/separation_restricts_equal_array_bases.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    without_implicit_solve(|| verify_c_sources(&source, &sources)).unwrap();
    let expanded = expand_c_claim_source_by_label(&source, &sources, "selected.ensures_0").unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    let missing_alias = source.replace("    requires p == q;", "");
    let error = without_implicit_solve(|| verify_c_sources(&missing_alias, &sources)).unwrap_err();
    assert!(error.report().contains("rewrite"), "{}", error.report());
    let out_of_range = source.replace(
        "ensures separate(A, memory(q[i]))",
        "ensures separate(A, memory(q[cap]))",
    );
    assert!(without_implicit_solve(|| verify_c_sources(&out_of_range, &sources)).is_err());
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_02"
)]
fn elements_separation_does_not_widen_byte_cells() {
    let source = r#"
        import click::separation;
        theorem invalid(p: uint8*, i: int32, j: int32) {
            requires i != j;
            ensures separate(memory(p[i..i+4]), memory(p[j])) by {
                apply(separation::separate_elements(p, i, j));
            }
        }
    "#;
    assert!(without_implicit_solve(|| verify_click_theorems(source)).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn separating_conjunction_laws_expand_without_implicit_search() {
    let (source, inputs) = mdtest_sources("mdtests/separation_conjunction.md");
    let inputs = inputs
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    without_implicit_solve(|| verify_c_sources(&source, &inputs)).unwrap();
    for claim in ["frame.ensures_0", "components.ensures_0", "empty.ensures_0"] {
        let expanded = expand_c_claim_source_by_label(&source, &inputs, claim).unwrap();
        without_implicit_solve(|| verify_c_sources(&expanded, &inputs)).unwrap();
    }
}

#[test]
fn conjunction_nodes_keep_multiplicity_and_session_identity() {
    let _session = crate::kernel::VerificationSession::enter();
    let a = crate::kernel::Resource::Parameter(Variable(987));
    let repeated = crate::kernel::Resource::star(a.clone(), a.clone());
    assert_ne!(repeated, a);
    assert_eq!(
        repeated,
        crate::kernel::Resource::star(a.clone(), a.clone())
    );
    let retained_state = crate::kernel::VerificationSession::capture_state();
    let entry_count = crate::kernel::VerificationSession::state_entry_count();
    let other = crate::kernel::Resource::star(repeated.clone(), a.clone());
    assert_ne!(repeated, other);
    assert!(crate::kernel::VerificationSession::state_entry_count() > entry_count);
    assert!(crate::kernel::VerificationSession::restore_state(
        &retained_state
    ));
    assert_eq!(
        entry_count,
        crate::kernel::VerificationSession::state_entry_count()
    );
    assert_eq!(repeated, crate::kernel::Resource::star(a.clone(), a));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn recursive_call_resource_bound_is_explicit_and_replays() {
    for fixture in [
        "recursive_call_footprint_containment",
        "recursive_call_pair_footprint_containment",
        "recursive_call_result_footprint_containment",
    ] {
        let (source, inputs) = mdtest_sources(&format!("mdtests/{fixture}.md"));
        let inputs = inputs
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        with_proof_trace("caller", || {
            let verified = verify_c_sources(&source, &inputs).unwrap_or_else(|error| {
                panic!(
                    "{fixture}: {}\n{}",
                    error.report(),
                    error.trace_context_report().unwrap_or_default()
                )
            });
            let expanded =
                super::expand_checked_grouped_claim(&source, &verified, "caller").unwrap();
            verify_c_sources(&expanded, &inputs)
                .unwrap_or_else(|error| panic!("{fixture}: {}\n{expanded}", error.report()));
        });
    }
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_03"
)]
fn wide_subrange_applies_and_expands_without_implicit_solve() {
    let (source, sources) = mdtest_sources("mdtests/separation_subrange_supports_wide_bounds.md");
    assert!(sources.is_empty());
    without_implicit_solve(|| verify_click_theorems(&source)).unwrap();
    let expanded = expand_c_claim_source_by_label(&source, &[], "wide.ensures_0").unwrap();
    without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
    for premise in ["lo <= a;", "a <= b;", "b <= hi;"] {
        let missing = source.replacen(&format!("requires {premise}"), "", 1);
        assert_ne!(missing, source);
        assert!(without_implicit_solve(|| verify_click_theorems(&missing)).is_err());
    }
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_03"
)]
fn element_containment_expands_without_implicit_solve() {
    let (source, _) = mdtest_sources("mdtests/separation_element_contains_the_selected_cell.md");
    without_implicit_solve(|| verify_click_theorems(&source)).unwrap();
    for label in ["signed.ensures_0", "wide.ensures_0"] {
        let expanded = expand_c_claim_source_by_label(&source, &[], label).unwrap();
        without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
    }
    for premise in ["requires lo <= i;", "requires i < hi;"] {
        let missing = source.replacen(premise, "", 1);
        assert_ne!(missing, source);
        assert!(without_implicit_solve(|| verify_click_theorems(&missing)).is_err());
    }
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_03"
)]
fn rebased_intervals_apply_and_replay_without_search() {
    let (source, _) = mdtest_sources("mdtests/separation_rebase.md");
    without_implicit_solve(|| verify_click_theorems(&source)).unwrap();
    for label in ["rebase_narrow.ensures_0", "rebase_wide.ensures_0"] {
        let expanded = expand_c_claim_source_by_label(&source, &[], label).unwrap();
        without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
    }
    for premise in ["requires 0 <= lo;", "requires lo <= hi;"] {
        let missing = source.replace(premise, "");
        assert!(without_implicit_solve(|| verify_click_theorems(&missing)).is_err());
    }
    let enlarged = source.replace("0..hi-lo]", "0..hi-lo+1]");
    assert!(without_implicit_solve(|| verify_click_theorems(&enlarged)).is_err());
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by resource_parameters_batch_03"
)]
fn adjacent_ranges_apply_and_replay_without_search() {
    let (source, _) = mdtest_sources("mdtests/separation_adjacent_ranges.md");
    without_implicit_solve(|| verify_click_theorems(&source)).unwrap();
    for label in ["narrow.ensures_0", "wide.ensures_0", "empty.ensures_0"] {
        let expanded = expand_c_claim_source_by_label(&source, &[], label).unwrap();
        without_implicit_solve(|| verify_click_theorems(&expanded)).unwrap();
    }
    for premise in ["requires lo <= mid;", "requires mid <= hi;"] {
        let missing = source.replacen(premise, "", 1);
        assert_ne!(missing, source);
        assert!(without_implicit_solve(|| verify_click_theorems(&missing)).is_err());
    }
    let overlap = source.replace("memory(p[mid..hi])", "memory(p[lo..hi])");
    assert!(without_implicit_solve(|| verify_click_theorems(&overlap)).is_err());
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "resource_parameters.rs",
    marker: "resource_parameters_batch_",
    resource_parameters_batch_00: [
        resource_parameters_apply_explicit_axiom_and_expand,
        resource_parameters_require_every_theorem_premise,
        resource_parameters_refuse_numeric_arguments,
        resource_parameters_prove_field_separation_without_search,
    ],
    resource_parameters_batch_01: [
        resource_parameters_capture_simultaneously,
        resource_parameters_accept_declared_descriptors,
        resource_parameters_do_not_grant_ownership_or_numeric_values,
        generic_pointer_parameters_subrange_and_expansion,
    ],
    resource_parameters_batch_02: [
        generic_pointer_parameters_require_consistent_element_types,
        generic_pointer_struct_parameters_apply_and_expand,
        elements_separation_requires_distinct_indices,
        elements_separation_does_not_widen_byte_cells,
    ],
    resource_parameters_batch_03: [
        wide_subrange_applies_and_expands_without_implicit_solve,
        element_containment_expands_without_implicit_solve,
        rebased_intervals_apply_and_replay_without_search,
        adjacent_ranges_apply_and_replay_without_search,
    ],
}
