#[path = "../build_support/search_boundary.rs"]
#[allow(dead_code)]
mod boundary;

#[test]
fn checking_rejects_planner_dependencies_and_enumeration_escape_hatches() {
    for source in [
        "use crate::surface::planning::proposition_search::PropositionSearch;",
        "fn check(c: C) { c.memory_loadable_candidates(&block); }",
        "fn check(c: C, permission: P) { c.search_memory_loadable_candidates_for_base(permission, &base); }",
        "use crate::kernel::C::search_memory_loadable_candidates_for_base as views;",
        "use crate::{surface as s};",
        "fn check() { crate::surface::hidden!(); }",
        "fn check() { include!(\"hidden.rs\"); }",
        "fn check() { crate::surface::planning::search(); }",
        "fn check(c: C) { c.diagnostic_fact_sample(12, 0); }",
        "fn check(c: C) { let f = C::diagnostic_fact_sample; f(c); }",
        "fn check(c: C) { invoke!(c.r#diagnostic_fact_sample()); }",
        "macro_rules! hidden { () => { crate::surface::planning::search() } }",
    ] {
        assert!(
            boundary::check_source("src/kernel/new_checker.rs", source).is_err(),
            "accepted {source}"
        );
    }
}

#[test]
fn checking_accepts_indexed_and_explicit_input_work_and_test_dependencies() {
    let source = r#"
        // surface::planning and diagnostic_fact_sample are comments, not code.
        fn check(c: C) {
            let surface = 1;
            let message = "diagnostic_fact_sample";
            c.get(&surface);
            c.scan_explicit_input();
        }
        #[cfg(test)] mod tests { use crate::surface::planning::proposition_search::PropositionSearch; }
    "#;
    assert!(boundary::check_source("src/kernel/checker.rs", source).is_ok());
}

#[test]
fn module_walk_checks_production_files_even_when_named_tests() {
    let temp = tempfile::tempdir().unwrap();
    let kernel = temp.path().join("src/kernel");
    std::fs::create_dir_all(&kernel).unwrap();
    std::fs::write(kernel.join("mod.rs"), "mod innocent_tests;").unwrap();
    std::fs::write(kernel.join("innocent_tests.rs"), "use crate::surface as s;").unwrap();
    assert!(boundary::check_tree(temp.path(), "src/kernel/mod.rs").is_err());
    std::fs::write(kernel.join("mod.rs"), "#[cfg(test)] mod innocent_tests;").unwrap();
    assert!(boundary::check_tree(temp.path(), "src/kernel/mod.rs").is_ok());
}

#[test]
fn only_planning_can_construct_search_permission() {
    let temp = tempfile::tempdir().unwrap();
    let permission =
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/surface/planning/permission.rs");
    for (body, succeeds) in [
        (
            "pub(crate) fn check(_: &crate::planning::SearchPermission) {}",
            true,
        ),
        (
            "fn check() { let _ = crate::planning::SearchPermission::new(); }",
            false,
        ),
        (
            "fn check() { let _ = crate::planning::SearchPermission { _private: () }; }",
            false,
        ),
    ] {
        let source = format!(
            r#"
            #![allow(dead_code)]
            mod planning {{
                #[path = {permission:?}] mod permission;
                pub(crate) use permission::SearchPermission;
                pub(crate) fn search() {{ let permission = SearchPermission::new(); consume(&permission); }}
                fn consume(_: &SearchPermission) {{}}
            }}
            mod checking {{ {body} }}
        "#
        );
        let file = temp.path().join("probe.rs");
        std::fs::write(&file, source).unwrap();
        let output = std::process::Command::new("rustc")
            .args(["--edition=2024", "--crate-type=lib", "--emit=metadata"])
            .arg(&file)
            .arg("--out-dir")
            .arg(temp.path())
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            succeeds,
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        if !succeeds {
            assert!(String::from_utf8_lossy(&output.stderr).contains("private"));
        }
    }
}

#[test]
fn selected_reasoning_requires_explicit_premises_or_planner_permission() {
    let temp = tempfile::tempdir().unwrap();
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    let permission = root.join("src/surface/planning/permission.rs");
    let selected = root.join("src/kernel/assumptions/selected_facts.rs");
    for (body, succeeds) in [
        ("let _ = SelectedFacts::from_propositions(&[1, 2]);", true),
        (
            "let _ = SelectedFacts { context: std::borrow::Cow::Owned(PureFactContext::new()) };",
            false,
        ),
        (
            "let _ = SelectedFacts::for_search(&PureFactContext::new(), SearchPermission::new());",
            false,
        ),
        (
            "let _: SelectedFacts = PureFactContext::new().into();",
            false,
        ),
        (
            "let mut facts = SelectedFacts::from_propositions(&[]); *facts = PureFactContext::new();",
            false,
        ),
    ] {
        // Compile the actual constructor module, with a minimal fact store.
        // No cfg(test): production must not gain the test-only adapter.
        let source = format!(
            r#"
            #![allow(dead_code, unused_imports)]
            mod planning {{
                #[path = {permission:?}] mod permission;
                pub(crate) use permission::SearchPermission;
                pub(crate) fn search() {{
                    let _ = crate::kernel::SelectedFacts::for_search(
                        &crate::kernel::PureFactContext::new(), SearchPermission::new());
                }}
            }}
            use planning::SearchPermission;
            mod kernel {{
                pub(crate) type Proposition = u8;
                #[derive(Clone)] pub(crate) struct PureFactContext;
                impl PureFactContext {{
                    pub(crate) fn new() -> Self {{ Self }}
                    fn assume_proposition(self, _: Proposition) -> Self {{ self }}
                }}
                pub(crate) fn clone_proposition_iteratively(p: &Proposition) -> Proposition {{ *p }}
                #[path = {selected:?}] mod selected_facts;
                pub(crate) use selected_facts::SelectedFacts;
            }}
            mod checking {{
                use crate::{{kernel::{{SelectedFacts, PureFactContext}}, SearchPermission}};
                fn check() {{ {body} }}
            }}
        "#
        );
        let file = temp.path().join("probe.rs");
        std::fs::write(&file, source).unwrap();
        let output = std::process::Command::new("rustc")
            .args(["--edition=2024", "--crate-type=lib", "--emit=metadata"])
            .arg(&file)
            .arg("--out-dir")
            .arg(temp.path())
            .output()
            .unwrap();
        assert_eq!(
            output.status.success(),
            succeeds,
            "{body}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    }
}

#[test]
fn fact_withdrawal_is_only_available_in_tests() {
    for path in ["src/kernel/checker.rs", "src/surface/planning/search.rs"] {
        for source in [
            "fn check(c: C, p: P) { c.without_exact_fact(&p); }",
            "fn check() { let f = C::remove_proposition_fact; }",
            "fn check() { hidden!(c.forget_condition_fact(p)); }",
            "impl C { fn without_exact_fact(&self) {} }",
        ] {
            assert!(
                boundary::check_source(path, source).is_err(),
                "accepted {source}"
            );
        }
        assert!(
            boundary::check_source(
                path,
                "impl C { #[cfg(test)] fn without_exact_fact(&self) {} }"
            )
            .is_ok()
        );
    }
}

#[test]
fn step_refusal_cannot_materialize_the_ambient_context() {
    assert!(
        boundary::check_source(
            "src/surface/proof/cursor_execution.rs",
            "fn listed_context_pure_facts(c: C) { c.pure_facts(); }",
        )
        .is_err()
    );
    assert!(
        boundary::check_source(
            "src/surface/proof/cursor_execution.rs",
            "fn listed_context_pure_facts(c: C) { c.diagnostic_fact_sample(32, 0); }",
        )
        .is_ok()
    );
}

#[test]
fn conversion_refusals_cannot_call_search() {
    for source in [
        "use crate::surface::planning::proposition_search::PropositionSearch;",
        "fn explain(c: C, p: P) { c.proves(p); }",
        "fn explain(c: C) { c.pure_facts(); }",
    ] {
        assert!(
            boundary::check_source(
                "src/surface/proof/fixed_state_proofs/conversion_conditions.rs",
                source
            )
            .is_err()
        );
    }
}

#[test]
fn checked_view_queries_cannot_restore_alias_enumeration() {
    for (path, function) in [
        (
            "src/kernel/assumptions.rs",
            "memory_loadable_related_candidates",
        ),
        (
            "src/kernel/assumptions/memory_reasoning.rs",
            "proves_memory_loadable_inner",
        ),
        (
            "src/kernel/assumptions/memory_reasoning.rs",
            "has_memory_read_defined_evidence",
        ),
        (
            "src/kernel/assumptions/memory_reasoning.rs",
            "kept_memory_range_holding_access",
        ),
    ] {
        for method in ["pointer_spellings", "exact_pointer_aliases"] {
            let source = format!("fn {function}(c: C, base: P) {{ c.{method}(&base); }}");
            assert!(boundary::check_source(path, &source).is_err(), "{source}");
        }
        let source = format!(
            "fn {function}(c: C, base: P) {{ c.canonical_pointer(&base); c.storage_address(&base); }}"
        );
        assert!(boundary::check_source(path, &source).is_ok());
    }
}

#[test]
fn checked_conditions_cannot_restore_alias_enumeration() {
    for (path, function) in [
        (
            "src/kernel/assumptions/condition_reasoning/decision.rs",
            "has_condition_fact",
        ),
        (
            "src/kernel/assumptions/condition_reasoning/decision.rs",
            "decide_by_equivalent_order",
        ),
        (
            "src/kernel/assumptions/condition_reasoning/selected_conditions.rs",
            "indexed_matching_condition_fact_for_memory_resolution",
        ),
    ] {
        for method in [
            "bitvector_equality_class",
            "scalar_evidence_class",
            "exact_offset_aliases",
            "condition_match_keys_for_spellings",
        ] {
            let source = format!("fn {function}(c: C, term: T) {{ c.{method}(&term); }}");
            assert!(boundary::check_source(path, &source).is_err(), "{source}");
        }
        let source = format!("fn {function}(c: C, term: T) {{ c.knows_condition(&term, true); }}");
        assert!(boundary::check_source(path, &source).is_ok());
    }
}

#[test]
fn kept_frame_fallback_cannot_restore_block_search() {
    for method in [
        "owned_memory_members_in_block",
        "memory_members_with_base",
        "kept_range_bases_proven_equal",
    ] {
        let source = format!("fn kept_memory_range_holding_access(c: C) {{ c.{method}(); }}");
        assert!(
            boundary::check_source("src/kernel/assumptions/memory_reasoning.rs", &source).is_err()
        );
    }
    let source = "fn evidence(c: C) { c.search_memory_read_defined_candidates(); }";
    assert!(boundary::check_source("src/kernel/assumptions/memory_reasoning.rs", source).is_err());
}

#[test]
fn order_equality_and_access_checks_cannot_restore_candidate_enumeration() {
    for path in [
        "src/kernel/assumptions/condition_reasoning/order_paths.rs",
        "src/kernel/assumptions/condition_reasoning/overflow_intervals.rs",
        "src/kernel/assumptions/condition_reasoning/decision.rs",
        "src/kernel/assumptions/condition_reasoning/selected_conditions.rs",
    ] {
        assert!(
            boundary::check_source(path, "fn check(c: C) { c.condition_facts_with_side(t); }")
                .is_err()
        );
        assert!(
            boundary::check_source(
                path,
                "fn check(c: C) { c.checked_order_bounds.interval(t, false); }"
            )
            .is_ok()
        );
    }
    for name in [
        "MemoryAccessCandidates",
        "access_entries",
        "indexed_access_entries",
    ] {
        let source = format!("fn check(c: C) {{ c.{name}(); }}");
        assert!(
            boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source).is_err()
        );
    }
}

#[test]
fn checked_provenance_cannot_restore_alias_bucket_search() {
    for (function, method) in [
        ("designations_equal", "direct_aliases"),
        ("opaque_extents_equal", "direct_aliases"),
        (
            "known_value_of_framed_pointer_read",
            "exact_pointer_aliases",
        ),
    ] {
        let source = format!("fn {function}(c: C) {{ c.{method}(); }}");
        assert!(boundary::check_source("src/kernel/assumptions.rs", &source).is_err());
    }
}

#[test]
fn signed_interval_cannot_restore_order_chain_walks() {
    for method in [
        "upper_bounds_for_search",
        "lower_bounds_for_search",
        "chained_signed_constant_bound",
        "exact_signed_order_bounds",
        "exact_signed_order_bounds_for_key",
    ] {
        let source = format!("fn signed_interval(c: C) {{ c.{method}(t); }}");
        assert!(
            boundary::check_source(
                "src/kernel/assumptions/condition_reasoning/overflow_intervals.rs",
                &source
            )
            .is_err()
        );
    }
}

#[test]
fn constant_equality_evidence_cannot_restore_bucket_enumeration() {
    for (function, method) in [
        ("signed_constant_evidence", "signed_order_bound_entries"),
        ("indexed_exact_int32_constant", "exact_literal_sources"),
    ] {
        let source = format!("fn {function}(c: C) {{ c.{method}(t); }}");
        assert!(
            boundary::check_source(
                "src/kernel/assumptions/condition_reasoning/decision.rs",
                &source
            )
            .is_err()
        );
    }
}

#[test]
fn direct_literal_and_store_checks_reject_alias_walks() {
    for (path, function, names) in [
        (
            "src/kernel/equality_graph/evidence.rs",
            "direct_scalar_constant",
            &[
                "scalar_evidence_inputs",
                "scalar_evidence_class",
                "scalar_evidence_derivation",
            ][..],
        ),
        (
            "src/kernel/assumptions/memory_reasoning.rs",
            "written_base_spellings",
            &[
                "pointer_alias_class",
                "exact_pointer_aliases",
                "base_spellings_through_aliases",
            ][..],
        ),
        (
            "src/kernel/assumptions/memory_reasoning.rs",
            "owned_store_footprint",
            &["pointer_alias_class"][..],
        ),
        (
            "src/kernel/assumptions/memory_reasoning.rs",
            "access_owned_apart_from_store",
            &["pointer_alias_class"][..],
        ),
    ] {
        for name in names {
            for expression in [
                format!("c.{name}()"),
                format!("C::{name}"),
                format!("invoke!(c.{name}())"),
            ] {
                let source = format!("fn {function}(c: C) {{ let _ = {expression}; }}");
                assert!(
                    boundary::check_source(path, &source).is_err(),
                    "accepted {source}"
                );
            }
        }
        let source =
            format!("fn {function}(c: C) {{ c.scalar_evidence_keys.contains_key(&key); }}");
        assert!(boundary::check_source(path, &source).is_ok());
    }
}

#[test]
fn store_preservation_cannot_retry_general_composition_or_range_search() {
    for name in [
        "owned_composition_store_separated_evidence",
        "owned_composition_store_separated_evidence_impl",
        "pointers_proven_disjoint_by_explicit_range_for_memory_resolution",
        "pointers_directly_disjoint_by_range",
        "pointers_proven_distinct_for_memory_resolution",
    ] {
        for expression in [
            format!("c.{name}()"),
            format!("C::{name}"),
            format!("invoke!(c.{name}())"),
        ] {
            let source =
                format!("fn without_possible_aliasing_cells(c: C) {{ let _ = {expression}; }}");
            assert!(
                boundary::check_source("src/kernel/primitives/memory_state.rs", &source).is_err(),
                "accepted {source}"
            );
        }
    }
    assert!(
        boundary::check_source(
            "src/kernel/primitives/memory_state.rs",
            "fn without_possible_aliasing_cells(c: C) { c.access_owned_apart_from_store(); }"
        )
        .is_ok()
    );
}

#[test]
fn direct_store_distinctness_rejects_search_and_alias_walks() {
    for name in [
        "pointers_proven_distinct_for_memory_resolution",
        "pointers_proven_distinct_for_memory_resolution_unmemoized",
        "pointer_offsets_equal_for_memory_resolution",
        "pointer_offsets_with_common_base_proven_distinct_for_memory_resolution",
        "pointers_proven_disjoint_by_explicit_range_for_memory_resolution",
        "exact_pointer_aliases",
        "proves_recorded_signed_order",
        "decide",
    ] {
        let source = format!("fn pointers_directly_distinct_for_store(c: C) {{ c.{name}(); }}");
        assert!(
            boundary::check_source("src/kernel/reasoning/memory_resolution.rs", &source).is_err(),
            "accepted {source}"
        );
    }
}

#[test]
fn store_ownership_selection_rejects_member_and_composition_walks() {
    for function in [
        "owned_store_footprint",
        "store_members_in",
        "access_owned_apart_from_store",
        "parameter_store_partition",
        "parameter_partition_cell_base",
    ] {
        for name in [
            "owned_memory_members_with_base",
            "memory_members_with_base",
            "owned_member_holding_access",
            "listed_under",
            "listed_under_members",
            "listed_under_anchors",
        ] {
            let source = format!("fn {function}(c: C) {{ c.{name}(); }}");
            assert!(
                boundary::check_source("src/kernel/assumptions/memory_reasoning.rs", &source)
                    .is_err(),
                "accepted {source}"
            );
        }
        let source = format!(
            "fn {function}(c: C) {{ c.unique_owned_memory_member_with_base(); c.directly_listed_under_bases(); }}"
        );
        assert!(
            boundary::check_source("src/kernel/assumptions/memory_reasoning.rs", &source).is_ok()
        );
    }
}

#[test]
fn automatic_store_geometry_rejects_order_and_slot_search() {
    for (function, names) in [
        (
            "one_element_gap_separates_bytes",
            &[
                "proves_recorded_signed_order",
                "decide",
                "signed_order_bound_entries",
            ][..],
        ),
        (
            "run_slots_kept_by_store",
            &[
                "typed_ranges_disjoint_from_pointer_evidence",
                "typed_range_disjoint_from_pointer_evidence",
                "PerSlot",
                "AskWithin",
            ][..],
        ),
        (
            "run_has_direct_store_separation",
            &[
                "typed_ranges_disjoint_from_pointer_evidence",
                "typed_range_disjoint_from_pointer_evidence",
                "PerSlot",
                "AskWithin",
            ][..],
        ),
    ] {
        for name in names {
            let source = format!("fn {function}(c: C) {{ c.{name}(); }}");
            assert!(
                boundary::check_source("src/kernel/reasoning/memory_resolution.rs", &source)
                    .is_err(),
                "accepted {source}"
            );
        }
    }
    assert!(
        boundary::check_source(
            "src/kernel/reasoning/memory_resolution.rs",
            "fn run_slots_kept_by_store(c: C) { c.signed_interval(); SlotSet::Except(0, 8); }"
        )
        .is_ok()
    );
}
