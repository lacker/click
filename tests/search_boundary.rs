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
        std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join("src/kernel/search/permission.rs");
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
    let permission = root.join("src/kernel/search/permission.rs");
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
            "bitvector_equality_class_view",
            "scalar_evidence_class",
            "scalar_evidence_class_view",
            "recorded_equality_class",
            "recorded_equality_class_view",
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
                "scalar_evidence_class_view",
                "recorded_equality_class",
                "recorded_equality_class_view",
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

#[test]
fn direct_nonmemory_support_rejects_candidate_search() {
    for name in [
        "find",
        "find_map",
        "filter",
        "filter_map",
        "flat_map",
        "collect",
        "direct_match_candidates_for",
        "related_pointer_roots",
    ] {
        let source = format!("fn direct_nonmemory_support_entry(c: C) {{ c.{name}(); }}");
        assert!(
            boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source).is_err()
        );
    }
    assert!(
        boundary::check_source(
            "src/kernel/primitives/resource_algebra.rs",
            "fn direct_nonmemory_support_entry(c: C) { c.get().iter().next(); }"
        )
        .is_ok()
    );
}

#[test]
fn single_memory_owner_selection_rejects_fragment_enumeration() {
    for (path, function, names) in [
        (
            "src/kernel/primitives/resource_algebra.rs",
            "directly_supporting_owned_entry_with_separation",
            &["iter", "find", "filter_map", "collect"][..],
        ),
        (
            "src/kernel/primitives/memory_equality_index.rs",
            "single_supplier",
            &[
                "signed_order_bound_entries",
                "get_greater_than",
                "find",
                "filter_map",
                "collect",
            ][..],
        ),
    ] {
        for name in names {
            let source = format!("fn {function}(c: C) {{ c.{name}(); }}");
            assert!(boundary::check_source(path, &source).is_err());
        }
    }
    assert!(
        boundary::check_source(
            "src/kernel/primitives/resource_algebra.rs",
            "fn directly_supporting_owned_entry_with_separation(c: C) { c.single_supplier(); }"
        )
        .is_ok()
    );
}

#[test]
fn loan_origin_reconciliation_rejects_search_and_history() {
    for name in [
        "has_other_directly_supporting_owned_entry",
        "with_coalesced_owned_memory",
        "view_occurrences_for_fact",
        "changed_facts_since",
        "descends_from",
    ] {
        let source = format!("fn plan(c: C) {{ c.{name}(); }}");
        assert!(boundary::check_source("src/kernel/loans.rs", &source).is_err());
    }
    for name in ["iter", "find", "filter_map", "collect"] {
        let source = format!("fn origin_of(c: C) {{ c.{name}(); }}");
        assert!(
            boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source).is_err()
        );
    }
    assert!(
        boundary::check_source(
            "src/kernel/primitives/resource_algebra.rs",
            "fn origin_of(c: C) { c.get(); }",
        )
        .is_ok()
    );
}

#[test]
fn loan_binding_selection_rejects_candidate_search() {
    for function in ["bound_view_candidate", "select_bound_view"] {
        for name in ["find", "find_map", "filter", "filter_map", "collect"] {
            let source = format!("fn {function}(c: C) {{ c.{name}(); }}");
            assert!(boundary::check_source("src/kernel/loans.rs", &source).is_err());
        }
    }
}

#[test]
fn selected_loan_consumption_rejects_supplier_discovery() {
    for name in [
        "iter",
        "find",
        "find_map",
        "collect",
        "normalized_memory_suppliers",
        "without_fact_incrementally",
    ] {
        let source = format!("fn without_selected_fact_with_origins(c: C) {{ c.{name}(); }}");
        assert!(
            boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source).is_err()
        );
    }
}

#[test]
fn loop_binding_handoff_rejects_view_rediscovery() {
    for (path, function) in [
        ("src/kernel/loops.rs", "loop_body_resource_context"),
        ("src/kernel/loans.rs", "attach_to_inserted_views"),
    ] {
        for name in ["view_occurrences_for_fact", "find", "find_map"] {
            let source = format!("fn {function}(c: C) {{ c.{name}(); }}");
            assert!(boundary::check_source(path, &source).is_err());
        }
    }
}

#[test]
fn indexed_memory_support_rejects_candidate_search() {
    for name in [
        "iter",
        "collect",
        "find",
        "find_map",
        "normalized_memory_suppliers",
        "with_coalesced_owned_memory",
    ] {
        for function in [
            "directly_supporting_memory_fact",
            "constant_relative_byte_endpoints",
            "constant_memory_coordinates",
            "consume_unit_owned_memory",
            "consume_symbolic_partition",
            "memory_range_definitely_shorter",
            "reserve_owned_memory_fragments_impl",
        ] {
            let source = format!("fn {function}(c: C) {{ c.{name}(); }}");
            assert!(
                boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source)
                    .is_err()
            );
        }
    }
}

#[test]
fn local_storage_classification_rejects_candidate_search() {
    for name in [
        "iter",
        "collect",
        "find",
        "find_map",
        "memory_fact_candidates",
        "view_occurrences_for_fact",
    ] {
        let source = format!("fn has_no_explicit_memory_for_local_storage(c: C) {{ c.{name}(); }}");
        assert!(
            boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source).is_err()
        );
    }
    assert!(
        boundary::check_source(
            "src/kernel/functions.rs",
            "fn prepare(c: C) { c.with_coalesced_owned_memory(); }"
        )
        .is_err()
    );
}

#[test]
fn call_completion_rejects_frame_revalidation_and_normalization() {
    for (path, function) in [
        ("src/kernel/loans.rs", "recover_stable_views_impl"),
        (
            "src/kernel/functions.rs",
            "recover_candidate_stable_view_resources",
        ),
        (
            "src/kernel/functions.rs",
            "evaluate_contract_return_resources",
        ),
    ] {
        for name in [
            "normalized_around_facts",
            "try_compose_with_fact_with_occurrence",
            "try_compose_with_facts_delaying_normalization",
            "try_compose_with_facts_delaying_normalization_with_occurrences",
        ] {
            let source = format!("fn {function}(c: C) {{ c.{name}(); }}");
            assert!(boundary::check_source(path, &source).is_err());
        }
    }
    assert!(
        boundary::check_source(
            "src/kernel/functions.rs",
            "fn recover_candidate_stable_view_resources(c: C) { c.facts(); }"
        )
        .is_err()
    );
}

#[test]
fn explicit_loop_frames_reject_ambient_ownership_and_observation_scans() {
    for name in ["owned_memory_facts", "memory_facts_in_block"] {
        let source = format!("fn with_loop_frame_resources(c: C) {{ c.{name}(); }}");
        assert!(boundary::check_source("src/kernel/loops.rs", &source).is_err());
    }
}

#[test]
fn owned_neighbor_selection_rejects_candidate_enumeration() {
    for name in [
        "collect",
        "find",
        "find_map",
        "filter",
        "flat_map",
        "for_each",
        "owned_validity_candidates",
        "memory_fact_candidates",
        "normalized_memory_suppliers",
        "facts",
    ] {
        let source = format!("fn constant_owned_neighbors(c: C) {{ c.{name}(); }}");
        assert!(
            boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source).is_err()
        );
    }
}

#[test]
fn exact_alias_owner_neighbors_reject_supplier_scans() {
    for name in [
        "iter",
        "collect",
        "find",
        "find_map",
        "normalized_memory_suppliers",
        "with_coalesced_owned_memory",
    ] {
        let source = format!("fn constant_owned_neighbors_at_exact_alias(c: C) {{ c.{name}(); }}");
        assert!(
            boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source).is_err()
        );
    }
}

#[test]
fn ownership_validity_rejects_mixed_access_buckets() {
    for name in ["memory_by_base", "memory_by_block"] {
        let source = format!("fn owned_validity_candidates(c: C) {{ c.{name}.get(k); }}");
        assert!(
            boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source).is_err()
        );
    }
    assert!(
        boundary::check_source(
            "src/kernel/primitives/resource_algebra.rs",
            "fn owned_validity_candidates(c: C) { c.owned_memory_by_base.get(k); }"
        )
        .is_ok()
    );
}

#[test]
fn owner_absence_rejects_alias_and_resource_enumeration() {
    for name in [
        "iter",
        "collect",
        "find",
        "find_map",
        "filter",
        "flat_map",
        "for_each",
        "exact_pointer_aliases",
        "exact_pointer_offset_aliases",
        "owned_validity_candidates",
        "facts",
    ] {
        let source = format!("fn has_owned_memory_outside_block(c: C) {{ c.{name}(); }}");
        assert!(
            boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source).is_err()
        );
    }
}

#[test]
fn constant_overlap_rejects_alias_and_premise_enumeration() {
    for name in [
        "iter",
        "collect",
        "find",
        "find_map",
        "filter",
        "flat_map",
        "for_each",
        "exact_pointer_aliases",
        "exact_pointer_offset_aliases",
        "memory_ranges_proven_overlapping",
        "memory_ranges_proven_overlapping_without_aliases",
        "facts",
    ] {
        let source = format!("fn constant_memory_overlap(c: C) {{ c.{name}(); }}");
        assert!(
            boundary::check_source("src/kernel/primitives/resource_algebra.rs", &source).is_err()
        );
    }
}

#[test]
fn cache_protection_rejects_loan_enumeration() {
    for name in [
        "iter",
        "collect",
        "unindexed_memory",
        "permits_memory_access",
        "permits_memory_access_with_assumptions",
        "active_memory_overlaps",
        "protected_range_proven_overlapping",
    ] {
        let source = format!("fn has_indexed_memory_overlap(c: C) {{ c.{name}(); }}");
        assert!(boundary::check_source("src/kernel/loans.rs", &source).is_err());
    }
}

#[test]
fn havoc_cache_retention_cannot_restore_the_write_barrier_scan() {
    for function in [
        "loan_preserving_havoc_keeps_cell",
        "loan_preserving_havoc_keeps_run",
    ] {
        for name in [
            "permits_memory_access",
            "permits_memory_access_with_assumptions",
            "active_memory_overlaps",
        ] {
            let source = format!("fn {function}(c: C) {{ c.{name}(); }}");
            assert!(
                boundary::check_source("src/kernel/primitives/memory_state.rs", &source).is_err()
            );
        }
    }
}

#[test]
fn write_barriers_and_diagnostics_cannot_collect_conflicting_loans() {
    for function in [
        "permits_memory_access_with_assumptions",
        "conflicting_memory_loan",
        "first_active_memory_overlap",
        "first_active_memory_overlap_with_assumptions",
    ] {
        for method in [
            "active_memory_overlaps",
            "active_memory_overlaps_with_assumptions",
        ] {
            let source = format!("fn {function}(c: C) {{ c.{method}(); }}");
            assert!(boundary::check_source("src/kernel/loans.rs", &source).is_err());
        }
    }
    for function in [
        "first_active_memory_overlap",
        "first_active_memory_overlap_with_assumptions",
    ] {
        for method in [
            "collect",
            "with_value",
            "flat_map",
            "filter",
            "find",
            "find_map",
            "for_each",
            "fold",
        ] {
            let source = format!("fn {function}(c: C) {{ c.{method}(); }}");
            assert!(boundary::check_source("src/kernel/loans.rs", &source).is_err());
        }
    }
}

#[test]
fn call_postconditions_cannot_restore_implicit_constant_recovery() {
    for name in [
        "add_normalized_verified_ensure_facts",
        "resolve_load_along_memory_derivations",
    ] {
        let source = format!("fn add_ensures(c: C) {{ c.{name}(); }}");
        assert!(boundary::check_source("src/kernel/functions.rs", &source).is_err());
    }
}

#[test]
fn active_memory_loan_presence_cannot_scan_ledger_history_or_indices() {
    for method in [
        "iter",
        "values",
        "keys",
        "collect",
        "any",
        "all",
        "fold",
        "count",
        "loans",
        "scopes",
        "unindexed_memory",
        "active_memory_index",
        "cache_memory_index",
        "loan_protects_memory",
    ] {
        let source = format!("fn has_active_memory_loans(c: C) {{ c.{method}(); }}");
        assert!(boundary::check_source("src/kernel/loans.rs", &source).is_err());
    }
}

#[path = "../build_support/proof_search_boundary.rs"]
mod proof_search_boundary;

#[test]
fn new_operation_search_edges_are_rejected_even_through_aliases_and_macros() {
    for source in [
        "fn step(p: P) { ProofSearch::try_solve_closure(p); }",
        "fn step(p: P) { let f = ProofSearch::try_solve_closure; f(p); }",
        "fn step(p: P) { hidden!(ProofSearch::try_solve_closure(p)); }",
        "use crate::kernel::search::ProofSearch as S; fn step(p: P) { S::try_solve_closure(p); }",
        "fn step(c: C) { c.compositions_only(); }",
        "impl ProofSearch<P> { fn new_unclassified_strategy() {} }",
        "impl Proof { fn try_solve_closure(&self) {} }",
        "impl ProofObject { fn derive_proposition(&self) {} }",
    ] {
        let file = syn::parse_file(source).unwrap();
        assert!(
            proof_search_boundary::check("src/new_operation.rs", &file).is_err(),
            "{source}"
        );
    }
}

#[test]
fn frozen_proof_search_inventory_rejects_deleted_or_duplicated_references() {
    let path = "src/kernel/publication.rs";
    for (source, accepted) in [
        ("fn release_store() { call_kept_ownership(); }", true),
        ("fn release_store() {}", false),
        (
            "fn release_store() { call_kept_ownership(); call_kept_ownership(); }",
            false,
        ),
    ] {
        let file = syn::parse_file(source).unwrap();
        assert_eq!(
            proof_search_boundary::check(path, &file).is_ok(),
            accepted,
            "{source}"
        );
    }
}

#[test]
fn frozen_proof_search_inventory_names_existing_files() {
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for key in proof_search_boundary::expected().keys() {
        let path = key.split('\t').next().unwrap();
        assert!(root.join(path).is_file(), "stale inventory path: {path}");
    }
}

#[test]
fn extracted_legacy_search_retains_the_existing_operation_guards() {
    for (path, source) in [
        (
            "src/kernel/loans/legacy_search.rs",
            "impl ProofSearch<P> { fn loan_access(c: C) { c.active_memory_overlaps(); } }",
        ),
        (
            "src/kernel/loans/legacy_search.rs",
            "fn loan_aliases(c: C) { c.changed_facts_since(); }",
        ),
        (
            "src/kernel/primitives/resource_algebra/legacy_search.rs",
            "impl ProofSearch<P> { fn ownership_validity_candidates(c: C) { c.memory_by_base(); } }",
        ),
        (
            "src/kernel/primitives/resource_algebra/legacy_search.rs",
            "impl ProofSearch<P> { fn ownership_validity_candidates(c: C) { c.memory_by_block(); } }",
        ),
    ] {
        assert!(
            boundary::check_source(path, source).is_err(),
            "{path}: {source}"
        );
    }
    let root = std::path::Path::new(env!("CARGO_MANIFEST_DIR"));
    for path in [
        "src/kernel/loans/legacy_search.rs",
        "src/kernel/primitives/resource_algebra/legacy_search.rs",
        "src/kernel/functions/legacy_search.rs",
    ] {
        let source = std::fs::read_to_string(root.join(path)).unwrap();
        boundary::check_source(path, &source).unwrap();
    }
}

#[test]
fn driver_boundary_rejects_new_backedges_and_misplaced_orchestration() {
    for source in [
        "impl Proof { fn new_operation(&self) { self.driver().apply_step(); } }",
        "impl Proof { fn apply_step(&self) {} }",
        "impl ProofScope { fn apply_theorem_application(&self) {} }",
        "impl ProofDriver<P> { fn unclassified_dispatch(&self) {} }",
    ] {
        let file = syn::parse_file(source).unwrap();
        assert!(
            proof_search_boundary::check("src/new_operation.rs", &file).is_err(),
            "{source}"
        );
    }
}

#[test]
fn file_module_path_attributes_are_relative_to_the_source_directory() {
    let temp = tempfile::tempdir().unwrap();
    let kernel = temp.path().join("src/kernel");
    std::fs::create_dir_all(kernel.join("helpers")).unwrap();
    std::fs::write(kernel.join("mod.rs"), "mod operations;").unwrap();
    std::fs::write(
        kernel.join("operations.rs"),
        r#"#[path = "helpers/../moved.rs"] mod moved;"#,
    )
    .unwrap();
    std::fs::write(kernel.join("moved.rs"), "fn harmless() {}").unwrap();
    assert!(boundary::check_tree(temp.path(), "src/kernel/mod.rs").is_ok());
    std::fs::write(kernel.join("moved.rs"), "use crate::surface as s;").unwrap();
    assert!(boundary::check_tree(temp.path(), "src/kernel/mod.rs").is_err());
}

#[test]
fn moving_explicit_dispatch_to_the_driver_does_not_hide_operation_search() {
    let file = syn::parse_file("impl ProofDriver<P> { fn apply_theorem_application(&self) { ProofSearch::select_theorem_application_step(self.proof); } }").unwrap();
    let edges = proof_search_boundary::inventory("src/surface/proof/driver/theorems.rs", &file);
    assert!(edges.keys().all(|key| key.contains("\toperation\t")));
    assert_eq!(edges.len(), 1);
}

#[test]
fn implicit_obligations_cannot_restore_private_solver_strategies() {
    let path = "src/surface/proof/driver/obligations.rs";
    for method in [
        "try_solve_closure_with_surfaces",
        "try_direct_caller_requirement_closure",
        "Witness",
        "try_restricted_solve_closure",
    ] {
        let source = format!(
            "fn prove_obligations_by_solve_or_name_the_first_missed() {{ hidden!({method}); }}"
        );
        assert!(boundary::check_source(path, &source).is_err(), "{method}");
    }
    assert!(boundary::check_source(path, "fn prove_obligations_by_solve_or_name_the_first_missed(p: P) { p.driver().try_solve_closure(); }").is_ok());
}

#[test]
fn proof_driver_inventory_ignores_unrelated_local_driver_variables() {
    let file = syn::parse_file("fn frontend() { let driver = compiler(); validate(driver); } fn proof(p: P) { p.driver(); DriveProof::driver(p); }").unwrap();
    let edges = proof_search_boundary::inventory("src/example.rs", &file);
    assert_eq!(edges.len(), 1);
    let (key, count) = edges.iter().next().unwrap();
    assert!(key.contains("::proof\tdriver"));
    assert_eq!(*count, 2);
}

#[test]
fn have_primitive_cannot_schedule_proofs_or_search() {
    let path = "src/surface/proof/proof_object/splits_and_scopes.rs";
    for source in [
        "impl Proof { fn begin_have(&self) { self.driver().open_have(goal); } }",
        "impl Proof { fn begin_have(&self) { ProofSearch::proves(facts, goal); } }",
        "impl Proof { fn begin_have(&self) { invoke!(self.driver()); } }",
        "impl Proof { fn begin_have(&self) { let run = ProofDriver::open_have; } }",
    ] {
        assert!(
            boundary::check_source(path, source).is_err(),
            "accepted {source}"
        );
    }
    assert!(boundary::check_source(path,
        "impl Proof { fn begin_have(&self) { self.lower_surface_goal_recording_introductions(goal); } }"
    ).is_ok());
}

#[test]
fn contract_claim_primitive_cannot_schedule_proofs_or_search() {
    let path = "src/surface/proof/proof_object/outcomes_and_focus.rs";
    for source in [
        "impl Proof { fn begin_contract_claim(&self) { self.driver().open_contract_claim(goal); } }",
        "impl Proof { fn begin_contract_claim(&self) { ProofSearch::proves(facts, goal); } }",
        "impl Proof { fn begin_contract_claim(&self) { invoke!(self.driver()); } }",
    ] {
        assert!(
            boundary::check_source(path, source).is_err(),
            "accepted {source}"
        );
    }
    assert!(boundary::check_source(path,
        "impl Proof { fn begin_contract_claim(&self) { refuse_or_record_open_obligation(error)?; } }"
    ).is_ok());
}

#[test]
fn resource_scope_completion_cannot_schedule_proofs_or_search() {
    let path = "src/surface/proof/proof_object/scope.rs";
    for source in [
        "impl ProofScope { fn join_inner(&self) { self.body.driver().close_scope_with_body_fact_proof(); } }",
        "impl ProofScope { fn close_open_scope_from(&self) { ProofSearch::proves(facts, goal); } }",
        "impl ProofScope { fn join_inner(&self) { invoke!(self.body.driver()); } }",
        "impl ProofScope { fn join_inner(&self) { let run = ProofDriver::complete_scope; } }",
    ] {
        assert!(
            boundary::check_source(path, source).is_err(),
            "accepted {source}"
        );
    }
    assert!(
        boundary::check_source(
            path,
            "impl ProofScope { fn join_inner(&self) { refuse_or_record_open_obligation(error)?; } }"
        )
        .is_ok()
    );
}

#[test]
fn branch_primitives_cannot_interpret_scripts_or_schedule_search() {
    for method in [
        "apply_execution_if_within",
        "apply_execution_branch_within",
        "apply_focused_expanded_execution_arm",
        "apply_expanded_execution_if",
    ] {
        let file = syn::parse_file(&format!("impl Proof {{ fn {method}(&self) {{}} }}")).unwrap();
        assert!(proof_search_boundary::check("src/new_operation.rs", &file).is_err());
    }
    for (path, source) in [
        (
            "src/surface/proof/proof_object/execution_joins.rs",
            "impl Proof { fn split_focused_execution_branch_with(&self) { self.driver().apply_step(step); } }",
        ),
        (
            "src/surface/proof/proof_object/execution_joins.rs",
            "impl Proof { fn focus_expanded_execution_arm_entry(&self) { invoke!(ProofSearch::proves(facts, goal)); } }",
        ),
        (
            "src/surface/proof/proof_object/splits_and_scopes.rs",
            "impl Proof { fn apply_execution_if_with<Then: FnOnce(Self)>(self, apply_then: Then) { apply_then(self); } }",
        ),
    ] {
        assert!(
            boundary::check_source(path, source).is_err(),
            "accepted {source}"
        );
    }
}

#[test]
fn callback_error_reporting_cannot_reenter_the_driver() {
    let path = "src/surface/proof/proof_object/execution_statements.rs";
    let source = r#"impl Proof {
        fn unfinished_callback_script_error(&self) {
            let mut pending = self.clone();
            for _ in 0..6 {
                pending = pending.driver().apply_step(ProofStep::Step);
            }
        }
    }"#;
    let file = syn::parse_file(source).unwrap();
    let records = proof_search_boundary::inventory(path, &file);
    assert!(
        records
            .keys()
            .any(|key| key.contains("unfinished_callback_script_error"))
    );
    assert!(proof_search_boundary::check(path, &file).is_err());
}

#[test]
fn match_arm_exclusion_primitives_cannot_dispatch_steps() {
    let path = "src/surface/proof/proof_object/match_cases.rs";
    for name in [
        "prepare_execution_match_arm_exclusion",
        "finish_execution_match_arm_exclusion",
    ] {
        let source = format!(
            "impl Proof {{ fn {name}(&self) {{ self.driver().apply_step_at(step, source_index); }} }}"
        );
        let file = syn::parse_file(&source).unwrap();
        let errors = proof_search_boundary::check(path, &file).unwrap_err();
        assert!(
            errors.iter().any(
                |error| error.starts_with("unreviewed proof-search dependency:")
                    && error.contains(name)
            ),
            "{errors:?}"
        );
    }
}

#[test]
fn signed_definedness_certificate_attempts_stay_in_search() {
    let path = "src/surface/proof/signed_definedness.rs";
    for source in [
        "impl Proof { fn try_signed_definedness_certificate(&self) {} }",
        "impl Proof { fn apply_signed_definedness_certificate(&self) { self.driver().apply_step(certificate); } }",
        "impl Proof { fn apply_certificate(&self) { ProofSearch::try_signed_definedness_certificate(self, width, premises); } }",
    ] {
        let file = syn::parse_file(source).unwrap();
        assert!(
            proof_search_boundary::check(path, &file).is_err(),
            "{source}"
        );
    }
}

#[test]
fn unsigned_order_fact_restatement_stays_in_search() {
    let path = "src/surface/proof/smart_closures.rs";
    for source in [
        "impl Proof { fn try_unsigned_strict_fact(&self) {} }",
        "impl Proof { fn unsigned_strict_fact(&self) { self.driver().have_by_integer_arithmetic(goal, premises); } }",
        "impl Proof { fn use_order(&self) { ProofSearch::try_unsigned_strict_fact(self, lower, upper, facts); } }",
    ] {
        let file = syn::parse_file(source).unwrap();
        let errors = proof_search_boundary::check(path, &file).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.contains("search method must not return")
                    || error.starts_with("unreviewed proof-search dependency:")),
            "{errors:?}"
        );
    }
}

#[test]
fn invariant_bundle_solving_belongs_to_the_driver() {
    for owner in ["Proof", "ProofScope"] {
        let file = syn::parse_file(&format!(
            "impl {owner} {{ fn plan_invariant_bundle_closure(&self) {{}} }}"
        ))
        .unwrap();
        let errors = proof_search_boundary::check("src/new_operation.rs", &file).unwrap_err();
        assert!(
            errors
                .iter()
                .any(|error| error.contains("driver method must not return")),
            "{errors:?}"
        );
    }
}

#[test]
fn resource_opening_selection_stays_in_search() {
    let path = "src/surface/proof/proof_object/resource_steps.rs";
    for source in [
        "impl Proof { fn try_open_for_missing_resource(&self) {} }",
        "impl Proof { fn solve_open_for_missing_resource(&self) { self.driver().apply_step(open); } }",
        "impl Proof { fn open(&self) { ProofSearch::try_open_for_missing_resource(self, missing); } }",
    ] {
        let file = syn::parse_file(source).unwrap();
        assert!(
            proof_search_boundary::check(path, &file).is_err(),
            "{source}"
        );
    }
}

#[test]
fn live_transport_planning_stays_in_search() {
    let path = "src/surface/proof/proof_object/execution_statements.rs";
    for source in [
        "impl Proof { fn apply_planned_fact_transport(&self) {} }",
        "impl Proof { fn apply_planned_fact_transport_inner(&self) {} }",
        "impl Proof { fn transport(&self) { ProofSearch::apply_planned_fact_transport(self, source, target); } }",
    ] {
        let file = syn::parse_file(source).unwrap();
        assert!(
            proof_search_boundary::check(path, &file).is_err(),
            "{source}"
        );
    }
}

#[test]
fn outcome_transport_planning_stays_in_search() {
    let path = "src/surface/proof/proof_object/execution_statements.rs";
    for source in [
        "impl Proof { fn apply_planned_outcome_fact_transport(&self) {} }",
        "impl Proof { fn transport(&self) { ProofSearch::apply_planned_outcome_fact_transport(self, source, target); } }",
    ] {
        let file = syn::parse_file(source).unwrap();
        assert!(
            proof_search_boundary::check(path, &file).is_err(),
            "{source}"
        );
    }
}

#[test]
fn smart_arithmetic_dispatch_is_separate_from_operation_search() {
    let path = "src/surface/proof/driver/steps.rs";
    let source = "impl ProofDriver { fn apply_step_without_outcome_wrapping(&self) { ProofSearch::apply_arithmetic_using(self.proof, premises); ProofSearch::try_wide_arithmetic_using(self.proof, premises); } }";
    let file = syn::parse_file(source).unwrap();
    let records = proof_search_boundary::inventory(path, &file);
    assert!(
        records
            .keys()
            .any(|key| key.contains("\tdriver\t") && key.ends_with("\tapply_arithmetic_using"))
    );
    assert!(
        records.keys().any(
            |key| key.contains("\toperation\t") && key.ends_with("\ttry_wide_arithmetic_using")
        )
    );
    let file = syn::parse_file("impl Proof { fn apply_arithmetic_using(&self) {} }").unwrap();
    assert!(
        proof_search_boundary::check("src/surface/proof/proof_object/step_application.rs", &file)
            .is_err()
    );
}

#[test]
fn statement_preparation_cannot_search_for_atomic_prerequisites() {
    let file = syn::parse_file("fn certified_transitions_from_execution() { ProofSearch::derive_atomic_proposition(context, goal); }").unwrap();
    assert!(
        proof_search_boundary::check(
            "src/surface/proof/execution_planning/transition_certification.rs",
            &file,
        )
        .is_err()
    );
}

#[test]
fn search_entries_cannot_omit_or_delay_runtime_discovery_recording() {
    for body in [
        "{}",
        r#"{ work(); #[cfg(test)] crate::kernel::search::record_discovery("proves"); }"#,
        r#"{ #[cfg(test)] crate::kernel::search::record_discovery("other"); }"#,
    ] {
        let source = format!("impl ProofSearch<P> {{ fn proves() {body} }}");
        let errors =
            proof_search_boundary::check("src/new_search.rs", &syn::parse_file(&source).unwrap())
                .unwrap_err();
        assert!(
            errors.iter().any(|e| e.contains("must record discovery")),
            "{errors:?}"
        );
    }
    let source = r#"impl ProofSearch<P> { fn proves() {
        #[cfg(test)] crate::kernel::search::record_discovery("proves");
    } }"#;
    proof_search_boundary::check("src/new_search.rs", &syn::parse_file(source).unwrap()).unwrap();
}

#[test]
fn migrated_operations_cannot_drop_their_discovery_guard() {
    for name in [
        "apply_theorem_using",
        "prepare_theorem_application",
        "finish_prepared_theorem_application",
        "finish_prepared_step",
        "begin_contract_claim",
        "begin_have",
    ] {
        let source = format!("impl Proof {{ fn {name}() {{}} }}");
        let errors = proof_search_boundary::check(
            "src/new_operation.rs",
            &syn::parse_file(&source).unwrap(),
        )
        .unwrap_err();
        assert!(
            errors
                .iter()
                .any(|e| e.contains("must enter its no-discovery scope")),
            "{errors:?}"
        );
    }
}

#[test]
fn kernel_claim_focus_must_keep_its_discovery_guard() {
    let source = "impl ProofObject<L, P, E> { fn focus_contract_claim() {} }";
    let errors =
        proof_search_boundary::check("src/new_operation.rs", &syn::parse_file(source).unwrap())
            .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("must enter its no-discovery scope")),
        "{errors:?}"
    );
}

#[test]
fn removed_declaration_validation_escape_cannot_be_reintroduced() {
    let file = syn::parse_file(
        "fn ordinary_operation() { FastOperationScope::enter_declaration_validation(); }",
    )
    .unwrap();
    assert!(proof_search_boundary::check("src/new_operation.rs", &file).is_err());
}

#[test]
fn join_must_keep_its_discovery_guard() {
    let source = "impl ProofScope { fn join() {} }";
    let errors =
        proof_search_boundary::check("src/new_operation.rs", &syn::parse_file(source).unwrap())
            .unwrap_err();
    assert!(
        errors
            .iter()
            .any(|e| e.contains("must enter its no-discovery scope")),
        "{errors:?}"
    );
}

#[test]
fn smart_proof_producers_cannot_construct_plain_normalize() {
    use syn::visit::Visit;
    #[derive(Default)]
    struct PlainNormalize(bool);
    fn test_only(attrs: &[syn::Attribute]) -> bool {
        attrs.iter().any(|attr| attr.path().is_ident("test") ||
            attr.path().is_ident("cfg") && matches!(&attr.meta, syn::Meta::List(meta) if meta.tokens.to_string() == "test"))
    }
    impl PlainNormalize {
        fn tokens(&mut self, stream: proc_macro2::TokenStream) {
            let tokens = stream.into_iter().collect::<Vec<_>>();
            for token in &tokens {
                if let proc_macro2::TokenTree::Group(group) = token {
                    self.tokens(group.stream());
                }
            }
            for window in tokens.windows(4) {
                if matches!(&window[0], proc_macro2::TokenTree::Ident(id) if id == "ProofStep" || id == "ProofTactic")
                    && matches!(&window[1], proc_macro2::TokenTree::Punct(p) if p.as_char() == ':')
                    && matches!(&window[2], proc_macro2::TokenTree::Punct(p) if p.as_char() == ':')
                    && matches!(&window[3], proc_macro2::TokenTree::Ident(id) if id == "Normalize")
                {
                    self.0 = true;
                }
            }
        }
    }
    impl<'ast> Visit<'ast> for PlainNormalize {
        fn visit_item(&mut self, item: &'ast syn::Item) {
            let attrs = match item {
                syn::Item::Fn(item) => &item.attrs,
                syn::Item::Mod(item) => &item.attrs,
                syn::Item::Impl(item) => &item.attrs,
                _ => return syn::visit::visit_item(self, item),
            };
            if !test_only(attrs) {
                syn::visit::visit_item(self, item);
            }
        }
        fn visit_impl_item_fn(&mut self, item: &'ast syn::ImplItemFn) {
            if !test_only(&item.attrs) {
                syn::visit::visit_impl_item_fn(self, item);
            }
        }
        fn visit_expr_path(&mut self, expr: &'ast syn::ExprPath) {
            let names = expr
                .path
                .segments
                .iter()
                .map(|s| s.ident.to_string())
                .collect::<Vec<_>>();
            if names.windows(2).any(|pair| {
                matches!(pair[0].as_str(), "ProofStep" | "ProofTactic") && pair[1] == "Normalize"
            }) {
                self.0 = true;
            }
            syn::visit::visit_expr_path(self, expr);
        }
        fn visit_macro(&mut self, mac: &'ast syn::Macro) {
            self.tokens(mac.tokens.clone());
        }
    }
    let rejects = |source: &str| {
        let mut check = PlainNormalize::default();
        check.visit_file(&syn::parse_file(source).unwrap());
        check.0
    };
    assert!(rejects("fn search() { vec![ProofStep::Normalize]; }"));
    assert!(rejects("fn search() { use_it(ProofTactic::Normalize); }"));
    assert!(!rejects(
        "fn search() { vec![ProofStep::Known, ProofStep::NormalizeUsing(premises)]; } #[cfg(test)] mod tests { fn explicit() { vec![ProofStep::Normalize]; } }"
    ));
    for relative in [
        "src/surface/planning/solve.rs",
        "src/surface/proof/smart_closures.rs",
        "src/surface/proof/smart_closures/search.rs",
        "src/surface/proof/selected_arithmetic/search.rs",
        "src/surface/proof/surface_certificates.rs",
    ] {
        let source = std::fs::read_to_string(
            std::path::Path::new(env!("CARGO_MANIFEST_DIR")).join(relative),
        )
        .unwrap();
        assert!(
            !rejects(&source),
            "{relative} constructs a plain normalize certificate"
        );
    }
}
