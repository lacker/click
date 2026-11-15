use super::expansion_tests::mdtest_sources;
use super::*;

#[test]
fn removed_transport_certificate_is_not_a_tactic() {
    let source = "theorem retired() { ensures true by { transport_certificate { premise 0: true => true; conclusion 0; } } }";
    let error = verify_click_theorems(source).unwrap_err();
    assert!(
        error.report().contains("transport_certificate"),
        "{}",
        error.report()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_00")]
fn preserve_checks_byte_reads_without_search() {
    let (source, sources) = mdtest_sources("mdtests/preserve_byte_read.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    without_implicit_solve(|| verify_c_sources(&source, &sources)).unwrap();
    let expanded =
        expand_c_claim_source(&source, &sources, "keep", ContractProofClaim::Grouped).unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    // Separation of q cannot carry a read of the cell actually written.
    let overlapping = source.replace(
        "*q == at(statement(0).entry, *q)",
        "*p == at(statement(0).entry, *p)",
    );
    assert!(without_implicit_solve(|| verify_c_sources(&overlapping, &sources)).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_00")]
fn preserve_checks_pointer_read() {
    let (source, sources) = mdtest_sources("mdtests/preserve_pointer_read.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    with_proof_trace("copy_pos", || {
        if let Err(error) = without_implicit_solve(|| verify_c_sources(&source, &sources)) {
            panic!(
                "{}\n{}",
                error.report(),
                error.trace_context_report().unwrap_or_default()
            );
        }
    });
    let expanded =
        expand_c_claim_source(&source, &sources, "copy_pos", ContractProofClaim::Grouped).unwrap();
    assert!(!expanded.contains("transport_certificate"));
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    let scalar_source = source.replace("source->data", "source->len");
    without_implicit_solve(|| verify_c_sources(&scalar_source, &sources)).unwrap();
    for (from, to) in [
        ("memory(target->pos))", "memory(target->len))"),
        ("statement(0).footprint", "statement(1).footprint"),
        ("at(before, source->data)", "at(after, source->data)"),
    ] {
        let invalid = source.replace(from, to);
        assert_ne!(invalid, source);
        assert!(verify_c_sources(&invalid, &sources).is_err(), "{invalid}");
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_00")]
fn ordinary_equalities_compose_without_search() {
    let source = r#"
        theorem transitive_values(x: int32*, y: int32*, z: int32*) {
            requires x == y;
            requires y == z;
            ensures x == z by {
                rewrite(x, y);
                known();
            }
        }
    "#;
    without_implicit_solve(|| verify_click_theorems(source)).unwrap();
    let missing = source.replace("requires y == z;", "");
    assert!(without_implicit_solve(|| verify_click_theorems(&missing)).is_err());
    let wrong = source.replace("ensures x == z", "ensures x != z");
    assert!(without_implicit_solve(|| verify_click_theorems(&wrong)).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_00")]
fn preserve_checks_signed_and_unsigned_64_bit_reads() {
    for (interface_type, click_type) in [("long", "int64"), ("unsigned long", "uint64")] {
        let c =
            format!("void write(int *dest, {interface_type} *kept) {{ *dest = 1; *dest = 2; }}");
        let source = format!(
            r#"
            verifying "wide.c";
            void write(int32 *dest, {click_type} *kept) {{
                owns dest[0..1];
                views kept[0..1];
                requires separate(memory(dest[0..1]), memory(kept[0..1]));
            }} by {{
                mark before;
                step() by {{ known(); }}
                mark after;
                have *kept == at(before, *kept) by {{
                    have separate(statement(0).footprint, memory(*kept)) by {{ normalize() using {{ at(before, separate(memory(dest[0..1]), memory(kept[0..1]))); }}; }}
                    preserve(separate(statement(0).footprint, memory(*kept)));
                }}
                step() by {{ known(); }}
                mark final;
                have *kept == at(before, *kept) by {{
                    have *kept == at(after, *kept) by {{
                        have separate(statement(1).footprint, memory(*kept)) by {{ normalize() using {{ at(before, separate(memory(dest[0..1]), memory(kept[0..1]))); }}; }}
                        preserve(separate(statement(1).footprint, memory(*kept)));
                    }}
                    rewrite(*kept, at(after, *kept));
                    known();
                }}
                step();
                known(); known(); known(); known();
            }}
        "#
        );
        without_implicit_solve(|| verify_c_sources(&source, &[("wide.c", &c)])).unwrap();
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_01")]
fn region_footprint_refuses_unrecorded_memory_changes() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = ExecutionState::new();
    let after = before.clone().with_memory(before.memory().clone().store(
        crate::kernel::Pointer::symbolic(Variable(8_390_200)),
        ProgramValue::Int32(7u32.into()),
    ));
    let mut retained_states = RecordedStates::new();
    retained_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Entry,
        },
        before,
    );
    retained_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Exit,
        },
        after,
    );
    assert!(
        retained_states
            .footprint(&CodeRegionRef::Region(0))
            .is_err()
    );
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_01")]
fn region_footprint_identity_survives_unrelated_states() {
    let _session = crate::kernel::VerificationSession::enter();
    let state = ExecutionState::new();
    let mut retained_states = RecordedStates::new();
    retained_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Entry,
        },
        state.clone(),
    );
    retained_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(0),
            kind: ProgramPointKind::Exit,
        },
        state.clone(),
    );
    let first = retained_states
        .footprint(&CodeRegionRef::Region(0))
        .unwrap();
    retained_states.insert(
        ProgramPointRef {
            region: CodeRegionRef::Region(1),
            kind: ProgramPointKind::Entry,
        },
        state,
    );
    assert_eq!(
        first,
        retained_states
            .footprint(&CodeRegionRef::Region(0))
            .unwrap()
    );
}

#[test]
fn region_footprint_free_and_call_preservation_expands_without_search() {
    for (fixture, claim) in [
        (
            "mdtests/a_cell_beside_a_freed_allocation_is_framed.md",
            "dispose_beside",
        ),
        ("mdtests/region_footprint_call.md", "beside_call"),
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        without_implicit_solve(|| verify_c_sources(&source, &sources)).unwrap();
        let expanded =
            expand_c_claim_source(&source, &sources, claim, ContractProofClaim::Grouped).unwrap();
        assert!(!expanded.contains("transport_certificate"));
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
        if claim == "beside_call" {
            // The contract still supplies this separation. A selected proof
            // must not silently find it in the ambient context.
            let missing = source.replace("            separate(memory(*q), memory(*r));\n", "");
            assert_ne!(missing, source);
            assert!(verify_c_sources(&missing, &sources).is_err());
        }
    }
}

#[test]
#[ignore = "nightly: expands and replays complete memory proofs"]
fn cell_source_removal_repairs_expand_and_replay_without_implicit_search() {
    for (fixture, claim) in [
        (
            "mdtests/execute_in_a_proof_if_arm_splits_alias_cases_inside_a_c_if.md",
            "f",
        ),
        (
            "mdtests/failed_allocation_preserves_existing_loads.md",
            "failed_allocation_preserves_existing_loads",
        ),
        (
            "mdtests/loop_node_link_frames_across_parent_link_store.md",
            "rotate",
        ),
        ("mdtests/bubble_pass3_max_suffix.md", "bubble_pass3"),
    ] {
        let (source, sources) = mdtest_sources(fixture);
        let sources = sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        let expanded = expand_c_claim_source(&source, &sources, claim, ContractProofClaim::Grouped)
            .unwrap_or_else(|error| panic!("{fixture}: {}", error.report()));
        assert!(!expanded.contains("transport_certificate"), "{fixture}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap_or_else(|error| {
            panic!(
                "{fixture}: {}\nExpanded source:\n{expanded}",
                error.report()
            )
        });
    }
}

fn check_resource_field_certificate(ty: &str) {
    let (source, sources) = mdtest_sources("mdtests/preserve_resource_field.md");
    let source = source
        .replace(
            "abstract resource model()",
            "spec enum ModelValue { Empty, Value(int32) }\nabstract resource model()",
        )
        .replace("field value: int32;", &format!("field value: {ty};"));
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    without_implicit_solve(|| verify_c_sources(&source, &sources))
        .unwrap_or_else(|e| panic!("{ty}: {}", e.report()));
    let expanded =
        expand_c_claim_source(&source, &sources, "keep", ContractProofClaim::Grouped).unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_01")]
fn preserve_checks_named_resource_field() {
    check_resource_field_certificate("int32");
}
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_01")]
fn preserve_checks_integer_resource_field() {
    check_resource_field_certificate("Integer");
}
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_02")]
fn preserve_checks_wide_resource_field() {
    check_resource_field_certificate("uint64");
}
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_02")]
fn preserve_checks_pointer_resource_field() {
    check_resource_field_certificate("int32*");
}
#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_02")]
fn preserve_checks_algebraic_resource_field() {
    check_resource_field_certificate("ModelValue");
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_02")]
fn preserve_resource_descriptors_follow_call_bindings() {
    let (source, sources) = mdtest_sources("mdtests/preserve_resource_field.md");
    let caller = format!(
        "{source}\n{}",
        r#"
        void call_keep(int *p) {
            owns *p;
            owns other: model();
            requires separate(memory(*p), other);
        } by {
            step() { requires separate(memory(*p), other) by known(); }
            step();
            known(); known(); known(); known(); known();
        }
    "#
    );
    let c = format!("{}\nvoid call_keep(int *p) {{ keep(p); }}", sources[0].1);
    without_implicit_solve(|| verify_c_sources(&caller, &[("resource_frame.c", &c)]))
        .unwrap_or_else(|e| panic!("{}", e.report()));
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_03")]
fn preserve_refuses_other_or_modified_resource() {
    let (source, sources) = mdtest_sources("mdtests/preserve_resource_field.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let wrong_instance = source
        .replace("owns m: model();", "owns m: model(); owns n: model();")
        .replace("m.value", "n.value");
    let error = without_implicit_solve(|| verify_c_sources(&wrong_instance, &sources)).unwrap_err();
    assert!(
        error.report().contains("selected field"),
        "{}",
        error.report()
    );
    let changed_source = source.replace(
        "void keep(int *p) {",
        "extern void update(int *p) { owns m: model(); }\nvoid keep(int *p) {",
    );
    let changed_c = "void update(int *p); void keep(int *p) { update(p); }";
    let error = without_implicit_solve(|| {
        verify_c_sources(&changed_source, &[("resource_frame.c", changed_c)])
    })
    .unwrap_err();
    assert!(error.report().contains("normalize"), "{}", error.report());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_03")]
fn preserve_named_resource_is_a_theorem_argument() {
    let (source, sources) = mdtest_sources("mdtests/preserve_resource_field.md");
    let source = format!(
        "{}\n{source}",
        r#"
        theorem keep_separation(A: Resource, B: Resource) {
            requires separate(A, B);
            ensures separate(A, B) by { known(); }
        }
    "#
    )
    .replacen(
        "    step();",
        r#"
        have separate(memory(*p), m) by {
            apply(keep_separation(memory(*p), m)) using { separate(memory(*p), m); };
        }
        step();"#,
        1,
    );
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    without_implicit_solve(|| verify_c_sources(&source, &sources))
        .unwrap_or_else(|e| panic!("{}", e.report()));
    let expanded =
        expand_c_claim_source(&source, &sources, "keep", ContractProofClaim::Grouped).unwrap();
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
}

#[test]
#[ignore = "nightly: focused full destructor expansion"]
fn destructor_footprint_cleanup_expands_and_replays() {
    let path = std::path::Path::new(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/cpp_generic_class_state_in_a_resource.md");
    let fixture = crate::cli::read_mdtest(&path).unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let inputs = crate::cli::prepare_mdtest_inputs(&fixture).unwrap();
    let expanded = expand_claim_by_label(
        None,
        source,
        &inputs.program_inputs(),
        "__cpp_q_X8_537461636b3c543e_X6_7e537461636b.contract",
        None,
    )
    .unwrap_or_else(|error| panic!("{}", error.report()));
    assert!(!expanded.source.contains("transport_certificate"));
    let line = expanded
        .source
        .lines()
        .position(|line| line.contains("template<class T> Stack<T>::~Stack()"))
        .expect("destructor declaration")
        + 5;
    without_implicit_solve(|| {
        verify_sources_at(&expanded.source, &inputs.program_inputs(), line, 1)
    })
    .unwrap_or_else(|error| panic!("{}\n{}", error.report(), expanded.source));
}

#[test]
#[ignore = "nightly: full positive prefixes of pointer rejection fixtures"]
fn pointer_rejection_prefixes_expand_and_replay() {
    for (fixture, claim, from, to) in [
        (
            "joined_pointer_field_read_rejects_different_field",
            "inspect",
            "have model->right == leaf by {\n                                normalize() using { sibling == model; sibling->left == child; child == leaf; };\n                            }",
            "have child == leaf by { known(); }",
        ),
        (
            "mutex_protected_pointer_footprint_stale_read_rejected",
            "read_twice",
            "ensures result == 1;",
            "ensures result == 0 or result == 1;",
        ),
    ] {
        let (source, inputs) = mdtest_sources(&format!("mdtests/{fixture}.md"));
        // The ordinary fixtures still reject their original false claims.
        // Replay the otherwise identical proofs with their valid conclusions.
        let repaired = source.replace(from, to);
        assert_ne!(source, repaired);
        let inputs = inputs
            .iter()
            .map(|(n, s)| (n.as_str(), s.as_str()))
            .collect::<Vec<_>>();
        let expanded =
            expand_c_claim_source(&repaired, &inputs, claim, ContractProofClaim::Grouped)
                .unwrap_or_else(|error| panic!("{fixture}: {}", error.report()));
        without_implicit_solve(|| verify_c_sources(&expanded, &inputs))
            .unwrap_or_else(|error| panic!("{fixture}: {}\n{expanded}", error.report()));
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_03")]
fn preserve_step_carries_a_fact_with_ordinary_rewriting() {
    let (source, sources) = mdtest_sources("mdtests/preserve_step_carries_a_fact.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    without_implicit_solve(|| verify_c_sources(&source, &sources)).unwrap();
    let expanded =
        expand_c_claim_source(&source, &sources, "keep", ContractProofClaim::Grouped).unwrap();
    assert!(expanded.contains("preserve(separate("), "{expanded}");
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    let overlap = source.replace(
        "have *q == at(statement(0).entry, *q)",
        "have *p == at(statement(0).entry, *p)",
    );
    assert!(without_implicit_solve(|| verify_c_sources(&overlap, &sources)).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_04")]
fn resource_viewability_restriction_expands_without_transport() {
    for (fixture, claim) in [
        ("viewable_restrict_memory.md", "first"),
        ("viewable_restrict_resources.md", "view_component"),
    ] {
        let (source, sources) = mdtest_sources(&format!("mdtests/{fixture}"));
        let sources = sources
            .iter()
            .map(|(n, s)| (n.as_str(), s.as_str()))
            .collect::<Vec<_>>();
        without_implicit_solve(|| verify_c_sources(&source, &sources))
            .unwrap_or_else(|e| panic!("{fixture}: {}", e.report()));
        let expanded = expand_c_claim_source_by_label(
            &source,
            &sources,
            if claim == "first" {
                "first.contract"
            } else {
                "view_component.ensures_0"
            },
        )
        .unwrap();
        assert!(!expanded.contains("transport("), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_04")]
fn viewability_transport_expands_to_ordinary_restriction() {
    let (source, sources) = mdtest_sources("mdtests/viewable_restrict_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    verify_c_sources(&source, &sources).unwrap();
    let expanded = expand_c_claim_source_by_label(&source, &sources, "first.contract").unwrap();
    assert!(
        expanded.contains("separation::viewable_restrict"),
        "{expanded}"
    );
    assert!(
        expanded.contains("separation::contains_subrange"),
        "{expanded}"
    );
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_04")]
fn generic_viewability_transport_expands_to_ordinary_restriction() {
    let (source, _) = mdtest_sources("mdtests/viewable_restrict_resources.md");
    let source = source.replace(
        "apply(separation::viewable_restrict(A, B))",
        "transport(viewable(A), viewable(B))",
    );
    verify_c_sources(&source, &[]).unwrap();
    let expanded = expand_c_claim_source_by_label(&source, &[], "restrict_view.ensures_0").unwrap();
    assert!(
        expanded.contains("separation::viewable_restrict"),
        "{expanded}"
    );
    assert!(!expanded.contains("transport("), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &[])).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_04")]
fn single_write_transport_expands_to_preserve_without_search() {
    let (source, sources) = mdtest_sources("mdtests/single_write_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    verify_c_sources(&source, &sources).unwrap();
    let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
    assert!(expanded.contains("preserve(separate("), "{expanded}");
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    let overlap = source.replace("have *q == at(statement(0).entry, *q)", "have *p == at(statement(0).entry, *p)")
        .replace("transport(at(statement(0).entry, *q) == at(statement(0).entry, *q),\n            *q == at(statement(0).entry, *q))", "transport(at(statement(0).entry, *p) == at(statement(0).entry, *p),\n            *p == at(statement(0).entry, *p))");
    assert!(verify_c_sources(&overlap, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_05")]
fn single_write_resource_transport_expands_to_preserve_without_search() {
    let (source, sources) = mdtest_sources("mdtests/single_write_resource_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    verify_c_sources(&source, &sources).unwrap();
    let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
    assert!(expanded.contains("preserve(separate("), "{expanded}");
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_05")]
fn multiple_write_transport_expands_to_ordinary_equalities() {
    let (source, sources) = mdtest_sources("mdtests/multi_write_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    for source in [source.clone(), source.replace(
        "separate(statement(0).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*q));",
        "separate(statement(1).footprint, memory(*q));\n            separate(statement(0).footprint, memory(*q));",
    )] {
        verify_c_sources(&source, &sources).unwrap();
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(separate(").count(), 2, "{expanded}");
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_05")]
fn multiple_write_resource_transport_expands_to_ordinary_equalities() {
    let (source, sources) = mdtest_sources("mdtests/multi_write_resource_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
    assert_eq!(
        expanded.matches("preserve(separate(").count(),
        2,
        "{expanded}"
    );
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_05")]
fn multiple_write_transport_rejects_changed_reads_and_invalid_separation() {
    let (source, sources) = mdtest_sources("mdtests/multi_write_transport_expansion.md");
    let c = sources[0].1.replace("*p = 1;", "*p = 1; *q = 2;");
    let missing = source
        .replace("    have *q ==", "    step();\n    have *q ==")
        .replace("views *q;", "owns *q;");
    assert!(verify_c_sources(&missing, &[(sources[0].0.as_str(), c.as_str())]).is_err());
    let c = sources[0].1.replace("*p = 1;", "*q = 1;");
    let overlapping = source.replace("views *q;", "owns *q;");
    assert!(verify_c_sources(&overlapping, &[(sources[0].0.as_str(), c.as_str())]).is_err());
    let invalid = source.replace(
        "            separate(statement(1).footprint, memory(*q));",
        "            separate(statement(1).footprint, memory(*p));",
    );
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    assert!(verify_c_sources(&invalid, &sources).is_err());
}

#[test]
fn inequality_transport_expands_to_preserve_rewrite_and_known() {
    let (source, sources) = mdtest_sources("mdtests/inequality_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    for relation in [">", ">=", "<", "<=", "!="] {
        let source = source.replace("> 0", &format!("{relation} 0"));
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert!(expanded.contains("preserve(separate("), "{expanded}");
        assert!(expanded.contains("rewrite("), "{expanded}");
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
    let missing_source = source.replace("    requires *q > 0;\n", "");
    assert!(verify_c_sources(&missing_source, &sources).is_err());
    let changed_goal = source
        .replace("have *q > 0", "have *q > 1")
        .replace(", *q > 0)", ", *q > 1)");
    assert!(verify_c_sources(&changed_goal, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_06")]
fn inequality_transport_handles_multiple_statements_and_resource_fields() {
    let (source, sources) = mdtest_sources("mdtests/inequality_transport_expansion.md");
    let c = sources[0].1.replace("*p = 0;", "*p = 0; *p = 1;");
    let source = source.replace("    have *q > 0 by", r#"
    step();
    have separate(statement(1).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have *q > 0 by"#).replace("            separate(statement(0).footprint, memory(*q));",
        "            separate(statement(0).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*q));");
    let resource = source
        .replace(
            "void keep(int32*",
            "abstract resource model() { field value: int32; }\nvoid keep(int32*",
        )
        .replace("views *q;", "owns m: model();")
        .replace("memory(*q)", "m")
        .replace("*q", "m.value");
    let reversed = source.replace("*q > 0", "0 < *q").replace(
        "at(statement(0).entry, *q) > 0",
        "0 < at(statement(0).entry, *q)",
    );
    for source in [source, resource, reversed] {
        let sources = [(sources[0].0.as_str(), c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(
            expanded.matches("preserve(separate(").count(),
            2,
            "{expanded}"
        );
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_06")]
fn known_value_transport_expands_to_ordinary_steps() {
    let (source, sources) = mdtest_sources("mdtests/known_value_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let reversed = source.replace("*q == 7", "7 == *q").replace(
        "at(statement(0).entry, *q) == 7",
        "7 == at(statement(0).entry, *q)",
    );
    for source in [source.clone(), reversed] {
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert!(expanded.contains("preserve(separate("), "{expanded}");
        assert!(expanded.contains("rewrite("), "{expanded}");
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
    let missing_source = source.replace("    requires *q == 7;\n", "");
    assert!(verify_c_sources(&missing_source, &sources).is_err());
    let changed_value = source
        .replace("have *q == 7", "have *q == 8")
        .replace(", *q == 7)", ", *q == 8)");
    assert!(verify_c_sources(&changed_value, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_06")]
fn known_value_transport_preserves_resource_fields_across_statements() {
    let (source, sources) = mdtest_sources("mdtests/known_value_transport_expansion.md");
    let c = sources[0].1.replace("*p = 0;", "*p = 0; *p = 1;");
    let source = source.replace("    have *q == 7 by", r#"
    step();
    have separate(statement(1).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have *q == 7 by"#).replace("            separate(statement(0).footprint, memory(*q));", "            separate(statement(0).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*q));");
    let resource = source
        .replace(
            "void keep(int32*",
            "abstract resource model() { field value: int32; }\nvoid keep(int32*",
        )
        .replace("views *q;", "owns m: model();")
        .replace("memory(*q)", "m")
        .replace("*q", "m.value");
    for source in [source, resource] {
        let sources = [(sources[0].0.as_str(), c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(
            expanded.matches("preserve(separate(").count(),
            2,
            "{expanded}"
        );
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
fn state_comparison_transport_expands_without_search() {
    let (source, sources) = mdtest_sources("mdtests/state_comparison_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    for relation in ["==", "!=", "<", "<=", ">", ">="] {
        let source = source.replace("== 7", &format!("{relation} 7"));
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert!(expanded.contains("preserve(separate("), "{expanded}");
        assert!(expanded.contains("rewrite("), "{expanded}");
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
    let reversed = source.replace("*q == 7", "7 == *q");
    let expanded = expand_c_claim_source_by_label(&reversed, &sources, "keep.contract").unwrap();
    assert!(!expanded.contains("transport("), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    let missing = source.replace("    requires *q == 7;\n", "");
    assert!(verify_c_sources(&missing, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_06")]
fn state_comparison_transport_retains_the_other_operands_state() {
    let (source, sources) = mdtest_sources("mdtests/state_comparison_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let source = source
        .replace(
            "    requires *q == 7;",
            "    requires *q == 7;\n    requires *p == 7;",
        )
        .replace(
            "at(statement(0).entry, *q == 7)",
            "at(statement(0).entry, *q == *p)",
        )
        .replace("have *q == 7", "have *q == at(statement(0).entry, *p)")
        .replace(
            ", *q == 7) using",
            ", *q == at(statement(0).entry, *p)) using",
        );
    let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
    assert!(expanded.contains("preserve(separate("), "{expanded}");
    assert!(!expanded.contains("transport("), "{expanded}");
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    // The write changes p from 7 to 0. Its old value may not become its current value.
    let wrong = source
        .replace("have *q == at(statement(0).entry, *p)", "have *q == *p")
        .replace(
            ", *q == at(statement(0).entry, *p)) using",
            ", *q == *p) using",
        );
    assert!(verify_c_sources(&wrong, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_07")]
fn state_comparison_transport_handles_resource_fields_across_statements() {
    let (source, sources) = mdtest_sources("mdtests/state_comparison_transport_expansion.md");
    let c = sources[0].1.replace("*p = 0;", "*p = 0; *p = 1;");
    let source = source.replace("    have *q == 7 by", r#"
    step();
    have separate(statement(1).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have *q == 7 by"#).replace("            separate(statement(0).footprint, memory(*q));", "            separate(statement(0).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*q));");
    let resource = source
        .replace(
            "void keep(int32*",
            "abstract resource model() { field value: int32; }\nvoid keep(int32*",
        )
        .replace("views *q;", "owns m: model();")
        .replace("memory(*q)", "m")
        .replace("*q", "m.value");
    for source in [source, resource] {
        let sources = [(sources[0].0.as_str(), c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(
            expanded.matches("preserve(separate(").count(),
            2,
            "{expanded}"
        );
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
fn two_read_transport_expands_both_operands_without_search() {
    let (source, sources) = mdtest_sources("mdtests/two_read_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let mut variants = ["==", "!=", "<", "<=", ">", ">="]
        .into_iter()
        .map(|relation| source.replace("*q == *r", &format!("*q {relation} *r")))
        .collect::<Vec<_>>();
    variants.push(source.replace("*q == *r", "*r == *q"));
    variants.push(source.replace(
        "at(statement(0).entry, *q == *r)",
        "at(statement(0).entry, *q) == at(statement(0).entry, *r)",
    ));
    for source in variants {
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(
            expanded.matches("preserve(separate(").count(),
            2,
            "{expanded}"
        );
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_07")]
fn two_read_transport_refuses_changed_reads_and_missing_source() {
    let (source, sources) = mdtest_sources("mdtests/two_read_transport_expansion.md");
    for read in ["q", "r"] {
        let c = sources[0].1.replace("*p = 0;", &format!("*{read} = 0;"));
        let invalid = source.replace(&format!("views *{read};"), &format!("owns *{read};"));
        assert!(verify_c_sources(&invalid, &[(sources[0].0.as_str(), c.as_str())]).is_err());
    }
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    assert!(verify_c_sources(&source.replace("    requires *q == *r;\n", ""), &sources).is_err());
    let invalid = source.replace("            separate(statement(0).footprint, memory(*r));", "            separate(statement(0).footprint, memory(*r));\n            separate(statement(0).footprint, memory(*p));");
    assert!(verify_c_sources(&invalid, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_07")]
fn two_read_transport_handles_resources_and_multiple_statements() {
    let (source, sources) = mdtest_sources("mdtests/two_read_transport_expansion.md");
    let c = sources[0].1.replace("*p = 0;", "*p = 0; *p = 1;");
    let source = source.replace("    have *q == *r by", r#"
    step();
    have separate(statement(1).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have separate(statement(1).footprint, memory(*r)) by {
        normalize() using { separate(memory(*p), memory(*r)); };
    }
    have *q == *r by"#).replace("            separate(statement(0).footprint, memory(*r));", "            separate(statement(0).footprint, memory(*r));\n            separate(statement(1).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*r));");
    let resource = source
        .replace(
            "void keep(int32*",
            "abstract resource model() { field value: int32; }\nvoid keep(int32*",
        )
        .replace("views *q;", "owns a: model();")
        .replace("views *r;", "owns b: model();")
        .replace("memory(*q)", "a")
        .replace("memory(*r)", "b")
        .replace("*q", "a.value")
        .replace("*r", "b.value");
    for source in [source, resource] {
        let sources = [(sources[0].0.as_str(), c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(
            expanded.matches("preserve(separate(").count(),
            4,
            "{expanded}"
        );
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
fn conjunction_transport_expands_with_ordinary_both() {
    let (source, sources) = mdtest_sources("mdtests/conjunction_transport_expansion.md");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let variants = [
        source.clone(),
        source.replace("*r == 8", "*r > 8"),
        source.replace("*q == 7 and *r == 8", "*r == 8 and *q == 7"),
        source.replace(
            "at(statement(0).entry, *q == 7 and *r == 8)",
            "at(statement(0).entry, *q == 7) and at(statement(0).entry, *r == 8)",
        ),
    ];
    for source in variants {
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert!(expanded.contains("both {"), "{expanded}");
        assert_eq!(
            expanded.matches("preserve(separate(").count(),
            2,
            "{expanded}"
        );
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_07")]
fn conjunction_transport_requires_both_facts_and_preservations() {
    let (source, sources) = mdtest_sources("mdtests/conjunction_transport_expansion.md");
    for read in ["q", "r"] {
        let c = sources[0].1.replace("*p = 0;", &format!("*{read} = 0;"));
        let invalid = source.replace(&format!("views *{read};"), &format!("owns *{read};"));
        assert!(verify_c_sources(&invalid, &[(sources[0].0.as_str(), c.as_str())]).is_err());
    }
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    for remaining in ["*q == 7", "*r == 8"] {
        let missing = source.replace(
            "requires *q == 7 and *r == 8;",
            &format!("requires {remaining};"),
        );
        assert!(verify_c_sources(&missing, &sources).is_err());
    }
    let invalid = source.replace("            separate(statement(0).footprint, memory(*r));", "            separate(statement(0).footprint, memory(*r));\n            separate(statement(0).footprint, memory(*p));");
    assert!(verify_c_sources(&invalid, &sources).is_err());
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_08")]
fn conjunction_transport_handles_resources_and_multiple_statements() {
    let (source, sources) = mdtest_sources("mdtests/conjunction_transport_expansion.md");
    let c = sources[0].1.replace("*p = 0;", "*p = 0; *p = 1;");
    let source = source.replace("    have *q == 7 and *r == 8 by", r#"
    step();
    have separate(statement(1).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have separate(statement(1).footprint, memory(*r)) by {
        normalize() using { separate(memory(*p), memory(*r)); };
    }
    have *q == 7 and *r == 8 by"#).replace("            separate(statement(0).footprint, memory(*r));", "            separate(statement(0).footprint, memory(*r));\n            separate(statement(1).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*r));");
    let resource = source
        .replace(
            "void keep(int32*",
            "abstract resource model() { field value: int32; }\nvoid keep(int32*",
        )
        .replace("views *q;", "owns a: model();")
        .replace("views *r;", "owns b: model();")
        .replace("memory(*q)", "a")
        .replace("memory(*r)", "b")
        .replace("*q", "a.value")
        .replace("*r", "b.value");
    for source in [source, resource] {
        let sources = [(sources[0].0.as_str(), c.as_str())];
        let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
        assert_eq!(
            expanded.matches("preserve(separate(").count(),
            4,
            "{expanded}"
        );
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    }
}

#[test]
fn nested_conjunction_transport_expands_and_replays() {
    let (source, files) = mdtest_sources("mdtests/nested_conjunction_transport_expansion.md");
    let files = files
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let nested = "*q == 7 and (*r == 8 and *s == 9)";
    let resource = source
        .replace(
            "void keep(int32*",
            "abstract resource model() { field value: int32; }\nvoid keep(int32*",
        )
        .replace("views *q;", "owns a: model();")
        .replace("views *r;", "owns b: model();")
        .replace("views *s;", "owns c: model();")
        .replace("memory(*q)", "a")
        .replace("memory(*r)", "b")
        .replace("memory(*s)", "c")
        .replace("*q", "a.value")
        .replace("*r", "b.value")
        .replace("*s", "c.value");
    for source in [
        source.clone(),
        source.replace(nested, "(*q == 7 and *r == 8) and *s == 9"),
        source.replace(nested, "(*q == 7 and *r == 8) and (*s == 9 and *q > 0)"),
        source.replace(
            &format!("at(statement(0).entry, {nested})"),
            "at(statement(0).entry, *q == 7) and at(statement(0).entry, *r == 8 and *s == 9)",
        ),
        resource,
    ] {
        let expanded = expand_c_claim_source_by_label(&source, &files, "keep.contract").unwrap();
        assert!(expanded.matches("both {").count() >= 2, "{expanded}");
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &files)).unwrap();
    }
}

#[test]
#[cfg_attr(feature = "fast-gate", ignore = "covered by transport_batch_08")]
fn nested_conjunction_transport_checks_deep_leaves_and_all_evidence() {
    let (source, files) = mdtest_sources("mdtests/nested_conjunction_transport_expansion.md");
    for read in ["q", "r", "s"] {
        let c = files[0].1.replace("*p = 0;", &format!("*{read} = 0;"));
        let invalid = source.replace(&format!("views *{read};"), &format!("owns *{read};"));
        assert!(verify_c_sources(&invalid, &[(files[0].0.as_str(), c.as_str())]).is_err());
    }
    let files = files
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    for invalid in [
        source.replace("requires *q == 7 and (*r == 8 and *s == 9);", "requires *q == 7 and *r == 8;"),
        source.replace("            separate(statement(0).footprint, memory(*s));",
            "            separate(statement(0).footprint, memory(*s));\n            separate(statement(0).footprint, memory(*p));"),
    ] {
        assert!(verify_c_sources(&invalid, &files).is_err());
    }
}

#[test]
fn conjunction_projection_transport_expands_only_the_selected_leaf() {
    let (source, files) = mdtest_sources("mdtests/conjunction_projection_transport_expansion.md");
    let files = files
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let resource = source
        .replace(
            "void keep(int32*",
            "abstract resource model() { field value: int32; }\nvoid keep(int32*",
        )
        .replace("views *q;", "owns a: model();")
        .replace("memory(*q)", "a")
        .replace("*q", "a.value");
    for source in [
        source.clone(),
        source.replace("*p == 8 and *q == 7", "*q == 7 and *p == 8"),
        source.replace("*p == 8 and *q == 7", "*p == 8 and (*p > 0 and *q == 7)"),
        source.replace("at(statement(0).entry, *p == 8 and *q == 7)", "at(statement(0).entry, *p == 8) and at(statement(0).entry, *q == 7)"),
        source.replace("            separate(statement(0).footprint", "            at(statement(0).entry, *p == 8 and *q == 7);\n            separate(statement(0).footprint"),
        resource,
    ] {
        let expanded = expand_c_claim_source_by_label(&source, &files, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(separate(").count(), 1, "{expanded}");
        assert!(!expanded.contains("both {"), "{expanded}");
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &files)).unwrap();
    }
}

#[test]
fn conjunction_projection_transport_checks_source_and_preservation() {
    let (source, files) = mdtest_sources("mdtests/conjunction_projection_transport_expansion.md");
    let changed_c = files[0].1.replace("*p = 0;", "*q = 0;");
    let changed = source.replace("views *q;", "owns *q;");
    assert!(verify_c_sources(&changed, &[(files[0].0.as_str(), changed_c.as_str())]).is_err());
    let files = files
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    for invalid in [
        source.replace("requires *p == 8 and *q == 7;", "requires *p == 8;"),
        source.replace("at(statement(0).entry, *p == 8 and *q == 7)", "at(statement(0).entry, *p == 8 and *q == 9)"),
        source.replace("            separate(statement(0).footprint, memory(*q));", "            separate(statement(0).footprint, memory(*q));\n            separate(statement(0).footprint, memory(*p));"),
    ] {
        assert!(verify_c_sources(&invalid, &files).is_err());
    }
}

#[test]
fn conjunction_projection_transport_crosses_multiple_statements() {
    let (source, files) = mdtest_sources("mdtests/conjunction_projection_transport_expansion.md");
    let c = files[0].1.replace("*p = 0;", "*p = 0; *p = 1;");
    let source = source.replace("    have *q == 7 by", r#"
    step();
    have separate(statement(1).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have *q == 7 by"#).replace("            separate(statement(0).footprint, memory(*q));", "            separate(statement(0).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*q));");
    let files = [(files[0].0.as_str(), c.as_str())];
    let expanded = expand_c_claim_source_by_label(&source, &files, "keep.contract").unwrap();
    assert_eq!(expanded.matches("preserve(separate(").count(), 2);
    assert!(!expanded.contains("transport("));
    assert!(!expanded.contains("transport_certificate"));
    without_implicit_solve(|| verify_c_sources(&expanded, &files)).unwrap();
}

#[test]
fn conjunction_selection_transport_expands_and_replays() {
    let (source, files) = mdtest_sources("mdtests/conjunction_selection_transport_expansion.md");
    let files = files
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let resource = source
        .replace(
            "void keep(int32*",
            "abstract resource model() { field value: int32; }\nvoid keep(int32*",
        )
        .replace("views *q;", "owns a: model();")
        .replace("views *r;", "owns b: model();")
        .replace("memory(*q)", "a")
        .replace("memory(*r)", "b")
        .replace("*q", "a.value")
        .replace("*r", "b.value");
    for source in [
        source.clone(),
        source.replace("*q == 7 and *r == 8", "*r == 8 and *q == 7"),
        source.replace("*q == 7 and *r == 8", "(*r == 8 and *q == 7) and *q == 7"),
        source.replace("*q == 7 and (*p == 8 and *r == 8)", "(*q == 7 and *q > 0) and (*p == 8 and *r == 8)")
            .replace("*q == 7 and *r == 8", "(*r == 8 and *q > 0) and *q == 7"),
        source.replace("at(statement(0).entry, *q == 7 and (*p == 8 and *r == 8))", "at(statement(0).entry, *q == 7) and at(statement(0).entry, *p == 8 and *r == 8)"),
        source.replace("            separate(statement(0).footprint, memory(*q));", "            at(statement(0).entry, *q == 7 and (*p == 8 and *r == 8));\n            separate(statement(0).footprint, memory(*q));"),
        resource,
    ] {
        let expanded = expand_c_claim_source_by_label(&source, &files, "keep.contract").unwrap();
        assert!(expanded.contains("both {"), "{expanded}");
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &files)).unwrap();
    }
}

#[test]
fn conjunction_selection_transport_checks_every_selected_leaf() {
    let (source, files) = mdtest_sources("mdtests/conjunction_selection_transport_expansion.md");
    for read in ["q", "r"] {
        let c = files[0].1.replace("*p = 0;", &format!("*{read} = 0;"));
        let invalid = source.replace(&format!("views *{read};"), &format!("owns *{read};"));
        assert!(verify_c_sources(&invalid, &[(files[0].0.as_str(), c.as_str())]).is_err());
    }
    let files = files
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    for invalid in [
        source.replace("requires *q == 7 and (*p == 8 and *r == 8);", "requires *q == 7 and *p == 8;"),
        source.replace("*q == 7 and *r == 8", "*q == 7 and *r == 9"),
        source.replace("            separate(statement(0).footprint, memory(*q));", "            separate(statement(0).footprint, memory(*q));\n            separate(statement(0).footprint, memory(*p));"),
    ] {
        assert!(verify_c_sources(&invalid, &files).is_err());
    }
}

#[test]
fn conjunction_selection_transport_crosses_multiple_statements() {
    let (source, files) = mdtest_sources("mdtests/conjunction_selection_transport_expansion.md");
    let c = files[0].1.replace("*p = 0;", "*p = 0; *p = 1;");
    let source = source.replace("    have *q == 7 and *r == 8 by", r#"
    step();
    have separate(statement(1).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have separate(statement(1).footprint, memory(*r)) by {
        normalize() using { separate(memory(*p), memory(*r)); };
    }
    have *q == 7 and *r == 8 by"#).replace("            separate(statement(0).footprint, memory(*r));", "            separate(statement(0).footprint, memory(*r));\n            separate(statement(1).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*r));");
    let files = [(files[0].0.as_str(), c.as_str())];
    let expanded = expand_c_claim_source_by_label(&source, &files, "keep.contract").unwrap();
    assert_eq!(expanded.matches("preserve(separate(").count(), 4);
    assert!(!expanded.contains("transport("));
    assert!(!expanded.contains("transport_certificate"));
    without_implicit_solve(|| verify_c_sources(&expanded, &files)).unwrap();
}

#[test]
fn implication_transport_expands_by_preserving_guard_and_conclusion() {
    let (source, files) = mdtest_sources("mdtests/implication_transport_expansion.md");
    let files = files
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let resource = source
        .replace(
            "void keep(int32*",
            "abstract resource model() { field value: int32; }\nvoid keep(int32*",
        )
        .replace("views *q;", "owns a: model();")
        .replace("views *r;", "owns b: model();")
        .replace("memory(*q)", "a")
        .replace("memory(*r)", "b")
        .replace("*q", "a.value")
        .replace("*r", "b.value");
    let shared = source.replace("*r == 8", "*q > 0").replace(
        "            separate(statement(0).footprint, memory(*r));",
        "",
    );
    for (source, preserves) in [
        (source.clone(), 2),
        (source.replace("*q == 7 implies *r == 8", "*q > 0 implies *r != 8"), 2),
        (source.replace("*q == 7 implies *r == 8", "*q < *r implies *r == 8"), 2),
        (source.replace("at(statement(0).entry, *q == 7 implies *r == 8)", "at(statement(0).entry, *q == 7) implies at(statement(0).entry, *r == 8)"), 2),
        (source.replace("            separate(statement(0).footprint, memory(*q));", "            at(statement(0).entry, *q == 7 implies *r == 8);\n            separate(statement(0).footprint, memory(*q));"), 2),
        (resource, 2),
        (shared, 1),
    ] {
        let expanded = expand_c_claim_source_by_label(&source, &files, "keep.contract").unwrap();
        assert_eq!(expanded.matches("preserve(separate(").count(), preserves, "{expanded}");
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &files)).unwrap();
    }
}

#[test]
fn implication_transport_handles_four_distinct_reads() {
    let (mut source, files) = mdtest_sources("mdtests/implication_transport_expansion.md");
    let c = files[0].1.replace("int *r)", "int *r, int *s, int *t)");
    source = source
        .replace("int32* r)", "int32* r, int32* s, int32* t)")
        .replace("*q == 7 implies *r == 8", "*q < *r implies *s < *t");
    for read in ["s", "t"] {
        source = source.replace("    views *q;", &format!("    views *{read};\n    requires separate(memory(*p), memory(*{read}));\n    views *q;"))
            .replace("    have *q < *r implies *s < *t by", &format!("    have separate(statement(0).footprint, memory(*{read})) by {{ normalize() using {{ separate(memory(*p), memory(*{read})); }}; }}\n    have *q < *r implies *s < *t by"))
            .replace("            separate(statement(0).footprint, memory(*q));", &format!("            separate(statement(0).footprint, memory(*{read}));\n            separate(statement(0).footprint, memory(*q));"));
    }
    let files = [(files[0].0.as_str(), c.as_str())];
    let expanded = expand_c_claim_source_by_label(&source, &files, "keep.contract").unwrap();
    assert_eq!(expanded.matches("preserve(separate(").count(), 4);
    assert!(!expanded.contains("transport("));
    assert!(!expanded.contains("transport_certificate"));
    without_implicit_solve(|| verify_c_sources(&expanded, &files)).unwrap();
}

#[test]
fn implication_transport_rejects_changed_guard_and_conclusion() {
    let (source, files) = mdtest_sources("mdtests/implication_transport_expansion.md");
    for (read, initial, write) in [
        ("q", "*q == 0 and *r == 0", "*q = 7;"),
        ("r", "*q == 7 and *r == 8", "*r = 0;"),
    ] {
        // Old implication holds in both cases; the resulting implication is false.
        // Supply only genuine preservation of the other read, so refusal cannot
        // come from an earlier attempt to prove a false footprint separation.
        let c = files[0].1.replace("*p = 0;", write);
        let mut invalid = source.replace(&format!("views *{read};"), &format!("owns *{read};"))
            .replace("    requires *q == 7 implies *r == 8;", &format!("    requires {initial};\n    requires separate(memory(*q), memory(*r));\n    requires *q == 7 implies *r == 8;"));
        let block = format!(
            "    have separate(statement(0).footprint, memory(*{read})) by {{\n        normalize() using {{ separate(memory(*p), memory(*{read})); }};\n    }}\n"
        );
        invalid = invalid
            .replace(&block, "")
            .replace(
                &format!("            separate(statement(0).footprint, memory(*{read}));"),
                "            at(statement(0).entry, *q == 7 implies *r == 8);",
            )
            .replace(
                "normalize() using { separate(memory(*p), memory(*q)); };",
                "normalize() using { separate(memory(*q), memory(*r)); };",
            )
            .replace(
                "normalize() using { separate(memory(*p), memory(*r)); };",
                "normalize() using { separate(memory(*q), memory(*r)); };",
            );
        assert!(verify_c_sources(&invalid, &[(files[0].0.as_str(), c.as_str())]).is_err());
    }
    let files = files
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    for invalid in [
        source.replace("    requires *q == 7 implies *r == 8;", ""),
        source.replace("            separate(statement(0).footprint, memory(*q));", "            separate(statement(0).footprint, memory(*q));\n            separate(statement(0).footprint, memory(*p));"),
    ] {
        assert!(verify_c_sources(&invalid, &files).is_err());
    }
}

#[test]
fn implication_transport_crosses_multiple_statements() {
    let (source, files) = mdtest_sources("mdtests/implication_transport_expansion.md");
    let c = files[0].1.replace("*p = 0;", "*p = 0; *p = 1;");
    let source = source.replace("    have *q == 7 implies *r == 8 by", r#"
    step();
    have separate(statement(1).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have separate(statement(1).footprint, memory(*r)) by {
        normalize() using { separate(memory(*p), memory(*r)); };
    }
    have *q == 7 implies *r == 8 by"#).replace("            separate(statement(0).footprint, memory(*r));", "            separate(statement(0).footprint, memory(*r));\n            separate(statement(1).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*r));");
    let files = [(files[0].0.as_str(), c.as_str())];
    let expanded = expand_c_claim_source_by_label(&source, &files, "keep.contract").unwrap();
    assert_eq!(expanded.matches("preserve(separate(").count(), 4);
    assert!(!expanded.contains("transport("));
    assert!(!expanded.contains("transport_certificate"));
    without_implicit_solve(|| verify_c_sources(&expanded, &files)).unwrap();
}

#[test]
fn compound_implication_transport_expands_without_whole_goal_rewrites() {
    let (source, files) = mdtest_sources("mdtests/compound_implication_transport_expansion.md");
    let files = files
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let original = "(*q == 7 and *r > 0) implies (*q > 0 implies *r == 8)";
    let resource = source
        .replace(
            "void keep(int32*",
            "abstract resource model() { field value: int32; }\nvoid keep(int32*",
        )
        .replace("views *q;", "owns a: model();")
        .replace("views *r;", "owns b: model();")
        .replace("memory(*q)", "a")
        .replace("memory(*r)", "b")
        .replace("*q", "a.value")
        .replace("*r", "b.value");
    let mut variants = vec![resource, source.replace(&format!("at(statement(0).entry, {original})"),
        "at(statement(0).entry, *q == 7 and *r > 0) implies at(statement(0).entry, *q > 0 implies *r == 8)")];
    for formula in [
        original,
        "(*q == 7 or *r == 0) implies (*q > 0 implies *r == 8)",
        "not (*q != 7) implies (not (*r != 8) and (*q > 0 implies *r == 8))",
        "(*q == 7 implies *r == 8) implies (*r > 0 implies *q > 0)",
        "(*q == 7 and *r > 0) implies ((*q > 0 and *r == 8) or *q == 0)",
    ] {
        variants.push(source.replace(original, formula));
    }
    for source in variants {
        let expanded = expand_c_claim_source_by_label(&source, &files, "keep.contract").unwrap();
        assert_eq!(
            expanded.matches("preserve(separate(").count(),
            2,
            "{expanded}"
        );
        assert!(!expanded.contains("rewrite("), "{expanded}");
        assert!(!expanded.contains("transport("), "{expanded}");
        assert!(!expanded.contains("transport_certificate"), "{expanded}");
        without_implicit_solve(|| verify_c_sources(&expanded, &files)).unwrap();
    }
}

#[test]
fn compound_implication_transport_rejects_changed_nested_guards() {
    let (source, files) = mdtest_sources("mdtests/compound_implication_transport_expansion.md");
    let original = "(*q == 7 and *r > 0) implies (*q > 0 implies *r == 8)";
    for formula in [
        original,
        "(*r > 0) implies (*q == 7 implies *r == 8)",
        "(*q == 7 or *r == 0) implies *r == 8",
    ] {
        // q=0,r=7 satisfies each historical fact; q=7,r=7 falsifies each target.
        let c = files[0].1.replace("*p = 0;", "*q = 7;");
        let invalid = source.replace(original, formula).replace("views *q;", "owns *q;")
            .replace(&format!("    requires {formula};"), &format!("    requires *q == 0 and *r == 7;\n    requires separate(memory(*q), memory(*r));\n    requires {formula};"))
            .replace("    have separate(statement(0).footprint, memory(*q)) by {\n        normalize() using { separate(memory(*p), memory(*q)); };\n    }\n", "")
            .replace("normalize() using { separate(memory(*p), memory(*r)); };", "normalize() using { separate(memory(*q), memory(*r)); };")
            .replace("            separate(statement(0).footprint, memory(*q));", &format!("            at(statement(0).entry, {formula});"));
        assert!(verify_c_sources(&invalid, &[(files[0].0.as_str(), c.as_str())]).is_err());
    }
    let files = files
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    for invalid in [
        source.replace(&format!("    requires {original};"), ""),
        source.replace("            separate(statement(0).footprint, memory(*r));", "            separate(statement(0).footprint, memory(*r));\n            separate(statement(0).footprint, memory(*p));"),
    ] { assert!(verify_c_sources(&invalid, &files).is_err()); }
}

#[test]
fn compound_implication_transport_crosses_multiple_statements() {
    let (source, files) = mdtest_sources("mdtests/compound_implication_transport_expansion.md");
    let c = files[0].1.replace("*p = 0;", "*p = 0; *p = 1;");
    let source = source.replace("    have (*q == 7 and *r > 0) implies", r#"
    step();
    have separate(statement(1).footprint, memory(*q)) by {
        normalize() using { separate(memory(*p), memory(*q)); };
    }
    have separate(statement(1).footprint, memory(*r)) by {
        normalize() using { separate(memory(*p), memory(*r)); };
    }
    have (*q == 7 and *r > 0) implies"#).replace("            separate(statement(0).footprint, memory(*r));", "            separate(statement(0).footprint, memory(*r));\n            separate(statement(1).footprint, memory(*q));\n            separate(statement(1).footprint, memory(*r));");
    let files = [(files[0].0.as_str(), c.as_str())];
    let expanded = expand_c_claim_source_by_label(&source, &files, "keep.contract").unwrap();
    assert_eq!(expanded.matches("preserve(separate(").count(), 4);
    assert!(!expanded.contains("rewrite("));
    assert!(!expanded.contains("transport("));
    assert!(!expanded.contains("transport_certificate"));
    without_implicit_solve(|| verify_c_sources(&expanded, &files)).unwrap();
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "preservation.rs",
    marker: "transport_batch_",
    transport_batch_00: [
        preserve_checks_byte_reads_without_search,
        preserve_checks_pointer_read,
        ordinary_equalities_compose_without_search,
        preserve_checks_signed_and_unsigned_64_bit_reads,
    ],
    transport_batch_01: [
        region_footprint_refuses_unrecorded_memory_changes,
        region_footprint_identity_survives_unrelated_states,
        preserve_checks_named_resource_field,
        preserve_checks_integer_resource_field,
    ],
    transport_batch_02: [
        preserve_checks_wide_resource_field,
        preserve_checks_pointer_resource_field,
        preserve_checks_algebraic_resource_field,
        preserve_resource_descriptors_follow_call_bindings,
    ],
    transport_batch_03: [
        preserve_refuses_other_or_modified_resource,
        preserve_named_resource_is_a_theorem_argument,
        preserve_step_carries_a_fact_with_ordinary_rewriting,
    ],
    transport_batch_04: [
        resource_viewability_restriction_expands_without_transport,
        viewability_transport_expands_to_ordinary_restriction,
        generic_viewability_transport_expands_to_ordinary_restriction,
        single_write_transport_expands_to_preserve_without_search,
    ],
    transport_batch_05: [
        single_write_resource_transport_expands_to_preserve_without_search,
        multiple_write_transport_expands_to_ordinary_equalities,
        multiple_write_resource_transport_expands_to_ordinary_equalities,
        multiple_write_transport_rejects_changed_reads_and_invalid_separation,
    ],
    transport_batch_06: [
        inequality_transport_handles_multiple_statements_and_resource_fields,
        known_value_transport_expands_to_ordinary_steps,
        known_value_transport_preserves_resource_fields_across_statements,
        state_comparison_transport_retains_the_other_operands_state,
    ],
    transport_batch_07: [
        state_comparison_transport_handles_resource_fields_across_statements,
        two_read_transport_refuses_changed_reads_and_missing_source,
        two_read_transport_handles_resources_and_multiple_statements,
        conjunction_transport_requires_both_facts_and_preservations,
    ],
    transport_batch_08: [
        conjunction_transport_handles_resources_and_multiple_statements,
        nested_conjunction_transport_checks_deep_leaves_and_all_evidence,
    ],
}

#[test]
#[ignore = "nightly: computed scalar transport expansion and cold replay"]
fn computed_scalar_transport_expands_read_preservation() {
    let (source, sources) = mdtest_sources("mdtests/state_comparison_transport_expansion.md");
    let source = source.replace("*q == 7", "*q + 1 == 8");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
    assert!(!expanded.contains("transport("), "{expanded}");
    assert_eq!(
        expanded.matches("preserve(separate(").count(),
        1,
        "{expanded}"
    );
    assert!(!expanded.contains("transport_certificate"), "{expanded}");
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    let missing = source.replace("    requires *q + 1 == 8;\n", "");
    assert!(verify_c_sources(&missing, &sources).is_err());
    let changed = expanded.replacen(
        "have (to_integer(*q) + 1) == 8",
        "have (to_integer(*q) + 1) == 9",
        1,
    );
    assert_ne!(changed, expanded);
    assert!(without_implicit_solve(|| verify_c_sources(&changed, &sources)).is_err());
}

#[test]
#[ignore = "nightly: indexed transport expansion and cold replay"]
fn indexed_read_transport_expands_to_selected_preservation() {
    let (source, sources) = mdtest_sources("mdtests/two_read_transport_expansion.md");
    let source = source.replace("*q", "q[0]").replace("*r", "q[1]");
    let source = source.replace(
        "            separate(statement(0).footprint, memory(q[0]));",
        "            at(statement(0).entry, q[0] == q[1]);\n            separate(statement(0).footprint, memory(q[0]));",
    );
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
    assert!(!expanded.contains("transport("), "{expanded}");
    assert_eq!(
        expanded.matches("preserve(separate(").count(),
        2,
        "{expanded}"
    );
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
}

#[test]
#[ignore = "nightly: returned-have transport expansion and cold replay"]
fn a_returned_have_expands_the_same_single_preservation() {
    let (source, sources) = mdtest_sources("mdtests/single_write_transport_expansion.md");
    let source = source
        .replace(
            "    requires separate(memory(*p), memory(*q));",
            "    requires separate(memory(*p), memory(*q));\n    ensures 1 == 1;",
        )
        .replace("    have *q ==", "    step();\n    have *q ==")
        .replace("    step();\n}", "    known();\n}");
    let sources = sources
        .iter()
        .map(|(n, s)| (n.as_str(), s.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_c_claim_source_by_label(&source, &sources, "keep.contract").unwrap();
    assert!(!expanded.contains("transport("), "{expanded}");
    assert_eq!(
        expanded.matches("preserve(separate(").count(),
        1,
        "{expanded}"
    );
    without_implicit_solve(|| verify_c_sources(&expanded, &sources)).unwrap();
    let changed = expanded.replace("at(statement(0).exit, *q)", "at(statement(0).exit, *p)");
    assert_ne!(changed, expanded, "the preservation names its exit read");
    assert!(without_implicit_solve(|| verify_c_sources(&changed, &sources)).is_err());
}

#[test]
fn memory_observation_after_a_write_expands_and_replays() {
    let (source, sources) = mdtest_sources("mdtests/observe_memory_after_store.md");
    let sources = sources
        .iter()
        .map(|(name, text)| (name.as_str(), text.as_str()))
        .collect::<Vec<_>>();
    let expanded = expand_function_proof_source(&source, &sources, "update").unwrap();
    assert!(expanded.contains("observe(p[0..n])"), "{expanded}");
    assert!(!expanded.contains("transport("), "{expanded}");
    without_implicit_solve_for_claim("update.contract", || {
        verify_c_sources(&expanded, &sources).map_err(|error| error.report())
    })
    .unwrap();
    let larger = source.replace("observe(p[0..n])", "observe(p[0..n+1])");
    assert!(verify_c_sources(&larger, &sources).is_err());
}

#[test]
fn memory_observation_does_not_establish_initialization() {
    let source = r#"
        verifying "unwritten.c";
        void unwritten(int32 *p) {
            owns uninitialized(p[0..2]);
            ensures defined(p[1]);
        } by {
            step_until(function.exit);
            observe(p[0..2]);
            known();
        }
    "#;
    let sources = [("unwritten.c", "void unwritten(int32 *p) {}")];
    let live_only = source.replace("ensures defined(p[1]);", "ensures viewable(p[0..2]);");
    verify_c_sources(&live_only, &sources).unwrap();
    let unowned = live_only.replace("owns uninitialized(p[0..2]);", "");
    let error = verify_c_sources(&unowned, &sources).unwrap_err();
    assert!(
        error.message().contains("exact memory range"),
        "{}",
        error.report()
    );
    let error = verify_c_sources(source, &sources).unwrap_err();
    assert!(
        error.report().contains("goal: defined(p[1])"),
        "{}",
        error.report()
    );
}
