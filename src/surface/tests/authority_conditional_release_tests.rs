use super::*;

const C: &str = r#"struct child { int32 refs; int32 payload; };

void child_release(struct child* obj) {
    if (obj->refs == 1) {
        free(obj);
    } else {
        obj->refs = obj->refs - 1;
    }
}

void release_one(struct child* obj) {
    child_release(obj);
}
"#;
const SOURCE: &str = r#"import click::integer;
authorized resource child_ref(obj: struct child*) {}

resource child_control(obj: struct child*) {
    owns allocation(obj, sizeof(struct child));
    owns *obj;
    owns authority(child_ref(obj));
    fact obj->refs == count(child_ref(obj));
}


verifying "conditional_release.c";

void child_release(struct child* obj) {
    requires 1 <= obj->refs;
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(obj->refs) > 1 {
        produces child_control(obj);
    }
    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;
    ensures old(count(child_ref(obj))) > 1 implies obj->payload == old(obj->payload);
} by {
    unfold(child_control(obj));
    if obj->refs == 1 {
        unfold(child_ref(obj));
        unfold(authority(child_ref(obj)));
        step_until(function.exit);
        close();
    } else {
        unfold(child_ref(obj));
        have 1 < obj->refs by {
            close() using { 1 <= obj->refs; obj->refs != 1; }
        }
        have to_integer(obj->refs - 1) >= 1;
        step();
        step();
        fold(child_control(obj));
        step_until(function.exit);
        close();
    }
}


void release_one(struct child* obj) {
    requires 1 < obj->refs;
    owns child_control(obj);
    consumes child_ref(obj);
    ensures obj->payload == old(obj->payload);
} by {
    have obj->refs == count(child_ref(obj)) by { close(); }
    have 1 < count(child_ref(obj)) by { close(); }
    step(child_release);
    have obj->payload == old(obj->payload) by { close(); }
    step();
    close();
}
"#;

fn verify(source: &str) -> Result<Vec<VerifiedProgramTheorem>, ClickError> {
    let project = ClickProject::new(
        "conditional_release.click",
        [ClickModuleSource::new(
            "conditional_release.click",
            source,
            [],
        )],
    )
    .with_c_profile(CProjectProfile {
        target: None,
        runtime: None,
    });
    verify_c_project(&project, &[("conditional_release.c", C)])
}

#[test]
fn authority_conditional_release_certifies_its_resource_guard() {
    let source = SOURCE
        .split("void release_one(struct child* obj)")
        .next()
        .unwrap();
    verify(source).expect("the guarded resource claim certifies under both C branches");
}

#[test]
fn authority_conditional_release_rejects_returning_control_after_free() {
    let source = SOURCE.replace("if old(obj->refs) > 1", "if old(obj->refs) >= 1");
    let error = verify(&source).expect_err("the final branch cannot return freed control");
    assert!(error.message().contains("child_control"), "{error:?}");
}

#[test]
fn authority_conditional_release_rejects_missing_returned_control_witness() {
    let source = SOURCE.replace("fold(child_control(obj));", "");
    verify(&source)
        .expect_err("a conditional claim key cannot replace its returned resource witness");
}

#[test]
fn authority_conditional_release_keeps_undischarged_ensure_premise() {
    let source = SOURCE.replace(
        "old(count(child_ref(obj))) > 1 implies",
        "old(count(child_ref(obj))) > 2 implies",
    );
    verify(&source).expect_err("a checked count bound cannot assume the callee's stronger premise");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn authority_conditional_release_expansion_roundtrips_every_smart_site() {
    let source = SOURCE.replace(
        "    ensures obj->payload == old(obj->payload);",
        "    ensures obj->payload == old(obj->payload);\n    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;",
    );
    let project = ClickProject::new(
        "conditional_release.click",
        [ClickModuleSource::new(
            "conditional_release.click",
            &source,
            [],
        )],
    )
    .with_c_profile(CProjectProfile {
        target: None,
        runtime: None,
    });
    let c = [("conditional_release.c", C)];
    let sites =
        project_smart_tactic_source_sites(&project, &ProgramInputs::Bundle(c.to_vec())).unwrap();
    assert!(!sites.is_empty());
    for site in sites {
        let position = project_tactic_source_position(
            &project,
            &ProgramInputs::Bundle(c.to_vec()),
            &site.claim_label,
            site.source_index,
        )
        .unwrap();
        let expanded = expand_project_tactic_source_at(
            &project,
            &ProgramInputs::Bundle(c.to_vec()),
            position.line,
            position.column,
        )
        .unwrap();
        verify(&expanded).unwrap_or_else(|error| {
            panic!(
                "{} site {} ({}) expansion failed: {}",
                site.claim_label,
                site.source_index,
                site.tactic_name,
                error.message()
            )
        });
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn authority_borrowed_member_handoff_expands_every_smart_site() {
    let fixture = crate::cli::parse_mdtest(
        std::path::Path::new("shared_heap_detach_old_resource_handoff.md"),
        include_str!("../../../mdtests/shared_heap_detach_old_resource_handoff.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let c = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let project = ClickProject::new(
        "handoff.click",
        [ClickModuleSource::new("handoff.click", source, [])],
    )
    .with_c_profile(CProjectProfile {
        target: None,
        runtime: None,
    });
    verify_c_project(&project, &c).expect("the original handoff proof verifies");
    let sites =
        project_smart_tactic_source_sites(&project, &ProgramInputs::Bundle(c.to_vec())).unwrap();
    assert!(!sites.is_empty());
    for site in sites {
        let position = site.position;
        let expanded = expand_project_tactic_source_at(
            &project,
            &ProgramInputs::Bundle(c.to_vec()),
            position.line,
            position.column,
        )
        .unwrap();
        let expanded_project = ClickProject::new(
            "handoff.click",
            [ClickModuleSource::new("handoff.click", &expanded, [])],
        )
        .with_c_profile(CProjectProfile {
            target: None,
            runtime: None,
        });
        let owner = site.claim_label.rsplit_once('.').unwrap().0;
        super::expansion_tests::verify_expanded_project_function_source(
            source,
            &expanded,
            &expanded_project,
            &c,
            owner,
        )
        .unwrap_or_else(|error| {
            panic!(
                "{} site {} ({}) lost the checked entry borrow: {}",
                site.claim_label,
                site.source_index,
                site.tactic_name,
                error.message()
            )
        });
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn authority_owned_member_supplies_nested_release_count_bound() {
    let child_release = SOURCE
        .split("void release_one(struct child* obj)")
        .next()
        .unwrap();
    let source = format!(
        r#"{child_release}
void release_one(struct child* obj) {{
    consumes child_control(obj);
    consumes child_ref(obj);
    if old(count(child_ref(obj))) > 1 {{ produces child_control(obj); }}
    ensures count(child_ref(obj)) == old(count(child_ref(obj))) - 1;
}} by {{
    if obj->refs > 1 {{ step_until(function.exit); close(); }}
    else {{ step_until(function.exit); close(); }}
}}
"#
    );
    verify(&source).expect("the checked owned member supplies the nested helper's count bound");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 14s in the parallel gate"]
fn authority_nonterminal_detach_keeps_folded_named_output_once() {
    let fixture = crate::cli::parse_mdtest(
        std::path::Path::new("shared_heap_two_parent_caller.md"),
        include_str!("../../../mdtests/shared_heap_two_parent_caller.md"),
    )
    .unwrap();
    let source = fixture.click_source.as_deref().unwrap();
    let c = fixture
        .c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let project_for = |source: &str| {
        ClickProject::new(
            "nonterminal.click",
            [ClickModuleSource::new("nonterminal.click", source, [])],
        )
        .with_c_profile(CProjectProfile {
            target: None,
            runtime: None,
        })
    };
    crate::instrumentation::with_default_tactic_limits(|| {
        let project = project_for(source);
        verify_c_project(&project, &c).expect("the original named-output proof verifies");
        let sites = project_smart_tactic_source_sites(&project, &ProgramInputs::Bundle(c.to_vec()))
            .unwrap()
            .into_iter()
            .filter(|site| site.claim_label == "parent_detach.contract")
            .collect::<Vec<_>>();
        assert!(!sites.is_empty());
        for site in sites {
            let position = project_tactic_source_position(
                &project,
                &ProgramInputs::Bundle(c.to_vec()),
                &site.claim_label,
                site.source_index,
            )
            .unwrap();
            let expanded = expand_project_tactic_source_at(
                &project,
                &ProgramInputs::Bundle(c.to_vec()),
                position.line,
                position.column,
            )
            .unwrap();
            verify_c_project(&project_for(&expanded), &c).expect(
                "the named-output expansion preserves one survivor and one output instance",
            );
        }
        let duplicated_survivor = source.replace(
            "    owns child_ref(p->kid);\n    consumes child_ref(p->kid);",
            "    owns child_ref(p->kid);\n    consumes child_ref(p->kid);\n    produces child_ref(old(p->kid));",
        );
        assert_ne!(duplicated_survivor, source);
        assert!(
            verify_c_project(&project_for(&duplicated_survivor), &c).is_err(),
            "a checked output cannot create an extra surviving unit"
        );
    });
}

#[test]
fn mirrored_execution_bound_that_uses_legacy_normalization_refuses_expansion() {
    let source = r#"verifying "bound.c";
void bound(int32 value) {
    requires 2 <= value;
    ensures old(value) > 1;
} by {
    step_until(function.exit);
    have old(value) > 1 by {
        close() using { 2 <= old(value); }
    }
    close();
}
"#;
    let c = [("bound.c", "void bound(int32 value) {}")];
    crate::instrumentation::with_default_tactic_limits(|| {
        verify_c_sources(source, &c).expect("execution compares the same signed value");
        let error = expand_c_tactic_source_at(source, &c, 8, 9)
            .expect_err("the mirrored execution closure still uses compatibility normalization");
        assert!(
            error.message().contains("used legacy normalization"),
            "{error:?}"
        );
    });
}

#[test]
fn mirrored_strict_signed_bound_expands_to_checked_successor_rule() {
    let source = "theorem bound(value: int32) {\nrequires 2 <= value;\nensures value > 1 by {\nclose();\n}\n}\n";
    crate::instrumentation::with_default_tactic_limits(|| {
        verify_c_sources(source, &[])
            .expect("a mirrored strict bound follows from its successor bound");
        let expanded = expand_c_tactic_source_at(source, &[], 4, 1).unwrap();
        verify_c_sources(&expanded, &[]).expect("the mirrored successor certificate verifies");
    });
}

#[test]
fn strict_successor_bound_does_not_wrap_signed_maximum() {
    let source = "theorem bound(value: int32) {\nrequires 2147483647 <= value;\nensures value > 2147483647 by { close(); }\n}\n";
    crate::instrumentation::with_default_tactic_limits(|| {
        assert!(
            verify_c_sources(source, &[]).is_err(),
            "signed maximum has no successor"
        );
    });
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 8s in the parallel gate"]
fn authority_parent_entry_alias_expansion_preserves_later_resource_proof() {
    crate::instrumentation::with_default_tactic_limits(|| {
        let source = include_str!("../../../design/shared-heap-probes/shared_parent.click");
        let c = [(
            "shared_parent.c",
            include_str!("../../../design/shared-heap-probes/shared_parent.c"),
        )];
        let project_for = |source: &str| {
            ClickProject::new(
                "parent.click",
                [ClickModuleSource::new("parent.click", source, [])],
            )
            .with_c_profile(CProjectProfile {
                target: None,
                runtime: None,
            })
        };
        let project = project_for(source);
        verify_c_project(&project, &c).expect("the original parent lifecycle verifies");
        let line = source
            .lines()
            .enumerate()
            .skip_while(|(_, line)| !line.starts_with("void parent_detach("))
            .find(|(_, line)| line.trim() == "have old(p->kid) == entry_child;")
            .map(|(index, _)| index + 1)
            .expect("parent_detach states the entry alias before releasing the child");
        let expanded =
            expand_project_tactic_source_at(&project, &ProgramInputs::Bundle(c.to_vec()), line, 13)
                .unwrap();
        super::expansion_tests::verify_expanded_project_function_source(
            source,
            &expanded,
            &project_for(&expanded),
            &c,
            "parent_detach",
        )
        .expect("expanding the entry alias keeps later resource proofs equivalent");
    });
}
