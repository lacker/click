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
const SOURCE: &str = r#"authorized resource child_ref(obj: struct child*) {}

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
        execute();
        simp();
    } else {
        unfold(child_ref(obj));
        have 1 < obj->refs by {
            arithmetic() using { 1 <= obj->refs; obj->refs != 1; }
        }
        have obj->refs - 1 >= 1 by {
            apply(int32_above_one_predecessor_is_at_least_one(obj->refs)) using {
                1 < obj->refs;
            }
        }
        step();
        step();
        fold(child_control(obj));
        execute();
        simp();
    }
}


void release_one(struct child* obj) {
    requires 1 < obj->refs;
    owns child_control(obj);
    consumes child_ref(obj);
    ensures obj->payload == old(obj->payload);
} by {
    have obj->refs == count(child_ref(obj)) by { simp(); }
    have 1 < count(child_ref(obj)) by { simp(); }
    step(child_release(obj), {});
    have obj->payload == old(obj->payload) by { simp(); }
    step();
    simp();
}
"#;

fn verify(source: &str) -> Result<Vec<VerifiedCTheorem>, ClickError> {
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
    verify_c0_project(&project, &[("conditional_release.c", C)])
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
    verify_c0_project(&project, &c).expect("the original handoff proof verifies");
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
        let expanded_project = ClickProject::new(
            "handoff.click",
            [ClickModuleSource::new("handoff.click", expanded, [])],
        )
        .with_c_profile(CProjectProfile {
            target: None,
            runtime: None,
        });
        verify_c0_project(&expanded_project, &c).unwrap_or_else(|error| {
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
    if obj->refs > 1 {{ execute(); simp(); }}
    else {{ execute(); simp(); }}
}}
"#
    );
    verify(&source).expect("the checked owned member supplies the nested helper's count bound");
}

#[test]
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
        verify_c0_project(&project, &c).expect("the original named-output proof verifies");
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
            verify_c0_project(&project_for(&expanded), &c).expect(
                "the named-output expansion preserves one survivor and one output instance",
            );
        }
        let duplicated_survivor = source.replace(
            "    owns child_ref(p->kid);\n    consumes child_ref(p->kid);",
            "    owns child_ref(p->kid);\n    consumes child_ref(p->kid);\n    produces child_ref(old(p->kid));",
        );
        assert_ne!(duplicated_survivor, source);
        assert!(
            verify_c0_project(&project_for(&duplicated_survivor), &c).is_err(),
            "a checked output cannot create an extra surviving unit"
        );
    });
}

#[test]
fn mirrored_execution_bound_expands_to_checked_normalization() {
    let source = r#"verifying "bound.c";
void bound(int32 value) {
    requires 2 <= value;
    ensures old(value) > 1;
} by {
    execute();
    have old(value) > 1 by {
        simp() using { 2 <= old(value); }
    }
    simp();
}
"#;
    let c = [("bound.c", "void bound(int32 value) {}")];
    crate::instrumentation::with_default_tactic_limits(|| {
        verify_c0_sources(source, &c).expect("execution compares the same signed value");
        let expansion = expand_c0_tactic_source_at(source, &c, 8, 9)
            .expect("the mirrored execution closure expands");
        verify_c0_sources(&expansion, &c)
            .expect("the mirrored execution closure has a checked normalization");
    });
}

#[test]
fn mirrored_strict_signed_bound_expands_to_checked_successor_rule() {
    let source = "theorem bound(value: int32) {\nrequires 2 <= value;\nensures value > 1 by {\nsimp();\n}\n}\n";
    crate::instrumentation::with_default_tactic_limits(|| {
        verify_c0_sources(source, &[])
            .expect("a mirrored strict bound follows from its successor bound");
        let expanded = expand_c0_tactic_source_at(source, &[], 4, 1).unwrap();
        verify_c0_sources(&expanded, &[]).expect("the mirrored successor certificate verifies");
    });
}

#[test]
fn strict_successor_bound_does_not_wrap_signed_maximum() {
    let source = "theorem bound(value: int32) {\nrequires 2147483647 <= value;\nensures value > 2147483647 by { simp(); }\n}\n";
    crate::instrumentation::with_default_tactic_limits(|| {
        assert!(
            verify_c0_sources(source, &[]).is_err(),
            "signed maximum has no successor"
        );
    });
}

#[test]
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
        verify_c0_project(&project, &c).expect("the original parent lifecycle verifies");
        let line = source
            .lines()
            .position(|line| line.contains("have old(p->kid) == kid by simp;"))
            .unwrap()
            + 1;
        let expanded =
            expand_project_tactic_source_at(&project, &ProgramInputs::Bundle(c.to_vec()), line, 13)
                .unwrap();
        verify_c0_project(&project_for(&expanded), &c)
            .expect("expanding the entry alias keeps later resource proofs equivalent");
    });
}
