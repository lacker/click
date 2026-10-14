use super::*;

fn project(click_source: &str) -> ClickProject {
    ClickProject::new(
        "private_body.click",
        [ClickModuleSource::new(
            "private_body.click",
            click_source,
            [],
        )],
    )
    .with_c_profile(CProjectProfile {
        target: None,
        runtime: None,
    })
}

#[test]
fn authority_control_extra_payload_does_not_replace_counter_ownership() {
    let c_source = "struct object { int32 refs; int32 payload; }; void keep(struct object* obj) {}";
    let click_source = r#"
        authorized resource reference(obj: struct object*) {}
        resource control(obj: struct object*) {
            owns obj->payload;
            owns authority(reference(obj));
            fact obj->refs == count(reference(obj));
        }
        verifying "private_body.c";
        void keep(struct object* obj) {
            owns control(obj);
        } by { execute(); simp(); }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("payload ownership does not authenticate the counter load");
    assert!(
        error
            .message()
            .contains("without a covering contained memory resource"),
        "{error:?}"
    );
}

#[test]
fn authority_member_local_body_uses_scalar_allocation_ownership() {
    let c_source = r#"
        int32 value(void) {
            int32 x = 7;
            return x;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {
            owns p[0..1];
        }
        verifying "private_body.c";

        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            fold(reference(&x));
            have count(reference(&x)) == 1 by { simp(); }
            unfold(reference(&x));
            have count(reference(&x)) == 0 by { simp(); }
            unfold(authority(reference(&x)));
            execute();
            simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("scalar allocation supplies the body, and unfold restores it before local access");
}

#[test]
fn authority_member_private_heap_body_round_trip() {
    let c_source = r#"
        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return 0;
            free(p);
            return 1;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {
            owns p[0..1];
        }
        verifying "private_body.c";

        int32 value() {
            ensures result == 0 or result == 1;
        } by {
            step();
            step();
            branch then {
                execute();
                simp();
            } else {}
            fold(authority(reference(p)));
            fold(reference(p));
            open(reference(p)) {
                have count(reference(p)) == 1 by { simp(); }
            }
            unfold(reference(p));
            unfold(authority(reference(p)));
            execute();
            simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("fresh heap ownership can back a member and its private body");
}

#[test]
fn authority_helper_returns_member_with_private_memory_body() {
    let c_source = r#"
        int32 helper(int32* p) { *p = 7; return 7; }
        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return 0;
            int32 result = helper(p);
            free(p);
            return result;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {
            owns p[0..1];
        }
        verifying "private_body.c";

        int32 helper(int32* p) {
            owns authority(reference(p));
            owns reference(p);
            ensures result == 7;
        } by {
            open(reference(p)) { step(); }
            execute();
            simp();
        }

        int32 value() {
            ensures result == 0 or result == 7;
        } by {
            step();
            step();
            branch then { execute(); simp(); } else {}
            fold(authority(reference(p)));
            fold(reference(p));
            step();
            step();
            unfold(reference(p));
            unfold(authority(reference(p)));
            execute();
            simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("a checked helper returns the same private-body member");
}

#[test]
fn authority_helpers_create_and_consume_member_with_private_memory_body() {
    let c_source = r#"
        int32 acquire(int32* p) { p[0] = 7; p[1] = 9; return 7; }
        int32 release(int32* p) { p[0] = 7; p[1] = 9; return 7; }
        int32 value(void) {
            int32* p = malloc(8);
            if (p == 0) return 0;
            int32 result = acquire(p);
            release(p);
            free(p);
            return result;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {
            owns p[0..1];
            owns p[1..2];
        }
        verifying "private_body.c";

        int32 acquire(int32* p) {
            owns authority(reference(p));
            consumes p[0..1];
            consumes p[1..2];
            produces reference(p);
            ensures result == 7;
        } by {
            step();
            step();
            fold(reference(p));
            execute();
            simp();
        }

        int32 release(int32* p) {
            owns authority(reference(p));
            consumes reference(p);
            produces p[0..1];
            produces p[1..2];
            ensures result == 7;
        } by {
            unfold(reference(p));
            step();
            step();
            execute();
            simp();
        }

        int32 value() {
            ensures result == 0 or result == 7;
        } by {
            step();
            step();
            branch then { execute(); simp(); } else {}
            fold(authority(reference(p)));
            step();
            step();
            have count(reference(p)) == 1 by { simp(); }
            step();
            have count(reference(p)) == 0 by { simp(); }
            unfold(authority(reference(p)));
            execute();
            simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("verified helpers move the private body with one member birth and death");
}

#[test]
fn authority_creating_helper_cannot_outlive_caller_scalar_storage() {
    let c_source = r#"
        int32 acquire(int32* p) { *p = 7; return 7; }
        int32 value(void) {
            int32 x = 7;
            return acquire(&x);
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) { owns p[0..1]; }
        verifying "private_body.c";
        int32 acquire(int32* p) {
            owns authority(reference(p));
            consumes p[0..1];
            produces reference(p);
            ensures result == 7;
        } by {
            step();
            fold(reference(p));
            execute();
            simp();
        }
        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(reference(&x)));
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("the live population authority prevents retiring its backing scalar");
    assert!(
        error.message().contains("OutstandingAuthority"),
        "{error:?}"
    );
}

#[test]
fn authority_consuming_helper_cannot_return_the_wrong_private_body() {
    let c_source = r#"int32 release(int32* p) { return 7; }"#;
    let click_source = r#"
        authorized resource reference(p: int32*) { owns p[0..1]; }
        verifying "private_body.c";
        int32 release(int32* p) {
            owns authority(reference(p));
            consumes reference(p);
            produces p[1..2];
            ensures result == 7;
        } by {
            unfold(reference(p));
            execute();
            simp();
        }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("the returned private body must match the member definition");
    assert!(
        error
            .message()
            .contains("missing resource fact `owns p[1]`"),
        "{error:?}"
    );
    assert!(
        error.message().contains("Requires produces owns p[1]"),
        "{error:?}"
    );
    assert!(
        !error.message().contains("Requires produces owns p[1..2]"),
        "{error:?}"
    );
}

#[test]
fn authority_member_private_heap_body_cannot_back_two_births() {
    let c_source = r#"
        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return 0;
            free(p);
            return 1;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {
            owns p[0..1];
        }
        verifying "private_body.c";

        int32 value() {
            ensures result == 0 or result == 1;
        } by {
            step();
            step();
            branch then { execute(); simp(); } else {}
            fold(authority(reference(p)));
            fold(reference(p));
            fold(reference(p));
        }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("one exclusive private memory body cannot create two members");
    assert!(
        error.message().contains("Requires the private body"),
        "{error:?}"
    );
}

#[test]
fn authority_malloc_statement_evidence_starts_at_running_state() {
    let c_source =
        "int32 value(void) { int32* p; p = malloc(4); if (p == 0) return 0; free(p); return 0; }";
    let click_source = r#"
        verifying "private_body.c";
        int32 value() {
            ensures result == 0;
        } by {
            step();
            step();
            execute();
            simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("malloc statement evidence must start at the current proof state");
}

#[test]
fn authority_control_wrapper_tracks_memory_and_member_count_through_open_scopes() {
    let c_source = r#"
        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return -1;
            p[0] = 0;
            p[0] = 1;
            p[0] = 0;
            int32 result = p[0];
            free(p);
            return result;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        resource control(p: int32*) {
            owns p[0..1];
            owns authority(reference(p));
            fact p[0] == count(reference(p));
        }
        verifying "private_body.c";
        int32 value() { ensures result == -1 or result == 0; } by {
            step(); step();
            branch then { execute(); simp(); } else {}
            step();
            fold(authority(reference(p)));
            fold(control(p));
            open(control(p)) {
                fold(reference(p));
                step();
            }
            open(control(p)) {
                unfold(reference(p));
                step();
            }
            unfold(control(p));
            unfold(authority(reference(p)));
            execute(); simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("control owns the counter and authority through both count changes");
}

#[test]
fn authority_control_wrapper_rejects_a_false_close_invariant() {
    let c_source = r#"
        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return -1;
            p[0] = 0;
            p[0] = 1;
            p[0] = 0;
            int32 result = p[0];
            free(p);
            return result;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        resource control(p: int32*) {
            owns p[0..1];
            owns authority(reference(p));
            fact p[0] == count(reference(p));
        }
        verifying "private_body.c";
        int32 value() { ensures result == -1 or result == 0; } by {
            step(); step();
            branch then { execute(); simp(); } else {}
            step();
            fold(authority(reference(p)));
            fold(control(p));
            open(control(p)) {
                step();
            }
        }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("changing counter memory without a member birth violates control's fact");
    assert!(
        error.message().contains("p[0] == count(reference(p))"),
        "{error:?}"
    );
}

#[test]
fn authority_control_wrapper_requires_its_contained_authority() {
    let c_source = r#"
        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return -1;
            p[0] = 0;
            int32 result = p[0];
            free(p);
            return result;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        resource control(p: int32*) {
            owns p[0..1];
            owns authority(reference(p));
            fact p[0] == count(reference(p));
        }
        verifying "private_body.c";
        int32 value() { ensures result == -1 or result == 0; } by {
            step(); step();
            branch then { execute(); simp(); } else {}
            step();
            fold(control(p));
        }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("counter memory alone cannot create a population authority");
    assert!(error.message().contains("authority"), "{error:?}");
}

#[test]
fn authority_control_wrapper_requires_its_counter_memory() {
    let c_source = r#"
        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return -1;
            p[0] = 0;
            p[0] = 1;
            int32 result = p[0];
            free(p);
            return result;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) { owns p[0..1]; }
        resource control(p: int32*) {
            owns p[0..1];
            owns authority(reference(p));
            fact p[0] == count(reference(p));
        }
        verifying "private_body.c";
        int32 value() { ensures result == -1 or result == 1; } by {
            step(); step();
            branch then { execute(); simp(); } else {}
            step();
            fold(authority(reference(p)));
            step();
            fold(reference(p));
            fold(control(p));
        }
    "#;
    let error = verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect_err("the member's private body cannot also be control's counter memory");
    assert!(
        error.message().contains("authority control body"),
        "{error:?}"
    );
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn authority_control_survives_balanced_helper_calls() {
    let c_source = r#"
        void retain(int32* p) { p[0] = p[0] + 1; }
        void release(int32* p) { p[0] = p[0] - 1; }

        int32 value(void) {
            int32* p = malloc(4);
            if (p == 0) return -1;
            p[0] = 0;
            retain(p);
            release(p);
            int32 result = p[0];
            free(p);
            return result;
        }
    "#;
    let click_source = r#"
        authorized resource reference(p: int32*) {}
        resource control(p: int32*) {
            owns p[0..1];
            owns authority(reference(p));
            fact p[0] == count(reference(p));
        }
        verifying "private_body.c";
        void retain(int32* p) {
            owns control(p);
            requires p[0] < 2147483647;
            produces reference(p);
        } by {
            open(control(p)) {
                step();
                fold(reference(p));
            }
            execute(); simp();
        }
        void release(int32* p) {
            owns control(p);
            consumes reference(p);
            requires p[0] > 0;
        } by {
            open(control(p)) {
                unfold(reference(p));
                step();
            }
            execute(); simp();
        }
        int32 value() { ensures result == -1 or result == 0; } by {
            step(); step();
            branch then { execute(); simp(); } else {}
            step();
            fold(authority(reference(p)));
            fold(control(p));
            step();
            open(control(p)) {
                have count(reference(p)) == 1 by { simp(); }
                have p[0] == 1 by { simp(); }
            }
            step();
            unfold(control(p));
            unfold(authority(reference(p)));
            execute(); simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("ordinary control returns through retaining and releasing helpers");
    let expanded = expand_project_claim_source_by_label(
        &project(click_source),
        &ProgramInputs::Bundle([("private_body.c", c_source)].to_vec()),
        "value.contract",
    )
    .expect("the caller expands with checked unselected helper contracts");
    verify_c0_project(&project(&expanded), &[("private_body.c", c_source)])
        .expect("the expanded caller proof checks beside both helpers");
}

#[test]
fn authority_final_release_helper_retires_population_and_allocation() {
    let c_source = r#"
        struct object { int32 refs; };
        void release_final(struct object* obj) {
            obj->refs = 0;
            free(obj);
        }
        int32 value(void) {
            struct object* obj = malloc(sizeof(struct object));
            if (obj == 0) return -1;
            obj->refs = 1;
            release_final(obj);
            return 0;
        }
    "#;
    let click_source = r#"
        authorized resource reference(obj: struct object*) {}
        resource control(obj: struct object*) {
            owns allocation(obj, sizeof(struct object));
            owns *obj;
            owns authority(reference(obj));
            fact obj->refs == count(reference(obj));
        }
        verifying "private_body.c";

        void release_final(struct object* obj) {
            requires obj->refs == 1;
            consumes control(obj);
            consumes reference(obj);
        } by {
            unfold(control(obj));
            unfold(reference(obj));
            unfold(authority(reference(obj)));
            step();
            execute(); simp();
        }

        int32 value() { ensures result == -1 or result == 0; } by {
            step(); step();
            branch then { execute(); simp(); } else {}
            step();
            fold(authority(reference(obj)));
            fold(reference(obj));
            fold(control(obj));
            step();
            execute(); simp();
        }
    "#;
    verify_c0_project(&project(click_source), &[("private_body.c", c_source)])
        .expect("final release retires the last member, authority, and allocation through a call");

    let bad_c_source = c_source.replace("            free(obj);", "");
    let error = verify_c0_project(&project(click_source), &[("private_body.c", &bad_c_source)])
        .expect_err("a helper that omits free cannot consume the allocation");
    assert!(
        error
            .message()
            .contains("live allocation obligation was neither returned nor freed"),
        "{error:?}"
    );

    let bad_contract = click_source.replace("requires obj->refs == 1;", "requires obj->refs == 2;");
    let error = verify_c0_project(&project(&bad_contract), &[("private_body.c", c_source)])
        .expect_err("one consumed member cannot retire an authority with count two");
    assert!(
        error
            .message()
            .contains("Requires count(reference(...)) == 0"),
        "{error:?}"
    );
}
