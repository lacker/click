use super::*;

fn project(source: &str) -> ClickProject {
    ClickProject::new(
        "wrapper.click",
        [ClickModuleSource::new("wrapper.click", source, [])],
    )
    .with_c_profile(CProjectProfile {
        target: None,
        runtime: None,
    })
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by authority_transfer_wrapper_batch_00"
)]
fn authority_transfer_wrapper_preserves_each_existing_child() {
    let source = r#"
        authorized abstract resource member(object: int32);
        authorized resource held(object: int32) { owns member(object); }
        verifying "wrapper.c";
        int32 package(int32 object) {
            consumes member(object);
            owns member(object);
            produces held(object) by {
                step_until(function.exit);
                fold(held(object));
            }
        }
        int32 unpack(int32 object) {
            consumes held(object);
            produces member(object) by {
                step_until(function.exit);
                unfold(held(object));
            }
        }
    "#;
    let c = "int32 package(int32 object) { return object; } int32 unpack(int32 object) { return object; }";
    verify_c_project(&project(source), &[("wrapper.c", c)])
        .expect("wrappers transfer existing child ownership in both directions");
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by authority_transfer_wrapper_batch_00"
)]
fn authority_transfer_wrapper_cannot_create_a_missing_child() {
    let source = r#"
        authorized abstract resource member(object: int32);
        authorized resource held(object: int32) { owns member(object); }
        verifying "wrapper.c";
        int32 package(int32 object) {
            produces held(object) by {
                step_until(function.exit);
                fold(held(object));
            }
        }
    "#;
    let error = verify_c_project(
        &project(source),
        &[(
            "wrapper.c",
            "int32 package(int32 object) { return object; }",
        )],
    )
    .expect_err("wrapping cannot synthesize its child");
    assert!(error.message().contains("member"), "{error:?}");
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by authority_transfer_wrapper_batch_00"
)]
fn authority_transfer_wrapper_cannot_bypass_member_birth_checks() {
    let source = r#"
        authorized resource member(p: int32*) { owns p[0..1]; }
        authorized resource held(p: int32*) { owns member(p); }
        verifying "wrapper.c";
        int32 value() {
            ensures result == 7;
        } by {
            step();
            fold(authority(member(&x)));
            fold(held(&x));
            step_until(function.exit);
        }
    "#;
    let error = verify_c_project(
        &project(source),
        &[("wrapper.c", "int32 value(void) { int32 x = 7; return x; }")],
    )
    .expect_err("authority and private memory cannot supply a wrapped member");
    assert!(error.message().contains("member"), "{error:?}");
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by authority_transfer_wrapper_batch_00"
)]
fn authority_transfer_wrapper_preserves_a_tracked_member() {
    let source = r#"
        authorized resource member(p: int32*) { owns p[0..1]; }
        authorized resource held(p: int32*) { owns member(p); }
        verifying "wrapper.c";
        int32 run() {
            ensures result == 0 or result == 1;
        } by {
            step();
            step();
            branch { true => { step_until(function.exit); close(); } false => {} }
            fold(authority(member(p)));
            fold(member(p));
            fold(held(p));
            unfold(held(p));
            have count(member(p)) == 1 by { close(); }
            unfold(member(p));
            unfold(authority(member(p)));
            step_until(function.exit);
            close();
        }
    "#;
    let c = "int32 run(void) { int32* p = malloc(4); if (p == 0) return 0; free(p); return 1; }";
    verify_c_project(&project(source), &[("wrapper.c", c)])
        .expect("packaging and unpackaging preserve the tracked member and its population");
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by authority_transfer_wrapper_batch_01"
)]
fn authority_member_wrapper_requires_population_cleanup_before_free() {
    let source = r#"
        authorized resource member(p: int32*) { owns p[0..1]; }
        authorized resource held(p: int32*) { owns member(p); }
        verifying "wrapper.c";
        int32 run() {
            ensures result == 0 or result == 1;
        } by {
            step();
            step();
            branch { true => { step_until(function.exit); close(); } false => {} }
            fold(authority(member(p)));
            fold(member(p));
            fold(authority(held(p)));
            fold(held(p));
            have count(held(p)) == 1 by close();
            have count(member(p)) == 1 by close();
            step_until(function.exit);
        }
    "#;
    let c = "int32 run(void) { int32* p = malloc(4); if (p == 0) return 0; free(p); return 1; }";
    let error = verify_c_project(&project(source), &[("wrapper.c", c)]).expect_err(
        "a registered outer member must be consumed and both authorities retired before free",
    );
    assert!(
        error
            .message()
            .contains("an authority registered at this anchor is still outstanding"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by authority_transfer_wrapper_batch_01"
)]
fn authority_transfer_wrapper_cannot_rewrite_its_own_tracked_family_at_outcome() {
    let source = r#"
        authorized resource member(p: int32*) { owns p[0..1]; }
        authorized resource held(p: int32*) { owns member(p); }
        verifying "wrapper.c";
        int32* run() {
            ensures result == 0 or result != 0;
        } by {
            step();
            step();
            branch { true => { step_until(function.exit); close(); } false => {} }
            fold(authority(member(p)));
            fold(member(p));
            fold(authority(held(p)));
            step_until(function.exit);
            fold(held(result));
            close();
        }
    "#;
    let c = "int32* run(void) { int32* p = malloc(4); if (p == 0) return 0; return p; }";
    let error = verify_c_project(&project(source), &[("wrapper.c", c)])
        .expect_err("a registered family cannot become an ordinary wrapper after return");
    assert!(
        error
            .message()
            .contains("resource fold after function outcome is unavailable"),
        "{error:?}"
    );
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by authority_transfer_wrapper_batch_01"
)]
fn authority_transfer_wrapper_preserves_adjacent_mixed_width_memory_frame() {
    verify_c_project(
        &project(MEMORY_FRAME_SOURCE),
        &[("wrapper.c", MEMORY_FRAME_C)],
    )
    .expect("folding and unfolding preserve the exact unrelated memory frame");
}

const MEMORY_FRAME_SOURCE: &str = r#"
        authorized abstract resource member(object: int32);
        authorized resource held(object: int32) { owns member(object); }
        verifying "wrapper.c";
        int32 package(int32 object, struct Frame* frame) {
            consumes member(object);
            owns member(object);
            owns frame->wide;
            owns frame->narrow;
            produces held(object) by {
                step_until(function.exit);
                fold(held(object));
            }
        }
        int32 unpack(int32 object, struct Frame* frame) {
            consumes held(object);
            owns frame->wide;
            owns frame->narrow;
            produces member(object) by {
                step_until(function.exit);
                unfold(held(object));
            }
        }
    "#;
const MEMORY_FRAME_C: &str = "struct Frame { int64 wide; int32 narrow; }; int32 package(int32 object, struct Frame* frame) { return object; } int32 unpack(int32 object, struct Frame* frame) { return object; }";

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn authority_transfer_wrapper_memory_frame_expands_and_rechecks_retained_proof() {
    let sources = [("wrapper.c", MEMORY_FRAME_C)];
    let original = project(MEMORY_FRAME_SOURCE);
    let (session, verified) = ProgramVerificationSession::new_project(&original, &sources)
        .expect("retain the unchanged wrapper proof");
    let expanded = ["package.produces_0", "unpack.produces_0"].map(|label| {
        expand_checked_function_claim(MEMORY_FRAME_SOURCE, &verified, label)
            .expect("the checked wrapper exchange expands")
    });
    let position = crate::surface::expansion::position_at_offset(
        MEMORY_FRAME_SOURCE,
        MEMORY_FRAME_SOURCE.rfind("unfold(held(object));").unwrap(),
    );
    session
        .verify_at_project(MEMORY_FRAME_SOURCE, position.line, position.column)
        .expect("the retained exchange still checks");
    drop(session);
    for expanded in expanded {
        verify_c_project(&project(&expanded), &sources)
            .expect("the expanded exchange preserves both borrowed fields");
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn authority_transfer_wrapper_memory_frame_cannot_supply_missing_or_duplicate_children() {
    for source in [
        MEMORY_FRAME_SOURCE.replace("consumes held(object);", ""),
        MEMORY_FRAME_SOURCE.replace(
            "produces member(object) by {",
            "produces member(object); produces member(object) by {",
        ),
        MEMORY_FRAME_SOURCE.replace(
            "unfold(held(object));",
            "unfold(held(object)); unfold(held(object));",
        ),
    ] {
        verify_c_project(&project(&source), &[("wrapper.c", MEMORY_FRAME_C)])
            .expect_err("borrowed fields cannot manufacture wrapper or child authority");
    }
}

#[test]
#[cfg_attr(
    feature = "fast-gate",
    ignore = "covered by authority_transfer_wrapper_batch_01"
)]
fn separately_proved_resource_clauses_cannot_duplicate_a_borrowed_unit() {
    let source = r#"
        abstract resource Permit(object: int32);
        verifying "wrapper.c";
        int32 duplicate(int32 object) {
            owns Permit(object);
            produces Permit(object) by { step_until(function.exit); close(); }
        }
    "#;
    let error = verify_c_project(
        &project(source),
        &[(
            "wrapper.c",
            "int32 duplicate(int32 object) { return object; }",
        )],
    )
    .expect_err("the last separately proved resource clause still owes its complete joint prefix");
    assert!(
        error.proof_refusal() == Some(crate::surface::ProofRefusal::IncompleteProof)
            || error.message().contains("held instance"),
        "{error}"
    );
}

#[cfg(feature = "fast-gate")]
test_batches! {
    file: "authority_transfer_wrapper_tests.rs",
    marker: "authority_transfer_wrapper_batch_",
    authority_transfer_wrapper_batch_00: [
        authority_transfer_wrapper_preserves_each_existing_child,
        authority_transfer_wrapper_cannot_create_a_missing_child,
        authority_transfer_wrapper_cannot_bypass_member_birth_checks,
        authority_transfer_wrapper_preserves_a_tracked_member,
    ],
    authority_transfer_wrapper_batch_01: [
        authority_member_wrapper_requires_population_cleanup_before_free,
        authority_transfer_wrapper_cannot_rewrite_its_own_tracked_family_at_outcome,
        authority_transfer_wrapper_preserves_adjacent_mixed_width_memory_frame,
        separately_proved_resource_clauses_cannot_duplicate_a_borrowed_unit,
    ],
}
