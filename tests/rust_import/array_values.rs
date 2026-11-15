use super::*;

const COPY_AFTER_CALL: &str = include_str!("../../design/charon-trial/copy-after-call/copy.click");

fn copy_after_call_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/copy-after-call");
    fs::write(p.root.join("borrow.click"), COPY_AFTER_CALL).unwrap();
    p
}

#[test]
fn charon_array_copy_after_checked_call_preserves_an_independent_state() {
    let p = copy_after_call_project();
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(COPY_AFTER_CALL, &prepared).unwrap();
    for (before, after) in [
        ("ensures result == 5u32;", "ensures result == 1u32;"),
        ("ensures result == 5u32;", "ensures result == 9u32;"),
        // `replace_first` writes `words[0]`, so owning `words[1..4]` is
        // insufficient. (Owning `words[0..3]` is enough: the caller's copy
        // reads its own rejoined `words[0..4]` after the call.)
        ("owns words[0..4];", "owns words[1..4];"),
        ("owns words[0..4];", "views words[0..4];"),
    ] {
        let invalid = COPY_AFTER_CALL.replace(before, after);
        assert_ne!(invalid, COPY_AFTER_CALL);
        let error = ProgramVerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("false value or insufficient authority must fail");
        assert!(!format!("{error:?}").contains("budget exhausted"));
    }
}

#[cfg(not(feature = "fast-gate"))]
#[test]
#[ignore = "nightly: 1.9s in the parallel gate"]
fn charon_array_copy_after_checked_call_tools_recheck_expanded_certificates() {
    let p = copy_after_call_project();
    for command in ["profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I15_copy_after_call_I13_replace_first.contract",
        "__rust_q_I15_copy_after_call_I15_copy_after_call.ensures_0",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(&p, &["verify"]);
}

const COPY_SOURCE_AFTER_CALL: &str =
    include_str!("../../design/charon-trial/copy-source-after-call/copy.click");

fn copy_source_after_call_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/copy-source-after-call");
    fs::write(p.root.join("borrow.click"), COPY_SOURCE_AFTER_CALL).unwrap();
    p
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn charon_array_copy_preserves_symbolic_source_across_by_value_call() {
    let p = copy_source_after_call_project();
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(COPY_SOURCE_AFTER_CALL, &prepared).unwrap();
    for (before, after) in [
        (
            "ensures result == value;",
            "ensures result == value + 1u32;",
        ),
        (
            "ensures target.0[0] == old(other.0[0]);",
            "ensures target.0[0] == old(other.0[1]);",
        ),
        ("owns words.0[0..4];", "owns words.0[1..4];"),
    ] {
        let invalid = COPY_SOURCE_AFTER_CALL.replace(before, after);
        assert_ne!(invalid, COPY_SOURCE_AFTER_CALL);
        let error = ProgramVerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("false values or missing write authority must fail");
        assert!(!format!("{error:?}").contains("budget exhausted"));
    }
}

#[cfg(not(feature = "fast-gate"))]
#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn charon_array_copy_symbolic_source_tools_recheck_expanded_certificates() {
    let p = copy_source_after_call_project();
    for command in ["profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I22_copy_source_after_call_I3_set.contract",
        "__rust_q_I22_copy_source_after_call_I7_consume.contract",
        "__rust_q_I22_copy_source_after_call_I6_caller.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(&p, &["verify"]);
}

const SOURCE: &str = include_str!("../../design/charon-trial/array-values/bounds.rs");
const SIDECAR: &str = include_str!("../../design/charon-trial/array-values/bounds.click");
fn project() -> Project {
    let p = Project::from_fixture("design/charon-trial/array-values");
    fs::write(p.root.join("borrow.click"), SIDECAR).unwrap();
    p
}

#[test]
#[ignore = "nightly: 2.3s in the parallel gate"]
fn charon_array_reference_assignments_check_values_and_independent_states() {
    let p = project();
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    // The full original check covers the unchanged bodies. Each refusal
    // still checks the complete changed function, including every claim.
    for (owners, before, after) in [
        (
            &["swap"][..],
            "ensures result == 5u32;",
            "ensures result == 3u32;",
        ),
        (
            &["signed"][..],
            "ensures result == -3;",
            "ensures result == 7;",
        ),
        (
            &[
                "fill_small",
                "copy_small",
                "fill_medium",
                "copy_medium",
                "fill_million",
                "copy_million",
            ][..],
            "ensures result == 7u32;",
            "ensures result == 9u32;",
        ),
        (
            &["empty"][..],
            "ensures result == 0u64;",
            "ensures result == 1u64;",
        ),
    ] {
        let invalid = SIDECAR.replace(before, after);
        assert_ne!(invalid, SIDECAR);
        assert!(
            owners
                .iter()
                .any(|owner| verify_rust_function(&invalid, &prepared, owner).is_err())
        );
    }
}

#[cfg(not(feature = "fast-gate"))]
#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn charon_array_reference_assignments_tools_recheck_expanded_certificates() {
    let p = project();
    for command in ["profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "swap.ensures_0",
        "self_copy.ensures_0",
        "copy_million.ensures_0",
        "fill_million.ensures_0",
        "empty.ensures_0",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(&p, &["verify"]);
}

#[cfg(not(feature = "fast-gate"))]
#[test]
#[ignore = "nightly: 20 s, over the gate's per-test budget (2026-10-06)"]
fn charon_array_values_unchanged_fixture_verifies_external_states() {
    let p = Project::from_fixture("design/charon-trial/array-values");
    let source = include_str!("../../design/charon-trial/array-values/arrays.rs");
    let sidecar = include_str!("../../design/charon-trial/array-values/arrays.click");
    assert_eq!(
        source,
        include_str!("../../examples/rust-array-values/arrays.rs")
    );
    assert_eq!(
        sidecar,
        include_str!("../../examples/rust-array-values/arrays.click")
    );
    fs::write(p.root.join("borrow.click"), sidecar.as_bytes()).unwrap();
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    for owner in ["copy_reference", "copy_into", "repeat_call"] {
        verify_rust_function(sidecar, &prepared, owner).unwrap();
    }
    for (owner, before, after) in [
        (
            "copy_reference",
            "ensures result == words[0];",
            "ensures result == words[1];",
        ),
        (
            "copy_into",
            "ensures target[1] == old(source[1]);",
            "ensures target[1] == old(source[0]);",
        ),
        (
            "repeat_call",
            "ensures *value == 5u32;",
            "ensures *value == 4u32;",
        ),
        ("copy_into", "views source[0..2];", "views source[0..1];"),
        ("copy_into", "owns target[0..2];", "views target[0..2];"),
        ("copy_into", "owns target[0..2];", "owns target[0..1];"),
    ] {
        let invalid = sidecar.replace(before, after);
        assert_ne!(invalid, sidecar);
        let error = verify_rust_function(&invalid, &prepared, owner)
            .expect_err("the changed function must reject the mutation");
        assert_eq!(
            error.kind(),
            click::surface::ClickErrorKind::Proof,
            "{before}: {}",
            error.message()
        );
        assert!(
            !error.message().contains("budget exhausted"),
            "{before}: {}",
            error.message()
        );
    }
    for command in ["profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "copy_reference.ensures_0",
        "copy_into.contract",
        "repeat_call.contract",
        "zero_repeat_call.contract",
        "argument_order.contract",
        "assignment_order.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_array_reference_assignments_live_refresh_and_borrow_rejections() {
    let p = project();
    p.refresh().unwrap();
    ProgramVerificationSession::new_program_prepared(SIDECAR, p.prepared().unwrap()).unwrap();
    for (source, diagnostic) in [
        ("pub fn bad(x: &[u32;2]) { *x = [1,2]; }", "E0594"),
        (
            "pub fn bad(x: &mut [u32;2]) { let y=&mut *x; *x=[1,2]; y[0]=3; }",
            "E0506",
        ),
        (
            "pub fn bad(x: [u32;2])->u32 { x[0] }",
            "by-value Rust arrays as parameters",
        ),
        (
            "pub fn bad()->[u32;2] { [1,2] }",
            "reference/aggregate returns",
        ),
    ] {
        fs::remove_file(p.artifact("bounds.rs")).unwrap();
        fs::write(p.root.join("bounds.rs"), source).unwrap();
        let error = p.refresh().unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.artifact("bounds.rs").exists());
        fs::write(p.root.join("bounds.rs"), SOURCE).unwrap();
        p.refresh().unwrap();
    }
}

fn external_project() -> Project {
    let p = Project::from_fixture("design/charon-trial/array-values");
    fs::write(
        p.root.join("borrow.click"),
        include_bytes!("../../design/charon-trial/array-values/external.click").as_slice(),
    )
    .unwrap();
    p
}

#[cfg(not(feature = "fast-gate"))]
#[test]
#[ignore = "nightly: 15 s, over the gate's per-test budget (2026-10-06)"]
fn charon_external_array_copies_and_fills_verify_and_reject_false_bytes() {
    let p = external_project();
    let sidecar = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    // The full original check covers the unchanged bodies. Each refusal
    // still checks the complete changed function, including every claim.
    for (owners, before, after) in [
        (
            &[
                "copy_small",
                "copy_medium",
                "copy_million",
                "independent",
                "bytes",
            ][..],
            "old(source[0])",
            "old(source[1])",
        ),
        (
            &["fill_million"][..],
            "target[999999] == value",
            "target[999999] == value + 1u32",
        ),
        (
            &["independent"][..],
            "result == old(source[0])",
            "result == source[0]",
        ),
    ] {
        let invalid = sidecar.replace(before, after);
        assert_ne!(invalid, sidecar);
        assert!(
            owners
                .iter()
                .any(|owner| verify_rust_function(&invalid, &prepared, owner).is_err())
        );
    }
    for command in ["profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "copy_million.contract",
        "fill_million.contract",
        "independent.contract",
        "empty.ensures_0",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
    }
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_external_array_copies_live_refresh() {
    let p = external_project();
    p.refresh().unwrap();
    ProgramVerificationSession::new_program_prepared(
        &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
        p.prepared().unwrap(),
    )
    .unwrap();
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_whole_array_copy_live_refresh_checks_full_authority() {
    let p = Project::new(include_str!("../../examples/rust-array-values/arrays.rs"));
    let sidecar = include_str!("../../examples/rust-array-values/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    p.refresh().unwrap();
    let prepared = p.prepared().unwrap();
    ProgramVerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for (before, after) in [
        ("views source[0..2];", "views source[0..1];"),
        ("owns target[0..2];", "views target[0..2];"),
        ("owns target[0..2];", "owns target[0..1];"),
    ] {
        let invalid = sidecar.replace(before, after);
        assert_ne!(invalid, sidecar);
        assert!(ProgramVerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
