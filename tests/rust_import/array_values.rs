use super::*;

const COPY_AFTER_CALL: &str = include_str!("../../design/charon-trial/copy-after-call/copy.click");

fn copy_after_call_project() -> Project {
    let p = Project::new("");
    for (name, bytes) in [
        (
            "copy.rs",
            include_bytes!("../../design/charon-trial/copy-after-call/copy.rs").as_slice(),
        ),
        ("borrow.click", COPY_AFTER_CALL.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../../design/charon-trial/copy-after-call/copy.click.import.json")
                .as_slice(),
        ),
        (
            "copy.ullbc",
            include_bytes!("../../design/charon-trial/copy-after-call/copy.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../../design/charon-trial/copy-after-call/copy.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
fn charon_array_copy_after_checked_call_preserves_an_independent_snapshot() {
    let p = copy_after_call_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(COPY_AFTER_CALL, &prepared).unwrap();
    for (before, after) in [
        ("ensures result == 5u32;", "ensures result == 1u32;"),
        ("ensures result == 5u32;", "ensures result == 9u32;"),
        ("owns words[0..4];", "owns words[0..3];"),
        ("owns words[0..4];", "views words[0..4];"),
    ] {
        let invalid = COPY_AFTER_CALL.replace(before, after);
        assert_ne!(invalid, COPY_AFTER_CALL);
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("false value or insufficient authority must fail");
        assert!(!format!("{error:?}").contains("budget exhausted"));
    }
}

#[test]
#[ignore = "nightly: 1.9s in the parallel gate"]
fn charon_array_copy_after_checked_call_tools_recheck_expanded_certificates() {
    let p = copy_after_call_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I15_copy_after_call_I13_replace_first.contract",
        "__rust_q_I15_copy_after_call_I15_copy_after_call.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

const COPY_SOURCE_AFTER_CALL: &str =
    include_str!("../../design/charon-trial/copy-source-after-call/copy.click");

fn copy_source_after_call_project() -> Project {
    let p = Project::new("");
    for (name, bytes) in [
        (
            "copy.rs",
            include_bytes!("../../design/charon-trial/copy-source-after-call/copy.rs").as_slice(),
        ),
        ("borrow.click", COPY_SOURCE_AFTER_CALL.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!(
                "../../design/charon-trial/copy-source-after-call/copy.click.import.json"
            )
            .as_slice(),
        ),
        (
            "copy.ullbc",
            include_bytes!("../../design/charon-trial/copy-source-after-call/copy.ullbc")
                .as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!(
                "../../design/charon-trial/copy-source-after-call/copy.click.import.json.lock"
            )
            .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn charon_array_copy_preserves_symbolic_source_across_by_value_call() {
    let p = copy_source_after_call_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(COPY_SOURCE_AFTER_CALL, &prepared).unwrap();
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
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .expect("false values or missing write authority must fail");
        assert!(!format!("{error:?}").contains("budget exhausted"));
    }
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn charon_array_copy_symbolic_source_tools_recheck_expanded_certificates() {
    let p = copy_source_after_call_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "__rust_q_I22_copy_source_after_call_I3_set.contract",
        "__rust_q_I22_copy_source_after_call_I7_consume.contract",
        "__rust_q_I22_copy_source_after_call_I6_caller.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

const SOURCE: &str = include_str!("../../design/charon-trial/array-values/bounds.rs");
const SIDECAR: &str = include_str!("../../design/charon-trial/array-values/bounds.click");
fn project() -> Project {
    let p = Project::new("");
    for (name, bytes) in [
        ("bounds.rs", SOURCE.as_bytes()),
        ("borrow.click", SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../../design/charon-trial/array-values/bounds.click.import.json")
                .as_slice(),
        ),
        (
            "bounds.ullbc",
            include_bytes!("../../design/charon-trial/array-values/bounds.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../../design/charon-trial/array-values/bounds.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
#[ignore = "nightly: 2.3s in the parallel gate"]
fn charon_array_reference_assignments_check_values_and_independent_snapshots() {
    let p = project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    for (before, after) in [
        ("ensures result == 5u32;", "ensures result == 3u32;"),
        ("ensures result == -3;", "ensures result == 7;"),
        ("ensures result == 7u32;", "ensures result == 9u32;"),
        ("ensures result == 0u64;", "ensures result == 1u64;"),
    ] {
        let invalid = SIDECAR.replace(before, after);
        assert_ne!(invalid, SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn charon_array_reference_assignments_tools_recheck_expanded_certificates() {
    let p = project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "swap.contract",
        "self_copy.contract",
        "copy_million.contract",
        "fill_million.contract",
        "empty.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "nightly: 20 s, over the gate's per-test budget (2026-10-06)"]
fn charon_array_values_unchanged_fixture_verifies_external_snapshots() {
    let p = Project::new("");
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
    for (name, bytes) in [
        ("arrays.rs", source.as_bytes()),
        ("borrow.click", sidecar.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../../design/charon-trial/array-values/arrays.click.import.json")
                .as_slice(),
        ),
        (
            "arrays.ullbc",
            include_bytes!("../../design/charon-trial/array-values/arrays.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../../design/charon-trial/array-values/arrays.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    for (before, after) in [
        ("ensures result == words[0];", "ensures result == words[1];"),
        (
            "ensures target[1] == old(source[1]);",
            "ensures target[1] == old(source[0]);",
        ),
        ("ensures *value == 5u32;", "ensures *value == 4u32;"),
        ("views source[0..2];", "views source[0..1];"),
        ("owns target[0..2];", "views target[0..2];"),
        ("owns target[0..2];", "owns target[0..1];"),
    ] {
        let invalid = sidecar.replace(before, after);
        assert_ne!(invalid, sidecar);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "copy_reference.contract",
        "copy_into.contract",
        "repeat_call.contract",
        "zero_repeat_call.contract",
        "argument_order.contract",
        "assignment_order.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_array_reference_assignments_live_refresh_and_borrow_rejections() {
    let p = project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(SIDECAR, load_import(&p.config()).unwrap())
        .unwrap();
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
        fs::remove_file(p.root.join("bounds.ullbc")).unwrap();
        fs::write(p.root.join("bounds.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("bounds.ullbc").exists());
        fs::write(p.root.join("bounds.rs"), SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

fn external_project() -> Project {
    let p = Project::new("");
    for (name, bytes) in [
        (
            "external.rs",
            include_bytes!("../../design/charon-trial/array-values/external.rs").as_slice(),
        ),
        (
            "borrow.click",
            include_bytes!("../../design/charon-trial/array-values/external.click").as_slice(),
        ),
        (
            "borrow.click.import.json",
            include_bytes!("../../design/charon-trial/array-values/external.click.import.json")
                .as_slice(),
        ),
        (
            "external.ullbc",
            include_bytes!("../../design/charon-trial/array-values/external.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!(
                "../../design/charon-trial/array-values/external.click.import.json.lock"
            )
            .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
#[ignore = "nightly: 15 s, over the gate's per-test budget (2026-10-06)"]
fn charon_external_array_copies_and_fills_verify_and_reject_false_bytes() {
    let p = external_project();
    let sidecar = fs::read_to_string(p.root.join("borrow.click")).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for (before, after) in [
        ("old(source[0])", "old(source[1])"),
        ("target[999999] == value", "target[999999] == value + 1u32"),
        ("result == old(source[0])", "result == source[0]"),
    ] {
        let invalid = sidecar.replace(before, after);
        assert_ne!(invalid, sidecar);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "copy_million.contract",
        "fill_million.contract",
        "independent.contract",
        "empty.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_external_array_copies_live_refresh() {
    let p = external_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        &fs::read_to_string(p.root.join("borrow.click")).unwrap(),
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
}

#[test]
#[ignore = "requires the pinned live Charon/compiler; scripts/check.sh --charon-live"]
fn charon_whole_array_copy_live_refresh_checks_full_authority() {
    let p = Project::new(include_str!("../../examples/rust-array-values/arrays.rs"));
    let sidecar = include_str!("../../examples/rust-array-values/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    let config = serde_json::json!({
        "schema": 3, "backend": "charon-trial", "language": "rust",
        "target": "x86_64-unknown-linux-gnu", "source": "borrow.rs",
        "exporter": PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon"),
        "artifact": "borrow.ullbc",
    });
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for (before, after) in [
        ("views source[0..2];", "views source[0..1];"),
        ("owns target[0..2];", "views target[0..2];"),
        ("owns target[0..2];", "owns target[0..1];"),
    ] {
        let invalid = sidecar.replace(before, after);
        assert_ne!(invalid, sidecar);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
