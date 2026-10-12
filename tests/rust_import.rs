use click::languages::rust::{load_import, refresh_import};
use click::surface::C0VerificationSession;
use std::fs;
use std::path::PathBuf;
use std::process::Command;
use std::sync::atomic::{AtomicUsize, Ordering};

const SOURCE: &str = include_str!("../examples/basic-rust/borrow.rs");
const FIELD_BORROW_GUARD_SOURCE: &str = include_str!("../examples/rust-field-borrow/guard.rs");
const SIDECAR: &str = include_str!("../examples/basic-rust/borrow.click");
struct Project {
    root: PathBuf,
}
impl Project {
    fn isolated(source: &str) -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = std::env::temp_dir().join(format!(
            "click-rust-import-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        fs::write(root.join("borrow.rs"), source).unwrap();
        fs::write(root.join("borrow.click"), SIDECAR).unwrap();
        Self { root }
    }
    fn new(source: &str) -> Self {
        let p = Self::isolated(source);
        let root = &p.root;
        let exporter =
            std::env::var("CLICK_CHARON").expect("build-charon.sh supplies CLICK_CHARON");
        fs::write(root.join("borrow.click.import.json"), serde_json::to_vec(&serde_json::json!({"schema":3,"language":"rust","target":"x86_64-unknown-linux-gnu","source":"borrow.rs","exporter":exporter,"artifact":"borrow.ullbc"})).unwrap()).unwrap();
        p
    }
    fn config(&self) -> PathBuf {
        self.root.join("borrow.click.import.json")
    }
    fn cli(&self, args: &[&str]) -> std::process::Output {
        // `click audit` re-expands and re-verifies every site of a claim,
        // tens of seconds on these examples against under a second for
        // `verify`. The gate has a ten-minute budget, so it leaves audits to
        // the nightly run (`scripts/check.sh --nightly`).
        if args.first() == Some(&"audit") && std::env::var_os("CLICK_NIGHTLY").is_none() {
            return Command::new("true").output().unwrap();
        }
        Command::new(env!("CARGO_BIN_EXE_click"))
            .args(args)
            .arg(self.root.join("borrow.click"))
            .output()
            .unwrap()
    }
}
impl Drop for Project {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.root);
    }
}

const CHARON_SOURCE: &str = include_str!("../design/charon-trial/trial.rs");
const CHARON_SIDECAR: &str = include_str!("../design/charon-trial/trial.click");
fn charon_project() -> Project {
    let p = Project::new(CHARON_SOURCE);
    fs::write(p.root.join("trial.rs"), CHARON_SOURCE).unwrap();
    fs::write(p.root.join("borrow.click"), CHARON_SIDECAR).unwrap();
    fs::write(
        p.config(),
        include_bytes!("../design/charon-trial/trial.click.import.json"),
    )
    .unwrap();
    fs::write(
        p.root.join("trial.ullbc"),
        include_bytes!("../design/charon-trial/trial.ullbc"),
    )
    .unwrap();
    fs::write(
        p.config().with_file_name("borrow.click.import.json.lock"),
        include_bytes!("../design/charon-trial/trial.click.import.json.lock"),
    )
    .unwrap();
    p
}
const CHARON_OWNED_ARRAY_SOURCE: &str =
    include_str!("../design/charon-trial/owned-array-fields/owned.rs");
const CHARON_OWNED_ARRAY_SIDECAR: &str =
    include_str!("../design/charon-trial/owned-array-fields/owned.click");
fn charon_owned_array_project() -> Project {
    let p = Project::new(CHARON_OWNED_ARRAY_SOURCE);
    for (name, bytes) in [
        ("owned.rs", CHARON_OWNED_ARRAY_SOURCE.as_bytes()),
        ("borrow.click", CHARON_OWNED_ARRAY_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/owned-array-fields/owned.click.import.json")
                .as_slice(),
        ),
        (
            "owned.ullbc",
            include_bytes!("../design/charon-trial/owned-array-fields/owned.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!(
                "../design/charon-trial/owned-array-fields/owned.click.import.json.lock"
            )
            .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
fn charon_owned_array_fields_check_moves_snapshots_boundaries_and_frames() {
    let p = charon_owned_array_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_OWNED_ARRAY_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_OWNED_ARRAY_SIDECAR
            .replace("requires index < 4u64;", "requires index == 4294967296u64;"),
        CHARON_OWNED_ARRAY_SIDECAR
            .replace("ensures result == replacement;", "ensures result == value;"),
        CHARON_OWNED_ARRAY_SIDECAR.replace("ensures result == 28u32;", "ensures result == 29u32;"),
        CHARON_OWNED_ARRAY_SIDECAR.replace("ensures result == value;", "ensures result != value;"),
    ] {
        assert_ne!(invalid, CHARON_OWNED_ARRAY_SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn charon_owned_array_fields_cli_tools_recheck_expanded_certificates() {
    let p = charon_owned_array_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "moved.contract",
        "reassigned.contract",
        "snapshot.contract",
        "empty_move.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_owned_array_fields_live_refresh_and_compiler_rejections() {
    let p = charon_owned_array_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_OWNED_ARRAY_SIDECAR,
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
    fs::write(p.root.join("owned.rs"), "pub struct Packet { pub words: [u32;4] } pub fn nonuniform()->u32 { let packet=Packet { words:[1,2,3,4] }; let next=packet; next.words[0] }").unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared("verifying \"owned.rs\"; fn nonuniform() -> u32 { ensures result == 1u32; } by { execute(); simp(); }", load_import(&p.config()).unwrap()).unwrap();
    fs::write(p.root.join("owned.rs"), "pub struct Packet { pub words: [u32;4] } pub fn invalid()->u32 { let packet=Packet { words:[1;4] }; let next=packet; packet.words[0] + next.words[0] }").unwrap();
    fs::remove_file(p.root.join("owned.ullbc")).unwrap();
    let error = refresh_import(&p.config()).unwrap_err();
    assert!(!error.contains("panicked"), "{error}");
    assert!(!p.root.join("owned.ullbc").exists());
}

const CHARON_SNAPSHOT_SOURCE: &str =
    include_str!("../design/charon-trial/array-snapshots/snapshots.rs");
const CHARON_SNAPSHOT_SIDECAR: &str =
    include_str!("../design/charon-trial/array-snapshots/snapshots.click");
fn charon_snapshot_project() -> Project {
    let p = Project::new(CHARON_SNAPSHOT_SOURCE);
    for (name, bytes) in [
        ("snapshots.rs", CHARON_SNAPSHOT_SOURCE.as_bytes()),
        ("borrow.click", CHARON_SNAPSHOT_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/array-snapshots/snapshots.click.import.json")
                .as_slice(),
        ),
        (
            "snapshots.ullbc",
            include_bytes!("../design/charon-trial/array-snapshots/snapshots.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!(
                "../design/charon-trial/array-snapshots/snapshots.click.import.json.lock"
            )
            .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn charon_array_snapshots_check_computed_lanes_and_copy_independence() {
    let p = charon_snapshot_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_SNAPSHOT_SIDECAR, &prepared).unwrap();
    for (before, after) in [
        ("ensures result == a;", "ensures result == 99u32;"),
        ("ensures result == b;", "ensures result != b;"),
        ("ensures result == 28u32;", "ensures result == 29u32;"),
        ("ensures result == b ^ 1u32;", "ensures result == b;"),
    ] {
        let invalid = CHARON_SNAPSHOT_SIDECAR.replace(before, after);
        assert_ne!(invalid, CHARON_SNAPSHOT_SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn charon_array_snapshots_cli_tools_recheck_expanded_certificates() {
    let p = charon_snapshot_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "computed_move.contract",
        "source_write.contract",
        "target_write.contract",
        "sparse.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_array_snapshots_live_refresh() {
    let p = charon_snapshot_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_SNAPSHOT_SIDECAR,
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
}

const CHARON_OPERATOR_SOURCE: &str =
    include_str!("../design/charon-trial/assignment-operators/operators.rs");
const CHARON_OPERATOR_SIDECAR: &str =
    include_str!("../design/charon-trial/assignment-operators/operators.click");
fn charon_operator_project() -> Project {
    let p = Project::new(CHARON_OPERATOR_SOURCE);
    for (name, bytes) in [
        ("operators.rs", CHARON_OPERATOR_SOURCE.as_bytes()),
        ("borrow.click", CHARON_OPERATOR_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!(
                "../design/charon-trial/assignment-operators/operators.click.import.json"
            )
            .as_slice(),
        ),
        (
            "operators.ullbc",
            include_bytes!("../design/charon-trial/assignment-operators/operators.ullbc")
                .as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!(
                "../design/charon-trial/assignment-operators/operators.click.import.json.lock"
            )
            .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
#[ignore = "nightly: 39 s, over the gate's per-test budget (2026-10-06)"]
fn charon_assignment_operators_check_lanes_panic_obligations_and_authority() {
    let p = charon_operator_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_OPERATOR_SIDECAR, &prepared).unwrap();
    for (before, after) in [
        ("old(self.0[0]) * rhs", "old(self.0[0]) + rhs"),
        ("old(self.0[3]) % quotient", "old(self.0[2]) % quotient"),
        (
            "ensures other.0[0] == old(other.0[0]);",
            "ensures other.0[0] == 0u32;",
        ),
        ("requires quotient != 0u32;", "requires quotient == 0u32;"),
        ("owns self.0[0..4];", "views self.0[0..4];"),
        ("views other.0[0..4];", "views other.0[1..4];"),
        (
            "requires rhs == 0u32 or self.0[0] <= 4294967295u32 / rhs;",
            "requires rhs == 2u32; requires self.0[0] == 4294967295u32;",
        ),
        ("(b * 2u32 % 7u32)", "(b * 2u32 % 3u32)"),
        ("(a * 2u32 % 7u32)", "(a * 2u32)"),
    ] {
        let invalid = CHARON_OPERATOR_SIDECAR.replace(before, after);
        assert_ne!(invalid, CHARON_OPERATOR_SIDECAR);
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "{before}"
        );
    }
}

const CHARON_MULTIPLY_SOURCE: &str =
    include_str!("../design/charon-trial/symbolic-multiply/probe.rs");
const CHARON_MULTIPLY_SIDECAR: &str =
    include_str!("../design/charon-trial/symbolic-multiply/probe.click");
fn charon_multiply_project() -> Project {
    let p = Project::new(CHARON_MULTIPLY_SOURCE);
    for (name, bytes) in [
        ("probe.rs", CHARON_MULTIPLY_SOURCE.as_bytes()),
        ("borrow.click", CHARON_MULTIPLY_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/symbolic-multiply/probe.click.import.json")
                .as_slice(),
        ),
        (
            "probe.ullbc",
            include_bytes!("../design/charon-trial/symbolic-multiply/probe.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/symbolic-multiply/probe.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
fn charon_symbolic_multiply_checks_general_safety_and_full_width_boundaries() {
    let p = charon_multiply_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_MULTIPLY_SIDECAR, &prepared).unwrap();
    let premise = "requires rhs == 0u32 or x <= 4294967295u32 / rhs;";
    for requirements in [
        "requires rhs == 0u32; requires x == 4294967295u32;",
        "requires rhs == 1u32; requires x == 4294967295u32;",
        "requires rhs == 2u32; requires x <= 2147483647u32;",
        "requires rhs == 4294967295u32; requires x == 1u32;",
    ] {
        let valid = CHARON_MULTIPLY_SIDECAR.replace(premise, requirements);
        C0VerificationSession::new_program_prepared(&valid, &prepared).unwrap();
    }
    for requirements in [
        "",
        "requires rhs == 2u32; requires x == 4294967295u32;",
        "requires rhs == 0u32; requires x <= 4294967295u32 / rhs;",
    ] {
        let invalid = CHARON_MULTIPLY_SIDECAR.replace(premise, requirements);
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "{requirements}"
        );
    }
    let invalid =
        CHARON_MULTIPLY_SIDECAR.replace("ensures result == x * rhs;", "ensures result == x + rhs;");
    assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
}

#[test]
fn charon_symbolic_multiply_tools_recheck_the_unreachable_path_certificate() {
    let p = charon_multiply_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    assert_cli(
        &p,
        &["expand", "--claim", "multiply.contract", "--in-place"],
    );
    assert_cli(&p, &["verify"]);
}
#[test]
#[ignore = "nightly: 72 s, over the gate's per-test budget (2026-10-06)"]
fn charon_assignment_operators_cli_tools_recheck_expanded_certificates() {
    let p = charon_operator_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "U32X4_mul_assign_u32.contract",
        "U32X4_add_assign_ref_U32X4.contract",
        "reduced.contract",
        "local.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_assignment_operators_live_refresh_and_source_semantics() {
    let p = charon_operator_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_OPERATOR_SIDECAR,
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for source in [
        "pub struct S(pub u32); impl core::ops::AddAssign<S> for S { fn add_assign(&mut self, rhs:S) { self.0 += rhs.0; } }",
        "pub struct S<T>(pub T); impl<T> core::ops::AddAssign<T> for S<T> { fn add_assign(&mut self, rhs:T) { self.0 = rhs; } }",
        "pub struct S(pub u32); trait AddAssign { fn add_assign(&mut self, rhs:u32); } impl AddAssign for S { fn add_assign(&mut self, rhs:u32) { self.0 = rhs; } }",
        "pub struct S(pub u32); impl core::ops::AddAssign<&S> for S { fn add_assign(&mut self, rhs:&S) { rhs.0 = self.0; } }",
        "pub struct S(pub u32); impl core::ops::AddAssign<u32> for S { fn add_assign(&mut self, rhs:u32) { self.0 = rhs; } } pub fn S_add_assign_u32(x:&mut S, rhs:u32) { x.0 = rhs; }",
    ] {
        fs::write(p.root.join("operators.rs"), source).unwrap();
        let old_artifact = fs::read(p.root.join("operators.ullbc")).unwrap();
        let old_lock = fs::read(p.root.join("borrow.click.import.json.lock")).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(!error.contains("panicked"), "{error}");
        assert_eq!(
            fs::read(p.root.join("operators.ullbc")).unwrap(),
            old_artifact
        );
        assert_eq!(
            fs::read(p.root.join("borrow.click.import.json.lock")).unwrap(),
            old_lock
        );
    }
    // Same trait and owner, different RHS identities. Neither body performs addition.
    fs::write(p.root.join("operators.rs"), "pub struct S(pub u32); impl core::ops::AddAssign<u32> for S { fn add_assign(&mut self, rhs:u32) { self.0 = rhs; } } impl core::ops::AddAssign<&S> for S { fn add_assign(&mut self, rhs:&S) { self.0 = rhs.0; } } pub fn scalar(x:&mut S, rhs:u32) { *x += rhs; } pub fn borrowed(x:&mut S, rhs:&S) { *x += rhs; }").unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = r#"verifying "operators.rs";
impl AddAssign<u32> for S { fn add_assign(&mut self, rhs: u32) { owns self.0; ensures self.0 == rhs; } by { execute(); simp(); } }
impl AddAssign<&S> for S { fn add_assign(&mut self, rhs: &S) { requires separate(memory(self.0), memory(rhs.0)); views rhs.0; owns self.0; ensures self.0 == old(rhs.0); ensures rhs.0 == old(rhs.0); } by { execute(); simp(); } }
fn scalar(x: &mut S, rhs: u32) { owns x.0; ensures x.0 == rhs; } by { execute(); simp(); }
fn borrowed(x: &mut S, rhs: &S) { requires separate(memory(x.0), memory(rhs.0)); views rhs.0; owns x.0; ensures x.0 == old(rhs.0); } by { execute(); simp(); }
"#;
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    let false_math = sidecar.replace(
        "ensures self.0 == rhs;",
        "ensures self.0 == old(self.0) + rhs;",
    );
    assert!(C0VerificationSession::new_program_prepared(&false_math, &prepared).is_err());
}

const CHARON_ITERATION_SOURCE: &str =
    include_str!("../design/charon-trial/array-iteration/iteration.rs");
const CHARON_ITERATION_SIDECAR: &str =
    include_str!("../design/charon-trial/array-iteration/iteration.click");
fn charon_iteration_project() -> Project {
    let p = Project::new(CHARON_ITERATION_SOURCE);
    for (name, bytes) in [
        ("iteration.rs", CHARON_ITERATION_SOURCE.as_bytes()),
        ("borrow.click", CHARON_ITERATION_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/array-iteration/iteration.click.import.json")
                .as_slice(),
        ),
        (
            "iteration.ullbc",
            include_bytes!("../design/charon-trial/array-iteration/iteration.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!(
                "../design/charon-trial/array-iteration/iteration.click.import.json.lock"
            )
            .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn charon_shared_iteration_checks_order_moves_empty_arrays_and_read_authority() {
    let p = charon_iteration_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_ITERATION_SIDECAR, &prepared).unwrap();
    for (before, after) in [
        ("ensures result == 4u32;", "ensures result == 3u32;"),
        (
            "ensures result == ((a << 1u32) ^ b);",
            "ensures result == ((b << 1u32) ^ a);",
        ),
        ("ensures result == (a ^ b);", "ensures result == a;"),
        (
            "ensures result == old(words[0]);",
            "ensures result == old(words[1]);",
        ),
        ("views words[0..4];", "views words[1..4];"),
    ] {
        let invalid = CHARON_ITERATION_SIDECAR.replace(before, after);
        assert_ne!(invalid, CHARON_ITERATION_SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
#[ignore = "nightly: 12 s, over the gate's per-test budget (2026-10-06)"]
fn charon_shared_iteration_cli_tools_recheck_expanded_certificates() {
    let p = charon_iteration_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "borrowed.contract",
        "moved.contract",
        "ordered.contract",
        "signed.contract",
        "empty.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_shared_iteration_live_refresh_and_rejected_protocols() {
    let p = charon_iteration_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_ITERATION_SIDECAR,
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for source in [
        "pub fn bad(words: &mut [u32;4]) { for word in words.iter_mut() { *word = 0; } }",
        "pub fn bad(words: [u32;4])->u32 { let mut x=0; for word in words { x ^= word; } x }",
        "pub fn bad(words: &[u32;4])->u32 { let mut x=0; for word in words.iter().rev() { x ^= *word; } x }",
        "pub fn bad(words: &[u32;4]) { for word in words { *word = 0; } }",
    ] {
        fs::write(p.root.join("iteration.rs"), source).unwrap();
        let old_artifact = fs::read(p.root.join("iteration.ullbc")).unwrap();
        let old_lock = fs::read(p.root.join("borrow.click.import.json.lock")).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(!error.contains("panicked"), "{error}");
        assert_eq!(
            fs::read(p.root.join("iteration.ullbc")).unwrap(),
            old_artifact
        );
        assert_eq!(
            fs::read(p.root.join("borrow.click.import.json.lock")).unwrap(),
            old_lock
        );
    }
}

const CHARON_FIELDS_SOURCE: &str = include_str!("../design/charon-trial/array-fields/fields.rs");
const CHARON_FIELDS_SIDECAR: &str =
    include_str!("../design/charon-trial/array-fields/fields.click");
fn charon_fields_project() -> Project {
    let p = Project::new(CHARON_FIELDS_SOURCE);
    for (name, bytes) in [
        ("fields.rs", CHARON_FIELDS_SOURCE.as_bytes()),
        ("borrow.click", CHARON_FIELDS_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/array-fields/fields.click.import.json")
                .as_slice(),
        ),
        (
            "fields.ullbc",
            include_bytes!("../design/charon-trial/array-fields/fields.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/array-fields/fields.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
fn charon_shared_reference_signature_mismatch_displays_constness() {
    let p = charon_fields_project();
    let prepared = load_import(&p.config()).unwrap();
    let missing_const = CHARON_FIELDS_SIDECAR.replacen("state: &Lanes", "state: &mut Lanes", 1);
    let error = match C0VerificationSession::new_program_prepared(&missing_const, &prepared) {
        Ok(_) => panic!("a Rust shared reference requires a const pointer"),
        Err(error) => error,
    };
    assert!(
        error
            .message()
            .contains(".click has struct Lanes* state, C has const struct Lanes* state"),
        "{}",
        error.message()
    );
}

#[test]
fn charon_array_fields_check_bounds_authority_and_frames() {
    let p = charon_fields_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_FIELDS_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_FIELDS_SIDECAR.replace("requires index < 4u64;", "requires index == 4u64;"),
        CHARON_FIELDS_SIDECAR.replace("requires index < 7u64;", "requires index == 4294967296u64;"),
        CHARON_FIELDS_SIDECAR.replace("views state.values[0..4];", ""),
        CHARON_FIELDS_SIDECAR.replace("owns state.values[0..4];", "views state.values[0..4];"),
        CHARON_FIELDS_SIDECAR.replace(
            "ensures state.values[index] == value;",
            "ensures state.values[index] != value;",
        ),
        CHARON_FIELDS_SIDECAR.replace(
            "result == old(state.0[index])",
            "result != old(state.0[index])",
        ),
    ] {
        assert_ne!(invalid, CHARON_FIELDS_SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn charon_array_fields_cli_tools_recheck_borrowed_field_certificates() {
    let p = charon_fields_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "read.contract",
        "write.contract",
        "borrowed_first.contract",
        "borrowed_byte.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_array_fields_live_refresh_and_compiler_rejections() {
    let p = charon_fields_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_FIELDS_SIDECAR,
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for source in [
        "pub struct A { pub values:[u16;4] } pub fn bad(x:&A)->u16 { x.values[0] }",
        "#[repr(C,packed)] pub struct A { pub values:[u32;4] } pub fn bad(x:&A)->u32 { x.values[0] }",
        "pub struct A { pub values:[u32;4] } pub fn bad(x:&A) { x.values[0]=1; }",
    ] {
        fs::remove_file(p.root.join("fields.ullbc")).unwrap();
        fs::write(p.root.join("fields.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(!error.contains("panicked"), "{error}");
        assert!(!p.root.join("fields.ullbc").exists());
        fs::write(p.root.join("fields.rs"), CHARON_FIELDS_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_ARITHMETIC_SOURCE: &str =
    include_str!("../design/charon-trial/arithmetic/arithmetic.rs");
const CHARON_ARITHMETIC_SIDECAR: &str =
    include_str!("../design/charon-trial/arithmetic/arithmetic.click");
fn charon_arithmetic_project() -> Project {
    let p = Project::new(CHARON_ARITHMETIC_SOURCE);
    for (name, bytes) in [
        ("arithmetic.rs", CHARON_ARITHMETIC_SOURCE.as_bytes()),
        ("borrow.click", CHARON_ARITHMETIC_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/arithmetic/arithmetic.click.import.json")
                .as_slice(),
        ),
        (
            "arithmetic.ullbc",
            include_bytes!("../design/charon-trial/arithmetic/arithmetic.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/arithmetic/arithmetic.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn charon_checksum_arithmetic_checks_panic_bounds_and_full_width_values() {
    let p = charon_arithmetic_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_ARITHMETIC_SIDECAR, &prepared).unwrap();
    for claim in [
        "fn reduce(value: u32) -> u32 { requires value == 4294967295u32; ensures result == 224u32; }",
        "fn wide_quotient(value: usize, divisor: usize) -> usize { requires value == 18446744073709551615u64; requires divisor == 1u64; ensures result == 18446744073709551615u64; }",
        "fn wide_left(value: usize, count: usize) -> usize { requires value == 18446744073709551615u64; requires count == 1u64; ensures result == 18446744073709551614u64; }",
        "fn wide_right(value: usize, count: usize) -> usize { requires value == 18446744073709551615u64; requires count == 63u64; ensures result == 1u64; }",
        "fn word_right(value: u16, count: usize) -> u16 { requires value == 65535; requires count == 15u64; ensures result == 1; }",
        "fn shifted_byte(value: u8, count: u32) -> u8 { requires value == 128; requires count == 1u32; ensures result == 0; }",
        "fn conditional_divide(value: u32, divisor: u32, skip: bool) -> u32 { requires skip != 0; requires divisor == 0u32; ensures result == 0u32; }",
    ] {
        let claim = format!("verifying \"arithmetic.rs\"; {claim} by {{ execute(); simp(); }}");
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
    for invalid in [
        CHARON_ARITHMETIC_SIDECAR.replace("requires sum <= 4294967040u32;", ""),
        CHARON_ARITHMETIC_SIDECAR.replace("requires count < 8u32;", "requires count == 8u32;"),
        CHARON_ARITHMETIC_SIDECAR.replace("requires count < 64u64;", "requires count == 64u64;"),
        CHARON_ARITHMETIC_SIDECAR.replace(
            "requires 0 <= count and count < 32;",
            "requires count == -1;",
        ),
        CHARON_ARITHMETIC_SIDECAR.replace("requires divisor != 0u32;", "requires divisor == 0u32;"),
        CHARON_ARITHMETIC_SIDECAR.replace("requires divisor != 0u64;", "requires divisor == 0u64;"),
        CHARON_ARITHMETIC_SIDECAR.replace("value % 65521u32", "value % 65519u32"),
        CHARON_ARITHMETIC_SIDECAR.replace("((high << 16) | low)", "((high << 15) | low)"),
    ] {
        assert_ne!(invalid, CHARON_ARITHMETIC_SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    for count in [64u64, 4294967296, u64::MAX] {
        let claim = format!(
            "verifying \"arithmetic.rs\"; fn wide_left(value: usize, count: usize) -> usize {{ requires value == 0u64; requires count == {count}u64; ensures result == 0u64; }} by {{ execute(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&claim, &prepared)
            .err()
            .expect("invalid shift accepted");
        assert!(
            error.message().contains("Rust shl panic check"),
            "{}",
            error.message()
        );
    }
}
#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn charon_checksum_arithmetic_cli_tools_recheck_certificates() {
    let p = charon_arithmetic_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "reduce.contract",
        "pack.contract",
        "wide_left.contract",
        "signed_count.contract",
        "conditional_divide.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_and_charon_unsigned_shifts_preserve_full_width_counts() {
    let p = Project::new(CHARON_ARITHMETIC_SOURCE);
    refresh_import(&p.config()).unwrap();
    let sidecar = CHARON_ARITHMETIC_SIDECAR.replace("arithmetic.rs", "borrow.rs");
    C0VerificationSession::new_program_prepared(&sidecar, load_import(&p.config()).unwrap())
        .unwrap();
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_checksum_arithmetic_live_refresh_and_rejected_modes() {
    let p = charon_arithmetic_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_ARITHMETIC_SIDECAR,
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for source in [
        "pub fn bad(x:u32, count:u32)->u32 { x.wrapping_shl(count) }",
        "pub fn bad(x:u32, count:u32)->u32 { x.wrapping_shr(count) }",
        "pub fn bad(x:i32, count:u32)->i32 { x << count }",
        "pub fn bad(x:i32, divisor:i32)->i32 { x / divisor }",
    ] {
        fs::remove_file(p.root.join("arithmetic.ullbc")).unwrap();
        fs::write(p.root.join("arithmetic.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains("Charon trial does not support"), "{error}");
        assert!(!p.root.join("arithmetic.ullbc").exists());
        fs::write(p.root.join("arithmetic.rs"), CHARON_ARITHMETIC_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_NESTED_SOURCE: &str = include_str!("../design/charon-trial/nested/nested.rs");
const CHARON_NESTED_SIDECAR: &str = include_str!("../design/charon-trial/nested/nested.click");
fn charon_nested_project() -> Project {
    let p = Project::new(CHARON_NESTED_SOURCE);
    for (name, bytes) in [
        ("nested.rs", CHARON_NESTED_SOURCE.as_bytes()),
        ("borrow.click", CHARON_NESTED_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/nested/nested.click.import.json").as_slice(),
        ),
        (
            "nested.ullbc",
            include_bytes!("../design/charon-trial/nested/nested.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/nested/nested.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
#[ignore = "nightly: 14 s, over the gate's per-test budget (2026-10-06)"]
fn charon_nested_chunks_and_array_slices_check_bytes_bounds_and_claims() {
    let p = charon_nested_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_NESTED_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_NESTED_SIDECAR.replace("ensures result == 8u64;", "ensures result == 7u64;"),
        CHARON_NESTED_SIDECAR.replace("ensures result == 9;", "ensures result == 7;"),
        CHARON_NESTED_SIDECAR.replace("requires index < 8u64;", "requires index == 8u64;"),
        CHARON_NESTED_SIDECAR.replace("ensures result == 7;", "ensures result == 9;"),
        CHARON_NESTED_SIDECAR.replace("views bytes[0..8];", ""),
        CHARON_NESTED_SIDECAR.replace("bytes[k] == old(bytes[k])", "bytes[k] == 7"),
    ] {
        assert_ne!(invalid, CHARON_NESTED_SIDECAR);
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
#[ignore = "nightly: 40 s, over the gate's per-test budget (2026-10-06)"]
fn charon_nested_cli_tools_recheck_expanded_certificates() {
    let p = charon_nested_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "nested.contract",
        "array_len.contract",
        "array_mut.contract",
        "array_read.contract",
        "large_array_len.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_nested_live_refresh_and_rejected_array_borrows() {
    let p = charon_nested_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_NESTED_SIDECAR,
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for (source, diagnostic) in [
        (
            "pub fn bad()->u8 { let mut bytes=[7u8;8]; let slice:&[u8]=&bytes; bytes[0]=9; slice[0] }",
            "E0506",
        ),
        (
            "pub fn bad()->u8 { let bytes=[7u8;8]; let slice:&[u8]=&bytes; slice[0]=9; slice[0] }",
            "E0594",
        ),
        (
            "pub fn bad()->usize { let bytes=[7u16;8]; let slice:&[u16]=&bytes; slice.len() }",
            "Charon trial does not support",
        ),
        (
            "pub fn bad(n:i32) { let mut i=0; while i<n { let mut j=0; while j<n { if j==2 { break; } j+=1; } i+=1; } }",
            "extra exit",
        ),
    ] {
        fs::remove_file(p.root.join("nested.ullbc")).unwrap();
        fs::write(p.root.join("nested.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("nested.ullbc").exists());
        fs::write(p.root.join("nested.rs"), CHARON_NESTED_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_CHUNK_SOURCE: &str = include_str!("../design/charon-trial/chunks/chunks.rs");
const CHARON_CHUNK_SIDECAR: &str = include_str!("../design/charon-trial/chunks/chunks.click");
fn charon_chunk_project() -> Project {
    let p = Project::new(CHARON_CHUNK_SOURCE);
    for (name, bytes) in [
        ("chunks.rs", CHARON_CHUNK_SOURCE.as_bytes()),
        ("borrow.click", CHARON_CHUNK_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/chunks/chunks.click.import.json").as_slice(),
        ),
        (
            "chunks.ullbc",
            include_bytes!("../design/charon-trial/chunks/chunks.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/chunks/chunks.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
#[ignore = "nightly: 12 s, over the gate's per-test budget (2026-10-06)"]
fn charon_chunks_check_boundaries_authority_and_false_claims() {
    let p = charon_chunk_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_CHUNK_SIDECAR, &prepared).unwrap();
    for (length, size) in [
        (0u64, 4u64),
        (4, 4),
        (7, 4),
        (8, 4),
        (3, 4),
        (7, u64::MAX),
        (7, 4294967296),
    ] {
        let claim = format!(
            "verifying \"chunks.rs\"; fn tail(bytes: &[u8], size: usize) -> usize {{ requires bytes.len() == {length}u64; requires size == {size}u64; ensures result == {}u64; }} by {{ execute(); simp(); }}",
            length % size
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
    for length in [0u64, 3, 4, 7, 8] {
        let result = if length < 4 { 0 } else { 4 };
        let claim = format!(
            "verifying \"chunks.rs\"; fn next_len(bytes: &[u8]) -> usize {{ requires bytes.len() == {length}u64; ensures result == {result}u64; }} by {{ execute(); simp(); }}"
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
    for length in [1u64, 3, 5, 7] {
        let offset = length - length % 4;
        let claim = format!(
            "verifying \"chunks.rs\"; fn tail_byte(bytes: &[u8]) -> u8 {{ requires bytes.len() == {length}u64; views bytes[0..{length}]; ensures result == old(bytes[{offset}]); }} by {{ have bytes.len() - bytes.len() % 4u64 == {offset}u64 by {{ rewrite(bytes.len() == {length}u64); simp(); }} execute(); simp(); }}"
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
    for invalid in [
        CHARON_CHUNK_SIDECAR.replace("requires size != 0u64;", "requires size == 0u64;"),
        CHARON_CHUNK_SIDECAR.replace(
            "ensures result == bytes.len() % size;",
            "ensures result == bytes.len();",
        ),
        CHARON_CHUNK_SIDECAR.replace("    views bytes[0..bytes.len()];\n", ""),
        CHARON_CHUNK_SIDECAR.replace(
            "requires bytes.len() == 7u64;",
            "requires bytes.len() == 8u64;",
        ),
        CHARON_CHUNK_SIDECAR.replace("ensures result == old(bytes[4]);", "ensures result == 7;"),
    ] {
        assert_ne!(invalid, CHARON_CHUNK_SIDECAR);
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "accepted {invalid}"
        );
    }
}
#[test]
#[ignore = "nightly: 21 s, over the gate's per-test budget (2026-10-06)"]
fn charon_chunk_cli_tools_recheck_expanded_certificates() {
    let p = charon_chunk_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "tail.contract",
        "walk.contract",
        "next_len.contract",
        "tail_byte.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_chunks_live_refresh_and_rejected_protocols() {
    let p = charon_chunk_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_CHUNK_SIDECAR,
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for (source, diagnostic) in [
        (
            "pub fn bad(x:&[u8]) { let chunks=x.chunks_exact(4); for chunk in chunks { chunk[0]=7; } }",
            "E0594",
        ),
        (
            "pub fn bad(x:&[u8])->usize { let chunks=x.chunks_exact(4); for chunk in chunks { let a=chunk[0]; } chunks.remainder().len() }",
            "E0382",
        ),
        (
            "pub fn bad(x:&[u16])->usize { x.chunks_exact(4).remainder().len() }",
            "Charon trial does not support",
        ),
        (
            "pub fn bad(x:&[u8]) { for chunk in x.chunks_exact(4).rev() { let a=chunk[0]; } }",
            "Charon trial does not support",
        ),
    ] {
        fs::remove_file(p.root.join("chunks.ullbc")).unwrap();
        fs::write(p.root.join("chunks.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("chunks.ullbc").exists());
        fs::write(p.root.join("chunks.rs"), CHARON_CHUNK_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_SLICE_SOURCE: &str = include_str!("../design/charon-trial/slices/slices.rs");
const CHARON_SLICE_SIDECAR: &str = include_str!("../design/charon-trial/slices/slices.click");
fn charon_slice_project() -> Project {
    let p = Project::new(CHARON_SLICE_SOURCE);
    for (name, bytes) in [
        ("slices.rs", CHARON_SLICE_SOURCE.as_bytes()),
        ("borrow.click", CHARON_SLICE_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/slices/slices.click.import.json").as_slice(),
        ),
        (
            "slices.ullbc",
            include_bytes!("../design/charon-trial/slices/slices.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/slices/slices.click.import.json.lock")
                .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn charon_slices_preserve_metadata_permissions_and_cleanup() {
    let p = charon_slice_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_SLICE_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_SLICE_SIDECAR.replace("ensures result == bytes.len();", "ensures result == 0;"),
        CHARON_SLICE_SIDECAR.replace("ensures result == value;", "ensures result == value + 1;"),
        CHARON_SLICE_SIDECAR.replace(
            "ensures value[0] == old(value[0]);",
            "ensures value[0] == 7;",
        ),
        CHARON_SLICE_SIDECAR.replace("    requires index < bytes.len();\n", ""),
        CHARON_SLICE_SIDECAR.replace(
            "    requires index < bytes.len();",
            "    requires index == bytes.len();",
        ),
        CHARON_SLICE_SIDECAR.replace(
            "    requires index < bytes.len();",
            "    requires index == 4294967296u64;",
        ),
        CHARON_SLICE_SIDECAR.replace("    requires bytes.len() <= 2147483647u64;\n", ""),
        CHARON_SLICE_SIDECAR.replace("    views bytes[0..bytes.len()];\n", ""),
        CHARON_SLICE_SIDECAR.replace("    owns bytes[0..bytes.len()];\n", ""),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "accepted {invalid}"
        );
    }
    // Contract owns/views composition already establishes byte separation.
    let composed = CHARON_SLICE_SIDECAR.replace(
        "    requires separate(memory(value[0..1]), memory(bytes[0..bytes.len()]));\n",
        "",
    );
    C0VerificationSession::new_program_prepared(&composed, &prepared).unwrap();
    // Metadata alone requires no memory resource, including empty and very large slices.
    for length in [0u64, 8, 1024, 1_000_000, u64::MAX] {
        let claim = format!(
            "verifying \"slices.rs\"; fn length(bytes: &[u8]) -> usize {{ requires bytes.len() == {length}u64; ensures result == {length}u64; }} by {{ execute(); simp(); }}"
        );
        C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
    }
}
#[test]
fn charon_slice_failure_has_a_focused_trace() {
    // Frozen Rust inputs must use the same checked trace and proof selection
    // as C. Tracing one proof must not execute a failing sibling contract.
    let p = charon_slice_project();
    fs::write(
        p.root.join("borrow.click"),
        "verifying \"slices.rs\";\nfn length(bytes: &[u8]) -> usize { ensures result == 0u64; } by { execute(); simp(); }\ntheorem good(x: int32) { ensures x == x by { normalize(); } }\n",
    ).unwrap();
    let output = p.cli(&["verify"]);
    assert!(!output.status.success());
    let error = String::from_utf8(output.stderr).unwrap();
    assert!(error.contains("proof error:"), "{error}");
    assert!(error.contains("--trace-proof length"), "{error}");
    let output = p.cli(&["verify", "--trace-proof", "length", "--trace-to", "2:78"]);
    assert!(!output.status.success());
    let trace = String::from_utf8(output.stderr).unwrap();
    assert!(!trace.contains("typed compiler inputs"), "{trace}");
    assert!(trace.contains("proof trace"), "{trace}");
    assert!(trace.contains("tactic@2"), "{trace}");
    let output = p.cli(&["verify", "--trace-proof", "good"]);
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let trace = String::from_utf8(output.stdout).unwrap();
    assert!(trace.contains("1 selected proof verified"), "{trace}");
    let output = p.cli(&["verify", "--trace-proof", "missing"]);
    assert!(!output.status.success());
    assert!(String::from_utf8_lossy(&output.stderr).contains("is not a selected proof"));
}

#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn charon_slice_cli_tools_recheck_expanded_certificates() {
    let p = charon_slice_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "length.contract",
        "write_read.contract",
        "guarded_read.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_slices_live_refresh_and_borrow_checking() {
    let p = charon_slice_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_SLICE_SIDECAR,
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for (source, diagnostic) in [
        ("pub fn bad(x:&[u8]) { x[0]=7; }", "E0594"),
        (
            "pub fn bad(x:&mut [u8]) -> u8 { let y=&mut *x; x[0]=7; y[0] }",
            "E0503",
        ),
        (
            "pub fn bad(x:&[u16])->usize { x.len() }",
            "slice elements outside shared scalar array iteration",
        ),
    ] {
        fs::remove_file(p.root.join("slices.ullbc")).unwrap();
        fs::write(p.root.join("slices.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("slices.ullbc").exists());
        fs::write(p.root.join("slices.rs"), CHARON_SLICE_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_ARRAY_SOURCE: &str =
    include_str!("../design/charon-trial/conversions-arrays/arrays.rs");
const CHARON_ARRAY_SIDECAR: &str =
    include_str!("../design/charon-trial/conversions-arrays/arrays.click");
fn charon_array_project() -> Project {
    let p = Project::new(CHARON_ARRAY_SOURCE);
    for (name, bytes) in [
        ("arrays.rs", CHARON_ARRAY_SOURCE.as_bytes()),
        ("borrow.click", CHARON_ARRAY_SIDECAR.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/conversions-arrays/arrays.click.import.json")
                .as_slice(),
        ),
        (
            "arrays.ullbc",
            include_bytes!("../design/charon-trial/conversions-arrays/arrays.ullbc").as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!(
                "../design/charon-trial/conversions-arrays/arrays.click.import.json.lock"
            )
            .as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn charon_arrays_compose_with_resolved_conversion_and_drop() {
    let p = charon_array_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_ARRAY_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_ARRAY_SIDECAR.replace("ensures result == x;", "ensures result == x + 1;"),
        CHARON_ARRAY_SIDECAR.replace("value[0] == old(value[0]);", "value[0] == 7;"),
        CHARON_ARRAY_SIDECAR.replace("ensures result == 7;", "ensures result == 8;"),
        CHARON_ARRAY_SIDECAR.replace("ensures result == 9;", "ensures result == 2;"),
        CHARON_ARRAY_SIDECAR.replace("ensures result == 1;", "ensures result == 257;"),
        CHARON_ARRAY_SIDECAR.replace(
            "value[0] == old(value[0]) + 1;",
            "value[0] == old(value[0]);",
        ),
        CHARON_ARRAY_SIDECAR.replace("    owns value[0..1];\n", ""),
        CHARON_ARRAY_SIDECAR.replace("    requires value[0] < 2147483647;\n", ""),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "accepted {invalid}"
        );
    }
}
#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn charon_array_cli_tools_recheck_expanded_certificates() {
    let p = charon_array_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    for claim in [
        "guarded_array.contract",
        "large_array.contract",
        "empty_array.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_arrays_live_refresh_and_rejected_source_shapes() {
    let p = charon_array_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        CHARON_ARRAY_SIDECAR,
        load_import(&p.config()).unwrap(),
    )
    .unwrap();
    for (source, diagnostic) in [
        ("pub fn bad(x:u32)->u8 { u8::from(x) }", "E0277"),
        (
            "struct Fake; impl Fake { fn from(x:u16)->u32 { x as u32 } } pub fn bad(x:u16)->u32 { Fake::from(x) }",
            "nested or disambiguated source items",
        ),
        ("pub fn bad()->u16 { let x=[7u16;4]; x[0] }", "i32/u8/u32"),
        (
            "pub fn bad()->u32 { let x=[7u32;536870912]; x[0] }",
            "signed-word storage",
        ),
    ] {
        fs::remove_file(p.root.join("arrays.ullbc")).unwrap();
        fs::write(p.root.join("arrays.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("arrays.ullbc").exists());
        fs::write(p.root.join("arrays.rs"), CHARON_ARRAY_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

const CHARON_LOOP_SOURCE: &str = include_str!("../design/charon-trial/borrowed-loop/loop.rs");
const PLAIN_RECORD_LOOP_SOURCE: &str =
    include_str!("../design/charon-trial/plain-record-loop/loop.rs");
const PLAIN_RECORD_LOOP_PROOF: &str =
    include_str!("../design/charon-trial/plain-record-loop/loop.click");

fn plain_record_loop_project() -> Project {
    let p = Project::new(PLAIN_RECORD_LOOP_SOURCE);
    for (name, bytes) in [
        ("loop.rs", PLAIN_RECORD_LOOP_SOURCE.as_bytes()),
        ("borrow.click", PLAIN_RECORD_LOOP_PROOF.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/plain-record-loop/loop.click.import.json")
                .as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/plain-record-loop/loop.click.import.json.lock")
                .as_slice(),
        ),
        (
            "loop.ullbc",
            include_bytes!("../design/charon-trial/plain-record-loop/loop.ullbc").as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
fn charon_plain_record_loop_proves_symbolic_iterations_and_rejects_false_claims() {
    let p = plain_record_loop_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(PLAIN_RECORD_LOOP_PROOF, &prepared).unwrap();
    for (before, after) in [
        ("ensures result == n;", "ensures result == n + 1;"),
        ("invariant sum == i;", "invariant sum == i + 1;"),
        ("requires 0 <= n and n <= 1000;", "requires n <= 1000;"),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(
                &PLAIN_RECORD_LOOP_PROOF.replace(before, after),
                &prepared,
            )
            .is_err(),
            "accepted {before} -> {after}"
        );
    }
}

#[test]
#[ignore = "nightly: plain-record loop proof-tool agreement"]
fn charon_plain_record_loop_tools_recheck_expanded_certificate() {
    let p = plain_record_loop_project();
    for args in [
        vec!["verify"],
        vec!["expand", "--claim", "packet_walk.contract", "--in-place"],
        vec!["verify"],
        vec!["profile"],
    ] {
        let result = p.cli(&args);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

const CHUNK_VIEW_LOOP_SOURCE: &str = include_str!("../design/charon-trial/chunk-view-loop/loop.rs");
const CHUNK_VIEW_LOOP_PROOF: &str =
    include_str!("../design/charon-trial/chunk-view-loop/loop.click");

fn chunk_view_loop_project() -> Project {
    let p = Project::isolated(CHUNK_VIEW_LOOP_SOURCE);
    for (name, bytes) in [
        ("loop.rs", CHUNK_VIEW_LOOP_SOURCE.as_bytes()),
        ("borrow.click", CHUNK_VIEW_LOOP_PROOF.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/chunk-view-loop/loop.click.import.json")
                .as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/chunk-view-loop/loop.click.import.json.lock")
                .as_slice(),
        ),
        (
            "loop.ullbc",
            include_bytes!("../design/charon-trial/chunk-view-loop/loop.ullbc").as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn charon_chunk_view_loop_reborrows_shared_subslices_at_symbolic_heads() {
    let p = chunk_view_loop_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHUNK_VIEW_LOOP_PROOF, &prepared).unwrap();
    for (before, after) in [
        ("views bytes[0..16];", ""),
        ("views bytes[0..4];", "views bytes[0..17];"),
        (
            "invariant __rust_mir_6_cursor == bytes + (16u64 - __rust_mir_6_remaining);",
            "invariant __rust_mir_6_cursor == bytes + (17u64 - __rust_mir_6_remaining);",
        ),
        ("ensures result == 0u32;", "ensures result == 1u32;"),
    ] {
        let invalid = CHUNK_VIEW_LOOP_PROOF.replace(before, after);
        assert_ne!(invalid, CHUNK_VIEW_LOOP_PROOF);
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "accepted {before} -> {after}"
        );
    }
}

#[test]
#[ignore = "nightly: shared chunk-loop proof-tool agreement"]
fn charon_chunk_view_loop_tools_recheck_expanded_certificate() {
    let p = chunk_view_loop_project();
    for args in [
        vec!["verify"],
        vec!["expand", "--claim", "walk.contract", "--in-place"],
        vec!["verify"],
        vec!["profile"],
    ] {
        let result = p.cli(&args);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

const CHUNK_LANE_SOURCE: &str = include_str!("../design/charon-trial/chunk-lane-results/quad.rs");
const CHUNK_LANE_PROOF: &str = include_str!("../design/charon-trial/chunk-lane-results/quad.click");

fn chunk_lane_project() -> Project {
    let p = Project::isolated(CHUNK_LANE_SOURCE);
    for (name, bytes) in [
        ("quad.rs", CHUNK_LANE_SOURCE.as_bytes()),
        ("borrow.click", CHUNK_LANE_PROOF.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/chunk-lane-results/quad.click.import.json")
                .as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/chunk-lane-results/quad.click.import.json.lock")
                .as_slice(),
        ),
        (
            "quad.ullbc",
            include_bytes!("../design/charon-trial/chunk-lane-results/quad.ullbc").as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn charon_chunk_lane_results_survive_local_stores_at_symbolic_heads() {
    let p = chunk_lane_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHUNK_LANE_PROOF, &prepared).unwrap();
    for (before, after) in [
        (
            "have lanes.lanes[1] == chunk[1]",
            "have lanes.lanes[1] == chunk[0]",
        ),
        (
            "have lanes.lanes[2] == chunk[2]",
            "have lanes.lanes[2] == chunk[3]",
        ),
        (
            "have lanes.lanes[3] == chunk[3]",
            "have lanes.lanes[3] == chunk[3] + 1u32",
        ),
        (
            "have to_integer(lanes.lanes[0]) == to_integer((int32)chunk[0])",
            "have to_integer(lanes.lanes[0]) == to_integer((int32)chunk[1])",
        ),
        (
            "have to_integer(lanes.lanes[3]) == to_integer((int32)chunk[3])",
            "have to_integer(lanes.lanes[3]) == to_integer((int32)chunk[3]) + 1",
        ),
        ("views bytes[0..16];", ""),
    ] {
        let invalid = CHUNK_LANE_PROOF.replace(before, after);
        assert_ne!(invalid, CHUNK_LANE_PROOF);
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "accepted {before} -> {after}"
        );
    }
}

#[test]
#[ignore = "nightly: chunk lane-result proof-tool agreement"]
fn charon_chunk_lane_results_tools_recheck_expanded_certificate() {
    let p = chunk_lane_project();
    for args in [
        vec!["verify"],
        vec!["expand", "--claim", "quad::walk.contract", "--in-place"],
        vec!["verify"],
        vec!["profile"],
    ] {
        let result = p.cli(&args);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

const LOOP_ARRAY_COPY_SOURCE: &str = include_str!("../design/charon-trial/loop-array-copy/quad.rs");
const LOOP_ARRAY_COPY_PROOF: &str =
    include_str!("../design/charon-trial/loop-array-copy/quad.click");

fn loop_array_copy_project() -> Project {
    let p = Project::isolated(LOOP_ARRAY_COPY_SOURCE);
    for (name, bytes) in [
        ("quad.rs", LOOP_ARRAY_COPY_SOURCE.as_bytes()),
        ("borrow.click", LOOP_ARRAY_COPY_PROOF.as_bytes()),
        (
            "borrow.click.import.json",
            include_bytes!("../design/charon-trial/loop-array-copy/quad.click.import.json")
                .as_slice(),
        ),
        (
            "borrow.click.import.json.lock",
            include_bytes!("../design/charon-trial/loop-array-copy/quad.click.import.json.lock")
                .as_slice(),
        ),
        (
            "quad.ullbc",
            include_bytes!("../design/charon-trial/loop-array-copy/quad.ullbc").as_slice(),
        ),
    ] {
        fs::write(p.root.join(name), bytes).unwrap();
    }
    p
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn charon_loop_array_copy_survives_symbolic_heads() {
    let p = loop_array_copy_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(LOOP_ARRAY_COPY_PROOF, &prepared).unwrap();
    for (before, after) in [
        ("have array[1] == chunk[1]", "have array[1] == chunk[0]"),
        ("have array[2] == chunk[2]", "have array[2] == chunk[3]"),
        (
            "have array[3] == chunk[3]",
            "have array[3] == chunk[3] + 1u32",
        ),
        ("views bytes[0..16];", ""),
    ] {
        let invalid = LOOP_ARRAY_COPY_PROOF.replace(before, after);
        assert_ne!(invalid, LOOP_ARRAY_COPY_PROOF);
        assert!(
            C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err(),
            "accepted {before} -> {after}"
        );
    }
}

#[test]
fn charon_loop_array_copy_empty_input_never_reads_uninitialized_storage() {
    let p = loop_array_copy_project();
    let prepared = load_import(&p.config()).unwrap();
    let helper = LOOP_ARRAY_COPY_PROOF
        .split_once("fn quad::walk")
        .expect("the sidecar states `walk` after its helper")
        .0;
    let claim = format!(
        "{helper} fn quad::walk(bytes: &[u8]) -> u32 {{ requires bytes.len() == 0u64; ensures result == 0u32; }} by {{ execute(); simp(); }}"
    );
    C0VerificationSession::new_program_prepared(&claim, &prepared).unwrap();
}

#[test]
#[ignore = "nightly: loop-local array copy proof-tool agreement"]
fn charon_loop_array_copy_results_tools_recheck_expanded_certificate() {
    let p = loop_array_copy_project();
    for args in [
        vec!["verify"],
        vec![
            "expand",
            "--claim",
            "__rust_q_I4_quad_I4_walk.contract",
            "--in-place",
        ],
        vec!["verify"],
        vec!["profile"],
    ] {
        let result = p.cli(&args);
        assert!(
            result.status.success(),
            "{}",
            String::from_utf8_lossy(&result.stderr)
        );
    }
}

const CHARON_LOOP_SIDECAR: &str = include_str!("../design/charon-trial/borrowed-loop/loop.click");
fn charon_loop_project() -> Project {
    let p = Project::new(CHARON_LOOP_SOURCE);
    fs::write(p.root.join("loop.rs"), CHARON_LOOP_SOURCE).unwrap();
    fs::write(p.root.join("borrow.click"), CHARON_LOOP_SIDECAR).unwrap();
    fs::write(
        p.config(),
        include_bytes!("../design/charon-trial/borrowed-loop/loop.click.import.json"),
    )
    .unwrap();
    fs::write(
        p.root.join("loop.ullbc"),
        include_bytes!("../design/charon-trial/borrowed-loop/loop.ullbc"),
    )
    .unwrap();
    fs::write(
        p.config().with_file_name("borrow.click.import.json.lock"),
        include_bytes!("../design/charon-trial/borrowed-loop/loop.click.import.json.lock"),
    )
    .unwrap();
    p
}
#[test]
#[ignore = "nightly: 9s in the parallel gate"]
fn charon_borrowed_loop_checks_restoration_bounds_and_ranking() {
    let p = charon_loop_project();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_LOOP_SIDECAR, &prepared).unwrap();
    for n in [0, 1, 2147483647] {
        let concrete =
            CHARON_LOOP_SIDECAR.replace("requires n >= 0;", &format!("requires n == {n};"));
        C0VerificationSession::new_program_prepared(&concrete, &prepared).unwrap();
    }
    for invalid in [
        CHARON_LOOP_SIDECAR.replace("result == n", "result == n + 1"),
        CHARON_LOOP_SIDECAR.replace("value[0] == old(value[0])", "value[0] == 7"),
        CHARON_LOOP_SIDECAR.replace("requires n >= 0;", "requires n == -1;"),
        CHARON_LOOP_SIDECAR.replace(
            "invariant 0 <= i and i <= n;",
            "invariant 0 <= i and i < n;",
        ),
        CHARON_LOOP_SIDECAR.replace("decreases n - i;", "decreases i;"),
        CHARON_LOOP_SIDECAR.replace("    owns value[0..1];\n", ""),
        CHARON_LOOP_SIDECAR.replace("execute_until(loop(0))", "execute_until(loop(99))"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn charon_borrowed_loop_cli_expands_checked_loop_certificate() {
    let p = charon_loop_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    assert_cli(
        &p,
        &["expand", "--claim", "guarded_walk.contract", "--in-place"],
    );
    assert_cli(&p, &["verify"]);
    fs::write(
        p.root.join("borrow.click"),
        CHARON_LOOP_SIDECAR.replace("requires n >= 0;", "requires n == 0;"),
    )
    .unwrap();
    assert_cli(&p, &["verify"]);
    assert_cli(
        &p,
        &["expand", "--claim", "guarded_walk.contract", "--in-place"],
    );
    assert_cli(&p, &["verify"]);
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler"]
fn charon_borrowed_loop_live_refresh_and_rejected_control_flow() {
    let p = charon_loop_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_LOOP_SIDECAR, &prepared).unwrap();
    for (source, diagnostic) in [
        (
            CHARON_LOOP_SOURCE.replace(
                "        *slot = i;",
                "        *value = 0;\n        *slot = i;",
            ),
            "E0506",
        ),
        (
            "pub fn bad(n:i32) { let mut i=0; while i<n { if i==2 { break; } i+=1; } }".into(),
            "extra exit",
        ),
        (
            "pub fn bad(n:&i32) { let mut i=0; while i<*n { i+=1; } }".into(),
            "pure scalar",
        ),
    ] {
        fs::remove_file(p.root.join("loop.ullbc")).unwrap();
        fs::write(p.root.join("loop.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!p.root.join("loop.ullbc").exists());
        fs::write(p.root.join("loop.rs"), CHARON_LOOP_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn charon_trial_checks_arithmetic_and_owned_cleanup_through_shared_engine() {
    let p = charon_project();
    let prepared = load_import(&p.config()).unwrap();
    assert!(
        prepared
            .export()
            .functions
            .iter()
            .all(|f| f.mir.is_some() && f.body.is_empty())
    );
    C0VerificationSession::new_program_prepared(CHARON_SIDECAR, &prepared).unwrap();
    for invalid in [
        CHARON_SIDECAR.replace("result == x + 1", "result == x + 2"),
        CHARON_SIDECAR.replace("    requires x < 65535;\n", ""),
        CHARON_SIDECAR.replace(
            "fn guarded_increment(x: u16, value: &mut i32, early: bool) -> u16 {\n    requires x < 65535;",
            "fn guarded_increment(x: u16, value: &mut i32, early: bool) -> u16 {",
        ),
        CHARON_SIDECAR.replace("value[0] == old(value[0])", "value[0] == 7"),
        CHARON_SIDECAR.replace("    owns value[0..1];\n", ""),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}
#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn charon_trial_cli_tools_and_expanded_certificate_agree() {
    let p = charon_project();
    for command in ["verify", "profile", "audit"] {
        assert_cli(&p, &[command]);
    }
    assert_cli(
        &p,
        &[
            "expand",
            "--claim",
            "guarded_increment.contract",
            "--in-place",
        ],
    );
    assert_cli(&p, &["verify"]);
}
#[test]
fn charon_trial_lock_rejects_source_and_profile_changes() {
    let p = charon_project();
    fs::write(
        p.root.join("trial.rs"),
        format!("{CHARON_SOURCE}\n// changed"),
    )
    .unwrap();
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("lock differs")
    );
    fs::write(p.root.join("trial.rs"), CHARON_SOURCE).unwrap();
    let c = fs::read(p.config()).unwrap();
    fs::write(
        p.config(),
        String::from_utf8(c)
            .unwrap()
            .replace("charon-trial", "other"),
    )
    .unwrap();
    assert!(load_import(&p.config()).is_err());
}
#[test]
#[ignore = "requires the separately built pinned Charon/compiler; run explicitly after scripts/build-charon.sh"]
fn charon_trial_live_refresh_and_compiler_rejections() {
    let p = charon_project();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(p.config()).unwrap()).unwrap();
    config["exporter"] = serde_json::json!(
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("target/charon/debug/charon")
    );
    fs::write(p.config(), serde_json::to_vec(&config).unwrap()).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(CHARON_SIDECAR, &prepared).unwrap();
    for (source, expected) in [
        (
            include_str!("../design/borrow-probes/charon-borrow-rejected.rs"),
            "E0506",
        ),
        (
            include_str!("../design/borrow-probes/charon-move-rejected.rs"),
            "E0382",
        ),
        ("pub fn unsupported(x: u64) -> u64 { x }", "integer width"),
    ] {
        fs::remove_file(p.root.join("trial.ullbc")).unwrap();
        fs::write(p.root.join("trial.rs"), source).unwrap();
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(expected), "{error}");
        assert!(!p.root.join("trial.ullbc").exists());
        fs::write(p.root.join("trial.rs"), CHARON_SOURCE).unwrap();
        refresh_import(&p.config()).unwrap();
    }
}
#[test]
#[ignore = "nightly: 1.3s in the parallel gate; other gate tests reach the same code"]
fn rust_typed_import_verifies_borrow_parent_reuse_and_field_frame() {
    let p = gate_fixtures::project("basic", SOURCE);
    let prepared = load_import(&p.config()).unwrap();
    let (_, verified) = C0VerificationSession::new_program_prepared(SIDECAR, &prepared).unwrap();
    assert_eq!(verified.len(), 12);
    let false_claim = SIDECAR.replace("ensures result == 8;", "ensures result == 9;");
    assert!(C0VerificationSession::new_program_prepared(&false_claim, &prepared).is_err());
}
#[test]
fn rust_lock_rejects_changed_source_and_artifact() {
    let p = gate_fixtures::project("basic", SOURCE);
    fs::write(p.root.join("borrow.rs"), format!("{SOURCE}\n// changed")).unwrap();
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("lock differs")
    );
    fs::write(p.root.join("borrow.rs"), SOURCE).unwrap();
    fs::write(p.root.join("borrow.ullbc"), b"{}").unwrap();
    assert!(
        load_import(&p.config())
            .unwrap_err()
            .contains("lock differs")
    );
}
fn assert_native_boundary_proof(source: &str, sidecar: &str) {
    let p = Project::new(source);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared)
        .unwrap_or_else(|error| panic!("{source}: {}", error.message()));
    let false_claim = sidecar.replacen("ensures ", "ensures 0 == 1; ensures ", 1);
    assert_ne!(false_claim, sidecar);
    assert!(C0VerificationSession::new_program_prepared(&false_claim, &prepared).is_err());
    for permission in [
        "owns bytes[0..1];",
        "owns *p;",
        "views bytes[0..2];",
        "owns *bytes;",
    ] {
        if sidecar.contains(permission) {
            assert!(
                C0VerificationSession::new_program_prepared(
                    &sidecar.replace(permission, ""),
                    &prepared
                )
                .is_err()
            );
        }
    }
}

#[test]
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
fn rust_compiler_and_subset_rejections_are_distinct() {
    for (source, diagnostic) in [
        (
            "pub fn bad(p: &mut i32) { let child = &mut *p; *p = 4; *child = 7; }",
            "cannot assign",
        ),
        ("pub fn bad(x: u64) -> u64 { x }", "integer width"),
        (
            "pub fn bad(mut x: i32) -> i32 { loop { x += 1; } }",
            "MIR loop requires a conditional while header",
        ),
        ("mod other; pub fn ok(x:i32)->i32{x}", "compiler exited"),
        (
            "pub fn ok(x:i32)->i32 { include!(\"other.rs\") }",
            "compiler exited",
        ),
        (
            "pub unsafe fn bad(x:i32)->i32{x}",
            "unsafe, foreign, or generic",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "expected {diagnostic}: {error}");
        assert!(!p.root.join("borrow.ullbc").exists());
    }
}
fn assert_cli(p: &Project, args: &[&str]) {
    let result = p.cli(args);
    assert!(
        result.status.success(),
        "{args:?}: stdout: {}\nstderr: {}",
        String::from_utf8_lossy(&result.stdout),
        String::from_utf8_lossy(&result.stderr)
    );
}
#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_ordinary_cli_locks_and_verifies() {
    let p = Project::new(SOURCE);
    assert_cli(&p, &["import", "lock"]);
    assert_cli(&p, &["verify"]);
}
#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn rust_cli_profile_and_audit_use_the_shared_engine() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
}
#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn rust_cli_expansion_reverifies_through_ordinary_entry() {
    let p = Project::new(SOURCE);
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["expand", "--claim", "update.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_checked_arithmetic_requires_a_panic_freedom_bound() {
    let p = Project::new("pub fn increment(x:i32)->i32 { x + 1 }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let claim = "verifying \"borrow.rs\"; fn increment(x: i32) -> i32 { ensures result == x + 1; } by { execute(); simp(); }";
    assert!(C0VerificationSession::new_program_prepared(claim, &prepared).is_err());
    let bounded = claim.replace("ensures result", "requires x < 2147483647; ensures result");
    C0VerificationSession::new_program_prepared(&bounded, &prepared).unwrap();
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_boolean_return_and_local_initialization_verify() {
    let p = Project::new("pub fn invert(x:bool)->bool { let answer = !x; answer }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let claim = "verifying \"borrow.rs\"; fn invert(x: bool) -> bool { ensures result == (if x != 0 { 0 } else { 1 }); } by { if x == 0 { execute(); simp(); } else { execute(); simp(); } }";
    C0VerificationSession::new_program_prepared(claim, &prepared).unwrap();
}

const MOVE_SOURCE: &str = include_str!("../examples/rust-move-drop/guard.rs");
const MOVE_SIDECAR: &str = include_str!("../examples/rust-move-drop/guard.click");
fn moves_project(source: &str) -> (Project, String) {
    let p = Project::new(source);
    let sidecar = MOVE_SIDECAR.replace("guard.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    (p, sidecar)
}
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn rust_moves_drop_effect_and_return_capture_verify() {
    let (p, sidecar) = moves_project(MOVE_SOURCE);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for wrong in [
        sidecar.replace("ensures *value == old(*value);", "ensures *value == 7;"),
        sidecar.replace(
            "ensures *self.slot == old(self.saved);",
            "ensures *self.slot == 7;",
        ),
        sidecar.replace(
            "ensures result == (if early != 0 { 7 } else { 9 });",
            "ensures result == old(*value);",
        ),
        sidecar[sidecar.find("fn restore").unwrap()..]
            .to_string()
            .replace("fn restore", "verifying \"borrow.rs\"; fn restore"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&wrong, &prepared).is_err());
    }
    assert_eq!(
        fs::read_to_string(p.root.join("borrow.rs")).unwrap(),
        MOVE_SOURCE
    );
}
#[test]
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
fn rust_move_borrow_conflicts_and_partial_moves_fail_closed() {
    assert_native_boundary_proof(
        "pub struct S<'a> {pub p:&'a mut i32} pub fn bad(p:&mut i32) {let a=S{p};let moved=a.p;*moved=4;}",
        "verifying \"borrow.rs\"; fn bad(p: &mut i32) { owns *p; ensures *p == 4; } by { execute(); simp(); }",
    );

    for (source, diagnostic) in [
        (
            "pub struct S {pub x:i32} pub fn bad()->i32 {let a=S{x:1};let b=a; a.x}",
            "use of moved value",
        ),
        (
            "pub struct S {pub x:i32} pub fn bad()->i32 {let a=S{x:1};let r=&a;let b=a;r.x}",
            "cannot move out",
        ),
        (
            "pub struct S {pub x:i32} pub fn bad(a:S)->i32 {a.x}",
            "Rust value type",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
    }
}
#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn rust_move_drop_cli_proofs_expand_and_reverify() {
    let (p, _) = moves_project(MOVE_SOURCE);
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["expand", "--claim", "restore.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_conditional_move_and_explicit_drop_verify() {
    let source = format!(
        "{}    if early {{ let moved = guard; *moved.slot = 7; std::mem::drop(moved); 7 }}\n    else {{ *guard.slot = 9; 9 }}\n}}\n",
        MOVE_SOURCE.split("    let moved = guard;").next().unwrap()
    );
    let (p, sidecar) = moves_project(&source);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_owned_field_loan_recovery_verifies() {
    // Preserve the ordinary Rust source that exposed fragmented ownership at
    // the outer destructor call. Do not alter it to make the proof pass.
    let source = format!(
        "{}pub fn cleanup(value:&mut i32) {{ let mut first = Guard {{slot:value,saved:1}}; let second = Guard {{slot:&mut first.saved,saved:42}}; }}",
        MOVE_SOURCE.split("pub fn restore").next().unwrap()
    );
    let (p, _) = moves_project(&source);
    let sidecar = format!("{}fn cleanup(value: &mut i32) {{ owns *value; ensures *value == 42; }} by {{ execute(); simp(); }}", MOVE_SIDECAR.split("fn restore").next().unwrap()).replace("guard.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("*value == 42", "*value == 1"),
            &prepared
        )
        .is_err()
    );
    assert_eq!(
        fs::read_to_string(p.root.join("borrow.rs")).unwrap(),
        source
    );
}

#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn rust_owned_field_loan_cli_expands_and_reverifies() {
    let p = Project::new(include_str!("../examples/rust-field-borrow/guard.rs"));
    fs::write(
        p.root.join("borrow.click"),
        include_str!("../examples/rust-field-borrow/guard.click").replace("guard.rs", "borrow.rs"),
    )
    .unwrap();
    refresh_import(&p.config()).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "cleanup.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_owned_field_parent_can_write_after_explicit_child_drop() {
    let source = format!(
        "{}pub fn cleanup(value:&mut i32) {{ let mut first = Guard {{slot:value,saved:1}}; let second = Guard {{slot:&mut first.saved,saved:42}}; std::mem::drop(second); first.saved = 43; }}",
        MOVE_SOURCE.split("pub fn restore").next().unwrap()
    );
    let (p, _) = moves_project(&source);
    let sidecar = format!("{}fn cleanup(value: &mut i32) {{ owns *value; ensures *value == 43; }} by {{ execute(); simp(); }}", MOVE_SIDECAR.split("fn restore").next().unwrap()).replace("guard.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_owned_disjoint_mutable_fields_verify() {
    let source = "pub struct Pair {pub x:i32,pub y:i32} pub fn set(left:&mut i32,right:&mut i32) {*left=7;*right=9;} pub fn fields()->i32 {let mut pair=Pair{x:1,y:2}; let left=&mut pair.x; let right=&mut pair.y; set(left,right); if pair.y == 9 {pair.x} else {0}}";
    let p = Project::new(source);
    let sidecar = "verifying \"borrow.rs\"; fn set(left: &mut i32, right: &mut i32) {owns *left;owns *right;ensures *left==7;ensures *right==9;} by {execute();simp();} fn fields() -> i32 {ensures result==7;} by {execute();simp();}";
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("result==7", "result==0"),
            &prepared
        )
        .is_err()
    );
}

#[test]
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
fn rust_owned_field_conflicting_parent_access_is_rejected_by_compiler() {
    let prefix = MOVE_SOURCE.split("pub fn restore").next().unwrap();
    for (suffix, diagnostic) in [
        ("first.saved=5; std::mem::drop(second);", "cannot assign"),
        (
            "std::mem::drop(first); std::mem::drop(second);",
            "cannot move out",
        ),
        (
            "std::mem::drop(second); *second.slot=5;",
            "use of moved value",
        ),
    ] {
        let source = format!(
            "{prefix}pub fn bad(value:&mut i32) {{ let mut first=Guard{{slot:value,saved:1}}; let second=Guard{{slot:&mut first.saved,saved:42}}; {suffix} }}"
        );
        let p = Project::new(&source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert_eq!(
            fs::read_to_string(p.root.join("borrow.rs")).unwrap(),
            source
        );
    }
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_moves_plain_struct_and_reads_destination() {
    let p =
        Project::new("pub struct S {pub x:i32} pub fn plain()->i32 {let a=S{x:17}; let b=a; b.x}");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(
        "verifying \"borrow.rs\"; fn plain() -> i32 {ensures result == 17;} by {execute(); simp();}",
        &prepared,
    )
    .unwrap();
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_two_guards_clean_up_in_reverse_construction_order() {
    use click::languages::rust::schema::{MirStatement as S, MirTerminator as T};
    let source = format!(
        "{}pub fn cleanup(left:&mut i32,right:&mut i32) {{ let first=Guard{{slot:left,saved:17}}; let second=Guard{{slot:right,saved:42}}; }}",
        MOVE_SOURCE.split("pub fn restore").next().unwrap()
    );
    let (p, _) = moves_project(&source);
    let sidecar = format!("{}fn cleanup(left: &mut i32, right: &mut i32) {{ owns *left; owns *right; ensures *left == 17; ensures *right == 42; }} by {{ execute(); simp(); }}", MOVE_SIDECAR.split("fn restore").next().unwrap()).replace("guard.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    let mir = prepared
        .export()
        .functions
        .iter()
        .find(|f| f.name == "cleanup")
        .unwrap()
        .mir
        .as_ref()
        .unwrap();
    let constructors = mir
        .blocks
        .iter()
        .flat_map(|b| &b.statements)
        .filter_map(|s| match s {
            S::Initialize { target, .. } => Some(target.clone()),
            _ => None,
        })
        .collect::<Vec<_>>();
    let mut drops = Vec::new();
    let mut block = 0;
    loop {
        match &mir.blocks[block].terminator {
            T::Drop { local, target, .. } => {
                drops.push(local.clone());
                block = *target;
            }
            T::Goto { target } => block = *target,
            T::Return => break,
            _ => panic!("unexpected cleanup edge"),
        }
    }
    assert_eq!(drops, constructors.into_iter().rev().collect::<Vec<_>>());
}

const UNSIGNED_SOURCE: &str = include_str!("../examples/rust-unsigned/arithmetic.rs");
const UNSIGNED_SIDECAR: &str = include_str!("../examples/rust-unsigned/arithmetic.click");

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn rust_unsigned_arithmetic_and_expansion_verify() {
    let p = Project::new(UNSIGNED_SOURCE);
    let sidecar = UNSIGNED_SIDECAR.replace("arithmetic.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let (_, verified) = C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_eq!(verified.len(), 9);
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures result == 0;", "ensures result == 1;"),
            &prepared
        )
        .is_err()
    );
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "add_byte.contract",
        "shifted_byte.contract",
        "low_byte.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

/// A method's contract sits in an `impl` block and its receiver is `self`.
/// This is the contract `examples/rust-field-borrow` states for the free
/// function `Guard_drop(struct Guard* self)`.
#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn rust_sidecar_impl_blocks_verify() {
    let p = Project::new(FIELD_BORROW_GUARD_SOURCE);
    let sidecar = include_str!("fixtures/rust-verification/impl_blocks.click");
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace(
                "ensures *self.slot == old(self.saved);",
                "ensures *self.slot == old(self.saved) + 1;"
            ),
            &prepared
        )
        .is_err()
    );
    assert_cli(&p, &["verify"]);
    // The tools address a method by the function it is.
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(
        &p,
        &["expand", "--claim", "Guard_drop.contract", "--in-place"],
    );
    assert_cli(&p, &["verify"]);
}

/// A slice parameter in a Rust signature is one name: `bytes.len()` is its
/// length. These are the contracts `examples/rust-slices` states in C shape,
/// where the slice is a pointer and a `bytes_len` parameter.
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn rust_sidecar_slices_in_rust_syntax_verify() {
    let p = Project::new(SLICES_SOURCE);
    let sidecar = include_str!("fixtures/rust-verification/slices.click");
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    // A read past the stated length is still refused.
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace(
                "requires index < bytes.len();",
                "requires index <= bytes.len();"
            ),
            &prepared
        )
        .is_err()
    );
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "read.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

/// `&mut T` and `&T` parameters in a Rust signature. The contract names a
/// referent `*value` and a field `parent.left`; these are the contracts
/// `examples/basic-rust` states in C shape.
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_sidecar_references_in_rust_syntax_verify() {
    let p = Project::new(SOURCE);
    let sidecar = include_str!("fixtures/rust-verification/references.click");
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let (_, verified) = C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert_eq!(verified.len(), 12);
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures *value == 8;", "ensures *value == 9;"),
            &prepared
        )
        .is_err()
    );
    // A store through the reference needs `owns`, not `views`.
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("owns *value;", "views *value;"),
            &prepared
        )
        .is_err()
    );
    assert_cli(&p, &["verify"]);
}

/// A Rust sidecar states signatures as Rust does and casts with `as`. The
/// contracts are the ones `examples/rust-unsigned` states in C shape.
#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_sidecar_signatures_in_rust_syntax_verify() {
    let p = Project::new(UNSIGNED_SOURCE);
    let sidecar = include_str!("fixtures/rust-verification/fn_signatures.click");
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let (_, verified) = C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert_eq!(verified.len(), 3);
    // The signature is still checked against the imported function.
    let error = C0VerificationSession::new_program_prepared(
        &sidecar.replace("byte: u8", "byte: u32"),
        &prepared,
    )
    .err()
    .expect("the sidecar states another parameter type");
    assert!(error.message().contains("add_byte"), "{}", error.message());
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("value * 3u32", "value * 4u32"),
            &prepared
        )
        .is_err()
    );
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 23 s, over the gate's per-test budget (2026-10-06)"]
fn rust_unsigned_panic_paths_are_rejected() {
    for (ty, expression, precondition) in [
        ("u32", "x + 1", "x == 4294967295u32"),
        ("u8", "x + 1", "x == 255"),
        ("u32", "x - 1", "x == 0"),
        ("u8", "x - 1", "x == 0"),
        ("u32", "x * 2", "x == 4294967295u32"),
        ("u8", "x * 2", "x == 255"),
        ("u32", "1 / x", "x == 0"),
        ("u8", "1 % x", "x == 0"),
        ("u32", "1 << x", "x == 32"),
        ("u8", "1 >> x", "x == 8"),
    ] {
        let p = Project::new(&format!("pub fn bad(x:{ty})->{ty} {{ {expression} }}"));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn bad(x: {ty}) -> {ty} {{ requires {precondition}; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        assert!(
            C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
            "accepted {expression} at {precondition}"
        );
    }
}

#[test]
#[ignore = "nightly: 13 s, over the gate's per-test budget (2026-10-06)"]
fn rust_unsigned_nested_checks_and_short_circuit_preserve_panics() {
    for (expression, rust_type, valid) in [
        ("(x + 1) as u8", "u8", false),
        ("false && x + 1 > 0", "bool", true),
        ("true || x + 1 > 0", "bool", true),
        ("true && x + 1 > 0", "bool", false),
        ("false || x + 1 > 0", "bool", false),
    ] {
        let p = Project::new(&format!(
            "pub fn check(x:u32)->{rust_type} {{ {expression} }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn check(x: u32) -> {rust_type} {{ requires x == 4294967295u32; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        let result = C0VerificationSession::new_program_prepared(&sidecar, &prepared);
        assert_eq!(result.is_ok(), valid, "{expression}: {:?}", result.err());
    }
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_unsigned_casts_bitwise_and_assignments_verify() {
    let p = Project::new(
        "pub fn bits(mut x:u8)->u8 { x ^= 255; x &= 254; x |= 1; !x } pub fn narrow(x:i32)->u8 { x as u8 } pub fn signed(x:u32)->i32 { x as i32 } pub fn shift(x:u32, n:i32)->u32 { x >> n } pub fn byte_count(x:u32, n:u8)->u32 { x << n }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
fn bits(x: u8) -> u8 { requires x == 128; ensures result == 128; } by { execute(); simp(); }
fn narrow(x: i32) -> u8 { requires x == -1; ensures result == 255; } by { execute(); simp(); }
fn signed(x: u32) -> i32 { requires x == 4294967295u32; ensures result == -1; } by { execute(); simp(); }
fn shift(x: u32, n: i32) -> u32 { requires x == 4294967295u32; requires n == 31; ensures result == 1u32; } by { execute(); simp(); }
fn byte_count(x: u32, n: u8) -> u32 { requires n < 32u32; ensures result == (x << n as u32); } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("n == 31", "n == -1"),
            &prepared
        )
        .is_err()
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_unsigned_references_and_byte_field_layout_verify() {
    let p = Project::new(
        "pub struct Pair { pub byte:u8, pub word:u32 } pub fn write(p:&mut u8, q:&mut u32) { *p = 255; *q = 4294967295; } pub fn field(p:&mut Pair) { p.byte = 7; }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
fn write(p: &mut u8, q: &mut u32) { owns *p; owns *q; ensures *p == 255; ensures *q == 4294967295u32; } by { execute(); simp(); }
fn field(p: &mut Pair) { owns p.byte; owns p.word; ensures p.byte == 7; ensures p.word == old(p.word); } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
}

const SLICES_SOURCE: &str = include_str!("../examples/rust-slices/bytes.rs");
const SLICES_SIDECAR: &str = include_str!("../examples/rust-slices/bytes.click");

#[test]
fn rust_split_at_metadata_and_reads_verify() {
    let p = gate_fixtures::project("split", include_str!("../examples/rust-split-at/split.rs"));
    let sidecar =
        include_str!("../examples/rust-split-at/split.click").replace("split.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert!(prepared.export().functions.iter().flat_map(|f| f.mir.as_ref().unwrap().blocks.iter()).flat_map(|b| &b.statements).any(|s|
        matches!(s, click::languages::rust::schema::MirStatement::SliceSplit { left, right, .. } if left != right)));
    for incorrect in [
        sidecar.replace("ensures result == mid;", "ensures result == 0u64;"),
        sidecar.replace(
            "ensures result == bytes.len() - mid;",
            "ensures result == mid;",
        ),
        sidecar.replace(
            "ensures result == bytes[mid];",
            "ensures result == bytes[0];",
        ),
        sidecar.replace("views bytes[0..bytes.len()];", ""),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&incorrect, &prepared).is_err());
    }
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_split_at_endpoints_and_full_width_lengths_verify() {
    let p = Project::new(
        "pub fn length(bytes: &[u8], mid: usize) -> usize { let (left, right) = bytes.split_at(mid); right.len() }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for (length, midpoint) in [
        (0u64, 0u64),
        (4, 0),
        (4, 4),
        (2147483647, 2147483647),
        (4294967296, 1),
        (u64::MAX, 0),
    ] {
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn length(bytes: &[u8], mid: usize) -> usize {{ requires bytes.len() == {length}u64; requires mid == {midpoint}u64; ensures result == {}u64; }} by {{ execute(); simp(); }}",
            length - midpoint
        );
        C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    }
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_split_at_checks_its_bound_at_full_width() {
    let p = Project::new(
        "pub fn length(bytes: &[u8], mid: usize) -> usize { let (left, right) = bytes.split_at(mid); right.len() }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = |length: u64, midpoint: u64| {
        format!(
            "verifying \"borrow.rs\"; fn length(bytes: &[u8], mid: usize) -> usize {{ requires bytes.len() == {length}u64; requires mid == {midpoint}u64; ensures result == result; }} by {{ execute(); simp(); }}"
        )
    };
    // A midpoint past the length panics, whatever its width.
    for (length, midpoint) in [(0u64, 1u64), (4, 5), (4, 4294967296)] {
        let error =
            C0VerificationSession::new_program_prepared(&sidecar(length, midpoint), &prepared)
                .err()
                .expect("invalid split must fail");
        assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
        assert!(
            error.message().contains("Rust split_at panic check"),
            "{}",
            error.message()
        );
    }
    // A midpoint at a length past 32 bits splits: the offset is a 64-bit
    // element index, with no narrower bound on it (`design/typed-indices.md`).
    for (length, midpoint) in [(u64::MAX, u64::MAX), (4294967296, 4294967296)] {
        C0VerificationSession::new_program_prepared(&sidecar(length, midpoint), &prepared)
            .unwrap_or_else(|error| panic!("{length}, {midpoint}: {}", error.message()));
    }
}

#[test]
#[ignore = "nightly: 14 s, over the gate's per-test budget (2026-10-06)"]
fn rust_split_at_rejects_unsupported_results_and_mutation() {
    assert_native_boundary_proof(
        "pub fn bad(bytes: &[u8]) { let pair = bytes.split_at(1); }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8]) { requires bytes.len() == 4u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(bytes: &[u8; 4]) { let (left, right) = bytes.split_at(1); }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8; 4]) {  ensures 1 == 1; } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(bytes: &mut [u8]) { let (left, right) = bytes.split_at(1); }",
        "verifying \"borrow.rs\"; fn bad(bytes: &mut [u8]) { requires bytes.len() == 4u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(bytes: &[u8]) { let (left, _) = bytes.split_at(1); }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8]) { requires bytes.len() == 4u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    for (source, message) in [
        (
            "pub fn bad(bytes: &[u8]) { let (left, right) = bytes.split_at(1); right[0] = 7; }",
            "cannot assign",
        ),
        (
            "pub fn bad(bytes: &mut [u8]) { let (left, right) = bytes.split_at_mut(1); }",
            "does not support type",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(message), "expected {message}: {error}");
        assert!(!p.root.join("borrow.ullbc").exists());
    }
}

#[test]
#[ignore = "nightly: 12 s, over the gate's per-test budget (2026-10-06)"]
fn rust_split_at_empty_results_reject_indexing() {
    for (length, midpoint, result_slice) in [
        (0u64, 0u64, "left"),
        (0, 0, "right"),
        (4, 0, "left"),
        (4, 4, "right"),
    ] {
        let p = Project::new(&format!(
            "pub fn read(bytes: &[u8], mid: usize) -> u8 {{ let (left, right) = bytes.split_at(mid); {result_slice}[0] }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn read(bytes: &[u8], mid: usize) -> u8 {{ requires bytes.len() == {length}u64; requires mid == {midpoint}u64; views bytes[0..{length}]; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("empty result read must fail");
        assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
        assert!(
            error.message().contains("Rust slice index panic check"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn rust_split_at_calls_nested_splits_aliases_and_argument_evaluation_verify() {
    let p = Project::new(
        r#"
pub fn first(bytes: &[u8]) -> u8 { bytes[0] }
pub fn nested(bytes: &[u8]) -> u8 {
    let (left, right) = bytes.split_at(1);
    let (prefix, suffix) = right.split_at(1);
    let alias = suffix;
    first(alias)
}
pub fn retarget(bytes: &[u8]) -> usize {
    let (mut left, right) = bytes.split_at(1);
    left = right;
    left.len()
}
pub fn shadow(bytes: &[u8]) -> usize {
    let (bytes, tail) = bytes.split_at(bytes.len() - 1);
    bytes.len()
}
pub fn next(counter: &mut u32) -> usize {
    let old = *counter;
    *counter += 1;
    old as usize
}
pub fn once(bytes: &[u8], counter: &mut u32) -> usize {
    let (left, right) = bytes.split_at(next(counter));
    right.len()
}
"#,
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = r#"verifying "borrow.rs";
fn first(bytes: &[u8]) -> u8 {
    requires bytes.len() == 2u64;
    views bytes[0..1];
    ensures result == bytes[0];
} by { execute(); simp(); }
fn nested(bytes: &[u8]) -> u8 {
    requires bytes.len() == 4u64;
    views bytes[0..4];
    ensures result == bytes[2];
    ensures bytes[0] == old(bytes[0]);
    ensures bytes[3] == old(bytes[3]);
} by { execute(); simp(); }
fn retarget(bytes: &[u8]) -> usize {
    requires bytes.len() == 4u64;
    ensures result == 3u64;
} by { execute(); simp(); }
fn shadow(bytes: &[u8]) -> usize {
    requires bytes.len() == 4u64;
    ensures result == 3u64;
} by { execute(); simp(); }
fn next(counter: &mut u32) -> usize {
    requires *counter == 1u32;
    owns *counter;
    ensures result == 1u64;
    ensures *counter == 2u32;
} by { execute(); simp(); }
fn once(bytes: &[u8], counter: &mut u32) -> usize {
    requires bytes.len() == 4u64;
    requires *counter == 1u32;
    owns *counter;
    ensures result == 3u64;
    ensures *counter == 2u32;
} by { execute(); simp(); }
"#;
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures *counter == 2u32;", "ensures *counter == 3u32;"),
            &prepared
        )
        .is_err()
    );
    assert_cli(&p, &["expand", "--claim", "once.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn rust_byte_slices_indexing_calls_and_expansion_verify() {
    let p = Project::new(SLICES_SOURCE);
    let sidecar = SLICES_SIDECAR.replace("bytes.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["audit"]);
    for claim in ["read.contract", "write.contract", "length.contract"] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_byte_slices_variable_length_indexing_verify() {
    let p = Project::new("pub fn read(bytes:&[u8], index:usize)->u8 { bytes[index] }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
fn read(bytes: &[u8], index: usize) -> u8 {
    requires index < bytes.len();
    views *bytes;
    ensures result == bytes[index];
} by { execute(); simp(); }";
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "read.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 11 s, over the gate's per-test budget (2026-10-06)"]
fn rust_byte_slices_reject_panics_and_missing_write_authority() {
    for (source, signature, resource, index) in [
        (
            "pub fn bad(bytes:&[u8], index:usize)->u8 { bytes[index] }",
            "fn bad(bytes: &[u8], index: usize) -> u8",
            "views",
            0u64,
        ),
        (
            "pub fn bad(bytes:&[u8], index:usize)->u8 { bytes[index] }",
            "fn bad(bytes: &[u8], index: usize) -> u8",
            "views",
            4,
        ),
        (
            "pub fn bad(bytes:&[u8], index:usize)->u8 { bytes[index] }",
            "fn bad(bytes: &[u8], index: usize) -> u8",
            "views",
            4294967296,
        ),
        (
            "pub fn bad(bytes:&mut [u8], index:usize) { bytes[index] = 7; }",
            "fn bad(bytes: &mut [u8], index: usize)",
            "views",
            1,
        ),
    ] {
        let p = Project::new(source);
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let length = if index == 0 { 0 } else { 4 };
        let sidecar = format!(
            "verifying \"borrow.rs\"; {signature} {{ requires bytes.len() == {length}u64; requires index == {index}u64; {resource} bytes[0..{length}]; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("unsafe slice contract must fail");
        assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
        if resource == "views" && signature.contains("&mut") {
            assert!(error.message().contains("owns"), "{}", error.message());
        } else {
            assert!(
                error.message().contains("Rust slice index panic check"),
                "{}",
                error.message()
            );
        }
    }
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_byte_slices_length_preserves_target_width_and_index_borrows_verify() {
    let p = Project::new(
        "pub fn length(bytes:&[u8])->usize { bytes.len() } pub fn replace(bytes:&mut [u8], index:usize) { let child = &mut bytes[index]; *child = 9; } pub fn shift(x:u32, n:usize)->u32 { x << n }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
fn length(bytes: &[u8]) -> usize { requires bytes.len() == 4294967296u64; ensures result == 4294967296u64; } by { execute(); simp(); }
fn replace(bytes: &mut [u8], index: usize) { requires bytes.len() == 4u64; requires index < 4u64; owns bytes[0..4]; ensures bytes[index] == 9; } by { execute(); simp(); }
fn shift(x: u32, n: usize) -> u32 { requires x == 1u32; requires n == 31u64; ensures result == 2147483648u32; } by { execute(); rewrite(n == 31u64); rewrite(x == 1u32); normalize(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    let error = C0VerificationSession::new_program_prepared(
        &sidecar.replace("n == 31u64", "n == 4294967296u64"),
        &prepared,
    )
    .err()
    .expect("oversized usize shift must fail before truncation");
    assert!(
        error.message().contains("Rust shl panic check"),
        "{}",
        error.message()
    );
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures result == 4294967296u64", "ensures result == 0u64"),
            &prepared
        )
        .is_err()
    );
}

#[test]
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
fn rust_byte_slice_unsupported_shapes_and_borrow_errors_are_refused() {
    assert_native_boundary_proof(
        "pub fn bad(bytes:&[u32])->usize { bytes.len() }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u32]) -> usize { ensures result == bytes.len(); } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(bytes:&mut [u8], index:usize) { bytes[index] += 1; }",
        "verifying \"borrow.rs\"; fn bad(bytes: &mut [u8], index: usize) { requires index < bytes.len(); requires bytes[index] < 255; owns *bytes; ensures bytes[index] == old(bytes[index]) + 1; } by { execute(); simp(); }",
    );

    for (source, message) in [
        (
            "pub fn bad(bytes:&[u8])->&[u8] { bytes }",
            "returns are not supported",
        ),
        (
            "pub fn bad(bytes:&mut [u8]) { let child = &mut *bytes; bytes[0] = 1; child[0] = 2; }",
            "cannot",
        ),
    ] {
        let p = Project::new(source);
        let result = refresh_import(&p.config());
        assert!(result.unwrap_err().contains(message), "{source}");
    }
}

#[test]
fn rust_fixed_array_references_indexing_and_reborrows_verify() {
    let p = gate_fixtures::project("arrays", include_str!("../examples/rust-arrays/arrays.rs"));
    let sidecar =
        include_str!("../examples/rust-arrays/arrays.click").replace("arrays.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();

    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures words[1] == 7u32", "ensures words[1] == 8u32"),
            &prepared
        )
        .is_err()
    );
}

#[test]
#[ignore = "nightly: 11 s, over the gate's per-test budget (2026-10-06)"]
fn rust_fixed_array_indices_reject_panics_before_narrowing() {
    for (length, index) in [(4, 4u64), (4, 4294967296), (0, 0), (4, u64::MAX)] {
        let p = Project::new(&format!(
            "pub fn read(bytes: &[u8; {length}], index: usize) -> u8 {{ bytes[index] }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn read(bytes: &[u8; {length}], index: usize) -> u8 {{ requires index == {index}u64; views bytes[0..{length}]; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("array index must fail");
        assert_eq!(error.kind(), click::surface::ClickErrorKind::Proof);
        assert!(
            error.message().contains("Rust array index panic check"),
            "{}",
            error.message()
        );
    }
}

#[test]
fn rust_fixed_array_access_requires_memory_authority() {
    for (source, signature, resources) in [
        (
            "pub fn read(bytes: &[u8; 4]) -> u8 { bytes[0] }",
            "fn read(bytes: &[u8; 4]) -> u8",
            "",
        ),
        (
            "pub fn write(words: &mut [u32; 3]) { words[1] = 7; }",
            "fn write(words: &mut [u32; 3])",
            "views words[0..3];",
        ),
    ] {
        let fixture = if source.contains("pub fn read") {
            "array-read"
        } else {
            "array-write"
        };
        let p = gate_fixtures::project(fixture, source);
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; {signature} {{ {resources} ensures 1 == 1; }} by {{ execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("array access requires authority");
        assert_eq!(
            error.kind(),
            click::surface::ClickErrorKind::Proof,
            "{}",
            error.message()
        );
        assert!(
            error.message().contains(if resources.is_empty() {
                "views"
            } else {
                "owns"
            }),
            "{}",
            error.message()
        );
    }
}

#[test]
#[ignore = "nightly: 12 s, over the gate's per-test budget (2026-10-06)"]
fn rust_fixed_array_unsupported_shapes_and_conflicting_borrows_are_refused() {
    assert_native_boundary_proof(
        "pub fn bad(bytes: &mut [u8; 4]) { bytes[0] += 1; }",
        "verifying \"borrow.rs\"; fn bad(bytes: &mut [u8; 4]) { requires bytes[0] < 255; owns bytes[0..1]; ensures bytes[0] == old(bytes[0]) + 1; } by { execute(); simp(); }",
    );

    for (source, message) in [
        (
            "pub fn bad(bytes: &[u64; 4]) -> u64 { bytes[0] }",
            "integer width",
        ),
        (
            "pub fn bad(words: &[u32; 536870912]) -> usize { words.len() }",
            "array unsize pointer/length/type mismatch",
        ),
        (
            "pub fn bad(bytes: [u8; 4]) -> u8 { bytes[0] }",
            "by-value Rust arrays",
        ),
        (
            "pub fn bad(bytes: &[u8; 4]) -> &[u8] { bytes }",
            "reference/aggregate returns",
        ),
        (
            "pub fn bad(bytes: &mut [u8; 4]) { let child = &mut bytes[0]; bytes[0] = 1; *child = 2; }",
            "cannot assign",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(message), "expected {message}: {error}");
        assert!(!p.root.join("borrow.ullbc").exists());
    }
}

#[test]
#[ignore = "nightly: 19 s, over the gate's per-test budget (2026-10-06)"]
fn rust_local_array_construction_and_whole_value_copies_verify() {
    let p = Project::new(include_str!("../examples/rust-array-values/arrays.rs"));
    let sidecar = include_str!("../examples/rust-array-values/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "literal.contract",
        "independent.contract",
        "replace.contract",
        "copy_into.contract",
        "repeat_call.contract",
        "zero_repeat_call.contract",
        "argument_order.contract",
        "assignment_order.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("ensures result == 8;", "ensures result == 16;"),
            &prepared
        )
        .is_err()
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_whole_array_copies_require_authority_for_every_element() {
    let p = Project::new(include_str!("../examples/rust-array-values/arrays.rs"));
    let sidecar = include_str!("../examples/rust-array-values/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for unsupported in [
        sidecar.replace("views source[0..2];", "views source[0..1];"),
        sidecar.replace("owns target[0..2];", "views target[0..2];"),
        sidecar.replace("owns target[0..2];", "owns target[0..1];"),
    ] {
        assert!(
            C0VerificationSession::new_program_prepared(&unsupported, &prepared).is_err(),
            "unexpectedly verified: {unsupported}"
        );
    }
}

#[test]
#[ignore = "nightly: 15 s, over the gate's per-test budget (2026-10-06)"]
fn rust_arrays_coerce_to_byte_slices_with_lengths_and_authority() {
    let p = Project::new(include_str!("../examples/rust-array-slices/arrays.rs"));
    let sidecar = include_str!("../examples/rust-array-slices/arrays.click")
        .replace("arrays.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "local.contract",
        "alias.contract",
        "retarget_mut.contract",
        "empty.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
    for incorrect in [
        sidecar.replace("ensures result == 4u64;", "ensures result == 1u64;"),
        sidecar.replace(
            "fn read(bytes: &[u8; 3]) -> u8 {\n    views bytes[0..1];",
            "fn read(bytes: &[u8; 3]) -> u8 {",
        ),
        sidecar.replace(
            "fn mutate(bytes: &mut [u8; 3]) -> u8 {\n    owns bytes[1..2];",
            "fn mutate(bytes: &mut [u8; 3]) -> u8 {\n    views bytes[1..2];",
        ),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&incorrect, &prepared).is_err());
    }
    let overflow = Project::new(
        &include_str!("../examples/rust-array-slices/arrays.rs")
            .replace("[3u8, 5, 9]", "[255u8, 5, 9]"),
    );
    refresh_import(&overflow.config()).unwrap();
    let overflow_prepared = load_import(&overflow.config()).unwrap();
    let error = C0VerificationSession::new_program_prepared(&sidecar, &overflow_prepared)
        .err()
        .expect("overflow must be rejected");
    assert!(
        error.message().contains("Rust add panic check"),
        "{}",
        error.message()
    );
}

#[test]
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
fn rust_array_to_slice_coercions_preserve_bounds_and_borrow_checks() {
    assert_native_boundary_proof(
        "pub fn bad(words: &[u32; 4]) -> usize { let s: &[u32] = words; s.len() }",
        "verifying \"borrow.rs\"; fn bad(words: &[u32; 4]) -> usize { ensures result == 4u64; } by { execute(); simp(); }",
    );

    for (source, diagnostic) in [
        (
            "pub fn bad(bytes: &[u8; 4]) { let s: &mut [u8] = bytes; s[0] = 1; }",
            "mismatched types",
        ),
        (
            "pub fn bad(bytes: &mut [u8; 4]) { let s: &mut [u8] = bytes; bytes[0] = 1; s[0] = 2; }",
            "cannot assign",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "expected {diagnostic}: {error}");
    }
    let p = Project::new(
        "pub fn read(bytes: &[u8; 2], index: usize) -> u8 { let s: &[u8] = bytes; s[index] }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for index in ["2u64", "4294967296u64", "18446744073709551615u64"] {
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn read(bytes: &[u8; 2], index: usize) -> u8 {{ requires index == {index}; views bytes[0..2]; ensures result == 0; }} by {{ execute(); simp(); }}"
        );
        assert!(C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err());
    }
}

#[test]
fn rust_local_array_authority_and_copies_scale_with_array_length() {
    let mut samples = Vec::new();
    for length in [4, 16, 64] {
        let source = format!(
            "pub fn first(bytes: &[u8]) -> u8 {{ bytes[0] }} pub fn run() -> u8 {{ let bytes = [7u8; {length}]; let copied = bytes; first(&copied) }}"
        );
        let p = gate_fixtures::project(&format!("array-scale-{length}"), &source);
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = "verifying \"borrow.rs\"; fn first(bytes: &[u8]) -> u8 { requires bytes.len() > 0u64; requires bytes.len() <= 2147483647u64; views bytes[0..1]; ensures result == bytes[0]; } by { execute(); simp(); } fn run() -> u8 { ensures result == 7; } by { execute(); simp(); }";
        let (result, work) = click::instrumentation::measure_deterministic_work(|| {
            C0VerificationSession::new_program_prepared(sidecar, &prepared)
        });
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 8,
            "array verification grew faster than its explicit operations: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_array_to_slice_calls_preserve_untouched_local_elements() {
    let p = Project::new(
        "pub fn first(bytes: &[u8]) -> u8 { bytes[0] } pub fn set(bytes: &mut [u8]) { bytes[1] = 7; } pub fn untouched() -> u8 { let mut bytes = [3u8, 5, 9]; set(&mut bytes); bytes[0] } pub fn initial() -> u8 { let bytes = [3u8, 5, 9]; first(&bytes) }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; fn first(bytes: &[u8]) -> u8 { requires bytes.len() > 0u64; requires bytes.len() <= 2147483647u64; views bytes[0..1]; ensures result == bytes[0]; } by { execute(); simp(); } fn set(bytes: &mut [u8]) { requires bytes.len() > 1u64; requires bytes.len() <= 2147483647u64; owns bytes[1..2]; ensures bytes[1] == 7; } by { execute(); simp(); } fn untouched() -> u8 { ensures result == 3; } by { execute(); simp(); } fn initial() -> u8 { ensures result == 3; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
}

const USIZE_SOURCE: &str = include_str!("../examples/rust-usize/arithmetic.rs");
const USIZE_SIDECAR: &str = include_str!("../examples/rust-usize/arithmetic.click");

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_usize_arithmetic_casts_and_expansion_verify() {
    let p = gate_fixtures::project("usize", USIZE_SOURCE);
    let sidecar = USIZE_SIDECAR.replace("arithmetic.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    let general_mul = sidecar.replace(
        "requires x == 4294967296u64;\n    requires y == 2147483648u64;\n    ensures result == 9223372036854775808u64;",
        "requires y != 0u64;\n    requires x <= 18446744073709551615u64 / y;\n    ensures result == x * y;",
    );
    assert_ne!(general_mul, sidecar);
    C0VerificationSession::new_program_prepared(&general_mul, &prepared).unwrap();
    for changed in [
        sidecar.replace("requires index == 0u64;", "requires index == 1u64;"),
        sidecar.replace(
            "requires index == 0u64;",
            "requires index == 18446744073709551615u64;",
        ),
        sidecar.replace(
            "requires bytes.len() <= 18446744073709551614u64;",
            "requires bytes.len() == 18446744073709551615u64;",
        ),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&changed, &prepared).is_err());
    }
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace(
                "ensures result == 9223372036854775808u64;",
                "ensures result == 0u64;"
            ),
            &prepared,
        )
        .is_err()
    );
}

#[test]
#[ignore = "nightly: 18 s, over the gate's per-test budget (2026-10-06)"]
fn rust_usize_panic_paths_are_rejected() {
    for (expression, precondition) in [
        ("x + 1", "x == 18446744073709551615u64"),
        ("x - 1", "x == 0u64"),
        ("x * 2", "x == 9223372036854775808u64"),
        ("1 / x", "x == 0u64"),
        ("1 % x", "x == 0u64"),
        ("1 << x", "x == 64u64"),
        ("1 >> x", "x == 4294967296u64"),
        ("1 << x", "x == 18446744073709551615u64"),
    ] {
        let p = Project::new(&format!("pub fn bad(x:usize)->usize {{ {expression} }}"));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn bad(x: usize) -> usize {{ requires {precondition}; ensures result == result; }} by {{ execute(); simp(); }}"
        );
        assert!(
            C0VerificationSession::new_program_prepared(&sidecar, &prepared).is_err(),
            "accepted {expression} at {precondition}"
        );
    }
}

#[test]
#[ignore = "nightly: 26 s, over the gate's per-test budget (2026-10-06)"]
fn rust_usize_boundaries_and_nested_checks() {
    for (source, return_type, precondition, expected, valid) in [
        (
            "x + 0",
            "usize",
            "x == 18446744073709551615u64",
            "18446744073709551615u64",
            true,
        ),
        (
            "x * 0",
            "usize",
            "x == 18446744073709551615u64",
            "0u64",
            true,
        ),
        (
            "x * 1",
            "usize",
            "x == 18446744073709551615u64",
            "18446744073709551615u64",
            true,
        ),
        (
            "x - 1",
            "usize",
            "x == 9223372036854775808u64",
            "9223372036854775807u64",
            true,
        ),
        (
            "x / 2",
            "usize",
            "x == 18446744073709551615u64",
            "9223372036854775807u64",
            true,
        ),
        (
            "x % 2",
            "usize",
            "x == 18446744073709551615u64",
            "1u64",
            true,
        ),
        (
            "{ let mut y = x; y += 1; y -= 1; y *= 1; y /= 1; y %= 2; y <<= 63; y >>= 63; y }",
            "usize",
            "x == 4294967297u64",
            "1u64",
            true,
        ),
        (
            "(x + 1) as u32",
            "u32",
            "x == 18446744073709551615u64",
            "0u32",
            false,
        ),
        (
            "false && x + 1 > 0",
            "bool",
            "x == 18446744073709551615u64",
            "0",
            true,
        ),
        (
            "true || x + 1 > 0",
            "bool",
            "x == 18446744073709551615u64",
            "1",
            true,
        ),
        (
            "true && x + 1 > 0",
            "bool",
            "x == 18446744073709551615u64",
            "1",
            false,
        ),
    ] {
        let p = Project::new(&format!(
            "pub fn check(x:usize)->{return_type} {{ {source} }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn check(x: usize) -> {return_type} {{ requires {precondition}; ensures result == {expected}; }} by {{ execute(); simp(); }}"
        );
        let result = C0VerificationSession::new_program_prepared(&sidecar, &prepared);
        assert_eq!(result.is_ok(), valid, "{source}: {:?}", result.err());
    }
    let p = Project::new("pub fn right(x:usize, n:i32)->usize { x >> n }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; fn right(x: usize, n: i32) -> usize { requires n == -1; ensures result == result; } by { execute(); simp(); }";
    assert!(C0VerificationSession::new_program_prepared(sidecar, &prepared).is_err());
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_while_loop_invariants_verify_and_expand() {
    let p = gate_fixtures::project("loops", include_str!("../examples/rust-loops/loops.rs"));
    let prepared = load_import(&p.config()).unwrap();
    let sidecar =
        include_str!("../examples/rust-loops/loops.click").replace("loops.rs", "borrow.rs");
    let (_, verified) = C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    assert_eq!(verified.len(), 3);
    for false_claim in [
        sidecar.replace("ensures result == n;", "ensures result == n + 1;"),
        sidecar.replace("invariant i <= bytes.len();", "invariant i < bytes.len();"),
        sidecar.replace("decreases bytes.len() - i;", "decreases i;"),
        sidecar.replace("requires value == 1;", "requires value == 2147483647;"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&false_claim, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
}

#[test]
#[ignore = "nightly: 18 s, over the gate's per-test budget (2026-10-06)"]
fn rust_while_loop_rejects_unsupported_control_flow_and_guards() {
    {
        let p = Project::new("pub fn bad() { while true { continue; } }");
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        assert!(
            C0VerificationSession::new_program_prepared(
                "verifying \"borrow.rs\"; fn bad() { ensures 1 == 1; } by { execute(); simp(); }",
                &prepared
            )
            .is_err()
        );
    }

    {
        let p = Project::new("pub fn bad() { 'outer: while true {} }");
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        assert!(
            C0VerificationSession::new_program_prepared(
                "verifying \"borrow.rs\"; fn bad() { ensures 1 == 1; } by { execute(); simp(); }",
                &prepared
            )
            .is_err()
        );
    }

    assert_native_boundary_proof(
        "pub fn bad() { while true { break; } }",
        "verifying \"borrow.rs\"; fn bad() { ensures 1 == 1; } by { execute(); simp(); }",
    );

    for (source, diagnostic) in [
        (
            "pub fn bad() { for _i in 0..2 {} }",
            "does not support type",
        ),
        (
            "pub fn bad(mut i:i32, n:i32) { while i + 1 < n { i += 1; } }",
            "MIR while header",
        ),
        (
            "fn guard()->bool { false } pub fn bad() { while guard() {} }",
            "MIR loop requires a conditional while header",
        ),
        (
            "pub fn bad(bytes:&[u8]) { while bytes[0] != 0 {} }",
            "MIR while header",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "expected {diagnostic}: {error}");
    }
}

#[test]
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
fn rust_while_loop_panic_paths_are_rejected() {
    for (source, signature, invariant) in [
        (
            "pub fn bad(mut i:i32) { while i >= 0 { i += 1; } }",
            "fn bad(i: i32)",
            "i >= 0",
        ),
        (
            "pub fn bad(mut i:usize) { while i <= 18446744073709551615usize { i += 1; } }",
            "fn bad(i: usize)",
            "i <= 18446744073709551615u64",
        ),
        (
            "pub fn bad(bytes:&[u8]) { let mut i=0usize; while i <= bytes.len() { let _byte=bytes[i]; i += 1; } }",
            "fn bad(bytes: &[u8])",
            "i <= bytes.len()",
        ),
    ] {
        let p = Project::new(source);
        if let Err(error) = refresh_import(&p.config()) {
            assert!(error.contains("MIR while header"), "{error}");
            continue;
        }
        let prepared = load_import(&p.config()).unwrap();
        let prefix = "execute_until(loop(0));";
        let requirements = if signature.contains("bytes") {
            "requires bytes.len() <= 2147483647u64; views *bytes;"
        } else {
            ""
        };
        let sidecar = format!(
            "verifying \"borrow.rs\"; {signature} {{ {requirements} }} by {{ {prefix} loop {{ invariant {invariant}; }} execute(); simp(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("panic path must be rejected");
        assert!(
            !error.message().contains("requires the execution frontier"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_nested_while_loop_invariants_keep_preorder_indices() {
    let p = Project::new(
        "pub fn nested()->i32 { let mut i=0; while i < 1 { let mut j=0; while j < 1 { j += 1; } i += 1; } i }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; fn nested() -> i32 { ensures result == 1; } by { execute_until(loop(0)); loop { decreases 1-i; invariant 0<=i and i<=1; preserve by { execute_until(loop(1)); loop { decreases 1-j; invariant 0<=j and j<=1; } execute_until(back_edge()); close_invariants(); } } execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    assert_cli(&p, &["expand", "--claim", "nested.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_readable_local_names_preserve_shadowed_binding_identities() {
    let p = Project::new(
        "pub fn run(n:i32)->i32 { let n=2; let n=n+1; let __rust_checked_0=n+1; __rust_checked_0 }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; fn run(n: i32) -> i32 { ensures result == 4; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("result == 4", "result == 3"),
            &prepared
        )
        .is_err()
    );
}

#[test]
#[ignore = "nightly: 14 s, over the gate's per-test budget (2026-10-06)"]
fn rust_byte_sum_proves_exact_prefix_sum_and_expands() {
    let p = Project::new(include_str!("../examples/rust-byte-sum/sum.rs"));
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar =
        include_str!("../examples/rust-byte-sum/sum.click").replace("sum.rs", "borrow.rs");
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for invalid in [
        sidecar.replace(
            "ensures to_integer(result) == old(prefix",
            "ensures to_integer(result) + 1 == old(prefix",
        ),
        sidecar.replace("invariant i <= bytes.len();", "invariant i < bytes.len();"),
        sidecar.replace(
            "invariant to_integer(total) == prefix(bytes, i);",
            "invariant to_integer(total) + 1 == prefix(bytes, i);",
        ),
        sidecar.replace("decreases bytes.len() - i;", "decreases i;"),
        sidecar.replace("requires bytes.len() <= 1000u64;", ""),
    ] {
        assert_ne!(invalid, sidecar, "negative proof must change the sidecar");
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

fn assert_slice_iterator_artifact(p: &Project) {
    let prepared = load_import(&p.config()).unwrap();
    let function = prepared
        .export()
        .functions
        .iter()
        .find(|f| f.name == "sum")
        .unwrap();
    let mir = function.mir.as_ref().unwrap();
    assert!(function.body.is_empty());
    assert!(
        mir.blocks
            .iter()
            .flat_map(|b| &b.statements)
            .any(|s| matches!(
                s,
                click::languages::rust::schema::MirStatement::SharedArrayInitialize { .. }
            ))
    );
    assert!(
        mir.blocks
            .iter()
            .flat_map(|b| &b.statements)
            .any(|s| matches!(
                s,
                click::languages::rust::schema::MirStatement::SharedArrayNext { .. }
            ))
    );
    let text = serde_json::to_string(mir).unwrap();
    assert!(!text.contains("__rust_iter_index"));
}

#[test]
#[ignore = "nightly: 2s in the parallel gate; other gate tests reach the same code"]
fn rust_empty_slice_iterator_needs_no_read_authority() {
    for expression in ["bytes", "bytes.iter()"] {
        let source = format!(
            "pub fn empty(bytes: &[u8]) -> i32 {{ for byte in {expression} {{ let _value = *byte; }} 0 }}"
        );
        let fixture = if expression == "bytes" {
            "empty-direct"
        } else {
            "empty-iter"
        };
        let p = gate_fixtures::project(fixture, &source);
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = "verifying \"borrow.rs\"; fn empty(bytes: &[u8]) -> i32 { requires bytes.len() == 0u64; ensures result == 0; } by { execute(); simp(); }";
        C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
        assert!(
            C0VerificationSession::new_program_prepared(
                &sidecar.replace("bytes.len() == 0u64", "bytes.len() == 1u64"),
                &prepared
            )
            .is_err()
        );
    }
}

#[test]
#[ignore = "nightly: 36 s, over the gate's per-test budget (2026-10-06)"]
fn rust_slice_for_sum_verifies_and_expands() {
    let p = Project::new(include_str!("../examples/rust-iterators/sum.rs"));
    refresh_import(&p.config()).unwrap();
    assert_slice_iterator_artifact(&p);
    let prepared = load_import(&p.config()).unwrap();
    let sidecar =
        include_str!("../examples/rust-iterators/sum.click").replace("sum.rs", "borrow.rs");
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    let copied_iter = Project::new(
        &include_str!("../examples/rust-iterators/sum.rs")
            .replace("in bytes {", "in bytes.iter() {"),
    );
    refresh_import(&copied_iter.config()).unwrap();
    let copied_prepared = load_import(&copied_iter.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &copied_prepared).unwrap();
    for invalid in [
        sidecar.replace(
            "ensures to_integer(result) == old(prefix",
            "ensures to_integer(result) + 1 == old(prefix",
        ),
        sidecar.replace(
            "decreases iter_remaining;",
            "decreases bytes.len() - iter_remaining;",
        ),
        sidecar.replace(
            "invariant iter_remaining <= bytes.len();",
            "invariant iter_remaining < bytes.len();",
        ),
        sidecar.replace(
            "invariant iter_cursor == bytes + (bytes.len() - iter_remaining);",
            "invariant iter_cursor == bytes + ((bytes.len() - iter_remaining) + 1u64);",
        ),
        sidecar.replace("requires bytes.len() <= 1000u64;", ""),
    ] {
        assert_ne!(invalid, sidecar, "negative proof must change the sidecar");
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 29 s, over the gate's per-test budget (2026-10-06)"]
fn rust_slice_for_rejects_unsupported_iteration() {
    assert_native_boundary_proof(
        "pub fn bad(bytes: &[u8; 2]) { for &byte in bytes {} }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8; 2]) { views bytes[0..2]; ensures 1 == 1; } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(bytes: &[u8]) { for &byte in bytes { continue; } }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8]) { requires bytes.len() == 0u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(bytes: &[u8]) { for &byte in bytes { break; } }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8]) { requires bytes.len() == 0u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(bytes: &[u8]) { 'outer: for &byte in bytes {} }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8]) { requires bytes.len() == 0u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(mut bytes: &[u8]) { for &byte in bytes {} }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8]) { requires bytes.len() == 0u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(mut bytes: &[u8]) { for byte in bytes.iter() {} }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8]) { requires bytes.len() == 0u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(bytes: &[u8]) { let iter = bytes.iter(); for byte in iter {} }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8]) { requires bytes.len() == 0u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    assert_native_boundary_proof(
        "pub fn bad(bytes: &mut [u8]) { for byte in bytes.iter() {} }",
        "verifying \"borrow.rs\"; fn bad(bytes: &mut [u8]) { requires bytes.len() == 0u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    for source in [
        "pub fn bad(bytes: &[u8]) { for byte in bytes.iter().rev() {} }",
        "pub fn bad(bytes: &mut [u8]) { for byte in bytes.iter_mut() {} }",
        "pub fn bad(bytes: &mut [u8]) { for byte in bytes {} }",
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains("does not support type"), "{error}");
        assert!(!error.contains("panicked"), "{error}");
    }
}

#[test]
#[ignore = "nightly: 43 s, over the gate's per-test budget (2026-10-06)"]
fn rust_slice_iter_reference_sum_verifies_and_expands() {
    let source = include_str!("../examples/rust-iter-references/sum.rs");
    let sidecar =
        include_str!("../examples/rust-iter-references/sum.click").replace("sum.rs", "borrow.rs");
    // Shared references from both the implicit slice iterator and .iter()
    // have the same checked address and dereference semantics.
    for source in [source.to_string(), source.replace("bytes.iter()", "bytes")] {
        let p = Project::new(&source);
        refresh_import(&p.config()).unwrap();
        assert_slice_iterator_artifact(&p);
        let prepared = load_import(&p.config()).unwrap();
        C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
        for invalid in [
            sidecar.replace(
                "ensures to_integer(result) == old(prefix",
                "ensures to_integer(result) + 1 == old(prefix",
            ),
            sidecar.replace("requires bytes.len() <= 1000u64;", ""),
            sidecar.replace("views bytes[0..bytes.len()];", ""),
            sidecar.replace(
                "decreases iter_remaining;",
                "decreases bytes.len() - iter_remaining;",
            ),
        ] {
            assert_ne!(invalid, sidecar, "negative proof must change the sidecar");
            assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
        }
        if source.contains(".iter()") {
            fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
            assert_cli(&p, &["profile"]);
            assert_cli(&p, &["audit"]);
            assert_cli(&p, &["expand", "--claim", "sum.contract", "--in-place"]);
            assert_cli(&p, &["verify"]);
        }
    }
    let p = Project::new("pub fn bad(bytes: &[u8]) { for byte in bytes.iter() { *byte = 0; } }");
    let error = refresh_import(&p.config()).unwrap_err();
    assert!(error.contains("cannot assign"), "{error}");
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_chunks_exact_remainder_metadata_and_bytes() {
    let source = "pub fn tail_len(bytes: &[u8], size: usize) -> usize { let chunks = bytes.chunks_exact(size); let tail = chunks.remainder(); tail.len() }
    pub fn tail_byte(bytes: &[u8]) -> u8 { let chunks = bytes.chunks_exact(2); let tail = chunks.remainder(); tail[0] }";
    let p = Project::new(source);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
    fn tail_len(bytes: &[u8], size: usize) -> usize {
        requires size != 0u64;
        ensures result == bytes.len() % size;
    } by { execute(); simp(); }
    fn tail_byte(bytes: &[u8]) -> u8 {
        requires bytes.len() == 5u64; views bytes[0..5];
        ensures result == bytes[4];
    } by { have bytes.len() - bytes.len() % 2u64 == 4u64 by { rewrite(bytes.len() == 5u64); normalize(); } execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    for invalid in [
        sidecar.replace("requires size != 0u64;", ""),
        sidecar.replace("views bytes[0..5];", ""),
        sidecar.replace("result == bytes[4]", "result == bytes[3]"),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}

fn chunks_loop_project(by_reference: bool) -> (Project, String) {
    let source = include_str!("../examples/rust-chunks-exact/chunks.rs");
    let source = if by_reference {
        source
            .replace("let chunks =", "let mut chunks =")
            .replace("in chunks {", "in &mut chunks {")
            .replace("tail.len()", "chunks.remainder().len()")
    } else {
        source.to_string()
    };
    let sidecar = include_str!("../examples/rust-chunks-exact/chunks.click")
        .replace("chunks.rs", "borrow.rs");
    let p = Project::new(&source);
    refresh_import(&p.config()).unwrap();
    let sidecar = if by_reference {
        sidecar.replace("iter_", "chunks_")
    } else {
        sidecar
    };
    (p, sidecar)
}

fn check_chunks_loop_claims(by_reference: bool) {
    let (p, sidecar) = chunks_loop_project(by_reference);
    let iterator = if by_reference { "chunks" } else { "iter" };
    let prepared = load_import(&p.config()).unwrap();
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for invalid in [
        sidecar.replace(
            "ensures result == bytes.len() % 4u64;",
            "ensures result == bytes.len() % 4u64 + 1u64;",
        ),
        sidecar.replace("views bytes[0..bytes.len()];", ""),
        sidecar.replace(
            &format!("invariant {iterator}_remaining % 4u64 == 0u64;"),
            &format!("invariant {iterator}_remaining % 4u64 == 1u64;"),
        ),
        sidecar.replace("bytes[k] == old(bytes[k])", "bytes[k] != old(bytes[k])"),
    ] {
        assert_ne!(invalid, sidecar, "negative proof must change the sidecar");
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
}

fn check_chunks_loop_tools(by_reference: bool) {
    let (p, sidecar) = chunks_loop_project(by_reference);
    fs::write(p.root.join("borrow.click"), &sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "cover.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 38 s, over the gate's per-test budget (2026-10-06)"]
fn rust_chunks_exact_loops_cover_input_and_preserve_bytes() {
    check_chunks_loop_claims(false);
}

#[test]
#[ignore = "nightly: 40 s, over the gate's per-test budget (2026-10-06)"]
fn rust_chunks_exact_borrowed_loops_cover_input_and_preserve_bytes() {
    check_chunks_loop_claims(true);
}

#[test]
#[ignore = "nightly: 35 s, over the gate's per-test budget (2026-10-06)"]
fn rust_chunks_exact_owned_loop_tools_recheck_all_sites() {
    check_chunks_loop_tools(false);
}

#[test]
#[ignore = "nightly: 34 s, over the gate's per-test budget (2026-10-06)"]
fn rust_chunks_exact_borrowed_loop_tools_recheck_all_sites() {
    check_chunks_loop_tools(true);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_chunks_exact_boundaries_and_full_width_sizes() {
    let p = Project::new(
        "pub fn length(bytes: &[u8], size: usize) -> usize { let chunks = bytes.chunks_exact(size); chunks.remainder().len() }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    for (length, size) in [
        (0u64, 4u64),
        (8, 4),
        (5, 4),
        (3, 4),
        (5, 1),
        (5, 4294967296),
        (5, 9223372036854775808),
        (5, u64::MAX),
    ] {
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn length(bytes: &[u8], size: usize) -> usize {{ requires bytes.len() == {length}u64; requires size == {size}u64; ensures result == {}u64; }} by {{ execute(); simp(); }}",
            length % size
        );
        C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    }
    for length in [0, 5] {
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn length(bytes: &[u8], size: usize) -> usize {{ requires bytes.len() == {length}u64; requires size == 0u64; ensures result == 0u64; }} by {{ execute(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .expect("zero size must fail");
        assert!(
            error
                .message()
                .contains("Rust chunks_exact zero size panic check"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_chunks_exact_evaluates_size_once_and_keeps_shadowed_iterators_distinct() {
    let p = Project::new("pub fn size(p: &mut i32) -> usize { *p = *p + 1; 4 }
    pub fn length(bytes: &[u8], p: &mut i32) -> usize { let chunks = bytes.chunks_exact(size(p)); chunks.remainder().len() }
    pub fn shadow(bytes: &[u8]) -> usize { let chunks = bytes.chunks_exact(4); let tail = chunks.remainder(); let chunks = tail.chunks_exact(1); chunks.remainder().len() }");
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
    fn size(p: &mut i32) -> usize { requires *p == 0; owns *p; ensures *p == 1; ensures result == 4u64; } by { execute(); simp(); }
    fn length(bytes: &[u8], p: &mut i32) -> usize { requires bytes.len() == 5u64; requires *p == 0; owns *p; ensures *p == 1; ensures result == 1u64; } by { execute(); simp(); }
    fn shadow(bytes: &[u8]) -> usize { requires bytes.len() == 5u64; ensures result == 0u64; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    let artifact = prepared.export();
    let function = artifact
        .functions
        .iter()
        .find(|f| f.name == "length")
        .unwrap();
    assert_eq!(function.mir.as_ref().unwrap().blocks.iter().filter(|b| matches!(&b.terminator, click::languages::rust::schema::MirTerminator::Call { function, .. } if function == "size")).count(), 1);
}

#[test]
#[ignore = "nightly: 15 s, over the gate's per-test budget (2026-10-06)"]
fn rust_chunks_exact_rejects_writes_and_unsupported_iterator_protocols() {
    assert_native_boundary_proof(
        "pub fn bad(bytes: &[u8]) { let chunks = bytes.chunks_exact(4); let copy = chunks; }",
        "verifying \"borrow.rs\"; fn bad(bytes: &[u8]) { requires bytes.len() == 5u64; ensures 1 == 1; } by { execute(); simp(); }",
    );

    for (source, diagnostic) in [
        (
            "pub fn bad(bytes: &[u8]) { for chunk in bytes.chunks_exact(4) { chunk[0] = 0; } }",
            "cannot assign",
        ),
        (
            "pub fn bad(bytes: &[u8]) { let chunks = bytes.chunks_exact(4); let tail = chunks.remainder(); tail[0] = 0; }",
            "cannot assign",
        ),
        (
            "pub fn bad(bytes: &mut [u8]) { let chunks = bytes.chunks_exact_mut(4); }",
            "does not support type",
        ),
        (
            "pub fn bad(bytes: &[u8]) { for chunk in bytes.chunks_exact(4).rev() {} }",
            "does not support type",
        ),
        (
            "pub fn bad(bytes: &[u8]) { let mut chunks = bytes.chunks_exact(4); let item = chunks.next(); }",
            "typed Option dispatch",
        ),
        (
            "pub fn bad(bytes: &[u8]) { let chunks = bytes.chunks_exact(4); for chunk in chunks {} chunks.remainder(); }",
            "moved value",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!error.contains("panicked"), "{error}");
    }
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn rust_chunks_exact_direct_nested_loops_keep_independent_state() {
    let source = "pub fn nested(bytes: &[u8]) -> usize {
    for chunk in bytes.chunks_exact(4) {
        for part in chunk.chunks_exact(2) {}
    }
    0
}";
    let p = Project::new(source);
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\"; fn nested(bytes: &[u8]) -> usize { requires bytes.len() == 8u64; ensures result == 0u64; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared)
        .unwrap_or_else(|error| panic!("{}", error.message()));
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    assert_cli(&p, &["expand", "--claim", "nested.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_integer_from_preserves_native_unsigned_values() {
    let p = Project::new(
        "pub fn byte(x: u8) -> u32 { u32::from(x) }
        pub fn half(x: u8) -> u16 { u16::from(x) }
        pub fn word(x: u16) -> u32 { <u32 as From<u16>>::from(x) }
        pub fn size(x: u16) -> usize { usize::from(x) }
        pub fn identity(x: u16) -> u16 { u16::from(x) }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
        fn byte(x: u8) -> u32 { ensures result == x as u32; } by { execute(); simp(); }
        fn half(x: u8) -> u16 { ensures result as u32 == x as u32; } by { execute(); simp(); }
        fn word(x: u16) -> u32 { ensures result == x as u32; } by { execute(); simp(); }
        fn size(x: u16) -> usize { ensures result == x as usize; } by { execute(); simp(); }
        fn identity(x: u16) -> u16 { ensures result == x; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    assert!(
        C0VerificationSession::new_program_prepared(
            &sidecar.replace("result == x as u32", "result == x as u32 + 1u32"),
            &prepared,
        )
        .is_err()
    );
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "word.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rust_integer_from_evaluates_nested_calls_once_in_order() {
    let p = Project::new(
        "pub fn next(p: &mut i32) -> u8 { *p += 1; *p as u8 }
        pub fn pair(p: &mut i32) -> u32 { u32::from(next(p)) * 256 + u32::from(next(p)) }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
        fn next(p: &mut i32) -> u8 { requires 0 <= *p and *p <= 1; owns *p;
            ensures *p == old(*p) + 1; ensures result as u32 == (*p as u32 & 255u32);
        } by { execute(); simp(); }
        fn pair(p: &mut i32) -> u32 { requires *p == 0; owns *p;
            ensures *p == 2; ensures result == 258u32;
        } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rust_u16_casts_truncate_and_shifts_keep_sixteen_bits() {
    let p = Project::new(
        "pub fn low(x: usize) -> u16 { x as u16 }
        pub fn signed(x: i32) -> u16 { x as u16 }
        pub fn byte(x: u16) -> u8 { x as u8 }
        pub fn invert(x: u16) -> u16 { !x }
        pub fn shift(x: u16, count: usize) -> u16 { x << count }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
        fn low(x: usize) -> u16 { ensures result as u32 == (x as u32 & 65535u32); } by { execute(); simp(); }
        fn signed(x: i32) -> u16 { ensures result as u32 == (x as u32 & 65535u32); } by { execute(); simp(); }
        fn byte(x: u16) -> u8 { ensures result as u32 == (x as u32 & 255u32); } by { execute(); simp(); }
        fn invert(x: u16) -> u16 { ensures result as u32 == (~(x as u32) & 65535u32); } by { execute(); simp(); }
        fn shift(x: u16, count: usize) -> u16 { requires count < 16u64;
            ensures result as u32 == ((x as u32 << count as u32) & 65535u32);
        } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    for count in [16, 4294967296u64, u64::MAX] {
        let invalid = sidecar.replace(
            "requires count < 16u64;",
            &format!("requires count == {count}u64;"),
        );
        let error = C0VerificationSession::new_program_prepared(&invalid, &prepared)
            .err()
            .unwrap();
        assert!(
            error.message().contains("Rust shl panic check"),
            "{}",
            error.message()
        );
    }
}

#[test]
#[ignore = "nightly: 16 s, over the gate's per-test budget (2026-10-06)"]
fn rust_u16_arithmetic_checks_its_own_width() {
    let p = Project::new(
        "pub fn add(x: u16) -> u16 { x + 1 }
        pub fn sub(x: u16) -> u16 { x - 1 }
        pub fn mul(x: u16) -> u16 { x * 3 }
        pub fn div(x: u16, d: u16) -> u16 { x / d }
        pub fn rem(x: u16, d: u16) -> u16 { x % d }",
    );
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = "verifying \"borrow.rs\";
        fn add(x: u16) -> u16 { requires x <= 65534; ensures result as u32 == x as u32 + 1u32; } by { execute(); simp(); }
        fn sub(x: u16) -> u16 { requires 1 <= x; ensures result as u32 == x as u32 - 1u32; } by { execute(); simp(); }
        fn mul(x: u16) -> u16 { requires x <= 21845; ensures result as u32 == x as u32 * 3u32; } by { have 0 <= (x as i32) * 3 by { arithmetic() using { 0 <= x; x <= 21845; } } have (x as i32) * 3 <= 65535 by { arithmetic() using { 0 <= x; x <= 21845; } } execute(); simp(); }
        fn div(x: u16, d: u16) -> u16 { requires 0 < d; ensures result as u32 == x as u32 / d as u32; } by { execute(); simp(); }
        fn rem(x: u16, d: u16) -> u16 { requires 0 < d; ensures result as u32 == x as u32 % d as u32; } by { execute(); simp(); }";
    C0VerificationSession::new_program_prepared(sidecar, &prepared).unwrap();
    for (operator, input, divisor, label) in [
        ("+", 65535, 1, "Rust add panic check"),
        ("-", 0, 1, "Rust sub panic check"),
        ("*", 21846, 3, "Rust mul panic check"),
        ("/", 5, 0, "division by zero"),
        ("%", 5, 0, "division by zero"),
    ] {
        let p = Project::new(&format!(
            "pub fn bad(x: u16, d: u16) -> u16 {{ x {operator} d }}"
        ));
        refresh_import(&p.config()).unwrap();
        let prepared = load_import(&p.config()).unwrap();
        let sidecar = format!(
            "verifying \"borrow.rs\"; fn bad(x: u16, d: u16) -> u16 {{ requires x == {input}; requires d == {divisor}; ensures result == 0; }} by {{ execute(); }}"
        );
        let error = C0VerificationSession::new_program_prepared(&sidecar, &prepared)
            .err()
            .unwrap();
        assert!(error.message().contains(label), "{}", error.message());
    }
}

#[test]
#[ignore = "nightly: live compiler/extraction checks measured at 10–20 s"]
fn rust_integer_from_rejects_other_conversions_and_shadowed_methods() {
    for (source, diagnostic) in [
        (
            "pub fn bad(x: bool) -> u8 { u8::from(x) }",
            "integer From implementation/type mismatch",
        ),
        ("pub fn bad(x: u32) -> u16 { u16::from(x) }", "From<u32>"),
        ("pub fn bad(x: u8) -> u64 { u64::from(x) }", "integer width"),
        (
            "pub fn bad(x: u8) -> u32 { x.into() }",
            "unsafe or generic call",
        ),
        (
            "pub struct Word { x: u32 } impl Word { pub fn from(x: u8) -> u32 { 99 } } pub fn bad(x: u8) -> u32 { Word::from(x) }",
            "nested or disambiguated source items",
        ),
    ] {
        let p = Project::new(source);
        let error = refresh_import(&p.config()).unwrap_err();
        assert!(error.contains(diagnostic), "{error}");
        assert!(!error.contains("panicked"), "{error}");
    }
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn rust_u16_accumulator_fields_and_references_preserve_authority() {
    let p = Project::new(include_str!(
        "../examples/rust-integer-conversions/accumulator.rs"
    ));
    refresh_import(&p.config()).unwrap();
    let prepared = load_import(&p.config()).unwrap();
    let sidecar = include_str!("../examples/rust-integer-conversions/accumulator.click")
        .replace("accumulator.rs", "borrow.rs");
    C0VerificationSession::new_program_prepared(&sidecar, &prepared).unwrap();
    for invalid in [
        sidecar.replace("ensures state.a == 254;", "ensures state.a == 255;"),
        sidecar.replace("owns state.a;", "views state.a;"),
        sidecar.replace("owns state.b;", ""),
        sidecar.replace("views *value;", ""),
        sidecar.replace(
            "ensures state.b == old(state.b);",
            "ensures state.b != old(state.b);",
        ),
    ] {
        assert!(C0VerificationSession::new_program_prepared(&invalid, &prepared).is_err());
    }
    fs::write(p.root.join("borrow.click"), sidecar).unwrap();
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    assert_cli(&p, &["expand", "--claim", "bump_a.contract", "--in-place"]);
    assert_cli(&p, &["verify"]);
}

#[path = "rust_import/parity.rs"]
mod parity;

#[path = "rust_import/array_lengths.rs"]
mod array_lengths;
#[path = "rust_import/array_values.rs"]
mod array_values;

#[path = "rust_import/loop_headers.rs"]
mod loop_headers;

#[path = "rust_import/slice_into_iteration.rs"]
mod slice_into_iteration;

#[path = "rust_import/split_slices.rs"]
mod split_slices;

#[path = "rust_import/chunk_proof.rs"]
mod chunk_proof;

#[path = "rust_import/iterator_proof.rs"]
mod iterator_proof;

#[path = "rust_import/retirement.rs"]
mod retirement;

#[path = "rust_import/adler2_trial.rs"]
mod adler2_trial;

#[path = "rust_import/crate_inputs.rs"]
mod crate_inputs;

#[path = "rust_import/adler2_helpers.rs"]
mod adler2_helpers;

#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn split_gate_fixture_tools_recheck_certificates() {
    let p = gate_fixtures::project(
        "split",
        &fs::read_to_string(gate_fixtures::root().join("split/borrow.rs")).unwrap(),
    );
    let proof =
        include_str!("../examples/rust-split-at/split.click").replace("split.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), proof).unwrap();
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "left_length.contract",
        "right_length.contract",
        "left_first.contract",
        "right_first.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn arrays_gate_fixture_tools_recheck_certificates() {
    let p = gate_fixtures::project(
        "arrays",
        &fs::read_to_string(gate_fixtures::root().join("arrays/borrow.rs")).unwrap(),
    );
    let proof =
        include_str!("../examples/rust-arrays/arrays.click").replace("arrays.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), proof).unwrap();
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "read.contract",
        "write.contract",
        "signed.contract",
        "first.contract",
        "update.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn usize_gate_fixture_tools_recheck_certificates() {
    let p = gate_fixtures::project(
        "usize",
        &fs::read_to_string(gate_fixtures::root().join("usize/borrow.rs")).unwrap(),
    );
    let proof = include_str!("../examples/rust-usize/arithmetic.click")
        .replace("arithmetic.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), proof).unwrap();
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in [
        "add.contract",
        "mul.contract",
        "right.contract",
        "computed.contract",
    ] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[test]
#[ignore = "nightly: whole-example proof-tool rechecks"]
fn loops_gate_fixture_tools_recheck_certificates() {
    let p = gate_fixtures::project(
        "loops",
        &fs::read_to_string(gate_fixtures::root().join("loops/borrow.rs")).unwrap(),
    );
    let proof = include_str!("../examples/rust-loops/loops.click").replace("loops.rs", "borrow.rs");
    fs::write(p.root.join("borrow.click"), proof).unwrap();
    assert_cli(&p, &["verify"]);
    assert_cli(&p, &["profile"]);
    assert_cli(&p, &["audit"]);
    for claim in ["count.contract", "accumulate.contract", "walk.contract"] {
        assert_cli(&p, &["expand", "--claim", claim, "--in-place"]);
        assert_cli(&p, &["verify"]);
    }
}

#[path = "rust_import/gate_fixtures.rs"]
mod gate_fixtures;
