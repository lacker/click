use super::*;
use click::instrumentation::{VerificationEvent, collect};
use std::sync::atomic::{AtomicUsize, Ordering};

struct Project(PathBuf);

impl Project {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let path = env::temp_dir().join(format!(
            "click-incremental-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        ));
        fs::create_dir(&path).unwrap();
        let project = Self(fs::canonicalize(path).unwrap());
        project.git(&["init", "-q"]);
        project
    }

    fn git(&self, arguments: &[&str]) -> String {
        let output = Command::new("git")
            .arg("-C")
            .arg(&self.0)
            .args([
                "-c",
                "user.name=Click tests",
                "-c",
                "user.email=click-tests@example.invalid",
                "-c",
                "commit.gpgsign=false",
                "-c",
                "core.hooksPath=/dev/null",
            ])
            .args(arguments)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "git {arguments:?}: {}",
            String::from_utf8_lossy(&output.stderr),
        );
        String::from_utf8(output.stdout).unwrap().trim().to_string()
    }

    fn write(&self, name: &str, source: &str) {
        fs::write(self.0.join(name), source).unwrap();
    }

    fn commit(&self) -> String {
        self.git(&["add", "."]);
        self.git(&["commit", "-qm", "test inputs"]);
        self.git(&["rev-parse", "HEAD"])
    }

    fn sidecar(&self) -> PathBuf {
        self.0.join("project.click")
    }

    fn verify(&self) -> Result<(), String> {
        entry_with([self.sidecar().display().to_string()])
    }

    fn incremental(&self, revision: &str, explain: bool) -> Result<(), String> {
        let mut arguments = vec!["--changed-since".to_string(), revision.to_string()];
        if explain {
            arguments.push("--explain".to_string());
        }
        arguments.push(self.sidecar().display().to_string());
        entry_with(arguments)
    }

    fn attested(&self, revision: &str) -> bool {
        let commit = git_commit_id(&self.0, revision).unwrap();
        has_full_verification_marker(&self.0, &commit, &self.sidecar()).unwrap()
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

const TRUE_THEOREM: &str = "theorem claim() { ensures 1 == 1 by { normalize(); } }";
const FALSE_THEOREM: &str = "theorem claim() { ensures 1 == 2 by { normalize(); } }";

fn entered_verification(events: &[VerificationEvent]) -> bool {
    events
        .iter()
        .any(|event| matches!(event, VerificationEvent::PhaseStarted("environment")))
}

#[test]
fn incremental_rejects_unattested_false_theorem_only_sidecars() {
    let project = Project::new();
    project.write("project.click", FALSE_THEOREM);
    project.commit();

    assert!(project.verify().unwrap_err().contains("normalize"));
    let (explained, events) = collect(|| project.incremental("HEAD", true));
    explained.unwrap();
    assert!(
        !entered_verification(&events),
        "explanation must remain a dry run"
    );
    assert!(!project.attested("HEAD"));
    assert!(
        project
            .incremental("HEAD", false)
            .unwrap_err()
            .contains("normalize")
    );
    assert!(!project.attested("HEAD"));
}

#[test]
fn incremental_verifies_reuses_and_rechecks_theorem_only_sidecars() {
    let project = Project::new();
    project.write("project.click", TRUE_THEOREM);
    project.commit();

    let (rebuilt, events) = collect(|| project.incremental("HEAD", false));
    rebuilt.unwrap();
    assert!(
        entered_verification(&events),
        "an unattested theorem must be proved"
    );
    assert!(project.attested("HEAD"));

    let (reused, events) = collect(|| project.incremental("HEAD", false));
    reused.unwrap();
    assert!(
        !entered_verification(&events),
        "unchanged attested proofs are reused"
    );

    project.write("project.click", FALSE_THEOREM);
    assert!(
        project
            .incremental("HEAD", false)
            .unwrap_err()
            .contains("normalize")
    );
}

#[test]
fn incremental_full_rebuild_attests_matching_requested_theorem_baseline() {
    let project = Project::new();
    project.write("project.click", TRUE_THEOREM);
    let baseline = project.commit();
    project.git(&["commit", "--allow-empty", "-qm", "unrelated commit"]);

    project.incremental(&baseline, false).unwrap();
    assert!(project.attested(&baseline));
    assert!(project.attested("HEAD"));
    let (reused, events) = collect(|| project.incremental(&baseline, false));
    reused.unwrap();
    assert!(!entered_verification(&events));
}

fn header_project(transitive: bool) -> Project {
    let project = Project::new();
    let include = if transitive { "outer.h" } else { "cap.h" };
    if transitive {
        project.write("outer.h", "#include \"cap.h\"\n");
    }
    project.write("cap.h", "#define CAP 2\n");
    project.write(
        "probe.c",
        &format!("#include \"{include}\"\nint probe(void) {{ return CAP; }}\n"),
    );
    project.write(
        "project.click",
        "verifying \"probe.c\";\nint probe() { ensures result == 1; } by { execute(); simp(); }\n",
    );
    project
}

fn check_dirty_header_attestation(transitive: bool, staged: bool) {
    let project = header_project(transitive);
    project.commit();
    assert!(project.verify().is_err());

    project.write("cap.h", "#define CAP 1\n");
    if staged {
        project.git(&["add", "cap.h"]);
    }
    project.verify().unwrap();
    assert!(
        !project.attested("HEAD"),
        "a modified header must not attest the false baseline"
    );
    project.git(&[
        "restore",
        "--source=HEAD",
        "--staged",
        "--worktree",
        "cap.h",
    ]);
    assert!(project.verify().is_err());
    assert!(project.incremental("HEAD", false).is_err());
}

#[test]
fn uncommitted_direct_headers_cannot_attest_false_baselines() {
    check_dirty_header_attestation(false, false);
}

#[test]
fn staged_direct_headers_cannot_attest_false_baselines() {
    check_dirty_header_attestation(false, true);
}

#[test]
fn uncommitted_transitive_headers_cannot_attest_false_baselines() {
    check_dirty_header_attestation(true, false);
}

#[test]
fn staged_transitive_headers_cannot_attest_false_baselines() {
    check_dirty_header_attestation(true, true);
}

#[test]
fn untracked_headers_cannot_attest_incomplete_baselines() {
    let project = header_project(false);
    project.write("cap.h", "#define CAP 1\n");
    project.git(&["add", "project.click", "probe.c"]);
    project.git(&["commit", "-qm", "header absent from baseline"]);
    project.verify().unwrap();
    assert!(!project.attested("HEAD"));
}

#[test]
fn attestation_uses_verified_header_snapshot_after_files_change() {
    let project = header_project(true);
    project.commit();
    project.write("cap.h", "#define CAP 1\n");
    let (click_source, inputs) = load_sidecar_inputs(&project.sidecar()).unwrap();
    let CInput::Bundle(sources) = inputs else {
        panic!("test uses ordinary C inputs")
    };
    verify_c0_sources(&click_source, &source_refs(&sources)).unwrap();

    project.git(&["restore", "cap.h"]);
    record_full_verification(&project.sidecar(), &click_source, &sources, &[]).unwrap();
    assert!(
        !project.attested("HEAD"),
        "restoring files after verification cannot change what was proved"
    );
    assert!(project.incremental("HEAD", false).is_err());
}

#[test]
fn clean_header_baselines_are_attested_and_reused() {
    let project = header_project(true);
    project.write("cap.h", "#define CAP 1\n");
    project.commit();
    project.verify().unwrap();
    assert!(project.attested("HEAD"));
    let (reused, events) = collect(|| project.incremental("HEAD", false));
    reused.unwrap();
    assert!(!entered_verification(&events));

    project.write("cap.h", "#define CAP 2\n");
    assert!(project.incremental("HEAD", false).is_err());
}
