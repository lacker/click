#![cfg(not(target_os = "macos"))]

//! Compiler-backed fixtures call the shared verification engine directly.
//! They require GNU GCC at `/usr/bin/gcc`, which macOS does not provide.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use click::languages::c::compiler_import::{create_lock, load_imports};
use click::surface::{
    expand_c0_prepared_tactic_source_at, verify_c0_prepared_sources, verify_c0_prepared_sources_at,
};
use serde_json::json;

struct Project(PathBuf);

impl Project {
    fn new() -> Self {
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        let root = std::env::temp_dir().join(format!(
            "click-compiler-fixture-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).expect("create isolated compiler fixture");
        fs::create_dir(root.join("configured")).unwrap();
        for (path, contents) in [
            ("main.c", include_str!("fixtures/compiler-import/main.c")),
            (
                "context.h",
                include_str!("fixtures/compiler-import/context.h"),
            ),
            (
                "main.click",
                include_str!("fixtures/compiler-import/main.click"),
            ),
            (
                "configured/configured.h",
                include_str!("fixtures/compiler-import/configured/configured.h"),
            ),
        ] {
            fs::write(root.join(path), contents).unwrap();
        }
        let project = Self(root);
        project.configure(1, &[]);
        project
    }

    fn config(&self) -> PathBuf {
        self.0.join("main.click.import.json")
    }

    fn configure(&self, variant: u32, extra: &[&str]) {
        assert!(
            Path::new("/usr/bin/gcc").is_file(),
            "compiler fixture requires GCC at /usr/bin/gcc; provision it before scripts/check.sh"
        );
        let mut args = vec![
            format!("-DVARIANT={variant}"),
            "-isystem".into(),
            "configured".into(),
        ];
        args.extend(extra.iter().map(|arg| (*arg).to_string()));
        let config = json!({
            "schema": 1,
            "target": "x86_64-linux-kernel",
            "compiler": "/usr/bin/gcc",
            "working_directory": ".",
            "environment": {"allow": {"PATH": "/usr/bin:/bin", "LC_ALL": "C", "SOURCE_DATE_EPOCH": "0"}},
            "sources": [{"logical_source": "main.c", "path": "main.c", "args": args, "artifact": "main.i"}]
        });
        fs::write(self.config(), serde_json::to_vec_pretty(&config).unwrap()).unwrap();
    }

    fn proof(&self) -> String {
        fs::read_to_string(self.0.join("main.click")).unwrap()
    }
}

impl Drop for Project {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.0);
    }
}

#[test]
fn compiler_import_fixture_verifies_targets_and_checked_expansion() {
    let project = Project::new();
    create_lock(&project.config()).expect("lock real compiler input");
    let imports = load_imports(&project.config()).expect("fresh locked reproduction");
    let proof = project.proof();
    let verified = verify_c0_prepared_sources(&proof, &imports).expect("compiler-backed proof");
    assert!(!verified.is_empty());
    for theorem in verified {
        assert_eq!(
            theorem.import_identity.as_deref(),
            Some(imports[0].identity())
        );
    }
    let offset = proof.rfind("execute();").unwrap();
    let line = proof[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset - proof[..offset].rfind('\n').unwrap();
    verify_c0_prepared_sources_at(&proof, &imports, line, column).expect("targeted imported proof");
    let expanded = expand_c0_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked compiler-backed tactic expansion");
    assert_ne!(expanded, proof);
    verify_c0_prepared_sources(&expanded, &imports).expect("expanded certificate verifies");
    fs::write(project.0.join("main.click"), &expanded).unwrap();
    let reloaded = load_imports(&project.config()).expect("proof edits do not invalidate C input");
    verify_c0_prepared_sources(&expanded, &reloaded).expect("fresh imported expanded proof");
}

#[test]
fn compiler_import_define_changes_require_refresh_and_change_the_proof() {
    let project = Project::new();
    create_lock(&project.config()).unwrap();
    let first = load_imports(&project.config()).unwrap();
    project.configure(0, &[]);
    assert!(load_imports(&project.config()).is_err());
    create_lock(&project.config()).unwrap();
    let second = load_imports(&project.config()).unwrap();
    assert_ne!(first[0].identity(), second[0].identity());
    assert!(verify_c0_prepared_sources(&project.proof(), &second).is_err());
    let corrected = project.proof().replace("15", "7");
    verify_c0_prepared_sources(&corrected, &second).expect("changed compiler-selected branch");
}

#[test]
fn compiler_import_identity_binds_invocation_even_when_c_bytes_match() {
    let project = Project::new();
    create_lock(&project.config()).unwrap();
    let first = load_imports(&project.config()).unwrap();
    let original = fs::read(project.0.join("main.i")).unwrap();
    project.configure(1, &["-DUNUSED_CONFIGURATION_VALUE=123"]);
    assert!(load_imports(&project.config()).is_err());
    create_lock(&project.config()).unwrap();
    let second = load_imports(&project.config()).unwrap();
    assert_eq!(original, fs::read(project.0.join("main.i")).unwrap());
    assert_ne!(first[0].identity(), second[0].identity());
}

#[test]
fn compiler_import_header_and_artifact_changes_cannot_reuse_a_lock() {
    let project = Project::new();
    create_lock(&project.config()).unwrap();
    let artifact = project.0.join("main.i");
    let original = fs::read(&artifact).unwrap();
    fs::write(&artifact, "int answer(void) { return 999; }\n").unwrap();
    assert!(load_imports(&project.config()).is_err());
    fs::write(&artifact, original).unwrap();
    fs::write(
        project.0.join("configured/configured.h"),
        "#define SYSTEM_VALUE 2\n",
    )
    .unwrap();
    assert!(load_imports(&project.config()).is_err());
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    verify_c0_prepared_sources(&project.proof().replace("15", "16"), &imports)
        .expect("changed configured system header has checked behavior");
}

#[test]
fn compiler_import_lowering_error_points_to_original_header() {
    let project = Project::new();
    fs::write(
        project.0.join("context.h"),
        "int left(void); int right(void);\nstatic inline BASE_TYPE from_header(void) { return left() + right(); }\n",
    )
    .unwrap();
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    let error = verify_c0_prepared_sources(&project.proof(), &imports).unwrap_err();
    assert!(
        error.message().contains("context.h:2"),
        "{}",
        error.message()
    );
}

#[test]
fn compiler_import_reproduces_header_existence_and_preserves_unsupported_bodies() {
    let project = Project::new();
    fs::write(
        project.0.join("context.h"),
        "#if __has_include(\"optional.h\")\n#include \"optional.h\"\n#else\n#define OPTIONAL_VALUE 15\n#endif\nstatic inline int from_header(void) { return OPTIONAL_VALUE; }\n",
    ).unwrap();
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    verify_c0_prepared_sources(&project.proof(), &imports).unwrap();
    fs::write(project.0.join("optional.h"), "#define OPTIONAL_VALUE 16\n").unwrap();
    assert!(
        load_imports(&project.config()).is_err(),
        "newly selected header must invalidate the old lock"
    );
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    verify_c0_prepared_sources(&project.proof().replace("15", "16"), &imports).unwrap();

    // The sidecar does not mention this function. Its effects still must reach
    // the C frontend and be rejected, rather than be removed as metadata.
    let mut source = fs::read_to_string(project.0.join("main.c")).unwrap();
    source.push_str("\nvoid unmentioned(void) { __asm__ volatile(\"cli\"); }\n");
    fs::write(project.0.join("main.c"), source).unwrap();
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    assert!(imports[0].source().contains("unmentioned"));
    assert!(verify_c0_prepared_sources(&project.proof().replace("15", "16"), &imports).is_err());
}

#[test]
fn compiler_import_rejects_semantic_directives_and_target_options() {
    let project = Project::new();
    project.configure(1, &["-fshort-wchar"]);
    assert!(
        create_lock(&project.config())
            .unwrap_err()
            .contains("unsupported compiler argument")
    );
    project.configure(1, &[]);
    let mut source = fs::read_to_string(project.0.join("main.c")).unwrap();
    source.insert_str(0, "#pragma pack(1)\n");
    fs::write(project.0.join("main.c"), source).unwrap();
    create_lock(&project.config()).unwrap();
    assert!(
        load_imports(&project.config()).is_err(),
        "residual semantic pragma cannot be erased"
    );
}

#[test]
fn compiler_import_results_bind_helpers_in_other_translation_units() {
    let project = Project::new();
    fs::write(
        project.0.join("main.c"),
        "int from_header(void);\nint answer(void) { return from_header(); }\n",
    )
    .unwrap();
    fs::write(
        project.0.join("helper.c"),
        "int from_header(void) { return 15; }\n",
    )
    .unwrap();
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    config["sources"].as_array_mut().unwrap().push(json!({
        "logical_source": "helper.c", "path": "helper.c", "args": [], "artifact": "helper.i"
    }));
    fs::write(
        project.config(),
        serde_json::to_vec_pretty(&config).unwrap(),
    )
    .unwrap();
    let proof = format!("verifying \"helper.c\";\n{}", project.proof());
    create_lock(&project.config()).unwrap();
    let first = load_imports(&project.config()).unwrap();
    let verified = verify_c0_prepared_sources(&proof, &first).unwrap();
    let identity = verified[0].import_identity.clone().unwrap();
    assert_eq!(
        identity.len(),
        64,
        "project identity is fixed-size per theorem"
    );
    assert!(
        verified
            .iter()
            .all(|theorem| theorem.import_identity.as_deref() == Some(&identity))
    );
    let reversed = first.iter().rev().cloned().collect::<Vec<_>>();
    assert_eq!(
        verify_c0_prepared_sources(&proof, &reversed).unwrap()[0]
            .import_identity
            .as_deref(),
        Some(identity.as_str())
    );
    let duplicate = [first[0].clone(), first[0].clone(), first[1].clone()];
    assert!(
        verify_c0_prepared_sources(&proof, &duplicate)
            .unwrap_err()
            .message()
            .contains("duplicate")
    );
    fs::write(
        project.0.join("helper.c"),
        "int from_header(void) { return 16; }\n",
    )
    .unwrap();
    assert!(load_imports(&project.config()).is_err());
    create_lock(&project.config()).unwrap();
    let second = load_imports(&project.config()).unwrap();
    assert_eq!(
        first[0].identity(),
        second[0].identity(),
        "the calling C unit itself did not change"
    );
    let changed = verify_c0_prepared_sources(&proof.replace("15", "16"), &second).unwrap();
    assert_ne!(
        changed[0].import_identity.as_deref(),
        Some(identity.as_str())
    );
}

#[test]
fn compiler_import_rejects_output_input_collisions_before_writing() {
    let project = Project::new();
    let original = fs::read(project.0.join("main.c")).unwrap();
    let original_config = fs::read(project.config()).unwrap();
    for artifact in [
        "main.c",
        "main.click.import.json",
        "main.click.import.lock.json",
    ] {
        let mut config: serde_json::Value = serde_json::from_slice(&original_config).unwrap();
        config["sources"][0]["artifact"] = json!(artifact);
        fs::write(
            project.config(),
            serde_json::to_vec_pretty(&config).unwrap(),
        )
        .unwrap();
        assert!(create_lock(&project.config()).is_err());
        assert_eq!(fs::read(project.0.join("main.c")).unwrap(), original);
    }
    let mut config: serde_json::Value = serde_json::from_slice(&original_config).unwrap();
    config["sources"][0]["artifact"] = json!("context.h");
    let header = fs::read(project.0.join("context.h")).unwrap();
    fs::write(
        project.config(),
        serde_json::to_vec_pretty(&config).unwrap(),
    )
    .unwrap();
    assert!(
        create_lock(&project.config())
            .unwrap_err()
            .contains("owned output")
    );
    assert_eq!(fs::read(project.0.join("context.h")).unwrap(), header);
}

#[test]
fn compiler_import_preserves_explicit_external_assumption_reporting() {
    let project = Project::new();
    fs::write(
        project.0.join("main.c"),
        "int external_identity(int x);\nint caller(int x) { return external_identity(x); }\n",
    )
    .unwrap();
    let proof = "verifying \"main.c\";\nextern int32 external_identity(int32 x) { requires x >= 0; ensures result == x; }\nint32 caller(int32 x) { requires x >= 0; ensures result == x; }\n";
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    let assumptions = click::surface::c0_prepared_external_dependencies(proof, &imports).unwrap();
    assert_eq!(
        assumptions.get("caller"),
        Some(&vec!["external_identity".to_string()])
    );
    verify_c0_prepared_sources(proof, &imports).unwrap();
}
