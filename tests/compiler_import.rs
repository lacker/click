#![cfg(not(target_os = "macos"))]

//! Compiler-backed fixtures call the shared verification engine directly.
//! They require GNU GCC at `/usr/bin/gcc`, which macOS does not provide.

use click::surface::ProgramInputs;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use click::languages::c::compiler_import::PreparedCImport;
use click::surface::{
    expand_c_prepared_tactic_source_at, verify_c_prepared_sources, verify_sources_at,
};
use serde_json::json;

/// The fixtures describe each import as the per-sidecar config of earlier
/// releases, `main.import-description.json`. Click reads only project units,
/// so this translates a description into the equivalent unit `main` of a
/// `click.project.json` beside it.
fn describe_project(description: &Path) -> Result<PathBuf, String> {
    let directory = description.parent().unwrap();
    let config: serde_json::Value = serde_json::from_slice(
        &fs::read(description).map_err(|error| format!("read import description: {error}"))?,
    )
    .map_err(|error| format!("parse import description: {error}"))?;
    let mut sources = serde_json::Map::new();
    for source in config["sources"].as_array().unwrap() {
        let mut entry = json!({"args": source["args"]});
        for field in ["projection", "functions"] {
            if let Some(value) = source.get(field) {
                entry[field] = value.clone();
            }
        }
        sources.insert(source["path"].as_str().unwrap().to_string(), entry);
    }
    let mut unit = json!({
        "language": "c",
        "compiler": config["compiler"],
        "env": config["environment"]["allow"],
        "sources": sources,
    });
    if let Some(root) = config["working_directory"]
        .as_str()
        .filter(|root| *root != ".")
    {
        unit["root"] = root.into();
    }
    if let Some(profile) = config.get("option_profile") {
        unit["option_profile"] = profile.clone();
    }
    let mut project = json!({"units": {"main": unit}});
    if let Some(target) = config.get("target") {
        project["target"] = target.clone();
    }
    if let Some(mode) = config.get("mode") {
        project["mode"] = mode.clone();
    }
    let project_file = directory.join(click::project::FILE_NAME);
    fs::write(&project_file, serde_json::to_vec_pretty(&project).unwrap()).unwrap();
    Ok(project_file)
}

/// The C section of the `main` unit's entry in a project lock.
fn unit_lock(lock: &serde_json::Value) -> &serde_json::Value {
    &lock["units"]["main"]["lock"]["c"]
}

fn unit_lock_mut(lock: &mut serde_json::Value) -> &mut serde_json::Value {
    &mut lock["units"]["main"]["lock"]["c"]
}

/// Prepares the described import as its project's unit.
fn create_lock(description: &Path) -> Result<(), String> {
    click::project::Project::load(&describe_project(description)?)?.lock()
}

/// Loads every described source from its project's lock, without the
/// compiler.
fn load_imports(description: &Path) -> Result<Vec<PreparedCImport>, String> {
    let project_file = describe_project(description)?;
    let config: serde_json::Value =
        serde_json::from_slice(&fs::read(description).unwrap()).unwrap();
    let root = description
        .parent()
        .unwrap()
        .join(config["working_directory"].as_str().unwrap_or("."));
    let requested = config["sources"]
        .as_array()
        .unwrap()
        .iter()
        .map(|source| {
            let path = source["path"].as_str().unwrap().to_string();
            let canonical = fs::canonicalize(root.join(&path)).ok();
            (path, canonical)
        })
        .collect::<Vec<_>>();
    match click::project::Project::load(&project_file)?.prepared_sources(&requested)? {
        Some(click::project::UnitSelection::C(imports)) => Ok(imports),
        _ => Err("expected the prepared C unit".into()),
    }
}

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
        self.0.join("main.import-description.json")
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
            "target": "x86_64-unknown-linux-gnu",
            "mode": "kernel",
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

/// A C project lock names the project's own files by `$project`: one
/// project prepared at two paths writes the same lock, so each copy's import
/// has the same identity.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5.4s in the parallel gate"]
fn compiler_import_project_locks_are_portable() {
    let first = Project::new();
    let second = Project::new();
    create_lock(&first.config()).expect("lock the first copy");
    create_lock(&second.config()).expect("lock the second copy");
    let read =
        |project: &Project| fs::read_to_string(project.0.join(click::project::LOCK_NAME)).unwrap();
    let lock = read(&first);
    assert!(!lock.contains(first.0.to_str().unwrap()), "{lock}");
    assert_eq!(lock, read(&second));
    let identity = |project: &Project| {
        load_imports(&project.config()).expect("offline locked import")[0]
            .identity()
            .to_string()
    };
    assert_eq!(identity(&first), identity(&second));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn compiler_import_fixture_verifies_targets_and_checked_expansion() {
    let project = Project::new();
    create_lock(&project.config()).expect("lock real compiler input");
    let imports = load_imports(&project.config()).expect("offline locked import");
    let proof = project.proof();
    let verified = verify_c_prepared_sources(&proof, &imports).expect("compiler-backed proof");
    assert!(!verified.is_empty());
    for theorem in verified {
        assert_eq!(
            theorem.import_identity.as_deref(),
            Some(imports[0].identity())
        );
    }
    let offset = proof.rfind("ensures result == 15;").unwrap();
    let line = proof[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset - proof[..offset].rfind('\n').unwrap();
    verify_sources_at(&proof, &ProgramInputs::Prepared(&imports), line, column)
        .expect("targeted imported proof");
    let expanded = expand_c_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked compiler-backed tactic expansion");
    assert_ne!(expanded, proof);
    verify_c_prepared_sources(&expanded, &imports).expect("expanded certificate verifies");
    let sites =
        click::surface::smart_tactic_source_sites(&proof, &ProgramInputs::Prepared(&imports))
            .unwrap();
    let claim = &sites.last().unwrap().claim_label;
    let positions = sites
        .iter()
        .filter(|site| &site.claim_label == claim)
        .map(|site| site.position.clone())
        .collect::<Vec<_>>();
    let batch = click::surface::expand_tactics_source_at(
        &proof,
        &ProgramInputs::Prepared(&imports),
        &positions,
    )
    .unwrap();
    verify_c_prepared_sources(&batch.source, &imports).expect("batch compiler-backed expansion");
    let scoped = click::surface::ClickProject::new(
        "main.click",
        [click::surface::ClickModuleSource::new(
            "main.click",
            &proof,
            [],
        )],
    );
    let batch = click::surface::expand_project_tactics_source_at(
        &scoped,
        &ProgramInputs::Prepared(&imports),
        &positions,
    )
    .unwrap();
    click::surface::verify_c_prepared_project(&scoped.with_entry_source(batch.source), &imports)
        .expect("batch project compiler-backed expansion");
    fs::write(project.0.join("main.click"), &expanded).unwrap();
    let reloaded = load_imports(&project.config()).expect("proof edits do not invalidate C input");
    verify_c_prepared_sources(&expanded, &reloaded).expect("offline imported expanded proof");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s in the parallel gate"]
fn compiler_import_define_changes_require_refresh_and_change_the_proof() {
    let project = Project::new();
    create_lock(&project.config()).unwrap();
    let first = load_imports(&project.config()).unwrap();
    project.configure(0, &[]);
    assert!(load_imports(&project.config()).is_err());
    create_lock(&project.config()).unwrap();
    let second = load_imports(&project.config()).unwrap();
    assert_ne!(first[0].identity(), second[0].identity());
    assert!(verify_c_prepared_sources(&project.proof(), &second).is_err());
    let corrected = project.proof().replace("15", "7");
    verify_c_prepared_sources(&corrected, &second).expect("changed compiler-selected branch");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn compiler_import_identity_binds_invocation_even_when_c_bytes_match() {
    let project = Project::new();
    create_lock(&project.config()).unwrap();
    let first = load_imports(&project.config()).unwrap();
    let original = fs::read(project.0.join(".click/captures/main/main.c.i")).unwrap();
    project.configure(1, &["-DUNUSED_CONFIGURATION_VALUE=123"]);
    assert!(load_imports(&project.config()).is_err());
    create_lock(&project.config()).unwrap();
    let second = load_imports(&project.config()).unwrap();
    assert_eq!(
        original,
        fs::read(project.0.join(".click/captures/main/main.c.i")).unwrap()
    );
    assert_ne!(first[0].identity(), second[0].identity());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn compiler_import_header_and_artifact_changes_cannot_reuse_a_lock() {
    let project = Project::new();
    create_lock(&project.config()).unwrap();
    let artifact = project.0.join(".click/captures/main/main.c.i");
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
    verify_c_prepared_sources(&project.proof().replace("15", "16"), &imports)
        .expect("changed configured system header has checked behavior");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn compiler_import_lowering_error_points_to_original_header() {
    let project = Project::new();
    fs::write(
        project.0.join("context.h"),
        "int left(void); int right(void);\nstatic inline BASE_TYPE from_header(void) { return left() + right(); }\n",
    )
    .unwrap();
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    let error = verify_c_prepared_sources(&project.proof(), &imports).unwrap_err();
    assert!(
        error.message().contains("context.h:2"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 8s in the parallel gate"]
fn compiler_import_reproduces_header_existence_and_preserves_unsupported_bodies() {
    let project = Project::new();
    fs::write(
        project.0.join("context.h"),
        "#if __has_include(\"optional.h\")\n#include \"optional.h\"\n#else\n#define OPTIONAL_VALUE 15\n#endif\nstatic inline int from_header(void) { return OPTIONAL_VALUE; }\n",
    ).unwrap();
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    verify_c_prepared_sources(&project.proof(), &imports).unwrap();
    let original_identity = imports[0].identity().to_string();
    fs::write(project.0.join("optional.h"), "#define OPTIONAL_VALUE 16\n").unwrap();
    // A locked import means the prepared state, including the absence of
    // this header. Only an explicit refresh selects the newly added header.
    let still_locked = load_imports(&project.config()).unwrap();
    assert_eq!(still_locked[0].identity(), original_identity);
    verify_c_prepared_sources(&project.proof(), &still_locked).unwrap();
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    assert_ne!(imports[0].identity(), original_identity);
    verify_c_prepared_sources(&project.proof().replace("15", "16"), &imports).unwrap();

    // The sidecar does not mention this function. Its effects still must reach
    // the C frontend and be rejected, rather than be removed as metadata.
    let mut source = fs::read_to_string(project.0.join("main.c")).unwrap();
    source.push_str("\nvoid unmentioned(void) { __asm__ volatile(\"cli\"); }\n");
    fs::write(project.0.join("main.c"), source).unwrap();
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    assert!(imports[0].source().contains("unmentioned"));
    assert!(verify_c_prepared_sources(&project.proof().replace("15", "16"), &imports).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
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
    let verified = verify_c_prepared_sources(&proof, &first).unwrap();
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
        verify_c_prepared_sources(&proof, &reversed).unwrap()[0]
            .import_identity
            .as_deref(),
        Some(identity.as_str())
    );
    let duplicate = [first[0].clone(), first[0].clone(), first[1].clone()];
    assert!(
        verify_c_prepared_sources(&proof, &duplicate)
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
    let changed = verify_c_prepared_sources(&proof.replace("15", "16"), &second).unwrap();
    assert_ne!(
        changed[0].import_identity.as_deref(),
        Some(identity.as_str())
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn compiler_import_preserves_explicit_external_assumption_reporting() {
    let project = Project::new();
    fs::write(
        project.0.join("main.c"),
        "int external_identity(int x);\nint caller(int x) { return external_identity(x); }\n",
    )
    .unwrap();
    let proof = "target \"x86_64-unknown-linux-gnu\";\nmode \"kernel\";\nverifying \"main.c\";\nextern int32 external_identity(int32 x) { requires x >= 0; ensures result == x; }\nint32 caller(int32 x) { requires x >= 0; ensures result == x; }\n";
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    let assumptions = click::surface::c_prepared_external_dependencies(proof, &imports).unwrap();
    assert_eq!(
        assumptions.get("caller"),
        Some(&vec!["external_identity".to_string()])
    );
    verify_c_prepared_sources(proof, &imports).unwrap();
}

fn configure_userspace(project: &Project) {
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    config["target"] = json!("x86_64-unknown-linux-gnu");
    config.as_object_mut().unwrap().remove("mode");
    fs::write(
        project.config(),
        serde_json::to_vec_pretty(&config).unwrap(),
    )
    .unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s in the parallel gate"]
fn userspace_compiler_import_verifies_profile_and_expansion() {
    let project = Project::new();
    configure_userspace(&project);
    fs::write(project.0.join("profile.h"), "#define ANSWER 42\n").unwrap();
    fs::write(
        project.0.join("main.c"),
        r#"
#if defined(__KERNEL__) || __STDC_VERSION__ != 201112L || !defined(__STRICT_ANSI__)
#error wrong C profile
#endif
#if _POSIX_C_SOURCE != 200809L || _REENTRANT != 1
#error wrong pthread profile
#endif
#if __CHAR_BIT__ != 8 || __SIZEOF_LONG__ != 8 || __SIZEOF_POINTER__ != 8 || defined(__CHAR_UNSIGNED__)
#error wrong ABI
#endif
#include "profile.h"
int answer(void) { return ANSWER; }
"#,
    )
    .unwrap();
    let proof = "target \"x86_64-unknown-linux-gnu\"; verifying \"main.c\"; int answer() { ensures result == 42; }";
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    let verified = verify_c_prepared_sources(proof, &imports).unwrap();
    assert!(verified.iter().all(|theorem| {
        theorem.target() == click::languages::c::target::CTarget::X86_64LinuxUserspace
            && theorem.import_identity.as_deref() == Some(imports[0].identity())
    }));
    let column = proof.find("ensures result == 42;").unwrap() + 1;
    let expanded = expand_c_prepared_tactic_source_at(proof, &imports, 1, column).unwrap();
    verify_c_prepared_sources(&expanded, &imports).unwrap();
    // Both whole-file and selected-site checking must reject a target mismatch.
    let wrong = proof.replace("verifying", "mode \"kernel\"; verifying");
    let error = verify_c_prepared_sources(&wrong, &imports).unwrap_err();
    assert!(
        error.message().contains("but the sidecar selects"),
        "{error:?}"
    );
    let column = wrong.find("ensures result == 42;").unwrap() + 1;
    assert!(verify_sources_at(&wrong, &ProgramInputs::Prepared(&imports), 1, column).is_err());
    assert!(expand_c_prepared_tactic_source_at(&wrong, &imports, 1, column).is_err());
    // Opened headers remain lock dependencies even when their bytes do not
    // affect the selected function.
    fs::write(project.0.join("profile.h"), "/* changed header */\n").unwrap();
    assert!(load_imports(&project.config()).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn userspace_and_kernel_imports_have_distinct_identity_for_identical_c() {
    let project = Project::new();
    fs::write(
        project.0.join("main.c"),
        "int answer(void) { return 42; }\n",
    )
    .unwrap();
    create_lock(&project.config()).unwrap();
    let kernel = load_imports(&project.config()).unwrap();
    let original = fs::read(project.0.join(".click/captures/main/main.c.i")).unwrap();
    configure_userspace(&project);
    assert!(load_imports(&project.config()).is_err());
    create_lock(&project.config()).unwrap();
    let userspace = load_imports(&project.config()).unwrap();
    assert_eq!(
        original,
        fs::read(project.0.join(".click/captures/main/main.c.i")).unwrap()
    );
    assert_ne!(kernel[0].identity(), userspace[0].identity());
    let proof = "target \"x86_64-unknown-linux-gnu\"; verifying \"main.c\"; int answer() { ensures result == 42; }";
    assert!(verify_c_prepared_sources(proof, &kernel).is_err());
    verify_c_prepared_sources(proof, &userspace).unwrap();
}

#[test]
fn userspace_string_header_skips_the_legacy_fallback() {
    let project = Project::new();
    configure_userspace(&project);
    fs::write(
        project.0.join("main.c"),
        r#"
#include <string.h>
#define HAVE_STRINGS_H 1
#if defined(HAVE_STRINGS_H) && !defined(_STRING_H) && !defined(__USE_BSD)
#include <strings.h>
#endif
size_t answer(void) { return strlen("hello"); }
"#,
    )
    .unwrap();
    create_lock(&project.config()).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn userspace_compiler_import_refuses_profile_overrides_and_ambient_headers() {
    let project = Project::new();
    for args in [
        vec!["-std=gnu11"],
        vec!["-fno-unsigned-char"],
        vec!["-D__KERNEL__=1"],
        vec!["-D__KERNEL__(x)=1"],
        vec!["-D", "_POSIX_C_SOURCE =199309L"],
        vec!["-U", "_REENTRANT"],
        vec!["-D_POSIX_C_SOURCE=199309L"],
        vec!["-D__STDC_VERSION__=199901L"],
        vec!["-U__STRICT_ANSI__"],
    ] {
        project.configure(1, &args);
        configure_userspace(&project);
        let error = create_lock(&project.config()).unwrap_err();
        assert!(
            error.contains("unsupported compiler argument") || error.contains("cannot override"),
            "{args:?}: {error}"
        );
    }
    project.configure(1, &[]);
    configure_userspace(&project);
    fs::write(project.0.join("main.c"), "#include <pthread.h>\n").unwrap();
    let error = create_lock(&project.config()).unwrap_err();
    assert!(error.contains("pthread.h"), "{error}");
    assert!(!project.0.join(".click/captures/main/main.c.i").exists());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s in the parallel gate"]
fn compiler_import_dependency_closure_projection_is_an_explicit_checked_option() {
    let project = Project::new();
    let original_config = fs::read(project.config()).unwrap();
    let with_projection = |value: &str| {
        let mut config: serde_json::Value = serde_json::from_slice(&original_config).unwrap();
        config["sources"][0]["projection"] = json!(value);
        fs::write(
            project.config(),
            serde_json::to_vec_pretty(&config).unwrap(),
        )
        .unwrap();
    };

    with_projection("whatever-parses");
    let error = create_lock(&project.config()).expect_err("unknown projection");
    assert!(error.contains("unsupported import projection"), "{error}");

    // An unused declaration the parser rejects is omitted by the projection,
    // while the proof about the definition it keeps still verifies.
    let mut header = fs::read_to_string(project.0.join("context.h")).unwrap();
    header = header.replace(
        "#endif\n",
        "static inline int unused_stray(int x) { __asm__ __volatile__(\"cli\"); return x; }\n#endif\n",
    );
    fs::write(project.0.join("context.h"), header).unwrap();
    with_projection("dependency-closure");
    create_lock(&project.config()).expect("lock the projected import");
    let imports = load_imports(&project.config()).expect("load the projected import");
    assert!(!imports[0].source().contains("unused_stray"));
    assert!(imports[0].source().contains("from_header"));
    verify_c_prepared_sources(&project.proof(), &imports).expect("the kept proof verifies");

    // Without the projection the same artifact is refused at the stray
    // assembly, and the configuration change is a different lock.
    fs::write(project.config(), &original_config).unwrap();
    create_lock(&project.config()).expect("lock the whole import");
    let imports = load_imports(&project.config()).expect("load the whole import");
    let error = verify_c_prepared_sources(&project.proof(), &imports)
        .expect_err("the whole unit includes the stray assembly");
    assert!(
        error.message().contains("inline assembly"),
        "{}",
        error.message()
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1s focused; locks and checks both dependency cases"]
fn compiler_import_projects_only_selected_functions_and_their_dependencies() {
    let project = Project::new();
    configure_userspace(&project);
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    let set_roots = |config: &mut serde_json::Value, roots: &[&str]| {
        config["sources"][0]["projection"] = json!("dependency-closure");
        config["sources"][0]["functions"] = json!(roots);
        fs::write(project.config(), serde_json::to_vec_pretty(config).unwrap()).unwrap();
    };
    let source = "struct slot { int payload; };\n\
                  static int sibling(struct slot *obj) { return (obj->payload = 1); }\n\
                  int selected(void) { return 42; }\n";
    fs::write(project.0.join("main.c"), source).unwrap();
    let proof = r#"verifying "main.c"; int selected() { ensures result == 42; }"#;
    set_roots(&mut config, &["selected"]);
    create_lock(&project.config()).unwrap();
    let lock: serde_json::Value =
        serde_json::from_slice(&fs::read(project.0.join(".click/captures/manifest.json")).unwrap())
            .unwrap();
    assert_eq!(
        unit_lock(&lock)["sources"][0]["functions"],
        json!(["selected"])
    );
    let imports = load_imports(&project.config()).unwrap();
    assert!(!imports[0].source().contains("sibling"));
    verify_c_prepared_sources(proof, &imports).unwrap();

    set_roots(&mut config, &["sibling"]);
    let error = load_imports(&project.config()).expect_err("the root list is locked");
    assert!(error.contains("does not match its description"), "{error}");
    assert!(error.contains("click capture"), "{error}");
    set_roots(&mut config, &["selected"]);

    let caller = source.replace("return 42;", "struct slot value; return sibling(&value);");
    fs::write(project.0.join("main.c"), caller).unwrap();
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    assert!(imports[0].source().contains("static int sibling"));
    let error =
        verify_c_prepared_sources(proof, &imports).expect_err("the called body is required");
    let diagnostic = error.to_string();
    assert!(diagnostic.contains("main.c:2"), "{diagnostic}");
    assert!(
        diagnostic
            .contains("assignment expressions currently require a simple scalar variable target"),
        "{diagnostic}"
    );
}

/// A copy of the pinned Adler-32 project, whose `zlib` directory holds the
/// zlib sidecars, beside a copy of the repository's `vendor` trees, which hold
/// the original zlib files: the project file, lock, prepared sources and every
/// sidecar come along.
struct ZlibProject {
    _copy: tempfile::TempDir,
    zlib: PathBuf,
}

impl ZlibProject {
    /// The copied `zlib` directory.
    fn path(&self) -> &Path {
        &self.zlib
    }
}

/// Copies the directory tree `from` to `to`.
fn copy_tree(from: &Path, to: &Path) {
    fs::create_dir_all(to).unwrap();
    for entry in fs::read_dir(from).unwrap() {
        let entry = entry.unwrap();
        let destination = to.join(entry.file_name());
        if entry.file_type().unwrap().is_dir() {
            copy_tree(&entry.path(), &destination);
        } else {
            fs::copy(entry.path(), destination).unwrap();
        }
    }
}

/// The int32 and uint64 Adler-32 specifications and the theorems equating
/// them, as one source: the zlib proofs import the bridge, which imports both.
fn adler_specifications() -> String {
    include_str!("../design/adler32/project/adler32-spec-bridge.click")
        .replace(
            "import \"adler32-spec.click\";",
            include_str!("../design/adler32/project/adler32-spec.click"),
        )
        .replace(
            "import \"adler32-spec-u64.click\";",
            include_str!("../design/adler32/project/adler32-spec-u64.click"),
        )
}

fn zlib_project() -> ZlibProject {
    let copy = tempfile::tempdir().expect("isolated offline Adler-32 project");
    let repository = Path::new(env!("CARGO_MANIFEST_DIR"));
    copy_tree(
        &repository.join("design/adler32"),
        &copy.path().join("design/adler32"),
    );
    let zlib = copy.path().join("design/adler32/project/zlib");
    ZlibProject { _copy: copy, zlib }
}

/// The original `adler32.c`, as the zlib sidecars spell it.
const ZLIB_ADLER32: &str = "../../vendor/zlib-1.3.1/adler32.c";

/// The prepared zlib `source`, spelled as from a zlib sidecar, from the
/// project's units, without the compiler.
fn zlib_imports(root: &Path, source: &str) -> Result<Vec<PreparedCImport>, String> {
    let project = click::project::Project::load(&root.join("..").join(click::project::FILE_NAME))?;
    let path = fs::canonicalize(root.join(source)).ok();
    match project.prepared_sources(&[(source.to_string(), path)])? {
        Some(click::project::UnitSelection::C(imports)) => Ok(imports),
        _ => Err(format!("the zlib project does not list `{source}`")),
    }
}

#[test]
fn pinned_zlib_empty_contract_verifies_offline_and_relocates() {
    let root = zlib_project();
    let imports =
        zlib_imports(root.path(), ZLIB_ADLER32).expect("offline locked zlib source closure");
    let proof = fs::read_to_string(root.path().join("empty.click")).unwrap();
    let verified = verify_c_prepared_sources(&proof, &imports).expect("unchanged zlib empty input");
    assert_eq!(verified.len(), 1);
    assert_eq!(
        verified[0].import_identity.as_deref(),
        Some(imports[0].identity())
    );
    let offset = proof.find("ensures").unwrap();
    let line = proof[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset - proof[..offset].rfind('\n').unwrap();
    let expanded = expand_c_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked zlib execution expansion");
    verify_c_prepared_sources(&expanded, &imports).expect("expanded zlib contract");
    let false_claim = proof.replace("ensures result == 1u64", "ensures result == 2u64");
    assert!(verify_c_prepared_sources(&false_claim, &imports).is_err());
    let header = root.path().join("../../vendor/zlib-1.3.1/zutil.h");
    fs::write(
        &header,
        format!(
            "{}\n/* changed original input */\n",
            fs::read_to_string(&header).unwrap()
        ),
    )
    .unwrap();
    assert!(zlib_imports(root.path(), ZLIB_ADLER32).is_err());
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 5s shared specification, expansion, and negative contracts"]
fn pinned_zlib_one_byte_matches_checked_shared_specification_offline() {
    let root = zlib_project();
    let imports =
        zlib_imports(root.path(), ZLIB_ADLER32).expect("offline locked unchanged C source");
    // Imported pure theorem interfaces are backed by their checked bodies in
    // this verification unit; no library result summary supplies the checksum.
    let proof = include_str!("../design/adler32/project/zlib/one-byte.click")
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        );
    let verified = verify_c_prepared_sources(&proof, &imports).expect("shared one-byte checksum");
    let implementation = verified
        .iter()
        .find(|claim| claim.function_block.signature().name() == "adler32_z")
        .expect("checked original implementation");
    assert_eq!(
        implementation.import_identity.as_deref(),
        Some(imports[0].identity())
    );
    let offset = proof.rfind("step_until(function.exit);").unwrap();
    let line = proof[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset - proof[..offset].rfind('\n').unwrap();
    let expanded = expand_c_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked original return expansion");
    verify_c_prepared_sources(&expanded, &imports).expect("expanded shared checksum proof");
    for invalid in [
        proof.replace(
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), 1u64, 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), 1u64, 1, 0) + 1;",
        ),
        proof.replace("requires len == 1u64;", "requires len == 0u64;"),
        proof.replace("views buf[0u64..1u64];", ""),
    ] {
        assert_ne!(proof, invalid);
        assert!(
            verify_sources_at(&invalid, &ProgramInputs::Prepared(&imports), line, column).is_err()
        );
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: original short loop, expansion, and authority mutations"]
fn pinned_zlib_short_loop_matches_checked_shared_specification_offline() {
    let root = zlib_project();
    let imports =
        zlib_imports(root.path(), ZLIB_ADLER32).expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/adler32/project/zlib/short-memory.click")
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        // Both the sidecar and prefix library import the shared specification.
        // Check each theorem body once, rather than assuming its interface.
        .replacen(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
            1,
        )
        .replace("import \"../adler32-spec-bridge.click\";", "");
    let checked = verify_c_prepared_sources(&proof, &imports)
        .expect("short-loop shared checksum, termination, and input preservation");
    assert_eq!(
        checked
            .iter()
            .filter(|claim| claim.function_block.signature().name() == "adler32_z")
            .count(),
        3,
        "checksum, packed bound, and byte preservation on one final path"
    );
    for claim in &checked {
        if claim.function_block.signature().name() != "adler32_z" {
            continue;
        }
        assert_eq!(
            claim.import_identity.as_deref(),
            Some(imports[0].identity())
        );
    }
    let offset = proof.find("step_until(loop(0).entry);").unwrap();
    let line = proof[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset - proof[..offset].rfind('\n').unwrap();
    let expanded = expand_c_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked original loop-entry expansion");
    verify_c_prepared_sources(&expanded, &imports).expect("expanded short-loop checksum proof");
    for invalid in [
        proof.replace("views buf[0u64..len];", "views buf[0u64..len - 1u64];"),
        proof.replacen("views buf[0u64..len];", "", 1),
        proof.replace(
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), 1, 0) + 1;",
        ),
        proof.replace(
            "invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));",
            "invariant to_integer(adler) == 2 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));",
        ),
        proof.replace(
            "invariant to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len));",
            "invariant to_integer(sum2) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len));",
        ),
        proof.replace(
            "ensures forall (k: uint64)",
            "ensures result == 0u64;\n ensures forall (k: uint64)",
        ),
    ] {
        assert_ne!(proof, invalid);
        assert!(
            verify_sources_at(&invalid, &ProgramInputs::Prepared(&imports), line, column).is_err()
        );
    }
}

#[test]
fn pinned_zlib_null_reset_is_independent_of_seed_and_nonunit_length() {
    let root = zlib_project();
    let imports = zlib_imports(root.path(), ZLIB_ADLER32).unwrap();
    let proof = include_str!("../design/adler32/project/zlib/reset.click");
    verify_c_prepared_sources(proof, &imports).expect("unchanged C null reset path");
    assert!(
        verify_c_prepared_sources(&proof.replace("result == 1u64", "result == 2u64"), &imports)
            .is_err()
    );
    // The original source's one-byte fast path precedes its null check.
    // That path needs byte-read authority and is outside the reset contract.
    assert!(
        verify_c_prepared_sources(
            &proof.replace("requires len != 1u64;", "requires len == 1u64;"),
            &imports
        )
        .is_err()
    );
}

#[test]
fn adler_c_rust_correspondence_requires_matched_inputs() {
    let source = include_str!("../design/adler32/project/adler2/correspondence.click").replace(
        "import \"../adler32-spec-u64.click\";",
        include_str!("../design/adler32/project/adler32-spec-u64.click"),
    );
    let verify_unit = |proof: &str, name: &str| {
        let start = proof.find(&format!("theorem {name}(")).unwrap();
        let offset = start + proof[start..].find(" by {").unwrap() + " by {".len();
        let offset = offset + proof[offset..].len() - proof[offset..].trim_start().len();
        let prefix = &proof[..offset];
        let line = prefix.bytes().filter(|&byte| byte == b'\n').count() + 1;
        let column = prefix.rsplit('\n').next().unwrap().len() + 1;
        verify_sources_at(proof, &ProgramInputs::Bundle(vec![]), line, column)
    };
    for name in [
        "adler_result_widen",
        "adler_c_rust_results",
        "adler_c_rust_reset",
    ] {
        verify_unit(&source, name).expect("checked correspondence body");
    }
    for (correct, incorrect) in [
        (
            "requires forall (k: uint64) { k < length implies c_bytes[k] == rust_bytes[k] };",
            "",
        ),
        (
            "requires to_integer(rust_result) == adler_spec_checksum_u64(rust_bytes, length, initial_a, initial_b);",
            "requires to_integer(rust_result) == adler_spec_checksum_u64(rust_bytes, length, initial_a + 1, initial_b);",
        ),
        (
            "ensures c_result == rust_result as uint64 by",
            "ensures c_result == rust_result as uint64 + 1u64 by",
        ),
        ("requires rust_a == 1u32;", "requires rust_a == 2u32;"),
    ] {
        assert!(source.contains(correct), "mutation target must exist");
        let invalid = source.replace(correct, incorrect);
        let name = if correct.contains("rust_a") {
            "adler_c_rust_reset"
        } else {
            "adler_c_rust_results"
        };
        assert!(verify_unit(&invalid, name).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: correspondence expansion and every shared-specification body"]
fn adler_c_rust_correspondence_expands_with_checked_dependencies() {
    let source = include_str!("../design/adler32/project/adler2/correspondence.click").replace(
        "import \"../adler32-spec-u64.click\";",
        include_str!("../design/adler32/project/adler32-spec-u64.click"),
    );
    click::surface::verify_click_theorems(&source)
        .expect("result correspondence and every shared-specification dependency body");
    let mut expanded = source.clone();
    for label in [
        "adler_result_widen.ensures_0",
        "adler_c_rust_results.ensures_0",
        "adler_c_rust_reset.ensures_0",
    ] {
        expanded = click::surface::expand_c_claim_source_by_label(&expanded, &[], label)
            .expect("checked C/Rust correspondence expansion");
    }
    click::surface::verify_click_theorems(&expanded)
        .expect("expanded correspondence and every shared-specification body");
}

/// The full-width specification, and its agreement with the int32 one, with
/// every dependency body. It states sums past `INT32_MAX` without narrowing:
/// the old spec's probe that the first 2^32 bytes sum to zero no longer goes
/// through, because a `uint64` length does not wrap to 0.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 20s full-width specification, its int32 bridge, and a wrap probe"]
fn adler_uint64_specification_agrees_with_the_int32_one_and_does_not_narrow() {
    let source = adler_specifications();
    let past_int32 = "theorem adler_byte_past_four_gib(bytes: uint8[]) {
 ensures adler_byte_sum_u64(bytes, 4294967297u64) == adler_byte_sum_u64(bytes, 4294967296u64) + to_integer(bytes[4294967296u64]) by {
  apply(adler_sum_append_u64(bytes, 4294967297u64));
  close();
 }
}";
    click::surface::verify_click_theorems(&format!("{source}\n{past_int32}"))
        .expect("the full-width specification, the bridge, and a sum past 2^32");
    let wrapped = "theorem adler_four_gib_wraps(bytes: uint8[], length: uint64) {
 requires length == 4294967296u64;
 ensures adler_byte_sum_u64(bytes, length) == 0 by {
  have length == 0u64 by close();
  rewrite(length, 0u64);
  apply(adler_sum_empty_u64(bytes, 0));
  close();
 }
}";
    assert!(
        click::surface::verify_click_theorems(&format!("{source}\n{wrapped}")).is_err(),
        "a uint64 length of 2^32 must not wrap to 0"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: unchanged DO16 checksum proof, checked helpers, and mutations"]
fn pinned_zlib_sixteen_block_matches_checked_shared_specification_offline() {
    let root = zlib_project();
    let imports =
        zlib_imports(root.path(), ZLIB_ADLER32).expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/adler32/project/zlib/sixteen.click")
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );
    let checked = verify_c_prepared_sources(&proof, &imports)
        .expect("DO16 shared checksum, termination, byte preservation, and all helper bodies");
    let contracts: Vec<_> = checked
        .iter()
        .filter(|claim| claim.function_block.signature().name() == "adler32_z")
        .collect();
    assert_eq!(contracts.len(), 2, "checksum and byte preservation");
    for claim in contracts {
        assert_eq!(
            claim.import_identity.as_deref(),
            Some(imports[0].identity())
        );
    }
    let offset = proof.find("step_until(loop(3).entry);").unwrap();
    let line = proof[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset - proof[..offset].rfind('\n').unwrap();
    let expanded = expand_c_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked original DO16 loop-entry expansion");
    verify_c_prepared_sources(&expanded, &imports).expect("expanded DO16 checksum proof");
    for invalid in [
        proof.replacen("views buf[0u64..len];", "", 1),
        proof.replacen("views buf[0u64..len];", "views buf[0u64..len - 1u64];", 1),
        proof.replace(
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), 16u64, 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), 16u64, 1, 0) + 1;",
        ),
        proof.replacen(
            "invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(16u64, len));",
            "invariant to_integer(adler) == 2 + adler_byte_sum(old(buf), zlib_prefix_count(16u64, len));",
            1,
        ),
        proof.replacen(
            "invariant to_integer(sum2) == to_integer(zlib_prefix_count(16u64, len)) + adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len));",
            "invariant to_integer(sum2) == adler_weighted_sum(old(buf), zlib_prefix_count(16u64, len), zlib_prefix_count(16u64, len));",
            1,
        ),
    ] {
        assert_ne!(proof, invalid);
        assert!(verify_c_prepared_sources(&invalid, &imports).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: repeated DO16 checksum, checked helpers, expansion, and mutations"]
fn pinned_zlib_repeated_blocks_match_checked_shared_specification_offline() {
    let root = zlib_project();
    let imports =
        zlib_imports(root.path(), ZLIB_ADLER32).expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/adler32/project/zlib/repeated.click")
        .replace(
            "import \"window.click\";",
            include_str!("../design/adler32/project/zlib/window.click"),
        )
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );
    let checked = verify_c_prepared_sources(&proof, &imports)
        .expect("repeated-block checksum, termination, byte preservation, and all helper bodies");
    let contracts: Vec<_> = checked
        .iter()
        .filter(|claim| claim.function_block.signature().name() == "adler32_z")
        .collect();
    assert_eq!(contracts.len(), 2, "checksum and byte preservation");
    for claim in contracts {
        assert_eq!(
            claim.import_identity.as_deref(),
            Some(imports[0].identity())
        );
    }
    let expanded = click::surface::expand_c_prepared_claim_source_by_label(
        &proof,
        &imports,
        "adler32_z.contract",
    )
    .expect("checked complete repeated-block certificate expansion");
    verify_c_prepared_sources(&expanded, &imports)
        .expect("expanded repeated-block checksum and every helper body");
    for invalid in [
        proof.replacen("views buf[0u64..len];", "", 1),
        proof.replacen("views buf[0u64..len];", "views buf[0u64..len - 1u64];", 1),
        proof.replace(
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), 1, 0) + 1;",
        ),
        proof.replacen(
            "invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));",
            "invariant to_integer(adler) == 2 + adler_byte_sum(old(buf), zlib_prefix_count(old(len), len));",
            1,
        ),
        proof.replacen(
            "invariant to_integer(sum2) == to_integer(zlib_prefix_count(old(len), len)) + adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len));",
            "invariant to_integer(sum2) == adler_weighted_sum(old(buf), zlib_prefix_count(old(len), len), zlib_prefix_count(old(len), len));",
            1,
        ),
    ] {
        assert_ne!(proof, invalid);
        assert!(verify_c_prepared_sources(&invalid, &imports).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: NMAX batch checksum, checked helpers, expansion, and mutations"]
fn pinned_zlib_nmax_batch_matches_checked_shared_specification_offline() {
    let root = zlib_project();
    let imports =
        zlib_imports(root.path(), ZLIB_ADLER32).expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/adler32/project/zlib/batch.click")
        .replace(
            "import \"batch-helpers.click\";",
            include_str!("../design/adler32/project/zlib/batch-helpers.click"),
        )
        .replace(
            "import \"window.click\";",
            include_str!("../design/adler32/project/zlib/window.click"),
        )
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );
    let checked = verify_c_prepared_sources(&proof, &imports)
        .expect("NMAX batch checksum, termination, byte preservation, and all helper bodies");
    let contracts: Vec<_> = checked
        .iter()
        .filter(|claim| claim.function_block.signature().name() == "adler32_z")
        .collect();
    assert_eq!(contracts.len(), 2, "checksum and byte preservation");
    for claim in contracts {
        assert_eq!(
            claim.import_identity.as_deref(),
            Some(imports[0].identity())
        );
    }
    let expanded = click::surface::expand_c_prepared_claim_source_by_label(
        &proof,
        &imports,
        "adler32_z.contract",
    )
    .expect("checked complete NMAX batch certificate expansion");
    verify_c_prepared_sources(&expanded, &imports)
        .expect("expanded NMAX batch checksum and every helper body");
    for invalid in [
        proof.replacen("views buf[0u64..len];", "", 1),
        proof.replacen("views buf[0u64..len];", "views buf[0u64..len - 1u64];", 1),
        proof.replace(
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), 5552u64, 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), 5552u64, 1, 0) + 1;",
        ),
        proof.replacen(
            "invariant to_integer(adler) == 1 + adler_byte_sum(old(buf), zlib_batch_count(n));",
            "invariant to_integer(adler) == 2 + adler_byte_sum(old(buf), zlib_batch_count(n));",
            1,
        ),
        proof.replacen(
            "invariant to_integer(sum2) == to_integer(zlib_batch_count(n)) + adler_weighted_sum(old(buf), zlib_batch_count(n), zlib_batch_count(n));",
            "invariant to_integer(sum2) == adler_weighted_sum(old(buf), zlib_batch_count(n), zlib_batch_count(n));",
            1,
        ),
    ] {
        assert_ne!(proof, invalid);
        assert!(verify_c_prepared_sources(&invalid, &imports).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: symbolic DO16 count, lane, and read-bound theorem bodies"]
fn pinned_zlib_window_lemmas_have_checked_bodies() {
    let source = include_str!("../design/adler32/project/zlib/window.click")
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );
    click::surface::verify_click_theorems(&source)
        .expect("all shared, native recurrence, and symbolic window bodies");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: shared checksum library and native block recurrence bodies"]
fn pinned_zlib_block_lemmas_have_checked_bodies() {
    let source = include_str!("../design/adler32/project/zlib/block.click")
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );
    click::surface::verify_click_theorems(&source)
        .expect("all shared and native recurrence bodies");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: seeded NMAX arithmetic, reduction, prefix composition, and expansion"]
fn pinned_zlib_seeded_batch_lemmas_have_checked_bodies() {
    let source = include_str!("../design/adler32/project/zlib/seeded-batch.click")
        .replace(
            "import \"batch-helpers.click\";",
            include_str!("../design/adler32/project/zlib/batch-helpers.click"),
        )
        .replace(
            "import \"window.click\";",
            include_str!("../design/adler32/project/zlib/window.click"),
        )
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );
    click::surface::verify_click_theorems(&source)
        .expect("seeded native recurrence, reductions, prefix composition, and all dependencies");
    let mut expanded = source.clone();
    for label in [
        "zlib_seeded_component_step.ensures_0",
        "zlib_seeded_reduced_components.ensures_0",
        "zlib_seeded_reduced_components.ensures_1",
        "zlib_seeded_reduced_components.ensures_2",
        "zlib_seeded_batch_concat.ensures_0",
        "zlib_seeded_batch_concat.ensures_1",
        "zlib_stream_batch_read_bound.ensures_0",
        "zlib_stream_batch_read_bound.ensures_1",
        "zlib_stream_batch_read_bound.ensures_2",
        "zlib_stream_batch_read_bound.ensures_3",
        "zlib_stream_batch_read_bound.ensures_4",
        "zlib_native_cursor_join.ensures_0",
        "zlib_stream_batch_lane_bound.ensures_0",
        "zlib_stream_remaining_step.ensures_0",
        "zlib_stream_remaining_step.ensures_1",
        "zlib_stream_remaining_step.ensures_2",
        "zlib_stream_remaining_step.ensures_3",
        "zlib_stream_prefix_step.ensures_0",
        "zlib_stream_capacity_step.ensures_0",
        "zlib_stream_tail_read_bound.ensures_0",
        "zlib_stream_tail_read_bound.ensures_1",
        "zlib_scalar_seeded_component_step.ensures_0",
        "zlib_stream_split_count.ensures_0",
        "zlib_raw_seeded_batch_concat.ensures_0",
        "zlib_raw_seeded_batch_concat.ensures_1",
        "zlib_components_pack.ensures_0",
        "zlib_stream_scalar_read_bound.ensures_0",
        "zlib_stream_scalar_read_bound.ensures_1",
        "zlib_stream_concat_bound.ensures_0",
    ] {
        expanded = click::surface::expand_c_claim_source_by_label(&expanded, &[], label)
            .expect("checked seeded batch certificate expansion");
    }
    click::surface::verify_click_theorems(&expanded)
        .expect("expanded seeded batch lemmas and every dependency");
    for (correct, incorrect) in [
        (
            "ensures to_integer(a + value as uint32 as uint64) == to_integer(a0) + adler_byte_sum(bytes, n + 1)",
            "ensures to_integer(a + value as uint32 as uint64) == to_integer(a0) + adler_byte_sum(bytes, n + 1) + 1",
        ),
        (
            "and to_integer(b + (a + value as uint32 as uint64)) == to_integer(b0) + to_integer(n + 1) * to_integer(a0)",
            "and to_integer(b + (a + value as uint32 as uint64)) == to_integer(n + 1) * to_integer(a0)",
        ),
        (
            "ensures to_integer(b % 65521u64) == adler_spec_b(bytes, prefix + length, 1, 0)",
            "ensures to_integer(b % 65521u64) == adler_spec_b(bytes, prefix + length, 1, 0) + 1",
        ),
    ] {
        let invalid = source.replacen(correct, incorrect, 1);
        assert_ne!(source, invalid);
        assert!(click::surface::verify_click_theorems(&invalid).is_err());
    }
}

/// A user-space compiler import in a fresh directory, with the given files
/// and arguments for `main.c`.
fn userspace_import(files: &[(&str, &str)], args: &[&str]) -> tempfile::TempDir {
    assert!(
        Path::new("/usr/bin/gcc").is_file(),
        "compiler fixture requires GCC at /usr/bin/gcc; provision it before scripts/check.sh"
    );
    let root = tempfile::tempdir().expect("isolated compiler fixture");
    for (path, contents) in files {
        let path = root.path().join(path);
        fs::create_dir_all(path.parent().unwrap()).unwrap();
        fs::write(path, contents).unwrap();
    }
    write_userspace_config(root.path(), args);
    root
}

fn write_userspace_config(root: &Path, args: &[&str]) {
    let config = json!({
        "schema": 1,
        "target": "x86_64-unknown-linux-gnu",
        "compiler": "/usr/bin/gcc",
        "working_directory": ".",
        "environment": {"allow": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"}},
        "sources": [{"logical_source": "main.c", "path": "main.c", "args": args, "artifact": "main.i"}]
    });
    fs::write(
        root.join("main.import-description.json"),
        serde_json::to_vec_pretty(&config).unwrap(),
    )
    .unwrap();
}

const LABEL_SOURCE: &str = r#"#include <stdint.h>
#include <string.h>
#include <limits.h>
#include "label.h"

int32_t label_fits(const char *label) {
    size_t length = strlen(label);
    if (length <= LABEL_LIMIT && LABEL_LIMIT < INT_MAX) {
        return 1;
    }
    return 0;
}
"#;

const LABEL_PROOF: &str = r#"target "x86_64-unknown-linux-gnu";
verifying "main.c";

int32 label_fits(const char* label) {
    let n: uint64;
    views click::c::string::cstr_at(label, n);
    ensures result == 0 or result == 1;
}
"#;

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 6s serial; the examples gate locks a modeled-header import"]
fn compiler_import_supplies_clicks_modeled_headers_beside_project_flags() {
    let project = userspace_import(
        &[
            ("main.c", LABEL_SOURCE),
            ("include/label.h", "#define LABEL_LIMIT LIMIT_FROM_BUILD\n"),
        ],
        &["-I", "include", "-DLIMIT_FROM_BUILD=16"],
    );
    let config = project.path().join("main.import-description.json");
    create_lock(&config).expect("lock a user-space import that includes libc headers");
    let artifact =
        fs::read_to_string(project.path().join(".click/captures/main/main.c.i")).unwrap();
    // The artifact names Click's headers, not the private directory GCC
    // read them from, so a refresh reproduces it byte for byte.
    assert!(artifact.contains("# 1 \"<string.h>\" 1 3 4"), "{artifact}");
    assert!(!artifact.contains("click-import-headers"), "{artifact}");
    assert!(artifact.contains("size_t strlen(const char *s);"));
    let lock: serde_json::Value = serde_json::from_slice(
        &fs::read(project.path().join(".click/captures/manifest.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(unit_lock(&lock)["schema"], 3);
    let opened = unit_lock(&lock)["sources"][0]["click_headers"]
        .as_object()
        .unwrap();
    assert_eq!(
        opened.keys().map(String::as_str).collect::<Vec<_>>(),
        ["limits.h", "stdint.h", "string.h"]
    );
    // The envelope's inputs are the source and the headers outside Click's.
    let source = unit_lock(&lock)["sources"][0]["path"].as_str().unwrap();
    let logical = unit_lock(&lock)["sources"][0]["logical_source"]
        .as_str()
        .unwrap();
    assert!(
        lock["units"]["main"]["lock"]["sources"][logical]["inputs"]
            .as_object()
            .unwrap()
            .keys()
            .filter(|path| *path != source)
            .all(|path| path.ends_with("include/label.h")),
        "{lock}"
    );
    let imports = load_imports(&config).expect("offline import");
    verify_c_prepared_sources(LABEL_PROOF, &imports).expect("strlen binds to Click's contract");
    // The call is checked against the contract: without its precondition
    // the proof fails, and so does a claim the length does not decide.
    let unreadable = LABEL_PROOF.replace(
        "    let n: uint64;\n    views click::c::string::cstr_at(label, n);\n",
        "",
    );
    assert!(verify_c_prepared_sources(&unreadable, &imports).is_err());
    let false_claim = LABEL_PROOF.replace("result == 0 or result == 1", "result == 1");
    assert!(verify_c_prepared_sources(&false_claim, &imports).is_err());
    create_lock(&config).unwrap();
    assert_eq!(
        artifact,
        fs::read_to_string(project.path().join(".click/captures/main/main.c.i")).unwrap(),
        "a refresh reproduces the artifact"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 9s serial; the examples gate locks a modeled-header import"]
fn compiler_import_refuses_unmodeled_system_headers_by_name() {
    let project = userspace_import(&[("main.c", "#include <ctype.h>\nint x;\n")], &[]);
    let config = project.path().join("main.import-description.json");
    let error = create_lock(&config).unwrap_err();
    assert!(
        error.contains("<ctype.h> is not one of Click's modeled system headers")
            && error.contains("docs/reference/language/c.md#system-headers")
            && !error.contains("click-import-headers"),
        "{error}"
    );
    assert!(
        !project
            .path()
            .join(".click/captures/main/main.c.i")
            .exists()
    );

    // `__has_include` finds a hosted header Click refuses, as it finds the C
    // library's, so the program cannot silently take the other branch.
    fs::write(
        project.path().join("main.c"),
        "#if __has_include(<time.h>)\n#include <time.h>\n#endif\nint x;\n",
    )
    .unwrap();
    let error = create_lock(&config).unwrap_err();
    assert!(error.contains("<time.h> is not one of"), "{error}");

    fs::write(
        project.path().join("main.c"),
        "#include <openssl/ssl.h>\nint x;\n",
    )
    .unwrap();
    let error = create_lock(&config).unwrap_err();
    assert!(
        error.contains("openssl/ssl.h: No such file or directory")
            && error.contains("the system headers Click supplies for x86_64-unknown-linux-gnu (userspace) are <inttypes.h>, <limits.h>"),
        "{error}"
    );

    fs::write(
        project.path().join("main.c"),
        "#include <pthread.h>\nint x;\n",
    )
    .unwrap();
    let error = create_lock(&config).unwrap_err();
    assert!(error.contains("modeled-pthread runtime"), "{error}");

    // The kernel target has only the freestanding headers Click models.
    let mut kernel: serde_json::Value =
        serde_json::from_slice(&fs::read(&config).unwrap()).unwrap();
    kernel["mode"] = json!("kernel");
    fs::write(&config, serde_json::to_vec_pretty(&kernel).unwrap()).unwrap();
    fs::write(
        project.path().join("main.c"),
        "#include <string.h>\nint x;\n",
    )
    .unwrap();
    let error = create_lock(&config).unwrap_err();
    assert!(
        error.contains("string.h: No such file or directory")
            && error.contains(
                "for x86_64-unknown-linux-gnu (kernel) are <inttypes.h>, <limits.h>, <stdbool.h>, <stdint.h>;"
            ),
        "{error}"
    );
    fs::write(
        project.path().join("main.c"),
        "#include <limits.h>\nint big(void) { return INT_MAX; }\n",
    )
    .unwrap();
    create_lock(&config).expect("kernel target models <limits.h>");
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 10s serial; the examples gate locks a modeled-header import"]
fn compiler_import_project_headers_precede_clicks_in_gcc_search_order() {
    let source = "#include <limits.h>\n#ifdef PROJECT_LIMITS\nint which(void) { return PROJECT_LIMITS; }\n#else\nint which(void) { return CHAR_MAX; }\n#endif\n";
    let project = userspace_import(
        &[
            ("main.c", source),
            ("quoted/limits.h", "#define PROJECT_LIMITS 1\n"),
            ("angled/limits.h", "#define PROJECT_LIMITS 2\n"),
        ],
        &["-iquote", "quoted"],
    );
    let config = project.path().join("main.import-description.json");
    let which = |args: &[&str]| {
        write_userspace_config(project.path(), args);
        create_lock(&config).unwrap();
        let imports = load_imports(&config).unwrap();
        let lock =
            fs::read_to_string(project.path().join(".click/captures/manifest.json")).unwrap();
        // GCC splits an expansion from a system header across line markers,
        // so compare the C without whitespace.
        let source = imports[0].source().split_whitespace().collect::<String>();
        (source, lock)
    };
    // `-iquote` serves only `#include "..."`, so `<limits.h>` is Click's.
    let (source, lock) = which(&["-iquote", "quoted"]);
    assert!(source.contains("return127;"), "{source}");
    assert!(lock.contains("\"limits.h\""));
    // A project `-I` or `-isystem` directory precedes the C library's place
    // in GCC's search, so its header is used, as GCC would use it, and Click's
    // is not opened.
    for args in [["-I", "angled"], ["-isystem", "angled"]] {
        let (source, lock) = which(&args);
        assert!(source.contains("return2;"), "{args:?}: {source}");
        assert!(!lock.contains("\"click_headers\""), "{args:?}: {lock}");
    }
    // A project header can still continue the search into Click's.
    fs::write(
        project.path().join("angled/limits.h"),
        "#include_next <limits.h>\n#define PROJECT_LIMITS (CHAR_MAX - 125)\n",
    )
    .unwrap();
    let (source, lock) = which(&["-I", "angled"]);
    assert!(source.contains("return(127-125);"), "{source}");
    assert!(lock.contains("\"limits.h\""));
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 3s serial; the examples gate locks a modeled-header import"]
fn compiler_import_lock_binds_clicks_header_text_and_catalog() {
    let project = userspace_import(
        &[
            ("main.c", LABEL_SOURCE),
            ("include/label.h", "#define LABEL_LIMIT 16\n"),
        ],
        &["-Iinclude"],
    );
    let config = project.path().join("main.import-description.json");
    let lock_path = project.path().join(".click/captures/manifest.json");
    create_lock(&config).unwrap();
    let original = fs::read_to_string(&lock_path).unwrap();
    load_imports(&config).unwrap();
    let mut lock: serde_json::Value = serde_json::from_str(&original).unwrap();
    // A lock prepared against a different `<string.h>` text, as after a
    // Click upgrade that changes the model, must be refreshed.
    unit_lock_mut(&mut lock)["sources"][0]["click_headers"]["string.h"] = json!("0".repeat(64));
    fs::write(&lock_path, serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    let error = load_imports(&config).unwrap_err();
    assert!(
        error.contains("Click's <string.h> changed since the import lock"),
        "{error}"
    );
    // So must one prepared against a different header set.
    let mut lock: serde_json::Value = serde_json::from_str(&original).unwrap();
    unit_lock_mut(&mut lock)["click_header_catalog_sha256"] = json!("0".repeat(64));
    fs::write(&lock_path, serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    let error = load_imports(&config).unwrap_err();
    assert!(
        error.contains("Click's system headers for x86_64-unknown-linux-gnu (userspace) changed"),
        "{error}"
    );
    // Dropping the record does not turn the lock into a legacy one.
    let mut lock: serde_json::Value = serde_json::from_str(&original).unwrap();
    unit_lock_mut(&mut lock)
        .as_object_mut()
        .unwrap()
        .remove("click_header_catalog_sha256");
    fs::write(&lock_path, serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    assert!(load_imports(&config).is_err());
    let mut lock: serde_json::Value = serde_json::from_str(&original).unwrap();
    unit_lock_mut(&mut lock)["schema"] = json!(2);
    unit_lock_mut(&mut lock)
        .as_object_mut()
        .unwrap()
        .remove("click_header_catalog_sha256");
    fs::write(&lock_path, serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    assert!(load_imports(&config).is_err());
    fs::write(&lock_path, &original).unwrap();
    load_imports(&config).unwrap();
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: unchanged zlib multiple NMAX batches, DO16 and scalar tails, and expansion"]
fn pinned_zlib_stream_matches_checked_shared_specification_offline() {
    let root = zlib_project();
    let imports =
        zlib_imports(root.path(), ZLIB_ADLER32).expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/adler32/project/zlib/stream.click")
        .replace(
            "import \"seeded-batch.click\";",
            include_str!("../design/adler32/project/zlib/seeded-batch.click"),
        )
        .replace(
            "import \"batch-helpers.click\";",
            include_str!("../design/adler32/project/zlib/batch-helpers.click"),
        )
        .replace(
            "import \"window.click\";",
            include_str!("../design/adler32/project/zlib/window.click"),
        )
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );
    let checked = verify_c_prepared_sources(&proof, &imports).expect(
        "multi-batch and tail checksum, termination, byte preservation, and all helper bodies",
    );
    let contracts: Vec<_> = checked
        .iter()
        .filter(|claim| claim.function_block.signature().name() == "adler32_z")
        .collect();
    assert_eq!(
        contracts.len(),
        4,
        "checksum and byte preservation for zero and nonzero post-batch tails"
    );
    for claim in contracts {
        assert_eq!(
            claim.import_identity.as_deref(),
            Some(imports[0].identity())
        );
    }
    let expanded = click::surface::expand_c_prepared_claim_source_by_label(
        &proof,
        &imports,
        "adler32_z.contract",
    )
    .expect("checked complete multi-batch and tail certificate expansion");
    verify_c_prepared_sources(&expanded, &imports)
        .expect("expanded multi-batch and tail checksum and every helper body");
    for invalid in [
        proof.replacen("views buf[0u64..len];", "", 1),
        proof.replacen("views buf[0u64..len];", "views buf[0u64..len - 1u64];", 1),
        proof.replacen(
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), 1, 0) + 1;",
            1,
        ),
        proof.replacen(
            "invariant buf == old(buf) + (old(len) - len);",
            "invariant buf == old(buf) + (old(len) - len) + 1;",
            1,
        ),
        proof.replacen(
            "invariant to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum",
            "invariant to_integer(adler) == 1 + to_integer(at(loop(4).entry, adler)) + adler_byte_sum",
            1,
        ),
    ] {
        assert_ne!(proof, invalid);
        assert!(verify_c_prepared_sources(&invalid, &imports).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: full-range original zlib checksum, all paths, dependency bodies and complete expansion"]
fn pinned_zlib_full_stream_matches_checked_shared_specification_offline() {
    let root = zlib_project();
    let imports =
        zlib_imports(root.path(), ZLIB_ADLER32).expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/adler32/project/zlib/full-stream.click")
        .replace(
            "import \"full-stream-helpers.click\";",
            include_str!("../design/adler32/project/zlib/full-stream-helpers.click"),
        )
        .replace(
            "import \"../adler2/bounded-count.click\";",
            include_str!("../design/adler32/project/adler2/bounded-count.click"),
        )
        .replace(
            "import \"seeded-batch.click\";",
            include_str!("../design/adler32/project/zlib/seeded-batch.click"),
        )
        .replace(
            "import \"batch-helpers.click\";",
            include_str!("../design/adler32/project/zlib/batch-helpers.click"),
        )
        .replace(
            "import \"window.click\";",
            include_str!("../design/adler32/project/zlib/window.click"),
        )
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );
    let checked = verify_c_prepared_sources(&proof, &imports).expect(
        "full signed-range checksum, termination, byte preservation, and all helper bodies",
    );
    let contracts: Vec<_> = checked
        .iter()
        .filter(|claim| claim.function_block.signature().name() == "adler32_z")
        .collect();
    assert_eq!(
        contracts.len(),
        8,
        "checksum and byte preservation across all four original return paths"
    );
    for claim in contracts {
        assert_eq!(
            claim.import_identity.as_deref(),
            Some(imports[0].identity())
        );
    }
    let expanded = click::surface::expand_c_prepared_claim_source_by_label(
        &proof,
        &imports,
        "adler32_z.contract",
    )
    .expect("checked complete full-range certificate expansion");
    verify_c_prepared_sources(&expanded, &imports)
        .expect("expanded full-range checksum and every helper body");
    for invalid in [
        proof.replacen("views buf[0u64..len];", "", 1),
        proof.replacen("views buf[0u64..len];", "views buf[0u64..len - 1u64];", 1),
        proof.replacen(
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), 1, 0) + 1;",
            1,
        ),
        proof.replacen(
            "invariant buf == old(buf) + (old(len) - len);",
            "invariant buf == old(buf) + (old(len) - len) + 1;",
            1,
        ),
        proof.replacen(
            "invariant to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum",
            "invariant to_integer(adler) == 1 + to_integer(at(loop(4).entry, adler)) + adler_byte_sum",
            1,
        ),
    ] {
        assert_ne!(proof, invalid);
        assert!(verify_c_prepared_sources(&invalid, &imports).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: full-range native count, cursor, capacity, concatenation guards and expansion"]
fn pinned_zlib_full_stream_lemmas_have_checked_bodies() {
    let source = include_str!("../design/adler32/project/zlib/full-stream-helpers.click")
        .replace(
            "import \"../adler2/bounded-count.click\";",
            include_str!("../design/adler32/project/adler2/bounded-count.click"),
        )
        .replace(
            "import \"seeded-batch.click\";",
            include_str!("../design/adler32/project/zlib/seeded-batch.click"),
        )
        .replace(
            "import \"batch-helpers.click\";",
            include_str!("../design/adler32/project/zlib/batch-helpers.click"),
        )
        .replace(
            "import \"window.click\";",
            include_str!("../design/adler32/project/zlib/window.click"),
        )
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );

    click::surface::verify_click_theorems(&source)
        .expect("full-range helpers and every dependency body");
    let mut expanded = source.clone();
    for label in [
        "zlib_full_prefix_observation.ensures_0",
        "zlib_full_prefix_observation.ensures_1",
        "zlib_full_prefix_pointer.ensures_0",
        "zlib_full_stream_remaining_step.ensures_0",
        "zlib_full_stream_remaining_step.ensures_1",
        "zlib_full_stream_remaining_step.ensures_2",
        "zlib_full_stream_remaining_step.ensures_3",
        "zlib_full_stream_prefix_step.ensures_0",
        "zlib_full_stream_split_count.ensures_0",
        "zlib_full_stream_scalar_read_bound.ensures_0",
        "zlib_full_stream_scalar_read_bound.ensures_1",
        "zlib_full_concat_bound.ensures_0",
        "zlib_full_chunk_bound.ensures_0",
        "zlib_full_pack_order.ensures_0",
    ] {
        expanded = click::surface::expand_c_claim_source_by_label(&expanded, &[], label)
            .expect("checked full-range helper certificate expansion");
    }
    click::surface::verify_click_theorems(&expanded)
        .expect("expanded full-range helpers and dependencies");
    for (correct, incorrect) in [
        (
            "requires total - remaining <= 2147483647u64;",
            "requires total - remaining <= 2147483648u64;",
        ),
        (
            "requires to_integer(first) + to_integer(second) <= 18446744073709551615;",
            "requires to_integer(first) + to_integer(second) <= 18446744073709551616;",
        ),
        (
            "ensures total - remaining < total by",
            "ensures total - remaining > total by",
        ),
        (
            "ensures zlib_prefix_count(total, middle) <= 2147483647 - zlib_prefix_count(middle, remaining) and defined",
            "ensures zlib_prefix_count(total, middle) < 2147483647 - zlib_prefix_count(middle, remaining) and defined",
        ),
    ] {
        let invalid = source.replacen(correct, incorrect, 1);
        assert_ne!(source, invalid);
        assert!(click::surface::verify_click_theorems(&invalid).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: full-range original zlib checksum, all seeds and paths, dependency bodies and complete expansion"]
fn pinned_zlib_canonical_seed_matches_checked_shared_specification_offline() {
    let root = zlib_project();
    let imports =
        zlib_imports(root.path(), ZLIB_ADLER32).expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/adler32/project/zlib/canonical.click")
        .replace(
            "import \"canonical-helpers.click\";",
            include_str!("../design/adler32/project/zlib/canonical-helpers.click"),
        )
        .replace(
            "import \"full-stream-helpers.click\";",
            include_str!("../design/adler32/project/zlib/full-stream-helpers.click"),
        )
        .replace(
            "import \"../adler2/bounded-count.click\";",
            include_str!("../design/adler32/project/adler2/bounded-count.click"),
        )
        .replace(
            "import \"seeded-batch.click\";",
            include_str!("../design/adler32/project/zlib/seeded-batch.click"),
        )
        .replace(
            "import \"batch-helpers.click\";",
            include_str!("../design/adler32/project/zlib/batch-helpers.click"),
        )
        .replace(
            "import \"window.click\";",
            include_str!("../design/adler32/project/zlib/window.click"),
        )
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );
    let checked = verify_c_prepared_sources(&proof, &imports).expect(
        "canonical-seed signed-range checksum, termination, byte preservation, and all helper bodies",
    );
    let contracts: Vec<_> = checked
        .iter()
        .filter(|claim| claim.function_block.signature().name() == "adler32_z")
        .collect();
    assert_eq!(
        contracts.len(),
        16,
        "checksum and byte preservation across four fast reductions, two short reductions, and both batch-tail returns"
    );
    for claim in contracts {
        assert_eq!(
            claim.import_identity.as_deref(),
            Some(imports[0].identity())
        );
    }
    let expanded = click::surface::expand_c_prepared_claim_source_by_label(
        &proof,
        &imports,
        "adler32_z.contract",
    )
    .expect("checked complete canonical-seed full-range certificate expansion");
    verify_c_prepared_sources(&expanded, &imports)
        .expect("expanded canonical-seed full-range checksum and every helper body");
    for invalid in [
        proof.replacen("views buf[0u64..len];", "", 1),
        proof.replacen("views buf[0u64..len];", "views buf[0u64..len - 1u64];", 1),
        proof.replacen(
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler))));",
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), to_integer(zlib_seed_a(old(adler))), to_integer(zlib_seed_b(old(adler)))) + 1;",
            1,
        ),
        proof.replacen(
            "invariant buf == old(buf) + (old(len) - len);",
            "invariant buf == old(buf) + (old(len) - len) + 1;",
            1,
        ),
        proof.replacen(
            "invariant to_integer(adler) == to_integer(at(loop(4).entry, adler)) + adler_byte_sum",
            "invariant to_integer(adler) == 1 + to_integer(at(loop(4).entry, adler)) + adler_byte_sum",
            1,
        ),
    ] {
        assert_ne!(proof, invalid);
        assert!(verify_c_prepared_sources(&invalid, &imports).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: canonical seed, reduction, unpacking and composition and expansion"]
fn pinned_zlib_canonical_seed_lemmas_have_checked_bodies() {
    let source = include_str!("../design/adler32/project/zlib/canonical-helpers.click")
        .replace(
            "import \"full-stream-helpers.click\";",
            include_str!("../design/adler32/project/zlib/full-stream-helpers.click"),
        )
        .replace(
            "import \"../adler2/bounded-count.click\";",
            include_str!("../design/adler32/project/adler2/bounded-count.click"),
        )
        .replace(
            "import \"seeded-batch.click\";",
            include_str!("../design/adler32/project/zlib/seeded-batch.click"),
        )
        .replace(
            "import \"batch-helpers.click\";",
            include_str!("../design/adler32/project/zlib/batch-helpers.click"),
        )
        .replace(
            "import \"window.click\";",
            include_str!("../design/adler32/project/zlib/window.click"),
        )
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );

    click::surface::verify_click_theorems(&source)
        .expect("full-range helpers and every dependency body");
    let mut expanded = source.clone();
    for label in [
        "zlib_general_raw_seeded_batch_concat.ensures_0",
        "zlib_general_raw_seeded_batch_concat.ensures_1",
        "zlib_general_components_pack.ensures_0",
        "zlib_reduce_once_below.ensures_0",
        "zlib_reduce_once_above.ensures_0",
        "zlib_seed_bounds.ensures_0",
        "zlib_one_seeded_components.ensures_0",
        "zlib_short_count_limit.ensures_0",
        "zlib_canonical_pack.ensures_0",
        "zlib_canonical_pack.ensures_1",
        "zlib_packed_integer_seed.ensures_0",
    ] {
        expanded = click::surface::expand_c_claim_source_by_label(&expanded, &[], label)
            .expect("checked full-range helper certificate expansion");
    }
    click::surface::verify_click_theorems(&expanded)
        .expect("expanded full-range helpers and dependencies");
    for (correct, incorrect) in [
        (
            "requires value <= 131041u64;",
            "requires value <= 131042u64;",
        ),
        (
            "to_integer(a % 65521u64) == adler_spec_a(bytes, prefix + length, initial_a) by",
            "to_integer(a % 65521u64) == adler_spec_a(bytes, prefix + length, initial_a) + 1 by",
        ),
        ("requires a <= 65520;", "requires a <= 65536;"),
        (
            "to_integer(zlib_seed_a(word)) == a and",
            "to_integer(zlib_seed_a(word)) == a + 1 and",
        ),
    ] {
        let invalid = source.replacen(correct, incorrect, 1);
        assert_ne!(source, invalid);
        assert!(click::surface::verify_click_theorems(&invalid).is_err());
    }
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: two actual zlib C updates, all callee and helper bodies, complete expansion"]
fn pinned_zlib_incremental_c_matches_checked_shared_specification_offline() {
    let root = zlib_project();
    let imports =
        zlib_imports(root.path(), "incremental.c").expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/adler32/project/zlib/incremental.click")
        .replace(
            "import \"canonical.click\";",
            include_str!("../design/adler32/project/zlib/canonical.click"),
        )
        .replace(
            "verifying \"../../vendor/zlib-1.3.1/adler32.c\";",
            "verifying \"incremental.c\";",
        )
        .replace(
            "import \"canonical-helpers.click\";",
            include_str!("../design/adler32/project/zlib/canonical-helpers.click"),
        )
        .replace(
            "import \"full-stream-helpers.click\";",
            include_str!("../design/adler32/project/zlib/full-stream-helpers.click"),
        )
        .replace(
            "import \"../adler2/bounded-count.click\";",
            include_str!("../design/adler32/project/adler2/bounded-count.click"),
        )
        .replace(
            "import \"seeded-batch.click\";",
            include_str!("../design/adler32/project/zlib/seeded-batch.click"),
        )
        .replace(
            "import \"batch-helpers.click\";",
            include_str!("../design/adler32/project/zlib/batch-helpers.click"),
        )
        .replace(
            "import \"window.click\";",
            include_str!("../design/adler32/project/zlib/window.click"),
        )
        .replace(
            "import \"block.click\";",
            include_str!("../design/adler32/project/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/adler32/project/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/adler32/project/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/adler32/project/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../adler32-spec-bridge.click\";",
            &adler_specifications(),
        );
    let checked = verify_c_prepared_sources(&proof, &imports).expect(
        "canonical-seed signed-range checksum, termination, byte preservation, and all helper bodies",
    );
    let contracts: Vec<_> = checked
        .iter()
        .filter(|claim| claim.function_block.signature().name() == "click_zlib_incremental")
        .collect();
    assert_eq!(
        contracts.len(),
        2,
        "two real C calls establish the whole checksum and preserve all bytes"
    );
    for claim in contracts {
        assert_eq!(
            claim.import_identity.as_deref(),
            Some(imports[0].identity())
        );
    }
    let expanded = click::surface::expand_c_prepared_claim_source_by_label(
        &proof,
        &imports,
        "click_zlib_incremental.contract",
    )
    .expect("checked complete canonical-seed full-range certificate expansion");
    verify_c_prepared_sources(&expanded, &imports)
        .expect("expanded canonical-seed full-range checksum and every helper body");
    for invalid in [
        proof.replacen("requires split <= len;", "requires split <= len + 1u64;", 1),
        proof.replacen("requires buf + split != 0;", "", 1),
        proof.replacen("requires buf + split != 0;\n views buf[0u64..len];", "requires buf + split != 0;", 1),
        proof.replacen("requires buf + split != 0;\n views buf[0u64..len];", "requires buf + split != 0;\n views buf[0u64..len - 1u64];", 1),
        proof.replacen(
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), to_integer(zlib_seed_a(old(seed))), to_integer(zlib_seed_b(old(seed))));",
            "ensures to_integer(result) == adler_spec_checksum_u64(old(buf), old(len), to_integer(zlib_seed_a(old(seed))), to_integer(zlib_seed_b(old(seed)))) + 1;",
            1,
        ),
    ] {
        assert_ne!(proof, invalid);
        assert!(verify_c_prepared_sources(&invalid, &imports).is_err());
    }
}

/// A full-sidecar project: the proofs live in their own directory, and a
/// `click.project.json` unit reads an external tree in its own layout. The
/// tree gains no files, the committed lock still loads after the whole
/// checkout moves, and changed inputs are refused.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 4s in the parallel gate"]
fn project_unit_verifies_an_external_tree_in_place() {
    assert!(
        Path::new("/usr/bin/gcc").is_file(),
        "compiler fixture requires GCC at /usr/bin/gcc; provision it before scripts/check.sh"
    );
    static NEXT: AtomicUsize = AtomicUsize::new(0);
    let base = std::env::temp_dir().join(format!(
        "click-project-unit-{}-{}",
        std::process::id(),
        NEXT.fetch_add(1, Ordering::Relaxed)
    ));
    let root = base.join("checkout");
    let upstream = root.join("vendor/label-1.0");
    let example = Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/label-build-flags");
    for (from, to) in [
        ("label_fit.c", "src/label_fit.c"),
        ("label_copy.c", "src/label_copy.c"),
        ("label.h", "src/label.h"),
        ("include/label_config.h", "src/include/label_config.h"),
    ] {
        let to = upstream.join(to);
        fs::create_dir_all(to.parent().unwrap()).unwrap();
        fs::copy(example.join(from), to).unwrap();
    }
    let proof = fs::read_to_string(example.join("label.click"))
        .unwrap()
        .replace(
            "verifying \"label_fit.c\";",
            "verifying \"../../vendor/label-1.0/src/label_fit.c\";",
        )
        .replace(
            "verifying \"label_copy.c\";",
            "verifying \"../../vendor/label-1.0/src/label_copy.c\";",
        );
    let sidecar = root.join("proofs/checks/label.click");
    fs::create_dir_all(sidecar.parent().unwrap()).unwrap();
    fs::write(&sidecar, &proof).unwrap();
    let project_file = root.join("proofs/click.project.json");
    let describe = |capacity: u32| {
        json!({
            "target": "x86_64-unknown-linux-gnu",
            "units": {"label": {
                "language": "c",
                "root": "../vendor/label-1.0",
                "compiler": "/usr/bin/gcc",
                "env": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"},
                "args": ["-Isrc/include", format!("-DLABEL_CAPACITY={capacity}")],
                "sources": {"src/label_fit.c": {}, "src/label_copy.c": {}}
            }}
        })
    };
    fs::write(&project_file, describe(32).to_string()).unwrap();
    let tree = |root: &Path| {
        let mut files = Vec::new();
        let mut pending = vec![root.to_path_buf()];
        while let Some(directory) = pending.pop() {
            for entry in fs::read_dir(&directory).unwrap() {
                let path = entry.unwrap().path();
                if path.is_dir() {
                    pending.push(path);
                } else {
                    files.push(path.strip_prefix(root).unwrap().to_path_buf());
                }
            }
        }
        files.sort();
        files
    };
    let before = tree(&upstream);

    click::project::Project::find(sidecar.parent().unwrap())
        .unwrap()
        .expect("the project above the sidecar")
        .lock()
        .expect("lock the external unit");
    assert_eq!(tree(&upstream), before, "the external tree gains no files");
    let load = |sidecar: &Path| match click::cli::read_verification_inputs(sidecar, &proof)? {
        click::cli::VerificationInput::Prepared(imports) => Ok(imports),
        _ => Err("expected the unit's prepared sources".to_string()),
    };
    let imports = load(&sidecar).expect("load the locked unit");
    assert_eq!(
        imports
            .iter()
            .map(|import| import.logical_source())
            .collect::<Vec<_>>(),
        [
            "../../vendor/label-1.0/src/label_fit.c",
            "../../vendor/label-1.0/src/label_copy.c"
        ]
    );
    verify_c_prepared_sources(&proof, &imports).expect("the external unit verifies");

    let moved = base.join("moved");
    fs::rename(&root, &moved).unwrap();
    let sidecar = moved.join("proofs/checks/label.click");
    load(&sidecar).expect("the lock loads after the checkout moves");

    let header = moved.join("vendor/label-1.0/src/include/label_config.h");
    let original = fs::read_to_string(&header).unwrap();
    fs::write(&header, format!("{original}/* edited */\n")).unwrap();
    let error = load(&sidecar).unwrap_err();
    assert!(
        error.contains("label_config.h") && error.contains("differs from its import lock"),
        "{error}"
    );
    fs::write(&header, original).unwrap();

    fs::write(
        moved.join("proofs/click.project.json"),
        describe(16).to_string(),
    )
    .unwrap();
    let error = load(&sidecar).unwrap_err();
    assert!(error.contains("does not match its description"), "{error}");
    let _ = fs::remove_dir_all(&base);
}

/// The files and directories under `root`, by relative path, with each file's
/// bytes: the inventory a run must leave unchanged.
#[cfg(not(feature = "fast-gate"))]
fn tree_inventory(root: &Path) -> std::collections::BTreeMap<PathBuf, Option<Vec<u8>>> {
    let mut inventory = std::collections::BTreeMap::new();
    let mut pending = vec![root.to_path_buf()];
    while let Some(directory) = pending.pop() {
        for entry in fs::read_dir(&directory).unwrap() {
            let path = entry.unwrap().path();
            let relative = path.strip_prefix(root).unwrap().to_path_buf();
            if path.is_dir() {
                inventory.insert(relative, None);
                pending.push(path);
            } else {
                inventory.insert(relative, Some(fs::read(&path).unwrap()));
            }
        }
    }
    inventory
}

/// Sets every file and directory under `root` read-only, or writable again.
#[cfg(not(feature = "fast-gate"))]
fn set_tree_writable(root: &Path, writable: bool) {
    use std::os::unix::fs::PermissionsExt;
    let mut pending = vec![root.to_path_buf()];
    while let Some(path) = pending.pop() {
        let directory = path.is_dir();
        if directory {
            pending.extend(fs::read_dir(&path).unwrap().map(|e| e.unwrap().path()));
        }
        let mode = match (directory, writable) {
            (true, true) => 0o755,
            (true, false) => 0o555,
            (false, true) => 0o644,
            (false, false) => 0o444,
        };
        fs::set_permissions(&path, fs::Permissions::from_mode(mode)).unwrap();
    }
}

#[cfg(not(feature = "fast-gate"))]
/// The foreign-layout example reads an upstream tree whose paths and names
/// Click did not choose, with its generated configuration header in an
/// out-of-tree build directory in the project. Locking and verifying a copy
/// whose upstream tree is read-only add and change no file in the tree,
/// reproduce the committed portable lock, and a changed upstream byte is
/// refused by the name of the file.
#[test]
#[ignore = "nightly: runs GCC to lock the foreign-layout example"]
fn foreign_layout_tree_is_read_in_place_and_never_written() {
    let copy = tempfile::tempdir().unwrap();
    let example = copy.path().join("foreign-layout");
    copy_tree(
        &Path::new(env!("CARGO_MANIFEST_DIR")).join("examples/foreign-layout"),
        &example,
    );
    let project = example.join("project");
    let upstream = example.join("upstream/RingQ-1.2");
    let committed = fs::read(project.join(".click/captures/manifest.json")).unwrap();
    fs::remove_file(project.join(".click/captures/manifest.json")).unwrap();
    fs::remove_dir_all(project.join(".click")).unwrap();
    let before = tree_inventory(&upstream);
    set_tree_writable(&upstream, false);
    let click = |args: &[&str]| {
        std::process::Command::new(env!("CARGO_BIN_EXE_click"))
            .args(args)
            .current_dir(&project)
            .output()
            .unwrap()
    };
    let locked = click(&["capture"]);
    let verified = click(&["verify", "ringq.click"]);
    let after = tree_inventory(&upstream);
    set_tree_writable(&upstream, true);
    assert!(
        locked.status.success(),
        "{}",
        String::from_utf8_lossy(&locked.stderr)
    );
    assert!(
        verified.status.success(),
        "{}",
        String::from_utf8_lossy(&verified.stderr)
    );
    assert_eq!(
        before, after,
        "locking and verifying changed the upstream tree"
    );
    assert_eq!(
        fs::read(project.join(".click/captures/manifest.json")).unwrap(),
        committed,
        "a fresh lock of the copy differs from the committed one"
    );
    let header = upstream.join("inc/ringq/RingQ.h");
    let mut bytes = fs::read(&header).unwrap();
    bytes[0] = b'#';
    fs::write(&header, bytes).unwrap();
    let stale = click(&["verify", "--locked", "ringq.click"]);
    let error = String::from_utf8_lossy(&stale.stderr);
    assert!(!stale.status.success());
    assert!(error.contains("RingQ.h"), "{error}");
}

#[cfg(not(feature = "fast-gate"))]
#[test]
#[ignore = "nightly: live CLI captures of two configured sources"]
fn capture_selects_sources_and_reuses_them_across_proof_layouts() {
    let project = tempfile::tempdir().unwrap();
    let root = project.path();
    fs::create_dir(root.join("src")).unwrap();
    fs::create_dir(root.join("proofs")).unwrap();
    fs::write(
        root.join("click.project.json"),
        r#"{"units":{"app":{"language":"c","compiler":"/usr/bin/gcc",
          "env":{"PATH":"/usr/bin:/bin","LC_ALL":"C"},
          "sources":{"src/first.c":{},"src/second.c":{}}}}}"#,
    )
    .unwrap();
    fs::write(root.join("src/first.c"), "int first(void) { return 42; }").unwrap();
    fs::write(root.join("src/second.c"), "int second(void) { return 7; }").unwrap();
    fs::write(
        root.join("proofs/first.click"),
        r#"verifying "../src/first.c"; int first() { ensures result == 42; }"#,
    )
    .unwrap();
    fs::write(
        root.join("src/second.click"),
        r#"verifying "second.c"; int second() { ensures result == 7; }"#,
    )
    .unwrap();
    let click = |args: &[&str]| {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_click"))
            .args(args)
            .current_dir(root)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{args:?}: {}",
            String::from_utf8_lossy(&output.stderr)
        );
    };
    let captures = root.join(click::project::ARTIFACT_DIRECTORY);
    click(&["capture", "proofs/first.click"]);
    assert!(root.join(click::project::LOCK_NAME).is_file());
    assert!(captures.join("app/src/first.c.i").is_file());
    assert!(!captures.join("app/src/second.c.i").exists());
    click(&["capture", "src/second.c"]);
    click(&["verify", "proofs/first.click"]);
    click(&["verify", "src/second.click"]);
    fs::write(root.join("src/second.c"), "int second(void) { return 8; }").unwrap();
    click(&["verify", "proofs/first.click"]);
}

#[cfg(not(feature = "fast-gate"))]
#[test]
#[ignore = "nightly: live capture and verification with source and header edits"]
fn verify_refreshes_only_the_captures_it_uses() {
    let project = tempfile::tempdir().unwrap();
    let root = project.path();
    fs::write(
        root.join("click.project.json"),
        r#"{"units":{"app":{"language":"c","compiler":"/usr/bin/gcc",
           "env":{"PATH":"/usr/bin:/bin","LC_ALL":"C"},
           "sources":{"first.c":{},"second.c":{}}}}}"#,
    )
    .unwrap();
    fs::write(root.join("value.h"), "#define VALUE 42\n").unwrap();
    for name in ["first", "second"] {
        fs::write(
            root.join(format!("{name}.c")),
            format!("#include \"value.h\"\nint {name}(void) {{ return VALUE; }}\n"),
        )
        .unwrap();
        fs::write(
            root.join(format!("{name}.click")),
            format!("verifying \"{name}.c\"; int {name}() {{ ensures result >= 42; }}"),
        )
        .unwrap();
    }
    let verify = |args: &[&str], expected_success: bool| {
        let output = std::process::Command::new(env!("CARGO_BIN_EXE_click"))
            .arg("verify")
            .args(args)
            .current_dir(root)
            .output()
            .unwrap();
        let stderr = String::from_utf8_lossy(&output.stderr).into_owned();
        assert_eq!(
            output.status.success(),
            expected_success,
            "{args:?}: {stderr}"
        );
        stderr
    };
    let manifest = root.join(click::project::LOCK_NAME);
    let captures = root.join(click::project::ARTIFACT_DIRECTORY).join("app");
    verify(&["--locked", "first.click"], false);
    assert!(!manifest.exists());
    assert!(verify(&["first.click"], true).contains("refreshing capture for `first.c`"));
    assert!(!captures.join("second.c.i").exists());
    verify(&["second.click"], true);

    fs::write(
        root.join("first.click"),
        "verifying \"first.c\"; int first() { ensures result > 41; }",
    )
    .unwrap();
    assert!(!verify(&["first.click"], true).contains("refreshing capture"));

    fs::write(
        root.join("first.c"),
        "#include \"value.h\"\nint first(void) { return VALUE + 1; }",
    )
    .unwrap();
    verify(&["--locked", "first.click"], false);
    assert!(verify(&["first.click"], true).contains("refreshing capture for `first.c`"));
    verify(&["--locked", "second.click"], true);

    fs::write(root.join("value.h"), "#define VALUE 43\n").unwrap();
    assert!(verify(&["first.click"], true).contains("refreshing capture for `first.c`"));
    verify(&["--locked", "second.click"], false);
    assert!(verify(&["second.click"], true).contains("refreshing capture for `second.c`"));
    verify(&["--locked", "first.click"], true);
}
