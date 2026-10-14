#![cfg(not(target_os = "macos"))]

//! Compiler-backed fixtures call the shared verification engine directly.
//! They require GNU GCC at `/usr/bin/gcc`, which macOS does not provide.

use click::surface::ProgramInputs;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicUsize, Ordering};

use click::languages::c::compiler_import::{create_lock, load_imports};
use click::surface::{
    expand_c0_prepared_tactic_source_at, verify_c0_prepared_sources, verify_sources_at,
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
#[ignore = "nightly: 3s in the parallel gate"]
fn compiler_import_fixture_verifies_targets_and_checked_expansion() {
    let project = Project::new();
    create_lock(&project.config()).expect("lock real compiler input");
    let imports = load_imports(&project.config()).expect("offline locked import");
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
    verify_sources_at(&proof, &ProgramInputs::Prepared(&imports), line, column)
        .expect("targeted imported proof");
    let expanded = expand_c0_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked compiler-backed tactic expansion");
    assert_ne!(expanded, proof);
    verify_c0_prepared_sources(&expanded, &imports).expect("expanded certificate verifies");
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
    verify_c0_prepared_sources(&batch.source, &imports).expect("batch compiler-backed expansion");
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
    click::surface::verify_c0_prepared_project(&scoped.with_entry_source(batch.source), &imports)
        .expect("batch project compiler-backed expansion");
    fs::write(project.0.join("main.click"), &expanded).unwrap();
    let reloaded = load_imports(&project.config()).expect("proof edits do not invalidate C input");
    verify_c0_prepared_sources(&expanded, &reloaded).expect("offline imported expanded proof");
}

#[test]
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
    assert!(verify_c0_prepared_sources(&project.proof(), &second).is_err());
    let corrected = project.proof().replace("15", "7");
    verify_c0_prepared_sources(&corrected, &second).expect("changed compiler-selected branch");
}

#[test]
#[ignore = "nightly: 5s in the parallel gate"]
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
#[ignore = "nightly: 5s in the parallel gate"]
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
    let error = verify_c0_prepared_sources(&project.proof(), &imports).unwrap_err();
    assert!(
        error.message().contains("context.h:2"),
        "{}",
        error.message()
    );
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn compiler_import_reproduces_header_existence_and_preserves_unsupported_bodies() {
    let project = Project::new();
    fs::write(
        project.0.join("context.h"),
        "#if __has_include(\"optional.h\")\n#include \"optional.h\"\n#else\n#define OPTIONAL_VALUE 15\n#endif\nstatic inline int from_header(void) { return OPTIONAL_VALUE; }\n",
    ).unwrap();
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    verify_c0_prepared_sources(&project.proof(), &imports).unwrap();
    let original_identity = imports[0].identity().to_string();
    fs::write(project.0.join("optional.h"), "#define OPTIONAL_VALUE 16\n").unwrap();
    // A locked import means the prepared snapshot, including the absence of
    // this header. Only an explicit refresh selects the newly added header.
    let still_locked = load_imports(&project.config()).unwrap();
    assert_eq!(still_locked[0].identity(), original_identity);
    verify_c0_prepared_sources(&project.proof(), &still_locked).unwrap();
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    assert_ne!(imports[0].identity(), original_identity);
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
#[ignore = "nightly: 1.5s in the parallel gate"]
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
#[ignore = "nightly: 3s in the parallel gate"]
fn compiler_import_preserves_explicit_external_assumption_reporting() {
    let project = Project::new();
    fs::write(
        project.0.join("main.c"),
        "int external_identity(int x);\nint caller(int x) { return external_identity(x); }\n",
    )
    .unwrap();
    let proof = "target \"x86_64-linux-kernel\";\nverifying \"main.c\";\nextern int32 external_identity(int32 x) { requires x >= 0; ensures result == x; }\nint32 caller(int32 x) { requires x >= 0; ensures result == x; }\n";
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    let assumptions = click::surface::c0_prepared_external_dependencies(proof, &imports).unwrap();
    assert_eq!(
        assumptions.get("caller"),
        Some(&vec!["external_identity".to_string()])
    );
    verify_c0_prepared_sources(proof, &imports).unwrap();
}

fn configure_userspace(project: &Project) {
    let mut config: serde_json::Value =
        serde_json::from_slice(&fs::read(project.config()).unwrap()).unwrap();
    config["target"] = json!("x86_64-linux-userspace");
    fs::write(
        project.config(),
        serde_json::to_vec_pretty(&config).unwrap(),
    )
    .unwrap();
}

#[test]
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
    let proof = "target \"x86_64-linux-userspace\"; verifying \"main.c\"; int answer() { ensures result == 42; } by { execute(); simp(); }";
    create_lock(&project.config()).unwrap();
    let imports = load_imports(&project.config()).unwrap();
    let verified = verify_c0_prepared_sources(proof, &imports).unwrap();
    assert!(verified.iter().all(|theorem| {
        theorem.target() == click::languages::c::target::CTarget::X86_64LinuxUserspace
            && theorem.import_identity.as_deref() == Some(imports[0].identity())
    }));
    let column = proof.find("execute();").unwrap() + 1;
    let expanded = expand_c0_prepared_tactic_source_at(proof, &imports, 1, column).unwrap();
    verify_c0_prepared_sources(&expanded, &imports).unwrap();
    // Both whole-file and selected-site checking must reject a target mismatch.
    let wrong = proof.replace("x86_64-linux-userspace", "x86_64-linux-kernel");
    let error = verify_c0_prepared_sources(&wrong, &imports).unwrap_err();
    assert!(
        error.message().contains("but the sidecar selects"),
        "{error:?}"
    );
    let column = wrong.find("execute();").unwrap() + 1;
    assert!(verify_sources_at(&wrong, &ProgramInputs::Prepared(&imports), 1, column).is_err());
    assert!(expand_c0_prepared_tactic_source_at(&wrong, &imports, 1, column).is_err());
    // Opened headers remain lock dependencies even when their bytes do not
    // affect the selected function.
    fs::write(project.0.join("profile.h"), "/* changed header */\n").unwrap();
    assert!(load_imports(&project.config()).is_err());
}

#[test]
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
    let original = fs::read(project.0.join("main.i")).unwrap();
    configure_userspace(&project);
    assert!(load_imports(&project.config()).is_err());
    create_lock(&project.config()).unwrap();
    let userspace = load_imports(&project.config()).unwrap();
    assert_eq!(original, fs::read(project.0.join("main.i")).unwrap());
    assert_ne!(kernel[0].identity(), userspace[0].identity());
    let proof = "target \"x86_64-linux-userspace\"; verifying \"main.c\"; int answer() { ensures result == 42; } by { execute(); simp(); }";
    assert!(verify_c0_prepared_sources(proof, &kernel).is_err());
    verify_c0_prepared_sources(proof, &userspace).unwrap();
}

#[test]
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
    assert!(!project.0.join("main.i").exists());
}

#[test]
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
    verify_c0_prepared_sources(&project.proof(), &imports).expect("the kept proof verifies");

    // Without the projection the same artifact is refused at the stray
    // assembly, and the configuration change is a different lock.
    fs::write(project.config(), &original_config).unwrap();
    create_lock(&project.config()).expect("lock the whole import");
    let imports = load_imports(&project.config()).expect("load the whole import");
    let error = verify_c0_prepared_sources(&project.proof(), &imports)
        .expect_err("the whole unit includes the stray assembly");
    assert!(
        error.message().contains("inline assembly"),
        "{}",
        error.message()
    );
}

#[test]
fn pinned_zlib_empty_contract_verifies_offline_and_relocates() {
    let root = tempfile::tempdir().expect("isolated offline zlib fixture");
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/zlib");
    for name in [
        "adler32.c",
        "zutil.h",
        "zlib.h",
        "zconf.h",
        "adler32.i",
        "empty.click",
        "empty.click.import.json",
        "empty.click.import.lock.json",
    ] {
        fs::copy(fixture.join(name), root.path().join(name)).expect(name);
    }
    let config = root.path().join("empty.click.import.json");
    let imports = load_imports(&config).expect("offline locked zlib source closure");
    let proof = fs::read_to_string(root.path().join("empty.click")).unwrap();
    let verified =
        verify_c0_prepared_sources(&proof, &imports).expect("unchanged zlib empty input");
    assert_eq!(verified.len(), 1);
    assert_eq!(
        verified[0].import_identity.as_deref(),
        Some(imports[0].identity())
    );
    let offset = proof.find("execute();").unwrap();
    let line = proof[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset - proof[..offset].rfind('\n').unwrap();
    let expanded = expand_c0_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked zlib execution expansion");
    verify_c0_prepared_sources(&expanded, &imports).expect("expanded zlib contract");
    let false_claim = proof.replace("ensures result == 1u64", "ensures result == 2u64");
    assert!(verify_c0_prepared_sources(&false_claim, &imports).is_err());
    let header = root.path().join("zutil.h");
    fs::write(
        &header,
        format!(
            "{}\n/* changed original input */\n",
            fs::read_to_string(&header).unwrap()
        ),
    )
    .unwrap();
    assert!(load_imports(&config).is_err());
}

#[test]
#[ignore = "nightly: 5s shared specification, expansion, and negative contracts"]
fn pinned_zlib_one_byte_matches_checked_shared_specification_offline() {
    let root = tempfile::tempdir().expect("isolated offline zlib one-byte fixture");
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/zlib");
    for name in [
        "adler32.c",
        "zutil.h",
        "zlib.h",
        "zconf.h",
        "adler32.i",
        "one-byte.click.import.json",
        "one-byte.click.import.lock.json",
    ] {
        fs::copy(fixture.join(name), root.path().join(name)).expect(name);
    }
    let config = root.path().join("one-byte.click.import.json");
    let imports = load_imports(&config).expect("offline locked unchanged C source");
    // Imported pure theorem interfaces are backed by their checked bodies in
    // this verification unit; no library result summary supplies the checksum.
    let proof = include_str!("../design/charon-trial/zlib/one-byte.click")
        .replace(
            "import \"../../adler32-spec.click\";",
            include_str!("../design/adler32-spec.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/charon-trial/zlib/byte.click"),
        );
    let verified = verify_c0_prepared_sources(&proof, &imports).expect("shared one-byte checksum");
    let implementation = verified
        .iter()
        .find(|claim| claim.function_block.signature().name() == "adler32_z")
        .expect("checked original implementation");
    assert_eq!(
        implementation.import_identity.as_deref(),
        Some(imports[0].identity())
    );
    let offset = proof.rfind("execute();").unwrap();
    let line = proof[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset - proof[..offset].rfind('\n').unwrap();
    let expanded = expand_c0_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked original return expansion");
    verify_c0_prepared_sources(&expanded, &imports).expect("expanded shared checksum proof");
    for invalid in [
        proof.replace(
            "ensures to_integer(result) == adler_spec_checksum(old(buf), 1, 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum(old(buf), 1, 1, 0) + 1;",
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
#[ignore = "nightly: original short loop, expansion, and authority mutations"]
fn pinned_zlib_short_loop_matches_checked_shared_specification_offline() {
    let root = tempfile::tempdir().expect("isolated offline zlib short-loop fixture");
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/zlib");
    for name in [
        "adler32.c",
        "zutil.h",
        "zlib.h",
        "zconf.h",
        "adler32.i",
        "short-memory.click.import.json",
        "short-memory.click.import.lock.json",
    ] {
        fs::copy(fixture.join(name), root.path().join(name)).expect(name);
    }
    let imports = load_imports(&root.path().join("short-memory.click.import.json"))
        .expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/charon-trial/zlib/short-memory.click")
        .replace(
            "import \"byte.click\";",
            include_str!("../design/charon-trial/zlib/byte.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/charon-trial/zlib/short-prefix.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/charon-trial/adler2/count-bridge.click"),
        )
        // Both the sidecar and prefix library import the shared specification.
        // Check each theorem body once, rather than assuming its interface.
        .replacen(
            "import \"../../adler32-spec.click\";",
            include_str!("../design/adler32-spec.click"),
            1,
        )
        .replace("import \"../../adler32-spec.click\";", "");
    let checked = verify_c0_prepared_sources(&proof, &imports)
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
    let offset = proof.find("execute_until(loop(0));").unwrap();
    let line = proof[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset - proof[..offset].rfind('\n').unwrap();
    let expanded = expand_c0_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked original loop-entry expansion");
    verify_c0_prepared_sources(&expanded, &imports).expect("expanded short-loop checksum proof");
    for invalid in [
        proof.replace("views buf[0u64..len];", "views buf[0u64..len - 1u64];"),
        proof.replacen("views buf[0u64..len];", "", 1),
        proof.replace(
            "ensures to_integer(result) == adler_spec_checksum(old(buf), old((int32)(uint32)len), 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum(old(buf), old((int32)(uint32)len), 1, 0) + 1;",
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
    let root = tempfile::tempdir().expect("isolated offline zlib reset fixture");
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/zlib");
    for name in [
        "adler32.c",
        "zutil.h",
        "zlib.h",
        "zconf.h",
        "adler32.i",
        "reset.click.import.json",
        "reset.click.import.lock.json",
    ] {
        fs::copy(fixture.join(name), root.path().join(name)).expect(name);
    }
    let imports = load_imports(&root.path().join("reset.click.import.json")).unwrap();
    let proof = include_str!("../design/charon-trial/zlib/reset.click");
    verify_c0_prepared_sources(proof, &imports).expect("unchanged C null reset path");
    assert!(
        verify_c0_prepared_sources(&proof.replace("result == 1u64", "result == 2u64"), &imports)
            .is_err()
    );
    // The original source's one-byte fast path precedes its null check.
    // That path needs byte-read authority and is outside the reset contract.
    assert!(
        verify_c0_prepared_sources(
            &proof.replace("requires len != 1u64;", "requires len == 1u64;"),
            &imports
        )
        .is_err()
    );
}

#[test]
#[ignore = "nightly: unchanged DO16 checksum proof, checked helpers, and mutations"]
fn pinned_zlib_sixteen_block_matches_checked_shared_specification_offline() {
    let root = tempfile::tempdir().expect("isolated offline zlib DO16 fixture");
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/zlib");
    for name in [
        "adler32.c",
        "zutil.h",
        "zlib.h",
        "zconf.h",
        "adler32.i",
        "sixteen.click.import.json",
        "sixteen.click.import.lock.json",
    ] {
        fs::copy(fixture.join(name), root.path().join(name)).expect(name);
    }
    let imports = load_imports(&root.path().join("sixteen.click.import.json"))
        .expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/charon-trial/zlib/sixteen.click")
        .replace(
            "import \"block.click\";",
            include_str!("../design/charon-trial/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/charon-trial/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/charon-trial/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/charon-trial/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../../adler32-spec.click\";",
            include_str!("../design/adler32-spec.click"),
        );
    let checked = verify_c0_prepared_sources(&proof, &imports)
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
    let offset = proof.find("execute_until(loop(3));").unwrap();
    let line = proof[..offset]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = offset - proof[..offset].rfind('\n').unwrap();
    let expanded = expand_c0_prepared_tactic_source_at(&proof, &imports, line, column)
        .expect("checked original DO16 loop-entry expansion");
    verify_c0_prepared_sources(&expanded, &imports).expect("expanded DO16 checksum proof");
    for invalid in [
        proof.replacen("views buf[0u64..len];", "", 1),
        proof.replacen("views buf[0u64..len];", "views buf[0u64..len - 1u64];", 1),
        proof.replace(
            "ensures to_integer(result) == adler_spec_checksum(old(buf), 16, 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum(old(buf), 16, 1, 0) + 1;",
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
        assert!(verify_c0_prepared_sources(&invalid, &imports).is_err());
    }
}

#[test]
#[ignore = "nightly: repeated DO16 checksum, checked helpers, expansion, and mutations"]
fn pinned_zlib_repeated_blocks_match_checked_shared_specification_offline() {
    let root = tempfile::tempdir().expect("isolated offline zlib repeated-block fixture");
    let fixture = Path::new(env!("CARGO_MANIFEST_DIR")).join("design/charon-trial/zlib");
    for name in [
        "adler32.c",
        "zutil.h",
        "zlib.h",
        "zconf.h",
        "adler32.i",
        "repeated.click.import.json",
        "repeated.click.import.lock.json",
    ] {
        fs::copy(fixture.join(name), root.path().join(name)).expect(name);
    }
    let imports = load_imports(&root.path().join("repeated.click.import.json"))
        .expect("offline locked unchanged zlib source");
    let proof = include_str!("../design/charon-trial/zlib/repeated.click")
        .replace(
            "import \"window.click\";",
            include_str!("../design/charon-trial/zlib/window.click"),
        )
        .replace(
            "import \"block.click\";",
            include_str!("../design/charon-trial/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/charon-trial/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/charon-trial/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/charon-trial/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../../adler32-spec.click\";",
            include_str!("../design/adler32-spec.click"),
        );
    let checked = verify_c0_prepared_sources(&proof, &imports)
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
    let expanded = click::surface::expand_c0_prepared_claim_source_by_label(
        &proof,
        &imports,
        "adler32_z.contract",
    )
    .expect("checked complete repeated-block certificate expansion");
    verify_c0_prepared_sources(&expanded, &imports)
        .expect("expanded repeated-block checksum and every helper body");
    for invalid in [
        proof.replacen("views buf[0u64..len];", "", 1),
        proof.replacen("views buf[0u64..len];", "views buf[0u64..len - 1u64];", 1),
        proof.replace(
            "ensures to_integer(result) == adler_spec_checksum(old(buf), old((int32)(uint32)len), 1, 0);",
            "ensures to_integer(result) == adler_spec_checksum(old(buf), old((int32)(uint32)len), 1, 0) + 1;",
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
        assert!(verify_c0_prepared_sources(&invalid, &imports).is_err());
    }
}

#[test]
#[ignore = "nightly: symbolic DO16 count, lane, and read-bound theorem bodies"]
fn pinned_zlib_window_lemmas_have_checked_bodies() {
    let source = include_str!("../design/charon-trial/zlib/window.click")
        .replace(
            "import \"block.click\";",
            include_str!("../design/charon-trial/zlib/block.click"),
        )
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/charon-trial/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/charon-trial/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/charon-trial/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../../adler32-spec.click\";",
            include_str!("../design/adler32-spec.click"),
        );
    click::surface::verify_click_theorems(&source)
        .expect("all shared, native recurrence, and symbolic window bodies");
}

#[test]
#[ignore = "nightly: shared checksum library and native block recurrence bodies"]
fn pinned_zlib_block_lemmas_have_checked_bodies() {
    let source = include_str!("../design/charon-trial/zlib/block.click")
        .replace(
            "import \"short-prefix.click\";",
            include_str!("../design/charon-trial/zlib/short-prefix.click"),
        )
        .replace(
            "import \"byte.click\";",
            include_str!("../design/charon-trial/zlib/byte.click"),
        )
        .replace(
            "import \"../adler2/count-bridge.click\";",
            include_str!("../design/charon-trial/adler2/count-bridge.click"),
        )
        .replace(
            "import \"../../adler32-spec.click\";",
            include_str!("../design/adler32-spec.click"),
        );
    click::surface::verify_click_theorems(&source)
        .expect("all shared and native recurrence bodies");
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
        "target": "x86_64-linux-userspace",
        "compiler": "/usr/bin/gcc",
        "working_directory": ".",
        "environment": {"allow": {"PATH": "/usr/bin:/bin", "LC_ALL": "C"}},
        "sources": [{"logical_source": "main.c", "path": "main.c", "args": args, "artifact": "main.i"}]
    });
    fs::write(
        root.join("main.click.import.json"),
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

const LABEL_PROOF: &str = r#"target "x86_64-linux-userspace";
verifying "main.c";

int32 label_fits(const char* label) {
    requires cstr_readable(label);
    ensures result == 0 or result == 1;
} by {
    execute();
    simp();
}
"#;

#[test]
#[ignore = "nightly: 6s serial; the examples gate locks a modeled-header import"]
fn compiler_import_supplies_clicks_modeled_headers_beside_project_flags() {
    let project = userspace_import(
        &[
            ("main.c", LABEL_SOURCE),
            ("include/label.h", "#define LABEL_LIMIT LIMIT_FROM_BUILD\n"),
        ],
        &["-I", "include", "-DLIMIT_FROM_BUILD=16"],
    );
    let config = project.path().join("main.click.import.json");
    create_lock(&config).expect("lock a user-space import that includes libc headers");
    let artifact = fs::read_to_string(project.path().join("main.i")).unwrap();
    // The artifact names Click's headers, not the private directory GCC
    // read them from, so a refresh reproduces it byte for byte.
    assert!(artifact.contains("# 1 \"<string.h>\" 1 3 4"), "{artifact}");
    assert!(!artifact.contains("click-import-headers"), "{artifact}");
    assert!(artifact.contains("size_t strlen(const char *s);"));
    let lock: serde_json::Value = serde_json::from_slice(
        &fs::read(project.path().join("main.click.import.lock.json")).unwrap(),
    )
    .unwrap();
    assert_eq!(lock["schema"], 3);
    let opened = lock["sources"][0]["click_headers"].as_object().unwrap();
    assert_eq!(
        opened.keys().map(String::as_str).collect::<Vec<_>>(),
        ["limits.h", "stdint.h", "string.h"]
    );
    assert!(
        lock["sources"][0]["dependencies"]
            .as_object()
            .unwrap()
            .keys()
            .all(|path| path.ends_with("include/label.h")),
        "{lock}"
    );
    let imports = load_imports(&config).expect("offline import");
    verify_c0_prepared_sources(LABEL_PROOF, &imports).expect("strlen binds to Click's contract");
    // The call is checked against the contract: without its precondition
    // the proof fails, and so does a claim the length does not decide.
    let unreadable = LABEL_PROOF.replace("    requires cstr_readable(label);\n", "");
    assert!(verify_c0_prepared_sources(&unreadable, &imports).is_err());
    let false_claim = LABEL_PROOF.replace("result == 0 or result == 1", "result == 1");
    assert!(verify_c0_prepared_sources(&false_claim, &imports).is_err());
    create_lock(&config).unwrap();
    assert_eq!(
        artifact,
        fs::read_to_string(project.path().join("main.i")).unwrap(),
        "a refresh reproduces the artifact"
    );
}

#[test]
#[ignore = "nightly: 9s serial; the examples gate locks a modeled-header import"]
fn compiler_import_refuses_unmodeled_system_headers_by_name() {
    let project = userspace_import(&[("main.c", "#include <stdio.h>\nint x;\n")], &[]);
    let config = project.path().join("main.click.import.json");
    let error = create_lock(&config).unwrap_err();
    assert!(
        error.contains("<stdio.h> is not one of Click's modeled system headers")
            && error.contains("docs/reference/language/c.md#system-headers")
            && !error.contains("click-import-headers"),
        "{error}"
    );
    assert!(!project.path().join("main.i").exists());

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
            && error.contains("the system headers Click supplies for x86_64-linux-userspace are <inttypes.h>, <limits.h>"),
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
    kernel["target"] = json!("x86_64-linux-kernel");
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
                "for x86_64-linux-kernel are <inttypes.h>, <limits.h>, <stdbool.h>, <stdint.h>;"
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
    let config = project.path().join("main.click.import.json");
    let which = |args: &[&str]| {
        write_userspace_config(project.path(), args);
        create_lock(&config).unwrap();
        let imports = load_imports(&config).unwrap();
        let lock = fs::read_to_string(project.path().join("main.click.import.lock.json")).unwrap();
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
#[ignore = "nightly: 3s serial; the examples gate locks a modeled-header import"]
fn compiler_import_lock_binds_clicks_header_text_and_catalog() {
    let project = userspace_import(
        &[
            ("main.c", LABEL_SOURCE),
            ("include/label.h", "#define LABEL_LIMIT 16\n"),
        ],
        &["-Iinclude"],
    );
    let config = project.path().join("main.click.import.json");
    let lock_path = project.path().join("main.click.import.lock.json");
    create_lock(&config).unwrap();
    let original = fs::read_to_string(&lock_path).unwrap();
    load_imports(&config).unwrap();
    let mut lock: serde_json::Value = serde_json::from_str(&original).unwrap();
    // A lock prepared against a different `<string.h>` text, as after a
    // Click upgrade that changes the model, must be refreshed.
    lock["sources"][0]["click_headers"]["string.h"] = json!("0".repeat(64));
    fs::write(&lock_path, serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    let error = load_imports(&config).unwrap_err();
    assert!(
        error.contains("Click's <string.h> changed since the import lock"),
        "{error}"
    );
    // So must one prepared against a different header set.
    let mut lock: serde_json::Value = serde_json::from_str(&original).unwrap();
    lock["click_header_catalog_sha256"] = json!("0".repeat(64));
    fs::write(&lock_path, serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    let error = load_imports(&config).unwrap_err();
    assert!(
        error.contains("Click's system headers for x86_64-linux-userspace changed"),
        "{error}"
    );
    // Dropping the record does not turn the lock into a legacy one.
    let mut lock: serde_json::Value = serde_json::from_str(&original).unwrap();
    lock.as_object_mut()
        .unwrap()
        .remove("click_header_catalog_sha256");
    fs::write(&lock_path, serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    assert!(load_imports(&config).is_err());
    let mut lock: serde_json::Value = serde_json::from_str(&original).unwrap();
    lock["schema"] = json!(2);
    lock.as_object_mut()
        .unwrap()
        .remove("click_header_catalog_sha256");
    fs::write(&lock_path, serde_json::to_vec_pretty(&lock).unwrap()).unwrap();
    assert!(load_imports(&config).is_err());
    fs::write(&lock_path, &original).unwrap();
    load_imports(&config).unwrap();
}
