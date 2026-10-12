use click::surface::ProgramInputs;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

use sha2::{Digest, Sha256};

use click::cli::{
    CInput, files_with_extension, project_sidecars, read_c_inputs_for_project,
    read_click_project_at_root, read_verifying_sources, source_refs,
};
use click::instrumentation::{self, ArtifactReuseRejection};
use click::languages::refresh_compiler_import;
use click::surface::{
    c0_tactic_source_position, project_tactic_source_position, verify_c0_prepared_project,
    verify_c0_project, verify_c0_sources, verify_program_prepared_project,
};

#[path = "support/limits.rs"]
mod limits;
#[path = "support/tactic_work.rs"]
mod tactic_work;

const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
/// Set by the gate when the pinned C++ exporter is not installed.
const SKIP_CPP_FRONTEND: &str = "CLICK_SKIP_CPP_FRONTEND";
const SOURCE_MANIFEST: &str = "SOURCE.sha256";
const SOURCE_METADATA: &str = "SOURCE.md";

/// Known-broken or pathologically slow projects, skipped by default so the
/// suite is a meaningful green gate. Run one with `CLICK_EXAMPLE=<name>`, or
/// all of them with `CLICK_RUN_QUARANTINED=1`. Each entry names the reason;
/// remove entries as they are fixed (see docs/internals/testing.md).
const QUARANTINED: &[(&str, &str)] = &[(
    "multifile-registry",
    "`registry_run`'s entry cannot evaluate an owned field path into another module's \
     function-local static struct array (`owns beta::record_beta::batches[0].value`: \
     no known pointee type, the gap mdtests/initialized_aggregate_static_arrays.md pins); \
     past it, ordinary-entry static-state transport does not yet certify its cross-file \
     caller (issues/static-state-caller-transport.md)",
)];

/// The artifact reuse rejection ratchet (`docs/internals/testing.md`) over
/// every example project; see `tests/mdtests.rs` for the rule.
const ARTIFACT_REUSE_REJECTION_BASELINE: &[(ArtifactReuseRejection, usize)] = &[];

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn frozen_shared_heap_lifecycles_verify() {
    let project = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("design")
        .join("shared-heap-probes");
    run_example_in_thread(&project).unwrap_or_else(|error| panic!("{error}"));
}

#[test]
fn frozen_mutex_parity_verifies() {
    let project = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("design/concurrency-probes");
    run_example_in_thread(&project).unwrap_or_else(|error| panic!("{error}"));
}

#[test]
#[ignore = "nightly: 12s debug verify"]
fn frozen_mutex_composition_verifies() {
    let project = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("design/concurrency-composition");
    run_example_in_thread(&project).unwrap_or_else(|error| panic!("{error}"));
}

#[test]
fn concurrency_mutex_composition_source_is_frozen() {
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("design/concurrency-composition/shared_log.c");
    let bytes = fs::read(&source).expect("the frozen shared log C source exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "6a112d82a1f1bf3cae25d03f0310bc78a14be039bb65c64f5a5ffdebbf0ebab9",
        "the shared log proof must use the selected C source unchanged"
    );
}

#[test]
fn frozen_publication_verifies() {
    let project = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("design/concurrency-publication");
    run_example_in_thread(&project).unwrap_or_else(|error| panic!("{error}"));
}

#[test]
fn concurrency_publication_source_is_frozen() {
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("design/concurrency-publication/publication.c");
    let bytes = fs::read(&source).expect("the frozen publication C source exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "0b267dcc090dfbf990b915691c40b8b1c0016a811775db619022000b9d5e004c",
        "the publication proof must use the selected C source unchanged"
    );
}

#[test]
fn concurrency_mutex_parity_source_is_frozen() {
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("design/concurrency-probes/mutex_held_parity.c");
    let bytes = fs::read(&source).expect("the frozen parity C source exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "719d577494b9b2aa43aaa269e43bf8201e57a4039ff84ce9f6ec900571226d51",
        "the parity proof must use the selected C source unchanged"
    );
}

#[test]
#[ignore = "nightly: 23s in the parallel gate"]
fn canonical_charon_examples_verify_locked_inputs() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let inventory: Vec<serde_json::Value> =
        serde_json::from_slice(&fs::read(root.join("design/charon-trial/parity.json")).unwrap())
            .unwrap();
    let mut checked = 0;
    for entry in inventory {
        let config = root.join(entry["config"].as_str().unwrap());
        let metadata: serde_json::Value =
            serde_json::from_slice(&fs::read(&config).unwrap()).unwrap();
        assert_eq!(metadata["language"], "rust");
        assert_eq!(metadata["schema"], 3);
        assert!(
            metadata.get("backend").is_none(),
            "canonical Rust examples use the native default"
        );
        run_example_in_thread(config.parent().unwrap()).unwrap_or_else(|error| panic!("{error}"));
        checked += 1;
    }
    assert_eq!(checked, 16);
}

/// Examples the ten-minute gate leaves to the nightly run, with the
/// measurement that put each one here.
const NIGHTLY: &[(&str, &str)] = &[
    (
        "rbtree-insert",
        "verifies in about 118 s on 20 cores, most of the gate's budget alone (2026-10-06)",
    ),
    (
        "rbtree-erase",
        "erase sidecars take minutes; the earlier unlink corpus measured 176 s (2026-10-08)",
    ),
];

#[test]
fn example_projects() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let examples_dir = manifest_dir.join("examples");
    let requested = std::env::var_os("CLICK_EXAMPLE");
    let run_quarantined = requested.is_some() || std::env::var_os(RUN_QUARANTINED).is_some();
    let mut projects = fs::read_dir(&examples_dir)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", examples_dir.display()))
        .map(|entry| {
            entry
                .unwrap_or_else(|error| panic!("failed to read examples directory entry: {error}"))
                .path()
        })
        .filter(|path| path.is_dir())
        .filter(|path| {
            requested.as_ref().is_none_or(|requested| {
                path.file_name()
                    .is_some_and(|name| name == requested.as_os_str())
            })
        })
        .collect::<Vec<_>>();
    projects.sort();

    // The gate has a ten-minute budget. An example that takes most of it
    // alone runs in the nightly gate (`scripts/check.sh --nightly`), or on
    // request by name.
    if requested.is_none() && std::env::var_os("CLICK_NIGHTLY").is_none() {
        projects.retain(|path| {
            let name = path.file_name().and_then(|name| name.to_str());
            match name.and_then(|name| NIGHTLY.iter().find(|(nightly, _)| *nightly == name)) {
                Some((name, reason)) => {
                    println!("SKIPPING nightly example `{name}`: {reason}");
                    false
                }
                None => true,
            }
        });
    }
    // A gate run on a machine without the pinned C++ toolchain
    // (`scripts/check.sh`) leaves out the examples that refresh a C++ import.
    let skipped_cpp = std::env::var_os(SKIP_CPP_FRONTEND).is_some() && {
        let before = projects.len();
        projects.retain(|path| {
            let cpp = imports_cpp(path);
            if cpp {
                println!(
                    "SKIPPING C++ example `{}`: {SKIP_CPP_FRONTEND} is set",
                    path.display()
                );
            }
            !cpp
        });
        projects.len() != before
    };
    // CI splits the examples across jobs to stay inside the gate's time
    // budget: `EXAMPLE_PARTITION=k/n` keeps every n-th project from the k-th,
    // over the sorted names, so the shards cover them exactly once.
    if let Ok(partition) = std::env::var("EXAMPLE_PARTITION") {
        let (shard, total) = partition
            .split_once('/')
            .and_then(|(shard, total)| {
                Some((shard.parse::<usize>().ok()?, total.parse::<usize>().ok()?))
            })
            .filter(|(shard, total)| (1..=*total).contains(shard))
            .unwrap_or_else(|| {
                panic!("EXAMPLE_PARTITION must be `k/n` with 1 <= k <= n, got `{partition}`")
            });
        let mut index = 0;
        projects.retain(|_| {
            index += 1;
            (index - 1) % total == shard - 1
        });
    }
    if !run_quarantined {
        projects.retain(|path| {
            let name = path.file_name().and_then(|name| name.to_str());
            let quarantine = name.and_then(|name| {
                QUARANTINED
                    .iter()
                    .find(|(quarantined, _)| *quarantined == name)
            });
            match quarantine {
                Some((name, reason)) => {
                    println!("SKIPPING quarantined example `{name}`: {reason}");
                    false
                }
                None => true,
            }
        });
        assert!(
            !projects.is_empty(),
            "every example project is quarantined; run them with {RUN_QUARANTINED}=1",
        );
    }

    assert!(
        !projects.is_empty(),
        "expected at least one matching example project in `{}`",
        examples_dir.display(),
    );

    // Verify projects on every core. Deterministic tactic work budgets decide
    // correctness, so concurrency cannot change a verdict; the test runner
    // owns hang containment.
    let _ = instrumentation::take_artifact_reuse_rejection_census();
    let workers = std::thread::available_parallelism().map_or(1, usize::from);
    let failures = limits::run_parallel(&projects, workers, |project| {
        // One line as each project starts and one as it finishes, on stderr
        // so the gate can stream them: a stall shows as a started project
        // that never finishes, and a slow project is visible while it runs.
        eprintln!("example project `{}` started", project.display());
        let started = std::time::Instant::now();
        run_example_in_thread(project)?;
        eprintln!(
            "example project `{}` verified in {:.2}s",
            project.display(),
            started.elapsed().as_secs_f64()
        );
        Ok(())
    });
    if !failures.is_empty() {
        let mut message = format!(
            "{} of {} example projects failed:\n",
            failures.len(),
            projects.len()
        );
        for (index, diagnostics) in failures {
            message.push_str(&format!(
                "\nexample project `{}` {diagnostics}\n",
                projects[index].display()
            ));
        }
        panic!("{message}");
    }
    let census = instrumentation::take_artifact_reuse_rejection_census();
    if requested.is_none()
        && !run_quarantined
        && !skipped_cpp
        && let Some(mismatch) = instrumentation::artifact_reuse_rejection_census_mismatch(
            &census,
            ARTIFACT_REUSE_REJECTION_BASELINE,
        )
    {
        panic!("artifact reuse rejection ratchet (tests/examples.rs baselines):\n{mismatch}");
    }
}

/// The insert example verifies in the ordinary example gate; this pins what
/// that verdict is about: the unchanged Linux C and the shared model.
#[test]
fn rbtree_insert_uses_the_unchanged_c_and_the_shared_model() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (relative, expected) in [
        (
            "examples/rbtree-insert/rbtree.h",
            "69fc7419118e4a37fb46a2469b981646a733b1a7c247094d0b48aa643575cee3",
        ),
        (
            "examples/rbtree-insert/rb_insert_color.c",
            "b20d68f309682bdcebcf2176d655b92b582f2c88bcc0f4645a7384c0760df111",
        ),
    ] {
        let bytes = fs::read(root.join(relative)).expect("the unchanged insert C input exists");
        assert_eq!(hex_digest(sha256(&bytes)), expected, "changed {relative}");
    }
    let source = fs::read_to_string(root.join("examples/rbtree-insert/rbtree_insert.click"))
        .expect("the insert sidecar should exist");
    assert!(source.contains("import \"../rbtree-model/rbtree_model.click\";"));
    assert!(!source.contains("spec enum RbTree"));
    assert!(source.contains("void __rb_insert("));
}

/// A wholly selected claim's failure must be an audit failure, without a
/// per-site retry that can hide a broken combined expansion.
#[test]
#[ignore = "nightly: audit process regression stays outside the verification gate"]
fn audit_whole_claim_failure_is_fatal() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (keep_going, max_sites) in [
        (false, None),
        (true, None),
        (false, Some("1")),
        (true, Some("100")),
    ] {
        let mut command = Command::new(env!("CARGO_BIN_EXE_click"));
        command.args([
            "audit",
            "--claim",
            "scalar.arithmetic_result",
            "--expansion-work-limit",
            "1",
        ]);
        if keep_going {
            command.arg("--keep-going");
        }
        if let Some(limit) = max_sites {
            command.args(["--max-sites", limit]);
        }
        let output = command
            .arg(root.join("mdtests/scalar.md"))
            .output()
            .unwrap();
        assert!(!output.status.success());
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(stdout.contains("1 claim failures"), "{stdout}");
        assert!(!stdout.contains("auditing each alone"), "{stdout}");
        assert!(!stdout.contains("NOTE "), "{stdout}");
        assert!(stdout.contains("--start-at"), "{stdout}");
    }
}

/// Batching respects both the total site cap and already consumed sites.
#[test]
#[ignore = "nightly: audit selection regression stays outside the verification gate"]
fn bounded_audit_batches_only_claims_that_fit_the_remaining_cap() {
    let directory =
        std::env::temp_dir().join(format!("click-audit-cap-selection-{}", std::process::id()));
    fs::create_dir_all(&directory).unwrap();
    let path = directory.join("two.md");
    fs::write(
        &path,
        "# Bounded audit selection\n\n```c filename=two.c\n\
         int32 first(int32 x) { return x; }\n\
         int32 second(int32 x) { return x; }\n```\n\n```click\n\
         verifying \"two.c\";\n\
         int32 first(int32 x) { ensures result == x; } by { execute(); simp(); }\n\
         int32 second(int32 x) { ensures result == x; } by { execute(); simp(); }\n\
         ```\n\n```expect\npass\n```\n",
    )
    .unwrap();
    for (cap, passed, batched_claims) in [(1, 1, 0), (2, 2, 1), (3, 3, 1), (4, 4, 2), (5, 4, 2)] {
        let output = Command::new(env!("CARGO_BIN_EXE_click"))
            .args(["audit", "--verbose", "--max-sites", &cap.to_string()])
            .arg(&path)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{}",
            String::from_utf8_lossy(&output.stderr)
        );
        let stdout = String::from_utf8(output.stdout).unwrap();
        assert!(
            stdout.contains(&format!(
                "SUMMARY: {passed} sites passed; 0 site failures; 0 claim failures"
            )),
            "{stdout}"
        );
        assert_eq!(
            stdout.matches("2 sites together:").count(),
            batched_claims,
            "{stdout}"
        );
        assert_eq!(stdout.contains("RESUME:"), cap < 4, "{stdout}");
    }
    let source = fs::read_to_string(&path).unwrap();
    let (line, text) = source
        .lines()
        .enumerate()
        .find(|(_, line)| line.starts_with("int32 first") && line.contains("ensures"))
        .unwrap();
    let location = format!(
        "{}:{}:{}",
        path.display(),
        line + 1,
        text.find("simp()").unwrap() + 1
    );
    let output = Command::new(env!("CARGO_BIN_EXE_click"))
        .args([
            "audit",
            "--verbose",
            "--max-sites",
            "3",
            "--start-at",
            &location,
        ])
        .arg(&path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    let stdout = String::from_utf8(output.stdout).unwrap();
    assert!(
        stdout.contains("SUMMARY: 3 sites passed; 0 site failures; 0 claim failures"),
        "{stdout}"
    );
    assert_eq!(stdout.matches("2 sites together:").count(), 1, "{stdout}");
    assert!(!stdout.contains("RESUME:"), "{stdout}");
    fs::remove_dir_all(directory).unwrap();
}

/// Nested execution matches must retain their own branch's shared tactics.
#[test]
#[ignore = "nightly: whole rbtree insert expansion and cold verification exceed the gate budget"]
fn rbtree_insert_whole_claim_expansion_verifies() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("examples/rbtree-insert/rbtree_insert.click");
    let source = fs::read_to_string(&path).unwrap();
    let c_sources = read_verifying_sources(&path, &source).unwrap();
    let project = read_click_project_at_root(&path, &source, &root.join("examples")).unwrap();
    limits::spawn(
        "rbtree insert whole-claim expansion",
        "click-rbtree-expansion".to_string(),
        move || {
            let expanded = click::surface::expand_project_claim_source_by_label(
                &project,
                &ProgramInputs::Bundle(source_refs(&c_sources)),
                "__rb_insert.contract",
            )?;
            assert_ne!(expanded, source);
            let rewritten = project.with_entry_source(expanded);
            click::surface::verify_c0_project(&rewritten, &source_refs(&c_sources))
        },
    )
    .unwrap()
    .expect("the expanded insert claim must cold verify");
}

/// The insert proof against a copy of the C whose root case skips its
/// recolour, `rb_set_parent_color(node, NULL, RB_BLACK)`. The proof claims the
/// root's colour bit is black at that `break`, which the C no longer makes
/// true, and that claim is refused; the files on disk are not changed.
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn rbtree_insert_refuses_a_skipped_recolour() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("examples/rbtree-insert/rbtree_insert.click");
    let source = fs::read_to_string(&path).expect("the insert sidecar should exist");
    let mut c_sources =
        read_verifying_sources(&path, &source).expect("the insert C bundle should load");
    let recolour = "\t\t\trb_set_parent_color(node, NULL, RB_BLACK);\n";
    let (_, c) = c_sources
        .iter_mut()
        .find(|(name, _)| name.ends_with("rb_insert_color.c"))
        .expect("the bundle holds rb_insert_color.c");
    assert_eq!(c.matches(recolour).count(), 1, "the root recolour moved");
    *c = c.replace(recolour, "");
    let project = read_click_project_at_root(&path, &source, &root.join("examples"))
        .expect("the insert sidecar should resolve the shared model");
    // Like every other verification here, this runs on a harness verifier
    // thread: the proof is deep enough to overflow the default test stack.
    let error = limits::spawn(
        "skipped-recolour verifier",
        "click-skipped-recolour".to_string(),
        move || click::surface::verify_c0_project(&project, &source_refs(&c_sources)),
    )
    .unwrap_or_else(|error| panic!("{error}"))
    .expect_err("the insert proof must refuse C that skips the root recolour");
    let message = error.message();
    assert!(
        message.contains("could not establish `(node->__rb_parent_color & 1) == 1`"),
        "unexpected refusal: {message}"
    );
}

#[test]
fn rbtree_erase_uses_the_unchanged_pinned_unlink() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let bytes = fs::read(root.join("examples/rbtree-erase/rb_erase_augmented.c"))
        .expect("the pinned erase C input exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "f861b937f0cb142104061ccccb9f6247c99ca4f6d0f4d6033b8720a86f967022"
    );
}

fn erase_refuses_mutation(before: &str, after: &str) {
    erase_sidecar_refuses_mutation("rbtree_erase.click", before, after);
}

fn erase_sidecar_refuses_mutation(sidecar: &str, before: &str, after: &str) {
    erase_source_refuses_mutation(sidecar, "rb_erase_augmented.c", before, after);
}

fn erase_source_refuses_mutation(sidecar: &str, file: &str, before: &str, after: &str) {
    erase_source_refuses_replacement(sidecar, file, before, after, 1);
}

fn erase_source_replacement_error(
    sidecar: &str,
    file: &str,
    before: &str,
    after: &str,
    occurrences: usize,
) -> String {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("examples/rbtree-erase").join(sidecar);
    let source = fs::read_to_string(&path).expect("the erase sidecar exists");
    let mut c_sources = read_verifying_sources(&path, &source).expect("the erase C bundle loads");
    let (_, c) = c_sources
        .iter_mut()
        .find(|(name, _)| name.ends_with(file))
        .expect("the bundle contains the selected erase input");
    assert_eq!(
        c.matches(before).count(),
        occurrences,
        "mutation must identify the expected statements"
    );
    *c = c.replace(before, after);
    let project = read_click_project_at_root(&path, &source, &root.join("examples"))
        .expect("the erase proof resolves its shared resources and model");
    limits::spawn(
        "erase mutation verifier",
        "click-erase-mutation".to_string(),
        move || click::surface::verify_c0_project(&project, &source_refs(&c_sources)),
    )
    .unwrap_or_else(|error| panic!("{error}"))
    .expect_err("the erase proof must refuse a missing link or parent/color write")
    .message()
    .to_string()
}

fn erase_source_refuses_replacement(
    sidecar: &str,
    file: &str,
    before: &str,
    after: &str,
    occurrences: usize,
) {
    let error = erase_source_replacement_error(sidecar, file, before, after, occurrences);
    assert!(
        error.contains("fold")
            || error
                .contains("is not proven to have the arguments the parent body gives it")
            || error
                .contains("is not proven equal to the value the proposed parent fields give it")
            || error.contains("contract certification")
            || (error.contains("missing resource fact")
                && error.contains("C operation: parent = rb_parent"))
            || error
                .contains("(close_erase_spine_link precondition)")
            || (error.contains("have body tactic")
                && (error.contains("could not establish")
                    || error.contains(
                        "`normalize using` goal did not normalize to true using the listed conditions",
                    )
                    || error.contains(
                        "`assumption` requires the current goal as an available semantic fact",
                    )))
            || error
                .contains("unclosed goal: new->__rb_parent_color == old(old->__rb_parent_color)",)
            || error.contains("unclosed goal: result == 0")
            || error
                .contains("unclosed goal: result == old(node->rb_right)"),
        "unexpected refusal: {}",
        error
    );
}

#[test]
fn rbtree_erase_refuses_a_skipped_right_child_parent_color() {
    erase_refuses_mutation("\t\t\tchild->__rb_parent_color = pc;\n", "");
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rbtree_erase_refuses_a_skipped_left_child_parent_color() {
    erase_refuses_mutation(
        "\t\ttmp->__rb_parent_color = pc = node->__rb_parent_color;\n",
        "\t\tpc = node->__rb_parent_color;\n",
    );
}

#[test]
fn rbtree_erase_refuses_a_skipped_root_replacement() {
    erase_refuses_mutation("\t\t__rb_change_child(node, child, parent, root);\n", "");
}

#[test]
#[ignore = "nightly: 13.42 s to expand and recheck the successor claim (2026-10-08)"]
fn rbtree_erase_successor_explicit_closers_preserve_ownership() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("examples/rbtree-erase/rbtree_erase_successor.click");
    let source = fs::read_to_string(&path).unwrap();
    let c_sources = read_verifying_sources(&path, &source).unwrap();
    let project = read_click_project_at_root(&path, &source, &root.join("examples")).unwrap();
    let (line, text) = source
        .lines()
        .enumerate()
        .filter(|(_, line)| line.trim() == "simp();")
        .last()
        .unwrap();
    let column = text.find("simp").unwrap() + 1;
    limits::spawn(
        "successor closer expansion",
        "click-successor-expansion".into(),
        move || {
            let expanded = click::surface::expand_project_tactic_source_at(
                &project,
                &ProgramInputs::Bundle(source_refs(&c_sources)),
                line + 1,
                column,
            )?;
            let expanded_project =
                read_click_project_at_root(&path, &expanded, &root.join("examples"))
                    .expect("the expanded successor sidecar resolves its imports");
            click::surface::verify_c0_project(&expanded_project, &source_refs(&c_sources))
        },
    )
    .unwrap()
    .unwrap();
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rbtree_erase_successor_refuses_a_skipped_left_parent_write() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_successor.click",
        "\t\trb_set_parent(tmp, successor);\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 3s in the parallel gate"]
fn rbtree_erase_successor_refuses_a_skipped_parent_color_write() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_successor.click",
        "\t\tsuccessor->__rb_parent_color = pc;\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 6s in the parallel gate"]
fn rbtree_erase_black_successor_requires_the_fixup_parent() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_black_successor.click",
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = NULL;\n",
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rbtree_erase_child_successor_requires_blackening() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_child_successor.click",
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n",
        "\t\t\trb_set_parent_color(child2, parent, RB_RED);\n",
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rbtree_erase_child_successor_requires_parent_color_write() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_child_successor.click",
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn rbtree_erase_black_leaf_requires_left_parent_link_update() {
    erase_source_refuses_mutation(
        "rbtree_erase_black_leaf.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_left, new);",
        "            WRITE_ONCE(parent->rb_left, old);",
    );
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn rbtree_erase_black_leaf_requires_right_parent_link_update() {
    erase_source_refuses_mutation(
        "rbtree_erase_black_leaf.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_right, new);",
        "            WRITE_ONCE(parent->rb_right, old);",
    );
}

#[test]
#[ignore = "nightly: 7s in the parallel gate"]
fn rbtree_erase_black_leaf_requires_the_fixup_parent() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_black_leaf.click",
        "\t\t\trebalance = __rb_is_black(pc) ? parent : NULL;\n",
        "\t\t\trebalance = NULL;\n",
    );
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn rbtree_erase_red_leaf_requires_left_parent_link_update() {
    erase_source_refuses_mutation(
        "rbtree_erase_red_leaf.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_left, new);",
        "            WRITE_ONCE(parent->rb_left, old);",
    );
}

#[test]
#[ignore = "nightly: 9s in the parallel gate"]
fn rbtree_erase_red_leaf_requires_right_parent_link_update() {
    erase_source_refuses_mutation(
        "rbtree_erase_red_leaf.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_right, new);",
        "            WRITE_ONCE(parent->rb_right, old);",
    );
}

#[test]
#[ignore = "nightly: 8s in the parallel gate"]
fn rbtree_erase_red_leaf_requires_no_fixup() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_red_leaf.click",
        "\t\t\trebalance = __rb_is_black(pc) ? parent : NULL;\n",
        "\t\t\trebalance = parent;\n",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_right_child_requires_left_parent_link_update() {
    erase_source_refuses_mutation(
        "rbtree_erase_right_child.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_left, new);",
        "            WRITE_ONCE(parent->rb_left, old);",
    );
}

#[test]
#[ignore = "nightly: 13s in the parallel gate"]
fn rbtree_erase_right_child_requires_right_parent_link_update() {
    erase_source_refuses_mutation(
        "rbtree_erase_right_child.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_right, new);",
        "            WRITE_ONCE(parent->rb_right, old);",
    );
}

#[test]
#[ignore = "nightly: 12s in the parallel gate"]
fn rbtree_erase_right_child_requires_parent_color_write() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_right_child.click",
        "\t\t\tchild->__rb_parent_color = pc;\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_right_child_requires_blackening() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_right_child.click",
        "\t\t\tchild->__rb_parent_color = pc;\n",
        "\t\t\tchild->__rb_parent_color = pc & ~1;\n",
    );
}

#[test]
#[ignore = "nightly: 12s in the parallel gate"]
fn rbtree_erase_left_child_requires_left_parent_link_update() {
    erase_source_refuses_mutation(
        "rbtree_erase_left_child.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_left, new);",
        "            WRITE_ONCE(parent->rb_left, old);",
    );
}

#[test]
#[ignore = "nightly: 12s in the parallel gate"]
fn rbtree_erase_left_child_requires_right_parent_link_update() {
    erase_source_refuses_mutation(
        "rbtree_erase_left_child.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_right, new);",
        "            WRITE_ONCE(parent->rb_right, old);",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_left_child_requires_parent_color_write() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_left_child.click",
        "\t\ttmp->__rb_parent_color = pc = node->__rb_parent_color;\n",
        "\t\tpc = node->__rb_parent_color;\n",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_left_child_requires_blackening() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_left_child.click",
        "\t\ttmp->__rb_parent_color = pc = node->__rb_parent_color;\n",
        "\t\tpc = node->__rb_parent_color;\n\t\ttmp->__rb_parent_color = pc & ~1;\n",
    );
}

#[test]
#[ignore = "nightly: 12s in the parallel gate"]
fn rbtree_erase_right_child_requires_no_fixup() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_right_child.click",
        "\t\t\tchild->__rb_parent_color = pc;\n\t\t\trebalance = NULL;",
        "\t\t\tchild->__rb_parent_color = pc;\n\t\t\trebalance = parent;",
    );
}

#[test]
#[ignore = "nightly: 12s in the parallel gate"]
fn rbtree_erase_left_child_requires_no_fixup() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_left_child.click",
        "\t\t__rb_change_child(node, tmp, parent, root);\n\t\trebalance = NULL;",
        "\t\t__rb_change_child(node, tmp, parent, root);\n\t\trebalance = parent;",
    );
}

#[test]
#[ignore = "nightly: 13s in the parallel gate"]
fn rbtree_erase_nonroot_successor_requires_left_parent_link() {
    erase_source_refuses_mutation(
        "rbtree_erase_nonroot_successor.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_left, new);",
        "            WRITE_ONCE(parent->rb_left, old);",
    );
}

#[test]
#[ignore = "nightly: 14s in the parallel gate"]
fn rbtree_erase_nonroot_successor_requires_right_parent_link() {
    erase_source_refuses_mutation(
        "rbtree_erase_nonroot_successor.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_right, new);",
        "            WRITE_ONCE(parent->rb_right, old);",
    );
}

#[test]
#[ignore = "nightly: 13s in the parallel gate"]
fn rbtree_erase_nonroot_successor_requires_left_subtree_link() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_successor.click",
        "\t\tWRITE_ONCE(successor->rb_left, tmp);\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 13s in the parallel gate"]
fn rbtree_erase_nonroot_successor_requires_left_subtree_parent() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_successor.click",
        "\t\trb_set_parent(tmp, successor);\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 13s in the parallel gate"]
fn rbtree_erase_nonroot_successor_requires_successor_parent_color() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_successor.click",
        "\t\tsuccessor->__rb_parent_color = pc;\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 14s in the parallel gate"]
fn rbtree_erase_nonroot_successor_requires_no_fixup() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_successor.click",
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = parent;\n",
    );
}

#[test]
#[ignore = "nightly: 22s in the parallel gate"]
fn rbtree_erase_nonroot_child_successor_requires_left_parent_link() {
    erase_source_refuses_mutation(
        "rbtree_erase_nonroot_child_successor.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_left, new);",
        "            WRITE_ONCE(parent->rb_left, old);",
    );
}

#[test]
#[ignore = "nightly: 26s in the parallel gate"]
fn rbtree_erase_nonroot_child_successor_requires_right_parent_link() {
    erase_source_refuses_mutation(
        "rbtree_erase_nonroot_child_successor.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_right, new);",
        "            WRITE_ONCE(parent->rb_right, old);",
    );
}

#[test]
#[ignore = "nightly: 22s in the parallel gate"]
fn rbtree_erase_nonroot_child_successor_requires_left_subtree_link() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_child_successor.click",
        "\t\tWRITE_ONCE(successor->rb_left, tmp);\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 22s in the parallel gate"]
fn rbtree_erase_nonroot_child_successor_requires_left_subtree_parent() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_child_successor.click",
        "\t\trb_set_parent(tmp, successor);\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 23s in the parallel gate"]
fn rbtree_erase_nonroot_child_successor_requires_successor_parent_color() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_child_successor.click",
        "\t\tsuccessor->__rb_parent_color = pc;\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 23s in the parallel gate"]
fn rbtree_erase_nonroot_child_successor_requires_no_fixup() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_child_successor.click",
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n\t\t\trebalance = NULL;",
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n\t\t\trebalance = parent;",
    );
}

#[test]
#[ignore = "nightly: 22s in the parallel gate"]
fn rbtree_erase_nonroot_child_successor_requires_child_parent_color_write() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_child_successor.click",
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 23s in the parallel gate"]
fn rbtree_erase_nonroot_child_successor_requires_child_blackening() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_child_successor.click",
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n",
        "\t\t\trb_set_parent_color(child2, parent, RB_RED);\n",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_nonroot_black_successor_requires_left_parent_link() {
    erase_source_refuses_mutation(
        "rbtree_erase_nonroot_black_successor.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_left, new);",
        "            WRITE_ONCE(parent->rb_left, old);",
    );
}

#[test]
#[ignore = "nightly: 13s in the parallel gate"]
fn rbtree_erase_nonroot_black_successor_requires_right_parent_link() {
    erase_source_refuses_mutation(
        "rbtree_erase_nonroot_black_successor.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_right, new);",
        "            WRITE_ONCE(parent->rb_right, old);",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_nonroot_black_successor_requires_left_subtree_link() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_black_successor.click",
        "\t\tWRITE_ONCE(successor->rb_left, tmp);\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_nonroot_black_successor_requires_left_subtree_parent() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_black_successor.click",
        "\t\trb_set_parent(tmp, successor);\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_nonroot_black_successor_requires_successor_parent_color() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_black_successor.click",
        "\t\tsuccessor->__rb_parent_color = pc;\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_nonroot_black_successor_requires_fixup_parent() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_black_successor.click",
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = NULL;\n",
    );
}

#[test]
#[ignore = "nightly: 12s in the parallel gate"]
fn rbtree_erase_nonroot_black_successor_requires_successor_as_fixup_parent() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_nonroot_black_successor.click",
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = rb_is_black(successor) ? tmp : NULL;\n",
    );
}

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn rbtree_erase_black_successor_requires_root_replacement() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_black_successor.click",
        "\t\t__rb_change_child(node, successor, tmp, root);\n",
        "",
    );
}

#[test]
#[ignore = "nightly: 10s in the parallel gate"]
fn rbtree_erase_deep_successor_refuses_a_skipped_splice() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_spine.click",
        "\t\t\tWRITE_ONCE(parent->rb_left, child2);\n",
        "\t\t\tWRITE_ONCE(parent->rb_left, successor);\n",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_deep_successor_refuses_the_wrong_replacement_parent() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_spine.click",
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n",
        "\t\t\trb_set_parent_color(child2, successor, RB_BLACK);\n",
    );
}

#[test]
#[ignore = "nightly: deeper successor attachment mutation takes 10.1s"]
fn rbtree_erase_deep_successor_refuses_a_skipped_right_attachment() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_spine.click",
        "\t\t\tWRITE_ONCE(successor->rb_right, child);\n",
        "\t\t\tWRITE_ONCE(successor->rb_right, successor->rb_right);\n",
    );
}

#[test]
#[ignore = "nightly: deeper successor parent-update mutation takes 10.2s"]
fn rbtree_erase_deep_successor_refuses_a_skipped_right_parent_update() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_spine.click",
        "\t\t\trb_set_parent(child, successor);\n",
        "\t\t\trb_set_parent(child, node);\n",
    );
}

#[test]
#[ignore = "nightly: 12s in the parallel gate"]
fn rbtree_erase_deep_successor_refuses_a_red_replacement() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_spine.click",
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n",
        "\t\t\trb_set_parent_color(child2, parent, RB_RED);\n",
    );
}

#[test]
#[ignore = "nightly: deeper red-leaf fixup mutation takes 11s"]
fn rbtree_erase_deep_red_leaf_refuses_spurious_fixup() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_spine.click",
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = parent;\n",
    );
}

#[test]
#[ignore = "nightly: 10s in the parallel gate"]
fn rbtree_erase_deep_black_leaf_refuses_a_skipped_splice() {
    // Keep the C statement positions stable while leaving the successor linked.
    erase_sidecar_refuses_mutation(
        "rbtree_erase_black_spine.click",
        "\t\t\tWRITE_ONCE(parent->rb_left, child2);\n",
        "\t\t\tWRITE_ONCE(parent->rb_left, successor);\n",
    );
}

#[test]
#[ignore = "nightly: 11s in the parallel gate"]
fn rbtree_erase_deep_black_leaf_requires_fixup() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_black_spine.click",
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = NULL;\n",
    );
}

#[test]
#[ignore = "nightly: deeper black-leaf fixup-parent mutation takes 10.2s"]
fn rbtree_erase_deep_black_leaf_requires_the_splice_parent() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_black_spine.click",
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = successor;\n",
    );
}

#[test]
#[ignore = "nightly: 10s in the parallel gate"]
fn rbtree_erase_deep_black_leaf_requires_right_parent_update() {
    erase_sidecar_refuses_mutation(
        "rbtree_erase_black_spine.click",
        "\t\t\trb_set_parent(child, successor);\n",
        "",
    );
}

#[test]
fn rbtree_change_child_requires_left_link() {
    erase_source_refuses_mutation(
        "rbtree_change_child.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_left, new);",
        "            WRITE_ONCE(parent->rb_left, old);",
    );
}

#[test]
fn rbtree_change_child_requires_right_link() {
    erase_source_refuses_mutation(
        "rbtree_change_child.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_right, new);",
        "            WRITE_ONCE(parent->rb_right, old);",
    );
}

#[test]
fn rbtree_change_child_requires_root_link() {
    erase_source_refuses_mutation(
        "rbtree_change_child.click",
        "rbtree.h",
        "        WRITE_ONCE(root->rb_node, new);",
        "        WRITE_ONCE(root->rb_node, old);",
    );
}

#[test]
fn concurrency_fork_join_source_is_frozen() {
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/concurrency-fork-join/fork_join.c");
    let bytes = fs::read(&source).expect("the frozen fork/join C source exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "818486bb827c4ae7c7ad5638fd75bb0bb12fd7fb9796babaa2111f594609e9a6",
        "the concurrency proof must use the selected C source unchanged"
    );
}

#[test]
fn shared_refcount_source_is_frozen() {
    let source = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/shared-refcount/shared_refcount.c");
    let bytes = fs::read(&source).expect("the frozen shared refcount C source exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "ac5e6d927ada9341e3efb7ea77446785c364a8578e49d0a09f146b5037c5e025",
        "the shared refcount proof must use the selected C source unchanged"
    );
}

#[test]
fn concurrency_mutex_counter_source_is_frozen() {
    let source =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("design/concurrency-probes/mutex_counter.c");
    let bytes = fs::read(&source).expect("the frozen mutex counter C source exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "8bc4121624978882c13c2736ccc93097f2c7065e4e8d2cb9bfa9066a6170fa2c",
        "the mutex counter proof must use the selected C source unchanged"
    );
}

#[test]
fn byte_representation_source_is_frozen() {
    let source =
        PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/byte-representation/rep_copy.c");
    let bytes = fs::read(&source).expect("the frozen byte-representation C source exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "4d5a08408323753ddae195ae33c4a776a4499a7aa9e8d0abf68c491245fe6847",
        "the byte-representation proof must use the selected C source unchanged"
    );
}

/// Whether any sidecar of `project` imports C++, which needs the exporter.
fn imports_cpp(project: &Path) -> bool {
    fs::read_dir(project)
        .into_iter()
        .flatten()
        .flatten()
        .any(|entry| {
            let path = entry.path();
            path.file_name()
                .and_then(|name| name.to_str())
                .is_some_and(|name| name.ends_with(".click.import.json"))
                && fs::read(&path)
                    .ok()
                    .and_then(|bytes| serde_json::from_slice::<serde_json::Value>(&bytes).ok())
                    .is_some_and(|config| config["language"] == "c++")
        })
}

fn run_example_in_thread(project: &Path) -> Result<(), String> {
    let project = project.to_path_buf();
    limits::spawn("example verifier", "click-example".to_string(), move || {
        run_example_project(&project)
    })?
}

fn run_example_project(project: &Path) -> Result<(), String> {
    let prepare = project.join("prepare.py");
    if prepare.is_file() {
        let output = Command::new("python3")
            .arg(&prepare)
            .output()
            .map_err(|error| format!("failed to prepare `{}`: {error}", project.display()))?;
        if !output.status.success() {
            return Err(format!(
                "failed to prepare `{}`: {}{}",
                project.display(),
                String::from_utf8_lossy(&output.stdout),
                String::from_utf8_lossy(&output.stderr)
            ));
        }
    }
    let source_status = verify_source_integrity(project)?;
    if let Some(status) = source_status {
        eprintln!(
            "source fixture `{}` integrity manifest passed; status: {}",
            project.display(),
            status.as_str()
        );
    }

    let mut click_paths = project_sidecars(project)?;

    if click_paths.is_empty() {
        return Err(format!(
            "example project `{}` must contain at least one .click sidecar",
            project.display()
        ));
    }

    click_paths.sort();

    for click_path in click_paths {
        let click_source = fs::read_to_string(&click_path)
            .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
        let name = click_path
            .file_name()
            .and_then(|name| name.to_str())
            .ok_or_else(|| format!("invalid example sidecar `{}`", click_path.display()))?;
        let config = click_path.with_file_name(format!("{name}.import.json"));
        // Native Rust artifacts are checked offline here. The required
        // charon-live gate freshly extracts every canonical Rust source and
        // checks its contract; ordinary archive consumers need no Charon toolchain.
        let native_rust = if config.exists() {
            let metadata: serde_json::Value =
                serde_json::from_slice(&fs::read(&config).map_err(|error| error.to_string())?)
                    .map_err(|error| error.to_string())?;
            metadata["language"] == "rust"
        } else {
            false
        };
        if config.exists() && !native_rust {
            refresh_compiler_import(&config).map_err(|error| {
                format!(
                    "sidecar `{}` import refresh failed: {error}",
                    click_path.display()
                )
            })?;
        }
        let click_project = read_click_project_at_root(
            &click_path,
            &click_source,
            project.parent().unwrap_or(project),
        )?;
        let inputs = read_c_inputs_for_project(&click_path, &click_source, &click_project)?;
        match source_status {
            Some(SourceFixtureStatus::ParserOnly) => {
                let CInput::Bundle(c_sources) = inputs else {
                    return Err(format!(
                        "parser-only example `{}` cannot use a compiler import",
                        click_path.display()
                    ));
                };
                match if click_project.modules().len() == 1 && click_project.c_profile().is_none() {
                    verify_c0_sources(&click_source, &source_refs(&c_sources))
                } else {
                    verify_c0_project(&click_project, &source_refs(&c_sources))
                } {
                    Err(error)
                        if error.message().starts_with("failed to parse C source")
                            || error.message().starts_with("failed to parse C header")
                            || error.message().starts_with("failed to resolve includes") =>
                    {
                        eprintln!(
                            "parser status for `{}`: parser-only as expected: {}",
                            click_path.display(),
                            error.message()
                        );
                    }
                    Err(error) => {
                        return Err(format!(
                            "sidecar `{}` reached verification despite parser-only status: {}",
                            click_path.display(),
                            error.message()
                        ));
                    }
                    Ok(_) => {
                        return Err(format!(
                            "parser-only source fixture `{}` unexpectedly verified",
                            click_path.display()
                        ));
                    }
                }
            }
            Some(SourceFixtureStatus::Verified) | None => {
                let verify = || {
                    match &inputs {
                        CInput::Bundle(c_sources)
                            if click_project.modules().len() == 1
                                && click_project.c_profile().is_none() =>
                        {
                            verify_c0_sources(&click_source, &source_refs(c_sources))
                        }
                        CInput::Bundle(c_sources) => {
                            verify_c0_project(&click_project, &source_refs(c_sources))
                        }
                        CInput::Prepared(imports) => {
                            verify_c0_prepared_project(&click_project, imports)
                        }
                        CInput::PreparedProgram(import) => {
                            verify_program_prepared_project(&click_project, import)
                        }
                    }
                    .map(|_| ())
                    .map_err(|error| error.message().to_string())
                };
                let fixture = fixture_name(&click_path);
                let (result, samples) = tactic_work::measure(verify);
                if !samples.is_empty() {
                    let single_module =
                        click_project.modules().len() == 1 && click_project.c_profile().is_none();
                    tactic_work::write(
                        "examples",
                        &fixture,
                        Path::new(&fixture),
                        &samples,
                        |claim, source_index| {
                            match &inputs {
                                CInput::Bundle(c_sources) if single_module => {
                                    c0_tactic_source_position(
                                        &click_source,
                                        &source_refs(c_sources),
                                        claim,
                                        source_index,
                                    )
                                }
                                CInput::Bundle(c_sources) => project_tactic_source_position(
                                    &click_project,
                                    &ProgramInputs::Bundle(source_refs(c_sources)),
                                    claim,
                                    source_index,
                                ),
                                CInput::Prepared(imports) => project_tactic_source_position(
                                    &click_project,
                                    &ProgramInputs::Prepared(imports),
                                    claim,
                                    source_index,
                                ),
                                CInput::PreparedProgram(import) => project_tactic_source_position(
                                    &click_project,
                                    &ProgramInputs::program(import),
                                    claim,
                                    source_index,
                                ),
                            }
                            .ok()
                            .map(|position| (position.line, position.column))
                        },
                    );
                }
                result.map_err(|message| format!("sidecar `{fixture}` failed: {message}"))?;
                eprintln!("verified {}", click_path.display());
            }
        }
    }
    Ok(())
}

/// Names a sidecar by its repository-relative path.
fn fixture_name(click_path: &Path) -> String {
    click_path
        .strip_prefix(env!("CARGO_MANIFEST_DIR"))
        .unwrap_or(click_path)
        .components()
        .map(|component| component.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum SourceFixtureStatus {
    ParserOnly,
    Verified,
}

impl SourceFixtureStatus {
    fn as_str(self) -> &'static str {
        match self {
            Self::ParserOnly => "parser-only",
            Self::Verified => "verified",
        }
    }
}

fn verify_source_integrity(project: &Path) -> Result<Option<SourceFixtureStatus>, String> {
    let manifest_path = project.join(SOURCE_MANIFEST);
    if !manifest_path.is_file() {
        return Ok(None);
    }

    let metadata_path = project.join(SOURCE_METADATA);
    let metadata = fs::read_to_string(&metadata_path).map_err(|error| {
        format!(
            "source integrity manifest requires `{}`: {error}",
            metadata_path.display()
        )
    })?;
    let status = metadata
        .lines()
        .find_map(|line| line.trim().strip_prefix("status:"))
        .map(str::trim)
        .ok_or_else(|| {
            format!(
                "`{}` must declare `status: verified` or `status: parser-only`",
                metadata_path.display()
            )
        })
        .and_then(|status| match status {
            "verified" => Ok(SourceFixtureStatus::Verified),
            "parser-only" => Ok(SourceFixtureStatus::ParserOnly),
            _ => Err(format!(
                "`{}` has unsupported source status `{status}`",
                metadata_path.display()
            )),
        })?;

    let manifest = fs::read_to_string(&manifest_path)
        .map_err(|error| format!("failed to read `{}`: {error}", manifest_path.display()))?;
    let mut expected = BTreeMap::new();
    for (line_number, line) in manifest.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let mut fields = line.split_whitespace();
        let digest = fields.next().ok_or_else(|| {
            format!(
                "`{}` line {} has no digest",
                manifest_path.display(),
                line_number + 1
            )
        })?;
        let name = fields.next().ok_or_else(|| {
            format!(
                "`{}` line {} has no source path",
                manifest_path.display(),
                line_number + 1
            )
        })?;
        if fields.next().is_some() {
            return Err(format!(
                "`{}` line {} must contain exactly a digest and path",
                manifest_path.display(),
                line_number + 1
            ));
        }
        if digest.len() != 64 || !digest.bytes().all(|byte| byte.is_ascii_hexdigit()) {
            return Err(format!(
                "`{}` line {} has an invalid SHA-256 digest",
                manifest_path.display(),
                line_number + 1
            ));
        }
        let path = Path::new(name);
        if path.is_absolute()
            || path.components().any(|component| {
                matches!(
                    component,
                    Component::ParentDir | Component::RootDir | Component::Prefix(_)
                )
            })
            || !(matches!(
                path.extension().and_then(|extension| extension.to_str()),
                Some("c" | "h")
            ) || name == "COPYING")
        {
            return Err(format!(
                "`{}` line {} names an invalid source fixture path `{name}`",
                manifest_path.display(),
                line_number + 1
            ));
        }
        if expected
            .insert(name.to_string(), digest.to_ascii_lowercase())
            .is_some()
        {
            return Err(format!(
                "`{}` lists source `{name}` more than once",
                manifest_path.display()
            ));
        }
    }
    if expected.is_empty() {
        return Err(format!(
            "`{}` contains no source entries",
            manifest_path.display()
        ));
    }

    let actual_sources = files_with_extension(project, "c")?
        .into_iter()
        .map(|path| {
            path.strip_prefix(project)
                .map_err(|error| format!("failed to relativize `{}`: {error}", path.display()))
                .and_then(|path| {
                    path.to_str().map(str::to_owned).ok_or_else(|| {
                        format!("source path `{}` is not valid UTF-8", path.display())
                    })
                })
        })
        .collect::<Result<BTreeSet<_>, _>>()?;
    // All C files remain mandatory. Headers and the upstream license may
    // additionally be pinned without pretending they are translation units.
    let expected_sources = expected
        .keys()
        .filter(|name| {
            Path::new(name)
                .extension()
                .is_some_and(|extension| extension == "c")
        })
        .cloned()
        .collect::<BTreeSet<_>>();
    if actual_sources != expected_sources {
        return Err(format!(
            "`{}` must cover exactly the project C sources; expected {expected_sources:?}, found {actual_sources:?}",
            manifest_path.display()
        ));
    }

    for (name, expected_digest) in expected {
        let path = project.join(&name);
        let source = fs::read(&path)
            .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
        let actual_digest = hex_digest(sha256(&source));
        if actual_digest != expected_digest {
            return Err(format!(
                "source integrity mismatch for `{}`: manifest has `{expected_digest}`, file has `{actual_digest}`",
                path.display()
            ));
        }
    }
    Ok(Some(status))
}

fn sha256(bytes: &[u8]) -> [u8; 32] {
    Sha256::digest(bytes).into()
}

fn hex_digest(digest: [u8; 32]) -> String {
    const HEX: &[u8; 16] = b"0123456789abcdef";
    digest
        .into_iter()
        .flat_map(|byte| {
            [
                HEX[(byte >> 4) as usize] as char,
                HEX[(byte & 0x0f) as usize] as char,
            ]
        })
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_manifest_rejects_modified_file() {
        let unique = std::time::SystemTime::now()
            .duration_since(std::time::UNIX_EPOCH)
            .expect("system clock should be after the Unix epoch")
            .as_nanos();
        let directory = std::env::temp_dir().join(format!(
            "click-source-integrity-{}-{unique}",
            std::process::id()
        ));
        fs::create_dir(&directory).expect("temporary source directory should be creatable");
        fs::write(directory.join(SOURCE_METADATA), "status: verified\n").unwrap();
        let source = b"int32 unchanged(void) { return 0; }\n";
        fs::write(directory.join("fixture.c"), source).unwrap();
        let header = b"#define VERSION 17\n";
        fs::write(directory.join("fixture.h"), header).unwrap();
        fs::write(directory.join("COPYING"), b"license\n").unwrap();
        fs::write(
            directory.join(SOURCE_MANIFEST),
            format!(
                "{}  fixture.c\n{}  fixture.h\n{}  COPYING\n",
                hex_digest(sha256(source)),
                hex_digest(sha256(header)),
                hex_digest(sha256(b"license\n"))
            ),
        )
        .unwrap();

        assert_eq!(
            verify_source_integrity(&directory).unwrap(),
            Some(SourceFixtureStatus::Verified)
        );
        fs::write(directory.join("fixture.h"), b"#define VERSION 18\n").unwrap();
        let error = verify_source_integrity(&directory).unwrap_err();
        assert!(error.contains("source integrity mismatch"), "{error}");
        fs::write(directory.join("fixture.h"), header).unwrap();
        fs::write(
            directory.join("fixture.c"),
            b"int32 changed(void) { return 1; }\n",
        )
        .unwrap();
        let error = verify_source_integrity(&directory).unwrap_err();
        assert!(error.contains("source integrity mismatch"), "{error}");
        fs::remove_dir_all(directory).unwrap();
    }
}

#[test]
fn rbtree_erase_color_uses_the_unchanged_pinned_function() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let bytes = fs::read(root.join("examples/rbtree-erase/rb_erase_color.c"))
        .expect("the pinned erase-color C input exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "1964275955333d0c872f193d30283e6de1fbbd2e3315606734321de0d5bc503e"
    );
}

fn erase_color_refuses_mutation(sidecar: &str, before: &str, after: &str) {
    // The pinned function repeats each update in its two mirrored arms.
    // Replacing both preserves statement positions and covers either orientation.
    erase_source_refuses_replacement(sidecar, "rb_erase_color.c", before, after, 2);
}

#[test]
#[ignore = "nightly: erase-color verification takes about 7s"]
fn rbtree_erase_color_red_left_requires_parent_blackening() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_red_left.click",
        "rb_set_black(parent);",
        "parent->__rb_parent_color = parent->__rb_parent_color;",
    );
}

#[test]
#[ignore = "nightly: erase-color verification takes about 7s"]
fn rbtree_erase_color_red_left_requires_sibling_recoloring() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_red_left.click",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_RED);",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_BLACK);",
    );
}

#[test]
#[ignore = "nightly: erase-color verification takes about 7s"]
fn rbtree_erase_color_red_left_requires_the_sibling_parent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_red_left.click",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_RED);",
        "rb_set_parent_color(sibling, sibling,\n\t\t\t\t\t\t\t    RB_RED);",
    );
}

#[test]
#[ignore = "nightly: erase-color verification takes about 4s"]
fn rbtree_erase_color_root_left_requires_sibling_recoloring() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_root_left.click",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_RED);",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_BLACK);",
    );
}

#[test]
#[ignore = "nightly: erase-color verification takes about 4s"]
fn rbtree_erase_color_root_left_requires_the_sibling_parent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_root_left.click",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_RED);",
        "rb_set_parent_color(sibling, sibling,\n\t\t\t\t\t\t\t    RB_RED);",
    );
}

#[test]
#[ignore = "nightly: erase-color verification takes about 4s"]
fn rbtree_erase_color_root_left_requires_the_null_parent_cursor() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_root_left.click",
        "parent = rb_parent(node);",
        "parent = node;",
    );
}

// These mutations exercise the repeated case-2 proof, including its back edge.
#[test]
#[ignore = "nightly: repeated erase-color propagation verifies a whole sidecar"]
fn rbtree_erase_color_flips_requires_cursor_ascent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_flips.click",
        "parent = rb_parent(node);",
        "parent = node;",
    );
}

#[test]
#[ignore = "nightly: repeated erase-color propagation verifies a whole sidecar"]
fn rbtree_erase_color_flips_requires_focus_ascent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_flips.click",
        "node = parent;",
        "node = node;",
    );
}

#[test]
#[ignore = "nightly: repeated erase-color propagation verifies a whole sidecar"]
fn rbtree_erase_color_flips_requires_parent_blackening() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_flips.click",
        "rb_set_black(parent);",
        "parent->__rb_parent_color = parent->__rb_parent_color;",
    );
}

#[test]
#[ignore = "nightly: repeated erase-color propagation verifies a whole sidecar"]
fn rbtree_erase_color_flips_requires_sibling_recoloring() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_flips.click",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_RED);",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_BLACK);",
    );
}

#[test]
#[ignore = "nightly: propagated erase rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_outer_requires_cursor_ascent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_flips_outer.click",
        "parent = rb_parent(node);",
        "parent = node;",
    );
}

#[test]
#[ignore = "nightly: propagated erase rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_outer_requires_focus_ascent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_flips_outer.click",
        "node = parent;",
        "node = node;",
    );
}

#[test]
#[ignore = "nightly: propagated erase rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_outer_requires_parent_blackening() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_flips_outer.click",
        "rb_set_black(parent);",
        "parent->__rb_parent_color = parent->__rb_parent_color;",
    );
}

#[test]
#[ignore = "nightly: propagated erase rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_outer_requires_sibling_recoloring() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_flips_outer.click",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_RED);",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_BLACK);",
    );
}

#[test]
#[ignore = "nightly: propagated erase rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_outer_left_requires_parent_child_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_outer.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_right, tmp2);",
        "WRITE_ONCE(parent->rb_right, parent);",
        2,
    );
    assert!(
        error.contains("`have` failed for `parent->rb_right == tmp2`"),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated erase rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_outer_right_requires_parent_child_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_outer.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_left, tmp2);",
        "WRITE_ONCE(parent->rb_left, parent);",
        2,
    );
    assert!(
        error.contains("`have` failed for `parent->rb_left == tmp2`"),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated erase rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_outer_requires_far_child_blackening() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_flips_outer.click",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, sibling, RB_RED);",
    );
}

#[test]
#[ignore = "nightly: propagated erase rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_outer_requires_near_parent() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_outer.click",
        "rb_erase_color.c",
        "rb_set_parent(tmp2, parent);",
        "rb_set_parent(tmp2, sibling);",
        2,
    );
    assert!(
        error.contains(
            "`have` failed for `tmp2->__rb_parent_color == (color_bit(nc) | ((uint64)parent))`"
        ),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_rotations_left_requires_sibling_child_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_rotations.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_left, tmp1);",
        "WRITE_ONCE(sibling->rb_left, parent);",
        1,
    );
    assert!(
        error.contains("`have` failed for `sid->rb_left == tmp1"),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_rotations_right_requires_sibling_child_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_rotations.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_right, tmp1);",
        "WRITE_ONCE(sibling->rb_right, parent);",
        1,
    );
    assert!(
        error.contains("`have` failed for `sid->rb_right == tmp1"),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_rotations_left_requires_inner_child_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_rotations.click",
        "rb_erase_color.c",
        "WRITE_ONCE(tmp2->rb_right, sibling);",
        "WRITE_ONCE(tmp2->rb_right, parent);",
        1,
    );
    assert!(
        error.contains("`have` failed for `iid->rb_right == sid"),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_rotations_right_requires_inner_child_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_rotations.click",
        "rb_erase_color.c",
        "WRITE_ONCE(tmp2->rb_left, sibling);",
        "WRITE_ONCE(tmp2->rb_left, parent);",
        1,
    );
    assert!(
        error.contains("`have` failed for `iid->rb_left == sid"),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_rotations_requires_first_grandchild_parent() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_rotations.click",
        "rb_erase_color.c",
        "rb_set_parent_color(tmp1, sibling,\n\t\t\t\t\t\t\t    RB_BLACK);",
        "rb_set_parent_color(tmp1, parent,\n\t\t\t\t\t\t\t    RB_BLACK);",
        2,
    );
    assert!(
        error.contains("`have` failed for `tmp1->__rb_parent_color =="),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_rotations_requires_first_grandchild_blackening() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_rotations.click",
        "rb_erase_color.c",
        "rb_set_parent_color(tmp1, sibling,\n\t\t\t\t\t\t\t    RB_BLACK);",
        "rb_set_parent_color(tmp1, sibling,\n\t\t\t\t\t\t\t    RB_RED);",
        2,
    );
    assert!(
        error.contains("`have` failed for `tmp1->__rb_parent_color =="),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_rotations_requires_old_sibling_as_far_child() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_rotations.click",
        "rb_erase_color.c",
        "tmp1 = sibling;",
        "tmp1 = parent;",
        2,
    );
    assert!(
        error.contains("`have` failed for `tmp1 == sid"),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_rotations_requires_inner_node_as_sibling() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_rotations.click",
        "rb_erase_color.c",
        "sibling = tmp2;",
        "sibling = parent;",
        2,
    );
    assert!(
        error.contains("`have` failed for `sibling == iid"),
        "unexpected refusal: {error}",
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_exit_left_requires_parent_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_exit.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_right, tmp1);",
        "WRITE_ONCE(parent->rb_right, NULL);",
        1,
    );
    assert!(
        error.contains("`have` failed for `parent->rb_right == zid"),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_exit_left_requires_sibling_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_exit.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_left, parent);\n\t\t\t\trb_set_parent_color(tmp1, parent, RB_BLACK);",
        "WRITE_ONCE(sibling->rb_left, NULL);\n\t\t\t\trb_set_parent_color(tmp1, parent, RB_BLACK);",
        1,
    );
    assert!(
        error.contains("`have` failed for `sid->rb_left == parent"),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_exit_right_requires_parent_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_exit.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_left, tmp1);",
        "WRITE_ONCE(parent->rb_left, NULL);",
        1,
    );
    assert!(
        error.contains("`have` failed for `parent->rb_left == zid"),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_exit_right_requires_sibling_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_exit.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_right, parent);\n\t\t\t\trb_set_parent_color(tmp1, parent, RB_BLACK);",
        "WRITE_ONCE(sibling->rb_right, NULL);\n\t\t\t\trb_set_parent_color(tmp1, parent, RB_BLACK);",
        1,
    );
    assert!(
        error.contains("`have` failed for `sid->rb_right == parent"),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_exit_requires_near_parent() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_exit.click",
        "rb_erase_color.c",
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        2,
    );
    assert!(
        error.contains("`have` failed for `tmp1->__rb_parent_color =="),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_exit_requires_near_blackening() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_exit.click",
        "rb_erase_color.c",
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
        "rb_set_parent_color(tmp1, parent, RB_RED);",
        2,
    );
    assert!(
        error.contains("`have` failed for `tmp1->__rb_parent_color =="),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_exit_requires_red_parent() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_exit.click",
        "rb_erase_color.c",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\t\tRB_RED);",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\t\tRB_BLACK);",
        2,
    );
    assert!(error.contains("step"), "unexpected refusal: {error}");
}

#[test]
#[ignore = "nightly: propagated red-sibling repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_exit_requires_near_sibling_cursor() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_exit.click",
        "rb_erase_color.c",
        "sibling = tmp1;",
        "sibling = parent;",
        2,
    );
    assert!(
        error.contains("`have` failed for `sibling == zid"),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: rotation-helper verification checks both helper contracts"]
fn rbtree_rotate_set_parents_requires_the_copied_word() {
    erase_source_refuses_replacement(
        "rbtree_rotate_set_parents.click",
        "rbtree.h",
        "new->__rb_parent_color = old->__rb_parent_color;",
        "new->__rb_parent_color = new->__rb_parent_color;",
        1,
    );
}

#[test]
#[ignore = "nightly: rotation-helper verification checks both helper contracts"]
fn rbtree_rotate_set_parents_requires_the_new_parent() {
    erase_source_refuses_replacement(
        "rbtree_rotate_set_parents.click",
        "rbtree.h",
        "rb_set_parent_color(old, new, color);",
        "rb_set_parent_color(old, old, color);",
        1,
    );
}

#[test]
#[ignore = "nightly: rotation-helper verification checks both helper contracts"]
fn rbtree_rotate_set_parents_requires_root_replacement() {
    erase_source_refuses_replacement(
        "rbtree_rotate_set_parents.click",
        "rbtree.h",
        "WRITE_ONCE(root->rb_node, new);",
        "WRITE_ONCE(root->rb_node, old);",
        1,
    );
}

#[test]
#[ignore = "nightly: outer-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_left_requires_parent_child_link() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_left.click",
        "WRITE_ONCE(parent->rb_right, tmp2);",
        "WRITE_ONCE(parent->rb_right, parent);",
    );
}

#[test]
#[ignore = "nightly: outer-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_left_requires_sibling_child_link() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_left.click",
        "WRITE_ONCE(sibling->rb_left, parent);",
        "WRITE_ONCE(sibling->rb_left, 0);",
    );
}

#[test]
#[ignore = "nightly: outer-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_left_requires_far_child_blackening() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_left.click",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, sibling, RB_RED);",
    );
}

#[test]
#[ignore = "nightly: outer-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_left_requires_parent_blackening() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_left.click",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\tRB_BLACK);",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\tRB_RED);",
    );
}

#[test]
#[ignore = "nightly: outer-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_right_requires_parent_child_link() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_right.click",
        "WRITE_ONCE(parent->rb_left, tmp2);",
        "WRITE_ONCE(parent->rb_left, parent);",
    );
}

#[test]
#[ignore = "nightly: outer-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_right_requires_sibling_child_link() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_right.click",
        "WRITE_ONCE(sibling->rb_right, parent);",
        "WRITE_ONCE(sibling->rb_right, 0);",
    );
}

#[test]
#[ignore = "nightly: outer-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_right_requires_far_child_blackening() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_right.click",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, sibling, RB_RED);",
    );
}

#[test]
#[ignore = "nightly: outer-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_right_requires_parent_blackening() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_right.click",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\tRB_BLACK);",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\tRB_RED);",
    );
}

#[test]
#[ignore = "nightly: parent-update mutation verifies a whole sidecar"]
fn rbtree_set_parent_preserves_color() {
    erase_source_refuses_replacement(
        "rbtree_set_parent.click",
        "rbtree.h",
        "rb->__rb_parent_color = rb_color(rb) | (unsigned long)p;",
        "rb->__rb_parent_color = (unsigned long)p;",
        1,
    );
}

#[test]
#[ignore = "nightly: parent-update mutation verifies a whole sidecar"]
fn rbtree_set_parent_requires_new_parent() {
    erase_source_refuses_replacement(
        "rbtree_set_parent.click",
        "rbtree.h",
        "rb->__rb_parent_color = rb_color(rb) | (unsigned long)p;",
        "rb->__rb_parent_color = rb_color(rb) | (unsigned long)rb;",
        1,
    );
}

#[test]
#[ignore = "nightly: nonempty-near rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_nonempty_left_requires_near_parent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_nonempty_left.click",
        "rb_set_parent(tmp2, parent);",
        "rb_set_parent(tmp2, sibling);",
    );
}

#[test]
#[ignore = "nightly: nonempty-near rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_nonempty_left_requires_near_link() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_nonempty_left.click",
        "WRITE_ONCE(parent->rb_right, tmp2);",
        "WRITE_ONCE(parent->rb_right, NULL);",
    );
}

#[test]
#[ignore = "nightly: nonempty-near rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_nonempty_right_requires_near_parent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_nonempty_right.click",
        "rb_set_parent(tmp2, parent);",
        "rb_set_parent(tmp2, sibling);",
    );
}

#[test]
#[ignore = "nightly: nonempty-near rotation verifies a whole sidecar"]
fn rbtree_erase_color_outer_nonempty_right_requires_near_link() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_outer_nonempty_right.click",
        "WRITE_ONCE(parent->rb_left, tmp2);",
        "WRITE_ONCE(parent->rb_left, NULL);",
    );
}

#[test]
#[ignore = "nightly: inner-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_inner_left_requires_detached_inner_child() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_inner_left.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_left, tmp1);",
        "WRITE_ONCE(sibling->rb_left, tmp2);",
        1,
    );
}

#[test]
#[ignore = "nightly: inner-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_inner_left_requires_attached_old_sibling() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_inner_left.click",
        "rb_erase_color.c",
        "WRITE_ONCE(tmp2->rb_right, sibling);",
        "WRITE_ONCE(tmp2->rb_right, NULL);",
        1,
    );
}

#[test]
#[ignore = "nightly: inner-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_inner_left_requires_old_sibling_parent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_inner_left.click",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
    );
}

#[test]
#[ignore = "nightly: inner-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_inner_right_requires_detached_inner_child() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_inner_right.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_right, tmp1);",
        "WRITE_ONCE(sibling->rb_right, tmp2);",
        1,
    );
}

#[test]
#[ignore = "nightly: inner-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_inner_right_requires_attached_old_sibling() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_inner_right.click",
        "rb_erase_color.c",
        "WRITE_ONCE(tmp2->rb_left, sibling);",
        "WRITE_ONCE(tmp2->rb_left, NULL);",
        1,
    );
}

#[test]
#[ignore = "nightly: inner-red rotation verifies a whole sidecar"]
fn rbtree_erase_color_inner_right_requires_old_sibling_parent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_inner_right.click",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
    );
}

#[test]
#[ignore = "nightly: red-sibling rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_left_requires_parent_link() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_left.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_right, tmp1);",
        "WRITE_ONCE(parent->rb_right, NULL);",
        1,
    );
}

#[test]
#[ignore = "nightly: red-sibling rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_left_requires_sibling_link() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_left.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_left, parent);",
        "WRITE_ONCE(sibling->rb_left, NULL);",
        2,
    );
}

#[test]
#[ignore = "nightly: red-sibling rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_left_requires_red_parent() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_left.click",
        "rb_erase_color.c",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\t\tRB_RED);",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\t\tRB_BLACK);",
        2,
    );
}

#[test]
#[ignore = "nightly: red-sibling rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_right_requires_parent_link() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_right.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_left, tmp1);",
        "WRITE_ONCE(parent->rb_left, NULL);",
        1,
    );
}

#[test]
#[ignore = "nightly: red-sibling rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_right_requires_sibling_link() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_right.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_right, parent);",
        "WRITE_ONCE(sibling->rb_right, NULL);",
        2,
    );
}

#[test]
#[ignore = "nightly: red-sibling rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_right_requires_red_parent() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_right.click",
        "rb_erase_color.c",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\t\tRB_RED);",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\t\tRB_BLACK);",
        2,
    );
}

#[test]
#[ignore = "nightly: red-sibling double rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_outer_left_requires_first_parent_link() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_outer_left.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_right, tmp1);",
        "WRITE_ONCE(parent->rb_right, NULL);",
        1,
    );
}

#[test]
#[ignore = "nightly: red-sibling double rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_outer_left_requires_second_parent_link() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_outer_left.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_right, tmp2);",
        "WRITE_ONCE(parent->rb_right, sibling);",
        2,
    );
}

#[test]
#[ignore = "nightly: red-sibling double rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_outer_left_requires_far_child_parent() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_outer_left.click",
        "rb_erase_color.c",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
        2,
    );
}

#[test]
#[ignore = "nightly: red-sibling double rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_outer_right_requires_first_parent_link() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_outer_right.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_left, tmp1);",
        "WRITE_ONCE(parent->rb_left, NULL);",
        1,
    );
}

#[test]
#[ignore = "nightly: red-sibling double rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_outer_right_requires_second_parent_link() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_outer_right.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_left, tmp2);",
        "WRITE_ONCE(parent->rb_left, sibling);",
        2,
    );
}

#[test]
#[ignore = "nightly: red-sibling double rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_outer_right_requires_far_child_parent() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_outer_right.click",
        "rb_erase_color.c",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
        2,
    );
}

#[test]
#[ignore = "nightly: red-sibling inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_inner_left_requires_detached_inner_child() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_inner_left.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_left, tmp1);",
        "WRITE_ONCE(sibling->rb_left, tmp2);",
        1,
    );
}

#[test]
#[ignore = "nightly: red-sibling inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_inner_left_requires_attached_old_sibling() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_inner_left.click",
        "rb_erase_color.c",
        "WRITE_ONCE(tmp2->rb_right, sibling);",
        "WRITE_ONCE(tmp2->rb_right, NULL);",
        1,
    );
}

#[test]
#[ignore = "nightly: red-sibling inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_inner_left_requires_old_sibling_parent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_red_sibling_inner_left.click",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
    );
}

#[test]
#[ignore = "nightly: red-sibling inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_inner_right_requires_detached_inner_child() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_inner_right.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_right, tmp1);",
        "WRITE_ONCE(sibling->rb_right, tmp2);",
        1,
    );
}

#[test]
#[ignore = "nightly: red-sibling inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_inner_right_requires_attached_old_sibling() {
    erase_source_refuses_replacement(
        "rbtree_erase_color_red_sibling_inner_right.click",
        "rb_erase_color.c",
        "WRITE_ONCE(tmp2->rb_left, sibling);",
        "WRITE_ONCE(tmp2->rb_left, NULL);",
        1,
    );
}

#[test]
#[ignore = "nightly: red-sibling inner rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_inner_right_requires_old_sibling_parent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_red_sibling_inner_right.click",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
    );
}

#[test]
#[ignore = "nightly: nonempty-near rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_outer_nonempty_left_requires_near_parent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_red_sibling_outer_nonempty_left.click",
        "rb_set_parent(tmp2, parent);",
        "rb_set_parent(tmp2, sibling);",
    );
}

#[test]
#[ignore = "nightly: nonempty-near rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_outer_nonempty_left_requires_near_link() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_red_sibling_outer_nonempty_left.click",
        "WRITE_ONCE(parent->rb_right, tmp2);",
        "WRITE_ONCE(parent->rb_right, NULL);",
    );
}

#[test]
#[ignore = "nightly: nonempty-near rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_outer_nonempty_right_requires_near_parent() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_red_sibling_outer_nonempty_right.click",
        "rb_set_parent(tmp2, parent);",
        "rb_set_parent(tmp2, sibling);",
    );
}

#[test]
#[ignore = "nightly: nonempty-near rotation verifies a whole sidecar"]
fn rbtree_erase_color_red_sibling_outer_nonempty_right_requires_near_link() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_red_sibling_outer_nonempty_right.click",
        "WRITE_ONCE(parent->rb_left, tmp2);",
        "WRITE_ONCE(parent->rb_left, NULL);",
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling outer rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_outer_left_requires_parent_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_outer.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_right, tmp2);",
        "WRITE_ONCE(parent->rb_right, parent);",
        2,
    );
    assert!(
        error.contains("`have` failed for `parent->rb_right == iid`"),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling outer rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_outer_right_requires_parent_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_outer.click",
        "rb_erase_color.c",
        "WRITE_ONCE(parent->rb_left, tmp2);",
        "WRITE_ONCE(parent->rb_left, parent);",
        2,
    );
    assert!(
        error.contains("`have` failed for `parent->rb_left == iid`"),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling outer rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_outer_requires_far_blackening() {
    erase_color_refuses_mutation(
        "rbtree_erase_color_flips_red_outer.click",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, sibling, RB_RED);",
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling outer rotation verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_outer_requires_near_parent() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_outer.click",
        "rb_erase_color.c",
        "rb_set_parent(tmp2, parent);",
        "rb_set_parent(tmp2, sibling);",
        2,
    );
    assert!(
        error.contains("`have` failed for `tmp2->__rb_parent_color =="),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling inner repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_inner_right_requires_detached_child_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_inner_right.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_right, tmp1);",
        "WRITE_ONCE(sibling->rb_right, parent);",
        1,
    );
    assert!(
        error.contains("rb_right == tmp1"),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling inner repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_inner_right_requires_inner_parent_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_inner_right.click",
        "rb_erase_color.c",
        "WRITE_ONCE(tmp2->rb_left, sibling);",
        "WRITE_ONCE(tmp2->rb_left, parent);",
        1,
    );
    assert!(
        error.contains("iid->rb_left == sid"),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling inner repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_all_requires_left_detached_child_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_all.click",
        "rb_erase_color.c",
        "WRITE_ONCE(sibling->rb_left, tmp1);",
        "WRITE_ONCE(sibling->rb_left, parent);",
        1,
    );
    assert!(
        error.contains("rb_left == tmp1"),
        "unexpected refusal: {error}"
    );
}

#[test]
#[ignore = "nightly: propagated red-sibling inner repair verifies a whole sidecar"]
fn rbtree_erase_color_flips_red_all_requires_left_inner_parent_link() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_all.click",
        "rb_erase_color.c",
        "WRITE_ONCE(tmp2->rb_right, sibling);",
        "WRITE_ONCE(tmp2->rb_right, parent);",
        1,
    );
    assert!(
        error.contains("iid->rb_right == sid"),
        "unexpected refusal: {error}"
    );
}

#[test]
fn rbtree_erase_wrapper_uses_the_unchanged_pinned_callbacks_and_body() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let bytes = fs::read(root.join("examples/rbtree-erase/rb_erase.c"))
        .expect("the pinned erase wrapper exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "5854bdc7cdb7ec2d330c0f7aa15afb5f3c95983cf0a90f2ad0b608113a71b4b8"
    );
}

#[test]
#[ignore = "nightly: erase wrapper mutation verifies the combined repair sidecar"]
fn rbtree_erase_wrapper_requires_nonnull_color_repair() {
    let error = erase_source_replacement_error(
        "rbtree_erase_color_flips_red_all.click",
        "rb_erase.c",
        "if (rebalance)",
        "if (!rebalance)",
        1,
    );
    assert!(
        error.contains("requires a call to `____rb_erase_color` at the current frontier"),
        "unexpected refusal: {error}"
    );
}
