// Proof-result auto traits traverse the same Arc-linked alpha-key/load cycle
// documented in src/lib.rs. This crate needs the library's compiler setting.
#![recursion_limit = "256"]

use click::surface::ProgramInputs;
use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Component, Path, PathBuf};
use std::process::Command;

use sha2::{Digest, Sha256};

use click::cli::{
    CInput, files_with_extension, read_c_inputs_for_project, read_click_project,
    read_click_project_at_root, read_verifying_sources, select_sidecars, source_refs,
};
use click::instrumentation::{self, ArtifactReuseRejection, HiddenPrerequisiteRoute};
use click::surface::{
    c0_tactic_source_position, project_tactic_source_position, verify_c0_prepared_project,
    verify_c0_project, verify_c0_sources, verify_c0_sources_at, verify_program_prepared_project,
};

#[path = "support/limits.rs"]
mod limits;
#[path = "support/tactic_work.rs"]
mod tactic_work;

const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
/// Set by the gate when the pinned C++ exporter is not installed.
const SOURCE_MANIFEST: &str = "SOURCE.sha256";
const SOURCE_METADATA: &str = "SOURCE.md";

/// Known-broken or pathologically slow projects, skipped by default so the
/// suite is a meaningful green gate. Run one with `CLICK_EXAMPLE=<name>`, or
/// all of them with `CLICK_RUN_QUARANTINED=1`. Each entry names the reason;
/// remove entries as they are fixed (see docs/internals/testing.md).
const QUARANTINED: &[(&str, &str)] = &[];

/// The artifact reuse rejection ratchet (`docs/internals/testing.md`) over
/// every example project; see `tests/mdtests.rs` for the rule.
const ARTIFACT_REUSE_REJECTION_BASELINE: &[(ArtifactReuseRejection, usize)] = &[];

/// The hidden prerequisite ratchet (`docs/internals/testing.md`): count the
/// prerequisites simple statement checking derived by a search the proof does
/// not retain, over the whole unfiltered corpus, by route and top rule. A
/// count may only fall, and it is zero.
const HIDDEN_PREREQUISITE_BASELINE: &[((HiddenPrerequisiteRoute, &str), usize)] = &[];

#[test]
#[ignore = "nightly: 4s in the parallel gate"]
fn frozen_shared_heap_lifecycles_verify() {
    let project = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("design")
        .join("shared-heap-probes");
    run_example_in_thread(&project).unwrap_or_else(|error| panic!("{error}"));
}

#[test]
#[ignore = "nightly: 1.9s in the parallel gate"]
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
#[ignore = "nightly: 0.5s in the parallel gate"]
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
        let sidecar = root.join(entry["sidecar"].as_str().unwrap());
        let directory = sidecar.parent().unwrap();
        let config = directory.join("click.project.json");
        let metadata: serde_json::Value =
            serde_json::from_slice(&fs::read(&config).unwrap()).unwrap();
        let units = metadata["units"].as_object().unwrap();
        assert!(!units.is_empty());
        for unit in units.values() {
            assert_eq!(unit["language"], "rust");
            assert!(
                unit.get("backend").is_none(),
                "canonical Rust examples use the native default"
            );
        }
        assert!(directory.join("click.project.lock.json").is_file());
        run_example_in_thread(directory).unwrap_or_else(|error| panic!("{error}"));
        checked += 1;
    }
    assert_eq!(checked, 17);
}

/// Examples the ten-minute gate leaves to the nightly run, with the
/// measurement that put each one here.
const NIGHTLY: &[(&str, &str)] = &[
    (
        "rbtree/rbtree-insert",
        "verifies in about 118 s on 20 cores, most of the gate's budget alone (2026-10-06)",
    ),
    (
        "rbtree/rbtree-erase",
        "the general unlink and color repair take minutes; 347 s in a debug test build (2026-10-14)",
    ),
    (
        "rbtree/rbtree-augmented",
        "261 s in a debug test build on 4 cores, 44 s release, the gate's long pole (2026-10-15)",
    ),
];

#[test]
fn example_projects() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let examples_dir = manifest_dir.join("examples");
    let requested = std::env::var_os("CLICK_EXAMPLE");
    let run_quarantined = requested.is_some() || std::env::var_os(RUN_QUARANTINED).is_some();
    let examples_dir = fs::canonicalize(&examples_dir)
        .unwrap_or_else(|error| panic!("failed to resolve `{}`: {error}", examples_dir.display()));
    let mut projects = example_directories(&examples_dir)
        .into_iter()
        .filter(|path| {
            requested.as_ref().is_none_or(|requested| {
                let name = example_name(&examples_dir, path);
                let requested = requested.to_string_lossy();
                name == requested || name.starts_with(&format!("{requested}/"))
            })
        })
        .collect::<Vec<_>>();

    // The gate has a ten-minute budget. An example that takes most of it
    // alone runs in the nightly gate (`scripts/check.sh --nightly`), or on
    // request by name.
    // Leaving them out makes the census partial, as a partition does: the
    // pins count the whole corpus.
    let skipped_nightly = requested.is_none() && std::env::var_os("CLICK_NIGHTLY").is_none() && {
        let before = projects.len();
        projects.retain(|path| {
            let name = example_name(&examples_dir, path);
            match NIGHTLY.iter().find(|(nightly, _)| *nightly == name) {
                Some((name, reason)) => {
                    println!("SKIPPING nightly example `{name}`: {reason}");
                    false
                }
                None => true,
            }
        });
        projects.len() != before
    };
    // CI splits the examples across jobs to stay inside the gate's time
    // budget: `EXAMPLE_PARTITION=k/n` keeps every n-th project from the k-th,
    // over the sorted names, so the shards cover them exactly once.
    let partitioned = std::env::var_os("EXAMPLE_PARTITION").is_some();
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
            let name = example_name(&examples_dir, path);
            let quarantine = QUARANTINED
                .iter()
                .find(|(quarantined, _)| *quarantined == name);
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
    let _ = instrumentation::take_hidden_prerequisite_census();
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
    let hidden_prerequisites = instrumentation::take_hidden_prerequisite_census();
    if requested.is_none()
        && !run_quarantined
        && let Some(mismatch) = instrumentation::artifact_reuse_rejection_census_mismatch(
            &census,
            ARTIFACT_REUSE_REJECTION_BASELINE,
        )
    {
        panic!("artifact reuse rejection ratchet (tests/examples.rs baselines):\n{mismatch}");
    }
    if requested.is_none()
        && !run_quarantined
        && let Some(mismatch) = instrumentation::hidden_prerequisite_census_mismatch(
            &hidden_prerequisites,
            HIDDEN_PREREQUISITE_BASELINE,
            partitioned || skipped_nightly,
        )
    {
        panic!("hidden prerequisite ratchet (tests/examples.rs baselines):\n{mismatch}");
    }
}

/// The insert example verifies in the ordinary example gate; this pins what
/// that verdict is about: the unchanged Linux C and the shared model.
#[test]
fn rbtree_insert_uses_the_unchanged_c_and_the_shared_model() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (relative, expected) in [
        (
            "examples/rbtree/rbtree-insert/rbtree.h",
            "69fc7419118e4a37fb46a2469b981646a733b1a7c247094d0b48aa643575cee3",
        ),
        (
            "examples/rbtree/rbtree-insert/rb_insert_color.c",
            "b20d68f309682bdcebcf2176d655b92b582f2c88bcc0f4645a7384c0760df111",
        ),
    ] {
        let bytes = fs::read(root.join(relative)).expect("the unchanged insert C input exists");
        assert_eq!(hex_digest(sha256(&bytes)), expected, "changed {relative}");
    }
    let source = fs::read_to_string(root.join("examples/rbtree/rbtree-insert/rbtree_insert.click"))
        .expect("the insert sidecar should exist");
    assert!(source.contains("import \"../rbtree-model/rbtree_model.click\";"));
    assert!(!source.contains("spec enum RbTree"));
    assert!(source.contains("void __rb_insert("));
}

/// A wholly selected claim's failure must be an audit failure, without a
/// per-site retry that can hide a broken combined expansion.
///
/// The failure is forced through the claim's verification budget. A wholly
/// selected claim is expanded from the certificates the audit session
/// retained, which renders source without verifier work (`expand 0 units`),
/// so an expansion budget of one unit cannot fail it; reverifying the
/// expanded claim spends hundreds of units.
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
            "--verification-work-limit",
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
        assert!(stdout.contains("over its 1-unit budget"), "{stdout}");
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

/// Auto must choose a spellable certificate for the original recoloring equality.
#[test]
#[ignore = "nightly: rechecks rbtree recoloring expansion"]
fn rbtree_auto_recolor_expansion_rechecks() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("examples/rbtree/rbtree-insert/rbtree_insert.click");
    let mut source = fs::read_to_string(&path).unwrap();
    let anchor =
        "have rb_inorder(plug(Context::Top, RbTree::Node(nid, 0, Color::Black, nleft, nright)))";
    let have = source.find(anchor).expect("keep the original rbtree case");
    let start = have + source[have..].find("by {").unwrap();
    let open = start + "by ".len();
    let mut depth = 0;
    let end = source[open..]
        .char_indices()
        .find_map(|(offset, character)| {
            match character {
                '{' => depth += 1,
                '}' => depth -= 1,
                _ => {}
            }
            (depth == 0).then_some(open + offset + character.len_utf8())
        })
        .expect("the written proof block ends");
    source.replace_range(start..end, "by auto();");
    let c_sources = read_verifying_sources(&path, &source).unwrap();
    let project = read_click_project(&path, &source).unwrap();
    let line = source[..start]
        .bytes()
        .filter(|byte| *byte == b'\n')
        .count()
        + 1;
    let column = source[..start].rsplit('\n').next().unwrap().len() + 4;
    let expanded = click::surface::expand_project_tactic_source_at(
        &project,
        &ProgramInputs::Bundle(source_refs(&c_sources)),
        line,
        column,
    )
    .expect("auto's selected certificate must have source spelling");
    let rewritten = project.with_entry_source(expanded);
    click::surface::verify_project_at(
        &rewritten,
        &ProgramInputs::Bundle(source_refs(&c_sources)),
        line,
        column,
    )
    .expect("the expanded original-pattern site must reverify");
    let result = click::surface::expand_project_claim_source_by_label(
        &project,
        &ProgramInputs::Bundle(source_refs(&c_sources)),
        "__rb_insert.contract",
    );
    let error = match result {
        Ok(expanded) => {
            click::surface::verify_c0_project(
                &project.with_entry_source(expanded),
                &source_refs(&c_sources),
            )
            .expect("a whole-claim expansion must not emit unspellable values");
            return;
        }
        Err(error) => error,
    };
    assert!(
        error.message().contains("which has no surface spelling"),
        "{error:?}"
    );
    assert!(error.message().contains("__rb_insert"), "{error:?}");
    assert!(
        !error.message().contains("unexpected character"),
        "{error:?}"
    );
}

/// Nested execution matches must retain their own branch's shared tactics.
#[test]
#[ignore = "nightly: whole rbtree insert expansion and cold verification exceed the gate budget"]
fn rbtree_insert_whole_claim_expansion_verifies() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("examples/rbtree/rbtree-insert/rbtree_insert.click");
    let source = fs::read_to_string(&path).unwrap();
    let c_sources = read_verifying_sources(&path, &source).unwrap();
    let project = read_click_project(&path, &source).unwrap();
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

/// A recorded call frame must remain usable in a new proof-input lineage.
#[test]
#[ignore = "nightly: verifies and expands the sized context rotation in a retained session"]
fn rbtree_sized_context_rotation_retained_session_expansion_rechecks() {
    check_sized_context_rotation_retained_expansion("rbtree_size_insert_context_rotation.click");
}

#[test]
#[ignore = "nightly: verifies and expands the mirrored sized context rotation in a retained session"]
fn rbtree_sized_mirrored_context_rotation_retained_session_expansion_rechecks() {
    check_sized_context_rotation_retained_expansion(
        "rbtree_size_insert_mirrored_context_rotation.click",
    );
}

#[test]
#[ignore = "nightly: verifies and expands the sized double context rotation in a retained session"]
fn rbtree_sized_context_double_rotation_retained_session_expansion_rechecks() {
    check_sized_context_rotation_retained_expansion(
        "rbtree_size_insert_context_double_rotation.click",
    );
}

#[test]
#[ignore = "nightly: verifies and expands the mirrored sized double context rotation in a retained session"]
fn rbtree_sized_mirrored_context_double_rotation_retained_session_expansion_rechecks() {
    check_sized_context_rotation_retained_expansion(
        "rbtree_size_insert_mirrored_context_double_rotation.click",
    );
}

/// A metadata alias's snapshot hash must not change which read history a
/// cold check visits after earlier verification and project summarization.
#[test]
#[ignore = "nightly: checks sized uncle rotation cold, after summary, expanded, and retained"]
fn rbtree_sized_uncle_rotation_origin_order_and_expansion_recheck() {
    const SIDECAR: &str = "rbtree_size_insert_context_uncle_rotation.click";
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/rbtree/rbtree-augmented")
        .join(SIDECAR);
    limits::spawn(
        "uncle rotation cold comparisons",
        "click-uncle-origin-order".into(),
        move || {
            let source = fs::read_to_string(&path).unwrap();
            let (project, inputs) = click::cli::read_lone_sidecar_inputs(&path, &source).unwrap();
            let claim = "insert::__rb_insert.contract";
            let position =
                project_tactic_source_position(&project, &inputs.program_inputs(), claim, 0)
                    .unwrap();
            click::surface::verify_project_at(
                &project,
                &inputs.program_inputs(),
                position.line,
                position.column,
            )
            .expect("the original rotation verifies cold");
            click::surface::project_summary(&project, &inputs.program_inputs()).unwrap();
            let verified = click::surface::verify_project_at(
                &project,
                &inputs.program_inputs(),
                position.line,
                position.column,
            )
            .expect("summarization must not change the cold check's read-origin order");
            let expanded = click::surface::expand_verified_function_claim_source_by_label(
                &source, &verified, claim,
            )
            .unwrap()
            .expect("the checked rotation has an expansion");
            let rewritten = project.with_entry_source(expanded);
            let position =
                project_tactic_source_position(&rewritten, &inputs.program_inputs(), claim, 0)
                    .unwrap();
            click::surface::verify_project_at(
                &rewritten,
                &inputs.program_inputs(),
                position.line,
                position.column,
            )
            .expect("the expanded rotation verifies cold after summarization");
        },
    )
    .unwrap();
    check_sized_context_rotation_retained_expansion(SIDECAR);
}

fn check_sized_context_rotation_retained_expansion(sidecar: &str) {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("examples/rbtree/rbtree-augmented")
        .join(sidecar);
    limits::spawn(
        "sized context rotation retained expansion",
        "click-sized-context-expansion".to_string(),
        move || {
            let loaded = click::cli::load_target_inputs(&path, None).unwrap();
            let (session, verified) = match &loaded.inputs {
                CInput::Bundle(sources) => click::surface::C0VerificationSession::new_project(
                    &loaded.project,
                    &source_refs(sources),
                ),
                CInput::Prepared(imports) => {
                    click::surface::C0VerificationSession::new_prepared_project(
                        &loaded.project,
                        imports,
                    )
                }
                CInput::PreparedProgram(import) => {
                    click::surface::C0VerificationSession::new_program_prepared_project(
                        &loaded.project,
                        import,
                    )
                }
            }?;
            let claim = "insert::__rb_insert.contract";
            let expanded = click::surface::expand_verified_function_claim_source_by_label(
                &loaded.click_source,
                &verified,
                claim,
            )?
            .expect("the insertion claim has a retained certificate");
            let rewritten = loaded.project.with_entry_source(expanded.clone());
            let position = project_tactic_source_position(
                &rewritten,
                &loaded.inputs.program_inputs(),
                claim,
                0,
            )?;
            session.verify_at_project(&expanded, position.line, position.column)
        },
    )
    .unwrap()
    .expect("the expanded rotation must recheck against the retained function environment");
}

/// The insert proof against a copy of the C whose root case skips its
/// recolour, `rb_set_parent_color(node, NULL, RB_BLACK)`. The proof claims the
/// root's colour bit is black at that `break`, which the C no longer makes
/// true, and that claim is refused; the files on disk are not changed.
#[test]
#[ignore = "nightly: 5s in the parallel gate"]
fn rbtree_insert_refuses_a_skipped_recolour() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("examples/rbtree/rbtree-insert/rbtree_insert.click");
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
    let project = read_click_project(&path, &source)
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
    let bytes = fs::read(root.join("examples/rbtree/rbtree-erase/rb_erase_augmented.c"))
        .expect("the pinned erase C input exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "f861b937f0cb142104061ccccb9f6247c99ca4f6d0f4d6033b8720a86f967022"
    );
}

/// Expanding the last exit's closing `simp` writes explicit closers that
/// still return the outcome resource; the expansion cold verifies.
#[test]
#[ignore = "nightly: 41 s to expand and recheck the general unlink in a release build (2026-10-14)"]
fn rbtree_erase_general_explicit_closers_preserve_ownership() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("examples/rbtree/rbtree-erase/rbtree_erase_augmented.click");
    let source = fs::read_to_string(&path).unwrap();
    let c_sources = read_verifying_sources(&path, &source).unwrap();
    let project = read_click_project(&path, &source).unwrap();
    let (line, text) = source
        .lines()
        .enumerate()
        .filter(|(_, line)| line.trim() == "simp();")
        .last()
        .unwrap();
    let column = text.find("simp").unwrap() + 1;
    limits::spawn(
        "general unlink closer expansion",
        "click-general-erase-expansion".into(),
        move || {
            let expanded = click::surface::expand_project_tactic_source_at(
                &project,
                &ProgramInputs::Bundle(source_refs(&c_sources)),
                line + 1,
                column,
            )?;
            let expanded_project = read_click_project(&path, &expanded)
                .expect("the expanded general unlink resolves its imports");
            click::surface::verify_c0_project(&expanded_project, &source_refs(&c_sources))
        },
    )
    .unwrap()
    .unwrap();
}

/// The general unlink against a copy of `rb_erase_augmented.c` with one
/// statement replaced, refused with `refusal`. Each mutation keeps the C's
/// statement count, so the proof's `execute_until(statement(...))` positions
/// still name the same statements and the refusal is the exit that depends
/// on the replaced statement, not a misaligned frontier.
fn general_erase_refuses_mutation(before: &str, after: &str, refusal: &str) {
    let error = erase_source_replacement_error(
        "rbtree_erase_augmented.click",
        "rb_erase_augmented.c",
        before,
        after,
        1,
    );
    assert!(error.contains(refusal), "unexpected refusal: {error}");
}

fn erase_source_refuses_mutation(sidecar: &str, file: &str, before: &str, after: &str) {
    erase_source_refuses_replacement(sidecar, file, before, after, 1);
}

/// `auto` at this `arena` site once deadlocked: the equality graph held its
/// lock while canonicalizing a cell read, and canonicalization consulted the
/// same graph's read generation. It must now answer promptly. The original
/// proof stays in the example; only this test proves the fact by `auto`.
#[test]
#[ignore = "nightly: about 16 s in a debug build, most of it loading the whole arena sidecar"]
fn auto_on_an_arena_cell_read_answers_instead_of_deadlocking() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("examples/arena/arena_cells.click");
    let source = fs::read_to_string(&path).expect("the arena sidecar exists");
    let written = "have first->arena->occupied[k] == at(f1, first->arena->occupied[k]) by {";
    let start = source
        .find(written)
        .expect("the arena proof states the cell read");
    let block_end = start
        + source[start..]
            .find("\n                }\n")
            .expect("the written proof closes")
        + "\n                }".len();
    let edited = format!(
        "{}have first->arena->occupied[k] == at(f1, first->arena->occupied[k]) by auto();{}",
        &source[..start],
        &source[block_end..]
    );
    let line = edited[..start].matches('\n').count() + 1;
    let column = start - edited[..start].rfind('\n').map_or(0, |newline| newline + 1) + 1;
    let c_sources = read_verifying_sources(&path, &edited).expect("the arena C bundle loads");
    let started = std::time::Instant::now();
    let _ = limits::spawn(
        "arena auto verifier",
        "click-arena-auto".to_string(),
        move || verify_c0_sources_at(&edited, &source_refs(&c_sources), line, column),
    )
    .unwrap_or_else(|error| panic!("{error}"));
    assert!(
        started.elapsed() < std::time::Duration::from_secs(120),
        "`auto` at the arena cell read took {:?}",
        started.elapsed()
    );
}

fn erase_source_replacement_error(
    sidecar: &str,
    file: &str,
    before: &str,
    after: &str,
    occurrences: usize,
) -> String {
    erase_source_replacement_error_for_function(sidecar, file, before, after, occurrences, None)
}

fn erase_source_replacement_error_for_function(
    sidecar: &str,
    file: &str,
    before: &str,
    after: &str,
    occurrences: usize,
    function: Option<&str>,
) -> String {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("examples/rbtree/rbtree-erase").join(sidecar);
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
    let project = read_click_project(&path, &source)
        .expect("the erase proof resolves its shared resources and model");
    let function = function.map(str::to_owned);
    limits::spawn(
        "erase mutation verifier",
        "click-erase-mutation".to_string(),
        move || match function {
            Some(function) => click::surface::verify_project_functions(
                &project,
                &ProgramInputs::Bundle(source_refs(&c_sources)),
                [function],
            ),
            None => click::surface::verify_c0_project(&project, &source_refs(&c_sources)),
        },
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

/// The right-only child must take the erased node's parent and color.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_refuses_a_skipped_right_child_parent_color() {
    general_erase_refuses_mutation(
        "\t\t\tchild->__rb_parent_color = pc;\n",
        "\t\t\tchild = child;\n",
        "could not establish `er_id->__rb_parent_color == pc`",
    );
}

/// The left-only child must take the erased node's parent and color.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_refuses_a_skipped_left_child_parent_color() {
    general_erase_refuses_mutation(
        "\t\ttmp->__rb_parent_color = pc = node->__rb_parent_color;\n",
        "\t\tpc = pc = node->__rb_parent_color;\n",
        "could not establish `el_id->__rb_parent_color == pc`",
    );
}

/// A one-child exit must relink the erased node's parent.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_refuses_a_skipped_root_replacement() {
    general_erase_refuses_mutation(
        "\t\t__rb_change_child(node, child, parent, root);\n",
        "\t\tchild = child;\n",
        "requires a call to `__rb_change_child#inline:rb_erase.c` at the current frontier; next operation: child = child",
    );
}

/// The successor must become its new left subtree's parent.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_successor_refuses_a_skipped_left_parent_write() {
    general_erase_refuses_mutation(
        "\t\trb_set_parent(tmp, successor);\n",
        "\t\ttmp = tmp;\n",
        "fold requires the instance body facts for the proposed fields",
    );
}

/// The successor must take the erased node's parent and color.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_successor_refuses_a_skipped_parent_color_write() {
    general_erase_refuses_mutation(
        "\t\tsuccessor->__rb_parent_color = pc;\n",
        "\t\ttmp = tmp;\n",
        "fact 5 of 9 of arm `Right` is not established",
    );
}

/// A black-leaf successor leaves a deficit at its old parent.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_black_successor_requires_the_fixup_parent() {
    general_erase_refuses_mutation(
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = NULL;\n",
        "equality: 0 == mp",
    );
}

/// A successor's child that replaces it must be blackened.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_child_successor_requires_blackening() {
    general_erase_refuses_mutation(
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n",
        "\t\t\trb_set_parent_color(child2, parent, RB_RED);\n",
        "could not establish `cid->__rb_parent_color == (((uint64)mp) | 1)`",
    );
}

/// A successor's child that replaces it must take the successor's old parent.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_child_successor_requires_parent_color_write() {
    general_erase_refuses_mutation(
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n",
        "\t\t\tchild2 = child2;\n",
        "could not establish `cid->__rb_parent_color == (((uint64)mp) | 1)`",
    );
}

/// A black leaf leaves a deficit at its parent.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_black_leaf_requires_the_fixup_parent() {
    general_erase_refuses_mutation(
        "\t\t\trebalance = __rb_is_black(pc) ? parent : NULL;\n",
        "\t\t\trebalance = NULL;\n",
        "could not establish `result != 0`",
    );
}

/// A red leaf leaves no deficit.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_red_leaf_requires_no_fixup() {
    general_erase_refuses_mutation(
        "\t\t\trebalance = __rb_is_black(pc) ? parent : NULL;\n",
        "\t\t\trebalance = parent;\n",
        "required body fact: erased_parent == 0",
    );
}

/// The right-only child keeps the erased node's black color.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_right_child_requires_blackening() {
    general_erase_refuses_mutation(
        "\t\t\tchild->__rb_parent_color = pc;\n",
        "\t\t\tchild->__rb_parent_color = pc & ~1;\n",
        "could not establish `er_id->__rb_parent_color == pc`",
    );
}

/// The left-only child keeps the erased node's black color.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_left_child_requires_blackening() {
    general_erase_refuses_mutation(
        "\t\ttmp->__rb_parent_color = pc = node->__rb_parent_color;\n",
        "\t\ttmp->__rb_parent_color = pc = node->__rb_parent_color & ~1;\n",
        "could not establish `el_id->__rb_parent_color == pc`",
    );
}

/// A one-child exit leaves no deficit.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_right_child_requires_no_fixup() {
    general_erase_refuses_mutation(
        "\t\t\tchild->__rb_parent_color = pc;\n\t\t\trebalance = NULL;",
        "\t\t\tchild->__rb_parent_color = pc;\n\t\t\trebalance = parent;",
        "required body fact: erased_parent == 0",
    );
}

/// A one-child exit leaves no deficit.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_left_child_requires_no_fixup() {
    general_erase_refuses_mutation(
        "\t\t__rb_change_child(node, tmp, parent, root);\n\t\trebalance = NULL;",
        "\t\t__rb_change_child(node, tmp, parent, root);\n\t\trebalance = parent;",
        "required body fact: erased_parent == 0",
    );
}

/// The successor must adopt the erased node's left subtree.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_successor_requires_left_subtree_link() {
    general_erase_refuses_mutation(
        "\t\tWRITE_ONCE(successor->rb_left, tmp);\n",
        "\t\ttmp = tmp;\n",
        "could not establish `mid->rb_left == lid`",
    );
}

/// A red-leaf successor leaves no deficit.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_red_successor_requires_no_fixup() {
    general_erase_refuses_mutation(
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = parent;\n",
        "required body fact: result == 0",
    );
}

/// A successor with a child leaves no deficit.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_child_successor_requires_no_fixup() {
    general_erase_refuses_mutation(
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n\t\t\trebalance = NULL;",
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n\t\t\trebalance = parent;",
        "required body fact: result == 0",
    );
}

/// The deficit is at the successor's old parent, not its new one.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_black_successor_requires_its_old_parent_as_fixup_parent() {
    general_erase_refuses_mutation(
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = rb_is_black(successor) ? tmp : NULL;\n",
        "equality: rebalance == mp",
    );
}

/// A two-child exit must relink the erased node's parent to the successor.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_successor_requires_root_replacement() {
    general_erase_refuses_mutation(
        "\t\t__rb_change_child(node, successor, tmp, root);\n",
        "\t\ttmp = tmp;\n",
        "requires a call to `__rb_change_child#inline:rb_erase.c` at the current frontier; next operation: tmp = tmp",
    );
}

/// A deeper successor must be spliced out of its parent.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_deep_successor_refuses_a_skipped_splice() {
    general_erase_refuses_mutation(
        "\t\t\tWRITE_ONCE(parent->rb_left, child2);\n",
        "\t\t\tWRITE_ONCE(parent->rb_left, successor);\n",
        "could not establish `parent->rb_left == 0`",
    );
}

/// A deeper successor's child must take the successor's old parent.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_deep_successor_refuses_the_wrong_replacement_parent() {
    general_erase_refuses_mutation(
        "\t\t\trb_set_parent_color(child2, parent, RB_BLACK);\n",
        "\t\t\trb_set_parent_color(child2, successor, RB_BLACK);\n",
        "could not establish `cid->__rb_parent_color == (((uint64)mp) | 1)`",
    );
}

/// A deeper successor must adopt the erased node's right subtree.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_deep_successor_refuses_a_skipped_right_attachment() {
    general_erase_refuses_mutation(
        "\t\t\tWRITE_ONCE(successor->rb_right, child);\n",
        "\t\t\tWRITE_ONCE(successor->rb_right, successor->rb_right);\n",
        "could not establish `mid->rb_right == child`",
    );
}

/// The adopted right subtree must take the successor as parent.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_deep_successor_refuses_a_skipped_right_parent_update() {
    general_erase_refuses_mutation(
        "\t\t\trb_set_parent(child, successor);\n",
        "\t\t\trb_set_parent(child, node);\n",
        "`have` failed for `child->__rb_parent_color == (address(mid) + (child->__rb_parent_color & 1))`",
    );
}

/// A deeper black-leaf successor leaves the deficit at its old parent.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_deep_black_leaf_requires_the_splice_parent() {
    general_erase_refuses_mutation(
        "\t\t\trebalance = rb_is_black(successor) ? parent : NULL;\n",
        "\t\t\trebalance = successor;\n",
        "equality: rebalance == mp",
    );
}

/// The adopted right subtree's parent must be updated at all.
#[test]
#[ignore = "nightly: verifies the whole general unlink, 4 to 18 s in a release build"]
fn rbtree_erase_deep_black_leaf_requires_right_parent_update() {
    general_erase_refuses_mutation(
        "\t\t\trb_set_parent(child, successor);\n",
        "\t\t\tchild = child;\n",
        "`have` failed for `child->__rb_parent_color == (address(mid) + (child->__rb_parent_color & 1))`",
    );
}

#[test]
#[ignore = "nightly: 2.3s in the parallel gate"]
fn rbtree_change_child_requires_left_link() {
    erase_source_refuses_mutation(
        "rbtree_change_child.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_left, new);",
        "            WRITE_ONCE(parent->rb_left, old);",
    );
}

#[test]
#[ignore = "nightly: 2.5s in the parallel gate"]
fn rbtree_change_child_requires_right_link() {
    erase_source_refuses_mutation(
        "rbtree_change_child.click",
        "rbtree.h",
        "            WRITE_ONCE(parent->rb_right, new);",
        "            WRITE_ONCE(parent->rb_right, old);",
    );
}

#[test]
#[ignore = "nightly: 2.2s in the parallel gate"]
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

/// The directories the example gate runs: each directory under `examples`
/// that directly holds a sidecar, sorted. A project with sidecars in several
/// directories (`examples/rbtree`) runs as several, so the gate can schedule
/// and skip its parts by name.
fn example_directories(examples: &Path) -> Vec<PathBuf> {
    let selection = select_sidecars(examples)
        .unwrap_or_else(|error| panic!("failed to select example sidecars: {error}"));
    selection
        .sidecars()
        .filter_map(Path::parent)
        .map(Path::to_path_buf)
        .collect::<BTreeSet<_>>()
        .into_iter()
        .collect()
}

/// An example directory's name: its path below `examples`, such as
/// `rbtree/rbtree-insert`.
fn example_name(examples: &Path, directory: &Path) -> String {
    directory
        .strip_prefix(examples)
        .unwrap_or(directory)
        .components()
        .map(|component| component.as_os_str().to_string_lossy())
        .collect::<Vec<_>>()
        .join("/")
}

fn run_example_in_thread(project: &Path) -> Result<(), String> {
    let project = project.to_path_buf();
    limits::spawn("example verifier", "click-example".to_string(), move || {
        run_example_project(&project)
    })?
}

fn run_example_project(project: &Path) -> Result<(), String> {
    let source_status = verify_source_integrity(project)?;
    if let Some(status) = source_status {
        eprintln!(
            "source fixture `{}` integrity manifest passed; status: {}",
            project.display(),
            status.as_str()
        );
    }

    let selection = select_sidecars(project)?;
    let click_paths = selection
        .projects
        .iter()
        .flat_map(|selected| {
            selected
                .sidecars
                .iter()
                .map(|sidecar| (sidecar.clone(), selected.root.clone()))
        })
        .collect::<Vec<_>>();

    for (click_path, project_root) in click_paths {
        let click_source = fs::read_to_string(&click_path)
            .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
        let click_project = read_click_project_at_root(&click_path, &click_source, &project_root)?;
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
            ) || matches!(name, "COPYING" | "LICENSE" | "LICENSE.txt"))
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
    let bytes = fs::read(root.join("examples/rbtree/rbtree-erase/rb_erase_color.c"))
        .expect("the pinned erase-color C input exists");
    assert_eq!(
        hex_digest(sha256(&bytes)),
        "1964275955333d0c872f193d30283e6de1fbbd2e3315606734321de0d5bc503e"
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

// Each mutation below was first pinned against a per-case increment; the
// general proof subsumes those increments, so it must refuse every one.
// rb_erase_color.c contains only ____rb_erase_color (the pinned-source gate
// protects that fixture). Mutations leave the sidecar and every other C
// input unchanged, so recheck this complete function rather than unrelated
// pure lemmas and unchanged header helper proofs. Keep the exact diagnostic
// assertions for every mutation.
fn erase_color_general_refuses_mutation(
    before: &str,
    after: &str,
    occurrences: usize,
    expected: &str,
) {
    let error = erase_source_replacement_error_for_function(
        "rbtree_erase_color_flips_red_all.click",
        "rb_erase_color.c",
        before,
        after,
        occurrences,
        Some("____rb_erase_color"),
    );
    assert!(error.contains(expected), "unexpected refusal: {error}");
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_red_left_requires_parent_blackening() {
    erase_color_general_refuses_mutation(
        "rb_set_black(parent);",
        "parent->__rb_parent_color = parent->__rb_parent_color;",
        2,
        "`have` failed for `parent->__rb_parent_color == (at(red_flip, parent->__rb_parent_color) + 1)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_red_left_requires_sibling_recoloring() {
    erase_color_general_refuses_mutation(
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_RED);",
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_BLACK);",
        2,
        "`have` failed for `sid->__rb_parent_color == address(id)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_red_left_requires_the_sibling_parent() {
    erase_color_general_refuses_mutation(
        "rb_set_parent_color(sibling, parent,\n\t\t\t\t\t\t\t    RB_RED);",
        "rb_set_parent_color(sibling, sibling,\n\t\t\t\t\t\t\t    RB_RED);",
        2,
        "`have` failed for `sid->__rb_parent_color == address(id)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_root_left_requires_the_null_parent_cursor() {
    erase_color_general_refuses_mutation(
        "parent = rb_parent(node);",
        "parent = node;",
        2,
        "`have` failed for `parent == above`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_requires_focus_ascent() {
    erase_color_general_refuses_mutation(
        "node = parent;",
        "node = node;",
        2,
        "missing resource fact",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_outer_left_requires_parent_child_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(parent->rb_right, tmp2);",
        "WRITE_ONCE(parent->rb_right, parent);",
        2,
        "`have` failed for `parent->rb_right == iid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_outer_right_requires_parent_child_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(parent->rb_left, tmp2);",
        "WRITE_ONCE(parent->rb_left, parent);",
        2,
        "`have` failed for `parent->rb_left == iid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_outer_requires_far_child_blackening() {
    erase_color_general_refuses_mutation(
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, sibling, RB_RED);",
        2,
        "`have` failed for `tmp1->__rb_parent_color == (address(sibling) | 1)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_outer_requires_near_parent() {
    erase_color_general_refuses_mutation(
        "rb_set_parent(tmp2, parent);",
        "rb_set_parent(tmp2, sibling);",
        2,
        "`have` failed for `tmp2->__rb_parent_color == (color_bit(nc) | ((uint64)parent))`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_rotations_right_requires_sibling_child_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(sibling->rb_right, tmp1);",
        "WRITE_ONCE(sibling->rb_right, parent);",
        1,
        "`have` failed for `sid->rb_right == tmp1`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_rotations_right_requires_inner_child_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(tmp2->rb_left, sibling);",
        "WRITE_ONCE(tmp2->rb_left, parent);",
        1,
        "`have` failed for `iid->rb_left == sid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_rotations_requires_first_grandchild_parent() {
    erase_color_general_refuses_mutation(
        "rb_set_parent_color(tmp1, sibling,\n\t\t\t\t\t\t\t    RB_BLACK);",
        "rb_set_parent_color(tmp1, parent,\n\t\t\t\t\t\t\t    RB_BLACK);",
        2,
        "`have` failed for `tmp1->__rb_parent_color == (address(sibling) | 1)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_rotations_requires_first_grandchild_blackening() {
    erase_color_general_refuses_mutation(
        "rb_set_parent_color(tmp1, sibling,\n\t\t\t\t\t\t\t    RB_BLACK);",
        "rb_set_parent_color(tmp1, sibling,\n\t\t\t\t\t\t\t    RB_RED);",
        2,
        "`have` failed for `tmp1->__rb_parent_color == (address(sibling) | 1)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_rotations_requires_old_sibling_as_far_child() {
    erase_color_general_refuses_mutation(
        "tmp1 = sibling;",
        "tmp1 = parent;",
        2,
        "`have` failed for `tmp1 == sid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_rotations_requires_inner_node_as_sibling() {
    erase_color_general_refuses_mutation(
        "sibling = tmp2;",
        "sibling = parent;",
        2,
        "`have` failed for `sibling == iid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_red_exit_left_requires_parent_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(parent->rb_right, tmp1);",
        "WRITE_ONCE(parent->rb_right, NULL);",
        1,
        "`have` failed for `parent->rb_right == zid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_red_exit_left_requires_sibling_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(sibling->rb_left, parent);\n\t\t\t\trb_set_parent_color(tmp1, parent, RB_BLACK);",
        "WRITE_ONCE(sibling->rb_left, NULL);\n\t\t\t\trb_set_parent_color(tmp1, parent, RB_BLACK);",
        1,
        "`have` failed for `sid->rb_left == parent`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_red_exit_right_requires_parent_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(parent->rb_left, tmp1);",
        "WRITE_ONCE(parent->rb_left, NULL);",
        1,
        "`have` failed for `parent->rb_left == zid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_red_exit_right_requires_sibling_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(sibling->rb_right, parent);\n\t\t\t\trb_set_parent_color(tmp1, parent, RB_BLACK);",
        "WRITE_ONCE(sibling->rb_right, NULL);\n\t\t\t\trb_set_parent_color(tmp1, parent, RB_BLACK);",
        1,
        "`have` failed for `sid->rb_right == parent`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_red_exit_requires_near_parent() {
    erase_color_general_refuses_mutation(
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        2,
        "`have` failed for `tmp1->__rb_parent_color == (((uint64)parent) | 1)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_red_exit_requires_near_blackening() {
    erase_color_general_refuses_mutation(
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
        "rb_set_parent_color(tmp1, parent, RB_RED);",
        2,
        "`have` failed for `tmp1->__rb_parent_color == (((uint64)parent) | 1)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_red_exit_requires_red_parent() {
    erase_color_general_refuses_mutation(
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\t\tRB_RED);",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\t\tRB_BLACK);",
        2,
        "`have` failed for `parent->__rb_parent_color == ((uint64)sibling)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_flips_red_exit_requires_near_sibling_cursor() {
    erase_color_general_refuses_mutation(
        "sibling = tmp1;",
        "sibling = parent;",
        2,
        "`have` failed for `sibling == zid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_outer_left_requires_sibling_child_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(sibling->rb_left, parent);",
        "WRITE_ONCE(sibling->rb_left, 0);",
        2,
        "`have` failed for `sibling->rb_left == parent`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_outer_left_requires_parent_blackening() {
    erase_color_general_refuses_mutation(
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\tRB_BLACK);",
        "__rb_rotate_set_parents(parent, sibling, root,\n\t\t\t\t\t\tRB_RED);",
        2,
        "`have` failed for `parent->__rb_parent_color == (((uint64)iid) + 1)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_outer_right_requires_sibling_child_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(sibling->rb_right, parent);",
        "WRITE_ONCE(sibling->rb_right, 0);",
        2,
        "`have` failed for `sibling->rb_right == parent`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_outer_nonempty_left_requires_near_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(parent->rb_right, tmp2);",
        "WRITE_ONCE(parent->rb_right, NULL);",
        2,
        "`have` failed for `parent->rb_right == iid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_outer_nonempty_right_requires_near_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(parent->rb_left, tmp2);",
        "WRITE_ONCE(parent->rb_left, NULL);",
        2,
        "`have` failed for `parent->rb_left == iid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_inner_left_requires_detached_inner_child() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(sibling->rb_left, tmp1);",
        "WRITE_ONCE(sibling->rb_left, tmp2);",
        1,
        "`have` failed for `sid->rb_left == tmp1`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_inner_left_requires_attached_old_sibling() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(tmp2->rb_right, sibling);",
        "WRITE_ONCE(tmp2->rb_right, NULL);",
        1,
        "`have` failed for `iid->rb_right == sid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_inner_left_requires_old_sibling_parent() {
    erase_color_general_refuses_mutation(
        "rb_set_parent_color(tmp1, sibling, RB_BLACK);",
        "rb_set_parent_color(tmp1, parent, RB_BLACK);",
        2,
        "`have` failed for `tmp1->__rb_parent_color == (address(sibling) | 1)`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_inner_right_requires_detached_inner_child() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(sibling->rb_right, tmp1);",
        "WRITE_ONCE(sibling->rb_right, tmp2);",
        1,
        "`have` failed for `sid->rb_right == tmp1`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_inner_right_requires_attached_old_sibling() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(tmp2->rb_left, sibling);",
        "WRITE_ONCE(tmp2->rb_left, NULL);",
        1,
        "`have` failed for `iid->rb_left == sid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_red_sibling_left_requires_sibling_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(sibling->rb_left, parent);",
        "WRITE_ONCE(sibling->rb_left, NULL);",
        2,
        "`have` failed for `sibling->rb_left == parent`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_red_sibling_right_requires_sibling_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(sibling->rb_right, parent);",
        "WRITE_ONCE(sibling->rb_right, NULL);",
        2,
        "`have` failed for `sibling->rb_right == parent`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_red_sibling_outer_left_requires_second_parent_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(parent->rb_right, tmp2);",
        "WRITE_ONCE(parent->rb_right, sibling);",
        2,
        "`have` failed for `parent->rb_right == iid`",
    );
}

#[test]
#[ignore = "nightly: complete general erase-color proof with a mutated C input"]
fn rbtree_erase_color_general_red_sibling_outer_right_requires_second_parent_link() {
    erase_color_general_refuses_mutation(
        "WRITE_ONCE(parent->rb_left, tmp2);",
        "WRITE_ONCE(parent->rb_left, sibling);",
        2,
        "`have` failed for `parent->rb_left == iid`",
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
    let bytes = fs::read(root.join("examples/rbtree/rbtree-erase/rb_erase.c"))
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
        "rbtree_erase_leaf_wrapper.click",
        "rb_erase.c",
        "if (rebalance)",
        "if (!rebalance)",
        1,
    );
    assert!(
        error.contains("requires a call to `____rb_erase_color#inline:rb_erase.c` at the current frontier; next operation: skip"),
        "unexpected refusal: {error}"
    );
}

#[test]
fn rbtree_augmented_wrappers_keep_the_pinned_c() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    assert_eq!(
        hex_digest(sha256(
            &fs::read(root.join("examples/rbtree/rbtree-augmented/rb_insert_augmented.c")).unwrap()
        )),
        "213bdc5c780db8f91b3595d7fdc1dc94cee1b56c8d0f7a54cb5e6859ed79ef58",
    );
    assert_eq!(
        hex_digest(sha256(
            &fs::read(root.join("examples/rbtree/rbtree-augmented/rb_erase_augmented.c")).unwrap()
        )),
        "62e586fbf9b20527ee6454b9481a0ac0d6cab78dc005f5b189ec602ec63089e5",
    );
}

#[test]
#[ignore = "nightly: 13.9s in the parallel gate"]
fn rbtree_augmented_wrappers_reject_missing_or_wrong_calls() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (sidecar, input, before, after, expected) in [
        (
            "rbtree_insert_augmented.click",
            "rb_insert_augmented.c",
            "\t__rb_insert(node, root, augment_rotate);",
            "",
            "requires a call to `__rb_insert#inline:rb_insert_augmented.c` at the current frontier",
        ),
        (
            "rbtree_insert_augmented.click",
            "rb_insert_augmented.c",
            "\t__rb_insert_augmented(node, root, augment->rotate);",
            "\t__rb_insert_augmented(root->rb_node, root, augment->rotate);",
            "missing resource fact `views root->rb_node`",
        ),
        (
            "rbtree_erase_color.click",
            "rb_erase_augmented.c",
            "\t____rb_erase_color(parent, root, augment_rotate);",
            "",
            "requires a call to `____rb_erase_color#inline:rb_erase_augmented.c` at the current frontier",
        ),
        (
            "rbtree_erase_leaf.click",
            "rb_erase_augmented.c",
            "\t\t__rb_erase_color(rebalance, root, augment->rotate);",
            "\t\t;",
            "requires a call to `__rb_erase_color` at the current frontier",
        ),
    ] {
        let path = root.join("examples/rbtree/rbtree-augmented").join(sidecar);
        let source = fs::read_to_string(&path).unwrap();
        let mut inputs = read_verifying_sources(&path, &source).unwrap();
        let (_, c) = inputs
            .iter_mut()
            .find(|(name, _)| name.ends_with(input))
            .unwrap();
        assert_eq!(c.matches(before).count(), 1, "{sidecar}: unique mutation");
        *c = c.replace(before, after);
        let project = read_click_project(&path, &source).unwrap();
        let error = limits::spawn(
            "augmented wrapper mutation verifier",
            "click-augmented-wrapper-mutation".to_string(),
            move || verify_c0_project(&project, &source_refs(&inputs)),
        )
        .unwrap()
        .expect_err("the augmented wrapper must reject the changed call");
        assert!(
            error.message().contains(expected),
            "{sidecar}: {}",
            error.message()
        );
    }
}

/// Reruns a documented Click session: each fenced block with a `filename=`
/// (C, Click, JSON, a Makefile, ...) is written to a scratch directory in page
/// order, creating its parent directories, and each `console` block starting
/// with `$ click verify ARGS` or `$ click import lock ARGS` must show exactly
/// what that command prints there, stdout then stderr. Returns the last
/// version of each file.
fn run_documented_session(page: &str) -> BTreeMap<String, String> {
    run_documented_session_versions(page)
        .into_iter()
        .map(|(name, mut versions)| (name, versions.pop().unwrap()))
        .collect()
}

/// Like [`run_documented_session`], returning every version of each file the
/// page writes, in page order.
fn run_documented_session_versions(page: &str) -> BTreeMap<String, Vec<String>> {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let source = fs::read_to_string(root.join(page)).unwrap();
    let directory = std::env::temp_dir().join(format!(
        "click-documented-session-{}-{}",
        page.replace('/', "-"),
        std::process::id()
    ));
    let _ = fs::remove_dir_all(&directory);
    fs::create_dir_all(&directory).unwrap();
    let mut files: BTreeMap<String, Vec<String>> = BTreeMap::new();
    let mut sessions = 0;
    let mut lines = source.lines();
    while let Some(line) = lines.next() {
        let Some(info) = line.strip_prefix("```") else {
            continue;
        };
        let body = lines
            .by_ref()
            .take_while(|line| *line != "```")
            .map(|line| format!("{line}\n"))
            .collect::<String>();
        if let Some((_, name)) = info.split_once(" filename=") {
            assert!(
                !name.starts_with('/') && !name.split('/').any(|part| part == ".."),
                "{page}: documented file `{name}` must stay in the session directory"
            );
            let path = directory.join(name);
            fs::create_dir_all(path.parent().unwrap()).unwrap();
            fs::write(path, &body).unwrap();
            files.entry(name.to_string()).or_default().push(body);
        } else if info == "console" {
            let (command, expected) = body.split_once('\n').unwrap_or((&body, ""));
            let arguments = command
                .strip_prefix("$ click ")
                .filter(|rest| rest.starts_with("verify ") || rest.starts_with("import lock "))
                .unwrap_or_else(|| panic!("{page}: unexpected console command `{command}`"));
            let output = Command::new(env!("CARGO_BIN_EXE_click"))
                .args(arguments.split_whitespace())
                .current_dir(&directory)
                .output()
                .unwrap();
            // The scratch directory is not a Git worktree, so no incremental
            // baseline can be recorded; that warning is not part of the session.
            let stderr = String::from_utf8(output.stderr)
                .unwrap()
                .lines()
                .filter(|line| !line.contains("could not record incremental baseline"))
                .map(|line| format!("{line}\n"))
                .collect::<String>();
            let actual = format!("{}{stderr}", String::from_utf8(output.stdout).unwrap());
            assert_eq!(actual, expected, "{page}: `{command}`");
            sessions += 1;
        }
    }
    assert!(sessions > 0, "{page} documents no `click verify` session");
    fs::remove_dir_all(&directory).unwrap();
    files
}

/// The README's quick start is `examples/clamp`, and its transcript is what
/// `click verify` prints.
#[test]
fn readme_quick_start_is_the_clamp_example() {
    let files = run_documented_session("README.md");
    let example = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/clamp");
    for name in ["clamp.c", "clamp.click"] {
        assert_eq!(
            files[name],
            fs::read_to_string(example.join(name)).unwrap(),
            "README `{name}` differs from examples/clamp"
        );
    }
}

/// The own-project guide's commands print what it shows, and the files it
/// builds up are those of `examples/label-build-flags`, which the examples
/// gate verifies.
#[test]
#[ignore = "nightly: 6.7s in the parallel gate"]
fn own_project_guide_sessions_match_the_label_example() {
    let files = run_documented_session_versions("docs/concepts/own-project.md");
    let example = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("examples/label-build-flags");
    for name in [
        "Makefile",
        "include/label_config.h",
        "label.h",
        "label_fit.c",
        "label_copy.c",
        "label.click",
        "click.project.json",
    ] {
        let checked_in = fs::read_to_string(example.join(name)).unwrap();
        assert!(
            files
                .get(name)
                .is_some_and(|versions| versions.contains(&checked_in)),
            "the guide never shows examples/label-build-flags/{name} as checked in"
        );
    }
}

/// The first-proof tutorial's commands print what it shows, failure included.
#[test]
fn first_proof_tutorial_sessions_match_the_verifier() {
    let files = run_documented_session("docs/concepts/first-proof.md");
    assert!(files["increment.click"].contains("requires x < 2147483647;"));
}

/// The markdown harness uses enlarged verifier-thread stacks. Keep this
/// reproduction in the real CLI too, where main has the ordinary OS stack.
#[test]
fn uint64_successor_auto_answers_on_the_normal_cli_stack() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let output = Command::new(env!("CARGO_BIN_EXE_click"))
        .arg("verify")
        .arg(root.join("mdtests/uint64_successor_auto_with_additional_bound.md"))
        .output()
        .expect("run the verifier on its ordinary process stack");
    assert!(
        output.status.success(),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
    assert!(String::from_utf8_lossy(&output.stdout).contains("1 selected proof verified"));
}

/// Modular pointer-field outputs must keep the same proof meaning after expansion.
#[test]
#[ignore = "nightly: fresh, expanded and retained buffer output checks"]
fn c_buffer_resource_modular_output_expands_and_rechecks() {
    limits::spawn(
        "buffer output proof modes",
        "click-buffer-output-modes".into(),
        || {
            let path = Path::new("mdtests/c_buffer_resource_modular_output.md");
            let fixture = click::cli::parse_mdtest(
                path,
                include_str!("../mdtests/c_buffer_resource_modular_output.md"),
            )
            .unwrap();
            let source = fixture.click_source.as_deref().unwrap();
            let sources = source_refs(&fixture.c_sources);
            let (session, verified) =
                click::surface::C0VerificationSession::new(source, &sources).unwrap();
            assert!(!verified.is_empty());
            let mut rewrites = Vec::new();
            for name in ["init", "probe"] {
                let expanded = click::surface::expand_verified_function_claim_source_by_label(
                    source,
                    &verified,
                    &format!("{name}.contract"),
                )
                .expect("the complete buffer output claim must expand")
                .expect("the original verification contains the buffer output claim");
                let needle = format!("void {name}(");
                let declaration = expanded.find(&needle).unwrap();
                let offset = declaration + expanded[declaration..].find("ensures").unwrap();
                let line = expanded[..offset]
                    .bytes()
                    .filter(|byte| *byte == b'\n')
                    .count()
                    + 1;
                let column = expanded[..offset].rsplit('\n').next().unwrap().len() + 1;
                rewrites.push((expanded, line, column));
            }
            for (expanded, line, column) in &rewrites {
                session
                    .verify_at(expanded, *line, *column)
                    .expect("the expanded buffer output must check in its retained session");
            }
            // Generate and retain every rewrite before any cold check resets
            // the thread-local kernel tables.
            drop(session);
            for (expanded, _, _) in rewrites {
                verify_c0_sources(&expanded, &sources)
                    .expect("the written buffer output certificate must check fresh");
            }
        },
    )
    .unwrap();
}

#[test]
#[ignore = "nightly: CLI expansion and audit of a value-parameter refinement"]
fn expanded_value_parameter_refinement_resolves_and_audits() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let path = root.join("mdtests/named_contract_value_parameter_refinement_theorem.md");
    for operation in ["expand", "audit"] {
        let output = Command::new(env!("CARGO_BIN_EXE_click"))
            .args([operation, "--claim", "add3_adds_three.ensures_0"])
            .arg(&path)
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{operation}: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let original = fs::read_to_string(&path).unwrap();
    let incorrect = original.replace("amount: 3", "amount: 4");
    assert_ne!(original, incorrect);
    let changed =
        std::env::temp_dir().join(format!("click-false-refinement-{}.md", std::process::id()));
    fs::write(&changed, incorrect).unwrap();
    let output = Command::new(env!("CARGO_BIN_EXE_click"))
        .args(["expand", "--claim", "add3_adds_three.ensures_0"])
        .arg(&changed)
        .output()
        .unwrap();
    fs::remove_file(changed).unwrap();
    assert!(
        !output.status.success(),
        "a different contract value must fail"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr)
            .contains("contract-refinement proof does not establish"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

#[test]
#[ignore = "nightly: pointer guards and comparison results across complete expansion audits"]
fn pointer_comparison_certificates_expand_and_audit_without_origin_authority() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for fixture in [
        "address_equality_keeps_its_value_meaning.md",
        "model_identity_pointer_payload.md",
    ] {
        let output = Command::new(env!("CARGO_BIN_EXE_click"))
            .arg("audit")
            .arg(root.join("mdtests").join(fixture))
            .output()
            .unwrap();
        assert!(
            output.status.success(),
            "{fixture}: {}\n{}",
            String::from_utf8_lossy(&output.stdout),
            String::from_utf8_lossy(&output.stderr)
        );
    }
    let output = Command::new(env!("CARGO_BIN_EXE_click"))
        .arg("verify")
        .arg(root.join("mdtests/address_equality_does_not_grant_access_to_a_one_past_pointer.md"))
        .output()
        .unwrap();
    assert!(
        !output.status.success(),
        "address equality must not grant access"
    );
    assert!(
        String::from_utf8_lossy(&output.stderr).contains("missing resource fact"),
        "{}",
        String::from_utf8_lossy(&output.stderr)
    );
}

/// Keep both reported library-path failures on the real expansion/audit path.
#[test]
#[ignore = "nightly: CLI expansion and audit of library-name regressions"]
fn expanded_library_names_resolve_and_audit() {
    let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    for (fixture, claim) in [
        (
            "memcmp_const_unsigned_char_arguments.md",
            "compare4.contract",
        ),
        (
            "qualified_library_names.md",
            "append_nil_by_paths.ensures_0",
        ),
    ] {
        let path = root.join("mdtests").join(fixture);
        let expanded = Command::new(env!("CARGO_BIN_EXE_click"))
            .args(["expand", "--claim", claim])
            .arg(&path)
            .output()
            .unwrap();
        assert!(
            expanded.status.success(),
            "{fixture}: {}",
            String::from_utf8_lossy(&expanded.stderr)
        );
        let source = String::from_utf8(expanded.stdout).unwrap();
        // A premise-free application retains an explicit empty premise list
        // in its certificate. The full path must still resolve on recheck;
        // dropping that list could turn a different application into search.
        if fixture == "qualified_library_names.md" {
            assert!(
                source.contains("apply(click::list::append_left_identity(xs)) using {"),
                "{source}"
            );
        }
        let rewritten = std::env::temp_dir().join(format!(
            "click-expanded-library-{}-{fixture}",
            std::process::id()
        ));
        fs::write(&rewritten, &source).unwrap();
        let verified = Command::new(env!("CARGO_BIN_EXE_click"))
            .arg("verify")
            .arg(&rewritten)
            .output()
            .unwrap();
        fs::remove_file(&rewritten).unwrap();
        assert!(
            verified.status.success(),
            "{fixture}: {}",
            String::from_utf8_lossy(&verified.stderr)
        );
        // Premise-free applications are already simple, so audit the entire
        // fixture: they need no rewrite while any remaining automation does.
        let audited = Command::new(env!("CARGO_BIN_EXE_click"))
            .arg("audit")
            .arg(&path)
            .output()
            .unwrap();
        assert!(
            audited.status.success(),
            "{fixture}: {}\n{}",
            String::from_utf8_lossy(&audited.stdout),
            String::from_utf8_lossy(&audited.stderr)
        );
    }
}

/// The grow call's old-prefix fact cannot be framed across push's writable
/// buffer. Use push's exact call-exit guarantee and frame each side separately.
#[test]
#[ignore = "nightly: original grow-then-push proof across all proof modes"]
fn owned_vector_grow_then_push_prefix_rechecks_in_all_proof_modes() {
    limits::spawn(
        "vector grow-then-push proof modes",
        "click-vector-prefix-modes".into(),
        || {
            let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
            let path = root.join("examples/owned-vector/vector.click");
            let source = fs::read_to_string(&path).unwrap();
            let c_sources = read_verifying_sources(&path, &source).unwrap();
            let sources = source_refs(&c_sources);
            let expanded = click::surface::expand_c0_claim_source(
                &source,
                &sources,
                "allocated_vector_push",
                click::surface::CProofClaim::Grouped,
            )
            .expect("the complete grow-then-push claim must expand");
            let declaration = expanded.find("int32 allocated_vector_push(").unwrap();
            let offset = declaration + expanded[declaration..].find("ensures").unwrap();
            let line = expanded[..offset].bytes().filter(|b| *b == b'\n').count() + 1;
            let column = expanded[..offset].rsplit('\n').next().unwrap().len() + 1;
            verify_c0_sources_at(&expanded, &sources, line, column)
                .expect("the expanded grow-then-push claim must check fresh");
            // Session construction cold-verifies the complete original source.
            let (session, verified) =
                click::surface::C0VerificationSession::new(&source, &sources).unwrap();
            assert!(!verified.is_empty());
            session
                .verify_at(&expanded, line, column)
                .expect("the expanded grow-then-push claim must check retained");
        },
    )
    .unwrap();
}

/// The branch summary must retain the setter's result and actual write authority.
#[test]
#[ignore = "nightly: pointer-field call branch rejection controls"]
fn pointer_field_call_branch_rejects_wrong_result_and_missing_backing_authority() {
    limits::spawn(
        "pointer-field branch rejection controls",
        "click-pointer-field-branch-negative".into(),
        || {
            let path = Path::new("mdtests/c_pointer_field_preserving_calls_join_branches.md");
            let fixture = click::cli::parse_mdtest(
                path,
                include_str!("../mdtests/c_pointer_field_preserving_calls_join_branches.md"),
            )
            .unwrap();
            let source = fixture.click_source.unwrap();
            let c_sources = fixture.c_sources;
            let original_c = &c_sources[0].1;
            let wrong = original_c.replace("data[index] = value;", "data[index] = 0;");
            assert_ne!(wrong, *original_c);
            assert!(verify_c0_sources(&source, &[("vector.c", wrong.as_str())]).is_err());
            let ownership = "    owns owner->data[0..owner->cap];\n";
            assert_eq!(source.matches(ownership).count(), 1);
            let missing = source.replace(ownership, "");
            assert!(verify_c0_sources(&missing, &source_refs(&c_sources)).is_err());
        },
    )
    .unwrap();
}

/// A borrowed quantified fact must survive an unrelated write in every proof mode.
#[test]
#[ignore = "nightly: borrowed-composite expansion, retained checks, and rejection mutations"]
fn borrowed_composite_fact_after_write_expands_and_rechecks() {
    limits::spawn(
        "borrowed composite after a write",
        "click-borrowed-composite-after-write".into(),
        || {
            let path = Path::new(
                "mdtests/a_borrowed_composite_quantified_fact_opens_after_an_unrelated_write.md",
            );
            let fixture = click::cli::parse_mdtest(
                path,
                include_str!(
                    "../mdtests/a_borrowed_composite_quantified_fact_opens_after_an_unrelated_write.md"
                ),
            )
            .unwrap();
            let source = fixture.click_source.as_deref().unwrap();
            let sources = source_refs(&fixture.c_sources);
            verify_c0_sources(source, &sources).unwrap();
            let expanded = click::surface::expand_c0_claim_source(
                source,
                &sources,
                "first",
                click::surface::CProofClaim::Grouped,
            )
            .expect("opening the borrowed fact after a write must expand");
            verify_c0_sources(&expanded, &sources)
                .expect("the expanded borrowed fact must check fresh");
            let offset = expanded.find("ensures result != 0;").unwrap();
            let line = expanded[..offset].bytes().filter(|byte| *byte == b'\n').count() + 1;
            let column = expanded[..offset].rsplit('\n').next().unwrap().len() + 1;
            let (session, _) = click::surface::C0VerificationSession::new(source, &sources).unwrap();
            session
                .verify_at(&expanded, line, column)
                .expect("the expanded borrowed fact must check retained");
            drop(session);

            for (before, after) in [
                ("ensures result != 0;", "ensures result == 0;"),
                ("owns q[0..1];", ""),
                (
                    "fact forall (k: int32) { 0 <= k and k < n implies p[k] != 0 };",
                    "",
                ),
            ] {
                assert_eq!(source.matches(before).count(), 1);
                let changed = source.replace(before, after);
                assert!(verify_c0_sources(&changed, &sources).is_err(), "{before}");
            }
            let original = &fixture.c_sources[0].1;
            let borrowed_write = original.replace("q[0] = 1;", "p[0] = 0;");
            assert_ne!(borrowed_write, *original);
            assert!(verify_c0_sources(source, &[("probe.c", &borrowed_write)]).is_err());
        },
    )
    .unwrap();
}

#[test]
#[ignore = "nightly: population predicate audit and rejection controls"]
fn produced_population_predicate_expands_and_retains_its_return_state() {
    let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
        .join("mdtests/produced_population_count_in_ensured_predicate.md");
    let output = Command::new(env!("CARGO_BIN_EXE_click"))
        .arg("audit")
        .arg(&path)
        .output()
        .unwrap();
    assert!(
        output.status.success(),
        "{}\n{}",
        String::from_utf8_lossy(&output.stdout),
        String::from_utf8_lossy(&output.stderr)
    );
    limits::spawn(
        "population predicate rejection controls",
        "click-population-predicate-negative".into(),
        move || {
            let fixture = click::cli::read_mdtest(&path).unwrap();
            let source = fixture.click_source.unwrap();
            let sources = fixture.c_sources;
            for (before, after) in [
                (
                    "produces amount of slot(owner);",
                    "produces 1 of slot(owner);",
                ),
                ("requires count(slot(owner)) == 0;", ""),
                ("owns authority(slot(owner));", ""),
            ] {
                let invalid = source.replace(before, after);
                assert_ne!(invalid, source);
                assert!(
                    verify_c0_sources(&invalid, &source_refs(&sources)).is_err(),
                    "accepted {before} -> {after}"
                );
            }
            let wrong_capacity = sources
                .iter()
                .map(|(name, body)| {
                    (
                        name.clone(),
                        body.replace("owner->capacity = amount;", "owner->capacity = 0;"),
                    )
                })
                .collect::<Vec<_>>();
            assert_ne!(wrong_capacity, sources);
            assert!(verify_c0_sources(&source, &source_refs(&wrong_capacity)).is_err());
        },
    )
    .unwrap();
}
