use click::surface::ProgramInputs;
use std::fs;
use std::path::{Path, PathBuf};

use click::cli::{
    CInput, MdTestExpectation, prepare_mdtest_inputs, read_click_project, read_mdtest,
    read_mdtest_project_if_needed, source_refs,
};
use click::instrumentation::{self, ArtifactReuseRejection};
use click::surface::{
    c0_tactic_source_position, project_tactic_source_position, verify_c0_project,
    verify_c0_sources, verify_program_prepared_project,
};

#[path = "support/limits.rs"]
mod limits;
#[path = "support/tactic_work.rs"]
mod tactic_work;

const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
/// Set by the gate when the pinned C++ exporter is not installed.
const SKIP_CPP_FRONTEND: &str = "CLICK_SKIP_CPP_FRONTEND";
const BUBBLE_SORT3_WORK_LIMIT: usize = 100_000;
/// The explicit frame refusal takes about 175,000 units with scoped failure
/// reuse, versus 513,000 when its proof routes repeat the same questions.
const PROMPT_EXPLICIT_FRAME_FAILURE_WORK_LIMIT: usize = 250_000;

/// Known-broken mdtests, skipped by default so the suite is a meaningful
/// green gate. Run one with `MDTEST_FILTER=<name>`, or all of them with
/// `CLICK_RUN_QUARANTINED=1`. Each entry names the reason; remove entries as
/// they are fixed (see docs/internals/testing.md).
const QUARANTINED: &[(&str, &str)] = &[];

/// The artifact reuse rejection ratchet (`docs/internals/testing.md`): count
/// contract certification rejections of checked execution artifacts over the
/// whole unfiltered corpus, by reason. A count may only fall; lower its pin
/// when it does.
const ARTIFACT_REUSE_REJECTION_BASELINE: &[(ArtifactReuseRejection, usize)] = &[];

#[test]
fn mdtests() {
    let manifest_dir = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
    let mdtests_dir = manifest_dir.join("mdtests");
    let mut paths = fs::read_dir(&mdtests_dir)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", mdtests_dir.display()))
        .map(|entry| {
            entry
                .unwrap_or_else(|error| panic!("failed to read mdtest directory entry: {error}"))
                .path()
        })
        // Imported theorem bodies are interfaces to their importers. Run each
        // local Click library as its own entry so the gate checks those bodies.
        .filter(|path| {
            path.extension()
                .is_some_and(|extension| extension == "md" || extension == "click")
        })
        .collect::<Vec<_>>();
    let filtered = if let Ok(filter) = std::env::var("MDTEST_FILTER") {
        paths.retain(|path| {
            path.file_name()
                .is_some_and(|name| name.to_string_lossy().contains(&filter))
        });
        true
    } else {
        false
    };
    if !filtered && std::env::var_os(RUN_QUARANTINED).is_none() {
        paths.retain(|path| {
            let name = path.file_name().and_then(|name| name.to_str());
            let quarantine = name.and_then(|name| {
                QUARANTINED
                    .iter()
                    .find(|(quarantined, _)| *quarantined == name)
            });
            match quarantine {
                Some((name, reason)) => {
                    println!("SKIPPING quarantined mdtest `{name}`: {reason}");
                    false
                }
                None => true,
            }
        });
    }
    // A gate run on a machine without the pinned C++ toolchain
    // (`scripts/check.sh`) leaves out the mdtests that need its exporter.
    let skipped_cpp = std::env::var_os(SKIP_CPP_FRONTEND).is_some() && {
        let before = paths.len();
        paths.retain(|path| {
            let cpp = path.extension().is_some_and(|extension| extension == "md")
                && read_mdtest(path).is_ok_and(|mdtest| mdtest.cpp_source.is_some());
            if cpp {
                println!(
                    "SKIPPING C++ mdtest `{}`: {SKIP_CPP_FRONTEND} is set",
                    path.display()
                );
            }
            !cpp
        });
        paths.len() != before
    };
    let filtered = filtered || skipped_cpp;
    paths.sort();
    // CI splits the corpus across jobs to stay inside the gate's time
    // budget: `MDTEST_PARTITION=k/n` keeps every n-th file from the k-th,
    // over the sorted names, so the shards cover the corpus exactly once.
    let partitioned = if let Ok(partition) = std::env::var("MDTEST_PARTITION") {
        let (shard, total) = partition
            .split_once('/')
            .and_then(|(shard, total)| {
                Some((shard.parse::<usize>().ok()?, total.parse::<usize>().ok()?))
            })
            .filter(|(shard, total)| (1..=*total).contains(shard))
            .unwrap_or_else(|| {
                panic!("MDTEST_PARTITION must be `k/n` with 1 <= k <= n, got `{partition}`")
            });
        let mut index = 0;
        paths.retain(|_| {
            index += 1;
            (index - 1) % total == shard - 1
        });
        true
    } else {
        false
    };
    let filtered = filtered || partitioned;

    assert!(
        !paths.is_empty(),
        "expected at least one mdtest in `{}`",
        mdtests_dir.display()
    );

    // Verify files on every core. Tactic correctness is enforced by
    // deterministic work budgets, not by how much CPU time happens to be
    // available to each file, so concurrency cannot change a verdict. Peak
    // memory stays small: on 2026-09-11 the whole corpus peaked at 171 MB
    // serially and 291 MB on 8 workers.
    let _ = instrumentation::take_artifact_reuse_rejection_census();
    let _ = instrumentation::take_backwards_memory_derivation_census();
    let workers = std::thread::available_parallelism().map_or(1, usize::from);
    let failures = limits::run_parallel(&paths, workers, |path| run_mdtest_in_thread(path));
    let census = instrumentation::take_artifact_reuse_rejection_census();
    // Which producers still end a step on a snapshot older than itself, so
    // that the step is recorded on no history. A knowledge-losing forget
    // cannot: its mark makes the result a node no earlier snapshot can be
    // (`CMemory::mark_forgotten_from`). Anything else here is a producer
    // whose steps are invisible to every history-based rule, and this line
    // is how a corpus run names it.
    eprintln!(
        "backwards memory derivations over the corpus: {:?}",
        instrumentation::take_backwards_memory_derivation_census()
    );
    if failures.is_empty() {
        if !filtered
            && std::env::var_os(RUN_QUARANTINED).is_none()
            && let Some(mismatch) = instrumentation::artifact_reuse_rejection_census_mismatch(
                &census,
                ARTIFACT_REUSE_REJECTION_BASELINE,
            )
        {
            panic!("artifact reuse rejection ratchet (tests/mdtests.rs baselines):\n{mismatch}");
        }
        return;
    }

    let mut message = format!("{} of {} mdtests failed:\n", failures.len(), paths.len());
    for (index, diagnostics) in failures {
        message.push_str(&format!("\n`{}` {diagnostics}\n", paths[index].display()));
    }
    panic!("{message}");
}

fn run_mdtest_in_thread(path: &Path) -> Result<(), String> {
    let path = path.to_path_buf();
    let thread_name = path.file_stem().and_then(|name| name.to_str()).map_or_else(
        || "click-mdtest".to_string(),
        |name| format!("mdtest-{name}"),
    );
    // One line as each fixture starts and one as it finishes, on stderr so
    // the gate can stream them: a stall shows as a started fixture that
    // never finishes, and a slow fixture is visible while it runs, not only
    // in the total afterwards.
    let name = path.display().to_string();
    eprintln!("mdtest `{name}` started");
    let started = std::time::Instant::now();
    let result = limits::spawn("mdtest verifier", thread_name, move || {
        run_mdtest_attempt(&path)
    })?;
    eprintln!(
        "mdtest `{name}` {} in {:.2}s",
        if result.is_ok() { "passed" } else { "failed" },
        started.elapsed().as_secs_f64()
    );
    result
}

fn run_mdtest_attempt(path: &Path) -> Result<(), String> {
    // A calibration run measures every fixture unclipped, so the pinned
    // budgets below step aside with the defaults.
    let budgets_disabled = std::env::var_os("CLICK_DISABLE_TACTIC_BUDGETS").is_some();
    if !budgets_disabled
        && path
            .file_name()
            .is_some_and(|name| name == "bubble_sort3_loop_permutation.md")
    {
        // This is the former load-sensitive clock canary. Its measured
        // maxima are simple 146, smart 21,090, and control 42,169 work
        // units. Pin all three classes below 100,000 so machine load
        // cannot change the result.
        let limits = instrumentation::TacticWorkLimits {
            simple: BUBBLE_SORT3_WORK_LIMIT,
            smart: BUBBLE_SORT3_WORK_LIMIT,
            control: BUBBLE_SORT3_WORK_LIMIT,
        };
        return instrumentation::with_tactic_work_limits(limits, || run_mdtest(path));
    }
    if !budgets_disabled
        && path
            .file_name()
            .is_some_and(|name| name == "explicit_transport_failure_is_prompt.md")
    {
        return instrumentation::with_tactic_work_limits(
            instrumentation::TacticWorkLimits {
                simple: PROMPT_EXPLICIT_FRAME_FAILURE_WORK_LIMIT,
                control: PROMPT_EXPLICIT_FRAME_FAILURE_WORK_LIMIT,
                ..instrumentation::TacticWorkLimits::default()
            },
            || run_mdtest(path),
        );
    }
    if !budgets_disabled
        && path
            .file_name()
            .is_some_and(|name| name == "simp_false_list_position_is_prompt.md")
    {
        return instrumentation::with_tactic_work_limits(
            instrumentation::TacticWorkLimits {
                smart: 100_000,
                ..instrumentation::TacticWorkLimits::default()
            },
            || run_mdtest(path),
        );
    }
    run_mdtest(path)
}

fn run_mdtest(path: &Path) -> Result<(), String> {
    if path
        .extension()
        .is_some_and(|extension| extension == "click")
    {
        let source = fs::read_to_string(path)
            .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
        let project = read_click_project(path, &source)?;
        return verify_c0_project(&project, &[])
            .map(|_| ())
            .map_err(|error| error.report());
    }
    let mdtest = read_mdtest(path)?;
    let click_source = mdtest
        .click_source
        .as_deref()
        .ok_or_else(|| format!("`{}` is missing a ```click block", path.display()))?;
    let inputs = prepare_mdtest_inputs(&mdtest)?;
    let expectation = mdtest
        .expectation
        .as_ref()
        .ok_or_else(|| format!("`{}` is missing a ```expect block", path.display()))?;

    let project = read_mdtest_project_if_needed(path, click_source, &inputs)?;
    let verify = || -> Result<(), (String, String)> {
        match (&inputs, &project) {
            (CInput::Bundle(sources), Some(project)) => {
                verify_c0_project(project, &source_refs(sources)).map(|_| ())
            }
            (CInput::Bundle(sources), None) => {
                verify_c0_sources(click_source, &source_refs(sources)).map(|_| ())
            }
            (CInput::PreparedProgram(import), Some(project)) => {
                verify_program_prepared_project(project, import).map(|_| ())
            }
            (CInput::PreparedProgram(_), None) | (CInput::Prepared(_), _) => {
                unreachable!("every prepared mdtest input reads a Click project")
            }
        }
        .map_err(|error| (error.message().to_string(), error.report()))
    };

    let (result, samples) = tactic_work::measure(verify);
    if !samples.is_empty() {
        let line_offset = mdtest.click_start_line.saturating_sub(1);
        let relative = path
            .strip_prefix(env!("CARGO_MANIFEST_DIR"))
            .unwrap_or(path);
        tactic_work::write(
            "mdtests",
            &relative.display().to_string(),
            relative,
            &samples,
            |claim, source_index| {
                let position = match (&inputs, &project) {
                    (CInput::Bundle(sources), Some(project)) => project_tactic_source_position(
                        project,
                        &ProgramInputs::Bundle(source_refs(sources)),
                        claim,
                        source_index,
                    ),
                    (CInput::Bundle(sources), None) => c0_tactic_source_position(
                        click_source,
                        &source_refs(sources),
                        claim,
                        source_index,
                    ),
                    (CInput::PreparedProgram(import), Some(project)) => {
                        project_tactic_source_position(
                            project,
                            &ProgramInputs::program(import),
                            claim,
                            source_index,
                        )
                    }
                    _ => return None,
                };
                position
                    .ok()
                    .map(|position| (position.line + line_offset, position.column))
            },
        );
    }
    check_expectation(path, expectation, result)
}

fn check_expectation(
    path: &Path,
    expectation: &MdTestExpectation,
    result: Result<(), (String, String)>,
) -> Result<(), String> {
    match (expectation, result) {
        (MdTestExpectation::Pass, Ok(())) => Ok(()),
        (MdTestExpectation::Pass, Err((_, report))) => Err(format!(
            "`{}` expected pass, but failed: {report}",
            path.display()
        )),
        (MdTestExpectation::FailContains(expected), Ok(())) => Err(format!(
            "`{}` expected failure containing `{expected}`, but passed",
            path.display()
        )),
        (MdTestExpectation::FailContains(expected), Err((message, report))) => {
            if let Some(internal) = ["CMemory {", "CHeapMemory {", "pointer(pointer "]
                .into_iter()
                .find(|internal| report.contains(internal))
            {
                return Err(format!(
                    "`{}` leaked `{internal}` in its proof report: {report}",
                    path.display()
                ));
            }
            if message.contains(expected) {
                Ok(())
            } else {
                Err(format!(
                    "`{}` expected failure containing `{expected}`, got `{message}`",
                    path.display()
                ))
            }
        }
    }
}
