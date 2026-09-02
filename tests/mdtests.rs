use std::fs;
use std::path::{Path, PathBuf};

use click::cli::{MdTestExpectation, read_mdtest, run_parallel};
use click::instrumentation::{self, ContractFallback, SealRefusal};
use click::surface::verify_c0_sources;

const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
const BUBBLE_SORT3_WORK_LIMIT: usize = 100_000;

/// Known-broken mdtests, skipped by default so the suite is a meaningful
/// green gate. Run one with `MDTEST_FILTER=<name>`, or all of them with
/// `CLICK_RUN_QUARANTINED=1`. Each entry names the reason; remove entries as
/// they are fixed (see docs/internals/testing.md).
const QUARANTINED: &[(&str, &str)] = &[];

/// The body-rerun ratchet (`issues/double-execution.md`): how many times, over
/// the whole unfiltered corpus, claim finishing or contract certification
/// executed a function body because the sealer refused or a guard declined,
/// by reason. A count may only fall; lower its pin when it does.
const SEAL_REFUSAL_BASELINE: &[(SealRefusal, usize)] = &[];
const CONTRACT_FALLBACK_BASELINE: &[(ContractFallback, usize)] = &[
    (ContractFallback::UnauthorizedPredicatePremise, 19),
    (ContractFallback::UnauthorizedResourcePremise, 13),
    (ContractFallback::EntryStateDelta, 7),
];

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
        .filter(|path| path.extension().is_some_and(|extension| extension == "md"))
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
    paths.sort();

    assert!(
        !paths.is_empty(),
        "expected at least one mdtest in `{}`",
        mdtests_dir.display()
    );

    // Keep file verification serial to bound peak memory. Tactic correctness
    // is enforced by deterministic work budgets, not by how much CPU time
    // happens to be available to this fixture process.
    let _ = instrumentation::take_body_rerun_census();
    let failures = run_parallel(&paths, 1, |path| run_mdtest_in_thread(path));
    let census = instrumentation::take_body_rerun_census();
    if failures.is_empty() {
        if !filtered
            && std::env::var_os(RUN_QUARANTINED).is_none()
            && let Some(mismatch) = instrumentation::body_rerun_census_mismatch(
                &census,
                SEAL_REFUSAL_BASELINE,
                CONTRACT_FALLBACK_BASELINE,
            )
        {
            panic!("body rerun ratchet (tests/mdtests.rs baselines):\n{mismatch}");
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
    std::thread::Builder::new()
        .name(thread_name)
        .stack_size(64 * 1024 * 1024)
        .spawn(move || run_mdtest_attempt(&path))
        .map_err(|error| format!("failed to start mdtest verifier: {error}"))?
        .join()
        .map_err(|_| "mdtest verifier panicked".to_string())?
}

fn run_mdtest_attempt(path: &Path) -> Result<(), String> {
    instrumentation::without_tactic_time_limits(|| {
        if path
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
        run_mdtest(path)
    })
}

fn run_mdtest(path: &Path) -> Result<(), String> {
    let mdtest = read_mdtest(path)?;
    let click_source = mdtest
        .click_source
        .as_deref()
        .ok_or_else(|| format!("`{}` is missing a ```click block", path.display()))?;
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(filename, source)| (filename.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expectation = mdtest
        .expectation
        .as_ref()
        .ok_or_else(|| format!("`{}` is missing a ```expect block", path.display()))?;

    let result = verify_c0_sources(click_source, &c_sources);
    match (expectation, result) {
        (MdTestExpectation::Pass, Ok(_)) => {}
        (MdTestExpectation::Pass, Err(error)) => {
            return Err(format!(
                "`{}` expected pass, but failed: {}",
                path.display(),
                error.message()
            ));
        }
        (MdTestExpectation::FailContains(expected), Ok(_)) => {
            return Err(format!(
                "`{}` expected failure containing `{expected}`, but passed",
                path.display()
            ));
        }
        (MdTestExpectation::FailContains(expected), Err(error)) => {
            if !error.message().contains(expected) {
                return Err(format!(
                    "`{}` expected failure containing `{expected}`, got `{}`",
                    path.display(),
                    error.message()
                ));
            }
        }
    }
    Ok(())
}
