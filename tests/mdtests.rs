use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use click::cli::{
    DISABLE_TACTIC_BUDGETS, MdTestExpectation, duration_from_env, format_duration, read_mdtest,
    run_parallel,
};
use click::instrumentation;
use click::lang::click::verify_c0_sources;

const MDTEST_TIME_LIMIT: &str = "MDTEST_TIME_LIMIT";
const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
const DEFAULT_MDTEST_TIME_LIMIT: Duration = Duration::from_secs(30);

/// Known-broken mdtests, skipped by default so the suite is a meaningful
/// green gate. Run one with `MDTEST_FILTER=<name>`, or all of them with
/// `CLICK_RUN_QUARANTINED=1`. Each entry names the reason; remove entries as
/// they are fixed (see docs/advanced/testing-click.md).
const QUARANTINED: &[(&str, &str)] = &[
    (
        "bubble_pass3_max_suffix.md",
        "issues/binary-tree-grouped-simp-transition-not-expressible.md: expressible path facts do not replay the grouped transition's postcondition derivation",
    ),
    (
        "bubble_sort3_two_pass_sorted.md",
        "issues/universal-outcome-certificates-missing.md: no simple certificate for a universal proposition over CInt32",
    ),
    (
        "byte_slice_stdlib.md",
        "issues/byte-slice-indexed-range-premise-certificate-missing.md: indexed-range premise derivation has no explicit simple certificate",
    ),
    (
        "composite_resource_vector_fill_loop_snapshot.md",
        "issues/universal-outcome-certificates-missing.md: no simple certificate for a universal proposition over CInt32",
    ),
    (
        "copy3_array_demo.md",
        "issues/universal-outcome-certificates-missing.md: no simple certificate for a universal proposition over CInt32",
    ),
    (
        "fill3_array_loop.md",
        "issues/universal-outcome-certificates-missing.md: single-cell loop-effect consequence has no explicit simple certificate",
    ),
    (
        "fill_tail_rejects_tail_segment_unchanged.md",
        "issues/universal-outcome-certificates-missing.md: certificate-lowering error masks the intended semantic rejection diagnostic",
    ),
    (
        "fill_n_segment_invariant.md",
        "issues/universal-outcome-certificates-missing.md: filled-segment universal goal has no explicit simple certificate",
    ),
    (
        "proof_branch_pointer_local.md",
        "issues/branch-disjunctive-premise-certificate-missing.md: disjunctive premise derivation has no explicit simple certificate",
    ),
    (
        "proof_if_cases.md",
        "issues/owned-string-pure-theorem-certificate-missing.md: pure smart proof produces no pure surface certificate",
    ),
    (
        "shifted_copy_effect_uses_covering_separate.md",
        "issues/universal-outcome-certificates-missing.md: preserved-source universal goal has no explicit simple certificate",
    ),
    (
        "shifted_loop_effect_preserves_prefix.md",
        "issues/universal-outcome-certificates-missing.md: preserved-prefix loop-effect consequence has no explicit simple certificate",
    ),
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

    let time_limit = mdtest_time_limit();
    // Keep file verification serial to bound peak memory. Tactic correctness
    // is enforced by deterministic work budgets, not by how much CPU time
    // happens to be available to this fixture process.
    let failures = run_parallel(&paths, 1, |path| run_mdtest_with_timeout(path, time_limit));
    if failures.is_empty() {
        return;
    }

    let mut message = format!("{} of {} mdtests failed:\n", failures.len(), paths.len());
    for (index, diagnostics) in failures {
        message.push_str(&format!("\n`{}` {diagnostics}\n", paths[index].display()));
    }
    panic!("{message}");
}

fn mdtest_time_limit() -> Duration {
    duration_from_env(MDTEST_TIME_LIMIT, DEFAULT_MDTEST_TIME_LIMIT)
        .unwrap_or_else(|message| panic!("{message}"))
}

fn run_mdtest_with_timeout(path: &Path, time_limit: Duration) -> Result<(), String> {
    let path = path.to_path_buf();
    let thread_name = path.file_stem().and_then(|name| name.to_str()).map_or_else(
        || "click-mdtest".to_string(),
        |name| format!("mdtest-{name}"),
    );
    std::thread::Builder::new()
        .name(thread_name)
        .stack_size(64 * 1024 * 1024)
        .spawn(move || run_mdtest_attempt(&path, time_limit))
        .map_err(|error| format!("failed to start mdtest verifier: {error}"))?
        .join()
        .map_err(|_| "mdtest verifier panicked".to_string())?
}

fn run_mdtest_attempt(path: &Path, time_limit: Duration) -> Result<(), String> {
    let started = std::time::Instant::now();
    let operation = || run_mdtest(path);
    let result = if std::env::var_os(DISABLE_TACTIC_BUDGETS).is_some() {
        instrumentation::with_deadline(time_limit, operation)
    } else {
        let fixture_limits = instrumentation::TacticLimits {
            simple: time_limit,
            smart: time_limit,
            control: time_limit,
        };
        instrumentation::with_deadline(time_limit, || {
            instrumentation::with_tactic_limits(fixture_limits, operation)
        })
    };
    result?;
    if started.elapsed() > time_limit {
        return Err(format!(
            "exceeded the per-file mdtest time limit of {}; set {MDTEST_TIME_LIMIT} to override it",
            format_duration(time_limit)
        ));
    }
    Ok(())
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
