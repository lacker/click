use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use click::cli::{
    DISABLE_TACTIC_BUDGETS, MdTestExpectation, default_worker_count, duration_from_env,
    format_duration, read_mdtest, run_parallel, structured_tactic_budget_violations,
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
        "c_null_pointer_conversion.md",
        "null call certificate does not replay; see issues/smart-certificate-replay-consistency.md",
    ),
    (
        "conditional_resource_branchless_free.md",
        "null opaque-call footprint type mismatch; see issues/conditional-null-free-call-footprint.md",
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
    let failures = run_parallel(&paths, default_worker_count(paths.len()), |path| {
        run_mdtest_with_timeout(path, time_limit)
    });
    let failures = click::cli::retain_serial_budget_failures(failures, |index| {
        run_mdtest_with_timeout(&paths[index], time_limit)
    });
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
    std::thread::Builder::new()
        .name("click-mdtest".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let started = std::time::Instant::now();
            let (result, events) = instrumentation::with_deadline(time_limit, || {
                instrumentation::collect(|| run_mdtest(&path))
            });
            result?;
            let elapsed = started.elapsed();
            if elapsed > time_limit {
                return Err(format!(
                    "exceeded the per-file mdtest time limit of {}; set {MDTEST_TIME_LIMIT} to override it",
                    format_duration(time_limit)
                ));
            }
            if std::env::var_os(DISABLE_TACTIC_BUDGETS).is_none() {
                let violations = structured_tactic_budget_violations(&events);
                if !violations.is_empty() {
                    return Err(format!(
                        "passed, but broke tactic time budgets (set {DISABLE_TACTIC_BUDGETS}=1 to bypass):\n  {}",
                        violations.join("\n  ")
                    ));
                }
            }
            Ok(())
        })
        .map_err(|error| format!("failed to start mdtest verifier: {error}"))?
        .join()
        .map_err(|_| "mdtest verifier panicked".to_string())?
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
