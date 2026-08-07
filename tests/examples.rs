use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use click::cli::{
    DISABLE_TACTIC_BUDGETS, duration_from_env, files_with_extension, format_duration,
    read_verifying_sources, run_parallel, source_refs, structured_tactic_budget_violations,
};
use click::instrumentation;
use click::lang::click::verify_c0_sources;

const EXAMPLE_TIME_LIMIT: &str = "CLICK_EXAMPLE_TIME_LIMIT";
const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
const DEFAULT_EXAMPLE_TIME_LIMIT: Duration = Duration::from_secs(10 * 60);

/// Known-broken or pathologically slow projects, skipped by default so the
/// suite is a meaningful green gate. Run one with `CLICK_EXAMPLE=<name>`, or
/// all of them with `CLICK_RUN_QUARANTINED=1`. Each entry names the reason;
/// remove entries as they are fixed (see docs/advanced/testing-click.md).
const QUARANTINED: &[(&str, &str)] = &[];

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

    let time_limit = example_time_limit();
    // Wall-clock tactic deadlines must not count scheduler contention as
    // verifier work. Keep the correctness gate serial until Click has a
    // contention-independent work budget.
    let failures = run_parallel(&projects, 1, |project| {
        run_example_with_timeout(project, time_limit)
    });
    if failures.is_empty() {
        return;
    }

    let mut message = format!(
        "{} of {} example projects failed:\n",
        failures.len(),
        projects.len()
    );
    for (index, diagnostics) in failures {
        message.push_str(&format!(
            "\n`{}` {diagnostics}\n",
            projects[index].display()
        ));
    }
    panic!("{message}");
}

fn example_time_limit() -> Duration {
    duration_from_env(EXAMPLE_TIME_LIMIT, DEFAULT_EXAMPLE_TIME_LIMIT)
        .unwrap_or_else(|message| panic!("{message}"))
}

fn run_example_with_timeout(project: &Path, time_limit: Duration) -> Result<(), String> {
    let project = project.to_path_buf();
    std::thread::Builder::new()
        .name("click-example".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            let first = run_example_attempt(&project, time_limit)?;
            if std::env::var_os(DISABLE_TACTIC_BUDGETS).is_some() {
                return Ok(());
            }
            let first_violations = structured_tactic_budget_violations(&first);
            if first_violations.is_empty() {
                return Ok(());
            }
            let confirmation = run_example_attempt(&project, time_limit)?;
            let confirmation_violations = structured_tactic_budget_violations(&confirmation);
            if confirmation_violations.is_empty() {
                return Ok(());
            }
            Err(format!(
                "passed twice, but broke tactic time budgets in both measurements (set {DISABLE_TACTIC_BUDGETS}=1 to bypass):\n  first:\n    {}\n  confirmation:\n    {}",
                first_violations.join("\n    "),
                confirmation_violations.join("\n    "),
            ))
        })
        .map_err(|error| format!("failed to start example verifier: {error}"))?
        .join()
        .map_err(|_| "example verifier panicked".to_string())?
}

fn run_example_attempt(
    project: &Path,
    time_limit: Duration,
) -> Result<Vec<instrumentation::VerificationEvent>, String> {
    let started = std::time::Instant::now();
    let operation = || instrumentation::collect(|| run_example_project(project));
    let (result, events) = if std::env::var_os(DISABLE_TACTIC_BUDGETS).is_some() {
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
            "exceeded the per-project example time limit of {}; set {EXAMPLE_TIME_LIMIT} to override it",
            format_duration(time_limit)
        ));
    }
    Ok(events)
}

fn run_example_project(project: &Path) -> Result<(), String> {
    let mut click_paths = files_with_extension(project, "click")?;

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
        let c_sources = read_verifying_sources(&click_path, &click_source)?;
        verify_c0_sources(&click_source, &source_refs(&c_sources)).map_err(|error| {
            format!(
                "example sidecar `{}` failed: {}",
                click_path.display(),
                error.message()
            )
        })?;
    }
    Ok(())
}
