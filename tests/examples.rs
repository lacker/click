use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use click::cli::{
    DEFAULT_VERIFY_TIME_LIMIT, duration_from_env, files_with_extension, format_duration,
    read_verifying_sources, source_refs,
};
use click::instrumentation;
use click::lang::click::verify_c0_sources;

const EXAMPLE_TIME_LIMIT: &str = "CLICK_EXAMPLE_TIME_LIMIT";
const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";

/// Known-broken or pathologically slow projects, skipped by default so the
/// suite is a meaningful green gate. Run one with `CLICK_EXAMPLE=<name>`, or
/// all of them with `CLICK_RUN_QUARANTINED=1`. Each entry names the reason;
/// remove entries as they are fixed (see docs/advanced/testing-click.md).
const QUARANTINED: &[(&str, &str)] = &[
    (
        "binary-tree",
        "issues/binary-tree-grouped-simp-transition-not-expressible.md: grouped simp transition has no expressible certificate since opaque outcome certificates were rejected",
    ),
    (
        "bounded-pool",
        "issues/bounded-pool-outcome-conjunction-certificate-missing.md: outcome conjunction with a resource count has no explicit simple certificate",
    ),
    (
        "owned-split-buffer",
        "issues/owned-split-buffer-expansion-rewrite-not-exact.md: generated rewrite equality is not exact at replay",
    ),
    (
        "owned-string",
        "issues/owned-string-pure-theorem-certificate-missing.md: pure theorem smart proof produces no pure surface certificate",
    ),
    (
        "owned-vector",
        "issues/owned-vector-baseline-misses-project-budget.md: several smart proof sites push the project past its deadline",
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
    // This is the same serial, fail-fast policy as `click verify examples`:
    // verify N projects as ordinary projects, with an independent production
    // deadline and production tactic budgets for each sidecar.
    for project in &projects {
        println!("verifying example project `{}`", project.display());
        if let Err(diagnostics) = run_example_with_timeout(project, time_limit) {
            panic!("example project `{}` {diagnostics}", project.display());
        }
    }
}

fn example_time_limit() -> Duration {
    duration_from_env(EXAMPLE_TIME_LIMIT, DEFAULT_VERIFY_TIME_LIMIT)
        .unwrap_or_else(|message| panic!("{message}"))
}

fn run_example_with_timeout(project: &Path, time_limit: Duration) -> Result<(), String> {
    let project = project.to_path_buf();
    std::thread::Builder::new()
        .name("click-example".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || run_example_attempt(&project, time_limit))
        .map_err(|error| format!("failed to start example verifier: {error}"))?
        .join()
        .map_err(|_| "example verifier panicked".to_string())?
}

fn run_example_attempt(project: &Path, time_limit: Duration) -> Result<(), String> {
    run_example_project(project, time_limit)
}

fn run_example_project(project: &Path, time_limit: Duration) -> Result<(), String> {
    let mut click_paths = files_with_extension(project, "click")?;

    if click_paths.is_empty() {
        return Err(format!(
            "example project `{}` must contain at least one .click sidecar",
            project.display()
        ));
    }

    click_paths.sort();

    for click_path in click_paths {
        instrumentation::with_deadline(time_limit, || {
            let click_source = fs::read_to_string(&click_path)
                .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
            let c_sources = read_verifying_sources(&click_path, &click_source)?;
            verify_c0_sources(&click_source, &source_refs(&c_sources)).map_err(|error| {
                format!(
                    "sidecar `{}` failed under its {} limit: {}",
                    click_path.display(),
                    format_duration(time_limit),
                    error.message()
                )
            })
        })?;
        println!("verified {}", click_path.display());
    }
    Ok(())
}
