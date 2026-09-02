use std::fs;
use std::path::{Path, PathBuf};

use click::cli::{files_with_extension, read_verifying_sources, source_refs};
use click::instrumentation::{self, ContractFallback};
use click::surface::verify_c0_sources;

const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";

/// Known-broken or pathologically slow projects, skipped by default so the
/// suite is a meaningful green gate. Run one with `CLICK_EXAMPLE=<name>`, or
/// all of them with `CLICK_RUN_QUARANTINED=1`. Each entry names the reason;
/// remove entries as they are fixed (see docs/internals/testing.md).
const QUARANTINED: &[(&str, &str)] = &[];

/// The body-rerun ratchet (`docs/internals/testing.md`) over every example
/// project; see `tests/mdtests.rs` for the rule.
const CONTRACT_FALLBACK_BASELINE: &[(ContractFallback, usize)] = &[];

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

    // Keep project verification serial and fail fast. Deterministic tactic
    // work budgets decide correctness; the test runner owns hang containment.
    let _ = instrumentation::take_body_rerun_census();
    for project in &projects {
        // One line as each project starts and one as it finishes, on stderr
        // so the gate can stream them: a stall shows as a started project
        // that never finishes, and a slow project is visible while it runs.
        eprintln!("example project `{}` started", project.display());
        let started = std::time::Instant::now();
        if let Err(diagnostics) = run_example_in_thread(project) {
            panic!("example project `{}` {diagnostics}", project.display());
        }
        eprintln!(
            "example project `{}` verified in {:.2}s",
            project.display(),
            started.elapsed().as_secs_f64()
        );
    }
    let census = instrumentation::take_body_rerun_census();
    if requested.is_none()
        && !run_quarantined
        && let Some(mismatch) =
            instrumentation::body_rerun_census_mismatch(&census, CONTRACT_FALLBACK_BASELINE)
    {
        panic!("body rerun ratchet (tests/examples.rs baselines):\n{mismatch}");
    }
}

fn run_example_in_thread(project: &Path) -> Result<(), String> {
    let project = project.to_path_buf();
    std::thread::Builder::new()
        .name("click-example".to_string())
        .stack_size(64 * 1024 * 1024)
        .spawn(move || {
            instrumentation::without_tactic_time_limits(|| run_example_project(&project))
        })
        .map_err(|error| format!("failed to start example verifier: {error}"))?
        .join()
        .map_err(|_| "example verifier panicked".to_string())?
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
                "sidecar `{}` failed: {}",
                click_path.display(),
                error.message()
            )
        })?;
        eprintln!("verified {}", click_path.display());
    }
    Ok(())
}
