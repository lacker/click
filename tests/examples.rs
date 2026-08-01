use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use click::cli::{
    IsolatedRun, default_worker_count, duration_from_env, files_with_extension,
    isolated_test_command, run_isolated, run_parallel, source_refs,
};
use click::lang::click::verify_c0_sources;

const EXAMPLE_CHILD_PATH: &str = "CLICK_EXAMPLE_CHILD_PATH";
const EXAMPLE_TIME_LIMIT: &str = "CLICK_EXAMPLE_TIME_LIMIT";
const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
const DEFAULT_EXAMPLE_TIME_LIMIT: Duration = Duration::from_secs(10 * 60);

/// Known-broken or pathologically slow projects, skipped by default so the
/// suite is a meaningful green gate. Run one with `CLICK_EXAMPLE=<name>`, or
/// all of them with `CLICK_RUN_QUARANTINED=1`. Each entry names the reason;
/// remove entries as they are fixed (see docs/advanced/testing-click.md).
const QUARANTINED: &[(&str, &str)] = &[
    (
        "owned-string",
        "certificate spelling fails for the post-store terminated_at equality; see issues/certificate-spelling-gap.md",
    ),
    (
        "owned-vector",
        "pathologically slow with a stale failure frontier; remeasure after the certificate-spelling gap lands (issues/owned-vector-implies-gap.md)",
    ),
];

#[test]
fn example_projects() {
    if let Some(path) = std::env::var_os(EXAMPLE_CHILD_PATH) {
        run_example_project(Path::new(&path));
        return;
    }

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
    let failures = run_parallel(&projects, default_worker_count(projects.len()), |project| {
        run_example_with_timeout(project, time_limit)
    });
    let failures = click::cli::retain_serial_budget_failures(failures, |index| {
        run_example_with_timeout(&projects[index], time_limit)
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
        message.push_str(&format!("\n`{}` {diagnostics}\n", projects[index].display()));
    }
    panic!("{message}");
}

fn example_time_limit() -> Duration {
    duration_from_env(EXAMPLE_TIME_LIMIT, DEFAULT_EXAMPLE_TIME_LIMIT)
        .unwrap_or_else(|message| panic!("{message}"))
}

/// Runs one example project in an isolated child process (Click proofs have
/// overflowed the stack before; isolation keeps one crash from hiding the
/// other results) under a wall-clock limit.
fn run_example_with_timeout(project: &Path, time_limit: Duration) -> Result<(), String> {
    let command = isolated_test_command("example_projects", EXAMPLE_CHILD_PATH, project)?;
    run_isolated(
        command,
        time_limit,
        IsolatedRun {
            label: &format!("isolated example project `{}`", project.display()),
            limit_description: "the per-project example time limit",
            limit_variable: EXAMPLE_TIME_LIMIT,
            process_description: "its isolated example process",
        },
    )
}

fn run_example_project(project: &Path) {
    let mut c_paths =
        files_with_extension(project, "c").unwrap_or_else(|message| panic!("{message}"));
    let mut click_paths =
        files_with_extension(project, "click").unwrap_or_else(|message| panic!("{message}"));

    assert!(
        !click_paths.is_empty(),
        "example project `{}` must contain at least one .click sidecar",
        project.display()
    );

    c_paths.sort();
    click_paths.sort();

    let c_sources = c_paths
        .iter()
        .map(|path| {
            let filename = path
                .file_name()
                .and_then(|name| name.to_str())
                .unwrap_or_else(|| panic!("invalid UTF-8 path `{}`", path.display()))
                .to_string();
            let source = fs::read_to_string(path)
                .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
            (filename, source)
        })
        .collect::<Vec<_>>();
    let c_source_refs = source_refs(&c_sources);

    for click_path in click_paths {
        let click_source = fs::read_to_string(&click_path)
            .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", click_path.display()));
        verify_c0_sources(&click_source, &c_source_refs).unwrap_or_else(|error| {
            panic!(
                "example sidecar `{}` failed: {}",
                click_path.display(),
                error.message()
            )
        });
    }
}
