use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use click::cli::{
    BoundedOutput, default_worker_count, files_with_extension, format_duration, parse_duration,
    run_bounded, run_parallel, source_refs,
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
        "owned-segmented-buffer",
        "pipeline contract fails: `step using` misses a pure fact that prints identically to an available one (CMemory snapshot equality mismatch)",
    ),
    (
        "owned-split-buffer",
        "whole-file verification exceeds 10 minutes",
    ),
    (
        "owned-string",
        "owned_string_len fails: exact symbolic execution produced no valid paths",
    ),
    (
        "owned-vector",
        "whole-file verification exceeds 10 minutes",
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
    let Some(source) = std::env::var_os(EXAMPLE_TIME_LIMIT) else {
        return DEFAULT_EXAMPLE_TIME_LIMIT;
    };
    let source = source
        .to_str()
        .unwrap_or_else(|| panic!("{EXAMPLE_TIME_LIMIT} must be valid UTF-8"));
    parse_duration(source).unwrap_or_else(|message| panic!("{EXAMPLE_TIME_LIMIT}: {message}"))
}

/// Runs one example project in an isolated child process (Click proofs have
/// overflowed the stack before; isolation keeps one crash from hiding the
/// other results) under a wall-clock limit.
fn run_example_with_timeout(project: &Path, time_limit: Duration) -> Result<(), String> {
    let executable = std::env::current_exe()
        .map_err(|error| format!("failed to locate the examples integration-test executable: {error}"))?;
    let mut command = Command::new(executable);
    command
        .arg("--exact")
        .arg("example_projects")
        .arg("--nocapture")
        .env(EXAMPLE_CHILD_PATH, project)
        // Prover recursion follows term structure, which nests far deeper
        // than the default test-thread stack on snapshot-heavy fixtures.
        .env("RUST_MIN_STACK", "67108864");
    let label = format!("isolated example project `{}`", project.display());
    let (status, stdout, stderr) = match run_bounded(command, time_limit, &label)? {
        BoundedOutput::Completed(output) => (Some(output.status), output.stdout, output.stderr),
        BoundedOutput::TimedOut { stdout, stderr, .. } => (None, stdout, stderr),
    };
    let output = format!(
        "{}{}",
        String::from_utf8_lossy(&stdout),
        String::from_utf8_lossy(&stderr)
    );
    let Some(status) = status else {
        return Err(format!(
            "exceeded the per-project example time limit of {}; set {EXAMPLE_TIME_LIMIT} to override it{}",
            format_duration(time_limit),
            indented_output(&output)
        ));
    };
    if !status.success() {
        return Err(format!(
            "failed in its isolated example process{}",
            indented_output(&output)
        ));
    }
    Ok(())
}

fn indented_output(output: &str) -> String {
    let output = output.trim();
    if output.is_empty() {
        String::new()
    } else {
        format!(
            "\n{}",
            output
                .lines()
                .map(|line| format!("  {line}"))
                .collect::<Vec<_>>()
                .join("\n")
        )
    }
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
