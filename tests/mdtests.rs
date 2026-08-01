use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use click::cli::{
    IsolatedRun, MdTestExpectation, default_worker_count, duration_from_env, isolated_test_command,
    read_mdtest, run_isolated, run_parallel,
};
use click::lang::click::verify_c0_sources;

const MDTEST_CHILD_PATH: &str = "CLICK_MDTEST_CHILD_PATH";
const MDTEST_TIME_LIMIT: &str = "MDTEST_TIME_LIMIT";
const RUN_QUARANTINED: &str = "CLICK_RUN_QUARANTINED";
const DEFAULT_MDTEST_TIME_LIMIT: Duration = Duration::from_secs(30);

/// Known-broken mdtests, skipped by default so the suite is a meaningful
/// green gate. Run one with `MDTEST_FILTER=<name>`, or all of them with
/// `CLICK_RUN_QUARANTINED=1`. Each entry names the reason; remove entries as
/// they are fixed (see docs/advanced/testing-click.md).
const QUARANTINED: &[(&str, &str)] = &[
    (
        "composite_resource_vector_fill_loop_snapshot.md",
        "proof passes, but deterministic close_invariants replay takes ~2.8 s (issues/vector-close-invariants-slow.md)",
    ),
    (
        "field_derived_precise_effect_after_metadata_write.md",
        "effect-chain postconditions produce no replayable minimized derivation; it also has a slow simple fold (issues/certificate-spelling-gap.md, issues/field-derived-slow-fold.md)",
    ),
];

#[test]
fn mdtests() {
    if let Some(path) = std::env::var_os(MDTEST_CHILD_PATH) {
        run_mdtest(Path::new(&path));
        return;
    }

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

/// Runs one mdtest in an isolated child process (Click proofs have
/// overflowed the stack before; isolation keeps one crash from hiding the
/// other results) under a wall-clock limit.
fn run_mdtest_with_timeout(path: &Path, time_limit: Duration) -> Result<(), String> {
    let command = isolated_test_command("mdtests", MDTEST_CHILD_PATH, path)?;
    run_isolated(
        command,
        time_limit,
        IsolatedRun {
            label: &format!("isolated mdtest `{}`", path.display()),
            limit_description: "the per-file mdtest time limit",
            limit_variable: MDTEST_TIME_LIMIT,
            process_description: "its isolated mdtest process",
        },
    )
}

fn run_mdtest(path: &Path) {
    let mdtest = read_mdtest(path).unwrap_or_else(|message| panic!("{message}"));
    let click_source = mdtest
        .click_source
        .as_deref()
        .unwrap_or_else(|| panic!("`{}` is missing a ```click block", path.display()));
    let c_sources = mdtest
        .c_sources
        .iter()
        .map(|(filename, source)| (filename.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    let expectation = mdtest
        .expectation
        .as_ref()
        .unwrap_or_else(|| panic!("`{}` is missing a ```expect block", path.display()));

    let result = verify_c0_sources(click_source, &c_sources);
    match (expectation, result) {
        (MdTestExpectation::Pass, Ok(_)) => {}
        (MdTestExpectation::Pass, Err(error)) => {
            panic!(
                "`{}` expected pass, but failed: {}",
                path.display(),
                error.message()
            );
        }
        (MdTestExpectation::FailContains(expected), Ok(_)) => {
            panic!(
                "`{}` expected failure containing `{expected}`, but passed",
                path.display()
            );
        }
        (MdTestExpectation::FailContains(expected), Err(error)) => {
            assert!(
                error.message().contains(expected),
                "`{}` expected failure containing `{expected}`, got `{}`",
                path.display(),
                error.message()
            );
        }
    }
}
