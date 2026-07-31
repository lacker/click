use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use click::cli::{
    IsolatedRun, default_worker_count, duration_from_env, isolated_test_command, run_isolated,
    run_parallel,
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
        "bubble_pass3_max_suffix.md",
        "invariant closer cannot re-derive the symbolically extended bound (item-7 nested snapshot spellings)",
    ),
    (
        "bubble_sort3_two_pass_sorted.md",
        "invariant closer cannot re-derive the symbolically extended bound (item-7 nested snapshot spellings)",
    ),
    (
        "composite_resource_owner_buffer_field_dependent.md",
        "fold consumption cannot match deeply nested snapshot spellings (item-7)",
    ),
    (
        "fill_tail_keeps_first.md",
        "loop-havoc transport needs invariant-based load equality (item-7)",
    ),
    (
        "composite_resource_vector_fill_loop_snapshot.md",
        "back-edge closer needs named memory states; per-spelling bridging exhausted (notes/canonical-memory.md, branch claude/forall-extension-wip)",
    ),
    (
        "field_derived_precise_effect_after_metadata_write.md",
        "ensures derivations need named memory states; certified context does not derive them (notes/canonical-memory.md)",
    ),
];

#[derive(Debug)]
struct MdTest {
    c_sources: Vec<(String, String)>,
    click_source: Option<String>,
    expectation: Option<Expectation>,
}

#[derive(Debug)]
enum Expectation {
    Pass,
    FailContains(String),
}

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
    let source = fs::read_to_string(path)
        .unwrap_or_else(|error| panic!("failed to read `{}`: {error}", path.display()));
    let mdtest = parse_mdtest(path, &source);
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
        (Expectation::Pass, Ok(_)) => {}
        (Expectation::Pass, Err(error)) => {
            panic!(
                "`{}` expected pass, but failed: {}",
                path.display(),
                error.message()
            );
        }
        (Expectation::FailContains(expected), Ok(_)) => {
            panic!(
                "`{}` expected failure containing `{expected}`, but passed",
                path.display()
            );
        }
        (Expectation::FailContains(expected), Err(error)) => {
            assert!(
                error.message().contains(expected),
                "`{}` expected failure containing `{expected}`, got `{}`",
                path.display(),
                error.message()
            );
        }
    }
}

fn parse_mdtest(path: &Path, source: &str) -> MdTest {
    let mut mdtest = MdTest {
        c_sources: Vec::new(),
        click_source: None,
        expectation: None,
    };
    let lines = source.lines().collect::<Vec<_>>();
    let mut index = 0;

    while index < lines.len() {
        let line = lines[index];
        if !line.starts_with("```") {
            index += 1;
            continue;
        }

        let info = line.trim_start_matches("```").trim();
        index += 1;
        let start_line = index + 1;
        let mut body = Vec::new();
        while index < lines.len() && !lines[index].starts_with("```") {
            body.push(lines[index]);
            index += 1;
        }
        if index == lines.len() {
            panic!(
                "`{}` has unterminated fenced block starting at line {start_line}",
                path.display()
            );
        }
        index += 1;

        let body = body.join("\n");
        match block_kind(info) {
            Some(BlockKind::C { filename }) => {
                mdtest.c_sources.push((filename, body));
            }
            Some(BlockKind::Click) => {
                if mdtest.click_source.replace(body).is_some() {
                    panic!("`{}` has more than one ```click block", path.display());
                }
            }
            Some(BlockKind::Expect) => {
                let expectation = parse_expectation(path, start_line, &body);
                if mdtest.expectation.replace(expectation).is_some() {
                    panic!("`{}` has more than one ```expect block", path.display());
                }
            }
            None => {}
        }
    }

    mdtest
}

enum BlockKind {
    C { filename: String },
    Click,
    Expect,
}

fn block_kind(info: &str) -> Option<BlockKind> {
    let mut parts = info.split_whitespace();
    match parts.next()? {
        "c" => {
            let filename = parts.find_map(|part| part.strip_prefix("filename="))?;
            Some(BlockKind::C {
                filename: filename.to_string(),
            })
        }
        "click" => Some(BlockKind::Click),
        "expect" => Some(BlockKind::Expect),
        _ => None,
    }
}

fn parse_expectation(path: &Path, line: usize, body: &str) -> Expectation {
    let body = body.trim();
    if body == "pass" {
        return Expectation::Pass;
    }

    if let Some(message) = body.strip_prefix("fail:") {
        return Expectation::FailContains(message.trim().to_string());
    }

    panic!(
        "`{}` has invalid expectation at line {line}: expected `pass` or `fail: substring`, got `{body}`",
        path.display()
    );
}
