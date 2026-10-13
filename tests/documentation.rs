use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use click::cli::{
    CRASH_CONTAINMENT_TIME_LIMIT, PUBLIC_CLI_BEHAVIORS, PUBLIC_ENVIRONMENT_VARIABLES, RunLimits,
    format_duration,
};
use click::languages::c::syntax::C0_PUBLIC_FORMS;
use click::surface::{PUBLIC_TACTIC_FORMS, SURFACE_CLICK_FORMS, SURFACE_CLICK_WORDS};

#[path = "support/ai_reference.rs"]
mod ai_reference;

#[derive(Debug)]
struct InventoryItem {
    id: String,
    path: String,
}

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

#[test]
fn proof_and_program_languages_have_distinct_source_roots() {
    let source_root = root().join("src");
    for path in [
        "surface.rs",
        "surface/parser.rs",
        "languages.rs",
        "languages/c.rs",
        "languages/c/syntax.rs",
    ] {
        assert!(
            source_root.join(path).is_file(),
            "missing language-role source root `{path}`"
        );
    }
    assert!(
        !source_root.join("lang.rs").exists() && !source_root.join("lang").exists(),
        "Surface Click and program languages must not return to one flat `lang` namespace"
    );
    let library = fs::read_to_string(source_root.join("lib.rs")).expect("read library root");
    assert!(library.contains("pub mod surface;"));
    assert!(library.contains("pub mod languages;"));
    assert!(!library.contains("pub mod lang;"));
}

#[test]
fn language_proof_code_cannot_rebuild_the_kernel_proof_object() {
    let kernel = fs::read_to_string(root().join("src/kernel/proof/object.rs"))
        .expect("read kernel proof object");
    assert!(
        !kernel.contains("pub(crate) fn new(state: ProofState"),
        "the raw proof-object constructor must remain private to its kernel module"
    );
    for field in [
        "pub(crate) locals:",
        "pub(crate) open_branches:",
        "pub(crate) added_facts:",
        "pub(crate) checked_facts:",
    ] {
        assert!(
            !kernel.contains(field),
            "the raw proof-state field `{field}` must remain private"
        );
    }

    let directory = root().join("src/surface/proof/proof_object");
    let mut files = Vec::new();
    files_with_extension(&directory, "rs", &mut files);
    files.push(root().join("src/surface/proof/proof_object.rs"));
    for path in files {
        if path.file_name().and_then(|name| name.to_str()) == Some("tests.rs") {
            continue;
        }
        let source = fs::read_to_string(&path).expect("read language proof source");
        for escape_hatch in [
            "KernelProofState {",
            "KernelProofObject::new(",
            ".into_state(",
        ] {
            assert!(
                !source.contains(escape_hatch),
                "{} reconstructs kernel proof state through `{escape_hatch}`",
                path.display()
            );
        }
    }
}

/// The part of a source file that ships: everything before an inline
/// `#[cfg(test)] mod tests` block, or nothing for a file of tests.
fn shipped_part<'a>(path: &Path, source: &'a str) -> Option<&'a str> {
    let name = path.file_name().unwrap().to_str().unwrap();
    if name.ends_with("tests.rs")
        || path
            .components()
            .any(|component| component.as_os_str() == "tests")
    {
        return None;
    }
    Some(
        source
            .find("\n#[cfg(test)]\nmod tests {")
            .map_or(source, |end| &source[..end]),
    )
}

/// Verdicts come from deterministic work budgets only: the per-class tactic
/// budgets and the whole-run budget of `click::cli::RunLimits`. The one
/// wall-clock bound a shipped tool installs is the crash-containment bound of
/// `click::cli::with_run_limits`, whose message says it is not a verdict
/// about the proof. So no shipped source outside that helper may install a
/// deadline, and no fixture harness may install one of its own.
#[test]
fn wall_clock_bounds_are_crash_containment_only() {
    const OWNERS: &[&str] = &["src/instrumentation.rs", "src/cli.rs"];
    let mut files = Vec::new();
    files_with_extension(&root().join("src"), "rs", &mut files);
    files.sort();
    let mut checked = 0;
    for path in &files {
        let display = path.strip_prefix(root()).unwrap().display().to_string();
        let source = fs::read_to_string(path).expect("read source");
        let Some(shipped) = shipped_part(path, &source) else {
            continue;
        };
        checked += 1;
        if OWNERS.contains(&display.as_str()) {
            continue;
        }
        let lines = shipped.lines().collect::<Vec<_>>();
        for (index, line) in lines.iter().enumerate() {
            let Some(forbidden) = ["with_deadline(", "with_run_work_limit("]
                .into_iter()
                .find(|forbidden| line.contains(forbidden))
            else {
                continue;
            };
            // A `#[test]` or `#[cfg(test)]` function outside a `tests`
            // module is test code too.
            let in_test_function = lines[..index]
                .iter()
                .rposition(|line| {
                    let line = line.trim_start();
                    line.starts_with("fn ") || line.starts_with("pub") && line.contains(" fn ")
                })
                .is_some_and(|function| {
                    lines[function.saturating_sub(3)..function]
                        .iter()
                        .any(|line| matches!(line.trim(), "#[test]" | "#[cfg(test)]"))
                });
            assert!(
                in_test_function,
                "{display}:{} calls `{forbidden}` outside tests; a shipped tool bounds a run \
                 only through `click::cli::with_run_limits`, so wall-clock time stays crash \
                 containment and never becomes a verdict",
                index + 1
            );
        }
    }
    assert!(checked >= 100, "expected the shipped sources under src/");
    let cli = fs::read_to_string(root().join("src/cli.rs")).expect("read src/cli.rs");
    assert_eq!(
        cli.matches("instrumentation::with_deadline(").count(),
        1,
        "src/cli.rs installs the crash-containment bound in exactly one helper"
    );
    let instrumentation =
        fs::read_to_string(root().join("src/instrumentation.rs")).expect("read instrumentation");
    for message in ["crash-containment bound", "not a verdict about the proof"] {
        assert!(
            instrumentation.contains(message),
            "an expired containment bound must say `{message}`"
        );
    }

    let mut harnesses = Vec::new();
    files_with_extension(&root().join("tests"), "rs", &mut harnesses);
    for path in harnesses {
        let source = fs::read_to_string(&path).expect("read harness");
        let display = path.strip_prefix(root()).unwrap().display().to_string();
        if display == "tests/documentation.rs" {
            continue;
        }
        for forbidden in ["with_deadline(", "Instant::now() +"] {
            assert!(
                !source.contains(forbidden),
                "{display} installs a wall-clock bound (`{forbidden}`); fixture verdicts come \
                 from deterministic work budgets, and nextest's per-test timeout is the \
                 harnesses' hang containment"
            );
        }
    }
}

/// The command-line tools bound a run by deterministic work, and their
/// wall-clock bound is ten-minute crash containment, so an in-process test
/// of a tool cannot pass or fail with machine load unless it shortens that
/// bound itself. Every test that does, or that installs a deadline directly,
/// is listed here with its reason, so the wall-clock-dependent tests stay a
/// short, reviewed list.
#[test]
fn command_line_tests_name_every_wall_clock_bound_they_set() {
    const WALL_CLOCK: &[(&str, &str, &str)] = &[
        (
            "click-expand.rs",
            "reports_an_expired_expansion_deadline_directly",
            "checks the diagnostic of an already-expired containment bound",
        ),
        (
            "click-expand.rs",
            "exhausted_command_deadline_writes_no_artifact",
            "checks that `--time-limit 1ms` containment writes no artifact",
        ),
        (
            "click-expand.rs",
            "parses_time_limit_before_or_after_positionals",
            "parses the option; runs no verification",
        ),
        (
            "click-expand.rs",
            "parses_source_location_with_colons_in_path",
            "parses the option; runs no verification",
        ),
        (
            "click-verify.rs",
            "the_crash_bound_covers_source_loading_and_parsing",
            "checks that `--time-limit 1ms` containment is installed before sources load",
        ),
        (
            "click-verify.rs",
            "parses_default_and_overridden_run_limits",
            "parses the option; runs no verification",
        ),
        (
            "tests.rs",
            "parses_profile_arguments",
            "parses the option; runs no verification",
        ),
    ];
    let mut files = Vec::new();
    files_with_extension(&root().join("src/bin"), "rs", &mut files);
    files.sort();
    let mut checked = 0;
    let mut listed = BTreeSet::new();
    for path in files {
        let name = path.file_name().unwrap().to_str().unwrap().to_string();
        let display = path.strip_prefix(root()).unwrap().display().to_string();
        let source = fs::read_to_string(&path).expect("read command-line source");
        let lines: Vec<&str> = source.lines().collect();
        for (index, line) in lines.iter().enumerate() {
            if line.trim() != "#[test]" {
                continue;
            }
            let signature = lines[index + 1..]
                .iter()
                .position(|line| line.trim_start().starts_with("fn "))
                .map(|offset| index + 1 + offset)
                .unwrap_or_else(|| panic!("{display}:{} has no test function", index + 1));
            let test = lines[signature]
                .trim_start()
                .trim_start_matches("fn ")
                .split('(')
                .next()
                .unwrap();
            let indent = lines[signature].len() - lines[signature].trim_start().len();
            let close = format!("{}}}", " ".repeat(indent));
            let body = lines[signature + 1..]
                .iter()
                .take_while(|line| **line != close)
                .copied()
                .collect::<Vec<_>>()
                .join("\n");
            checked += 1;
            // Passing the option: an argument-list element or an owned
            // argument string, not a mention in an assertion.
            let sets_wall_clock = body.contains("with_deadline(")
                || body.contains("\"--time-limit\",")
                || body.contains("\"--time-limit\".to_string()");
            let exempt = WALL_CLOCK
                .iter()
                .any(|(file, exempt, _)| *file == name && *exempt == test);
            if exempt {
                listed.insert((name.clone(), test.to_string()));
            }
            assert!(
                !sets_wall_clock || exempt,
                "{display}:{} `{test}` sets a wall-clock bound; judge it by a deterministic \
                 work budget (`--work-limit`, `with_run_work_limit`) instead, or list it with \
                 a reason in `command_line_tests_name_every_wall_clock_bound_they_set`",
                signature + 1,
            );
        }
    }
    assert!(
        checked >= 100,
        "expected the command-line tests under src/bin/"
    );
    for (file, test, _) in WALL_CLOCK {
        assert!(
            listed.contains(&(file.to_string(), test.to_string())),
            "listed wall-clock test `{test}` is no longer in src/bin/**/{file}; remove it"
        );
    }
}

fn files_with_extension(directory: &Path, extension: &str, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).expect("read directory") {
        let path = entry.expect("read directory entry").path();
        if path.is_dir() {
            files_with_extension(&path, extension, files);
        } else if path.extension().and_then(|value| value.to_str()) == Some(extension) {
            files.push(path);
        }
    }
}

fn markdown_files(directory: &Path, files: &mut Vec<PathBuf>) {
    files_with_extension(directory, "md", files);
}

/// The rendered site's `llms.txt` and single-file bundle are generated, not
/// committed. Generating them checks every page's opening sentence and every
/// rewritten link; with `CLICK_AI_REFERENCE_OUT` set, the files are written
/// there (`scripts/build-ai-reference.sh`).
#[test]
fn ai_reference_site_files_generate() {
    let files = ai_reference::generate(&root()).unwrap_or_else(|error| panic!("{error}"));
    let names = files
        .iter()
        .map(|(name, _)| name.as_str())
        .collect::<Vec<_>>();
    assert!(names.contains(&"llms.txt") && names.contains(&"click-reference.md"));
    let Some(output) = std::env::var_os(ai_reference::OUTPUT_VARIABLE) else {
        return;
    };
    let output = PathBuf::from(output);
    for (relative, contents) in files {
        let path = output.join(&relative);
        if let Some(parent) = path.parent() {
            fs::create_dir_all(parent).unwrap_or_else(|error| panic!("{relative}: {error}"));
        }
        fs::write(&path, contents).unwrap_or_else(|error| panic!("{relative}: {error}"));
    }
}

fn slug(heading: &str) -> String {
    let mut result = String::new();
    for ch in heading.trim().chars() {
        if ch.is_ascii_alphanumeric() || ch == '_' || ch == '-' {
            result.push(ch.to_ascii_lowercase());
        } else if ch.is_whitespace() {
            result.push('-');
        }
    }
    while result.contains("--") {
        result = result.replace("--", "-");
    }
    result.trim_matches('-').to_string()
}

fn anchors(source: &str) -> BTreeSet<String> {
    source
        .lines()
        .filter_map(|line| {
            let heading = line.strip_prefix('#')?.trim_start_matches('#').trim();
            (!heading.is_empty()).then(|| slug(heading))
        })
        .collect()
}

fn inventory() -> Vec<InventoryItem> {
    let source =
        fs::read_to_string(root().join("docs/reference/inventory.toml")).expect("read inventory");
    let mut items = Vec::new();
    let mut id = None;
    let mut path = None;
    for line in source.lines().map(str::trim) {
        if line == "[[item]]" {
            if let (Some(id), Some(path)) = (id.take(), path.take()) {
                items.push(InventoryItem { id, path });
            }
        } else if let Some(value) = line.strip_prefix("id = ") {
            id = Some(unquote(value));
        } else if let Some(value) = line.strip_prefix("path = ") {
            path = Some(unquote(value));
        }
    }
    if let (Some(id), Some(path)) = (id, path) {
        items.push(InventoryItem { id, path });
    }
    items
}

fn unquote(value: &str) -> String {
    value
        .strip_prefix('"')
        .and_then(|value| value.strip_suffix('"'))
        .unwrap_or_else(|| panic!("inventory value is not a quoted string: {value}"))
        .to_string()
}

fn inventory_ids(prefix: &str) -> BTreeSet<String> {
    inventory()
        .into_iter()
        .filter_map(|item| item.id.strip_prefix(prefix).map(str::to_string))
        .collect()
}

#[test]
fn inventory_entries_are_unique_and_resolve() {
    let docs = root().join("docs");
    let mut ids = BTreeSet::new();
    for item in inventory() {
        assert!(
            ids.insert(item.id.clone()),
            "duplicate inventory ID {}",
            item.id
        );
        let (relative, anchor) = item
            .path
            .split_once('#')
            .unwrap_or_else(|| panic!("inventory path has no anchor: {}", item.path));
        let path = docs.join(relative);
        let source =
            fs::read_to_string(&path).unwrap_or_else(|error| panic!("{}: {error}", path.display()));
        assert!(
            anchors(&source).contains(anchor),
            "{} points to missing anchor #{anchor} in {}",
            item.id,
            path.display()
        );
    }
}

#[test]
fn every_page_has_structural_markdown_and_navigation() {
    let docs = root().join("docs");
    let mut files = Vec::new();
    markdown_files(&docs, &mut files);
    files.sort();

    let summary = fs::read_to_string(docs.join("SUMMARY.md")).expect("read SUMMARY.md");
    let listed = markdown_links(&summary)
        .into_iter()
        .filter(|link| link.ends_with(".md"))
        .collect::<Vec<_>>();
    let mut counts = BTreeMap::new();
    for link in listed {
        *counts.entry(link).or_insert(0usize) += 1;
    }

    let mut failures = Vec::new();
    for path in files {
        if path.ends_with("SUMMARY.md") {
            continue;
        }
        let relative = path.strip_prefix(&docs).expect("docs-relative path");
        let relative = relative.to_string_lossy().replace('\\', "/");
        match counts.get(&relative).copied().unwrap_or(0) {
            1 => {}
            0 => failures.push(format!("{relative}: page is absent from SUMMARY.md")),
            count => failures.push(format!(
                "{relative}: page occurs {count} times in SUMMARY.md"
            )),
        }

        let source = fs::read_to_string(&path).expect("read Markdown page");
        let headings = source
            .lines()
            .enumerate()
            .filter_map(|(line, text)| {
                let marks = text.chars().take_while(|ch| *ch == '#').count();
                (marks > 0 && text.chars().nth(marks) == Some(' ')).then_some((line + 1, marks))
            })
            .collect::<Vec<_>>();
        if headings.iter().filter(|(_, level)| *level == 1).count() != 1 {
            failures.push(format!("{relative}: expected exactly one H1"));
        }
        for pair in headings.windows(2) {
            if pair[1].1 > pair[0].1 + 1 {
                failures.push(format!(
                    "{relative}:{}: heading level skips from H{} to H{}",
                    pair[1].0, pair[0].1, pair[1].1
                ));
            }
        }
        for (line, text) in source.lines().enumerate() {
            if text.contains("![](") || text.contains("![ ](") {
                failures.push(format!(
                    "{relative}:{}: image needs meaningful alternative text",
                    line + 1
                ));
            }
            let Some(heading) = text
                .strip_prefix('#')
                .map(|text| text.trim_start_matches('#').trim())
            else {
                continue;
            };
            for word in heading.split_whitespace().skip(1) {
                let word = word.trim_matches(|ch: char| !ch.is_ascii_alphabetic() && ch != '`');
                if word.starts_with('`')
                    || matches!(word, "Click" | "Surface" | "Kernel" | "Rust" | "Git")
                    || word.chars().all(|ch| !ch.is_ascii_lowercase())
                {
                    continue;
                }
                if word
                    .chars()
                    .next()
                    .is_some_and(|ch| ch.is_ascii_uppercase())
                {
                    failures.push(format!(
                        "{relative}:{}: heading is not sentence case: {heading}",
                        line + 1
                    ));
                    break;
                }
            }
        }

        let mut open_fence = None;
        for (line, text) in source.lines().enumerate() {
            if let Some(rest) = text.strip_prefix("```") {
                if open_fence.is_none() {
                    if rest.trim().is_empty() {
                        failures.push(format!(
                            "{relative}:{}: opening code fence needs a language",
                            line + 1
                        ));
                    }
                    open_fence = Some(line + 1);
                } else {
                    open_fence = None;
                }
            }
        }
        if let Some(line) = open_fence {
            failures.push(format!("{relative}:{line}: unclosed code fence"));
        }
    }
    assert!(
        failures.is_empty(),
        "documentation structure failures:\n{}",
        failures.join("\n")
    );
}

#[test]
fn local_markdown_links_resolve() {
    let docs = root().join("docs");
    let canonical_docs = docs.canonicalize().expect("canonical docs directory");
    let mut files = Vec::new();
    markdown_files(&docs, &mut files);
    let mut failures = Vec::new();
    for path in files {
        let source = fs::read_to_string(&path).expect("read Markdown page");
        for link in markdown_links(&source) {
            if link.starts_with("http://")
                || link.starts_with("https://")
                || link.starts_with("mailto:")
                || link.starts_with('/')
            {
                continue;
            }
            let without_query = link.split('?').next().unwrap_or(&link);
            let (target, requested_anchor) = without_query
                .split_once('#')
                .map_or((without_query, None), |(target, anchor)| {
                    (target, Some(anchor))
                });
            let target_path = if target.is_empty() {
                path.clone()
            } else {
                path.parent().expect("page parent").join(target)
            };
            let target_path = target_path.canonicalize().unwrap_or(target_path);
            if !target_path.starts_with(&canonical_docs) {
                failures.push(format!(
                    "{}: local link {link} escapes docs/ and won't be published",
                    path.display()
                ));
                continue;
            }
            let Ok(target_source) = fs::read_to_string(&target_path) else {
                failures.push(format!("{}: broken link {link}", path.display()));
                continue;
            };
            if let Some(requested_anchor) = requested_anchor
                && !anchors(&target_source).contains(requested_anchor)
            {
                failures.push(format!(
                    "{}: link {link} has no matching anchor",
                    path.display()
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "broken local links:\n{}",
        failures.join("\n")
    );
}

#[test]
fn normative_technical_examples_are_backed_by_verification_fixtures() {
    let docs = root().join("docs");
    let mut pages = Vec::new();
    markdown_files(&docs, &mut pages);
    let mut failures = Vec::new();

    for page in pages {
        if page.starts_with(docs.join("reference/library")) {
            // Library declarations are exact source includes and every symbol
            // has a separately checked use in stdlib_every_symbol.md.
            continue;
        }
        let source = fs::read_to_string(&page).expect("read language reference");
        let lines = source.lines().collect::<Vec<_>>();
        for (index, line) in lines.iter().enumerate() {
            if !matches!(*line, "```click" | "```c") {
                continue;
            }
            let marker = index
                .checked_sub(1)
                .and_then(|previous| lines.get(previous))
                .and_then(|line| line.strip_prefix("<!-- verified-example: "))
                .and_then(|line| line.strip_suffix(" -->"));
            let Some(fixture) = marker else {
                failures.push(format!(
                    "{}:{}: normative code block has no verified-example marker",
                    page.display(),
                    index + 1
                ));
                continue;
            };
            let is_mdtest = fixture.starts_with("mdtests/") && fixture.ends_with(".md");
            let is_cpp_integration_fixture = fixture
                .starts_with("tests/fixtures/cpp-verification/")
                && fixture.ends_with(".click");
            let is_cpp_example =
                fixture.starts_with("examples/basic-cpp/") && fixture.ends_with(".click");
            let is_rust_integration_fixture = fixture
                .starts_with("tests/fixtures/rust-verification/")
                && fixture.ends_with(".click");
            if !is_mdtest
                && !is_cpp_integration_fixture
                && !is_cpp_example
                && !is_rust_integration_fixture
            {
                failures.push(format!(
                    "{}:{}: verified example must name an mdtests/*.md, a C++ or Rust integration fixture, or a C++ example: {fixture}",
                    page.display(),
                    index + 1
                ));
                continue;
            }
            let fixture_path = root().join(fixture);
            let Ok(fixture_source) = fs::read_to_string(&fixture_path) else {
                failures.push(format!(
                    "{}:{}: missing verified fixture {fixture}",
                    page.display(),
                    index + 1
                ));
                continue;
            };
            if is_mdtest {
                assert!(
                    fixture_source.contains("```click") && fixture_source.contains("```expect"),
                    "{fixture}: documentation fixtures must contain Click source and an expected result"
                );
            } else {
                let fence_end = lines[index + 1..]
                    .iter()
                    .position(|line| *line == "```")
                    .map(|offset| index + 1 + offset)
                    .expect("technical code fence must close");
                let documented_source = format!("{}\n", lines[index + 1..fence_end].join("\n"));
                assert_eq!(
                    documented_source, fixture_source,
                    "{fixture}: documented proof must exactly match its integration fixture"
                );
                let integration_tests = if is_rust_integration_fixture {
                    "tests/rust_import.rs"
                } else {
                    "tests/cpp_import.rs"
                };
                let cpp_import_tests = fs::read_to_string(root().join(integration_tests))
                    .expect("read the integration tests");
                let include_path = if is_cpp_example {
                    format!("../{fixture}")
                } else {
                    fixture
                        .strip_prefix("tests/")
                        .expect("C++ fixture lives below tests/")
                        .to_string()
                };
                assert!(
                    cpp_import_tests.contains(&include_path),
                    "{fixture}: the proof must be included by {integration_tests}"
                );
            }
            if *line == "```c" {
                assert!(
                    fixture_source.contains("```c filename="),
                    "{fixture}: C example fixture must contain a named C source block"
                );
            }
        }
    }

    assert!(
        failures.is_empty(),
        "unverified normative technical examples:\n{}",
        failures.join("\n")
    );
}

#[test]
fn example_catalog_only_names_checked_fixtures() {
    let source = fs::read_to_string(root().join("docs/reference/examples.md"))
        .expect("read example catalog");
    let mut checked = 0usize;
    for code in source.split('`').skip(1).step_by(2) {
        if code.starts_with("mdtests/") && code.ends_with(".md") {
            let fixture = root().join(code);
            let fixture_source = fs::read_to_string(&fixture)
                .unwrap_or_else(|error| panic!("catalog fixture `{code}`: {error}"));
            assert!(
                fixture_source.contains("```expect"),
                "catalog fixture `{code}` has no expected mdtest result"
            );
            checked += 1;
        } else if code.starts_with("examples/") && code.ends_with('/') {
            let fixture = root().join(code);
            assert!(
                fixture.is_dir(),
                "catalog example directory `{code}` is missing"
            );
            if code != "examples/" {
                assert!(
                    fs::read_dir(&fixture)
                        .expect("read example project")
                        .any(|entry| entry
                            .expect("read example file")
                            .path()
                            .extension()
                            .is_some_and(|extension| extension == "click")),
                    "catalog example directory `{code}` has no Click sidecar"
                );
            }
            checked += 1;
        }
    }
    assert!(
        checked >= 200,
        "example catalog unexpectedly covers only {checked} checked fixtures"
    );
}

fn markdown_links(source: &str) -> Vec<String> {
    let mut links = Vec::new();
    let bytes = source.as_bytes();
    let mut index = 0;
    while index + 1 < bytes.len() {
        if bytes[index] == b']' && bytes[index + 1] == b'(' {
            let start = index + 2;
            if let Some(end_offset) = source[start..].find(')') {
                let value = source[start..start + end_offset].trim();
                let value = value.split_whitespace().next().unwrap_or(value);
                if !value.is_empty() {
                    links.push(value.trim_matches(['<', '>']).to_string());
                }
                index = start + end_offset;
            }
        }
        index += 1;
    }
    links
}

#[test]
fn standard_library_inventory_is_bidirectional() {
    let source = fs::read_to_string(root().join("stdlib/prelude.click")).expect("read prelude");
    let mut declarations = BTreeSet::new();
    for line in source.lines() {
        let line = line.trim_start();
        if let Some(rest) = line.strip_prefix("abstract resource ") {
            let name = rest
                .split(|ch: char| ch == '(' || ch.is_whitespace())
                .next()
                .expect("resource name");
            declarations.insert(format!("resource.{name}"));
        }
        for kind in ["spec enum", "theorem", "function", "predicate", "resource"] {
            if let Some(rest) = line.strip_prefix(&format!("{kind} ")) {
                let name = rest
                    .split(|ch: char| ch == '(' || ch == '<' || ch.is_whitespace())
                    .next()
                    .expect("declaration name");
                let kind = if kind == "spec enum" { "type" } else { kind };
                declarations.insert(format!("{kind}.{name}"));
            }
        }
        if let Some(rest) = line.strip_prefix("extern ") {
            let name = rest
                .split('(')
                .next()
                .and_then(|signature| signature.split_whitespace().last())
                .expect("external function name");
            declarations.insert(format!("extern.{name}"));
        }
    }
    assert_eq!(declarations, inventory_ids("stdlib."));
}

#[test]
fn surface_click_word_inventory_is_bidirectional() {
    let implementation = SURFACE_CLICK_WORDS
        .iter()
        .map(|word| (*word).to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        implementation.len(),
        SURFACE_CLICK_WORDS.len(),
        "duplicate word in registry"
    );
    assert_eq!(implementation, inventory_ids("language.word."));

    let reference = fs::read_to_string(root().join("docs/reference/language/grammar.md"))
        .expect("read grammar reference");
    for word in SURFACE_CLICK_WORDS {
        assert!(
            reference.contains(&format!("`{word}`")),
            "Surface Click word `{word}` has no visible word-index entry"
        );
    }
}

#[test]
fn surface_click_form_inventory_is_bidirectional() {
    let implementation = SURFACE_CLICK_FORMS
        .iter()
        .map(|form| (*form).to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        implementation.len(),
        SURFACE_CLICK_FORMS.len(),
        "duplicate Surface Click form in registry"
    );
    let documented = inventory_ids("language.")
        .into_iter()
        .filter(|id| !id.starts_with("word."))
        .collect::<BTreeSet<_>>();
    assert_eq!(implementation, documented);
}

#[test]
fn c0_surface_inventory_is_bidirectional() {
    let implementation = C0_PUBLIC_FORMS
        .iter()
        .map(|form| (*form).to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        implementation.len(),
        C0_PUBLIC_FORMS.len(),
        "duplicate C0 form in registry"
    );
    assert_eq!(implementation, inventory_ids("c0."));
}

#[test]
fn standard_library_declarations_are_exact_source_includes() {
    let source = fs::read_to_string(root().join("stdlib/prelude.click")).expect("read prelude");
    let reference = fs::read_to_string(root().join("docs/reference/library/index.md"))
        .expect("read library reference");
    let mut declaration = String::new();
    let mut depth = 0usize;
    for line in source.lines() {
        let starts = line.starts_with("theorem ")
            || line.starts_with("spec enum ")
            || line.starts_with("function ")
            || line.starts_with("predicate ")
            || line.starts_with("resource ")
            || line.starts_with("abstract resource ")
            || line.starts_with("extern ");
        if declaration.is_empty() && !starts {
            continue;
        }
        if !declaration.is_empty() {
            declaration.push('\n');
        }
        declaration.push_str(line);
        depth += line.chars().filter(|ch| *ch == '{').count();
        depth -= line.chars().filter(|ch| *ch == '}').count();
        let complete =
            depth == 0 && (line.trim_end().ends_with('}') || line.trim_end().ends_with(';'));
        if complete {
            assert!(
                reference.contains(&declaration),
                "library reference has a missing or stale declaration:\n{declaration}"
            );
            declaration.clear();
        }
    }
    assert!(declaration.is_empty(), "unterminated stdlib declaration");
}

#[test]
fn every_standard_library_symbol_has_a_verified_use() {
    let fixture = fs::read_to_string(root().join("mdtests/stdlib_every_symbol.md"))
        .expect("read standard-library fixture");
    assert!(fixture.contains("```expect\npass\n```"));
    for id in inventory_ids("stdlib.") {
        let name = id
            .split_once('.')
            .map(|(_, name)| name)
            .unwrap_or_else(|| panic!("standard-library inventory ID has no kind: {id}"));
        assert!(
            fixture.contains(name),
            "standard-library symbol `{name}` has no use in mdtests/stdlib_every_symbol.md"
        );
    }
}

#[test]
fn tactic_inventory_matches_canonical_surface_names() {
    let source = fs::read_to_string(root().join("src/surface/validation/type_validation.rs"))
        .expect("read tactic names");
    let body = source
        .split("fn tactic_name(")
        .nth(1)
        .expect("tactic_name function")
        .split("pub(super) fn reject_duplicate")
        .next()
        .expect("end of tactic_name function");
    let mut names = BTreeSet::new();
    for segment in body.split("=> \"").skip(1) {
        if let Some(name) = segment.split('"').next() {
            names.insert(name.to_string());
        }
    }
    names.retain(|name| !INTERNAL_TACTICS.contains(&name.as_str()));
    assert_eq!(names, inventory_ids("tactic."));
}

#[test]
fn tactic_form_inventory_is_bidirectional() {
    let implementation = PUBLIC_TACTIC_FORMS
        .iter()
        .map(|form| form.id.to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        implementation.len(),
        PUBLIC_TACTIC_FORMS.len(),
        "duplicate tactic form in registry"
    );
    assert_eq!(implementation, inventory_ids("tactic-form."));

    let reference = fs::read_to_string(root().join("docs/reference/tactics/index.md"))
        .expect("read tactic reference");
    let rows = reference
        .lines()
        .filter(|line| line.starts_with("| `"))
        .filter(|line| line.matches('|').count() >= 6)
        .filter_map(|line| {
            let mut cells = line.split('|').map(str::trim);
            let _empty = cells.next()?;
            Some((cells.next()?, cells.next()?, line))
        })
        .collect::<Vec<_>>();
    for form in PUBLIC_TACTIC_FORMS {
        let matches_surface = |surface: &str| match form.id {
            "step" => surface == "`step()`",
            "apply-induction" => surface == "`apply(ih(m))`",
            "apply-induction-using" => surface == "`apply(ih(m)) using { P; ... }`",
            "apply-theorem" => surface == "`apply(theorem(args))`",
            "apply-theorem-using" => surface == "`apply(theorem(args)) using { P; ... }`",
            "arithmetic" => surface == "`arithmetic()`",
            "normalize" => surface == "`normalize()`",
            "normalize-using" => surface == "`normalize() using { P; ... }`",
            "arithmetic-using" => surface == "`arithmetic() using { P; ... }`",
            "transport" => surface == "`transport(P, Q)`",
            "transport-using" => surface == "`transport(P, Q) using { R; ... }`",
            "instantiate" => surface == "`instantiate(F, value)`",
            "intro" => surface == "`intro()`",
            "simp" => surface == "`simp()`",
            "simp-using" => surface == "`simp() using { P; ... }`",
            "unfold-function" => surface == "`unfold(function(args))`",
            "peel-function" => surface == "`peel(function(args)) using { P; ... }`",
            _ => surface.contains(form.syntax),
        };
        let matching = rows
            .iter()
            .filter(|(surface, _, _)| matches_surface(surface))
            .collect::<Vec<_>>();
        assert!(
            matching.len() == 1,
            "tactic form `{}` must map to exactly one reference row through `{}`; matches: {:?}",
            form.id,
            form.syntax,
            matching.iter().map(|(_, _, row)| row).collect::<Vec<_>>(),
        );
        let &(_, documented_class, row) = matching[0];
        assert_eq!(
            documented_class, form.class,
            "tactic form `{}` has the wrong class in its own reference row: {row}",
            form.id,
        );
    }
}

#[test]
fn simple_tactic_definition_includes_direct_checking_and_performance() {
    let concept = fs::read_to_string(root().join("docs/concepts/smart-and-simple-tactics.md"))
        .expect("read canonical tactic concept");
    let normalized = concept.split_whitespace().collect::<Vec<_>>().join(" ");
    for required in [
        "one deterministic checked operation",
        "without heuristic planning, premise selection, alternative-rule search, or speculative proof branching",
        "Simple checking must also be fast and output-sensitive",
        "approximately all cost that can conveniently be removed by making its choices explicit",
    ] {
        assert!(
            normalized.contains(required),
            "canonical simple-tactic definition lost `{required}`"
        );
    }

    let reference = fs::read_to_string(root().join("docs/reference/tactics/index.md"))
        .expect("read tactic reference");
    let step_row = reference
        .lines()
        .find(|line| line.starts_with("| `step()` |"))
        .expect("tactic reference must contain the step row");
    assert!(
        step_row.starts_with("| `step()` | simple |"),
        "`step()` must remain a simple tactic in the public reference: {step_row}"
    );

    let proof_scripts = fs::read_to_string(root().join("docs/concepts/proof-scripts.md"))
        .expect("read proof-script concept");
    for retired_description in [
        "`step()` for one smart transition",
        "bare `step()`",
        "`step()` is smart",
    ] {
        assert!(
            !proof_scripts.contains(retired_description),
            "proof-script concept classifies simple `step()` as smart through `{retired_description}`"
        );
    }
}

#[test]
fn every_tactic_form_has_a_checked_positive_fixture() {
    let source = fs::read_to_string(root().join("docs/reference/tactics/fixtures.toml"))
        .expect("read tactic fixture inventory");
    let mut fixtures = BTreeMap::new();
    let mut id = None;
    let mut path = None;
    let mut needle = None;
    for line in source.lines().map(str::trim) {
        if line == "[[form]]" {
            if let (Some(id), Some(path), Some(needle)) = (id.take(), path.take(), needle.take()) {
                assert!(
                    fixtures.insert(id, (path, needle)).is_none(),
                    "duplicate tactic fixture"
                );
            }
        } else if let Some(value) = line.strip_prefix("id = ") {
            id = Some(unquote(value));
        } else if let Some(value) = line.strip_prefix("path = ") {
            path = Some(unquote(value));
        } else if let Some(value) = line.strip_prefix("needle = ") {
            needle = Some(unquote(value));
        }
    }
    if let (Some(id), Some(path), Some(needle)) = (id, path, needle) {
        assert!(fixtures.insert(id, (path, needle)).is_none());
    }

    let expected = PUBLIC_TACTIC_FORMS
        .iter()
        .map(|form| form.id.to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(expected, fixtures.keys().cloned().collect());

    for (id, (path, needle)) in fixtures {
        assert!(
            path.starts_with("mdtests/")
                || path.starts_with("src/surface/tests/")
                || path == "tests/cpp_import.rs",
            "tactic fixture `{id}` must use an ordinary checked test source: {path}"
        );
        let fixture = fs::read_to_string(root().join(&path))
            .unwrap_or_else(|error| panic!("tactic fixture `{id}` {path}: {error}"));
        assert!(
            fixture.contains(&needle),
            "tactic fixture `{id}` no longer contains `{needle}` in {path}"
        );
        if path.starts_with("mdtests/") {
            assert!(
                fixture.contains("```expect"),
                "tactic fixture `{id}` has no mdtest expectation in {path}"
            );
            let mut in_click = false;
            let mut checked_click = String::new();
            for line in fixture.lines() {
                if line.split_whitespace().next() == Some("```click") {
                    in_click = true;
                    continue;
                }
                if in_click && line.trim() == "```" {
                    in_click = false;
                    checked_click.push('\n');
                    continue;
                }
                if in_click {
                    checked_click.push_str(line);
                    checked_click.push('\n');
                }
            }
            assert!(
                checked_click.contains(&needle),
                "tactic fixture `{id}` needle occurs outside a checked Click fence in {path}: {needle}"
            );
        } else {
            assert!(
                fixture.contains("#[test]"),
                "tactic fixture `{id}` isn't part of a Rust test file: {path}"
            );
        }
    }
}

/// Proof-object operations with a canonical name but no surface spelling.
const INTERNAL_TACTICS: &[&str] = &["auto", "choose"];

#[test]
fn cli_inventory_matches_argument_parsers() {
    for (command, file) in [
        ("verify", "src/bin/click-verify.rs"),
        ("profile", "src/bin/click-profile.rs"),
        ("expand", "src/bin/click-expand.rs"),
        ("audit", "src/bin/click-audit.rs"),
        ("import", "src/bin/click-import.rs"),
    ] {
        let source = fs::read_to_string(root().join(file)).expect("read CLI source");
        let parser = source
            .split("fn parse_arguments")
            .nth(1)
            .expect("parse_arguments function")
            .split("\nfn ")
            .next()
            .expect("end of parse_arguments function");
        let mut options = quoted_flags(parser);
        options.insert("--help".to_string());
        options.insert("-h".to_string());
        if parser.contains("argument == \"--\"") || parser.contains("\"--\" =>") {
            options.insert("--".to_string());
        }
        let prefix = format!("cli.{command}.");
        let mut documented = inventory_ids(&prefix);
        assert!(documented.remove("command"));
        assert_eq!(
            options, documented,
            "CLI inventory drift for click {command}"
        );
        let reference = fs::read_to_string(root().join(format!("docs/reference/cli/{command}.md")))
            .expect("read CLI reference");
        for option in options {
            assert!(
                reference.contains(&format!("`{option}")),
                "click {command} option `{option}` has no visible reference entry"
            );
        }
    }
}

#[test]
fn cli_behavior_inventory_is_bidirectional() {
    let implementation = PUBLIC_CLI_BEHAVIORS
        .iter()
        .map(|behavior| (*behavior).to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        implementation.len(),
        PUBLIC_CLI_BEHAVIORS.len(),
        "duplicate CLI behavior in registry"
    );
    assert_eq!(implementation, inventory_ids("cli.behavior."));
}

#[test]
fn cli_defaults_are_source_backed() {
    for (command, file) in [
        ("profile", "src/bin/click-profile.rs"),
        ("audit", "src/bin/click-audit.rs"),
    ] {
        let source = fs::read_to_string(root().join(file)).expect("read CLI source");
        let defaults = source
            .split("\ndefaults:\n")
            .nth(1)
            .expect("USAGE defaults block")
            .split("\n\noptions:")
            .next()
            .expect("end of defaults block");
        let reference = fs::read_to_string(root().join(format!("docs/reference/cli/{command}.md")))
            .expect("read CLI reference");
        for line in defaults.lines().map(str::trim) {
            if !line.starts_with("--") {
                continue;
            }
            let mut fields = line.split_whitespace();
            let option = fields.next().expect("default option");
            let value = fields.next().expect("default value");
            assert!(
                reference.contains(&format!("`{option}"))
                    && reference.contains(&format!("`{value}`")),
                "click {command} default `{option} {value}` is absent or stale"
            );
        }
    }

    for (command, limits) in [
        ("verify", RunLimits::verify()),
        ("expand", RunLimits::expand()),
    ] {
        assert_eq!(limits.time, CRASH_CONTAINMENT_TIME_LIMIT);
        let reference = fs::read_to_string(root().join(format!("docs/reference/cli/{command}.md")))
            .expect("read CLI reference");
        let time = format_duration(limits.time);
        assert!(
            reference.contains(&format!("`{time}`")),
            "click {command} default crash-containment bound `{time}` is absent or stale"
        );
        let work = limits.work.to_string();
        assert!(
            reference.contains(&format!("`{work}`")),
            "click {command} default work limit `{work}` is absent or stale"
        );
    }
}

#[test]
fn environment_variable_inventory_is_bidirectional() {
    let implementation = PUBLIC_ENVIRONMENT_VARIABLES
        .iter()
        .map(|variable| (*variable).to_string())
        .collect::<BTreeSet<_>>();
    assert_eq!(
        implementation.len(),
        PUBLIC_ENVIRONMENT_VARIABLES.len(),
        "duplicate environment variable in registry"
    );
    assert_eq!(implementation, inventory_ids("cli.env."));
}

#[test]
fn glossary_inventory_is_bidirectional() {
    let source =
        fs::read_to_string(root().join("docs/reference/glossary.md")).expect("read glossary");
    let terms = source
        .lines()
        .filter_map(|line| line.strip_prefix("### ").map(slug))
        .collect::<BTreeSet<_>>();
    assert_eq!(terms, inventory_ids("glossary."));
}

#[test]
fn public_docs_do_not_make_round_trip_validation_a_verification_phase() {
    let docs = root().join("docs");
    let mut files = Vec::new();
    markdown_files(&docs.join("concepts"), &mut files);
    markdown_files(&docs.join("reference"), &mut files);
    files.sort();

    let retired_claims = [
        "round-trip validation phase",
        "certificate-validation phase",
        "second verification phase",
        "validation interpreter",
    ];
    let glossary = docs.join("reference/glossary.md");
    let mut failures = Vec::new();
    for path in files {
        if path == glossary {
            continue;
        }
        let source = fs::read_to_string(&path).expect("read public documentation page");
        for (line, text) in source.lines().enumerate() {
            let lower = text.to_ascii_lowercase();
            for claim in retired_claims {
                if lower.contains(claim) {
                    failures.push(format!(
                        "{}:{}: replace retired public verification model `{claim}`",
                        path.strip_prefix(&docs)
                            .expect("docs-relative path")
                            .display(),
                        line + 1
                    ));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "round-trip validation described as a separate verification phase:\n{}",
        failures.join("\n")
    );
}

#[test]
fn canonical_documentation_terms_have_no_retired_aliases() {
    let docs = root().join("docs");
    let mut files = Vec::new();
    markdown_files(&docs, &mut files);
    files.sort();

    let retired = [
        "canonical load variable",
        "canonical load variables",
        "canonical name",
        "canonical names",
        // The memory-range fact is `viewable(...)` and its concept page is
        // `docs/concepts/viewability.md`, so no documentation URL spells the
        // old noun any more. The adjective is not retired: the kernel's own
        // `proves_memory_loadable` is still named in internals prose.
        "loadability",
        "loadable(",
        "memory dag",
        "proof frontier",
        "raw load",
        "raw loads",
        "snapshot bridge",
        "snapshot bridging",
    ];
    let mut failures = Vec::new();
    for path in files {
        if path.ends_with("style.md") || path.ends_with("reference/glossary.md") {
            continue;
        }
        let source = fs::read_to_string(&path).expect("read Markdown page");
        let mut in_code_fence = false;
        for (line, text) in source.lines().enumerate() {
            if text.starts_with("```") {
                in_code_fence = !in_code_fence;
                continue;
            }
            if in_code_fence {
                continue;
            }
            let lower = text.to_ascii_lowercase();
            let without_memory_effect_facts = lower
                .replace("memory-effect facts", "")
                .replace("memory-effect fact", "");
            if without_memory_effect_facts.contains("effect fact") {
                failures.push(format!(
                    "{}:{}: qualify `effect fact` as `memory-effect fact` or use `execution fact`",
                    path.strip_prefix(&docs)
                        .expect("docs-relative path")
                        .display(),
                    line + 1
                ));
            }
            for alias in retired {
                if lower.contains(alias) {
                    failures.push(format!(
                        "{}:{}: replace retired term `{alias}`",
                        path.strip_prefix(&docs)
                            .expect("docs-relative path")
                            .display(),
                        line + 1
                    ));
                }
            }
        }
    }
    assert!(
        failures.is_empty(),
        "retired documentation terminology:\n{}",
        failures.join("\n")
    );
}

#[test]
fn implementation_uses_canonical_form_and_load_variable_terms() {
    let repository = root();
    let mut files = Vec::new();
    files_with_extension(&repository.join("src"), "rs", &mut files);
    files_with_extension(&repository.join("design"), "md", &mut files);
    files.sort();

    let retired = [
        "canonical load variable",
        "canonical_load_variable",
        "canonical name",
        "canonical-name",
        "canonical_name",
        "canonical variable",
        "canonical-variable",
        "verification variable",
        "verification_variable",
    ];
    let mut failures = Vec::new();
    for path in files {
        let source = fs::read_to_string(&path).expect("read implementation terminology source");
        let lower = source.to_ascii_lowercase();
        for alias in retired {
            if lower.contains(alias) {
                failures.push(format!(
                    "{}: replace retired term `{alias}`",
                    path.strip_prefix(&repository)
                        .expect("repository-relative path")
                        .display()
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "retired implementation terminology:\n{}",
        failures.join("\n")
    );
}

/// The language reference states current behavior. Changelog phrasing such
/// as "this slice" or "not yet supported" dates the text and hides whether a
/// form is refused or merely undocumented.
#[test]
fn language_reference_states_current_behavior() {
    let repository = root();
    let mut files = Vec::new();
    files_with_extension(
        &repository.join("docs/reference/language"),
        "md",
        &mut files,
    );
    files.sort();
    let phrases = [
        "this slice",
        "outside this slice",
        "initial slice",
        "first-pass",
        "not yet supported",
        "not yet generated",
        "currently supported",
        "currently understand",
    ];
    let mut failures = Vec::new();
    for path in files {
        let text = fs::read_to_string(&path)
            .expect("read language reference")
            .to_ascii_lowercase()
            .split_whitespace()
            .collect::<Vec<_>>()
            .join(" ");
        for phrase in phrases {
            if text.contains(phrase) {
                failures.push(format!(
                    "{}: `{phrase}`",
                    path.strip_prefix(&repository)
                        .expect("repository-relative path")
                        .display()
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "state current behavior instead of changelog phrasing:\n{}",
        failures.join("\n")
    );
}

#[test]
fn retired_execution_engine_terminology_is_absent() {
    let repository = root();
    let mut files = vec![repository.join("AGENTS.md"), repository.join("README.md")];
    for directory in [
        "design", "docs", "examples", "issues", "mdtests", "src", "tests",
    ] {
        for extension in ["c", "click", "md", "rs", "toml"] {
            files_with_extension(&repository.join(directory), extension, &mut files);
        }
    }
    files.sort();

    // Construct the retired word so this regression does not itself preserve it.
    let retired = ["re", "play"].concat();
    let mut failures = Vec::new();
    for path in files {
        let source = fs::read_to_string(&path).expect("read terminology source");
        if source.to_ascii_lowercase().contains(&retired) {
            failures.push(
                path.strip_prefix(&repository)
                    .expect("repository-relative path")
                    .display()
                    .to_string(),
            );
        }
        if path
            .file_name()
            .and_then(|name| name.to_str())
            .is_some_and(|name| name.to_ascii_lowercase().contains(&retired))
        {
            failures.push(format!("{} (filename)", path.display()));
        }
    }
    assert!(
        failures.is_empty(),
        "retired execution-engine terminology remains in:\n{}",
        failures.join("\n")
    );
}

#[test]
fn cli_synopses_are_exact_help_includes() {
    for (command, file) in [
        ("verify", "src/bin/click-verify.rs"),
        ("profile", "src/bin/click-profile.rs"),
        ("expand", "src/bin/click-expand.rs"),
        ("audit", "src/bin/click-audit.rs"),
        ("import", "src/bin/click-import.rs"),
    ] {
        let source = fs::read_to_string(root().join(file)).expect("read CLI source");
        let synopsis = usage_synopsis(&source);
        let reference = fs::read_to_string(root().join(format!("docs/reference/cli/{command}.md")))
            .expect("read CLI reference");
        assert!(
            reference.contains(&synopsis),
            "click {command} synopsis drift; expected exact help text:\n{synopsis}"
        );
    }
}

fn usage_synopsis(source: &str) -> String {
    let after = source
        .split("const USAGE: &str = \"")
        .nth(1)
        .expect("USAGE constant");
    let literal = after.split("\";").next().expect("end of USAGE constant");
    let decoded = literal
        .trim_start_matches('\\')
        .replace("\\n", "\n")
        .replace("\\\n", "");
    decoded
        .split("\n\n")
        .next()
        .expect("USAGE synopsis")
        .to_string()
}

fn quoted_flags(source: &str) -> BTreeSet<String> {
    let mut flags = BTreeSet::new();
    for segment in source.split('"').skip(1).step_by(2) {
        if (segment.starts_with("--") || segment == "-h")
            && segment
                .chars()
                .all(|ch| ch.is_ascii_lowercase() || ch == '-')
        {
            flags.insert(segment.to_string());
        }
    }
    flags
}

#[test]
fn landing_page_identifies_the_ai_reference_and_the_human_guide() {
    let source = fs::read_to_string(root().join("docs/index.md")).expect("read landing page");
    assert!(source.contains("This is the AI reference"));
    assert!(source.contains("Agents maintain it"));
    assert!(source.contains("human-written guide"));
    assert!(source.contains("https://github.com/clicklang/click/tree/master/guide"));
    assert!(
        root().join("guide/README.md").is_file(),
        "the landing page points to guide/"
    );
}

#[test]
fn rendered_site_keyboard_enhancement_is_configured() {
    let book = fs::read_to_string(root().join("book.toml")).expect("read book.toml");
    assert!(book.contains("docs/theme/click.css"));
    assert!(book.contains("docs/theme/click.js"));

    let script = fs::read_to_string(root().join("docs/theme/click.js"))
        .expect("read documentation keyboard enhancement");
    assert!(script.contains("toggle.tabIndex = 0"));
    assert!(script.contains("event.key !== \"Enter\""));
    assert!(script.contains("event.key !== \" \""));
    assert!(script.contains("aria-controls"));
}

#[test]
fn readme_versions_match_the_package_version() {
    let version = env!("CARGO_PKG_VERSION");
    let readme = fs::read_to_string(root().join("README.md")).expect("read README");
    let mut stale = BTreeSet::new();
    for word in readme.split(|c: char| !(c.is_ascii_digit() || c == '.')) {
        let word = word.trim_matches('.');
        let parts: Vec<&str> = word.split('.').collect();
        if parts.len() == 3 && parts.iter().all(|part| !part.is_empty()) && word != version {
            stale.insert(word.to_string());
        }
    }
    assert!(
        stale.is_empty(),
        "README names versions {stale:?}; the package version is {version}"
    );
}

const COVERAGE_STATUSES: [&str; 4] = ["Supported", "Partial", "Not supported", "Not applicable"];
const COVERAGE_LANGUAGES: [&str; 3] = ["C", "C++", "Rust"];

/// Splits a Markdown table row into trimmed cells, or `None` for a
/// non-row or a delimiter row.
fn table_cells(line: &str) -> Option<Vec<&str>> {
    let inner = line.trim().strip_prefix('|')?.strip_suffix('|')?;
    let cells: Vec<&str> = inner.split('|').map(str::trim).collect();
    (!cells
        .iter()
        .all(|cell| cell.chars().all(|c| c == '-' || c == ' ')))
    .then_some(cells)
}

/// Inline-code spans of a cell that name repository fixtures.
fn cited_fixtures(cell: &str) -> Vec<&str> {
    cell.split('`')
        .skip(1)
        .step_by(2)
        .filter(|code| {
            ["mdtests/", "examples/", "integrations/", "tests/"]
                .iter()
                .any(|prefix| code.starts_with(prefix))
        })
        .collect()
}

/// Whether `source` defines `name` as a `#[test]` function. Attribute and
/// comment lines may sit between the attribute and the `fn`.
fn defines_test(source: &str, name: &str) -> bool {
    let lines: Vec<&str> = source.lines().collect();
    let signature = format!("fn {name}(");
    lines.iter().enumerate().any(|(index, line)| {
        line.trim_start().starts_with(&signature)
            && lines[..index]
                .iter()
                .rev()
                .map(|line| line.trim())
                .take_while(|line| line.starts_with("#[") || line.starts_with("//"))
                .any(|line| line == "#[test]")
    })
}

enum Evidence {
    Passing,
    Refusal,
}

/// Resolves one cited fixture, reporting what kind of evidence it is.
fn resolve_fixture(fixture: &str) -> Result<Evidence, String> {
    if let Some((file, test)) = fixture.split_once("::") {
        let source =
            fs::read_to_string(root().join(file)).map_err(|error| format!("{file}: {error}"))?;
        return defines_test(&source, test)
            .then_some(Evidence::Passing)
            .ok_or_else(|| format!("{file} has no #[test] fn {test}"));
    }
    if fixture.starts_with("mdtests/") && fixture.ends_with(".md") {
        let source = fs::read_to_string(root().join(fixture))
            .map_err(|error| format!("{fixture}: {error}"))?;
        let expectation = source
            .split("```expect\n")
            .nth(1)
            .and_then(|rest| rest.lines().next())
            .ok_or_else(|| format!("{fixture} has no expect block"))?;
        return Ok(if expectation.trim() == "pass" {
            Evidence::Passing
        } else {
            Evidence::Refusal
        });
    }
    if fixture.ends_with('/') {
        let mut sidecars = Vec::new();
        let directory = root().join(fixture);
        if directory.is_dir() {
            files_with_extension(&directory, "click", &mut sidecars);
        }
        return (!sidecars.is_empty())
            .then_some(Evidence::Passing)
            .ok_or_else(|| format!("{fixture} is not a directory with a Click sidecar"));
    }
    Err(format!(
        "{fixture} is not an mdtest, fixture directory, or FILE::TEST"
    ))
}

#[test]
fn coverage_matrix_cells_cite_existing_fixtures() {
    let page = "docs/reference/coverage.md";
    let source = fs::read_to_string(root().join(page)).expect("read the coverage matrix");
    let mut failures = Vec::new();
    let mut section = String::new();
    let mut in_matrix = false;
    let mut rows = 0usize;

    for (index, line) in source.lines().enumerate() {
        let at = format!("{page}:{}", index + 1);
        if let Some(heading) = line.strip_prefix("## ") {
            section = heading.to_string();
            in_matrix = false;
            continue;
        }
        let Some(cells) = table_cells(line) else {
            if !line.starts_with('|') {
                in_matrix = false;
            }
            continue;
        };
        if cells[1..] == COVERAGE_LANGUAGES {
            in_matrix = true;
            continue;
        }
        if !in_matrix {
            continue;
        }
        rows += 1;
        if cells.len() != 1 + COVERAGE_LANGUAGES.len() {
            failures.push(format!("{at}: row has {} cells", cells.len()));
            continue;
        }
        for (language, cell) in COVERAGE_LANGUAGES.iter().zip(&cells[1..]) {
            let Some(status) = COVERAGE_STATUSES
                .iter()
                .find(|status| cell.starts_with(*status))
            else {
                failures.push(format!("{at}: {language} cell has no status: {cell}"));
                continue;
            };
            let fixtures = cited_fixtures(cell);
            let needs_evidence = matches!(*status, "Supported" | "Partial");
            if needs_evidence && fixtures.is_empty() {
                failures.push(format!("{at}: {language} {status} cell cites no fixture"));
            }
            let mut passing = false;
            for fixture in fixtures {
                match resolve_fixture(fixture) {
                    Ok(Evidence::Passing) => passing = true,
                    Ok(Evidence::Refusal) => {}
                    Err(error) => failures.push(format!("{at}: {language}: {error}")),
                }
            }
            let refusals_suffice = section == "Runtime errors checked";
            if needs_evidence && !refusals_suffice && !passing {
                failures.push(format!(
                    "{at}: {language} {status} cell needs a passing fixture outside the runtime-error table"
                ));
            }
        }
    }

    assert!(
        rows >= 60,
        "coverage matrix unexpectedly has only {rows} rows"
    );
    assert!(
        failures.is_empty(),
        "coverage matrix evidence is stale:\n{}",
        failures.join("\n")
    );
}

#[test]
fn language_support_summaries_link_to_the_coverage_matrix() {
    let docs = root().join("docs");
    let summaries = [
        "index.md",
        "concepts/what-click-proves.md",
        "reference/language/limitations.md",
        "reference/language/c.md",
        "reference/rust.md",
        "reference/cli/import.md",
    ];
    let no_type_lists = [
        "concepts/what-click-proves.md",
        "reference/language/limitations.md",
    ];
    let scalar_names = [
        "int8", "int16", "int32", "int64", "uint8", "uint16", "uint32", "uint64",
    ];
    let mut failures = Vec::new();

    for page in summaries {
        let source = fs::read_to_string(docs.join(page)).expect("read summary page");
        if !markdown_links(&source).iter().any(|link| {
            link.split('#')
                .next()
                .is_some_and(|path| path.ends_with("coverage.md"))
        }) {
            failures.push(format!("{page}: link to the language coverage matrix"));
        }
        if !no_type_lists.contains(&page) {
            continue;
        }
        let mut in_code_fence = false;
        for (line, text) in source.lines().enumerate() {
            if text.starts_with("```") {
                in_code_fence = !in_code_fence;
                continue;
            }
            let named = scalar_names
                .iter()
                .filter(|name| text.contains(&format!("`{name}`")))
                .count();
            if !in_code_fence && named >= 3 {
                failures.push(format!(
                    "{page}:{}: scalar type list duplicates the coverage matrix",
                    line + 1
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "support summaries diverge from the coverage matrix:\n{}",
        failures.join("\n")
    );
}

#[test]
fn public_pages_say_supported_c_not_c0() {
    let docs = root().join("docs");
    let mut pages = vec![docs.join("index.md")];
    markdown_files(&docs.join("concepts"), &mut pages);
    markdown_files(&docs.join("reference"), &mut pages);
    pages.sort();
    let mut failures = Vec::new();
    for page in pages {
        // The glossary entry explains the historical name.
        if page.ends_with("reference/glossary.md") {
            continue;
        }
        let source = fs::read_to_string(&page).expect("read public page");
        let mut in_code_fence = false;
        for (line, text) in source.lines().enumerate() {
            if text.starts_with("```") {
                in_code_fence = !in_code_fence;
                continue;
            }
            if in_code_fence {
                continue;
            }
            // Drop inline code, then look for `C0` as a whole word.
            let prose: String = text.split('`').step_by(2).collect::<Vec<_>>().join(" ");
            let words = prose.split(|c: char| !(c.is_ascii_alphanumeric() || c == '_'));
            if words.into_iter().any(|word| word == "C0") {
                failures.push(format!(
                    "{}:{}: say `supported C` instead of `C0`",
                    page.strip_prefix(&docs)
                        .expect("docs-relative path")
                        .display(),
                    line + 1
                ));
            }
        }
    }
    assert!(
        failures.is_empty(),
        "retired term C0:\n{}",
        failures.join("\n")
    );
}
