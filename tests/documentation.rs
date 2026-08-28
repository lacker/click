use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

use click::cli::{
    DEFAULT_EXPANSION_TIME_LIMIT, DEFAULT_VERIFY_TIME_LIMIT, PUBLIC_CLI_BEHAVIORS,
    PUBLIC_ENVIRONMENT_VARIABLES, format_duration,
};
use click::lang::c::syntax::C0_PUBLIC_FORMS;
use click::lang::click::{PUBLIC_TACTIC_FORMS, SURFACE_CLICK_FORMS, SURFACE_CLICK_WORDS};

#[derive(Debug)]
struct InventoryItem {
    id: String,
    path: String,
}

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
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
            if let Some(requested_anchor) = requested_anchor {
                if !anchors(&target_source).contains(requested_anchor) {
                    failures.push(format!(
                        "{}: link {link} has no matching anchor",
                        path.display()
                    ));
                }
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
fn normative_technical_examples_are_backed_by_mdtests() {
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
            if !fixture.starts_with("mdtests/") || !fixture.ends_with(".md") {
                failures.push(format!(
                    "{}:{}: verified example must name an mdtests/*.md fixture: {fixture}",
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
            assert!(
                fixture_source.contains("```click") && fixture_source.contains("```expect"),
                "{fixture}: documentation fixtures must contain Click source and an expected result"
            );
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
        for kind in ["theorem", "function", "predicate", "resource"] {
            if let Some(rest) = line.strip_prefix(&format!("{kind} ")) {
                let name = rest
                    .split(|ch: char| ch == '(' || ch.is_whitespace())
                    .next()
                    .expect("declaration name");
                declarations.insert(format!("{kind}.{name}"));
            }
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
            || line.starts_with("function ")
            || line.starts_with("predicate ")
            || line.starts_with("resource ")
            || line.starts_with("abstract resource ");
        if declaration.is_empty() && !starts {
            continue;
        }
        if !declaration.is_empty() {
            declaration.push('\n');
        }
        declaration.push_str(line);
        depth += line.chars().filter(|ch| *ch == '{').count();
        depth -= line.chars().filter(|ch| *ch == '}').count();
        let complete = (depth == 0 && line.trim_end().ends_with('}'))
            || (depth == 0 && line.trim_end().ends_with(';'));
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
    let source = fs::read_to_string(root().join("src/lang/click/validation/type_validation.rs"))
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
    let documented = inventory_ids("tactic.");
    let active = documented
        .into_iter()
        .filter(|name| !RETIRED_TACTICS.contains(&name.as_str()))
        .collect::<BTreeSet<_>>();
    assert_eq!(names, active);
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
    for form in PUBLIC_TACTIC_FORMS {
        assert!(
            reference.contains(form.syntax),
            "tactic form `{}` is missing canonical syntax `{}`",
            form.id,
            form.syntax
        );
        assert!(
            reference.contains(form.class),
            "tactic form `{}` is missing class `{}`",
            form.id,
            form.class
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
            path.starts_with("mdtests/") || path.starts_with("src/lang/click/tests/"),
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
        } else {
            assert!(
                fixture.contains("#[test]"),
                "tactic fixture `{id}` isn't part of a Rust test file: {path}"
            );
        }
    }
}

const RETIRED_TACTICS: &[&str] = &[
    "conjunction",
    "apply_loop_summary",
    "summarize",
    "execute_rest",
    "symbolic_execute",
    "execute_step",
    "execute_then_step",
    "execute_else_step",
    "bounded_execute",
    "calculate",
    "double_negation",
    "vacuous",
];

#[test]
fn cli_inventory_matches_argument_parsers() {
    for (command, file) in [
        ("verify", "src/bin/click-verify.rs"),
        ("profile", "src/bin/click-profile.rs"),
        ("expand", "src/bin/click-expand.rs"),
        ("audit", "src/bin/click-audit.rs"),
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

    for (command, default) in [
        ("verify", DEFAULT_VERIFY_TIME_LIMIT),
        ("expand", DEFAULT_EXPANSION_TIME_LIMIT),
    ] {
        let reference = fs::read_to_string(root().join(format!("docs/reference/cli/{command}.md")))
            .expect("read CLI reference");
        let default = format_duration(default);
        assert!(
            reference.contains(&format!("`{default}`")),
            "click {command} default time limit `{default}` is absent or stale"
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
        "effect fact",
        "effect facts",
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
fn technical_landing_page_discloses_ai_authorship() {
    let source = fs::read_to_string(root().join("docs/index.md")).expect("read landing page");
    assert!(source.contains("written and maintained by AI"));
    assert!(source.contains("human-written guide"));
    assert!(source.contains("accurate, exhaustive, and mechanically checked"));
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
