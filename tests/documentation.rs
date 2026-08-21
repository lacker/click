use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Debug)]
struct InventoryItem {
    id: String,
    path: String,
}

fn root() -> PathBuf {
    PathBuf::from(env!("CARGO_MANIFEST_DIR"))
}

fn markdown_files(directory: &Path, files: &mut Vec<PathBuf>) {
    for entry in fs::read_dir(directory).expect("read docs directory") {
        let path = entry.expect("read docs entry").path();
        if path.is_dir() {
            markdown_files(&path, files);
        } else if path.extension().and_then(|value| value.to_str()) == Some("md") {
            files.push(path);
        }
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
    }
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
