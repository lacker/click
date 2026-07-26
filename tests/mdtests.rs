use std::fs;
use std::path::{Path, PathBuf};

use click::lang::click::verify_c0_sources;

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
    if let Ok(filter) = std::env::var("MDTEST_FILTER") {
        paths.retain(|path| {
            path.file_name()
                .is_some_and(|name| name.to_string_lossy().contains(&filter))
        });
    }
    paths.sort();

    assert!(
        !paths.is_empty(),
        "expected at least one mdtest in `{}`",
        mdtests_dir.display()
    );

    for path in paths {
        run_mdtest(&path);
    }
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
