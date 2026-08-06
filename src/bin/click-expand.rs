use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::sync::atomic::{AtomicU64, Ordering};
use std::time::Duration;

use click::cli::{
    DEFAULT_EXPANSION_TIME_LIMIT, looks_like_mdtest, parse_duration, parse_source_location,
    read_mdtest, read_verifying_sources, source_refs,
};
use click::lang::click::{
    c0_smart_tactic_source_sites, c0_tactic_source_position, expand_c0_tactic_source_at,
    verify_c0_sources_at,
};

const USAGE: &str = "usage: click expand [--time-limit <DURATION>] [--output <PATH> | --in-place] <sidecar.click|mdtest.md>:<line>:<column>\n\nExpansion is checked before output. With --in-place, the original is atomically replaced only after targeted verification succeeds.";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-expand: {message}");
        std::process::exit(1);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    click_path: PathBuf,
    line: usize,
    column: usize,
    time_limit: Duration,
    output: Option<PathBuf>,
    in_place: bool,
}

fn entry() -> Result<(), String> {
    entry_with(env::args().skip(1))
}

pub(crate) fn entry_with(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let raw = arguments.into_iter().collect::<Vec<_>>();
    if matches!(raw.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let arguments = parse_arguments(raw)?;
    let expanded = run(&arguments)?;
    if arguments.in_place {
        atomic_replace(&arguments.click_path, expanded.as_bytes())
    } else if let Some(output) = &arguments.output {
        fs::write(output, expanded)
            .map_err(|error| format!("failed to write `{}`: {error}", output.display()))
    } else {
        print!("{expanded}");
        Ok(())
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut positional = Vec::new();
    let mut time_limit = None;
    let mut output = None;
    let mut in_place = false;
    let mut parse_options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if parse_options && argument == "--" {
            parse_options = false;
        } else if !parse_options {
            positional.push(argument);
        } else if argument == "--output" {
            if output.is_some() {
                return Err("`--output` may only be supplied once".to_string());
            }
            output =
                Some(PathBuf::from(arguments.next().ok_or_else(|| {
                    format!("missing path after `--output`\n{USAGE}")
                })?));
        } else if argument == "--in-place" {
            in_place = true;
        } else if argument == "--time-limit" {
            if time_limit.is_some() {
                return Err("`--time-limit` may only be supplied once".to_string());
            }
            let duration = arguments
                .next()
                .ok_or_else(|| format!("missing duration after `--time-limit`\n{USAGE}"))?;
            time_limit = Some(parse_duration(&duration)?);
        } else if argument.starts_with('-') {
            return Err(format!("unknown option `{argument}`\n{USAGE}"));
        } else {
            positional.push(argument);
        }
    }
    let (click_path, line, column) = match positional.as_slice() {
        [location] => parse_source_location(location)?,
        _ => return Err(USAGE.to_string()),
    };
    if in_place && output.is_some() {
        return Err("`--output` and `--in-place` cannot be combined".to_string());
    }
    Ok(Arguments {
        click_path,
        line,
        column,
        time_limit: time_limit.unwrap_or(DEFAULT_EXPANSION_TIME_LIMIT),
        output,
        in_place,
    })
}

fn run(arguments: &Arguments) -> Result<String, String> {
    if looks_like_mdtest(&arguments.click_path) {
        return run_mdtest(arguments);
    }
    let click_source = fs::read_to_string(&arguments.click_path).map_err(|error| {
        format!(
            "failed to read `{}`: {error}",
            arguments.click_path.display()
        )
    })?;
    let owned_sources = read_verifying_sources(&arguments.click_path, &click_source)?;
    let sources = source_refs(&owned_sources);
    let (claim, expanded) = generate_expansion(arguments.time_limit, || {
        let claim = selected_claim(&click_source, &sources, arguments.line, arguments.column)?;
        let expanded =
            expand_c0_tactic_source_at(&click_source, &sources, arguments.line, arguments.column)
                .map_err(|error| error.message().to_string())?;
        Ok((claim, expanded))
    })?;
    verify_expansion(&expanded, &sources, &claim, arguments.time_limit)?;
    Ok(expanded)
}

/// Expands a tactic inside an mdtest's ```click block. The location is given
/// in `.md` file coordinates — the same coordinates `click profile` reports —
/// and the output is the whole markdown file with the block's body replaced,
/// so the same redirect workflow as sidecar expansion applies.
fn run_mdtest(arguments: &Arguments) -> Result<String, String> {
    let markdown = fs::read_to_string(&arguments.click_path).map_err(|error| {
        format!(
            "failed to read `{}`: {error}",
            arguments.click_path.display()
        )
    })?;
    let mdtest = read_mdtest(&arguments.click_path)?;
    let click_source = mdtest.click_source.as_deref().ok_or_else(|| {
        format!(
            "mdtest `{}` has no ```click block",
            arguments.click_path.display()
        )
    })?;
    let click_line = mdtest.click_line(arguments.line)?;
    let sources = source_refs(&mdtest.c_sources);
    let (claim, expanded) = generate_expansion(arguments.time_limit, || {
        let claim = selected_claim(click_source, &sources, click_line, arguments.column)?;
        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, click_line, arguments.column)
                .map_err(|error| error.message().to_string())?;
        Ok((claim, expanded))
    })?;
    verify_expansion(&expanded, &sources, &claim, arguments.time_limit)?;
    mdtest.replace_click_source(&markdown, &expanded)
}

fn generate_expansion<R>(
    time_limit: Duration,
    operation: impl FnOnce() -> Result<R, String>,
) -> Result<R, String> {
    click::instrumentation::with_deadline(time_limit, || {
        click::instrumentation::with_tactic_limits(
            click::instrumentation::TacticLimits {
                smart: time_limit,
                ..click::instrumentation::TacticLimits::default()
            },
            || {
                let result = operation()?;
                check_expansion_deadline("generating the selected tactic certificate")?;
                Ok(result)
            },
        )
    })
}

fn check_expansion_deadline(stage: &str) -> Result<(), String> {
    if click::instrumentation::deadline_exceeded() {
        Err(format!("expansion time limit exceeded while {stage}"))
    } else {
        Ok(())
    }
}

fn selected_claim(
    click_source: &str,
    sources: &[(&str, &str)],
    line: usize,
    column: usize,
) -> Result<String, String> {
    c0_smart_tactic_source_sites(click_source, sources)
        .map_err(|error| error.message().to_string())?
        .into_iter()
        .find_map(|site| {
            let position = c0_tactic_source_position(
                click_source,
                sources,
                &site.claim_label,
                site.source_index,
            )
            .ok()?;
            (position.line == line && position.column == column).then_some(site.claim_label)
        })
        .ok_or_else(|| "source location does not select a smart tactic".to_string())
}

fn verify_expansion(
    expanded: &str,
    sources: &[(&str, &str)],
    claim: &str,
    time_limit: Duration,
) -> Result<(), String> {
    click::instrumentation::with_deadline(time_limit, || {
        let position = c0_tactic_source_position(expanded, sources, claim, 0)
            .map_err(|error| error.message().to_string())?;
        verify_c0_sources_at(expanded, sources, position.line, position.column)
            .map(|_| ())
            .map_err(|error| format!("expanded proof did not verify: {}", error.message()))
    })
}

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

fn atomic_replace(path: &Path, contents: &[u8]) -> Result<(), String> {
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    let name = path
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or("click-source");
    let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
    let temporary = parent.join(format!(
        ".{name}.click-expand-{}-{sequence}",
        std::process::id()
    ));
    let result = (|| {
        let mut file = fs::OpenOptions::new()
            .write(true)
            .create_new(true)
            .open(&temporary)
            .map_err(|error| format!("failed to create `{}`: {error}", temporary.display()))?;
        file.write_all(contents)
            .and_then(|_| file.sync_all())
            .map_err(|error| format!("failed to write `{}`: {error}", temporary.display()))?;
        fs::rename(&temporary, path).map_err(|error| {
            format!(
                "failed to atomically replace `{}` from `{}`: {error}",
                path.display(),
                temporary.display()
            )
        })
    })();
    if result.is_err() {
        let _ = fs::remove_file(&temporary);
    }
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_time_limit_before_or_after_positionals() {
        let before =
            parse_arguments(["--time-limit", "30s", "example.click:12:5"].map(str::to_string))
                .expect("leading time limit should parse");
        let after =
            parse_arguments(["example.click:12:5", "--time-limit", "30s"].map(str::to_string))
                .expect("trailing time limit should parse");

        assert_eq!(before, after);
        assert_eq!(before.time_limit, Duration::from_secs(30));
        assert_eq!(before.output, None);
        assert!(!before.in_place);
        let default = parse_arguments(["example.click:12:5".to_string()])
            .expect("the default expansion should be bounded");
        assert_eq!(default.time_limit, DEFAULT_EXPANSION_TIME_LIMIT);
    }

    #[test]
    fn reports_an_expired_expansion_deadline_directly() {
        let error = click::instrumentation::with_deadline(Duration::ZERO, || {
            check_expansion_deadline("replaying a generated certificate")
        })
        .expect_err("an expired expansion deadline should fail directly");

        assert_eq!(
            error,
            "expansion time limit exceeded while replaying a generated certificate"
        );
    }

    #[test]
    fn translates_md_lines_into_the_click_block_and_rejects_outsiders() {
        let markdown = "# title\n\n```click\nproof p {\n  step;\n}\n```\n\ndone\n";
        let mdtest = click::cli::parse_mdtest(std::path::Path::new("t.md"), markdown)
            .expect("mdtest should parse");
        // Block body is md lines 4..6.
        assert_eq!(mdtest.click_line(4), Ok(1));
        assert_eq!(mdtest.click_line(5), Ok(2));
        assert_eq!(mdtest.click_line(6), Ok(3));
        assert!(mdtest.click_line(3).is_err());
        assert!(mdtest.click_line(7).is_err());
    }

    #[test]
    fn splices_the_expanded_block_back_into_the_markdown() {
        let markdown = "# title\n\n```click\nproof p {\n  step;\n}\n```\n\ndone\n";
        let mdtest = click::cli::parse_mdtest(std::path::Path::new("t.md"), markdown)
            .expect("mdtest should parse");
        let expanded = "proof p {\n  step one;\n  step two;\n}\n";
        assert_eq!(
            mdtest.replace_click_source(markdown, expanded).unwrap(),
            "# title\n\n```click\nproof p {\n  step one;\n  step two;\n}\n```\n\ndone\n"
        );
    }

    #[test]
    fn parses_source_location_with_colons_in_path() {
        let arguments = parse_arguments(
            ["volume:name/example.click:12:7", "--time-limit", "30s"].map(str::to_string),
        )
        .expect("source location should parse");

        assert_eq!(
            arguments.click_path,
            PathBuf::from("volume:name/example.click")
        );
        assert_eq!(arguments.line, 12);
        assert_eq!(arguments.column, 7);
        assert_eq!(arguments.time_limit, Duration::from_secs(30));
    }

    #[test]
    fn end_of_options_accepts_a_dash_prefixed_location() {
        let arguments = parse_arguments(["--", "-example.click:2:3"].map(str::to_string)).unwrap();
        assert_eq!(arguments.click_path, PathBuf::from("-example.click"));
    }

    #[test]
    fn run_expands_selected_unit_despite_unrelated_broken_proof() {
        let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let directory = env::temp_dir().join(format!(
            "click-expand-isolation-{}-{sequence}",
            std::process::id()
        ));
        fs::create_dir(&directory).unwrap();
        let good_c = "int32 good(int32 x) { return x; }";
        let bad_c = "int32 bad(int32 x) { return x; }";
        let click_source = r#"verifying "good.c";
verifying "bad.c";
int32 good(int32 x) {
    ensures result == x by { execute(); simp(); }
}
int32 bad(int32 x) {
    ensures result == x + 1 by simp;
}
"#;
        let click_path = directory.join("project.click");
        fs::write(directory.join("good.c"), good_c).unwrap();
        fs::write(directory.join("bad.c"), bad_c).unwrap();
        fs::write(&click_path, click_source).unwrap();
        let sources = [("good.c", good_c), ("bad.c", bad_c)];
        let position = c0_tactic_source_position(click_source, &sources, "good.ensures_0", 0)
            .expect("selected tactic should have a source position");
        let arguments = Arguments {
            click_path,
            line: position.line,
            column: position.column,
            time_limit: DEFAULT_EXPANSION_TIME_LIMIT,
            output: None,
            in_place: false,
        };

        let expanded = run(&arguments)
            .expect("the command should ignore an unrelated broken proof during expansion");

        assert_ne!(expanded, click_source);
        assert!(
            expanded.ends_with("int32 bad(int32 x) {\n    ensures result == x + 1 by simp;\n}\n")
        );
        fs::remove_dir_all(directory).unwrap();
    }
}
