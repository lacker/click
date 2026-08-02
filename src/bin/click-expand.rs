use std::env;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use click::cli::{
    BoundedOutput, MdTest, format_duration, looks_like_mdtest, parse_duration,
    parse_source_location, read_mdtest, read_verifying_sources, run_bounded, source_refs,
};
use click::lang::click::expand_c0_tactic_source_at;

const DEFAULT_TIME_LIMIT: Duration = Duration::from_secs(60);

const USAGE: &str =
    "usage: click-expand [--time-limit <DURATION>] <sidecar.click|mdtest.md>:<line>:<column>\n\nThe expansion is bounded to 60s by default; --time-limit overrides it.";

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
    child: bool,
}

fn entry() -> Result<(), String> {
    let raw = env::args().skip(1).collect::<Vec<_>>();
    if matches!(raw.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let arguments = parse_arguments(raw)?;
    if arguments.child {
        run(&arguments)
    } else {
        run_with_time_limit(&arguments, arguments.time_limit)
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut positional = Vec::new();
    let mut time_limit = None;
    let mut child = false;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if argument == "--child" {
            child = true;
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
    Ok(Arguments {
        click_path,
        line,
        column,
        time_limit: time_limit.unwrap_or(DEFAULT_TIME_LIMIT),
        child,
    })
}

fn run_with_time_limit(arguments: &Arguments, time_limit: Duration) -> Result<(), String> {
    let executable = env::current_exe()
        .map_err(|error| format!("failed to locate click-expand executable: {error}"))?;
    let mut command = Command::new(executable);
    command.arg("--child").arg(format!(
        "{}:{}:{}",
        arguments.click_path.display(),
        arguments.line,
        arguments.column
    ));
    let output = match run_bounded(command, time_limit, "timed expansion")? {
        BoundedOutput::TimedOut { stderr, .. } => {
            let diagnostics = String::from_utf8_lossy(&stderr);
            let diagnostics = diagnostics.trim();
            return Err(if diagnostics.is_empty() {
                format!("time limit of {} exceeded", format_duration(time_limit))
            } else {
                format!(
                    "time limit of {} exceeded\nlast diagnostics:\n{}",
                    format_duration(time_limit),
                    diagnostics
                )
            });
        }
        BoundedOutput::Completed(output) => output,
    };
    if !output.status.success() {
        let message = String::from_utf8_lossy(&output.stderr);
        let message = message
            .trim()
            .strip_prefix("click-expand: ")
            .unwrap_or(message.trim());
        return Err(if message.is_empty() {
            format!("timed expansion exited with {}", output.status)
        } else {
            message.to_string()
        });
    }
    std::io::stdout()
        .write_all(&output.stdout)
        .map_err(|error| format!("failed to write expanded source: {error}"))?;
    std::io::stderr()
        .write_all(&output.stderr)
        .map_err(|error| format!("failed to write expansion diagnostics: {error}"))?;
    Ok(())
}

fn run(arguments: &Arguments) -> Result<(), String> {
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
    let expanded =
        expand_c0_tactic_source_at(&click_source, &sources, arguments.line, arguments.column)
            .map_err(|error| error.message().to_string())?;
    print!("{expanded}");
    Ok(())
}

/// Expands a tactic inside an mdtest's ```click block. The location is given
/// in `.md` file coordinates — the same coordinates click-profile reports —
/// and the output is the whole markdown file with the block's body replaced,
/// so the same redirect workflow as sidecar expansion applies.
fn run_mdtest(arguments: &Arguments) -> Result<(), String> {
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
    let click_line = mdtest_click_line(&mdtest, click_source, arguments.line)?;
    let sources = source_refs(&mdtest.c_sources);
    let expanded =
        expand_c0_tactic_source_at(click_source, &sources, click_line, arguments.column)
            .map_err(|error| error.message().to_string())?;
    print!(
        "{}",
        spliced_markdown(&markdown, &mdtest, click_source, &expanded)
    );
    Ok(())
}

/// Translates a one-based `.md` line into a one-based line of the ```click
/// block's body, rejecting positions outside the block.
fn mdtest_click_line(mdtest: &MdTest, click_source: &str, md_line: usize) -> Result<usize, String> {
    let first = mdtest.click_start_line;
    let last = first + click_source.lines().count().saturating_sub(1);
    if md_line < first || md_line > last {
        return Err(format!(
            "line {md_line} is not inside the ```click block (lines {first}..{last})"
        ));
    }
    Ok(md_line - first + 1)
}

/// The markdown file with the ```click block's body replaced by `expanded`.
fn spliced_markdown(markdown: &str, mdtest: &MdTest, click_source: &str, expanded: &str) -> String {
    let lines = markdown.lines().collect::<Vec<_>>();
    let body_start = mdtest.click_start_line - 1;
    let body_len = click_source.lines().count();
    let mut spliced = Vec::with_capacity(lines.len());
    spliced.extend_from_slice(&lines[..body_start]);
    spliced.extend(expanded.lines());
    spliced.extend_from_slice(&lines[body_start + body_len..]);
    let mut result = spliced.join("\n");
    if markdown.ends_with('\n') {
        result.push('\n');
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
        assert!(!before.child);
        let default = parse_arguments(["example.click:12:5".to_string()])
            .expect("the default expansion should be bounded");
        assert_eq!(default.time_limit, DEFAULT_TIME_LIMIT);
    }

    #[test]
    fn translates_md_lines_into_the_click_block_and_rejects_outsiders() {
        let markdown = "# title\n\n```click\nproof p {\n  step;\n}\n```\n\ndone\n";
        let mdtest = click::cli::parse_mdtest(std::path::Path::new("t.md"), markdown)
            .expect("mdtest should parse");
        let click_source = mdtest.click_source.as_deref().expect("has click block");
        // Block body is md lines 4..6.
        assert_eq!(mdtest_click_line(&mdtest, click_source, 4), Ok(1));
        assert_eq!(mdtest_click_line(&mdtest, click_source, 5), Ok(2));
        assert_eq!(mdtest_click_line(&mdtest, click_source, 6), Ok(3));
        assert!(mdtest_click_line(&mdtest, click_source, 3).is_err());
        assert!(mdtest_click_line(&mdtest, click_source, 7).is_err());
    }

    #[test]
    fn splices_the_expanded_block_back_into_the_markdown() {
        let markdown = "# title\n\n```click\nproof p {\n  step;\n}\n```\n\ndone\n";
        let mdtest = click::cli::parse_mdtest(std::path::Path::new("t.md"), markdown)
            .expect("mdtest should parse");
        let click_source = mdtest.click_source.as_deref().expect("has click block");
        let expanded = "proof p {\n  step one;\n  step two;\n}\n";
        assert_eq!(
            spliced_markdown(markdown, &mdtest, click_source, expanded),
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
}
