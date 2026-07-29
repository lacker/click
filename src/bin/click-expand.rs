use std::env;
use std::fs;
use std::io::Write;
use std::path::PathBuf;
use std::process::Command;
use std::time::Duration;

use click::cli::{
    BoundedOutput, format_duration, parse_duration, parse_source_location, read_verifying_sources,
    run_bounded, source_refs,
};
use click::lang::click::expand_c0_tactic_source_at;

const USAGE: &str = "usage: click-expand [--time-limit <DURATION>] <sidecar.click>:<line>:<column>";

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
    time_limit: Option<Duration>,
}

fn entry() -> Result<(), String> {
    let raw = env::args().skip(1).collect::<Vec<_>>();
    if matches!(raw.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let arguments = parse_arguments(raw)?;
    if let Some(time_limit) = arguments.time_limit {
        run_with_time_limit(&arguments, time_limit)
    } else {
        run(&arguments)
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut positional = Vec::new();
    let mut time_limit = None;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if argument == "--time-limit" {
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
        time_limit,
    })
}

fn run_with_time_limit(arguments: &Arguments, time_limit: Duration) -> Result<(), String> {
    let executable = env::current_exe()
        .map_err(|error| format!("failed to locate click-expand executable: {error}"))?;
    let mut command = Command::new(executable);
    command.arg(format!(
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
        assert_eq!(before.time_limit, Some(Duration::from_secs(30)));
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
        assert_eq!(arguments.time_limit, Some(Duration::from_secs(30)));
    }
}
