use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::Duration;

use click::cli::{
    files_with_extension, find_projects, format_duration, looks_like_source_location,
    parse_duration, parse_source_location, read_verifying_sources, source_refs,
};
use click::lang::click::{verify_c0_sources, verify_c0_sources_at};

const USAGE: &str = "\
usage: click verify [--time-limit <DURATION>] <sidecar.click>[:<line>:<column>]
       click verify [--time-limit <DURATION>] <project-directory|examples-directory>

Verifies the whole sidecar, or, when a one-based :LINE:COLUMN suffix is
supplied, only the proof unit containing that source location and the C
functions it calls.

Given a directory, verifies every sidecar in it: either the project directory
itself when it holds sidecars, or each immediate subdirectory that does. This
is the command to run after applying an expansion emitted by `click expand`.
Each sidecar has a 30-second limit by default.";

const DEFAULT_TIME_LIMIT: Duration = Duration::from_secs(30);

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    target: String,
    time_limit: Duration,
}

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-verify: {message}");
        std::process::exit(1);
    }
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
    if looks_like_source_location(&arguments.target) {
        let (click_path, line, column) = parse_source_location(&arguments.target)?;
        return verify_location(&click_path, line, column, arguments.time_limit);
    }
    let path = Path::new(&arguments.target);
    if path.is_dir() {
        verify_directory(path, arguments.time_limit)
    } else {
        verify_file(path, arguments.time_limit)
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut target = None;
    let mut time_limit = DEFAULT_TIME_LIMIT;
    let mut parse_options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if parse_options && argument == "--" {
            parse_options = false;
        } else if parse_options && argument == "--time-limit" {
            let value = arguments
                .next()
                .ok_or_else(|| format!("missing duration after `--time-limit`\n{USAGE}"))?;
            time_limit = parse_duration(&value)?;
        } else if parse_options && argument.starts_with('-') {
            return Err(format!("unknown option `{argument}`\n{USAGE}"));
        } else if target.replace(argument).is_some() {
            return Err(USAGE.to_string());
        }
    }
    Ok(Arguments {
        target: target.ok_or_else(|| USAGE.to_string())?,
        time_limit,
    })
}

/// Verifies every sidecar under a project or examples directory, reporting
/// each one as it passes so a long run shows progress.
fn verify_directory(path: &Path, time_limit: Duration) -> Result<(), String> {
    let projects = find_projects(path)?;
    let mut sidecars = Vec::new();
    for project in &projects {
        let mut project_sidecars = files_with_extension(project, "click")?;
        project_sidecars.sort();
        sidecars.append(&mut project_sidecars);
    }
    if sidecars.is_empty() {
        return Err(format!(
            "`{}` contains no Click sidecars to verify",
            path.display()
        ));
    }
    for sidecar in &sidecars {
        verify_file(sidecar, time_limit)?;
        println!("verified {}", display_path(sidecar, path));
    }
    println!(
        "verified {} sidecar{} in {} project{}",
        sidecars.len(),
        plural(sidecars.len()),
        projects.len(),
        plural(projects.len())
    );
    Ok(())
}

/// Shows a discovered sidecar relative to the directory the user named, since
/// project discovery canonicalizes to absolute paths.
fn display_path(sidecar: &Path, root: &Path) -> String {
    let Ok(root) = fs::canonicalize(root) else {
        return sidecar.display().to_string();
    };
    let relative = sidecar.strip_prefix(&root).unwrap_or(sidecar);
    let shown: PathBuf = if relative == sidecar {
        sidecar.to_path_buf()
    } else {
        root.file_name().map_or_else(
            || relative.to_path_buf(),
            |name| Path::new(name).join(relative),
        )
    };
    shown.display().to_string()
}

fn plural(count: usize) -> &'static str {
    if count == 1 { "" } else { "s" }
}

fn verify_file(click_path: &Path, time_limit: Duration) -> Result<(), String> {
    click::instrumentation::with_deadline(time_limit, || {
        let (click_source, sources) = load_sidecar(click_path)?;
        verify_c0_sources(&click_source, &source_refs(&sources)).map_err(|error| {
            format!(
                "sidecar `{}` failed under its {} limit: {}",
                click_path.display(),
                format_duration(time_limit),
                error.message()
            )
        })
    })?;
    Ok(())
}

fn verify_location(
    click_path: &Path,
    line: usize,
    column: usize,
    time_limit: Duration,
) -> Result<(), String> {
    click::instrumentation::with_deadline(time_limit, || {
        let (click_source, sources) = load_sidecar(click_path)?;
        verify_c0_sources_at(&click_source, &source_refs(&sources), line, column).map_err(
            |error| {
                format!(
                    "proof unit `{}:{line}:{column}` failed under its {} limit: {}",
                    click_path.display(),
                    format_duration(time_limit),
                    error.message()
                )
            },
        )?;
        Ok::<(), String>(())
    })?;
    Ok(())
}

fn load_sidecar(click_path: &Path) -> Result<(String, Vec<(String, String)>), String> {
    let click_source = fs::read_to_string(click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let sources = read_verifying_sources(click_path, &click_source)?;
    Ok((click_source, sources))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn location_suffixes_win_over_paths_that_could_be_directories() {
        assert!(looks_like_source_location("examples/tiny/tiny.click:12:5"));
        assert!(!looks_like_source_location("examples/tiny"));
        assert!(!looks_like_source_location("examples"));
    }

    #[test]
    fn parses_default_and_overridden_time_limits() {
        assert_eq!(
            parse_arguments(["example.click".to_string()]),
            Ok(Arguments {
                target: "example.click".to_string(),
                time_limit: DEFAULT_TIME_LIMIT,
            })
        );
        assert_eq!(
            parse_arguments([
                "--time-limit".to_string(),
                "250ms".to_string(),
                "example.click".to_string(),
            ]),
            Ok(Arguments {
                target: "example.click".to_string(),
                time_limit: Duration::from_millis(250),
            })
        );
    }

    #[test]
    fn discovered_sidecars_display_under_the_named_directory() {
        let root = fs::canonicalize("examples").expect("the examples directory should exist");
        let sidecar = root.join("input-cursor").join("input_cursor.click");
        assert_eq!(
            display_path(&sidecar, Path::new("examples")),
            "examples/input-cursor/input_cursor.click"
        );
    }

    #[test]
    fn directory_mode_finds_every_sidecar_in_a_single_project() {
        let projects =
            find_projects(Path::new("examples/input-cursor")).expect("the project should resolve");
        assert_eq!(projects.len(), 1);
        let sidecars =
            files_with_extension(&projects[0], "click").expect("sidecars should be listed");
        assert!(!sidecars.is_empty());
    }
}
