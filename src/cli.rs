//! Shared helpers for the Click command-line binaries and test harnesses.
//!
//! These reconcile driver code that was previously duplicated (with drift)
//! across `click-verify`, `click-expand`, `click-audit`, `click-profile`, and
//! the integration-test harnesses: one-based source locations, human-readable
//! durations, bounded child processes, project discovery, and a bounded
//! worker pool.

use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use crate::lang::click::verifying_source_paths;

/// Parses a one-based `PATH:LINE:COLUMN` source location.
///
/// The location is split from the right so paths may contain colons. Lines
/// and columns are one-based; zero values are rejected.
pub fn parse_source_location(source: &str) -> Result<(PathBuf, usize, usize), String> {
    let (path_and_line, column) = source
        .rsplit_once(':')
        .ok_or_else(|| format!("invalid source location `{source}`; expected PATH:LINE:COLUMN"))?;
    let (path, line) = path_and_line
        .rsplit_once(':')
        .ok_or_else(|| format!("invalid source location `{source}`; expected PATH:LINE:COLUMN"))?;
    if path.is_empty() {
        return Err("source path must not be empty".to_string());
    }
    let line = line
        .parse::<usize>()
        .map_err(|_| format!("invalid source line `{line}`"))?;
    let column = column
        .parse::<usize>()
        .map_err(|_| format!("invalid source column `{column}`"))?;
    if line == 0 || column == 0 {
        return Err("source lines and columns are one-based".to_string());
    }
    Ok((PathBuf::from(path), line, column))
}

/// Returns true when the argument is shaped like `PATH:LINE:COLUMN`, meaning
/// it ends in two colon-separated all-digit segments.
///
/// This decides whether a command-line argument selects a source location or
/// names a whole file; malformed locations (for example zero-based lines)
/// still shape-match and report their validation error through
/// [`parse_source_location`].
pub fn looks_like_source_location(argument: &str) -> bool {
    let Some((path_and_line, column)) = argument.rsplit_once(':') else {
        return false;
    };
    let Some((path, line)) = path_and_line.rsplit_once(':') else {
        return false;
    };
    !path.is_empty()
        && !line.is_empty()
        && !column.is_empty()
        && line.bytes().all(|byte| byte.is_ascii_digit())
        && column.bytes().all(|byte| byte.is_ascii_digit())
}

/// Parses a human-readable duration.
///
/// Accepts `ms`, `s`, and `m` suffixes; a bare number is interpreted as
/// seconds. Zero durations are rejected.
pub fn parse_duration(source: &str) -> Result<Duration, String> {
    let source = source.trim();
    let (digits, multiplier) = if let Some(digits) = source.strip_suffix("ms") {
        (digits, 1_u128)
    } else if let Some(digits) = source.strip_suffix('s') {
        (digits, 1_000)
    } else if let Some(digits) = source.strip_suffix('m') {
        (digits, 60_000)
    } else {
        (source, 1_000)
    };
    let amount = digits.trim().parse::<u128>().map_err(|_| {
        format!(
            "invalid duration `{source}`; use milliseconds, seconds, or minutes (for example `500ms`, `30s`, or `2m`)"
        )
    })?;
    let milliseconds = amount
        .checked_mul(multiplier)
        .ok_or_else(|| format!("duration `{source}` is too large"))?;
    if milliseconds == 0 {
        return Err("duration must be greater than zero".to_string());
    }
    Ok(Duration::from_millis(u64::try_from(milliseconds).map_err(
        |_| format!("duration `{source}` is too large"),
    )?))
}

/// Formats a duration canonically so it round-trips through
/// [`parse_duration`]: whole minutes as `Nm`, whole seconds as `Ns`, and
/// anything else as `Nms`.
pub fn format_duration(duration: Duration) -> String {
    let milliseconds = duration.as_millis();
    if milliseconds % 60_000 == 0 && milliseconds != 0 {
        format!("{}m", milliseconds / 60_000)
    } else if milliseconds % 1_000 == 0 {
        format!("{}s", milliseconds / 1_000)
    } else {
        format!("{milliseconds}ms")
    }
}

/// Formats a measured duration for reports, keeping fractional precision
/// (for example `1.250s` or `750ms`). This does not round-trip through
/// [`parse_duration`].
pub fn format_fractional_duration(duration: Duration) -> String {
    let milliseconds = duration.as_secs_f64() * 1_000.0;
    if milliseconds >= 1_000.0 {
        format!("{:.3}s", milliseconds / 1_000.0)
    } else {
        format!("{milliseconds:.0}ms")
    }
}

/// A child process that ran to completion under [`run_bounded`].
#[derive(Debug)]
pub struct ChildOutput {
    pub status: ExitStatus,
    pub stdout: Vec<u8>,
    pub stderr: Vec<u8>,
    pub elapsed: Duration,
}

/// The outcome of running a child process under a wall-clock limit.
#[derive(Debug)]
pub enum BoundedOutput {
    Completed(ChildOutput),
    TimedOut {
        stdout: Vec<u8>,
        stderr: Vec<u8>,
        elapsed: Duration,
    },
}

/// Runs a child process with a wall-clock limit, killing and reaping it on
/// timeout and capturing its stdout and stderr either way.
pub fn run_bounded(command: Command, limit: Duration, label: &str) -> Result<BoundedOutput, String> {
    run_bounded_with_input(command, None, limit, label)
}

/// Like [`run_bounded`], but additionally writes `input` to the child's
/// stdin and closes it so the child observes end-of-input.
pub fn run_bounded_with_input(
    mut command: Command,
    input: Option<Vec<u8>>,
    limit: Duration,
    label: &str,
) -> Result<BoundedOutput, String> {
    if input.is_some() {
        command.stdin(Stdio::piped());
    }
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("failed to start {label}: {error}"))?;
    let writer = match input {
        Some(bytes) => {
            let mut stdin = child
                .stdin
                .take()
                .ok_or_else(|| format!("failed to open {label} input"))?;
            Some(thread::spawn(move || {
                // The child may exit without draining its input; a broken
                // pipe here is not an error worth reporting.
                let _ = stdin.write_all(&bytes);
            }))
        }
        None => None,
    };
    let stdout = child
        .stdout
        .take()
        .ok_or_else(|| format!("failed to capture {label} output"))?;
    let stderr = child
        .stderr
        .take()
        .ok_or_else(|| format!("failed to capture {label} diagnostics"))?;
    let stdout_reader = thread::spawn(move || read_all(stdout));
    let stderr_reader = thread::spawn(move || read_all(stderr));
    let start = Instant::now();
    let status = loop {
        if let Some(status) = child
            .try_wait()
            .map_err(|error| format!("failed to poll {label}: {error}"))?
        {
            break Some(status);
        }
        if start.elapsed() >= limit {
            let _ = child.kill();
            let _ = child.wait();
            break None;
        }
        thread::sleep(
            limit
                .saturating_sub(start.elapsed())
                .min(Duration::from_millis(10)),
        );
    };
    let elapsed = start.elapsed();
    if let Some(writer) = writer {
        let _ = writer.join();
    }
    let stdout = join_reader(stdout_reader, label, "output")?;
    let stderr = join_reader(stderr_reader, label, "diagnostics")?;
    Ok(match status {
        Some(status) => BoundedOutput::Completed(ChildOutput {
            status,
            stdout,
            stderr,
            elapsed,
        }),
        None => BoundedOutput::TimedOut {
            stdout,
            stderr,
            elapsed,
        },
    })
}

fn read_all(mut reader: impl Read) -> std::io::Result<Vec<u8>> {
    let mut bytes = Vec::new();
    reader.read_to_end(&mut bytes)?;
    Ok(bytes)
}

fn join_reader(
    reader: thread::JoinHandle<std::io::Result<Vec<u8>>>,
    label: &str,
    stream: &str,
) -> Result<Vec<u8>, String> {
    reader
        .join()
        .map_err(|_| format!("{label} {stream} reader panicked"))?
        .map_err(|error| format!("failed to read {label} {stream}: {error}"))
}

/// Reads the C sources a sidecar declares with `verifying`, relative to the
/// sidecar's directory.
pub fn read_verifying_sources(
    click_path: &Path,
    click_source: &str,
) -> Result<Vec<(String, String)>, String> {
    let parent = click_path.parent().unwrap_or_else(|| Path::new("."));
    verifying_source_paths(click_source)
        .map_err(|error| error.message().to_string())?
        .into_iter()
        .map(|name| {
            let source = fs::read_to_string(parent.join(&name))
                .map_err(|error| format!("failed to read `{name}`: {error}"))?;
            Ok((name, source))
        })
        .collect()
}

/// Borrows owned `(name, source)` pairs as the `&str` pairs the verification
/// entry points accept.
pub fn source_refs(sources: &[(String, String)]) -> Vec<(&str, &str)> {
    sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect()
}

/// Finds example projects under `path`: either `path` itself when it directly
/// contains a `.click` sidecar, or its immediate subdirectories that do.
/// Returned paths are canonicalized and sorted.
pub fn find_projects(path: &Path) -> Result<Vec<PathBuf>, String> {
    if !path.is_dir() {
        return Err(format!("`{}` is not a directory", path.display()));
    }
    if contains_click_file(path)? {
        return Ok(vec![fs::canonicalize(path).map_err(|error| {
            format!("failed to resolve `{}`: {error}", path.display())
        })?]);
    }
    let mut projects =
        fs::read_dir(path)
            .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?
            .filter_map(Result::ok)
            .map(|entry| entry.path())
            .filter(|candidate| candidate.is_dir())
            .filter_map(|candidate| match contains_click_file(&candidate) {
                Ok(true) => Some(fs::canonicalize(&candidate).map_err(|error| {
                    format!("failed to resolve `{}`: {error}", candidate.display())
                })),
                Ok(false) => None,
                Err(error) => Some(Err(error)),
            })
            .collect::<Result<Vec<_>, _>>()?;
    projects.sort();
    if projects.is_empty() {
        return Err(format!(
            "`{}` contains no projects with Click sidecars",
            path.display()
        ));
    }
    Ok(projects)
}

/// Returns true when the directory directly contains a `.click` sidecar.
pub fn contains_click_file(path: &Path) -> Result<bool, String> {
    Ok(fs::read_dir(path)
        .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?
        .filter_map(Result::ok)
        .any(|entry| {
            entry
                .path()
                .extension()
                .is_some_and(|extension| extension == "click")
        }))
}

/// Lists the files in `directory` (non-recursively) with the extension.
pub fn files_with_extension(directory: &Path, extension: &str) -> Result<Vec<PathBuf>, String> {
    Ok(fs::read_dir(directory)
        .map_err(|error| format!("failed to read `{}`: {error}", directory.display()))?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|actual| actual == extension))
        .collect())
}

/// A reasonable worker count for a pool processing `jobs` independent jobs:
/// the available parallelism, capped at eight and at the job count.
pub fn default_worker_count(jobs: usize) -> usize {
    let available = thread::available_parallelism().map_or(1, |count| count.get());
    available.min(8).min(jobs).max(1)
}

/// Runs `run` over every item using a bounded worker pool, collecting every
/// failure instead of stopping at the first.
///
/// Failures are returned as `(index, message)` pairs in item order.
pub fn run_parallel<T, F>(items: &[T], workers: usize, run: F) -> Vec<(usize, String)>
where
    T: Sync,
    F: Fn(&T) -> Result<(), String> + Sync,
{
    let next = AtomicUsize::new(0);
    let failures = Mutex::new(Vec::new());
    thread::scope(|scope| {
        for _ in 0..workers.max(1) {
            scope.spawn(|| {
                loop {
                    let index = next.fetch_add(1, Ordering::Relaxed);
                    let Some(item) = items.get(index) else {
                        break;
                    };
                    if let Err(message) = run(item) {
                        failures
                            .lock()
                            .expect("a worker panicked while recording a failure")
                            .push((index, message));
                    }
                }
            });
        }
    });
    let mut failures = failures
        .into_inner()
        .expect("a worker panicked while recording a failure");
    failures.sort_by_key(|(index, _)| *index);
    failures
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_source_locations_from_the_right_and_one_based() {
        assert_eq!(
            parse_source_location("dir:with:colon/example.click:12:5"),
            Ok((PathBuf::from("dir:with:colon/example.click"), 12, 5))
        );
        assert!(parse_source_location("example.click:0:5").is_err());
        assert!(parse_source_location("example.click:5:0").is_err());
        assert!(parse_source_location("example.click:12").is_err());
        assert!(parse_source_location(":12:5").is_err());
    }

    #[test]
    fn recognizes_location_shaped_arguments() {
        assert!(looks_like_source_location("example.click:12:5"));
        assert!(looks_like_source_location("dir:with:colon/example.click:0:5"));
        assert!(!looks_like_source_location("example.click"));
        assert!(!looks_like_source_location("example.click:12"));
        assert!(!looks_like_source_location("example.click:12:abc"));
        assert!(!looks_like_source_location("example.click:12:"));
    }

    #[test]
    fn parses_duration_units_and_plain_seconds() {
        assert_eq!(parse_duration("250ms"), Ok(Duration::from_millis(250)));
        assert_eq!(parse_duration("30s"), Ok(Duration::from_secs(30)));
        assert_eq!(parse_duration("2m"), Ok(Duration::from_secs(120)));
        assert_eq!(parse_duration("7"), Ok(Duration::from_secs(7)));
        assert!(parse_duration("0").is_err());
        assert!(parse_duration("0ms").is_err());
        assert!(parse_duration("later").is_err());
        assert!(parse_duration("").is_err());
    }

    #[test]
    fn formatted_durations_round_trip_through_parsing() {
        for duration in [
            Duration::from_millis(250),
            Duration::from_secs(30),
            Duration::from_secs(60),
            Duration::from_secs(90),
            Duration::from_secs(120),
        ] {
            let formatted = format_duration(duration);
            assert_eq!(parse_duration(&formatted), Ok(duration), "{formatted}");
        }
        assert_eq!(format_duration(Duration::from_secs(120)), "2m");
        assert_eq!(format_duration(Duration::from_secs(30)), "30s");
        assert_eq!(format_duration(Duration::from_millis(250)), "250ms");
    }

    #[test]
    fn fractional_durations_keep_measurement_precision() {
        assert_eq!(
            format_fractional_duration(Duration::from_millis(1_250)),
            "1.250s"
        );
        assert_eq!(format_fractional_duration(Duration::from_millis(750)), "750ms");
    }

    #[test]
    fn bounded_children_are_killed_at_their_limit() {
        let mut command = Command::new("sleep");
        command.arg("1");
        let output = run_bounded(command, Duration::from_millis(10), "test sleeper").unwrap();
        assert!(matches!(output, BoundedOutput::TimedOut { .. }));
    }

    #[test]
    fn bounded_children_pipe_input_and_capture_output() {
        let command = Command::new("cat");
        let output = run_bounded_with_input(
            command,
            Some(b"piped bytes".to_vec()),
            Duration::from_secs(10),
            "test cat",
        )
        .unwrap();
        let BoundedOutput::Completed(output) = output else {
            panic!("cat should complete before its limit");
        };
        assert!(output.status.success());
        assert_eq!(output.stdout, b"piped bytes");
    }

    #[test]
    fn parallel_runs_collect_every_failure_in_order() {
        let items = (0..20).collect::<Vec<usize>>();
        let failures = run_parallel(&items, 4, |item| {
            if item % 3 == 0 {
                Err(format!("item {item} failed"))
            } else {
                Ok(())
            }
        });
        assert_eq!(
            failures,
            (0..20)
                .filter(|item| item % 3 == 0)
                .map(|item| (item, format!("item {item} failed")))
                .collect::<Vec<_>>()
        );
    }
}
