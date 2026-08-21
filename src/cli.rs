//! Shared helpers for the Click command-line binaries and test harnesses.
//!
//! These reconcile driver code that was previously duplicated (with drift)
//! across `click-verify`, `click-expand`, `click-audit`, `click-profile`, and
//! the integration-test harnesses: one-based source locations, human-readable
//! durations, structured tactic budgets, project discovery, and a bounded
//! worker pool.

use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::Duration;

/// Environment variables that are part of Click's documented command and
/// repository-tooling surface. Debug-only probes are intentionally excluded.
pub const PUBLIC_ENVIRONMENT_VARIABLES: &[&str] = &[
    "CLICK_TIMINGS",
    "CLICK_TIMING_STARTS",
    "CLICK_FULL_DIAGNOSTICS",
    "MDTEST_FILTER",
    "CLICK_EXAMPLE",
    "CLICK_RUN_QUARANTINED",
    "CLICK_DISABLE_TACTIC_BUDGETS",
    "CLICK_DISABLE_DECIDE_MEMO",
    "CLICK_DISABLE_CERT_ARMS",
    "CLICK_DISABLE_MEMORY_DAG",
    "CLICK_DISABLE_CLOSER_REUSE",
];

/// Stable identifiers for documented command targets, selection rules,
/// defaults, output modes, and exit boundaries. Option spellings and
/// environment variables have separate registries.
pub const PUBLIC_CLI_BEHAVIORS: &[&str] = &[
    "shared.duration-syntax",
    "shared.exit-status",
    "verify.target.sidecar",
    "verify.target.location",
    "verify.target.project",
    "verify.target.collection",
    "verify.selection.incremental",
    "verify.default.time-limit",
    "verify.output",
    "profile.target.sidecar",
    "profile.target.project",
    "profile.target.collection",
    "profile.target.mdtest",
    "profile.target.mdtests-directory",
    "profile.default.smart-threshold",
    "profile.default.simple-threshold",
    "profile.default.control-threshold",
    "profile.default.time-limit",
    "profile.default.top",
    "profile.output.report",
    "profile.output.partial",
    "expand.target.sidecar",
    "expand.target.mdtest",
    "expand.selection.location",
    "expand.selection.claim",
    "expand.default.time-limit",
    "expand.output.stdout",
    "expand.output.path",
    "expand.output.in-place",
    "expand.exit.atomic-failure",
    "audit.target.sidecar",
    "audit.target.project",
    "audit.target.collection",
    "audit.target.mdtest",
    "audit.target.mdtests-directory",
    "audit.target.repository",
    "audit.selection.claim",
    "audit.selection.changed-since",
    "audit.selection.start-at",
    "audit.default.session-time-limit",
    "audit.default.expansion-time-limit",
    "audit.default.verification-time-limit",
    "audit.default.performance-slack",
    "audit.default.time-limit",
    "audit.output.progress",
    "audit.output.resume",
    "audit.output.summary",
    "audit.check.fixed-point",
    "audit.check.performance",
];

use crate::instrumentation::{TacticEvent, VerificationEvent};
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
    if milliseconds.is_multiple_of(60_000) && milliseconds != 0 {
        format!("{}m", milliseconds / 60_000)
    } else if milliseconds.is_multiple_of(1_000) {
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

/// Reads a duration from an environment variable, falling back to `default`
/// when the variable is unset.
///
/// The variable is parsed by [`parse_duration`], so every caller accepts the
/// same forms the binaries accept on the command line.
pub fn duration_from_env(variable: &str, default: Duration) -> Result<Duration, String> {
    let source = std::env::var_os(variable);
    duration_from_optional_os(variable, source.as_deref(), default)
}

fn duration_from_optional_os(
    variable: &str,
    source: Option<&std::ffi::OsStr>,
    default: Duration,
) -> Result<Duration, String> {
    let Some(source) = source else {
        return Ok(default);
    };
    let source = source
        .to_str()
        .ok_or_else(|| format!("{variable} must be valid UTF-8"))?;
    parse_duration(source).map_err(|message| format!("{variable}: {message}"))
}

/// Per-class tactic time thresholds (owner ruling 2026-07-31): a slow SIMPLE
/// tactic is an engine bug. A successful slow SMART tactic is an expansion
/// candidate; a failed SMART search should be decomposed unless it missed its
/// enforced bound or produced a tooling-quality failure.
/// These match `click profile`'s default reporting thresholds and the
/// structured-violation diagnostics below. Production *enforcement* is the
/// deterministic per-class work budget in `instrumentation::TacticWorkLimits`
/// with a generous real-time backstop (`instrumentation::TacticLimits`):
/// crossing a reporting threshold is a finding to investigate, while
/// exhausting a work budget fails the proof deterministically.
pub const DEFAULT_SIMPLE_TACTIC_LIMIT: Duration = Duration::from_millis(500);
pub const DEFAULT_SMART_TACTIC_LIMIT: Duration = Duration::from_secs(2);
pub const DEFAULT_CONTROL_TACTIC_LIMIT: Duration = Duration::from_secs(6);
pub const DEFAULT_EXPANSION_TIME_LIMIT: Duration = Duration::from_secs(60);
/// Whole-sidecar deadline used by ordinary `click verify` and verification
/// fixtures. Directory verification applies it independently to each
/// sidecar, so one slow project cannot consume the following projects' time.
pub const DEFAULT_VERIFY_TIME_LIMIT: Duration = Duration::from_secs(30);

/// Disables tactic budget enforcement in the fixture harnesses, for A/B runs
/// and archaeology on old trees.
pub const DISABLE_TACTIC_BUDGETS: &str = "CLICK_DISABLE_TACTIC_BUDGETS";

fn tactic_budget(class: &str) -> Option<(Duration, &'static str)> {
    match class {
        "simple" => Some((
            DEFAULT_SIMPLE_TACTIC_LIMIT,
            "a slow simple tactic is a Click engine bug",
        )),
        "smart" => Some((
            DEFAULT_SMART_TACTIC_LIMIT,
            "smart search is heuristic; expand a success, otherwise use smaller or explicit simple tactics",
        )),
        "control" => Some((
            DEFAULT_CONTROL_TACTIC_LIMIT,
            "a slow control tactic is a Click engine bug",
        )),
        _ => None,
    }
}

#[derive(Clone, Debug)]
struct TacticBudgetViolation {
    message: String,
}

fn structured_tactic_budget_findings(events: &[VerificationEvent]) -> Vec<TacticBudgetViolation> {
    let mut open: Vec<(TacticEvent, Duration)> = Vec::new();
    let mut violations = Vec::new();
    for event in events {
        match event {
            VerificationEvent::TacticStarted(tactic) => {
                open.push((tactic.clone(), Duration::ZERO));
            }
            VerificationEvent::TacticFinished {
                tactic, elapsed, ..
            } => {
                let nested = match open.iter().rposition(|(candidate, _)| candidate == tactic) {
                    Some(index) => {
                        let (_, nested) = open.remove(index);
                        open.truncate(index);
                        nested
                    }
                    None => Duration::ZERO,
                };
                if let Some((_, parent_nested)) = open.last_mut() {
                    *parent_nested += *elapsed;
                }
                let exclusive = elapsed.saturating_sub(nested);
                let Some((budget, consequence)) = tactic_budget(&tactic.class) else {
                    violations.push(TacticBudgetViolation {
                        message: format!(
                            "unrecognized tactic class `{}` (structured timing drift)",
                            tactic.class
                        ),
                    });
                    continue;
                };
                if exclusive > budget {
                    violations.push(TacticBudgetViolation {
                        message: format!(
                            "{} {} {} class {} statement {} source {}: {:.3} s exclusive, over the {} {} budget — {consequence}",
                            tactic.claim,
                            tactic.tactic_index,
                            tactic.tactic_name,
                            tactic.class,
                            tactic.statement_index,
                            tactic.source_index,
                            exclusive.as_secs_f64(),
                            format_duration(budget),
                            tactic.class,
                        ),
                    });
                }
            }
            _ => {}
        }
    }
    violations
}

/// Checks structured tactic events against the production class budgets.
/// Performance diagnostics and tests use it without parsing stderr.
pub fn structured_tactic_budget_violations(events: &[VerificationEvent]) -> Vec<String> {
    structured_tactic_budget_findings(events)
        .into_iter()
        .map(|violation| violation.message)
        .collect()
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

/// Quotes one argument for a POSIX-shell command printed for the user.
///
/// Shell operators such as redirection are not arguments and should be
/// written separately by the caller.
pub fn shell_quote(word: &str) -> String {
    if !word.is_empty()
        && word
            .bytes()
            .all(|byte| byte.is_ascii_alphanumeric() || b"/._:-".contains(&byte))
    {
        word.to_string()
    } else {
        format!("'{}'", word.replace('\'', "'\\''"))
    }
}

fn directory_entries(directory: &Path) -> Result<Vec<fs::DirEntry>, String> {
    fs::read_dir(directory)
        .map_err(|error| format!("failed to read `{}`: {error}", directory.display()))?
        .map(|entry| {
            entry.map_err(|error| {
                format!(
                    "failed to read an entry in `{}`: {error}",
                    directory.display()
                )
            })
        })
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
    let mut projects = Vec::new();
    for entry in directory_entries(path)? {
        let candidate = entry.path();
        if candidate.is_dir() && contains_click_file(&candidate)? {
            projects.push(fs::canonicalize(&candidate).map_err(|error| {
                format!("failed to resolve `{}`: {error}", candidate.display())
            })?);
        }
    }
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
    Ok(directory_entries(path)?.into_iter().any(|entry| {
        entry
            .path()
            .extension()
            .is_some_and(|extension| extension == "click")
    }))
}

/// Lists the files in `directory` (non-recursively) with the extension.
pub fn files_with_extension(directory: &Path, extension: &str) -> Result<Vec<PathBuf>, String> {
    let mut paths = directory_entries(directory)?
        .into_iter()
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|actual| actual == extension))
        .collect::<Vec<_>>();
    paths.sort();
    Ok(paths)
}

/// One markdown test: the C translation units, the Click sidecar, and the
/// expected outcome, all extracted from fenced blocks in a single `.md` file.
///
/// This is single-sourced here so the `mdtests` harness and `click-profile`
/// agree on what an mdtest *is*; a profiler that extracted the sources
/// slightly differently would profile a different program than the gate runs.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct MdTest {
    /// `(filename, source)` for every ```c block, in file order.
    pub c_sources: Vec<(String, String)>,
    /// The single ```click block, if the file has one.
    pub click_source: Option<String>,
    /// The one-based line in the `.md` file where the ```click block's first
    /// body line sits, so positions inside the sidecar can be reported as
    /// positions in the markdown file.
    pub click_start_line: usize,
    /// The ```expect block, if the file has one.
    pub expectation: Option<MdTestExpectation>,
}

impl MdTest {
    /// Translates a one-based container line into a one-based line inside the
    /// Click block, rejecting locations outside that block.
    pub fn click_line(&self, container_line: usize) -> Result<usize, String> {
        let click_source = self
            .click_source
            .as_deref()
            .ok_or_else(|| "mdtest has no ```click block".to_string())?;
        let first = self.click_start_line;
        let last = first + click_source.lines().count().saturating_sub(1);
        if container_line < first || container_line > last {
            return Err(format!(
                "line {container_line} is not inside the ```click block (lines {first}..{last})"
            ));
        }
        Ok(container_line - first + 1)
    }

    /// Replaces the Click block body in the original markdown container.
    /// The body is checked against the parsed source before splicing so stale
    /// coordinates cannot silently edit the wrong lines.
    pub fn replace_click_source(
        &self,
        container_source: &str,
        replacement: &str,
    ) -> Result<String, String> {
        let click_source = self
            .click_source
            .as_deref()
            .ok_or_else(|| "mdtest has no ```click block".to_string())?;
        let lines = container_source.lines().collect::<Vec<_>>();
        let body_start = self
            .click_start_line
            .checked_sub(1)
            .ok_or_else(|| "mdtest Click block has an invalid start line".to_string())?;
        let body_len = click_source.lines().count();
        let body_end = body_start
            .checked_add(body_len)
            .filter(|end| *end <= lines.len())
            .ok_or_else(|| "mdtest Click block extends past the container".to_string())?;
        if lines[body_start..body_end] != click_source.lines().collect::<Vec<_>>() {
            return Err("mdtest Click block no longer matches the parsed container".to_string());
        }
        let mut spliced = Vec::with_capacity(lines.len());
        spliced.extend_from_slice(&lines[..body_start]);
        spliced.extend(replacement.lines());
        spliced.extend_from_slice(&lines[body_end..]);
        let mut result = spliced.join("\n");
        if container_source.ends_with('\n') {
            result.push('\n');
        }
        Ok(result)
    }
}

/// What an mdtest expects verification to do.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MdTestExpectation {
    Pass,
    FailContains(String),
}

/// Extracts the fenced blocks of an mdtest.
///
/// `path` only names the file in diagnostics; the content comes from `source`.
pub fn parse_mdtest(path: &Path, source: &str) -> Result<MdTest, String> {
    let mut mdtest = MdTest {
        c_sources: Vec::new(),
        click_source: None,
        click_start_line: 1,
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

        let fence_line = index + 1;
        let info = line.trim_start_matches("```").trim();
        index += 1;
        let start_line = index + 1;
        let mut body = Vec::new();
        while index < lines.len() && !lines[index].starts_with("```") {
            body.push(lines[index]);
            index += 1;
        }
        if index == lines.len() {
            return Err(format!(
                "`{}` has unterminated fenced block starting at line {start_line}",
                path.display()
            ));
        }
        index += 1;

        let body = body.join("\n");
        match block_kind(path, fence_line, info)? {
            Some(BlockKind::C { filename }) => {
                if mdtest
                    .c_sources
                    .iter()
                    .any(|(existing, _)| existing == &filename)
                {
                    return Err(format!(
                        "`{}` has duplicate C filename `{filename}` at line {fence_line}",
                        path.display()
                    ));
                }
                mdtest.c_sources.push((filename, body));
            }
            Some(BlockKind::Click) => {
                if mdtest.click_source.replace(body).is_some() {
                    return Err(format!(
                        "`{}` has more than one ```click block",
                        path.display()
                    ));
                }
                mdtest.click_start_line = start_line;
            }
            Some(BlockKind::Expect) => {
                let expectation = parse_expectation(path, start_line, &body)?;
                if mdtest.expectation.replace(expectation).is_some() {
                    return Err(format!(
                        "`{}` has more than one ```expect block",
                        path.display()
                    ));
                }
            }
            None => {}
        }
    }

    Ok(mdtest)
}

/// Reads and extracts an mdtest from disk.
pub fn read_mdtest(path: &Path) -> Result<MdTest, String> {
    let source = fs::read_to_string(path)
        .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
    parse_mdtest(path, &source)
}

enum BlockKind {
    C { filename: String },
    Click,
    Expect,
}

fn block_kind(path: &Path, line: usize, info: &str) -> Result<Option<BlockKind>, String> {
    let mut parts = info.split_whitespace();
    let Some(kind) = parts.next() else {
        return Ok(None);
    };
    match kind {
        "c" => {
            let attributes = parts.collect::<Vec<_>>();
            let [attribute] = attributes.as_slice() else {
                return Err(format!(
                    "`{}` has invalid C fence at line {line}: expected exactly `c filename=NAME`",
                    path.display()
                ));
            };
            let Some(filename) = attribute.strip_prefix("filename=") else {
                return Err(format!(
                    "`{}` has invalid C fence at line {line}: expected `filename=NAME`, got `{attribute}`",
                    path.display()
                ));
            };
            if filename.is_empty() {
                return Err(format!(
                    "`{}` has empty C filename at line {line}",
                    path.display()
                ));
            }
            Ok(Some(BlockKind::C {
                filename: filename.to_string(),
            }))
        }
        "click" | "expect" => {
            if let Some(extra) = parts.next() {
                return Err(format!(
                    "`{}` has unexpected `{extra}` metadata on the `{kind}` fence at line {line}",
                    path.display()
                ));
            }
            Ok(Some(if kind == "click" {
                BlockKind::Click
            } else {
                BlockKind::Expect
            }))
        }
        _ => Ok(None),
    }
}

fn parse_expectation(path: &Path, line: usize, body: &str) -> Result<MdTestExpectation, String> {
    let body = body.trim();
    if body == "pass" {
        return Ok(MdTestExpectation::Pass);
    }
    if let Some(message) = body.strip_prefix("fail:") {
        return Ok(MdTestExpectation::FailContains(message.trim().to_string()));
    }
    Err(format!(
        "`{}` has invalid expectation at line {line}: expected `pass` or `fail: substring`, got `{body}`",
        path.display()
    ))
}

/// Lists the `.md` files under `path`: `path` itself when it is one, or the
/// markdown files directly inside it. Returned paths are sorted.
pub fn find_mdtests(path: &Path) -> Result<Vec<PathBuf>, String> {
    if path.is_file() {
        if !looks_like_mdtest(path) {
            return Err(format!("`{}` is not a markdown test", path.display()));
        }
        return Ok(vec![path.to_path_buf()]);
    }
    if !path.is_dir() {
        return Err(format!("`{}` is not a file or directory", path.display()));
    }
    let mut paths = files_with_extension(path, "md")?;
    paths.sort();
    if paths.is_empty() {
        return Err(format!("`{}` contains no markdown tests", path.display()));
    }
    Ok(paths)
}

/// Returns true when the path names a markdown file, so a driver can pick
/// mdtest mode over example-project mode from the argument alone.
pub fn looks_like_mdtest(path: &Path) -> bool {
    path.extension().is_some_and(|extension| extension == "md")
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

    fn tactic(index: usize, name: &str, class: &str) -> TacticEvent {
        TacticEvent {
            claim: "f.contract".to_string(),
            tactic_index: index,
            tactic_name: name.to_string(),
            class: class.to_string(),
            statement_index: index,
            source_index: index,
        }
    }

    #[test]
    fn structured_budget_violations_flag_each_class_over_its_own_budget() {
        let events = vec![
            VerificationEvent::TacticStarted(tactic(0, "step", "simple")),
            VerificationEvent::TacticFinished {
                tactic: tactic(0, "step", "simple"),
                elapsed: Duration::from_millis(700),
                work: 0,
            },
            VerificationEvent::TacticStarted(tactic(1, "simp", "smart")),
            VerificationEvent::TacticFinished {
                tactic: tactic(1, "simp", "smart"),
                elapsed: Duration::from_millis(1_900),
                work: 0,
            },
        ];
        let violations = structured_tactic_budget_violations(&events);
        assert_eq!(violations.len(), 1, "{violations:?}");
        assert!(
            violations[0].contains("f.contract 0 step"),
            "{violations:?}"
        );
        assert!(violations[0].contains("simple budget"), "{violations:?}");
    }

    #[test]
    fn smart_budget_violation_recommends_proof_decomposition() {
        let events = vec![
            VerificationEvent::TacticStarted(tactic(0, "execute_until", "smart")),
            VerificationEvent::TacticFinished {
                tactic: tactic(0, "execute_until", "smart"),
                elapsed: Duration::from_millis(2_100),
                work: 0,
            },
        ];
        let violations = structured_tactic_budget_violations(&events);
        assert_eq!(violations.len(), 1, "{violations:?}");
        assert!(
            violations[0].contains("smaller or explicit simple tactics"),
            "{violations:?}"
        );
    }

    #[test]
    fn structured_budget_violations_use_exclusive_time_for_containers() {
        // The smart container reports 2.5 s but 2.4 s of it is the nested
        // simple step; only the simple step is over its own budget.
        let events = vec![
            VerificationEvent::TacticStarted(tactic(0, "cases", "smart")),
            VerificationEvent::TacticStarted(tactic(1, "step", "simple")),
            VerificationEvent::TacticFinished {
                tactic: tactic(1, "step", "simple"),
                elapsed: Duration::from_millis(2_400),
                work: 0,
            },
            VerificationEvent::TacticFinished {
                tactic: tactic(0, "cases", "smart"),
                elapsed: Duration::from_millis(2_500),
                work: 0,
            },
        ];
        let violations = structured_tactic_budget_violations(&events);
        assert_eq!(violations.len(), 1, "{violations:?}");
        assert!(
            violations[0].contains("f.contract 1 step"),
            "{violations:?}"
        );
    }

    #[test]
    fn structured_budget_violations_are_empty_for_a_fast_run() {
        let events = vec![
            VerificationEvent::TacticStarted(tactic(0, "step", "simple")),
            VerificationEvent::TacticFinished {
                tactic: tactic(0, "step", "simple"),
                elapsed: Duration::from_millis(10),
                work: 0,
            },
        ];
        assert_eq!(
            structured_tactic_budget_violations(&events),
            Vec::<String>::new()
        );
    }

    #[test]
    fn structured_budget_violations_report_class_drift() {
        let events = vec![
            VerificationEvent::TacticStarted(tactic(0, "step", "brandnew")),
            VerificationEvent::TacticFinished {
                tactic: tactic(0, "step", "brandnew"),
                elapsed: Duration::from_secs(9),
                work: 0,
            },
        ];
        let violations = structured_tactic_budget_violations(&events);
        assert_eq!(violations.len(), 1, "{violations:?}");
        assert!(
            violations[0].contains("unrecognized tactic class"),
            "{violations:?}"
        );
    }

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
        assert!(looks_like_source_location(
            "dir:with:colon/example.click:0:5"
        ));
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
        assert_eq!(
            format_fractional_duration(Duration::from_millis(750)),
            "750ms"
        );
    }

    #[test]
    fn shell_words_are_quoted_for_copy_paste_commands() {
        assert_eq!(shell_quote("plain/path.click:2:3"), "plain/path.click:2:3");
        assert_eq!(shell_quote("a path/file.click"), "'a path/file.click'");
        assert_eq!(shell_quote("it's.click"), "'it'\\''s.click'");
        assert_eq!(shell_quote(""), "''");
    }

    #[test]
    fn mdtest_recognized_fences_reject_malformed_metadata() {
        let path = Path::new("bad.md");
        for source in [
            "```c\nint main() {}\n```\n",
            "```c filename=\nint main() {}\n```\n",
            "```c filename=a.c extra\nint main() {}\n```\n",
            "```click extra\nverifying a.c;\n```\n",
            "```expect extra\npass\n```\n",
        ] {
            assert!(parse_mdtest(path, source).is_err(), "{source}");
        }
    }

    #[test]
    fn mdtest_rejects_duplicate_c_filenames_but_ignores_unrelated_fences() {
        let duplicate = "```c filename=a.c\nint a;\n```\n```c filename=a.c\nint b;\n```\n";
        assert!(parse_mdtest(Path::new("duplicate.md"), duplicate).is_err());

        let source = "```rust ignore\nfn main() {}\n```\n```c filename=a.c\nint a;\n```\n";
        let mdtest = parse_mdtest(Path::new("mixed.md"), source).unwrap();
        assert_eq!(
            mdtest.c_sources,
            vec![("a.c".to_string(), "int a;".to_string())]
        );
    }

    #[test]
    fn mdtest_coordinates_and_replacement_preserve_the_container() {
        let markdown = "before\n```click\nstep();\n```\nafter\n";
        let mdtest = parse_mdtest(Path::new("container.md"), markdown).unwrap();
        assert!(mdtest.click_line(2).is_err());
        assert_eq!(mdtest.click_line(3), Ok(1));
        assert!(mdtest.click_line(4).is_err());
        assert_eq!(
            mdtest
                .replace_click_source(markdown, "step() using {\n}\n")
                .unwrap(),
            "before\n```click\nstep() using {\n}\n```\nafter\n"
        );

        let no_trailing_newline = markdown.trim_end();
        let mdtest = parse_mdtest(Path::new("container.md"), no_trailing_newline).unwrap();
        let replaced = mdtest
            .replace_click_source(no_trailing_newline, "assumption();")
            .unwrap();
        assert!(!replaced.ends_with('\n'));
        assert!(
            mdtest
                .replace_click_source(&markdown.replace("step();", "simp();"), "assumption();")
                .is_err()
        );
    }

    #[test]
    fn sidecars_load_only_declared_sources_and_resolve_relative_paths() {
        let root = std::env::temp_dir().join(format!(
            "click-source-loading-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let project = root.join("project");
        fs::create_dir_all(&project).unwrap();
        fs::write(root.join("actual.c"), "int32 actual() { return 1; }").unwrap();
        fs::write(project.join("unrelated.c"), "this is not C0").unwrap();
        let click_path = project.join("proof.click");
        let click_source = "verifying \"../actual.c\";\n";

        let sources = read_verifying_sources(&click_path, click_source).unwrap();
        assert_eq!(
            sources,
            vec![(
                "../actual.c".to_string(),
                "int32 actual() { return 1; }".to_string()
            )]
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn environment_durations_fall_back_and_report_their_variable() {
        assert_eq!(
            duration_from_optional_os("LIMIT", None, Duration::from_secs(3)),
            Ok(Duration::from_secs(3))
        );
        assert_eq!(
            duration_from_optional_os(
                "LIMIT",
                Some(std::ffi::OsStr::new("250ms")),
                Duration::from_secs(3),
            ),
            Ok(Duration::from_millis(250))
        );
        let message = duration_from_optional_os(
            "LIMIT",
            Some(std::ffi::OsStr::new("later")),
            Duration::from_secs(3),
        )
        .expect_err("an unparseable duration should be rejected");
        assert!(message.starts_with("LIMIT: "), "{message}");
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
