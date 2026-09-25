//! Shared helpers for the Click command-line binaries and test harnesses.
//!
//! These reconcile driver code that was previously duplicated (with drift)
//! across `click-verify`, `click-expand`, `click-audit`, `click-profile`, and
//! the integration-test harnesses: one-based source locations, human-readable
//! durations, structured tactic budgets, project discovery, and a bounded
//! worker pool.

use std::collections::BTreeMap;
use std::fs;
use std::path::{Path, PathBuf};
use std::sync::Mutex;
use std::sync::atomic::{AtomicUsize, Ordering};
use std::thread;
use std::time::Duration;

use serde::Deserialize;

/// Environment variables that are part of Click's documented command and
/// repository-tooling surface. Debug-only probes are intentionally excluded.
pub const PUBLIC_ENVIRONMENT_VARIABLES: &[&str] = &[
    "CLICK_TIMINGS",
    "CLICK_TIMING_STARTS",
    "CLICK_FULL_DIAGNOSTICS",
    "MDTEST_FILTER",
    "CLICK_EXAMPLE",
    "CLICK_RUN_QUARANTINED",
    "CLICK_TACTIC_WORK_REPORT",
    "CLICK_DISABLE_TACTIC_BUDGETS",
];

/// Stable identifiers for documented command targets, selection rules,
/// defaults, output modes, and exit boundaries. Option spellings and
/// environment variables have separate registries.
pub const PUBLIC_CLI_BEHAVIORS: &[&str] = &[
    "shared.duration-syntax",
    "shared.exit-status",
    "import.lock",
    "import.source-selection",
    "import.validation",
    "import.trust-boundary",
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
use crate::languages::c::compiler_import::PreparedCImport;
use crate::languages::c::source as c_source;
use crate::languages::cpp::PreparedCppImport;
use crate::surface::verifying_source_paths;
use crate::surface::{CProjectProfile, ClickModuleSource, ClickProject, click_import_sites};

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

/// The directory that holds `path`, which is `.` for a bare relative file name.
///
/// `Path::parent` returns an empty path for `a.click`, and an empty path names
/// no directory: it cannot be canonicalized, joined as a project root, or
/// handed to `git -C`. Every sidecar-relative lookup goes through here so a
/// bare name and `./a.click` select the same directory.
pub fn containing_directory(path: &Path) -> &Path {
    path.parent()
        .filter(|parent| !parent.as_os_str().is_empty())
        .unwrap_or_else(|| Path::new("."))
}

/// Reads the C sources a sidecar declares with `verifying`, relative to the
/// sidecar's directory.
pub fn read_declared_sources(
    click_path: &Path,
    click_source: &str,
) -> Result<Vec<(String, String)>, String> {
    let parent = containing_directory(click_path);
    verifying_source_paths(click_source)
        .map_err(|error| error.report())?
        .into_iter()
        .map(|name| {
            let source = fs::read_to_string(parent.join(&name))
                .map_err(|error| format!("failed to read `{name}`: {error}"))?;
            Ok((name, source))
        })
        .collect()
}

/// Reads the C sources a sidecar declares with `verifying`, plus all
/// recursively included project-local headers, relative to the sidecar's
/// directory.
pub fn read_verifying_sources(
    click_path: &Path,
    click_source: &str,
) -> Result<Vec<(String, String)>, String> {
    // Header discovery preprocesses the sources, so it needs the sidecar's
    // selected C implementation target before any proof runs.
    let target = crate::surface::selected_c_target(click_source).map_err(|error| error.report())?;
    read_verifying_sources_for_target(click_path, click_source, target)
}

pub fn read_verifying_sources_for_target(
    click_path: &Path,
    click_source: &str,
    target: crate::languages::c::target::CTarget,
) -> Result<Vec<(String, String)>, String> {
    let parent = containing_directory(click_path);
    let declared = read_declared_sources(click_path, click_source)?;
    let mut pending: Vec<String> = declared.iter().map(|(name, _)| name.clone()).collect();
    let mut loaded = Vec::new();
    let mut seen = std::collections::BTreeSet::new();
    let mut next = 0;
    while next < pending.len() {
        let name = pending[next].clone();
        next += 1;
        if !seen.insert(name.clone()) {
            continue;
        }
        let source = if let Some((_, source)) = declared
            .iter()
            .find(|(declared_name, _)| declared_name == &name)
        {
            source.clone()
        } else {
            fs::read_to_string(parent.join(&name))
                .map_err(|error| format!("failed to read `{name}`: {error}"))?
        };
        let includes = c_source::local_include_paths_for_target(&name, &source, target)
            .map_err(|error| format!("failed to process C source includes: {error}"))?;
        pending.extend(includes);
        loaded.push((name, source));
    }
    Ok(loaded)
}

/// Inputs selected by a sidecar. An explicit import manifest is authoritative;
/// malformed or missing locked artifacts are errors rather than a legacy
/// source-bundle fallback.
#[derive(Clone)]
pub enum CInput {
    Bundle(Vec<(String, String)>),
    Prepared(Vec<PreparedCImport>),
    PreparedCpp(PreparedCppImport),
}

impl CInput {
    pub fn is_prepared(&self) -> bool {
        matches!(self, Self::Prepared(_) | Self::PreparedCpp(_))
    }
}

pub fn read_c_inputs(sidecar: &Path, click_source: &str) -> Result<CInput, String> {
    let directory = fs::canonicalize(containing_directory(sidecar))
        .map_err(|error| format!("failed to resolve sidecar directory: {error}"))?;
    let target = match read_c_project_profile(&directory, &directory)?
        .and_then(|profile| profile.target)
    {
        Some(target) => target,
        None => crate::surface::selected_c_target(click_source).map_err(|error| error.report())?,
    };
    read_c_inputs_for_target(sidecar, click_source, target)
}

pub fn read_c_inputs_for_project(
    sidecar: &Path,
    click_source: &str,
    project: &ClickProject,
) -> Result<CInput, String> {
    let target =
        crate::surface::selected_project_c_target(project).map_err(|error| error.report())?;
    read_c_inputs_for_target(sidecar, click_source, target)
}

fn read_c_inputs_for_target(
    sidecar: &Path,
    click_source: &str,
    target: crate::languages::c::target::CTarget,
) -> Result<CInput, String> {
    let name = sidecar
        .file_name()
        .and_then(|name| name.to_str())
        .ok_or_else(|| format!("sidecar path `{}` has no valid filename", sidecar.display()))?;
    let config = sidecar.with_file_name(format!("{name}.import.json"));
    match fs::symlink_metadata(&config) {
        Ok(_) => {
            // Preserve the path spelling for the adapter's validation.
            // An existing but unreadable or dangling config cannot select
            // the legacy source-bundle route.
            let config = if config.is_absolute() {
                config
            } else {
                std::env::current_dir()
                    .map_err(|error| format!("failed to resolve import config directory: {error}"))?
                    .join(config)
            };
            return crate::languages::load_compiler_import(&config).map(|imports| match imports {
                crate::languages::PreparedCompilerImport::C(imports) => CInput::Prepared(imports),
                crate::languages::PreparedCompilerImport::Cpp(import) => {
                    CInput::PreparedCpp(import)
                }
            });
        }
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => {}
        Err(error) => {
            return Err(format!("failed to inspect `{}`: {error}", config.display()));
        }
    }
    Ok(CInput::Bundle(read_verifying_sources_for_target(
        sidecar,
        click_source,
        target,
    )?))
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ProjectConfigJson {
    target: Option<String>,
    runtime: Option<String>,
}

fn read_c_project_profile(
    directory: &Path,
    boundary_root: &Path,
) -> Result<Option<CProjectProfile>, String> {
    let path = directory.join("click.project.json");
    match fs::symlink_metadata(&path) {
        Ok(_) => {}
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(None),
        Err(error) => return Err(format!("failed to inspect `{}`: {error}", path.display())),
    }
    let resolved = fs::canonicalize(&path)
        .map_err(|error| format!("failed to resolve `{}`: {error}", path.display()))?;
    if !resolved.starts_with(boundary_root) {
        return Err(format!(
            "Click project config `{}` escapes project root `{}`",
            path.display(),
            boundary_root.display()
        ));
    }
    let source = fs::read_to_string(&resolved)
        .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
    let config: ProjectConfigJson = serde_json::from_str(&source)
        .map_err(|error| format!("invalid Click project config `{}`: {error}", path.display()))?;
    let target = config
        .target
        .map(|name| {
            crate::languages::c::target::CTarget::from_name(&name)
                .ok_or_else(|| format!("unknown C target `{name}` in `{}`", path.display()))
        })
        .transpose()?;
    let runtime = config
        .runtime
        .map(|name| {
            crate::languages::c::thread_runtime::CThreadRuntime::from_name(&name)
                .ok_or_else(|| format!("unknown C runtime `{name}` in `{}`", path.display()))
        })
        .transpose()?;
    Ok(Some(CProjectProfile { target, runtime }))
}

/// Loads the entry sidecar and its transitive local Click imports once, using
/// the sidecar's directory as the default project root.
///
/// Callers that intentionally load a multi-directory project should use
/// [`read_click_project_at_root`] and pass that project's explicit root.
pub fn read_click_project(sidecar: &Path, click_source: &str) -> Result<ClickProject, String> {
    let root = containing_directory(sidecar);
    read_click_project_at_root(sidecar, click_source, root)
}

/// Loads an entry sidecar and its transitive local Click imports within an
/// explicit project root.
///
/// The root is a Click concern, not a version-control concern. Canonical paths
/// enforce the boundary and deduplicate diamonds; project-relative identities
/// keep diagnostics and artifacts deterministic across worktree locations.
pub fn read_click_project_at_root(
    sidecar: &Path,
    click_source: &str,
    project_root: &Path,
) -> Result<ClickProject, String> {
    let entry = fs::canonicalize(sidecar)
        .map_err(|error| format!("failed to resolve `{}`: {error}", sidecar.display()))?;
    let root = fs::canonicalize(project_root).map_err(|error| {
        format!(
            "failed to resolve Click project root `{}`: {error}",
            project_root.display()
        )
    })?;
    if !entry.starts_with(&root) {
        return Err(format!(
            "Click entry `{}` is outside project root `{}`",
            entry.display(),
            root.display()
        ));
    }
    let mut sources = BTreeMap::<PathBuf, String>::new();
    sources.insert(entry.clone(), click_source.to_string());
    let mut resolved_imports = BTreeMap::<PathBuf, Vec<PathBuf>>::new();
    let mut state = BTreeMap::<PathBuf, u8>::new();
    let mut stack = Vec::new();
    load_click_module(
        &entry,
        &root,
        &mut sources,
        &mut resolved_imports,
        &mut state,
        &mut stack,
    )?;
    let identity = |path: &Path| -> Result<String, String> {
        path.strip_prefix(&root)
            .map(|relative| relative.to_string_lossy().replace('\\', "/"))
            .map_err(|_| {
                format!(
                    "Click module `{}` is outside project root `{}`",
                    path.display(),
                    root.display()
                )
            })
    };
    let mut modules = Vec::with_capacity(sources.len());
    for (path, source) in &sources {
        let imports = resolved_imports
            .get(path)
            .into_iter()
            .flatten()
            .map(|imported| identity(imported))
            .collect::<Result<Vec<_>, _>>()?;
        modules.push(ClickModuleSource::new(
            identity(path)?,
            source.clone(),
            imports,
        ));
    }
    modules.sort_by(|left, right| left.identity().cmp(right.identity()));
    let project = ClickProject::new(identity(&entry)?, modules);
    let directory = entry.parent().expect("a canonical sidecar has a parent");
    let local_profile = read_c_project_profile(directory, &root)?;
    let root_profile = if directory != root {
        read_c_project_profile(&root, &root)?
    } else {
        None
    };
    let profile = match (local_profile, root_profile) {
        (Some(_), Some(_)) => {
            return Err(format!(
                "Click project has `click.project.json` in both `{}` and `{}`; select one project-level config",
                directory.display(),
                root.display()
            ));
        }
        (Some(profile), None) | (None, Some(profile)) => Some(profile),
        (None, None) => None,
    };
    Ok(match profile {
        Some(profile) => project.with_c_profile(profile),
        None => project,
    })
}

fn load_click_module(
    path: &Path,
    root: &Path,
    sources: &mut BTreeMap<PathBuf, String>,
    resolved_imports: &mut BTreeMap<PathBuf, Vec<PathBuf>>,
    state: &mut BTreeMap<PathBuf, u8>,
    stack: &mut Vec<PathBuf>,
) -> Result<(), String> {
    match state.get(path).copied() {
        Some(2) => return Ok(()),
        Some(1) => {
            let start = stack
                .iter()
                .position(|candidate| candidate == path)
                .unwrap_or(0);
            let mut cycle = stack[start..]
                .iter()
                .map(|item| {
                    item.strip_prefix(root)
                        .unwrap_or(item)
                        .display()
                        .to_string()
                })
                .collect::<Vec<_>>();
            cycle.push(
                path.strip_prefix(root)
                    .unwrap_or(path)
                    .display()
                    .to_string(),
            );
            cycle.truncate(13);
            return Err(format!("Click import cycle: {}", cycle.join(" -> ")));
        }
        _ => {}
    }
    if stack.len() >= 256 {
        return Err(format!(
            "Click import chain exceeds 256 modules while loading `{}`",
            path.display()
        ));
    }
    state.insert(path.to_path_buf(), 1);
    stack.push(path.to_path_buf());
    let source = sources
        .get(path)
        .cloned()
        .ok_or_else(|| format!("Click module `{}` was not loaded", path.display()))?;
    let sites = click_import_sites(&source).map_err(|error| {
        format!(
            "failed to scan imports in `{}`: {}",
            path.display(),
            error.report()
        )
    })?;
    let parent = containing_directory(path);
    let mut imports = Vec::with_capacity(sites.len());
    for site in sites {
        let candidate = parent.join(&site.path);
        let imported = fs::canonicalize(&candidate).map_err(|error| {
            format!(
                "{}:{}:{}: failed to resolve import `{}` from `{}`: {error}",
                path.display(),
                site.position.line,
                site.position.column,
                site.path,
                path.display()
            )
        })?;
        if !imported.starts_with(root) {
            return Err(format!(
                "{}:{}:{}: import `{}` resolves outside project root `{}`",
                path.display(),
                site.position.line,
                site.position.column,
                site.path,
                root.display()
            ));
        }
        if imported
            .extension()
            .is_none_or(|extension| extension != "click")
        {
            return Err(format!(
                "{}:{}:{}: import `{}` is not a `.click` module",
                path.display(),
                site.position.line,
                site.position.column,
                site.path
            ));
        }
        if !sources.contains_key(&imported) {
            let imported_source = fs::read_to_string(&imported).map_err(|error| {
                format!(
                    "failed to read imported module `{}`: {error}",
                    imported.display()
                )
            })?;
            sources.insert(imported.clone(), imported_source);
        }
        imports.push(imported.clone());
        load_click_module(&imported, root, sources, resolved_imports, state, stack)?;
    }
    // Keep source order so the resolver can relate every canonical edge back
    // to its exact import declaration. Graph traversal and artifact hashing
    // sort their own copies where order must not affect meaning.
    resolved_imports.insert(path.to_path_buf(), imports);
    stack.pop();
    state.insert(path.to_path_buf(), 2);
    Ok(())
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

/// One example project selected by a CLI target, with its sidecars in order.
///
/// For a direct sidecar target, `path` is that sidecar and it is the only
/// member of `sidecars`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SelectedProject {
    pub path: PathBuf,
    pub sidecars: Vec<PathBuf>,
}

/// The Click sidecars a `verify`, `profile`, or `audit` target names, grouped
/// by example project, together with the root their local imports resolve
/// within.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SidecarSelection {
    pub project_root: PathBuf,
    pub projects: Vec<SelectedProject>,
}

impl SidecarSelection {
    /// Every selected sidecar, in project order.
    pub fn sidecars(&self) -> impl Iterator<Item = &Path> {
        self.projects
            .iter()
            .flat_map(|project| project.sidecars.iter().map(PathBuf::as_path))
    }
}

/// Selects the sidecars behind a target the way `click verify` does.
///
/// A file is one sidecar whose imports resolve within its own directory. A
/// directory that directly contains a sidecar is one example project; any
/// other directory selects its immediate subdirectories that do. Directory
/// projects resolve imports within the enclosing examples directory, so one
/// example may import another's model.
pub fn select_sidecars(path: &Path) -> Result<SidecarSelection, String> {
    if !path.is_dir() {
        let parent = containing_directory(path);
        return Ok(SidecarSelection {
            project_root: parent.to_path_buf(),
            projects: vec![SelectedProject {
                path: path.to_path_buf(),
                sidecars: vec![path.to_path_buf()],
            }],
        });
    }
    let project_paths = find_projects(path)?;
    let project_root = if contains_click_file(path)? {
        containing_directory(path)
    } else {
        path
    };
    let mut projects = Vec::with_capacity(project_paths.len());
    for project in project_paths {
        let sidecars = project_sidecars(&project)?;
        projects.push(SelectedProject {
            path: project,
            sidecars,
        });
    }
    let selection = SidecarSelection {
        project_root: project_root.to_path_buf(),
        projects,
    };
    if selection.sidecars().next().is_none() {
        return Err(format!(
            "`{}` contains no Click sidecars to verify",
            path.display()
        ));
    }
    Ok(selection)
}

/// What a `profile` or `audit` target selects: markdown tests, or sidecars
/// chosen exactly as `click verify` chooses them.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TargetSelection {
    Mdtests(Vec<PathBuf>),
    Sidecars(SidecarSelection),
}

/// Chooses between mdtest and sidecar mode by shape, not by a flag.
///
/// A `.md` argument names one mdtest. A directory holding real mdtest
/// containers is a mdtest collection even when it also holds local `.click`
/// modules those containers import. Otherwise example projects win, because
/// they carry `README.md` files that must not be mistaken for mdtests; a
/// directory with no sidecar project but some markdown falls back to mdtests.
pub fn select_targets(path: &Path) -> Result<TargetSelection, String> {
    if looks_like_mdtest(path) {
        return find_mdtests(path).map(TargetSelection::Mdtests);
    }
    if !path.is_dir() {
        return select_sidecars(path).map(TargetSelection::Sidecars);
    }
    if directory_contains_mdtests(path)? {
        return find_mdtests(path).map(TargetSelection::Mdtests);
    }
    match select_sidecars(path) {
        Ok(selection) => Ok(TargetSelection::Sidecars(selection)),
        Err(message) => {
            if files_with_extension(path, "md")?.is_empty() {
                Err(message)
            } else {
                find_mdtests(path).map(TargetSelection::Mdtests)
            }
        }
    }
}

/// Returns true when the directory directly contains a recognizable mdtest.
///
/// A malformed container that still has both a Click and an expectation fence
/// counts, so its parse error surfaces instead of the directory silently
/// becoming a Click project merely because it also holds imported modules.
pub fn directory_contains_mdtests(path: &Path) -> Result<bool, String> {
    for markdown in files_with_extension(path, "md")? {
        let source = fs::read_to_string(&markdown)
            .map_err(|error| format!("failed to read `{}`: {error}", markdown.display()))?;
        match parse_mdtest(&markdown, &source) {
            Ok(mdtest) if mdtest.click_source.is_some() && mdtest.expectation.is_some() => {
                return Ok(true);
            }
            Err(_) if source.contains("```click") && source.contains("```expect") => {
                return Ok(true);
            }
            Ok(_) | Err(_) => {}
        }
    }
    Ok(false)
}

/// Reads a sidecar, its transitive local Click imports within
/// `project_root`, and the C inputs its selected target declares.
///
/// `None` uses the sidecar's own directory as the project root.
pub fn load_sidecar_inputs(
    click_path: &Path,
    project_root: Option<&Path>,
) -> Result<(String, ClickProject, CInput), String> {
    let click_source = fs::read_to_string(click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let project = read_click_project_at_root(
        click_path,
        &click_source,
        project_root.unwrap_or_else(|| containing_directory(click_path)),
    )?;
    let inputs = read_c_inputs_for_project(click_path, &click_source, &project)?;
    Ok((click_source, project, inputs))
}

/// One file target of `click verify`, loaded for verification: a sidecar with
/// its imports and declared C inputs, or an mdtest's fenced blocks.
pub struct LoadedTarget {
    pub click_source: String,
    pub project: ClickProject,
    pub inputs: CInput,
    /// The parsed container when the target is an mdtest. Its
    /// `click_start_line` maps lines of the Click block to lines of the file.
    pub mdtest: Option<MdTest>,
}

impl LoadedTarget {
    /// Lines before the Click source inside the target file: zero for a
    /// sidecar, and the lines preceding the ```click block for an mdtest.
    pub fn line_offset(&self) -> usize {
        self.mdtest
            .as_ref()
            .map_or(0, |mdtest| mdtest.click_start_line.saturating_sub(1))
    }
}

/// Loads one file target. A `.md` path is an mdtest whose ```click, ```c, and
/// ```cpp fences are extracted and prepared exactly as the mdtest gate does;
/// its Click imports resolve beside the markdown file. Any other path is a
/// sidecar loaded by [`load_sidecar_inputs`].
pub fn load_target_inputs(
    path: &Path,
    project_root: Option<&Path>,
) -> Result<LoadedTarget, String> {
    if !looks_like_mdtest(path) {
        let (click_source, project, inputs) = load_sidecar_inputs(path, project_root)?;
        return Ok(LoadedTarget {
            click_source,
            project,
            inputs,
            mdtest: None,
        });
    }
    let mdtest = read_mdtest(path)?;
    let click_source = mdtest
        .click_source
        .clone()
        .ok_or_else(|| format!("mdtest `{}` has no ```click block", path.display()))?;
    let inputs = prepare_mdtest_inputs(&mdtest)?;
    let project = read_click_project(path, &click_source)?;
    Ok(LoadedTarget {
        click_source,
        project,
        inputs,
        mdtest: Some(mdtest),
    })
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

/// The sidecars a project directory verifies: its `.click` files, sorted,
/// less the declaration modules
/// ([`crate::surface::click_source_is_declaration_module`]). A module that
/// only declares resources, types, predicates, and pure functions for its
/// importers owns no claim, and it names struct layouts only its importers'
/// `verifying` sources supply, so it is checked where it is imported rather
/// than as an entry of its own.
pub fn project_sidecars(project: &Path) -> Result<Vec<PathBuf>, String> {
    let mut sidecars = Vec::new();
    for path in files_with_extension(project, "click")? {
        let source = fs::read_to_string(&path)
            .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
        if !crate::surface::click_source_is_declaration_module(&source) {
            sidecars.push(path);
        }
    }
    Ok(sidecars)
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
    /// The compiler-imported C++ translation unit, when this is a C++ mdtest.
    pub cpp_source: Option<CppMdTestSource>,
    /// The single ```click block, if the file has one.
    pub click_source: Option<String>,
    /// The one-based line in the `.md` file where the ```click block's first
    /// body line sits, so positions inside the sidecar can be reported as
    /// positions in the markdown file.
    pub click_start_line: usize,
    /// The ```expect block, if the file has one.
    pub expectation: Option<MdTestExpectation>,
}

/// A deliberately small C++ mdtest profile: one translation unit and one
/// selected function, imported through the pinned compiler frontend.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CppMdTestSource {
    pub filename: String,
    pub function: String,
    pub profile: String,
    pub source: String,
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
        cpp_source: None,
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
            Some(BlockKind::Cpp {
                filename,
                function,
                profile,
            }) => {
                if mdtest
                    .cpp_source
                    .replace(CppMdTestSource {
                        filename,
                        function,
                        profile,
                        source: body,
                    })
                    .is_some()
                {
                    return Err(format!(
                        "`{}` has more than one ```cpp block",
                        path.display()
                    ));
                }
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

    if mdtest.cpp_source.is_some() && !mdtest.c_sources.is_empty() {
        return Err(format!(
            "`{}` mixes ```c and ```cpp source blocks",
            path.display()
        ));
    }

    Ok(mdtest)
}

/// Reads and extracts an mdtest from disk.
pub fn read_mdtest(path: &Path) -> Result<MdTest, String> {
    let source = fs::read_to_string(path)
        .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
    parse_mdtest(path, &source)
}

/// Prepares the source representation consumed by every mdtest driver. C++
/// fences go through the same locked semantic import as ordinary C++ sidecars;
/// they never fall back to the C parser.
pub fn prepare_mdtest_inputs(mdtest: &MdTest) -> Result<CInput, String> {
    let Some(cpp) = &mdtest.cpp_source else {
        return Ok(CInput::Bundle(mdtest.c_sources.clone()));
    };
    static NEXT_MDTEST_IMPORT: AtomicUsize = AtomicUsize::new(0);
    let directory = std::env::temp_dir().join(format!(
        "click-cpp-mdtest-{}-{}",
        std::process::id(),
        NEXT_MDTEST_IMPORT.fetch_add(1, Ordering::Relaxed)
    ));
    fs::create_dir(&directory)
        .map_err(|error| format!("failed to create C++ mdtest directory: {error}"))?;
    struct RemoveDirectory(PathBuf);
    impl Drop for RemoveDirectory {
        fn drop(&mut self) {
            let _ = fs::remove_dir_all(&self.0);
        }
    }
    let _guard = RemoveDirectory(directory.clone());
    let exporter = std::env::var_os("CLICK_CPP_EXPORTER")
        .map(PathBuf::from)
        .unwrap_or_else(|| {
            Path::new(env!("CARGO_MANIFEST_DIR")).join("target/cpp-exporter/click-cpp-exporter")
        });
    let exporter = fs::canonicalize(&exporter).map_err(|error| {
        format!(
            "C++ mdtests need the pinned exporter at `{}` ({error}); run scripts/build-cpp-exporter.sh or set CLICK_CPP_EXPORTER",
            exporter.display()
        )
    })?;
    fs::write(directory.join(&cpp.filename), &cpp.source)
        .map_err(|error| format!("failed to materialize C++ mdtest source: {error}"))?;
    let exceptions = cpp.profile == "scalar_int32";
    let arguments = vec![
        "clang++",
        "-x",
        "c++",
        "-std=c++20",
        "--target=x86_64-unknown-linux-gnu",
        if exceptions {
            "-fexceptions"
        } else {
            "-fno-exceptions"
        },
        "-fno-rtti",
        "-funsigned-char",
        "-ffreestanding",
        "-nostdinc",
        "-nostdinc++",
        "-c",
        &cpp.filename,
        "-o",
        "fixture.o",
    ];
    let database = serde_json::json!([{
        "directory": directory,
        "file": cpp.filename,
        "arguments": arguments,
        "output": "fixture.o"
    }]);
    fs::write(
        directory.join("compile_commands.json"),
        serde_json::to_vec_pretty(&database).map_err(|error| error.to_string())?,
    )
    .map_err(|error| format!("failed to materialize C++ compilation database: {error}"))?;
    let config = serde_json::json!({
        "schema": 6,
        "language": "c++",
        "standard": "c++20",
        "target": "x86_64-unknown-linux-gnu",
        "exceptions": exceptions,
        "exception_behavior": cpp.profile,
        "rtti": false,
        "exporter": exporter,
        "compilation_database": "compile_commands.json",
        "working_directory": ".",
        "source": cpp.filename,
        "logical_source": cpp.filename,
        "dependencies": [],
        "function": cpp.function,
        "artifact": "fixture.click-cpp.json"
    });
    let config_path = directory.join("fixture.click.import.json");
    fs::write(
        &config_path,
        serde_json::to_vec_pretty(&config).map_err(|error| error.to_string())?,
    )
    .map_err(|error| format!("failed to materialize C++ import config: {error}"))?;
    crate::languages::cpp::refresh_import(&config_path)?;
    let import = crate::languages::cpp::load_import(&config_path)?;
    Ok(CInput::PreparedCpp(import))
}

enum BlockKind {
    C {
        filename: String,
    },
    Cpp {
        filename: String,
        function: String,
        profile: String,
    },
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
        "cpp" => {
            let attributes = parts.collect::<Vec<_>>();
            let [filename, function, profile] = attributes.as_slice() else {
                return Err(format!(
                    "`{}` has invalid C++ fence at line {line}: expected `cpp filename=NAME.cpp function=NAME profile=normal_only|scalar_int32`",
                    path.display()
                ));
            };
            let filename = filename.strip_prefix("filename=").ok_or_else(|| {
                format!(
                    "`{}` has invalid C++ filename at line {line}",
                    path.display()
                )
            })?;
            if !filename.ends_with(".cpp")
                || Path::new(filename)
                    .file_name()
                    .and_then(|name| name.to_str())
                    != Some(filename)
                || filename == ".cpp"
            {
                return Err(format!(
                    "`{}` has invalid C++ filename `{filename}` at line {line}: use a local .cpp basename",
                    path.display()
                ));
            }
            let function = function
                .strip_prefix("function=")
                .filter(|value| !value.is_empty())
                .ok_or_else(|| {
                    format!(
                        "`{}` has invalid C++ function at line {line}",
                        path.display()
                    )
                })?;
            let profile = profile.strip_prefix("profile=").ok_or_else(|| {
                format!(
                    "`{}` has invalid C++ profile at line {line}",
                    path.display()
                )
            })?;
            if !matches!(profile, "normal_only" | "scalar_int32") {
                return Err(format!(
                    "`{}` has unsupported C++ profile `{profile}` at line {line}",
                    path.display()
                ));
            }
            Ok(Some(BlockKind::Cpp {
                filename: filename.to_string(),
                function: function.to_string(),
                profile: profile.to_string(),
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

    /// A bare file name has an empty `Path::parent`; it selects the current
    /// directory exactly as `./name` does. The command-line regression that
    /// runs every subcommand on a bare name is
    /// `every_cli_tool_accepts_a_bare_sidecar_name` in `src/bin/click.rs`.
    #[test]
    fn a_bare_sidecar_name_selects_the_current_directory() {
        assert_eq!(containing_directory(Path::new("a.click")), Path::new("."));
        assert_eq!(containing_directory(Path::new("./a.click")), Path::new("."));
        assert_eq!(
            containing_directory(Path::new("examples/a.click")),
            Path::new("examples")
        );
        assert_eq!(containing_directory(Path::new("/")), Path::new("."));
        let selection = select_sidecars(Path::new("a.click")).unwrap();
        assert_eq!(selection.project_root, Path::new("."));
    }

    /// A declaration module beside its importers is not a directory entry:
    /// it owns no claim, and a sidecar that owns any (a `verifying` source,
    /// a theorem, a C function proof) is still selected.
    #[test]
    fn directory_selection_skips_declaration_modules() {
        let root = std::env::temp_dir().join(format!(
            "click-declaration-modules-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let _ = fs::remove_dir_all(&root);
        fs::create_dir_all(&root).unwrap();
        // Directory selection canonicalizes paths; macOS temp directories
        // commonly start at /var but resolve beneath /private/var.
        let root = fs::canonicalize(root).unwrap();
        let module = "# Shared resources.\nimport \"other.click\";\n\
            spec enum Shade { Light, Dark(int32) }\n\
            abstract resource token(p: int32*);\n\
            resource cell(p: int32*) { owns p[0..1]; }\n\
            function twice(x: int32) -> int32 { x + x }\n";
        let theorem = "theorem reflexive(x: int32) { ensures x == x by { simp(); } }\n";
        let entry = "import \"module.click\";\nverifying \"answer.c\";\n\
            int32 answer() { ensures result == 1; } by { execute(); simp(); }\n";
        fs::write(root.join("module.click"), module).unwrap();
        fs::write(root.join("theorems.click"), theorem).unwrap();
        fs::write(root.join("entry.click"), entry).unwrap();
        assert!(crate::surface::click_source_is_declaration_module(module));
        assert!(!crate::surface::click_source_is_declaration_module(theorem));
        assert!(!crate::surface::click_source_is_declaration_module(entry));
        assert!(!crate::surface::click_source_is_declaration_module(
            "resource cell(p: int32*) { owns p[0..1]; }\nint32 f() { ensures result == 0; } by { execute(); }\n"
        ));
        let selection = select_sidecars(&root).unwrap();
        assert_eq!(
            selection.sidecars().collect::<Vec<_>>(),
            vec![root.join("entry.click"), root.join("theorems.click")]
        );
        fs::remove_dir_all(&root).unwrap();
    }

    #[test]
    fn project_config_selects_pthread_without_sidecar_profile_directives() {
        let root = std::env::temp_dir().join(format!(
            "click-project-profile-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        fs::create_dir_all(&root).unwrap();
        let click = "verifying \"answer.c\";\nint32 answer() { ensures result == 1; } by { execute(); simp(); }\n";
        let path = root.join("answer.click");
        fs::write(&path, click).unwrap();
        fs::write(
            root.join("answer.c"),
            "#include <pthread.h>\nint answer(void) { return 1; }\n",
        )
        .unwrap();
        fs::write(
            root.join("click.project.json"),
            r#"{"target":"x86_64-linux-userspace","runtime":"modeled-pthread"}"#,
        )
        .unwrap();
        let project = read_click_project(&path, click).unwrap();
        let CInput::Bundle(sources) = read_c_inputs_for_project(&path, click, &project).unwrap()
        else {
            panic!("a project without an import manifest loads its C source bundle");
        };
        let verified = crate::surface::verify_c0_project(&project, &source_refs(&sources)).unwrap();
        assert_eq!(verified.len(), 1);
        assert!(
            verified[0]
                .selection
                .as_ref()
                .unwrap()
                .modeled_pthread_binding
                .is_some()
        );
        assert_eq!(
            crate::surface::selected_project_c_target(&project)
                .unwrap()
                .name(),
            "x86_64-linux-userspace"
        );

        fs::write(
            root.join("click.project.json"),
            r#"{"target":"x86_64-linux-userspace"}"#,
        )
        .unwrap();
        let without_runtime = read_click_project(&path, click).unwrap();
        let ordinary =
            crate::surface::verify_c0_project(&without_runtime, &source_refs(&sources)).unwrap();
        assert_ne!(verified[0].artifact_identity, ordinary[0].artifact_identity);
        assert!(
            ordinary[0]
                .selection
                .as_ref()
                .unwrap()
                .modeled_pthread_binding
                .is_none()
        );

        let conflicting =
            click.replacen("verifying", "target \"x86_64-linux-kernel\";\nverifying", 1);
        fs::write(&path, &conflicting).unwrap();
        let project = read_click_project(&path, &conflicting).unwrap();
        assert!(
            crate::surface::selected_project_c_target(&project)
                .unwrap_err()
                .message()
                .contains("project config")
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn explicit_project_root_supplies_one_profile_to_nested_sidecars() {
        let root = std::env::temp_dir().join(format!(
            "click-project-root-profile-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let nested = root.join("nested");
        fs::create_dir_all(&nested).unwrap();
        fs::write(
            root.join("click.project.json"),
            r#"{"target":"x86_64-linux-userspace","runtime":"modeled-pthread"}"#,
        )
        .unwrap();
        let click = "verifying \"answer.c\";\nint32 answer() { ensures result == 1; } by { execute(); simp(); }\n";
        let path = nested.join("answer.click");
        fs::write(&path, click).unwrap();
        fs::write(
            nested.join("answer.c"),
            "#include <pthread.h>\nint answer(void) { return 1; }\n",
        )
        .unwrap();
        let project = read_click_project_at_root(&path, click, &root).unwrap();
        let CInput::Bundle(sources) = read_c_inputs_for_project(&path, click, &project).unwrap()
        else {
            panic!("nested sidecar should use the root-configured bundle");
        };
        crate::surface::verify_c0_project(&project, &source_refs(&sources)).unwrap();
        fs::write(
            nested.join("click.project.json"),
            r#"{"target":"x86_64-linux-userspace","runtime":"modeled-pthread"}"#,
        )
        .unwrap();
        assert!(
            read_click_project_at_root(&path, click, &root)
                .unwrap_err()
                .contains("both")
        );
        fs::remove_dir_all(root).unwrap();
    }

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
            "```cpp filename=demo.cpp function=demo\nint demo() {}\n```\n",
            "```cpp filename=../demo.cpp function=demo profile=normal_only\nint demo() {}\n```\n",
            "```cpp filename=demo.cpp function=demo profile=unknown\nint demo() {}\n```\n",
            "```click extra\nverifying a.c;\n```\n",
            "```expect extra\npass\n```\n",
        ] {
            assert!(parse_mdtest(path, source).is_err(), "{source}");
        }
    }

    #[test]
    fn mdtest_cpp_fence_selects_a_single_imported_translation_unit() {
        let path = Path::new("cpp.md");
        let source = "```cpp filename=demo.cpp function=demo profile=scalar_int32\nint demo() { throw 7; }\n```\n```click\nverifying \"demo.cpp\";\n```\n```expect\npass\n```\n";
        let mdtest = parse_mdtest(path, source).unwrap();
        assert_eq!(mdtest.c_sources, Vec::new());
        assert_eq!(mdtest.cpp_source.unwrap().profile, "scalar_int32");
        let mixed = "```c filename=demo.c\nint demo();\n```\n```cpp filename=demo.cpp function=demo profile=normal_only\nint demo();\n```\n";
        assert!(parse_mdtest(path, mixed).is_err());
        let duplicate = "```cpp filename=a.cpp function=a profile=normal_only\nint a();\n```\n```cpp filename=b.cpp function=b profile=normal_only\nint b();\n```\n";
        assert!(parse_mdtest(path, duplicate).is_err());
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
            mdtest.replace_click_source(markdown, "step();\n").unwrap(),
            "before\n```click\nstep();\n```\nafter\n"
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
    fn sidecars_load_transitive_local_headers_after_declared_sources() {
        let root = std::env::temp_dir().join(format!(
            "click-source-header-loading-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let project = root.join("project");
        fs::create_dir_all(project.join("include")).unwrap();
        fs::write(
            project.join("main.c"),
            "#include \"include/types.h\"\nint32 main() { return 1; }\n",
        )
        .unwrap();
        fs::write(
            project.join("include/types.h"),
            "#include \"common.h\"\ntypedef int32 index_t;\n",
        )
        .unwrap();
        fs::write(
            project.join("include/common.h"),
            "struct pair { int32 value; };\n",
        )
        .unwrap();
        let click_path = project.join("proof.click");
        let sources = read_verifying_sources(&click_path, "verifying \"main.c\";\n").unwrap();
        assert_eq!(
            sources
                .iter()
                .map(|(name, _)| name.as_str())
                .collect::<Vec<_>>(),
            ["main.c", "include/types.h", "include/common.h"]
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn click_modules_load_transitively_with_stable_relative_identities() {
        let root = std::env::temp_dir().join(format!(
            "click-module-loading-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        fs::create_dir_all(root.join("models")).unwrap();
        fs::write(
            root.join("models/base.click"),
            "function base(x: int32) -> int32 { x }",
        )
        .unwrap();
        fs::write(
            root.join("models/mid.click"),
            "import \"base.click\"; function mid(x: int32) -> int32 { base(x) }",
        )
        .unwrap();
        let entry = root.join("entry.click");
        let source = "import \"models/mid.click\"; theorem ok() { ensures mid(0) == 0 by { unfold(mid(0)); unfold(base(0)); normalize(); } }";
        fs::write(&entry, source).unwrap();
        let project = read_click_project(&entry, source).unwrap();
        assert_eq!(project.entry(), "entry.click");
        assert_eq!(
            project
                .modules()
                .iter()
                .map(|module| module.identity())
                .collect::<Vec<_>>(),
            ["entry.click", "models/base.click", "models/mid.click"]
        );
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn click_module_loader_reports_missing_and_escaping_import_sites() {
        let root = std::env::temp_dir().join(format!(
            "click-module-errors-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        let project_dir = root.join("project");
        fs::create_dir_all(&project_dir).unwrap();
        let entry = project_dir.join("entry.click");
        let missing = "\nimport \"missing.click\";";
        fs::write(&entry, missing).unwrap();
        let error = read_click_project(&entry, missing).unwrap_err();
        assert!(error.contains("entry.click:2:1"), "{error}");
        assert!(error.contains("missing.click"), "{error}");

        fs::write(
            root.join("outside.click"),
            "theorem outside() { ensures 0 == 0 by simp; }",
        )
        .unwrap();
        let escape = "import \"../outside.click\";";
        fs::write(&entry, escape).unwrap();
        let error = read_click_project(&entry, escape).unwrap_err();
        assert!(error.contains("outside project root"), "{error}");
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn click_module_loader_rejects_cycles_before_parsing_proofs() {
        let root = std::env::temp_dir().join(format!(
            "click-module-cycle-{}-{}",
            std::process::id(),
            std::thread::current().name().unwrap_or("test")
        ));
        fs::create_dir_all(&root).unwrap();
        let a = root.join("a.click");
        fs::write(&a, "import \"b.click\";").unwrap();
        fs::write(root.join("b.click"), "import \"a.click\";").unwrap();
        let error = read_click_project(&a, "import \"b.click\";").unwrap_err();
        assert!(error.contains("a.click -> b.click -> a.click"), "{error}");
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
