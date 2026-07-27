use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Command, ExitStatus, Stdio};
use std::sync::atomic::{AtomicU64, Ordering};
use std::thread;
use std::time::{Duration, Instant};

use click::lang::click::{
    SourcePosition, c0_tactic_source_position, expand_c0_tactic_source_at, verify_c0_sources,
    verifying_source_paths,
};

const DEFAULT_DISCOVERY_LIMIT: Duration = Duration::from_secs(5 * 60);
const DEFAULT_EXPANSION_LIMIT: Duration = Duration::from_secs(2 * 60);
const DEFAULT_VERIFICATION_LIMIT: Duration = Duration::from_secs(5 * 60);
const MAX_DIAGNOSTIC_CHARS: usize = 2_000;
const USAGE: &str = "\
usage: click-audit [OPTIONS] <example-project|examples-directory>

The audit verifies each original project, inventories every smart tactic, then
expands and fully verifies each site against a fresh temporary project copy.

defaults:
  --discovery-time-limit 5m   original verification and site inventory
  --expansion-time-limit 2m   one source expansion
  --verification-time-limit 5m rewritten-project verification

options:
  --discovery-time-limit <DURATION>
  --expansion-time-limit <DURATION>
  --verification-time-limit <DURATION>
  --max-sites <COUNT>         bounded diagnostic run; omitted for a full audit";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-audit: {message}");
        std::process::exit(1);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    path: PathBuf,
    discovery_limit: Duration,
    expansion_limit: Duration,
    verification_limit: Duration,
    max_sites: Option<usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AuditSite {
    click_path: PathBuf,
    position: SourcePosition,
    claim: String,
    tactic_name: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TimingSite {
    click_path: PathBuf,
    claim: String,
    source_index: usize,
    tactic_name: String,
}

#[derive(Debug)]
struct ChildOutput {
    status: ExitStatus,
    stdout: Vec<u8>,
    stderr: Vec<u8>,
    elapsed: Duration,
}

#[derive(Debug)]
enum BoundedOutput {
    Completed(ChildOutput),
    TimedOut {
        stdout: Vec<u8>,
        stderr: Vec<u8>,
        elapsed: Duration,
    },
}

fn entry() -> Result<(), String> {
    let raw = env::args().skip(1).collect::<Vec<_>>();
    if let Some(result) = run_internal_command(&raw) {
        return result;
    }
    if matches!(raw.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    run_audit(parse_arguments(raw)?)
}

fn run_internal_command(arguments: &[String]) -> Option<Result<(), String>> {
    match arguments {
        [command, path] if command == "--internal-inventory" => {
            Some(verify_project(Path::new(path)))
        }
        [command, path] if command == "--internal-verify" => Some(verify_project(Path::new(path))),
        [command, location] if command == "--internal-expand" => {
            Some(expand_location(location).map(|source| print!("{source}")))
        }
        _ => None,
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut path = None;
    let mut discovery_limit = DEFAULT_DISCOVERY_LIMIT;
    let mut expansion_limit = DEFAULT_EXPANSION_LIMIT;
    let mut verification_limit = DEFAULT_VERIFICATION_LIMIT;
    let mut max_sites = None;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--discovery-time-limit" => {
                discovery_limit = parse_next_duration(&mut arguments, &argument)?;
            }
            "--expansion-time-limit" => {
                expansion_limit = parse_next_duration(&mut arguments, &argument)?;
            }
            "--verification-time-limit" => {
                verification_limit = parse_next_duration(&mut arguments, &argument)?;
            }
            "--max-sites" => {
                let source = arguments
                    .next()
                    .ok_or_else(|| format!("missing count after `{argument}`\n{USAGE}"))?;
                let count = source
                    .parse::<usize>()
                    .map_err(|_| format!("invalid site count `{source}`"))?;
                if count == 0 {
                    return Err("site count must be greater than zero".to_string());
                }
                max_sites = Some(count);
            }
            _ if argument.starts_with('-') => {
                return Err(format!("unknown option `{argument}`\n{USAGE}"));
            }
            _ if path.is_none() => path = Some(PathBuf::from(argument)),
            _ => return Err(USAGE.to_string()),
        }
    }
    Ok(Arguments {
        path: path.ok_or_else(|| USAGE.to_string())?,
        discovery_limit,
        expansion_limit,
        verification_limit,
        max_sites,
    })
}

fn parse_next_duration(
    arguments: &mut impl Iterator<Item = String>,
    option: &str,
) -> Result<Duration, String> {
    let source = arguments
        .next()
        .ok_or_else(|| format!("missing duration after `{option}`\n{USAGE}"))?;
    parse_duration(&source)
}

fn parse_duration(source: &str) -> Result<Duration, String> {
    let (digits, multiplier) = if let Some(digits) = source.strip_suffix("ms") {
        (digits, 1_u128)
    } else if let Some(digits) = source.strip_suffix('s') {
        (digits, 1_000)
    } else if let Some(digits) = source.strip_suffix('m') {
        (digits, 60_000)
    } else {
        (source, 1_000)
    };
    let amount = digits.parse::<u128>().map_err(|_| {
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

fn run_audit(arguments: Arguments) -> Result<(), String> {
    let projects = find_projects(&arguments.path)?;
    let mut audited_sites = 0;
    let mut discovered_sites = 0;
    let mut site_failures = 0;
    let mut project_failures = 0;
    let mut limit_remaining = arguments.max_sites;

    println!(
        "Click expansion audit (discovery {}, expansion {}, verification {})",
        format_duration(arguments.discovery_limit),
        format_duration(arguments.expansion_limit),
        format_duration(arguments.verification_limit),
    );
    for project in projects {
        let project_name = project
            .file_name()
            .and_then(|name| name.to_str())
            .unwrap_or("example");
        println!("\nDISCOVER {project_name}");
        let sites = match discover_sites(&project, arguments.discovery_limit) {
            Ok(sites) => sites,
            Err(message) => {
                println!("  FAIL {message}");
                project_failures += 1;
                continue;
            }
        };
        discovered_sites += sites.len();
        println!("  {} unique smart source sites", sites.len());
        for (index, site) in sites.iter().enumerate() {
            if limit_remaining == Some(0) {
                break;
            }
            if let Some(remaining) = &mut limit_remaining {
                *remaining -= 1;
            }
            let label = format!(
                "{}:{}:{}",
                site.click_path.display(),
                site.position.line,
                site.position.column
            );
            print!(
                "  [{}/{}] {label}  {} ({}) ... ",
                index + 1,
                sites.len(),
                site.claim,
                site.tactic_name,
            );
            std::io::stdout()
                .flush()
                .map_err(|error| format!("failed to flush audit progress: {error}"))?;
            match audit_site(
                &project,
                site,
                arguments.expansion_limit,
                arguments.verification_limit,
            ) {
                Ok((expansion_elapsed, verification_elapsed)) => {
                    audited_sites += 1;
                    println!(
                        "ok (expand {}, verify {})",
                        format_duration(expansion_elapsed),
                        format_duration(verification_elapsed)
                    );
                }
                Err(message) => {
                    println!("FAIL");
                    println!("      {}", message.replace('\n', "\n      "));
                    site_failures += 1;
                }
            }
        }
        if limit_remaining == Some(0) {
            break;
        }
    }

    println!(
        "\nSUMMARY: {audited_sites} sites passed; {site_failures} site failures; \
         {project_failures} project failures; {discovered_sites} sites discovered{}",
        if arguments.max_sites.is_some() {
            " (bounded run)"
        } else {
            ""
        }
    );
    let failures = site_failures + project_failures;
    if failures == 0 {
        Ok(())
    } else {
        Err(format!("{failures} expansion audit check(s) failed"))
    }
}

fn discover_sites(project: &Path, limit: Duration) -> Result<Vec<AuditSite>, String> {
    let executable =
        env::current_exe().map_err(|error| format!("failed to locate click-audit: {error}"))?;
    let mut command = Command::new(executable);
    command
        .arg("--internal-inventory")
        .arg(project)
        .env("CLICK_TIMINGS", "1");
    let output = run_bounded(command, limit, "project discovery")?;
    let completed = require_success(output, limit, "project discovery")?;
    let timings = parse_smart_timing_sites(&String::from_utf8_lossy(&completed.stderr))?;
    resolve_sites(timings)
}

fn parse_smart_timing_sites(output: &str) -> Result<Vec<TimingSite>, String> {
    let mut click_path = PathBuf::new();
    let mut sites = Vec::new();
    for line in output.lines() {
        if let Some(path) = line.strip_prefix("click timing: source ") {
            click_path = PathBuf::from(path);
            continue;
        }
        let fields = line.split_whitespace().collect::<Vec<_>>();
        if fields.len() != 13
            || fields[..3] != ["click", "timing:", "tactic"]
            || fields[6..8] != ["class", "smart"]
            || fields[10] != "source"
        {
            continue;
        }
        if click_path.as_os_str().is_empty() {
            return Err("smart timing event had no Click source path".to_string());
        }
        sites.push(TimingSite {
            click_path: click_path.clone(),
            claim: fields[3].to_string(),
            tactic_name: fields[5].to_string(),
            source_index: fields[11]
                .parse()
                .map_err(|_| format!("invalid timing source index `{}`", fields[11]))?,
        });
    }
    Ok(sites)
}

fn resolve_sites(timings: Vec<TimingSite>) -> Result<Vec<AuditSite>, String> {
    let mut source_cache = BTreeMap::<PathBuf, (String, Vec<(String, String)>)>::new();
    let mut sites = BTreeMap::new();
    for timing in timings {
        let canonical_path = fs::canonicalize(&timing.click_path).map_err(|error| {
            format!(
                "failed to resolve `{}` from timing output: {error}",
                timing.click_path.display()
            )
        })?;
        let (click_source, c_sources) = match source_cache.get(&canonical_path) {
            Some(cached) => cached,
            None => {
                let click_source = fs::read_to_string(&canonical_path).map_err(|error| {
                    format!("failed to read `{}`: {error}", canonical_path.display())
                })?;
                let parent = canonical_path.parent().unwrap_or_else(|| Path::new("."));
                let mut c_paths = files_with_extension(parent, "c")?;
                c_paths.sort();
                let c_sources = read_named_sources(&c_paths)?;
                source_cache
                    .entry(canonical_path.clone())
                    .or_insert((click_source, c_sources))
            }
        };
        let refs = source_refs(c_sources);
        let position =
            c0_tactic_source_position(click_source, &refs, &timing.claim, timing.source_index)
                .map_err(|error| {
                    format!(
                        "could not resolve {} source {} in `{}`: {}",
                        timing.claim,
                        timing.source_index,
                        canonical_path.display(),
                        error.message()
                    )
                })?;
        let key = (canonical_path.clone(), position.line, position.column);
        sites.entry(key).or_insert(AuditSite {
            click_path: canonical_path,
            position,
            claim: timing.claim,
            tactic_name: timing.tactic_name,
        });
    }
    Ok(sites.into_values().collect())
}

fn audit_site(
    project: &Path,
    site: &AuditSite,
    expansion_limit: Duration,
    verification_limit: Duration,
) -> Result<(Duration, Duration), String> {
    let executable =
        env::current_exe().map_err(|error| format!("failed to locate click-audit: {error}"))?;
    let location = format!(
        "{}:{}:{}",
        site.click_path.display(),
        site.position.line,
        site.position.column
    );
    let mut expansion = Command::new(&executable);
    expansion.arg("--internal-expand").arg(&location);
    let expansion = require_success(
        run_bounded(expansion, expansion_limit, "expansion")?,
        expansion_limit,
        "expansion",
    )?;
    let expanded = String::from_utf8(expansion.stdout)
        .map_err(|error| format!("expansion output was not UTF-8: {error}"))?;
    let original = fs::read_to_string(&site.click_path)
        .map_err(|error| format!("failed to reread `{}`: {error}", site.click_path.display()))?;
    if expanded == original {
        return Err("expansion returned the original sidecar unchanged".to_string());
    }
    verifying_source_paths(&expanded)
        .map_err(|error| format!("expanded sidecar did not parse: {}", error.message()))?;

    let project = fs::canonicalize(project)
        .map_err(|error| format!("failed to resolve `{}`: {error}", project.display()))?;
    let relative_sidecar = site.click_path.strip_prefix(&project).map_err(|_| {
        format!(
            "timing sidecar `{}` is outside project `{}`",
            site.click_path.display(),
            project.display()
        )
    })?;
    let temporary = TemporaryProject::copy_from(&project)?;
    let rewritten_path = temporary.path().join(relative_sidecar);
    fs::write(&rewritten_path, expanded)
        .map_err(|error| format!("failed to write `{}`: {error}", rewritten_path.display()))?;

    let mut verification = Command::new(executable);
    verification.arg("--internal-verify").arg(temporary.path());
    let verification = require_success(
        run_bounded(verification, verification_limit, "rewritten verification")?,
        verification_limit,
        "rewritten verification",
    )?;
    Ok((expansion.elapsed, verification.elapsed))
}

fn expand_location(location: &str) -> Result<String, String> {
    let (path_and_line, column) = location
        .rsplit_once(':')
        .ok_or_else(|| format!("invalid source location `{location}`"))?;
    let (path, line) = path_and_line
        .rsplit_once(':')
        .ok_or_else(|| format!("invalid source location `{location}`"))?;
    let line = line
        .parse::<usize>()
        .map_err(|_| format!("invalid source line `{line}`"))?;
    let column = column
        .parse::<usize>()
        .map_err(|_| format!("invalid source column `{column}`"))?;
    let click_path = Path::new(path);
    let click_source = fs::read_to_string(click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let parent = click_path.parent().unwrap_or_else(|| Path::new("."));
    let sources = verifying_source_paths(&click_source)
        .map_err(|error| error.message().to_string())?
        .into_iter()
        .map(|name| {
            let source = fs::read_to_string(parent.join(&name))
                .map_err(|error| format!("failed to read `{name}`: {error}"))?;
            Ok((name, source))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let refs = source_refs(&sources);
    expand_c0_tactic_source_at(&click_source, &refs, line, column)
        .map_err(|error| error.message().to_string())
}

fn run_bounded(
    mut command: Command,
    limit: Duration,
    label: &str,
) -> Result<BoundedOutput, String> {
    let mut child = command
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|error| format!("failed to start {label}: {error}"))?;
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

fn require_success(
    output: BoundedOutput,
    limit: Duration,
    label: &str,
) -> Result<ChildOutput, String> {
    match output {
        BoundedOutput::TimedOut {
            stdout,
            stderr,
            elapsed,
        } => {
            let diagnostic = child_diagnostic(&stdout, &stderr);
            Err(format!(
                "{label} exceeded {} after {}{}",
                format_duration(limit),
                format_duration(elapsed),
                if diagnostic.is_empty() {
                    String::new()
                } else {
                    format!("\nlast diagnostics:\n{diagnostic}")
                }
            ))
        }
        BoundedOutput::Completed(output) if output.status.success() => Ok(output),
        BoundedOutput::Completed(output) => {
            let diagnostic = child_diagnostic(&output.stdout, &output.stderr);
            Err(if diagnostic.is_empty() {
                format!("{label} exited with {}", output.status)
            } else {
                format!("{label} failed:\n{diagnostic}")
            })
        }
    }
}

fn child_diagnostic(stdout: &[u8], stderr: &[u8]) -> String {
    let stderr = String::from_utf8_lossy(stderr);
    let stderr = stderr
        .lines()
        .filter(|line| !line.starts_with("click timing:"))
        .collect::<Vec<_>>()
        .join("\n");
    if !stderr.trim().is_empty() {
        let diagnostic = stderr
            .trim()
            .strip_prefix("click-audit: ")
            .unwrap_or(stderr.trim());
        return truncate_diagnostic(diagnostic);
    }
    truncate_diagnostic(String::from_utf8_lossy(stdout).trim())
}

fn truncate_diagnostic(diagnostic: &str) -> String {
    let Some((cut, _)) = diagnostic.char_indices().nth(MAX_DIAGNOSTIC_CHARS) else {
        return diagnostic.to_string();
    };
    format!(
        "{}\n... diagnostic truncated ({} more characters)",
        &diagnostic[..cut],
        diagnostic.chars().count() - MAX_DIAGNOSTIC_CHARS
    )
}

fn verify_project(project: &Path) -> Result<(), String> {
    let mut c_paths = files_with_extension(project, "c")?;
    let mut click_paths = files_with_extension(project, "click")?;
    c_paths.sort();
    click_paths.sort();
    if click_paths.is_empty() {
        return Err(format!("`{}` has no Click sidecar", project.display()));
    }
    let c_sources = read_named_sources(&c_paths)?;
    let refs = source_refs(&c_sources);
    for click_path in click_paths {
        let click_source = fs::read_to_string(&click_path)
            .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
        if env::var_os("CLICK_TIMINGS").is_some() {
            eprintln!("click timing: source {}", click_path.display());
        }
        verify_c0_sources(&click_source, &refs).map_err(|error| {
            format!(
                "sidecar `{}` failed: {}",
                click_path.display(),
                error.message()
            )
        })?;
    }
    Ok(())
}

fn find_projects(path: &Path) -> Result<Vec<PathBuf>, String> {
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

fn contains_click_file(path: &Path) -> Result<bool, String> {
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

fn files_with_extension(directory: &Path, extension: &str) -> Result<Vec<PathBuf>, String> {
    Ok(fs::read_dir(directory)
        .map_err(|error| format!("failed to read `{}`: {error}", directory.display()))?
        .filter_map(Result::ok)
        .map(|entry| entry.path())
        .filter(|path| path.extension().is_some_and(|actual| actual == extension))
        .collect())
}

fn read_named_sources(paths: &[PathBuf]) -> Result<Vec<(String, String)>, String> {
    paths
        .iter()
        .map(|path| {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or_else(|| format!("invalid UTF-8 path `{}`", path.display()))?
                .to_string();
            let source = fs::read_to_string(path)
                .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
            Ok((name, source))
        })
        .collect()
}

fn source_refs(sources: &[(String, String)]) -> Vec<(&str, &str)> {
    sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect()
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

fn format_duration(duration: Duration) -> String {
    let milliseconds = duration.as_millis();
    if milliseconds % 60_000 == 0 {
        format!("{}m", milliseconds / 60_000)
    } else if milliseconds % 1_000 == 0 {
        format!("{}s", milliseconds / 1_000)
    } else {
        format!("{milliseconds}ms")
    }
}

static TEMP_SEQUENCE: AtomicU64 = AtomicU64::new(0);

struct TemporaryProject {
    path: PathBuf,
}

impl TemporaryProject {
    fn copy_from(source: &Path) -> Result<Self, String> {
        let sequence = TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed);
        let path = env::temp_dir().join(format!("click-audit-{}-{sequence}", std::process::id()));
        fs::create_dir(&path)
            .map_err(|error| format!("failed to create `{}`: {error}", path.display()))?;
        if let Err(error) = copy_directory(source, &path) {
            let _ = fs::remove_dir_all(&path);
            return Err(error);
        }
        Ok(Self { path })
    }

    fn path(&self) -> &Path {
        &self.path
    }
}

impl Drop for TemporaryProject {
    fn drop(&mut self) {
        let _ = fs::remove_dir_all(&self.path);
    }
}

fn copy_directory(source: &Path, target: &Path) -> Result<(), String> {
    for entry in fs::read_dir(source)
        .map_err(|error| format!("failed to read `{}`: {error}", source.display()))?
    {
        let entry = entry.map_err(|error| format!("failed to read directory entry: {error}"))?;
        let source_path = entry.path();
        let target_path = target.join(entry.file_name());
        if source_path.is_dir() {
            fs::create_dir(&target_path).map_err(|error| {
                format!("failed to create `{}`: {error}", target_path.display())
            })?;
            copy_directory(&source_path, &target_path)?;
        } else {
            fs::copy(&source_path, &target_path).map_err(|error| {
                format!(
                    "failed to copy `{}` to `{}`: {error}",
                    source_path.display(),
                    target_path.display()
                )
            })?;
        }
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_arguments_and_duration_units() {
        let arguments = parse_arguments(
            [
                "--discovery-time-limit",
                "30s",
                "--expansion-time-limit",
                "250ms",
                "--verification-time-limit",
                "2m",
                "--max-sites",
                "3",
                "examples",
            ]
            .map(str::to_string),
        )
        .unwrap();
        assert_eq!(arguments.discovery_limit, Duration::from_secs(30));
        assert_eq!(arguments.expansion_limit, Duration::from_millis(250));
        assert_eq!(arguments.verification_limit, Duration::from_secs(120));
        assert_eq!(arguments.max_sites, Some(3));
        assert_eq!(arguments.path, PathBuf::from("examples"));
    }

    #[test]
    fn parses_and_deduplicates_completed_smart_timing_sites() {
        let output = "\
click timing: source example.click
click timing: tactic f.contract 2 simp class smart statement 1 source 2 0.100000s
click timing: tactic f.contract 2 assumption class simple statement 1 source 2 0.001000s
click timing: tactic f.contract 2 simp class smart statement 1 source 2 0.200000s
";
        let sites = parse_smart_timing_sites(output).unwrap();
        assert_eq!(sites.len(), 2);
        assert!(sites.iter().all(|site| site.claim == "f.contract"));
        assert!(sites.iter().all(|site| site.source_index == 2));
    }

    #[test]
    fn copies_temporary_projects_and_removes_them_on_drop() {
        let root = env::temp_dir().join(format!(
            "click-audit-copy-test-{}-{}",
            std::process::id(),
            TEMP_SEQUENCE.fetch_add(1, Ordering::Relaxed)
        ));
        fs::create_dir(&root).unwrap();
        fs::write(root.join("example.click"), "source").unwrap();
        let copied_path = {
            let copied = TemporaryProject::copy_from(&root).unwrap();
            assert_eq!(
                fs::read_to_string(copied.path().join("example.click")).unwrap(),
                "source"
            );
            copied.path().to_path_buf()
        };
        assert!(!copied_path.exists());
        fs::remove_dir_all(root).unwrap();
    }

    #[test]
    fn bounded_children_are_killed_at_their_limit() {
        let mut command = Command::new("sleep");
        command.arg("1");
        let output = run_bounded(command, Duration::from_millis(10), "test sleeper").unwrap();
        assert!(matches!(output, BoundedOutput::TimedOut { .. }));
    }

    #[test]
    fn expanded_tiny_project_reparses_and_verifies() {
        let c_source = "int32 example() { return 0; }";
        let click_source = r#"
verifying "example.c";

int32 example() {
    ensures result == 0;
} by {
    execute_rest();
    simp();
}
"#;
        let sources = [("example.c", c_source)];
        verify_c0_sources(click_source, &sources).unwrap();
        let position =
            c0_tactic_source_position(click_source, &sources, "example.contract", 0).unwrap();
        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
                .unwrap();

        assert_ne!(expanded, click_source);
        verifying_source_paths(&expanded).unwrap();
        verify_c0_sources(&expanded, &sources).unwrap();
    }

    #[test]
    fn truncates_large_child_diagnostics_at_character_boundaries() {
        let diagnostic = "λ".repeat(MAX_DIAGNOSTIC_CHARS + 2);
        let truncated = truncate_diagnostic(&diagnostic);
        assert!(truncated.starts_with(&"λ".repeat(MAX_DIAGNOSTIC_CHARS)));
        assert!(truncated.ends_with("2 more characters)"));
    }
}
