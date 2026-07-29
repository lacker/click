use std::collections::BTreeMap;
use std::env;
use std::fs;
use std::io::{Read, Write};
use std::path::{Path, PathBuf};
use std::process::{Child, ChildStdin, Command, Stdio};
use std::sync::mpsc::{self, Receiver, RecvTimeoutError};
use std::thread;
use std::time::{Duration, Instant};

use click::cli::{
    self, BoundedOutput, ChildOutput, files_with_extension, find_projects, format_duration,
    parse_duration, read_verifying_sources, run_bounded, run_bounded_with_input, source_refs,
};
use click::lang::click::{
    C0VerificationSession, SourcePosition, c0_smart_tactic_source_sites, c0_tactic_source_position,
    expand_c0_tactic_source_at, verify_c0_sources, verifying_source_paths,
};

const DEFAULT_SESSION_LIMIT: Duration = Duration::from_secs(5 * 60);
const DEFAULT_EXPANSION_LIMIT: Duration = Duration::from_secs(2 * 60);
const DEFAULT_VERIFICATION_LIMIT: Duration = Duration::from_secs(5 * 60);
const MAX_DIAGNOSTIC_CHARS: usize = 2_000;
const USAGE: &str = "\
usage: click-audit [OPTIONS] <example-project|examples-directory>

The audit inventories smart tactics without executing proofs, then audits each
selected site in source order: it expands the site, verifies the rewritten
proof unit in the retained session, reverifies the rewritten sidecar through
the normal whole-file entry point, and re-expands the same site requiring
byte-identical output. By default it stops at the first failure and prints an
inclusive --start-at resume command.

defaults:
  --session-time-limit 5m     original-sidecar session initialization
  --expansion-time-limit 2m   one source expansion
  --verification-time-limit 5m rewritten-sidecar verification

options:
  --session-time-limit <DURATION>
                              (`--discovery-time-limit` is a compatibility alias)
  --expansion-time-limit <DURATION>
  --verification-time-limit <DURATION>
  --start-at <PATH:LINE:COLUMN>
                              inclusively resume at this source location
  --keep-going                continue after failures instead of stopping
  --max-sites <COUNT>         bounded diagnostic run; prints the next cursor";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-audit: {message}");
        std::process::exit(1);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    path: PathBuf,
    session_limit: Duration,
    expansion_limit: Duration,
    verification_limit: Duration,
    start_at: Option<SourceLocation>,
    keep_going: bool,
    max_sites: Option<usize>,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct SourceLocation {
    path: PathBuf,
    line: usize,
    column: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct AuditSite {
    click_path: PathBuf,
    position: SourcePosition,
    claim: String,
    tactic_name: String,
}

struct AuditSessionWorker {
    child: Child,
    stdin: ChildStdin,
    responses: Receiver<Result<(), String>>,
    alive: bool,
}

impl AuditSessionWorker {
    fn start(click_path: &Path, limit: Duration) -> Result<Self, String> {
        let executable =
            env::current_exe().map_err(|error| format!("failed to locate click-audit: {error}"))?;
        let mut child = Command::new(executable)
            .arg("--internal-session-worker")
            .arg(click_path)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::inherit())
            .spawn()
            .map_err(|error| format!("failed to start verification session: {error}"))?;
        let stdin = child
            .stdin
            .take()
            .ok_or_else(|| "failed to open verification-session input".to_string())?;
        let stdout = child
            .stdout
            .take()
            .ok_or_else(|| "failed to open verification-session output".to_string())?;
        let (sender, responses) = mpsc::channel();
        thread::spawn(move || {
            let mut stdout = stdout;
            loop {
                match read_session_response(&mut stdout) {
                    Ok(Some(response)) => {
                        if sender.send(response).is_err() {
                            break;
                        }
                    }
                    Ok(None) => break,
                    Err(error) => {
                        let _ = sender.send(Err(error));
                        break;
                    }
                }
            }
        });
        let mut worker = Self {
            child,
            stdin,
            responses,
            alive: true,
        };
        worker.receive(limit, "verification-session initialization")?;
        Ok(worker)
    }

    fn verify(
        &mut self,
        click_source: &str,
        position: SourcePosition,
        limit: Duration,
    ) -> Result<Duration, String> {
        if !self.alive {
            return Err("verification session is not running".to_string());
        }
        write_session_request(&mut self.stdin, click_source, position).map_err(|error| {
            self.terminate();
            format!("failed to send verification-session request: {error}")
        })?;
        let start = Instant::now();
        self.receive(limit, "rewritten-sidecar verification")?;
        Ok(start.elapsed())
    }

    fn receive(&mut self, limit: Duration, label: &str) -> Result<(), String> {
        match self.responses.recv_timeout(limit) {
            Ok(result) => result,
            Err(RecvTimeoutError::Timeout) => {
                self.terminate();
                Err(format!("{label} exceeded {}", format_duration(limit)))
            }
            Err(RecvTimeoutError::Disconnected) => {
                self.terminate();
                Err(format!("{label} worker exited without a response"))
            }
        }
    }

    fn terminate(&mut self) {
        if self.alive {
            let _ = self.child.kill();
            let _ = self.child.wait();
            self.alive = false;
        }
    }

    fn is_alive(&self) -> bool {
        self.alive
    }
}

impl Drop for AuditSessionWorker {
    fn drop(&mut self) {
        self.terminate();
    }
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
        [command, path] if command == "--internal-session-worker" => {
            Some(run_session_worker(Path::new(path)))
        }
        [command, location] if command == "--internal-expand" => {
            Some(expand_location(location).map(|source| print!("{source}")))
        }
        [command, path] if command == "--internal-verify-rewritten" => {
            Some(verify_rewritten_from_stdin(Path::new(path)))
        }
        [command, location] if command == "--internal-reexpand" => {
            Some(reexpand_from_stdin(location).map(|source| print!("{source}")))
        }
        _ => None,
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut path = None;
    let mut session_limit = DEFAULT_SESSION_LIMIT;
    let mut expansion_limit = DEFAULT_EXPANSION_LIMIT;
    let mut verification_limit = DEFAULT_VERIFICATION_LIMIT;
    let mut start_at = None;
    let mut keep_going = false;
    let mut max_sites = None;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        match argument.as_str() {
            "--session-time-limit" | "--discovery-time-limit" => {
                session_limit = parse_next_duration(&mut arguments, &argument)?;
            }
            "--expansion-time-limit" => {
                expansion_limit = parse_next_duration(&mut arguments, &argument)?;
            }
            "--verification-time-limit" => {
                verification_limit = parse_next_duration(&mut arguments, &argument)?;
            }
            "--start-at" => {
                if start_at.is_some() {
                    return Err("`--start-at` may only be supplied once".to_string());
                }
                let source = arguments
                    .next()
                    .ok_or_else(|| format!("missing location after `{argument}`\n{USAGE}"))?;
                start_at = Some(parse_source_location(&source)?);
            }
            "--keep-going" => keep_going = true,
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
        session_limit,
        expansion_limit,
        verification_limit,
        start_at,
        keep_going,
        max_sites,
    })
}

fn parse_source_location(source: &str) -> Result<SourceLocation, String> {
    let (path, line, column) = cli::parse_source_location(source)?;
    Ok(SourceLocation { path, line, column })
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

fn run_audit(arguments: Arguments) -> Result<(), String> {
    let projects = find_projects(&arguments.path)?;
    println!("INVENTORY");
    let sites = inventory_sites(&projects)?;
    println!("  {} unique smart source sites", sites.len());

    let start_at = arguments
        .start_at
        .as_ref()
        .map(canonicalize_location)
        .transpose()?;
    if let Some(start_at) = &start_at
        && !sites.iter().any(|site| site.click_path == start_at.path)
    {
        return Err(format!(
            "`--start-at` path `{}` has no smart tactic sites in `{}`",
            start_at.path.display(),
            arguments.path.display()
        ));
    }
    let first = first_site_at_or_after(&sites, start_at.as_ref());
    if start_at.is_some() && first == sites.len() {
        return Err("`--start-at` is after the final smart tactic site".to_string());
    }

    let selected = &sites[first..];
    let mut audited_sites = 0;
    let mut site_failures = 0;
    let mut session_failures = 0;
    let mut attempted_sites = 0;
    let mut worker: Option<(PathBuf, AuditSessionWorker)> = None;
    let mut cursor = 0;

    println!(
        "\nClick expansion audit (session {}, expansion {}, verification {})",
        format_duration(arguments.session_limit),
        format_duration(arguments.expansion_limit),
        format_duration(arguments.verification_limit),
    );

    while cursor < selected.len() {
        if arguments
            .max_sites
            .is_some_and(|limit| attempted_sites == limit)
        {
            break;
        }
        let site = &selected[cursor];
        let needs_session = worker
            .as_ref()
            .is_none_or(|(path, current)| path != &site.click_path || !current.is_alive());
        if needs_session {
            worker = None;
            print!("SESSION {} ... ", site.click_path.display());
            std::io::stdout()
                .flush()
                .map_err(|error| format!("failed to flush audit progress: {error}"))?;
            match AuditSessionWorker::start(&site.click_path, arguments.session_limit) {
                Ok(new_worker) => {
                    println!("ready");
                    worker = Some((site.click_path.clone(), new_worker));
                }
                Err(message) => {
                    println!("FAIL");
                    println!("    {}", message.replace('\n', "\n    "));
                    print_resume(&arguments, site);
                    session_failures += 1;
                    if !arguments.keep_going {
                        break;
                    }
                    let failed_path = site.click_path.clone();
                    while cursor < selected.len() && selected[cursor].click_path == failed_path {
                        cursor += 1;
                    }
                    continue;
                }
            }
        }

        attempted_sites += 1;
        let label = format_location(&site_location(site));
        print!(
            "[{}/{}] {label}  {} ({}) ... ",
            first + cursor + 1,
            sites.len(),
            site.claim,
            site.tactic_name,
        );
        std::io::stdout()
            .flush()
            .map_err(|error| format!("failed to flush audit progress: {error}"))?;
        let current = &mut worker
            .as_mut()
            .expect("the selected sidecar session was initialized")
            .1;
        match audit_site(
            site,
            current,
            arguments.expansion_limit,
            arguments.verification_limit,
        ) {
            Ok(timings) => {
                audited_sites += 1;
                println!(
                    "ok (expand {}, verify {}, reverify {}, reexpand {})",
                    format_duration(timings.expansion),
                    format_duration(timings.session_verification),
                    format_duration(timings.reverification),
                    format_duration(timings.reexpansion),
                );
                cursor += 1;
            }
            Err(message) => {
                println!("FAIL");
                println!("    {}", message.replace('\n', "\n    "));
                print_resume(&arguments, site);
                site_failures += 1;
                if !arguments.keep_going {
                    break;
                }
                cursor += 1;
            }
        }
    }

    println!(
        "\nSUMMARY: {audited_sites} sites passed; {site_failures} site failures; \
         {session_failures} session failures; {} sites discovered{}",
        sites.len(),
        if arguments.max_sites.is_some() {
            " (bounded run)"
        } else {
            ""
        }
    );
    let failures = site_failures + session_failures;
    if failures == 0 {
        if cursor < selected.len() {
            println!();
            print_resume(&arguments, &selected[cursor]);
        }
        Ok(())
    } else {
        Err(format!("{failures} expansion audit check(s) failed"))
    }
}

fn inventory_sites(projects: &[PathBuf]) -> Result<Vec<AuditSite>, String> {
    let mut sites = BTreeMap::new();
    for project in projects {
        let mut click_paths = files_with_extension(project, "click")?;
        click_paths.sort();
        for click_path in click_paths {
            let canonical_path = fs::canonicalize(&click_path).map_err(|error| {
                format!("failed to resolve `{}`: {error}", click_path.display())
            })?;
            let click_source = fs::read_to_string(&canonical_path).map_err(|error| {
                format!("failed to read `{}`: {error}", canonical_path.display())
            })?;
            let c_sources = read_verifying_sources(&canonical_path, &click_source)?;
            let refs = source_refs(&c_sources);
            let syntactic_sites =
                c0_smart_tactic_source_sites(&click_source, &refs).map_err(|error| {
                    format!(
                        "could not inventory smart tactics in `{}`: {}",
                        canonical_path.display(),
                        error.message()
                    )
                })?;
            for syntactic in syntactic_sites {
                let position = c0_tactic_source_position(
                    &click_source,
                    &refs,
                    &syntactic.claim_label,
                    syntactic.source_index,
                )
                .map_err(|error| {
                    format!(
                        "could not resolve {} source {} in `{}`: {}",
                        syntactic.claim_label,
                        syntactic.source_index,
                        canonical_path.display(),
                        error.message()
                    )
                })?;
                let key = (canonical_path.clone(), position.line, position.column);
                sites.entry(key).or_insert(AuditSite {
                    click_path: canonical_path.clone(),
                    position,
                    claim: syntactic.claim_label,
                    tactic_name: syntactic.tactic_name,
                });
            }
        }
    }
    Ok(sites.into_values().collect())
}

fn canonicalize_location(location: &SourceLocation) -> Result<SourceLocation, String> {
    let path = fs::canonicalize(&location.path)
        .map_err(|error| format!("failed to resolve `{}`: {error}", location.path.display()))?;
    Ok(SourceLocation {
        path,
        line: location.line,
        column: location.column,
    })
}

fn first_site_at_or_after(sites: &[AuditSite], start: Option<&SourceLocation>) -> usize {
    start.map_or(0, |start| {
        sites.partition_point(|site| site_location(site) < *start)
    })
}

fn site_location(site: &AuditSite) -> SourceLocation {
    SourceLocation {
        path: site.click_path.clone(),
        line: site.position.line,
        column: site.position.column,
    }
}

fn format_location(location: &SourceLocation) -> String {
    format!(
        "{}:{}:{}",
        location.path.display(),
        location.line,
        location.column
    )
}

fn print_resume(arguments: &Arguments, site: &AuditSite) {
    println!("RESUME:");
    println!("  {}", resume_command(arguments, &site_location(site)));
    let _ = std::io::stdout().flush();
}

fn resume_command(arguments: &Arguments, location: &SourceLocation) -> String {
    let mut words = vec![
        "click-audit".to_string(),
        "--session-time-limit".to_string(),
        format_duration(arguments.session_limit),
        "--expansion-time-limit".to_string(),
        format_duration(arguments.expansion_limit),
        "--verification-time-limit".to_string(),
        format_duration(arguments.verification_limit),
    ];
    if arguments.keep_going {
        words.push("--keep-going".to_string());
    }
    if let Some(max_sites) = arguments.max_sites {
        words.push("--max-sites".to_string());
        words.push(max_sites.to_string());
    }
    words.push("--start-at".to_string());
    words.push(format_location(location));
    words.push(arguments.path.display().to_string());
    words
        .into_iter()
        .map(|word| shell_quote(&word))
        .collect::<Vec<_>>()
        .join(" ")
}

fn shell_quote(word: &str) -> String {
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

/// Timings for the checks performed on one audited site.
struct SiteTimings {
    expansion: Duration,
    session_verification: Duration,
    reverification: Duration,
    reexpansion: Duration,
}

fn audit_site(
    site: &AuditSite,
    worker: &mut AuditSessionWorker,
    expansion_limit: Duration,
    verification_limit: Duration,
) -> Result<SiteTimings, String> {
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

    let verification_elapsed = worker.verify(&expanded, site.position, verification_limit)?;

    // Checklist step 6: reverify the rewritten sidecar from normal inputs by
    // running the whole-file entry point in a fresh process under the
    // verification time limit.
    let mut reverification = Command::new(&executable);
    reverification
        .arg("--internal-verify-rewritten")
        .arg(&site.click_path);
    let reverification = require_success(
        run_bounded_with_input(
            reverification,
            Some(expanded.clone().into_bytes()),
            verification_limit,
            "whole-file reverification",
        )?,
        verification_limit,
        "whole-file reverification",
    )?;

    // Checklist step 7: re-expanding the same site against the rewritten
    // source must be a fixed point, byte for byte.
    let mut reexpansion = Command::new(&executable);
    reexpansion.arg("--internal-reexpand").arg(&location);
    let reexpansion = require_success(
        run_bounded_with_input(
            reexpansion,
            Some(expanded.clone().into_bytes()),
            expansion_limit,
            "re-expansion",
        )?,
        expansion_limit,
        "re-expansion",
    )?;
    let reexpanded = String::from_utf8(reexpansion.stdout)
        .map_err(|error| format!("re-expansion output was not UTF-8: {error}"))?;
    if reexpanded != expanded {
        return Err(format!(
            "re-expansion was not byte-identical to the first rewrite \
             ({} bytes rewritten, {} bytes re-expanded)",
            expanded.len(),
            reexpanded.len()
        ));
    }

    // Checklist step 8 (comparing branch/path outcomes between the original
    // and rewritten proofs) is intentionally not implemented yet.

    Ok(SiteTimings {
        expansion: expansion.elapsed,
        session_verification: verification_elapsed,
        reverification: reverification.elapsed,
        reexpansion: reexpansion.elapsed,
    })
}

fn expand_location(location: &str) -> Result<String, String> {
    let (click_path, line, column) = cli::parse_source_location(location)?;
    let click_source = fs::read_to_string(&click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let sources = read_verifying_sources(&click_path, &click_source)?;
    let refs = source_refs(&sources);
    expand_c0_tactic_source_at(&click_source, &refs, line, column)
        .map_err(|error| error.message().to_string())
}

fn read_stdin_source(label: &str) -> Result<String, String> {
    let mut source = String::new();
    std::io::stdin()
        .read_to_string(&mut source)
        .map_err(|error| format!("failed to read {label} from stdin: {error}"))?;
    Ok(source)
}

/// Checklist step 6 worker: verifies a rewritten sidecar, read from stdin,
/// through the normal whole-file entry point, resolving its C sources
/// relative to the original on-disk sidecar path.
fn verify_rewritten_from_stdin(original_click_path: &Path) -> Result<(), String> {
    let rewritten = read_stdin_source("rewritten sidecar")?;
    let sources = read_verifying_sources(original_click_path, &rewritten)?;
    verify_c0_sources(&rewritten, &source_refs(&sources))
        .map(|_| ())
        .map_err(|error| error.message().to_string())
}

/// Checklist step 7 worker: expands the given source location against a
/// rewritten sidecar read from stdin, resolving its C sources relative to the
/// original on-disk sidecar path.
fn reexpand_from_stdin(location: &str) -> Result<String, String> {
    let (click_path, line, column) = cli::parse_source_location(location)?;
    let rewritten = read_stdin_source("rewritten sidecar")?;
    let sources = read_verifying_sources(&click_path, &rewritten)?;
    expand_c0_tactic_source_at(&rewritten, &source_refs(&sources), line, column)
        .map_err(|error| error.message().to_string())
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

fn run_session_worker(click_path: &Path) -> Result<(), String> {
    let click_source = fs::read_to_string(click_path)
        .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
    let c_sources = read_verifying_sources(click_path, &click_source)?;
    let refs = source_refs(&c_sources);
    let session = match C0VerificationSession::new(&click_source, &refs) {
        Ok((session, _)) => {
            write_session_response(&mut std::io::stdout(), Ok(()))?;
            session
        }
        Err(error) => {
            write_session_response(&mut std::io::stdout(), Err(error.message().to_string()))?;
            return Ok(());
        }
    };
    let mut stdin = std::io::stdin();
    loop {
        let Some((rewritten, position)) = read_session_request(&mut stdin)? else {
            return Ok(());
        };
        let result = session
            .verify_at(&rewritten, position.line, position.column)
            .map(|_| ())
            .map_err(|error| error.message().to_string());
        write_session_response(&mut std::io::stdout(), result)?;
    }
}

fn write_session_request(
    output: &mut impl Write,
    click_source: &str,
    position: SourcePosition,
) -> std::io::Result<()> {
    write_u64(output, click_source.len() as u64)?;
    output.write_all(click_source.as_bytes())?;
    write_u64(output, position.line as u64)?;
    write_u64(output, position.column as u64)?;
    output.flush()
}

fn read_session_request(input: &mut impl Read) -> Result<Option<(String, SourcePosition)>, String> {
    let Some(length) = read_u64(input)? else {
        return Ok(None);
    };
    let length = usize::try_from(length)
        .map_err(|_| "verification-session request is too large".to_string())?;
    if length > 64 * 1024 * 1024 {
        return Err("verification-session request exceeds 64 MiB".to_string());
    }
    let mut source = vec![0; length];
    input
        .read_exact(&mut source)
        .map_err(|error| format!("failed to read verification-session source: {error}"))?;
    let line = read_required_u64(input, "line")?;
    let column = read_required_u64(input, "column")?;
    let source = String::from_utf8(source)
        .map_err(|error| format!("verification-session source was not UTF-8: {error}"))?;
    let line =
        usize::try_from(line).map_err(|_| "verification-session line is too large".to_string())?;
    let column = usize::try_from(column)
        .map_err(|_| "verification-session column is too large".to_string())?;
    Ok(Some((source, SourcePosition { line, column })))
}

fn write_session_response(
    output: &mut impl Write,
    result: Result<(), String>,
) -> Result<(), String> {
    let (status, message) = match result {
        Ok(()) => (0_u8, String::new()),
        Err(message) => (1_u8, message),
    };
    output
        .write_all(&[status])
        .and_then(|_| write_u64(output, message.len() as u64))
        .and_then(|_| output.write_all(message.as_bytes()))
        .and_then(|_| output.flush())
        .map_err(|error| format!("failed to write verification-session response: {error}"))
}

fn read_session_response(input: &mut impl Read) -> Result<Option<Result<(), String>>, String> {
    let mut status = [0_u8; 1];
    match input.read(&mut status) {
        Ok(0) => return Ok(None),
        Ok(1) => {}
        Ok(_) => unreachable!("one-byte buffer cannot read more than one byte"),
        Err(error) => {
            return Err(format!(
                "failed to read verification-session response: {error}"
            ));
        }
    }
    let length = read_required_u64(input, "response length")?;
    let length = usize::try_from(length)
        .map_err(|_| "verification-session response is too large".to_string())?;
    let mut message = vec![0; length];
    input
        .read_exact(&mut message)
        .map_err(|error| format!("failed to read verification-session diagnostic: {error}"))?;
    let message = String::from_utf8(message)
        .map_err(|error| format!("verification-session diagnostic was not UTF-8: {error}"))?;
    match status[0] {
        0 if message.is_empty() => Ok(Some(Ok(()))),
        0 => Err("successful verification-session response contained a diagnostic".to_string()),
        1 => Ok(Some(Err(message))),
        other => Err(format!(
            "unknown verification-session response status {other}"
        )),
    }
}

fn write_u64(output: &mut impl Write, value: u64) -> std::io::Result<()> {
    output.write_all(&value.to_le_bytes())
}

fn read_u64(input: &mut impl Read) -> Result<Option<u64>, String> {
    let mut bytes = [0_u8; 8];
    let mut read = 0;
    while read < bytes.len() {
        match input.read(&mut bytes[read..]) {
            Ok(0) if read == 0 => return Ok(None),
            Ok(0) => {
                return Err("verification-session frame ended mid-integer".to_string());
            }
            Ok(count) => read += count,
            Err(error) => {
                return Err(format!(
                    "failed to read verification-session frame: {error}"
                ));
            }
        }
    }
    Ok(Some(u64::from_le_bytes(bytes)))
}

fn read_required_u64(input: &mut impl Read, field: &str) -> Result<u64, String> {
    read_u64(input)?.ok_or_else(|| format!("verification-session frame ended before its {field}"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parses_arguments_and_duration_units() {
        let arguments = parse_arguments(
            [
                "--session-time-limit",
                "30s",
                "--expansion-time-limit",
                "250ms",
                "--verification-time-limit",
                "2m",
                "--start-at",
                "examples/example.click:12:3",
                "--keep-going",
                "--max-sites",
                "3",
                "examples",
            ]
            .map(str::to_string),
        )
        .unwrap();
        assert_eq!(arguments.session_limit, Duration::from_secs(30));
        assert_eq!(arguments.expansion_limit, Duration::from_millis(250));
        assert_eq!(arguments.verification_limit, Duration::from_secs(120));
        assert_eq!(
            arguments.start_at,
            Some(SourceLocation {
                path: PathBuf::from("examples/example.click"),
                line: 12,
                column: 3,
            })
        );
        assert!(arguments.keep_going);
        assert_eq!(arguments.max_sites, Some(3));
        assert_eq!(arguments.path, PathBuf::from("examples"));
    }

    #[test]
    fn source_locations_parse_from_the_right_and_are_one_based() {
        assert_eq!(
            parse_source_location("some:directory/example.click:12:34").unwrap(),
            SourceLocation {
                path: PathBuf::from("some:directory/example.click"),
                line: 12,
                column: 34,
            }
        );
        assert!(parse_source_location("example.click:0:1").is_err());
        assert!(parse_source_location("example.click:1").is_err());
    }

    #[test]
    fn resume_command_retries_the_cursor_inclusively() {
        let arguments = Arguments {
            path: PathBuf::from("examples with spaces"),
            session_limit: Duration::from_secs(30),
            expansion_limit: Duration::from_secs(2),
            verification_limit: Duration::from_secs(3),
            start_at: None,
            keep_going: false,
            max_sites: Some(1),
        };
        let location = SourceLocation {
            path: PathBuf::from("/tmp/example.click"),
            line: 12,
            column: 34,
        };
        assert_eq!(
            resume_command(&arguments, &location),
            "click-audit --session-time-limit 30s --expansion-time-limit 2s \
             --verification-time-limit 3s --max-sites 1 --start-at \
             /tmp/example.click:12:34 'examples with spaces'"
        );
    }

    #[test]
    fn start_cursor_is_an_inclusive_global_lower_bound() {
        let site = |path: &str, line| AuditSite {
            click_path: PathBuf::from(path),
            position: SourcePosition { line, column: 3 },
            claim: "claim".to_string(),
            tactic_name: "simp".to_string(),
        };
        let sites = vec![
            site("/tmp/a.click", 10),
            site("/tmp/a.click", 20),
            site("/tmp/b.click", 5),
        ];
        assert_eq!(
            first_site_at_or_after(
                &sites,
                Some(&SourceLocation {
                    path: PathBuf::from("/tmp/a.click"),
                    line: 20,
                    column: 3,
                })
            ),
            1
        );
        assert_eq!(
            first_site_at_or_after(
                &sites,
                Some(&SourceLocation {
                    path: PathBuf::from("/tmp/a.click"),
                    line: 15,
                    column: 1,
                })
            ),
            1
        );
    }

    #[test]
    fn session_protocol_round_trips_requests_and_responses() {
        let position = SourcePosition {
            line: 12,
            column: 34,
        };
        let mut request = Vec::new();
        write_session_request(&mut request, "proof source λ", position).unwrap();
        assert_eq!(
            read_session_request(&mut request.as_slice()).unwrap(),
            Some(("proof source λ".to_string(), position))
        );

        let mut success = Vec::new();
        write_session_response(&mut success, Ok(())).unwrap();
        assert_eq!(
            read_session_response(&mut success.as_slice()).unwrap(),
            Some(Ok(()))
        );

        let mut failure = Vec::new();
        write_session_response(&mut failure, Err("bad certificate".to_string())).unwrap();
        assert_eq!(
            read_session_response(&mut failure.as_slice()).unwrap(),
            Some(Err("bad certificate".to_string()))
        );
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
        let inventory = c0_smart_tactic_source_sites(click_source, &sources).unwrap();
        assert_eq!(
            inventory
                .iter()
                .map(|site| (
                    site.claim_label.as_str(),
                    site.source_index,
                    site.tactic_name.as_str()
                ))
                .collect::<Vec<_>>(),
            vec![
                ("example.contract", 0, "execute_rest"),
                ("example.contract", 1, "simp"),
            ]
        );
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
    fn inventory_does_not_advertise_loop_invariants_as_proof_sites() {
        let c_source = r#"
int32 count_to_one() {
    int32 i;
    i = 0;
    while (i < 1) {
        i = i + 1;
    }
    return i;
}
"#;
        let click_source = r#"
verifying "loop.c";

int32 count_to_one() {
    for loop(0) {
        invariant i >= 0 and i <= 1;
        initialize by simp;
        preserve by simp;
    }
    ensures result == 1;
} by auto;
"#;
        let sources = [("loop.c", c_source)];
        let inventory = c0_smart_tactic_source_sites(click_source, &sources).unwrap();

        assert!(
            inventory
                .iter()
                .all(|site| !site.claim_label.contains(".invariant_")),
            "{inventory:?}"
        );
        assert!(inventory.iter().any(|site| {
            site.claim_label == "count_to_one.loop(0).initialize" && site.tactic_name == "simp"
        }));
        assert!(inventory.iter().any(|site| {
            site.claim_label == "count_to_one.loop(0).preserve" && site.tactic_name == "simp"
        }));
    }

    #[test]
    fn truncates_large_child_diagnostics_at_character_boundaries() {
        let diagnostic = "λ".repeat(MAX_DIAGNOSTIC_CHARS + 2);
        let truncated = truncate_diagnostic(&diagnostic);
        assert!(truncated.starts_with(&"λ".repeat(MAX_DIAGNOSTIC_CHARS)));
        assert!(truncated.ends_with("2 more characters)"));
    }
}
