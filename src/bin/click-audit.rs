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
    self, BoundedOutput, ChildOutput, MdTestExpectation, files_with_extension, find_mdtests,
    find_projects, format_duration, looks_like_mdtest, parse_duration, read_verifying_sources,
    run_bounded, run_bounded_with_input, source_refs,
};
use click::lang::click::{
    C0VerificationSession, SourcePosition, c0_smart_tactic_source_sites, c0_tactic_source_position,
    expand_c0_tactic_source_at, verify_c0_sources_at,
};

const DEFAULT_SESSION_LIMIT: Duration = Duration::from_secs(5 * 60);
const DEFAULT_EXPANSION_LIMIT: Duration = Duration::from_secs(2 * 60);
const DEFAULT_VERIFICATION_LIMIT: Duration = Duration::from_secs(5 * 60);
const DEFAULT_PERFORMANCE_SLACK: Duration = Duration::from_millis(500);
const DEFAULT_TIME_LIMIT: Duration = Duration::from_secs(10 * 60);
const MAX_DIAGNOSTIC_CHARS: usize = 2_000;
const USAGE: &str = "\
usage: click-audit [OPTIONS] <example-project|examples-directory|mdtest.md|mdtests-directory|repository-root>

The audit inventories smart tactics without executing proofs, then audits each
selected site in source order: it expands the site, verifies the rewritten
proof unit in the retained session, reverifies that proof unit through the
normal targeted entry point in a fresh process, and checks the rewrite is an
expansion fixed point (the audited smart tactic is gone from its claim and
the emitted expansion introduced no new smart tactic). By default it stops at
the first failure and prints an inclusive --start-at resume command.

Raw phase time grows with proof-unit size and is reported but is not itself a
failure. On the first site of each claim, audit compares cold verification of
the expanded proof with the original proof in the same run. A regression must
be both over 2x and over the performance slack, then repeat once, to fail.
Hard child and whole-run limits remain safety failures.

defaults:
  --session-time-limit 5m     original-sidecar session initialization
  --expansion-time-limit 2m   one source expansion
  --verification-time-limit 5m rewritten-sidecar verification
  --performance-slack 500ms   minimum same-run expanded verification regression
  --time-limit 10m            whole-run wall clock; prints the resume cursor

options:
  --session-time-limit <DURATION>
                              (`--discovery-time-limit` is a compatibility alias)
  --expansion-time-limit <DURATION>
  --verification-time-limit <DURATION>
  --performance-slack <DURATION>
  --slow-site-limit <DURATION> deprecated alias for --performance-slack
  --time-limit <DURATION>
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
    performance_slack: Duration,
    time_limit: Duration,
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
    /// Position in the user-edited container (`.click` or markdown).
    position: SourcePosition,
    /// Position in the extracted Click source used by verification APIs.
    click_position: SourcePosition,
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
        [command, path, claim] if command == "--internal-verify-rewritten" => {
            Some(verify_rewritten_from_stdin(Path::new(path), claim))
        }
        [command, path, claim] if command == "--internal-reexpand" => {
            Some(reexpand_from_stdin(Path::new(path), claim).map(|source| print!("{source}")))
        }
        _ => None,
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut path = None;
    let mut session_limit = DEFAULT_SESSION_LIMIT;
    let mut expansion_limit = DEFAULT_EXPANSION_LIMIT;
    let mut verification_limit = DEFAULT_VERIFICATION_LIMIT;
    let mut performance_slack = DEFAULT_PERFORMANCE_SLACK;
    let mut time_limit = DEFAULT_TIME_LIMIT;
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
            "--performance-slack" | "--slow-site-limit" => {
                performance_slack = parse_next_duration(&mut arguments, &argument)?;
            }
            "--time-limit" => {
                time_limit = parse_next_duration(&mut arguments, &argument)?;
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
        performance_slack,
        time_limit,
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
    let sources = audit_targets(&arguments.path)?;
    println!("INVENTORY");
    let sites = inventory_sites(&sources)?;
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
    let mut out_of_time = false;
    let mut cold_reverified_claims = std::collections::BTreeSet::new();
    let started = Instant::now();

    println!(
        "\nClick expansion audit (session {}, expansion {}, verification {}, \
         performance slack {}, run limit {})",
        format_duration(arguments.session_limit),
        format_duration(arguments.expansion_limit),
        format_duration(arguments.verification_limit),
        format_duration(arguments.performance_slack),
        format_duration(arguments.time_limit),
    );

    while cursor < selected.len() {
        if arguments
            .max_sites
            .is_some_and(|limit| attempted_sites == limit)
        {
            break;
        }
        if started.elapsed() >= arguments.time_limit {
            out_of_time = true;
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
        let cold_reverify =
            cold_reverified_claims.insert((site.click_path.clone(), site.claim.clone()));
        match audit_site(
            site,
            current,
            arguments.expansion_limit,
            arguments.verification_limit,
            arguments.performance_slack,
            cold_reverify,
        ) {
            Ok(timings) => {
                audited_sites += 1;
                println!(
                    "ok (expand {}, verify {}, original {}, reverify {}, reexpand {})",
                    format_duration(timings.expansion),
                    format_duration(timings.session_verification),
                    format_duration(timings.original_reverification),
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
    if out_of_time {
        if cursor < selected.len() {
            println!();
            print_resume(&arguments, &selected[cursor]);
        }
        return Err(format!(
            "audit stopped at its {} run limit after {} of {} selected sites{}",
            format_duration(arguments.time_limit),
            attempted_sites,
            selected.len(),
            if failures == 0 {
                String::new()
            } else {
                format!("; {failures} check(s) failed")
            }
        ));
    }
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

fn audit_targets(path: &Path) -> Result<Vec<PathBuf>, String> {
    if looks_like_mdtest(path) {
        return find_mdtests(path);
    }
    if path.is_file()
        && path
            .extension()
            .is_some_and(|extension| extension == "click")
    {
        return Ok(vec![fs::canonicalize(path).map_err(|error| {
            format!("failed to resolve `{}`: {error}", path.display())
        })?]);
    }
    let examples = path.join("examples");
    let mdtests = path.join("mdtests");
    if examples.is_dir() && mdtests.is_dir() {
        let mut sources = audit_targets(&examples)?;
        sources.extend(audit_targets(&mdtests)?);
        sources.sort();
        sources.dedup();
        return Ok(sources);
    }
    match find_projects(path) {
        Ok(projects) => {
            let mut sources = Vec::new();
            for project in projects {
                sources.extend(files_with_extension(&project, "click")?);
            }
            sources.sort();
            sources
                .into_iter()
                .map(|source| {
                    fs::canonicalize(&source).map_err(|error| {
                        format!("failed to resolve `{}`: {error}", source.display())
                    })
                })
                .collect()
        }
        Err(project_error) => {
            if path.is_dir() && !files_with_extension(path, "md")?.is_empty() {
                find_mdtests(path)
            } else {
                Err(project_error)
            }
        }
    }
}

struct AuditSource {
    container_source: String,
    click_source: String,
    c_sources: Vec<(String, String)>,
    line_offset: usize,
}

fn load_audit_source(path: &Path) -> Result<AuditSource, String> {
    let source = fs::read_to_string(path)
        .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
    load_audit_source_from_text(path, source)
}

fn load_audit_source_from_text(
    path: &Path,
    container_source: String,
) -> Result<AuditSource, String> {
    if looks_like_mdtest(path) {
        let mdtest = cli::parse_mdtest(path, &container_source)?;
        let click_source = mdtest
            .click_source
            .ok_or_else(|| format!("mdtest `{}` has no ```click block", path.display()))?;
        return Ok(AuditSource {
            container_source,
            click_source,
            c_sources: mdtest.c_sources,
            line_offset: mdtest.click_start_line.saturating_sub(1),
        });
    }
    let c_sources = read_verifying_sources(path, &container_source)?;
    Ok(AuditSource {
        click_source: container_source.clone(),
        container_source,
        c_sources,
        line_offset: 0,
    })
}

fn inventory_sites(sources: &[PathBuf]) -> Result<Vec<AuditSite>, String> {
    let mut sites = BTreeMap::new();
    for source_path in sources {
        let canonical_path = fs::canonicalize(source_path)
            .map_err(|error| format!("failed to resolve `{}`: {error}", source_path.display()))?;
        if looks_like_mdtest(&canonical_path) {
            let markdown = fs::read_to_string(&canonical_path).map_err(|error| {
                format!("failed to read `{}`: {error}", canonical_path.display())
            })?;
            let mdtest = cli::parse_mdtest(&canonical_path, &markdown)?;
            if matches!(mdtest.expectation, Some(MdTestExpectation::FailContains(_))) {
                continue;
            }
        }
        let source = load_audit_source(&canonical_path)?;
        let AuditSource {
            click_source,
            c_sources,
            line_offset,
            ..
        } = source;
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
            let container_position = SourcePosition {
                line: position.line + line_offset,
                column: position.column,
            };
            let key = (
                canonical_path.clone(),
                container_position.line,
                container_position.column,
            );
            sites.entry(key).or_insert(AuditSite {
                click_path: canonical_path.clone(),
                position: container_position,
                click_position: position,
                claim: syntactic.claim_label,
                tactic_name: syntactic.tactic_name,
            });
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
        "--performance-slack".to_string(),
        format_duration(arguments.performance_slack),
        "--time-limit".to_string(),
        format_duration(arguments.time_limit),
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
    original_reverification: Duration,
    reverification: Duration,
    reexpansion: Duration,
}

fn audit_site(
    site: &AuditSite,
    worker: &mut AuditSessionWorker,
    expansion_limit: Duration,
    verification_limit: Duration,
    performance_slack: Duration,
    cold_reverify: bool,
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
    let expanded_source = load_audit_source_from_text(&site.click_path, expanded.clone())
        .map_err(|error| format!("expanded proof container did not parse: {error}"))?;
    let expanded_position = claim_source_position(&expanded_source, &site.claim)?;

    // Expansion can insert or remove lines at the selected tactic.  Resolve
    // the proof unit again by claim instead of sending its now-stale source
    // coordinate to the retained verification session.
    let verification_elapsed = worker.verify(&expanded, expanded_position, verification_limit)?;

    // Checklist step 6: reverify the rewritten proof unit from normal
    // inputs by running the targeted entry point in a fresh process under
    // the verification time limit. The retained session already checked the
    // rewrite changed nothing outside the audited proof unit, so the other
    // units' outcomes cannot change; a whole-file pass here would redo them
    // all per site, which made auditing a project cost sites x whole-file
    // time. The cold-process pass exists to catch anything the retained
    // session's cached environment masks, which one site per claim already
    // exercises — repeating it for every site of a many-site claim would
    // double the whole audit for no additional coverage.
    let (original_reverification_elapsed, reverification_elapsed) = if cold_reverify {
        let original_elapsed = cold_verify(
            &executable,
            site,
            &original,
            verification_limit,
            "original proof-unit verification",
        )?;
        let expanded_elapsed = cold_verify(
            &executable,
            site,
            &expanded,
            verification_limit,
            "expanded proof-unit verification",
        )?;
        if verification_regressed(original_elapsed, expanded_elapsed, performance_slack) {
            // Timing-only findings get one fresh serial confirmation, matching
            // the ordinary tactic-budget gate's noise policy.
            let confirmed_original = cold_verify(
                &executable,
                site,
                &original,
                verification_limit,
                "confirmation original proof-unit verification",
            )?;
            let confirmed_expanded = cold_verify(
                &executable,
                site,
                &expanded,
                verification_limit,
                "confirmation expanded proof-unit verification",
            )?;
            if verification_regressed(confirmed_original, confirmed_expanded, performance_slack) {
                let artifact = audit_artifact_path(&site.click_path);
                return Err(format!(
                    "expanded proof-unit verification regressed in two serial comparisons: \
                     {} -> {}, then {} -> {} (failure requires over 2x and over {}); \
                     reproduce the exact expanded workload with:\n  \
                     cargo run --quiet --bin click-expand -- --time-limit {} {} > {}\n  \
                     cargo run --quiet --bin click-profile -- {}",
                    format_duration(original_elapsed),
                    format_duration(expanded_elapsed),
                    format_duration(confirmed_original),
                    format_duration(confirmed_expanded),
                    format_duration(performance_slack),
                    format_duration(expansion_limit),
                    location,
                    artifact.display(),
                    artifact.display(),
                ));
            }
        }
        (original_elapsed, expanded_elapsed)
    } else {
        (Duration::ZERO, Duration::ZERO)
    };

    // Checklist step 7: re-expanding the same claim against the rewritten
    // source must be a fixed point, byte for byte. The site is re-resolved
    // by claim because the rewrite moves and replaces tactics.
    let mut reexpansion = Command::new(&executable);
    reexpansion
        .arg("--internal-reexpand")
        .arg(&site.click_path)
        .arg(&site.claim);
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

    // Proof scripts have no runtime semantics: re-verifying the same isolated
    // claim is the semantic invariant. Requiring the prover to visit identical
    // internal branch/path states would reject valid explicit certificates and
    // is intentionally not an audit invariant.

    Ok(SiteTimings {
        expansion: expansion.elapsed,
        session_verification: verification_elapsed,
        original_reverification: original_reverification_elapsed,
        reverification: reverification_elapsed,
        reexpansion: reexpansion.elapsed,
    })
}

fn cold_verify(
    executable: &Path,
    site: &AuditSite,
    source: &str,
    verification_limit: Duration,
    label: &str,
) -> Result<Duration, String> {
    let mut verification = Command::new(executable);
    verification
        .arg("--internal-verify-rewritten")
        .arg(&site.click_path)
        .arg(&site.claim);
    let output = require_success(
        run_bounded_with_input(
            verification,
            Some(source.as_bytes().to_vec()),
            verification_limit,
            label,
        )?,
        verification_limit,
        label,
    )?;
    Ok(output.elapsed)
}

fn verification_regressed(
    original: Duration,
    expanded: Duration,
    performance_slack: Duration,
) -> bool {
    expanded > original.saturating_mul(2) && expanded > original + performance_slack
}

fn audit_artifact_path(source: &Path) -> PathBuf {
    let stem = source
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("expanded");
    let extension = source
        .extension()
        .and_then(|extension| extension.to_str())
        .unwrap_or("click");
    source.with_file_name(format!("{stem}.audit-expanded.{extension}"))
}

fn expand_location(location: &str) -> Result<String, String> {
    let (click_path, line, column) = cli::parse_source_location(location)?;
    let source = load_audit_source(&click_path)?;
    let click_line = line
        .checked_sub(source.line_offset)
        .ok_or_else(|| format!("line {line} is before the mdtest's ```click block"))?;
    if click_line == 0 || click_line > source.click_source.lines().count() {
        return Err(format!(
            "line {line} is outside the proof container's Click source"
        ));
    }
    let refs = source_refs(&source.c_sources);
    let expanded_click =
        expand_c0_tactic_source_at(&source.click_source, &refs, click_line, column)
            .map_err(|error| error.message().to_string())?;
    if looks_like_mdtest(&click_path) {
        Ok(splice_click_source(&source, &expanded_click))
    } else {
        Ok(expanded_click)
    }
}

fn splice_click_source(source: &AuditSource, expanded_click: &str) -> String {
    let lines = source.container_source.lines().collect::<Vec<_>>();
    let body_start = source.line_offset;
    let body_len = source.click_source.lines().count();
    let mut spliced = Vec::with_capacity(lines.len());
    spliced.extend_from_slice(&lines[..body_start]);
    spliced.extend(expanded_click.lines());
    spliced.extend_from_slice(&lines[body_start + body_len..]);
    let mut result = spliced.join("\n");
    if source.container_source.ends_with('\n') {
        result.push('\n');
    }
    result
}

fn read_stdin_source(label: &str) -> Result<String, String> {
    let mut source = String::new();
    std::io::stdin()
        .read_to_string(&mut source)
        .map_err(|error| format!("failed to read {label} from stdin: {error}"))?;
    Ok(source)
}

/// Checklist step 6 worker: verifies the audited proof unit of a rewritten
/// sidecar, read from stdin, through the normal targeted entry point,
/// resolving its C sources relative to the original on-disk sidecar path.
/// The unit is re-located by claim (its first tactic source) because the
/// rewrite moves source positions.
fn verify_rewritten_from_stdin(
    original_click_path: &Path,
    claim_label: &str,
) -> Result<(), String> {
    let rewritten = read_stdin_source("rewritten sidecar")?;
    let source = load_audit_source_from_text(original_click_path, rewritten)?;
    let refs = source_refs(&source.c_sources);
    let position = claim_source_position(&source, claim_label)?;
    verify_c0_sources_at(&source.click_source, &refs, position.line, position.column)
        .map(|_| ())
        .map_err(|error| error.message().to_string())
}

fn claim_source_position(
    source: &AuditSource,
    claim_label: &str,
) -> Result<SourcePosition, String> {
    let refs = source_refs(&source.c_sources);
    c0_tactic_source_position(&source.click_source, &refs, claim_label, 0).map_err(|error| {
        format!(
            "could not locate `{claim_label}` in the rewritten sidecar: {}",
            error.message()
        )
    })
}

/// Checklist step 7 worker: checks the rewritten sidecar (read from stdin)
/// is an expansion fixed point for the audited site, resolving C sources
/// relative to the original on-disk sidecar path.
///
/// The rewrite moves and replaces tactics, so the audited site cannot be
/// re-located by its original position. The fixed-point property that is
/// actually checkable per site: the audited smart tactic must be gone from
/// the claim's smart inventory, and the emitted expansion must not have
/// introduced any new smart tactic (certificates are explicit tactics), so
/// the claim's smart-site multiset strictly shrinks. A path-aligned
/// certificate can replace more than one symmetric occurrence at once, so an
/// exact one-site decrease would reject a stronger valid expansion. Other
/// smart sites of the claim are audited on their own turns against the
/// original sidecar.
/// On success the rewritten source is echoed so the caller's byte-identical
/// comparison passes.
fn reexpand_from_stdin(click_path: &Path, claim_label: &str) -> Result<String, String> {
    let original = load_audit_source(click_path)?;
    let rewritten = read_stdin_source("rewritten sidecar")?;
    let rewritten_source = load_audit_source_from_text(click_path, rewritten.clone())?;
    let claim_sites = |source: &str, sources: &[(String, String)]| {
        let refs = sources
            .iter()
            .map(|(name, source)| (name.as_str(), source.as_str()))
            .collect::<Vec<_>>();
        c0_smart_tactic_source_sites(source, &refs)
            .map(|sites| {
                sites
                    .into_iter()
                    .filter(|site| site.claim_label == claim_label)
                    .map(|site| site.tactic_name)
                    .collect::<Vec<_>>()
            })
            .map_err(|error| {
                format!(
                    "could not inventory smart tactics for `{claim_label}`: {}",
                    error.message()
                )
            })
    };
    let original_sites = claim_sites(&original.click_source, &original.c_sources)?;
    let rewritten_sites = claim_sites(&rewritten_source.click_source, &rewritten_source.c_sources)?;
    let mut unmatched_original = original_sites.clone();
    let introduced = rewritten_sites.iter().find(|rewritten| {
        let Some(index) = unmatched_original
            .iter()
            .position(|original| original == *rewritten)
        else {
            return true;
        };
        unmatched_original.remove(index);
        false
    });
    if let Some(introduced) = introduced {
        return Err(format!(
            "expansion introduced smart tactic `{introduced}` in `{claim_label}`: \
             {} smart site(s) before ({}), {} after ({})",
            original_sites.len(),
            original_sites.join(", "),
            rewritten_sites.len(),
            rewritten_sites.join(", "),
        ));
    }
    if unmatched_original.is_empty() {
        return Err(format!(
            "expansion did not remove a smart tactic from `{claim_label}`: {} site(s) before and {} after",
            original_sites.len(),
            rewritten_sites.len(),
        ));
    }
    Ok(rewritten)
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
    let source = load_audit_source(click_path)?;
    let refs = source_refs(&source.c_sources);
    let session = match C0VerificationSession::new(&source.click_source, &refs) {
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
        let rewritten = load_audit_source_from_text(click_path, rewritten)?;
        let result = session
            .verify_at(&rewritten.click_source, position.line, position.column)
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
    use click::lang::click::verify_c0_sources;

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
            performance_slack: Duration::from_millis(500),
            time_limit: Duration::from_secs(600),
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
             --verification-time-limit 3s --performance-slack 500ms --time-limit 10m \
             --max-sites 1 --start-at /tmp/example.click:12:34 'examples with spaces'"
        );
    }

    #[test]
    fn performance_comparison_requires_ratio_and_absolute_slack() {
        let slack = Duration::from_millis(500);
        assert!(!verification_regressed(
            Duration::from_secs(5),
            Duration::from_secs(9),
            slack,
        ));
        assert!(!verification_regressed(
            Duration::from_millis(100),
            Duration::from_millis(250),
            slack,
        ));
        assert!(verification_regressed(
            Duration::from_secs(1),
            Duration::from_millis(2_501),
            slack,
        ));
    }

    #[test]
    fn start_cursor_is_an_inclusive_global_lower_bound() {
        let site = |path: &str, line| AuditSite {
            click_path: PathBuf::from(path),
            position: SourcePosition { line, column: 3 },
            click_position: SourcePosition { line, column: 3 },
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
    execute();
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
                ("example.contract", 0, "execute"),
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
        click::lang::click::verifying_source_paths(&expanded).unwrap();
        verify_c0_sources(&expanded, &sources).unwrap();
    }

    #[test]
    fn rewritten_claim_position_survives_an_expansion_that_removes_a_tactic() {
        let c_source = "int32 example() { return 0; }";
        let click_source = r#"verifying "example.c";
int32 example() {
    ensures result == 0;
} by {
    execute();
    simp();
}
"#;
        let sources = [("example.c", c_source)];
        let position =
            c0_tactic_source_position(click_source, &sources, "example.contract", 1).unwrap();
        let expanded =
            expand_c0_tactic_source_at(click_source, &sources, position.line, position.column)
                .expect("redundant trailing simp should expand away");
        assert!(!expanded.contains("simp();"));

        let source = AuditSource {
            container_source: expanded.clone(),
            click_source: expanded,
            c_sources: vec![("example.c".to_string(), c_source.to_string())],
            line_offset: 0,
        };
        let relocated = claim_source_position(&source, "example.contract")
            .expect("the rewritten claim should have a fresh selector");
        verify_c0_sources_at(
            &source.click_source,
            &[("example.c", c_source)],
            relocated.line,
            relocated.column,
        )
        .expect("the relocated rewritten proof should verify");
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
    fn repository_root_targets_examples_and_passing_mdtests() {
        let root = PathBuf::from(env!("CARGO_MANIFEST_DIR"));
        let targets = audit_targets(&root).expect("repository audit targets should resolve");
        assert!(
            targets.iter().any(|path| {
                path.extension()
                    .is_some_and(|extension| extension == "click")
            }),
            "example sidecars must be included"
        );
        assert!(
            targets
                .iter()
                .any(|path| path.ends_with("mdtests/scalar.md")),
            "passing mdtests must be included"
        );
    }

    #[test]
    fn markdown_inventory_and_expansion_use_container_coordinates() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR")).join("mdtests/scalar.md");
        let sites = inventory_sites(std::slice::from_ref(&path))
            .expect("the scalar mdtest should inventory");
        let site = sites.first().expect("the scalar mdtest has one smart site");
        assert!(site.position.line > site.click_position.line);
        let location = format_location(&site_location(site));
        let expanded = expand_location(&location).expect("the markdown smart site should expand");
        let source = load_audit_source_from_text(&path, expanded)
            .expect("expanded markdown should re-extract");
        let refs = source_refs(&source.c_sources);
        verify_c0_sources(&source.click_source, &refs)
            .expect("expanded markdown proof should verify");
    }

    #[test]
    fn truncates_large_child_diagnostics_at_character_boundaries() {
        let diagnostic = "λ".repeat(MAX_DIAGNOSTIC_CHARS + 2);
        let truncated = truncate_diagnostic(&diagnostic);
        assert!(truncated.starts_with(&"λ".repeat(MAX_DIAGNOSTIC_CHARS)));
        assert!(truncated.ends_with("2 more characters)"));
    }
}
