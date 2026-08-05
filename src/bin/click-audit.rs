use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::{Duration, Instant};

use click::cli::{
    self, MdTestExpectation, files_with_extension, find_mdtests, find_projects, format_duration,
    looks_like_mdtest, parse_duration, read_verifying_sources, shell_quote, source_refs,
};
use click::lang::click::{
    C0VerificationSession, SourcePosition, c0_incremental_selection, c0_smart_tactic_source_sites,
    c0_tactic_source_position, expand_c0_tactic_source_at, verify_c0_sources_at,
    verifying_source_paths,
};

const DEFAULT_SESSION_LIMIT: Duration = Duration::from_secs(5 * 60);
const DEFAULT_EXPANSION_LIMIT: Duration = Duration::from_secs(2 * 60);
const DEFAULT_VERIFICATION_LIMIT: Duration = Duration::from_secs(5 * 60);
const DEFAULT_PERFORMANCE_SLACK: Duration = Duration::from_millis(500);
const DEFAULT_TIME_LIMIT: Duration = Duration::from_secs(10 * 60);
const RUN_LIMIT_EXHAUSTED: &str = "whole-run time limit exhausted";
const USAGE: &str = "\
usage: click audit [OPTIONS] <sidecar.click|example-project|examples-directory|mdtest.md|mdtests-directory|repository-root>

The audit inventories smart tactics without executing proofs, then audits each
selected site in source order: it expands the site, verifies the rewritten
proof unit in the retained session, reverifies that proof unit through the
normal direct targeted entry point, and checks the rewrite is an
expansion fixed point (the audited smart tactic is gone from its claim and
the emitted expansion introduced no new smart tactic). By default it stops at
the first failure and prints an inclusive --start-at resume command.
Successful progress is concise by default: one row per claim. `--verbose`
restores one row per smart site.

Raw phase time grows with proof-unit size and is reported but is not itself a
failure. On the first site of each claim, audit compares cold verification of
the expanded proof with the original proof in the same run. A regression must
be both over 2x and over the performance slack, then repeat once, to fail.
Hard phase and whole-run limits remain safety failures.

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
  --claim <CLAIM>             audit one named claim; may be repeated
  --changed-since <REVISION>  audit claims affected since a Git revision
  --verbose                   print one successful row per smart site
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
    claims: Vec<String>,
    changed_since: Option<String>,
    verbose: bool,
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

struct ConciseClaimProgress {
    key: (PathBuf, String),
    passed: usize,
    total: usize,
}

struct AuditSessionWorker {
    click_path: PathBuf,
    session: C0VerificationSession,
}

impl AuditSessionWorker {
    fn start(click_path: &Path, limit: Duration) -> Result<Self, String> {
        let started = Instant::now();
        let source = load_audit_source(click_path)?;
        let refs = source_refs(&source.c_sources);
        let (session, _) = click::instrumentation::with_deadline(limit, || {
            C0VerificationSession::new(&source.click_source, &refs)
        })
        .map_err(|error| error.message().to_string())?;
        ensure_phase_limit(
            started.elapsed(),
            limit,
            "verification-session initialization",
        )?;
        Ok(Self {
            click_path: click_path.to_path_buf(),
            session,
        })
    }

    fn verify(
        &mut self,
        click_source: &str,
        position: SourcePosition,
        limit: Duration,
    ) -> Result<Duration, String> {
        let start = Instant::now();
        let rewritten = load_audit_source_from_text(&self.click_path, click_source.to_string())?;
        click::instrumentation::with_deadline(limit, || {
            self.session
                .verify_at(&rewritten.click_source, position.line, position.column)
        })
        .map_err(|error| error.message().to_string())?;
        let elapsed = start.elapsed();
        ensure_phase_limit(elapsed, limit, "rewritten-sidecar verification")?;
        Ok(elapsed)
    }

    fn is_alive(&self) -> bool {
        true
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
    run_audit(parse_arguments(raw)?)
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut path = None;
    let mut session_limit = DEFAULT_SESSION_LIMIT;
    let mut expansion_limit = DEFAULT_EXPANSION_LIMIT;
    let mut verification_limit = DEFAULT_VERIFICATION_LIMIT;
    let mut performance_slack = DEFAULT_PERFORMANCE_SLACK;
    let mut time_limit = DEFAULT_TIME_LIMIT;
    let mut start_at = None;
    let mut claims = Vec::new();
    let mut changed_since = None;
    let mut verbose = false;
    let mut keep_going = false;
    let mut max_sites = None;
    let mut parse_options = true;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
        if parse_options && argument == "--" {
            parse_options = false;
            continue;
        }
        if !parse_options {
            if path.replace(PathBuf::from(argument)).is_some() {
                return Err(USAGE.to_string());
            }
            continue;
        }
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
            "--claim" => {
                let claim = arguments
                    .next()
                    .ok_or_else(|| format!("missing claim after `{argument}`\n{USAGE}"))?;
                if claims.contains(&claim) {
                    return Err(format!("claim `{claim}` was selected more than once"));
                }
                claims.push(claim);
            }
            "--changed-since" => {
                if changed_since.is_some() {
                    return Err("`--changed-since` may only be supplied once".to_string());
                }
                changed_since = Some(
                    arguments
                        .next()
                        .ok_or_else(|| format!("missing revision after `{argument}`\n{USAGE}"))?,
                );
            }
            "--verbose" => verbose = true,
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
        claims,
        changed_since,
        verbose,
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
    let inventory_claims = sites
        .iter()
        .map(|site| (site.click_path.clone(), site.claim.clone()))
        .collect::<BTreeSet<_>>()
        .len();
    println!(
        "  {} unique smart source sites in {inventory_claims} claims",
        sites.len()
    );
    let claim_sites = select_claim_sites(&sites, &arguments.claims)?;
    if !arguments.claims.is_empty() {
        println!(
            "  selected {} sites in {} named claims",
            claim_sites.len(),
            arguments.claims.len()
        );
    }
    let scoped_sites = if let Some(revision) = &arguments.changed_since {
        let selected = select_changed_sites(&sources, &claim_sites, revision)?;
        let selected_claims = selected
            .iter()
            .map(|site| (site.click_path.clone(), site.claim.clone()))
            .collect::<BTreeSet<_>>()
            .len();
        println!(
            "  selected {} sites in {selected_claims} affected claims since {revision}",
            selected.len()
        );
        selected
    } else {
        claim_sites
    };

    let start_at = arguments
        .start_at
        .as_ref()
        .map(canonicalize_location)
        .transpose()?;
    if let Some(start_at) = &start_at
        && !scoped_sites
            .iter()
            .any(|site| site.click_path == start_at.path)
    {
        return Err(format!(
            "`--start-at` path `{}` has no smart tactic sites in `{}`",
            start_at.path.display(),
            arguments.path.display()
        ));
    }
    let first = first_site_at_or_after(&scoped_sites, start_at.as_ref());
    if start_at.is_some() && first == scoped_sites.len() {
        return Err("`--start-at` is after the final smart tactic site".to_string());
    }

    let selected = &scoped_sites[first..];
    let mut selected_claim_counts = BTreeMap::new();
    let mut selected_claim_order = BTreeMap::new();
    for site in selected {
        let key = (site.click_path.clone(), site.claim.clone());
        let next = selected_claim_order.len() + 1;
        selected_claim_order.entry(key.clone()).or_insert(next);
        *selected_claim_counts.entry(key).or_default() += 1;
    }
    let mut audited_sites = 0;
    let mut site_failures = 0;
    let mut session_failures = 0;
    let mut attempted_sites = 0;
    let mut worker: Option<(PathBuf, AuditSessionWorker)> = None;
    let mut cursor = 0;
    let mut out_of_time = false;
    let mut cold_reverified_claims = std::collections::BTreeSet::new();
    let mut concise_progress: Option<ConciseClaimProgress> = None;
    let started = Instant::now();
    let deadline = started + arguments.time_limit;

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
        if Instant::now() >= deadline {
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
            let session_limit = match remaining_phase_limit(deadline, arguments.session_limit) {
                Ok(limit) => limit,
                Err(_) => {
                    println!("STOPPED ({RUN_LIMIT_EXHAUSTED})");
                    out_of_time = true;
                    break;
                }
            };
            match AuditSessionWorker::start(&site.click_path, session_limit) {
                Ok(new_worker) => {
                    println!("ready");
                    worker = Some((site.click_path.clone(), new_worker));
                }
                Err(message) => {
                    if Instant::now() >= deadline {
                        println!("STOPPED");
                        println!("    {RUN_LIMIT_EXHAUSTED}");
                        out_of_time = true;
                        break;
                    }
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
        if arguments.verbose {
            print!(
                "[{}/{}] {label}  {} ({}) ... ",
                first + cursor + 1,
                scoped_sites.len(),
                site.claim,
                site.tactic_name,
            );
        } else if concise_progress.is_none() {
            let key = (site.click_path.clone(), site.claim.clone());
            print!(
                "CLAIM [{}/{}] {}  {} ({} sites) ... ",
                selected_claim_order[&key],
                selected_claim_order.len(),
                site.click_path.display(),
                site.claim,
                selected_claim_counts[&key],
            );
            concise_progress = Some(ConciseClaimProgress {
                key,
                passed: 0,
                total: selected_claim_counts[&(site.click_path.clone(), site.claim.clone())],
            });
        }
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
            deadline,
        ) {
            Ok(timings) => {
                audited_sites += 1;
                if arguments.verbose {
                    println!("{}", render_site_timings(&timings));
                } else if let Some(progress) = concise_progress.as_mut() {
                    progress.passed += 1;
                    let next_is_same_claim = selected.get(cursor + 1).is_some_and(|next| {
                        progress.key == (next.click_path.clone(), next.claim.clone())
                    });
                    let capped_mid_claim = arguments
                        .max_sites
                        .is_some_and(|limit| attempted_sites == limit)
                        && next_is_same_claim;
                    if !next_is_same_claim {
                        println!("ok ({} sites)", progress.passed);
                        concise_progress = None;
                    } else if capped_mid_claim {
                        println!(
                            "partial ({}/{} sites passed)",
                            progress.passed, progress.total
                        );
                        concise_progress = None;
                    }
                }
                cursor += 1;
            }
            Err(message) => {
                if Instant::now() >= deadline || message == RUN_LIMIT_EXHAUSTED {
                    println!("STOPPED");
                    println!("    {RUN_LIMIT_EXHAUSTED}");
                    out_of_time = true;
                    break;
                }
                if arguments.verbose {
                    println!("FAIL");
                } else {
                    println!("FAIL at {label} ({})", site.tactic_name);
                    concise_progress = None;
                }
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

    if let Some(progress) = concise_progress.take() {
        println!(
            "partial ({}/{} sites passed)",
            progress.passed, progress.total
        );
    }

    println!(
        "\nSUMMARY: {audited_sites} sites passed; {site_failures} site failures; \
         {session_failures} session failures; {} sites discovered{}",
        scoped_sites.len(),
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
    if path
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
    mdtest: Option<cli::MdTest>,
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
            .clone()
            .ok_or_else(|| format!("mdtest `{}` has no ```click block", path.display()))?;
        return Ok(AuditSource {
            container_source,
            click_source,
            c_sources: mdtest.c_sources.clone(),
            line_offset: mdtest.click_start_line.saturating_sub(1),
            mdtest: Some(mdtest),
        });
    }
    let c_sources = read_verifying_sources(path, &container_source)?;
    Ok(AuditSource {
        click_source: container_source.clone(),
        container_source,
        c_sources,
        line_offset: 0,
        mdtest: None,
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

fn select_claim_sites(sites: &[AuditSite], claims: &[String]) -> Result<Vec<AuditSite>, String> {
    if claims.is_empty() {
        return Ok(sites.to_vec());
    }
    for claim in claims {
        let paths = sites
            .iter()
            .filter(|site| site.claim == *claim)
            .map(|site| site.click_path.clone())
            .collect::<BTreeSet<_>>();
        if paths.is_empty() {
            let known = sites
                .iter()
                .map(|site| site.claim.as_str())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .take(12)
                .collect::<Vec<_>>()
                .join(", ");
            return Err(format!(
                "unknown audit claim `{claim}`{}",
                if known.is_empty() {
                    String::new()
                } else {
                    format!("; known claims include: {known}")
                }
            ));
        }
        if paths.len() > 1 {
            return Err(format!(
                "audit claim `{claim}` is ambiguous across: {}; name one sidecar as the audit target",
                paths
                    .iter()
                    .map(|path| path.display().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
    }
    let requested = claims.iter().collect::<BTreeSet<_>>();
    Ok(sites
        .iter()
        .filter(|site| requested.contains(&site.claim))
        .cloned()
        .collect())
}

fn select_changed_sites(
    sources: &[PathBuf],
    sites: &[AuditSite],
    revision: &str,
) -> Result<Vec<AuditSite>, String> {
    if sources.is_empty() {
        return Ok(Vec::new());
    }
    let repo = git_repo_root(&sources[0])?;
    git_commit_id(&repo, revision)?;
    let changed_paths = git_changed_paths(&repo, revision)?;
    if changed_paths_require_full_audit(&repo, &changed_paths) {
        println!("  full audit: Click verifier or audit implementation changed");
        return Ok(sites.to_vec());
    }

    let mut selected = Vec::new();
    for source_path in sources {
        let source_sites = sites
            .iter()
            .filter(|site| site.click_path == *source_path)
            .cloned()
            .collect::<Vec<_>>();
        if source_sites.is_empty() {
            continue;
        }
        let current = load_audit_source(source_path)?;
        let Some(baseline) = load_baseline_audit_source(&repo, revision, source_path)? else {
            println!(
                "  full sidecar: `{}` is absent or incomplete at {revision}",
                source_path.display()
            );
            selected.extend(source_sites);
            continue;
        };
        let current_refs = source_refs(&current.c_sources);
        let baseline_refs = source_refs(&baseline.c_sources);
        let selection = match c0_incremental_selection(
            &current.click_source,
            &current_refs,
            &baseline.click_source,
            &baseline_refs,
        ) {
            Ok(selection) => selection,
            Err(error) => {
                println!(
                    "  full sidecar: `{}` could not be compared semantically: {}",
                    source_path.display(),
                    error.message()
                );
                selected.extend(source_sites);
                continue;
            }
        };
        if selection.full_rebuild {
            selected.extend(source_sites);
            continue;
        }
        let functions = selection
            .selected_functions
            .iter()
            .map(String::as_str)
            .collect::<BTreeSet<_>>();
        selected.extend(select_function_sites(&source_sites, &functions));
    }
    Ok(selected)
}

fn select_function_sites(sites: &[AuditSite], functions: &BTreeSet<&str>) -> Vec<AuditSite> {
    sites
        .iter()
        .filter(|site| {
            site.claim
                .split_once('.')
                .is_none_or(|(owner, _)| functions.contains(owner))
        })
        .cloned()
        .collect()
}

fn git_repo_root(path: &Path) -> Result<PathBuf, String> {
    let anchor = if path.is_dir() {
        path
    } else {
        path.parent().unwrap_or_else(|| Path::new("."))
    };
    let output = Command::new("git")
        .args([
            "-C",
            &anchor.display().to_string(),
            "rev-parse",
            "--show-toplevel",
        ])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if !output.status.success() {
        return Err(format!(
            "`{}` is not inside a readable git worktree",
            path.display()
        ));
    }
    Ok(PathBuf::from(
        String::from_utf8_lossy(&output.stdout).trim(),
    ))
}

fn git_commit_id(repo: &Path, revision: &str) -> Result<String, String> {
    let output = Command::new("git")
        .args([
            "-C",
            &repo.display().to_string(),
            "rev-parse",
            "--verify",
            &format!("{revision}^{{commit}}"),
        ])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if output.status.success() {
        Ok(String::from_utf8_lossy(&output.stdout).trim().to_string())
    } else {
        Err(format!("unknown git revision `{revision}`"))
    }
}

fn git_changed_paths(repo: &Path, revision: &str) -> Result<Vec<PathBuf>, String> {
    let output = Command::new("git")
        .args([
            "-C",
            &repo.display().to_string(),
            "diff",
            "--name-only",
            revision,
            "--",
        ])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if !output.status.success() {
        return Err(format!("git diff failed for revision `{revision}`"));
    }
    Ok(String::from_utf8_lossy(&output.stdout)
        .lines()
        .filter(|line| !line.is_empty())
        .map(PathBuf::from)
        .collect())
}

fn changed_paths_require_full_audit(repo: &Path, changed_paths: &[PathBuf]) -> bool {
    let click_engine_checkout = repo.join("src/lang/click.rs").is_file()
        && repo.join("src/kernel").is_dir()
        && fs::read_to_string(repo.join("Cargo.toml"))
            .is_ok_and(|manifest| manifest.contains("name = \"click\""));
    click_engine_checkout
        && changed_paths.iter().any(|path| {
            path.starts_with("src")
                || path == Path::new("Cargo.toml")
                || path == Path::new("Cargo.lock")
                || path.starts_with("stdlib")
        })
}

fn git_show(repo: &Path, revision: &str, path: &Path) -> Result<Option<String>, String> {
    let relative = path.strip_prefix(repo).map_err(|_| {
        format!(
            "`{}` is outside git worktree `{}`",
            path.display(),
            repo.display()
        )
    })?;
    let spec = format!("{revision}:{}", relative.display());
    let output = Command::new("git")
        .args(["-C", &repo.display().to_string(), "show", &spec])
        .output()
        .map_err(|error| format!("failed to run git: {error}"))?;
    if output.status.success() {
        Ok(Some(String::from_utf8_lossy(&output.stdout).into_owned()))
    } else {
        Ok(None)
    }
}

fn load_baseline_audit_source(
    repo: &Path,
    revision: &str,
    path: &Path,
) -> Result<Option<AuditSource>, String> {
    let Some(container_source) = git_show(repo, revision, path)? else {
        return Ok(None);
    };
    if looks_like_mdtest(path) {
        return load_audit_source_from_text(path, container_source).map(Some);
    }
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    let mut c_sources = Vec::new();
    for name in verifying_source_paths(&container_source).map_err(|error| {
        format!(
            "could not read baseline sidecar `{}`: {}",
            path.display(),
            error.message()
        )
    })? {
        let source_path = parent.join(&name);
        let Some(source) = git_show(repo, revision, &source_path)? else {
            return Ok(None);
        };
        c_sources.push((name, source));
    }
    Ok(Some(AuditSource {
        click_source: container_source.clone(),
        container_source,
        c_sources,
        line_offset: 0,
        mdtest: None,
    }))
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
        "click".to_string(),
        "audit".to_string(),
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
    if arguments.verbose {
        words.push("--verbose".to_string());
    }
    for claim in &arguments.claims {
        words.push("--claim".to_string());
        words.push(claim.clone());
    }
    if let Some(revision) = &arguments.changed_since {
        words.push("--changed-since".to_string());
        words.push(revision.clone());
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

/// Timings for the checks performed on one audited site.
struct SiteTimings {
    expansion: Duration,
    session_verification: Duration,
    cold_verification: Option<(Duration, Duration)>,
    reexpansion: Duration,
}

fn render_site_timings(timings: &SiteTimings) -> String {
    if let Some((original, rewritten)) = timings.cold_verification {
        format!(
            "ok (expand {}, verify {}, cold original {}, cold rewritten {}, reexpand {})",
            format_duration(timings.expansion),
            format_duration(timings.session_verification),
            format_duration(original),
            format_duration(rewritten),
            format_duration(timings.reexpansion),
        )
    } else {
        format!(
            "ok (expand {}, verify {}, cold comparison not run, reexpand {})",
            format_duration(timings.expansion),
            format_duration(timings.session_verification),
            format_duration(timings.reexpansion),
        )
    }
}

fn remaining_phase_limit(deadline: Instant, configured: Duration) -> Result<Duration, String> {
    let remaining = deadline
        .checked_duration_since(Instant::now())
        .filter(|remaining| !remaining.is_zero())
        .ok_or_else(|| RUN_LIMIT_EXHAUSTED.to_string())?;
    Ok(configured.min(remaining))
}

fn ensure_phase_limit(elapsed: Duration, limit: Duration, label: &str) -> Result<(), String> {
    if elapsed > limit {
        Err(format!(
            "{label} exceeded {} after {}",
            format_duration(limit),
            format_duration(elapsed)
        ))
    } else {
        Ok(())
    }
}

fn audit_site(
    site: &AuditSite,
    worker: &mut AuditSessionWorker,
    expansion_limit: Duration,
    verification_limit: Duration,
    performance_slack: Duration,
    cold_reverify: bool,
    deadline: Instant,
) -> Result<SiteTimings, String> {
    let location = format!(
        "{}:{}:{}",
        site.click_path.display(),
        site.position.line,
        site.position.column
    );
    let phase_limit = remaining_phase_limit(deadline, expansion_limit)?;
    let expansion_started = Instant::now();
    let expanded =
        click::instrumentation::with_deadline(phase_limit, || expand_location(&location))?;
    let expansion_elapsed = expansion_started.elapsed();
    ensure_phase_limit(expansion_elapsed, phase_limit, "expansion")?;
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
    let verification_elapsed = worker.verify(
        &expanded,
        expanded_position,
        remaining_phase_limit(deadline, verification_limit)?,
    )?;

    // Checklist step 6: reverify the rewritten proof unit from normal
    // inputs by running the direct targeted entry point under
    // the verification time limit. The retained session already checked the
    // rewrite changed nothing outside the audited proof unit, so the other
    // units' outcomes cannot change; a whole-file pass here would redo them
    // all per site, which made auditing a project cost sites x whole-file
    // time. The cold direct pass catches anything the retained session's
    // cached environment masks, which one site per claim already
    // exercises — repeating it for every site of a many-site claim would
    // double the whole audit for no additional coverage.
    let cold_verification = if cold_reverify {
        let original_elapsed = cold_verify(
            site,
            &original,
            remaining_phase_limit(deadline, verification_limit)?,
            "original proof-unit verification",
        )?;
        let expanded_elapsed = cold_verify(
            site,
            &expanded,
            remaining_phase_limit(deadline, verification_limit)?,
            "expanded proof-unit verification",
        )?;
        if verification_regressed(original_elapsed, expanded_elapsed, performance_slack) {
            // Timing-only findings get one fresh serial confirmation, matching
            // the ordinary tactic-budget gate's noise policy.
            let confirmed_original = cold_verify(
                site,
                &original,
                remaining_phase_limit(deadline, verification_limit)?,
                "confirmation original proof-unit verification",
            )?;
            let confirmed_expanded = cold_verify(
                site,
                &expanded,
                remaining_phase_limit(deadline, verification_limit)?,
                "confirmation expanded proof-unit verification",
            )?;
            if verification_regressed(confirmed_original, confirmed_expanded, performance_slack) {
                let artifact = audit_artifact_path(&site.click_path);
                return Err(format!(
                    "expanded proof-unit verification regressed in two serial comparisons: \
                     {} -> {}, then {} -> {} (failure requires over 2x and over {}); \
                     reproduce the exact expanded workload with:\n  \
                     click expand --time-limit {} --output {} {}\n  \
                     click profile {}",
                    format_duration(original_elapsed),
                    format_duration(expanded_elapsed),
                    format_duration(confirmed_original),
                    format_duration(confirmed_expanded),
                    format_duration(performance_slack),
                    format_duration(expansion_limit),
                    shell_quote(&artifact.display().to_string()),
                    shell_quote(&location),
                    shell_quote(&artifact.display().to_string()),
                ));
            }
        }
        Some((original_elapsed, expanded_elapsed))
    } else {
        None
    };

    // Checklist step 7: re-expanding the same claim against the rewritten
    // source must be a fixed point, byte for byte. The site is re-resolved
    // by claim because the rewrite moves and replaces tactics.
    let phase_limit = remaining_phase_limit(deadline, expansion_limit)?;
    let reexpansion_started = Instant::now();
    let reexpanded = reexpand_source(&site.click_path, &site.claim, &expanded)?;
    let reexpansion_elapsed = reexpansion_started.elapsed();
    ensure_phase_limit(reexpansion_elapsed, phase_limit, "re-expansion")?;
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
        expansion: expansion_elapsed,
        session_verification: verification_elapsed,
        cold_verification,
        reexpansion: reexpansion_elapsed,
    })
}

fn cold_verify(
    site: &AuditSite,
    source: &str,
    verification_limit: Duration,
    label: &str,
) -> Result<Duration, String> {
    let started = Instant::now();
    click::instrumentation::with_deadline(verification_limit, || {
        verify_rewritten(&site.click_path, &site.claim, source)
    })?;
    let elapsed = started.elapsed();
    ensure_phase_limit(elapsed, verification_limit, label)?;
    Ok(elapsed)
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
    let click_line = if let Some(mdtest) = &source.mdtest {
        mdtest.click_line(line)?
    } else if line > 0 && line <= source.click_source.lines().count() {
        line
    } else {
        return Err(format!(
            "line {line} is outside the proof container's Click source"
        ));
    };
    let refs = source_refs(&source.c_sources);
    let expanded_click =
        expand_c0_tactic_source_at(&source.click_source, &refs, click_line, column)
            .map_err(|error| error.message().to_string())?;
    if looks_like_mdtest(&click_path) {
        source
            .mdtest
            .as_ref()
            .expect("markdown audit sources retain their parsed container")
            .replace_click_source(&source.container_source, &expanded_click)
    } else {
        Ok(expanded_click)
    }
}

/// Verifies the audited proof unit of a rewritten sidecar through the normal
/// targeted entry point,
/// resolving its C sources relative to the original on-disk sidecar path.
/// The unit is re-located by claim (its first tactic source) because the
/// rewrite moves source positions.
fn verify_rewritten(
    original_click_path: &Path,
    claim_label: &str,
    rewritten: &str,
) -> Result<(), String> {
    let source = load_audit_source_from_text(original_click_path, rewritten.to_string())?;
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

/// Checks that the rewritten sidecar is an expansion fixed point for the
/// audited site, resolving C sources
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
fn reexpand_source(
    click_path: &Path,
    claim_label: &str,
    rewritten: &str,
) -> Result<String, String> {
    let original = load_audit_source(click_path)?;
    let rewritten_source = load_audit_source_from_text(click_path, rewritten.to_string())?;
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
    Ok(rewritten.to_string())
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
                "--claim",
                "example.ensures_0",
                "--changed-since",
                "HEAD~1",
                "--verbose",
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
        assert!(arguments.verbose);
        assert_eq!(arguments.claims, ["example.ensures_0"]);
        assert_eq!(arguments.changed_since.as_deref(), Some("HEAD~1"));
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
    fn named_claim_selection_is_exact_ordered_and_rejects_ambiguity() {
        let site = |path: &str, claim: &str, line| AuditSite {
            click_path: PathBuf::from(path),
            position: SourcePosition { line, column: 1 },
            click_position: SourcePosition { line, column: 1 },
            claim: claim.to_string(),
            tactic_name: "auto".to_string(),
        };
        let sites = vec![
            site("a.click", "alpha.ensures_0", 1),
            site("a.click", "alpha.ensures_0", 2),
            site("a.click", "beta.ensures_0", 3),
        ];
        let selected = select_claim_sites(&sites, &["alpha.ensures_0".to_string()]).unwrap();
        assert_eq!(selected.len(), 2);
        assert_eq!(selected[0].position.line, 1);
        assert_eq!(selected[1].position.line, 2);
        assert!(
            select_claim_sites(&sites, &["missing".to_string()])
                .unwrap_err()
                .contains("unknown audit claim")
        );

        let ambiguous = vec![
            site("a.click", "alpha.ensures_0", 1),
            site("b.click", "alpha.ensures_0", 1),
        ];
        assert!(
            select_claim_sites(&ambiguous, &["alpha.ensures_0".to_string()])
                .unwrap_err()
                .contains("ambiguous")
        );
    }

    #[test]
    fn changed_selection_maps_leaf_proof_and_contract_changes_to_callers() {
        let c_sources = [
            ("leaf.c", "int32 leaf(int32 x) { return x; }"),
            (
                "caller.c",
                "int32 caller(int32 x) { int32 y = leaf(x); return y; }",
            ),
            ("unrelated.c", "int32 unrelated(int32 x) { return x; }"),
        ];
        let baseline = r#"
verifying "leaf.c";
verifying "caller.c";
verifying "unrelated.c";
int32 leaf(int32 x) { ensures result == x; } by simp;
int32 caller(int32 x) { ensures result == x; } by auto;
int32 unrelated(int32 x) { ensures result == x; } by auto;
"#;
        let site = |claim: &str, line| AuditSite {
            click_path: PathBuf::from("example.click"),
            position: SourcePosition { line, column: 1 },
            click_position: SourcePosition { line, column: 1 },
            claim: claim.to_string(),
            tactic_name: "auto".to_string(),
        };
        let sites = vec![
            site("leaf.contract", 1),
            site("caller.contract", 2),
            site("unrelated.contract", 3),
        ];

        for changed in [
            baseline.replacen("by simp", "by auto", 1),
            baseline.replacen("result == x", "result >= x", 1),
        ] {
            let selection =
                c0_incremental_selection(&changed, &c_sources, baseline, &c_sources).unwrap();
            assert_eq!(selection.selected_functions, ["caller", "leaf"]);
            let functions = selection
                .selected_functions
                .iter()
                .map(String::as_str)
                .collect::<BTreeSet<_>>();
            let selected = select_function_sites(&sites, &functions);
            assert_eq!(
                selected
                    .iter()
                    .map(|site| site.claim.as_str())
                    .collect::<Vec<_>>(),
                ["leaf.contract", "caller.contract"]
            );
        }
    }

    #[test]
    fn click_engine_changes_force_a_full_changed_audit() {
        let repo = Path::new(env!("CARGO_MANIFEST_DIR"));
        assert!(changed_paths_require_full_audit(
            repo,
            &[PathBuf::from("src/lang/click.rs")]
        ));
        assert!(!changed_paths_require_full_audit(
            repo,
            &[PathBuf::from("examples/owned-vector/vector.c")]
        ));
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
            claims: vec!["example.ensures_0".to_string()],
            changed_since: Some("HEAD~1".to_string()),
            verbose: true,
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
            "click audit --session-time-limit 30s --expansion-time-limit 2s \
             --verification-time-limit 3s --performance-slack 500ms --time-limit 10m \
             --verbose --claim example.ensures_0 --changed-since 'HEAD~1' --max-sites 1 \
             --start-at /tmp/example.click:12:34 'examples with spaces'"
        );
    }

    #[test]
    fn end_of_options_accepts_a_dash_prefixed_target() {
        let arguments = parse_arguments(["--".to_string(), "-example.click".to_string()]).unwrap();
        assert_eq!(arguments.path, PathBuf::from("-example.click"));
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
    fn whole_run_deadline_caps_each_phase() {
        let deadline = Instant::now() + Duration::from_secs(1);
        let limit = remaining_phase_limit(deadline, Duration::from_secs(30)).unwrap();
        assert!(limit <= Duration::from_secs(1));
        assert!(limit > Duration::ZERO);

        let expired = Instant::now()
            .checked_sub(Duration::from_millis(1))
            .unwrap();
        assert_eq!(
            remaining_phase_limit(expired, Duration::from_secs(30)),
            Err(RUN_LIMIT_EXHAUSTED.to_string())
        );
    }

    #[test]
    fn site_timing_output_distinguishes_measured_and_skipped_cold_work() {
        let base = SiteTimings {
            expansion: Duration::from_millis(1),
            session_verification: Duration::from_millis(2),
            cold_verification: None,
            reexpansion: Duration::from_millis(5),
        };
        let skipped = render_site_timings(&base);
        assert!(skipped.contains("cold comparison not run"), "{skipped}");
        assert!(!skipped.contains("cold original 0"), "{skipped}");

        let measured = render_site_timings(&SiteTimings {
            cold_verification: Some((Duration::from_millis(3), Duration::from_millis(4))),
            ..base
        });
        assert!(measured.contains("cold original 3ms"), "{measured}");
        assert!(measured.contains("cold rewritten 4ms"), "{measured}");
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
            mdtest: None,
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
    fn branched_expansion_reaches_the_audit_fixed_point() {
        let directory =
            std::env::temp_dir().join(format!("click-audit-branched-paths-{}", std::process::id()));
        if directory.exists() {
            fs::remove_dir_all(&directory).unwrap();
        }
        fs::create_dir(&directory).unwrap();
        let c_source = r#"int32 write_selected(int32 p[2], int32 flag) {
    if (flag) { p[0] = 1; return 0; }
    else { p[1] = 1; return 1; }
}"#;
        let click_source = r#"verifying "write_selected.c";
int32 write_selected(int32 p[2], int32 flag) {
    consumes p[0..2];
    mutable p[0..2];
    ensures result == 0 or result == 1;
} by {
    execute();
    if result == 0 {
        have result + 1 == 1 by simp;
        frame();
    } else {
        have result - 1 == 0 by simp;
        frame();
    }
    simp();
}
"#;
        let click_path = directory.join("branched.click");
        fs::write(directory.join("write_selected.c"), c_source).unwrap();
        fs::write(&click_path, click_source).unwrap();
        let sites = inventory_sites(std::slice::from_ref(&click_path)).unwrap();
        let site = sites
            .iter()
            .find(|site| site.tactic_name == "have")
            .expect("the branch should expose an auditable smart have");
        let expanded = expand_location(&format_location(&site_location(site)))
            .expect("the audit expansion path should handle branched frames");
        let source = load_audit_source_from_text(&click_path, expanded.clone()).unwrap();
        let refs = source_refs(&source.c_sources);
        verify_c0_sources(&source.click_source, &refs)
            .expect("the audited branched expansion should verify");

        assert_eq!(
            reexpand_source(&click_path, &site.claim, &expanded).unwrap(),
            expanded
        );
        fs::remove_dir_all(directory).unwrap();
    }
}
