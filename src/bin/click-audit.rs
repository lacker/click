use std::collections::{BTreeMap, BTreeSet};
use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::sync::mpsc;
use std::thread;
use std::time::{Duration, Instant};

use crate::git::{git_commit_id, git_repo_root, git_show};
use click::cli::{
    self, CInput, MdTestExpectation, TargetSelection, containing_directory, find_mdtests,
    format_duration, looks_like_mdtest, parse_duration, prepare_mdtest_inputs, read_c_inputs,
    read_lone_sidecar_project, read_mdtest_project_if_needed, select_targets, shell_quote,
    source_refs,
};
use click::surface::{
    C0VerificationSession, ClickProject, SourcePosition, c0_incremental_selection,
    click_import_sites, expand_c0_claim_source_by_label, expand_c0_prepared_claim_source_by_label,
    expand_c0_prepared_tactic_source_at, expand_c0_tactic_source_at,
    expand_program_prepared_claim_source_by_label, expand_program_prepared_tactic_source_at,
    expand_project_claim_source_by_label, expand_project_tactic_source_at,
    project_smart_tactic_source_sites, project_tactic_source_position, smart_tactic_source_sites,
    tactic_source_position, verify_project_at, verify_sources_at, verifying_source_paths,
};
use click::surface::{claim_label_matches, display_rust_names};

/// Each phase's wall-clock bound is crash containment only: a phase is judged
/// by its deterministic work, so machine load cannot change a verdict.
const DEFAULT_SESSION_LIMIT: Duration = cli::CRASH_CONTAINMENT_TIME_LIMIT;
const DEFAULT_EXPANSION_LIMIT: Duration = cli::CRASH_CONTAINMENT_TIME_LIMIT;
const DEFAULT_VERIFICATION_LIMIT: Duration = cli::CRASH_CONTAINMENT_TIME_LIMIT;
/// Deterministic work budgets for one phase, in the units the tactic budgets
/// are charged (`click::instrumentation::measure_deterministic_work`).
///
/// Calibration (2026-09-26, base `8a223dd2`): the largest session is
/// `examples/arena`'s at 6.5 million units, and the largest expansion and
/// proof-unit verification measured were under half a million units
/// (`examples/arena`, `rbtree-model`, `owned-vector`). The budgets leave over
/// 15x headroom on the session and 100x on one expansion or verification. At
/// the slowest measured rate (about 110,000 units a second under a load
/// average of 18) the crash bound still fires only past what these budgets
/// admit.
const DEFAULT_SESSION_WORK_LIMIT: usize = 100_000_000;
const DEFAULT_EXPANSION_WORK_LIMIT: usize = cli::DEFAULT_EXPANSION_WORK_LIMIT;
const DEFAULT_VERIFICATION_WORK_LIMIT: usize = 50_000_000;
/// The smallest expanded-over-original work increase that can fail the
/// performance comparison, beside its 2x ratio. Measured expansions spend
/// within 1% of their original's work; the slack keeps a proof unit of a few
/// thousand units from failing over a few thousand units of certificate
/// checking.
const DEFAULT_PERFORMANCE_SLACK: usize = 10_000;
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
includes the phase costs for each claim batch.

A claim whose sites are all selected is expanded once, with every site
together, since expanding one site runs its whole claim. Failure of that whole-claim
expansion fails the audit. A partial selection is captured together in one verification as well;
its fixed-point check covers only the emitted regions, leaving unselected
smart tactics unchanged.

The audit's own checks count deterministic work units, the ones the tactic
budgets are charged, so machine load cannot change them; wall-clock time is
reported only as information. On the first site of each claim, audit compares
the work of cold verification of the expanded proof with the original's, and
fails when the expanded proof spends both over 2x and over the performance
slack more. Each phase has a deterministic work budget. The phase time limits
are crash-containment bounds for a hung run, and the whole-run time limit
stops at a resumable cursor. Verification inside each phase keeps the tactic
limits `click verify` applies.

defaults:
  --session-work-limit 100000000   smart-site inventory or original-sidecar session initialization
  --expansion-work-limit 50000000  one expansion, and the re-expansion check
  --verification-work-limit 50000000
                                   one retained or cold proof-unit verification
  --performance-slack 10000        minimum expanded-over-original work increase
  --session-time-limit 10m         crash containment for inventory or session initialization
  --expansion-time-limit 10m       crash containment for one expansion
  --verification-time-limit 10m    crash containment for one verification
  --time-limit 10m                 whole-run wall clock; prints the resume cursor

options:
  --session-work-limit <UNITS>
  --expansion-work-limit <UNITS>
  --verification-work-limit <UNITS>
  --performance-slack <UNITS>
  --slow-site-limit <UNITS>   deprecated alias for --performance-slack
  --session-time-limit <DURATION>
                              (`--discovery-time-limit` is a compatibility alias)
  --expansion-time-limit <DURATION>
  --verification-time-limit <DURATION>
  --time-limit <DURATION>
  --start-at <PATH:LINE:COLUMN>
                              inclusively resume at this source location
  --claim <CLAIM>             audit one claim, by label or by PATH:LINE[:COLUMN]
                              of a line its clause or proof covers; may be
                              repeated
  --changed-since <REVISION>  audit claims affected since a Git revision
  --verbose                   print one successful row per smart site
  --keep-going                continue after failures instead of stopping
  --exclude <PATH>            leave out a proof container, or every one
                              under a directory; may be repeated
  --max-sites <COUNT>         bounded diagnostic run; prints the next cursor";

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    path: PathBuf,
    limits: AuditLimits,
    time_limit: Duration,
    start_at: Option<SourceLocation>,
    claims: Vec<String>,
    changed_since: Option<String>,
    verbose: bool,
    keep_going: bool,
    /// Proof containers, or directories of them, left out of the audit.
    exclude: Vec<PathBuf>,
    max_sites: Option<usize>,
}

/// The bounds on one audit phase: a deterministic work budget, which is the
/// verdict, and a wall-clock bound kept only as crash containment.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct PhaseLimit {
    work: usize,
    time: Duration,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct AuditLimits {
    session: PhaseLimit,
    expansion: PhaseLimit,
    verification: PhaseLimit,
    /// The smallest expanded-over-original work increase that can fail the
    /// performance comparison, beside its 2x ratio.
    performance_slack: usize,
}

impl Default for AuditLimits {
    fn default() -> Self {
        Self {
            session: PhaseLimit {
                work: DEFAULT_SESSION_WORK_LIMIT,
                time: DEFAULT_SESSION_LIMIT,
            },
            expansion: PhaseLimit {
                work: DEFAULT_EXPANSION_WORK_LIMIT,
                time: DEFAULT_EXPANSION_LIMIT,
            },
            verification: PhaseLimit {
                work: DEFAULT_VERIFICATION_WORK_LIMIT,
                time: DEFAULT_VERIFICATION_LIMIT,
            },
            performance_slack: DEFAULT_PERFORMANCE_SLACK,
        }
    }
}

impl PhaseLimit {
    /// This limit with its crash bound capped by what remains of the
    /// whole-run `deadline`.
    fn within(self, deadline: Instant) -> Result<Self, String> {
        Ok(Self {
            work: self.work,
            time: remaining_phase_limit(deadline, self.time)?,
        })
    }
}

/// What one audit phase cost: the deterministic work that judges it, and the
/// wall-clock time reported only as information.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct PhaseCost {
    work: usize,
    elapsed: Duration,
}

impl std::fmt::Display for PhaseCost {
    fn fmt(&self, formatter: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            formatter,
            "{} units, {}",
            self.work,
            format_duration(self.elapsed)
        )
    }
}

/// Runs one audit phase under `limit`: its deterministic work is the
/// verdict, and its wall-clock bound only contains a hung run.
fn run_phase<R>(
    label: &str,
    limit: PhaseLimit,
    operation: impl FnOnce() -> Result<R, String>,
) -> Result<(R, PhaseCost), String> {
    let time_limit = limit.time;
    let started = Instant::now();
    let (result, work) = click::instrumentation::measure_deterministic_work(|| {
        cli::within_run_limits(
            cli::RunLimits {
                work: limit.work,
                time: time_limit,
            },
            operation,
        )
    });
    let elapsed = started.elapsed();
    if elapsed >= time_limit {
        return Err(format!(
            "{label} crossed its {} crash-containment bound after {} ({work} work units); \
             audit judges a phase by its deterministic work, so a run this slow is hung \
             or starved of CPU{}",
            format_duration(time_limit),
            format_duration(elapsed),
            result
                .err()
                .map(|message| format!("\n{message}"))
                .unwrap_or_default()
        ));
    }
    if work > limit.work {
        return Err(format!(
            "{label} spent {work} deterministic work units, over its {}-unit budget \
             (wall clock {}, information only){}",
            limit.work,
            format_duration(elapsed),
            result
                .err()
                .map(|message| format!("\n{message}"))
                .unwrap_or_default()
        ));
    }
    let value = result?;
    Ok((value, PhaseCost { work, elapsed }))
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
    passed: usize,
    total: usize,
}

/// The retained verification session lives on a thread of its own. Its
/// verified environment names snapshots in the kernel's thread-local tables,
/// and every expansion, cold reverification, and re-expansion the audit runs
/// between session checks starts fresh tables on its own thread. Sharing the
/// audit thread let those runs replace the session's tables, so a rewrite
/// could exhaust a tactic budget only in the session. The kernel refuses a
/// session whose tables were replaced; this thread keeps them intact.
struct AuditSessionWorker {
    source: AuditSource,
    requests: Option<mpsc::Sender<SessionRequest>>,
    responses: mpsc::Receiver<Result<PhaseCost, String>>,
    thread: Option<thread::JoinHandle<()>>,
    /// What initializing the session cost.
    initialization: PhaseCost,
}

struct SessionRequest {
    click_source: String,
    position: SourcePosition,
    limit: PhaseLimit,
}

/// At least the main thread's usual 8 MiB, so a proof that `click verify`
/// checks on the main thread does not overflow only in the audit session.
const SESSION_THREAD_STACK_BYTES: usize = 64 << 20;

impl AuditSessionWorker {
    fn start(click_path: &Path, limit: PhaseLimit) -> Result<Self, String> {
        let source = load_audit_source(click_path)?;
        let session_source = source.clone();
        let (request_sender, request_receiver) = mpsc::channel::<SessionRequest>();
        let (response_sender, response_receiver) = mpsc::channel();
        let thread = thread::Builder::new()
            .name("click-audit-session".to_string())
            .stack_size(SESSION_THREAD_STACK_BYTES)
            .spawn(move || {
                let session = match run_phase("verification-session initialization", limit, || {
                    start_session(&session_source)
                }) {
                    Ok((session, cost)) => {
                        if response_sender.send(Ok(cost)).is_err() {
                            return;
                        }
                        session
                    }
                    Err(message) => {
                        let _ = response_sender.send(Err(message));
                        return;
                    }
                };
                for request in request_receiver {
                    let result = verify_in_session(&session, &session_source, &request);
                    if response_sender.send(result).is_err() {
                        return;
                    }
                }
            })
            .map_err(|error| format!("failed to start the verification-session thread: {error}"))?;
        let mut worker = Self {
            source,
            requests: Some(request_sender),
            responses: response_receiver,
            thread: Some(thread),
            initialization: PhaseCost::default(),
        };
        worker.initialization = worker.receive("verification-session initialization")?;
        Ok(worker)
    }

    fn verify(
        &mut self,
        click_source: &str,
        position: SourcePosition,
        limit: PhaseLimit,
    ) -> Result<PhaseCost, String> {
        let request = SessionRequest {
            click_source: click_source.to_string(),
            position,
            limit,
        };
        self.requests
            .as_ref()
            .ok_or("the verification-session thread has stopped")?
            .send(request)
            .map_err(|_| "the verification-session thread has stopped".to_string())?;
        self.receive("rewritten-sidecar verification")
    }

    fn receive(&mut self, label: &str) -> Result<PhaseCost, String> {
        self.responses.recv().unwrap_or_else(|_| {
            Err(format!(
                "the verification-session thread stopped during {label}"
            ))
        })
    }

    fn is_alive(&self) -> bool {
        self.thread
            .as_ref()
            .is_some_and(|thread| !thread.is_finished())
    }
}

impl Drop for AuditSessionWorker {
    fn drop(&mut self) {
        // Closing the request channel ends the session thread's loop.
        self.requests = None;
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

fn start_session(source: &AuditSource) -> Result<C0VerificationSession, String> {
    let (session, _) = match &source.inputs {
        CInput::Bundle(sources) => match &source.project {
            Some(project) => C0VerificationSession::new_project(project, &source_refs(sources)),
            None => C0VerificationSession::new(&source.click_source, &source_refs(sources)),
        },
        CInput::Prepared(imports) => match &source.project {
            Some(project) => C0VerificationSession::new_prepared_project(project, imports),
            None => C0VerificationSession::new_prepared(&source.click_source, imports),
        },
        CInput::PreparedProgram(import) => match &source.project {
            Some(project) => C0VerificationSession::new_program_prepared_project(project, import),
            None => C0VerificationSession::new_program_prepared(&source.click_source, import),
        },
    }
    .map_err(|error| error.report())?;
    Ok(session)
}

fn verify_in_session(
    session: &C0VerificationSession,
    source: &AuditSource,
    request: &SessionRequest,
) -> Result<PhaseCost, String> {
    let SessionRequest {
        click_source,
        position,
        limit,
    } = request;
    let verify = || match &source.inputs {
        CInput::Bundle(_) => match &source.project {
            Some(_) => session.verify_at_project(click_source, position.line, position.column),
            None => session.verify_at(click_source, position.line, position.column),
        },
        CInput::Prepared(_) | CInput::PreparedProgram(_) => match &source.project {
            Some(_) => session.verify_at_project(click_source, position.line, position.column),
            None => session.verify_at_prepared(click_source, position.line, position.column),
        },
    };
    let ((), cost) = run_phase("rewritten-sidecar verification", *limit, || {
        verify().map(|_| ()).map_err(|error| error.report())
    })?;
    Ok(cost)
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
    let mut limits = AuditLimits::default();
    let mut time_limit = DEFAULT_TIME_LIMIT;
    let mut start_at = None;
    let mut claims = Vec::new();
    let mut changed_since = None;
    let mut verbose = false;
    let mut keep_going = false;
    let mut exclude = Vec::new();
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
                limits.session.time = parse_next_duration(&mut arguments, &argument)?;
            }
            "--expansion-time-limit" => {
                limits.expansion.time = parse_next_duration(&mut arguments, &argument)?;
            }
            "--verification-time-limit" => {
                limits.verification.time = parse_next_duration(&mut arguments, &argument)?;
            }
            "--session-work-limit" => {
                limits.session.work = parse_next_work_units(&mut arguments, &argument)?;
            }
            "--expansion-work-limit" => {
                limits.expansion.work = parse_next_work_units(&mut arguments, &argument)?;
            }
            "--verification-work-limit" => {
                limits.verification.work = parse_next_work_units(&mut arguments, &argument)?;
            }
            "--performance-slack" | "--slow-site-limit" => {
                limits.performance_slack = parse_next_work_units(&mut arguments, &argument)?;
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
            "--exclude" => {
                let excluded = arguments
                    .next()
                    .ok_or_else(|| format!("missing path after `{argument}`\n{USAGE}"))?;
                exclude.push(PathBuf::from(excluded));
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
        limits,
        time_limit,
        start_at,
        claims,
        changed_since,
        verbose,
        keep_going,
        exclude,
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

fn parse_next_work_units(
    arguments: &mut impl Iterator<Item = String>,
    option: &str,
) -> Result<usize, String> {
    let source = arguments
        .next()
        .ok_or_else(|| format!("missing work-unit count after `{option}`\n{USAGE}"))?;
    parse_work_units(&source).map_err(|message| format!("`{option}`: {message}"))
}

/// Parses a deterministic work-unit count; `_` may group digits.
fn parse_work_units(source: &str) -> Result<usize, String> {
    let digits = source.trim().replace('_', "");
    if digits.is_empty() || !digits.bytes().all(|byte| byte.is_ascii_digit()) {
        return Err(format!(
            "invalid work-unit count `{source}`; audit budgets and the performance slack count \
             deterministic work units, not time (for example `100000` or `2_000_000`)"
        ));
    }
    digits
        .parse::<usize>()
        .map_err(|_| format!("work-unit count `{source}` is too large"))
}

fn run_audit(arguments: Arguments) -> Result<(), String> {
    let started = Instant::now();
    let deadline = started + arguments.time_limit;
    let sources = without_excluded(audit_targets(&arguments.path)?, &arguments.exclude)?;
    println!("INVENTORY");
    let inventory_limit = arguments.limits.session.within(deadline)?;
    let (sites, _) = run_phase("smart-site inventory", inventory_limit, || {
        for path in &sources {
            let source = load_audit_source(path)?;
            let runtime = match &source.project {
                Some(project) => click::surface::selected_project_thread_runtime(project),
                None => click::surface::selected_thread_runtime(&source.click_source),
            }
            .map_err(|error| error.report())?;
            if let Some(assumption) = runtime.assumption() {
                println!("  {} runtime assumption: {assumption}", path.display());
            }
        }
        inventory_sites(&sources)
    })?;
    let inventory_claims = sites
        .iter()
        .map(|site| (site.click_path.clone(), site.claim.clone()))
        .collect::<BTreeSet<_>>()
        .len();
    println!(
        "  {} unique smart source sites in {inventory_claims} claims",
        sites.len()
    );
    let claims = resolve_audit_claims(&sources, &arguments.claims)?;
    let claim_sites = select_claim_sites(&sites, &claims)?;
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
    // Sites of the current claim whose rewrites await its one verification:
    // each site's position in `selected` and its rewritten container.
    let mut pending: Vec<(usize, String)> = Vec::new();
    // Every inventoried site of each claim, to tell a wholly selected claim
    // from one a cursor or a change selection covers in part.
    let mut inventoried_claim_counts: BTreeMap<(PathBuf, String), usize> = BTreeMap::new();
    for site in &sites {
        *inventoried_claim_counts
            .entry((site.click_path.clone(), site.claim.clone()))
            .or_default() += 1;
    }
    let mut claim_failures = 0;
    let limits = &arguments.limits;
    println!(
        "\nClick expansion audit (work budgets: session {}, expansion {}, verification {}, \
         performance slack {} units; crash bounds: session {}, expansion {}, verification {}; \
         run limit {})",
        limits.session.work,
        limits.expansion.work,
        limits.verification.work,
        limits.performance_slack,
        format_duration(limits.session.time),
        format_duration(limits.expansion.time),
        format_duration(limits.verification.time),
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
            let session_limit = match arguments.limits.session.within(deadline) {
                Ok(limit) => limit,
                Err(_) => {
                    println!("STOPPED ({RUN_LIMIT_EXHAUSTED})");
                    out_of_time = true;
                    break;
                }
            };
            match AuditSessionWorker::start(&site.click_path, session_limit) {
                Ok(new_worker) => {
                    println!("ready ({})", new_worker.initialization);
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

        // Every selected slice of a claim shares one capture and one rewrite
        // check. A cap limits the slice before either expansion route runs.
        let claim_key = (site.click_path.clone(), site.claim.clone());
        let claim_sites = selected[cursor..]
            .iter()
            .take_while(|next| next.click_path == site.click_path && next.claim == site.claim)
            .count();
        let at_claim_start = pending.is_empty()
            && cursor
                .checked_sub(1)
                .and_then(|previous| selected.get(previous))
                .is_none_or(|previous| {
                    previous.click_path != site.click_path || previous.claim != site.claim
                });
        let claim_sites = claim_sites.min(
            arguments
                .max_sites
                .map_or(usize::MAX, |limit| limit.saturating_sub(attempted_sites)),
        );
        let whole_claim = inventoried_claim_counts.get(&claim_key) == Some(&claim_sites);
        if at_claim_start {
            print!(
                "CLAIM [{}/{}] {}  {} ({claim_sites} sites) ... ",
                selected_claim_order[&claim_key],
                selected_claim_order.len(),
                site.click_path.display(),
                site.claim,
            );
            std::io::stdout()
                .flush()
                .map_err(|error| format!("failed to flush audit progress: {error}"))?;
            let current = &mut worker
                .as_mut()
                .expect("the selected sidecar session was initialized")
                .1;
            let audit = if whole_claim {
                audit_claim_rewrite(site, current, &arguments.limits, deadline)
            } else {
                audit_selected_claim_rewrite(
                    &selected[cursor..cursor + claim_sites],
                    current,
                    &arguments.limits,
                    deadline,
                )
            };
            match audit {
                Ok(costs) => {
                    if arguments.verbose {
                        println!("ok ({claim_sites} sites together: {costs})");
                    } else {
                        println!("ok ({claim_sites} sites)");
                    }
                    cold_reverified_claims.insert(claim_key);
                    attempted_sites += claim_sites;
                    audited_sites += claim_sites;
                    cursor += claim_sites;
                    continue;
                }
                Err(message) => {
                    if Instant::now() >= deadline || message == RUN_LIMIT_EXHAUSTED {
                        println!("STOPPED");
                        println!("    {RUN_LIMIT_EXHAUSTED}");
                        out_of_time = true;
                        break;
                    }
                    println!("FAIL");
                    println!("    {}", message.replace('\n', "\n    "));
                    print_resume(&arguments, site);
                    claim_failures += 1;
                    attempted_sites += claim_sites;
                    if !arguments.keep_going {
                        break;
                    }
                    cursor += claim_sites;
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
                passed: 0,
                total: selected_claim_counts[&key],
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
        let next_is_same_claim = selected
            .get(cursor + 1)
            .is_some_and(|next| next.click_path == site.click_path && next.claim == site.claim);
        let capped = arguments
            .max_sites
            .is_some_and(|limit| attempted_sites == limit);
        let mut stop = false;
        match audit_site_rewrite(site, current, &arguments.limits, cold_reverify, deadline) {
            Ok(rewrite) => {
                if arguments.verbose {
                    println!("{}", render_site_rewrite(&rewrite));
                }
                pending.push((cursor, rewrite.expanded));
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
                stop = !arguments.keep_going;
            }
        }
        // The claim's rewrites are verified together once its last selected
        // site has been expanded.
        if !pending.is_empty() && (!next_is_same_claim || capped || stop) {
            if arguments.verbose {
                print!(
                    "CLAIM {} verify {} rewrite(s) ... ",
                    site.claim,
                    pending.len()
                );
                std::io::stdout()
                    .flush()
                    .map_err(|error| format!("failed to flush audit progress: {error}"))?;
            }
            let rewrites = pending
                .iter()
                .map(|(_, expanded)| expanded.as_str())
                .collect::<Vec<_>>();
            match verify_claim_rewrites(
                current,
                &site.claim,
                &rewrites,
                &arguments.limits,
                deadline,
            ) {
                Ok(cost) => {
                    audited_sites += pending.len();
                    if arguments.verbose {
                        println!("ok ({cost})");
                    } else if let Some(progress) = concise_progress.as_mut() {
                        progress.passed += pending.len();
                        if !next_is_same_claim {
                            println!("ok ({} sites)", progress.passed);
                        } else {
                            println!(
                                "partial ({}/{} sites passed)",
                                progress.passed, progress.total
                            );
                        }
                        concise_progress = None;
                    }
                }
                Err(failures) => {
                    if Instant::now() >= deadline
                        || failures
                            .iter()
                            .any(|(_, message)| message == RUN_LIMIT_EXHAUSTED)
                    {
                        println!("STOPPED");
                        println!("    {RUN_LIMIT_EXHAUSTED}");
                        out_of_time = true;
                        break;
                    }
                    println!("FAIL");
                    concise_progress = None;
                    for (index, message) in &failures {
                        let failed = &selected[pending[*index].0];
                        println!(
                            "  {} ({})",
                            format_location(&site_location(failed)),
                            failed.tactic_name
                        );
                        println!("    {}", message.replace('\n', "\n    "));
                    }
                    print_resume(&arguments, &selected[pending[failures[0].0].0]);
                    audited_sites += pending.len() - failures.len();
                    site_failures += failures.len();
                    stop |= !arguments.keep_going;
                }
            }
            pending.clear();
        }
        if stop {
            break;
        }
        cursor += 1;
    }
    // Sites expanded but not yet verified with their claim were not audited;
    // a resumed run starts from the first of them.
    if let Some((first, _)) = pending.first() {
        cursor = *first;
    }

    if let Some(progress) = concise_progress.take() {
        println!(
            "partial ({}/{} sites passed)",
            progress.passed, progress.total
        );
    }

    println!(
        "\nSUMMARY: {audited_sites} sites passed; {site_failures} site failures; \
         {claim_failures} claim failures; {session_failures} session failures; {} sites discovered{}",
        scoped_sites.len(),
        if arguments.max_sites.is_some() {
            " (bounded run)"
        } else {
            ""
        }
    );
    let failures = site_failures + claim_failures + session_failures;
    if out_of_time {
        if cursor < selected.len() {
            println!();
            print_resume(&arguments, &selected[cursor]);
        }
        return Err(format!(
            "audit stopped at its {} wall-clock run bound after {} of {} selected sites{}; \
             this bound paces a long audit and is not a verdict about any proof, so resume \
             with the command above",
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

/// Drops every source that is an excluded path or lies under one. An
/// exclusion that matches nothing is an error: it names a path that moved or
/// was never part of the audit, and silently auditing it again is what the
/// option exists to prevent.
fn without_excluded(sources: Vec<PathBuf>, exclude: &[PathBuf]) -> Result<Vec<PathBuf>, String> {
    if exclude.is_empty() {
        return Ok(sources);
    }
    let mut excluded = Vec::with_capacity(exclude.len());
    for path in exclude {
        let resolved = fs::canonicalize(path).map_err(|error| {
            format!("failed to resolve `--exclude {}`: {error}", path.display())
        })?;
        excluded.push((path, resolved, false));
    }
    let mut kept = Vec::with_capacity(sources.len());
    for source in sources {
        let resolved = fs::canonicalize(&source)
            .map_err(|error| format!("failed to resolve `{}`: {error}", source.display()))?;
        match excluded
            .iter_mut()
            .find(|(_, excluded, _)| resolved.starts_with(excluded))
        {
            Some((_, _, matched)) => *matched = true,
            None => kept.push(source),
        }
    }
    if let Some((path, _, _)) = excluded.iter().find(|(_, _, matched)| !matched) {
        return Err(format!(
            "`--exclude {}` matches no proof container in the audited path",
            path.display()
        ));
    }
    Ok(kept)
}

/// Selects audit sources with the target selection shared with `click
/// verify` and `click profile`, plus the repository root, which covers both
/// `examples/` and `mdtests/`.
fn audit_targets(path: &Path) -> Result<Vec<PathBuf>, String> {
    let examples = path.join("examples");
    let mdtests = path.join("mdtests");
    if examples.is_dir() && mdtests.is_dir() {
        let mut sources = audit_targets(&examples)?;
        sources.extend(find_mdtests(&mdtests)?);
        sources.sort();
        sources.dedup();
        return Ok(sources);
    }
    match select_targets(path)? {
        TargetSelection::Mdtests(paths) => Ok(paths),
        TargetSelection::Sidecars(selection) => {
            let mut sources = selection
                .sidecars()
                .map(Path::to_path_buf)
                .collect::<Vec<_>>();
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
    }
}

#[derive(Clone)]
struct AuditSource {
    container_source: String,
    click_source: String,
    c_sources: Vec<(String, String)>,
    inputs: CInput,
    project: Option<ClickProject>,
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
        let inputs = prepare_mdtest_inputs(&mdtest)?;
        let click_source = mdtest
            .click_source
            .clone()
            .ok_or_else(|| format!("mdtest `{}` has no ```click block", path.display()))?;
        let project = read_mdtest_project_if_needed(path, &click_source, &inputs)?;
        return Ok(AuditSource {
            container_source,
            click_source,
            c_sources: mdtest.c_sources.clone(),
            inputs,
            project,
            line_offset: mdtest.click_start_line.saturating_sub(1),
            mdtest: Some(mdtest),
        });
    }
    let inputs = read_c_inputs(path, &container_source)?;
    let project = read_lone_sidecar_project(path, &container_source)?;
    let c_sources = match &inputs {
        CInput::Bundle(sources) => sources.clone(),
        CInput::Prepared(_) | CInput::PreparedProgram(_) => Vec::new(),
    };
    Ok(AuditSource {
        click_source: container_source.clone(),
        container_source,
        c_sources,
        inputs,
        project: Some(project),
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
            c_sources: _,
            inputs,
            project,
            line_offset,
            ..
        } = source;
        let syntactic_sites = match (&project, &inputs) {
            (Some(project), _) => {
                project_smart_tactic_source_sites(project, &inputs.program_inputs())
            }
            (None, inputs) => smart_tactic_source_sites(&click_source, &inputs.program_inputs()),
        }
        .map_err(|error| {
            format!(
                "could not inventory smart tactics in `{}`: {}",
                canonical_path.display(),
                error.report()
            )
        })?;
        for syntactic in syntactic_sites {
            let position = syntactic.position;
            let container_position = SourcePosition {
                line: position.line + line_offset,
                column: position.column,
                origin: None,
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

/// One `--claim`: a label, or the claim covering a source location, which
/// also names the one file it is in.
#[derive(Clone, Debug, Eq, PartialEq)]
struct AuditClaim {
    /// As the user wrote it.
    requested: String,
    label: String,
    path: Option<PathBuf>,
}

impl AuditClaim {
    fn selects(&self, site: &AuditSite) -> bool {
        claim_label_matches(&site.claim, &self.label)
            && self
                .path
                .as_ref()
                .is_none_or(|path| *path == site.click_path)
    }
}

/// Resolves each `--claim`: a label as written, or `FILE:LINE[:COLUMN]`, the
/// claim whose clause or proof covers that line of one audited file.
fn resolve_audit_claims(sources: &[PathBuf], claims: &[String]) -> Result<Vec<AuditClaim>, String> {
    claims
        .iter()
        .map(|requested| {
            let Some(location) = cli::parse_claim_location(requested) else {
                return Ok(AuditClaim {
                    requested: requested.clone(),
                    label: requested.clone(),
                    path: None,
                });
            };
            let (path, _, _) = location?;
            let canonical = fs::canonicalize(&path)
                .map_err(|error| format!("failed to resolve `{}`: {error}", path.display()))?;
            if !sources
                .iter()
                .any(|source| fs::canonicalize(source).is_ok_and(|source| source == canonical))
            {
                return Err(format!(
                    "`{requested}` names a location in `{}`, which this audit does not read",
                    path.display()
                ));
            }
            let source = load_audit_source(&canonical)?;
            let claim = cli::claim_at_argument(
                requested,
                &canonical,
                source.line_offset,
                source.project.as_ref(),
                &source.click_source,
                &source.inputs,
                // Audit sites carry the label of the proof that writes them.
                click::surface::ClaimLocationScope::ProofUnit,
            )
            .expect("a parsed claim location")?;
            Ok(AuditClaim {
                requested: requested.clone(),
                label: claim.label,
                path: Some(canonical),
            })
        })
        .collect()
}

fn select_claim_sites(
    sites: &[AuditSite],
    claims: &[AuditClaim],
) -> Result<Vec<AuditSite>, String> {
    if claims.is_empty() {
        return Ok(sites.to_vec());
    }
    for claim in claims {
        let paths = sites
            .iter()
            .filter(|site| claim.selects(site))
            .map(|site| site.click_path.clone())
            .collect::<BTreeSet<_>>();
        if paths.is_empty() {
            if claim.path.is_some() {
                return Err(format!(
                    "`{}` names claim `{}`, which has no smart tactic to audit",
                    claim.requested,
                    display_rust_names(&claim.label)
                ));
            }
            let known = sites
                .iter()
                .map(|site| site.claim.as_str())
                .collect::<BTreeSet<_>>()
                .into_iter()
                .take(12)
                .collect::<Vec<_>>()
                .join(", ");
            return Err(format!(
                "unknown audit claim `{}`{}",
                claim.requested,
                if known.is_empty() {
                    String::new()
                } else {
                    format!("; known claims include: {known}")
                }
            ));
        }
        if paths.len() > 1 {
            return Err(format!(
                "audit claim `{}` is ambiguous across: {}; name one sidecar as the audit target, or select the claim by `FILE:LINE`",
                claim.requested,
                paths
                    .iter()
                    .map(|path| path.display().to_string())
                    .collect::<Vec<_>>()
                    .join(", ")
            ));
        }
    }
    Ok(sites
        .iter()
        .filter(|site| claims.iter().any(|claim| claim.selects(site)))
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
                    error.report()
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
    let click_engine_checkout = repo.join("src/surface.rs").is_file()
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
    if !click_import_sites(&container_source)
        .map_err(|error| error.report())?
        .is_empty()
    {
        // Historical graph loading needs every imported file at the selected
        // revision. Falling back to the ordinary full audit is safe.
        return Ok(None);
    }
    let parent = containing_directory(path);
    let mut c_sources = Vec::new();
    for name in verifying_source_paths(&container_source).map_err(|error| {
        format!(
            "could not read baseline sidecar `{}`: {}",
            path.display(),
            error.report()
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
        inputs: CInput::Bundle(c_sources.clone()),
        project: None,
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
    let limits = &arguments.limits;
    let mut words = vec![
        "click".to_string(),
        "audit".to_string(),
        "--session-work-limit".to_string(),
        limits.session.work.to_string(),
        "--expansion-work-limit".to_string(),
        limits.expansion.work.to_string(),
        "--verification-work-limit".to_string(),
        limits.verification.work.to_string(),
        "--performance-slack".to_string(),
        limits.performance_slack.to_string(),
        "--session-time-limit".to_string(),
        format_duration(limits.session.time),
        "--expansion-time-limit".to_string(),
        format_duration(limits.expansion.time),
        "--verification-time-limit".to_string(),
        format_duration(limits.verification.time),
        "--time-limit".to_string(),
        format_duration(arguments.time_limit),
    ];
    if arguments.keep_going {
        words.push("--keep-going".to_string());
    }
    for excluded in &arguments.exclude {
        words.push("--exclude".to_string());
        words.push(excluded.display().to_string());
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

fn remaining_phase_limit(deadline: Instant, configured: Duration) -> Result<Duration, String> {
    let remaining = deadline
        .checked_duration_since(Instant::now())
        .filter(|remaining| !remaining.is_zero())
        .ok_or_else(|| RUN_LIMIT_EXHAUSTED.to_string())?;
    Ok(configured.min(remaining))
}

/// The cost of each check of one site audited alone.
#[cfg(test)]
struct SiteTimings {
    expansion: PhaseCost,
    session_verification: PhaseCost,
    cold_verification: Option<(PhaseCost, PhaseCost)>,
    reexpansion: PhaseCost,
}

/// Audits one site alone, verifying its rewrite in the session by itself.
#[cfg(test)]
fn audit_site(
    site: &AuditSite,
    worker: &mut AuditSessionWorker,
    limits: &AuditLimits,
    cold_reverify: bool,
    deadline: Instant,
) -> Result<SiteTimings, String> {
    let rewrite = audit_site_rewrite(site, worker, limits, cold_reverify, deadline)?;
    let session_verification =
        verify_rewrite_in_session(worker, &site.claim, &rewrite.expanded, limits, deadline)?;
    Ok(SiteTimings {
        expansion: rewrite.expansion,
        session_verification,
        cold_verification: rewrite.cold_verification,
        reexpansion: rewrite.reexpansion,
    })
}

/// One site's checked rewrite. The caller verifies it in the retained
/// session, together with the rest of its claim's.
struct SiteRewrite {
    /// The proof container with this one site expanded.
    expanded: String,
    expansion: PhaseCost,
    cold_verification: Option<(PhaseCost, PhaseCost)>,
    reexpansion: PhaseCost,
}

fn render_site_rewrite(rewrite: &SiteRewrite) -> String {
    match rewrite.cold_verification {
        Some((original, rewritten)) => format!(
            "expanded (expand {}, cold original {original}, cold rewritten {rewritten}, \
             reexpand {})",
            rewrite.expansion, rewrite.reexpansion,
        ),
        None => format!(
            "expanded (expand {}, cold comparison not run, reexpand {})",
            rewrite.expansion, rewrite.reexpansion,
        ),
    }
}

/// Expands one site and checks everything about the rewrite that does not
/// need the retained session: the cold comparison and the re-expansion fixed
/// point.
/// Audits every smart site of one claim in a single expansion.
///
/// The claim is expanded once with all its sites, the expanded claim must
/// keep no smart tactic, and it is verified in the retained session and
/// through the cold direct entry point beside the original. Returns the
/// phase costs for the progress row.
fn audit_claim_rewrite(
    site: &AuditSite,
    worker: &mut AuditSessionWorker,
    limits: &AuditLimits,
    deadline: Instant,
) -> Result<String, String> {
    let (expanded, expansion) = run_phase("expansion", limits.expansion.within(deadline)?, || {
        expand_claim_with_source(&site.click_path, &worker.source, &site.claim)
    })?;
    let original = worker.source.container_source.clone();
    if expanded == original {
        return Err("expansion returned the original sidecar unchanged".to_string());
    }
    let expanded_click_source = rewritten_click_source(&worker.source, &expanded)
        .map_err(|error| format!("expanded proof container did not parse: {error}"))?;
    claim_source_position_for_source(&worker.source, &expanded_click_source, &site.claim)?;

    // The fixed point: an expanded claim holds simple tactics only.
    let remaining = claim_smart_sites(
        &expanded_click_source,
        &worker.source.inputs,
        worker.source.project.as_ref(),
        &site.claim,
    )?;
    if !remaining.is_empty() {
        return Err(format!(
            "the expanded claim `{}` still holds {} smart tactic(s): {}",
            site.claim,
            remaining.len(),
            remaining.join(", ")
        ));
    }

    let retained = verify_rewrite_in_session(worker, &site.claim, &expanded, limits, deadline)?;
    let original_cost = cold_verify(
        &original,
        &worker.source,
        &site.claim,
        limits.verification.within(deadline)?,
        "original proof-unit verification",
    )?;
    let expanded_cost = cold_verify(
        &expanded,
        &worker.source,
        &site.claim,
        limits.verification.within(deadline)?,
        "expanded proof-unit verification",
    )?;
    if let Some(regression) =
        performance_regression(original_cost, expanded_cost, limits.performance_slack)
    {
        return Err(format!(
            "{regression}; reproduce the exact expanded workload with:\n  \
             click expand --claim {} --time-limit {} --output {} {}\n  \
             click profile {}",
            shell_quote(&site.claim),
            format_duration(limits.expansion.time),
            shell_quote(&audit_artifact_path(&site.click_path).display().to_string()),
            shell_quote(&site.click_path.display().to_string()),
            shell_quote(&audit_artifact_path(&site.click_path).display().to_string()),
        ));
    }
    Ok(format!(
        "expand {expansion}, verify {retained}, cold original {original_cost}, cold rewritten {expanded_cost}"
    ))
}

/// A partial selection uses one capture and one rewritten claim check,
/// regardless of its site count. Its fixed-point inventory consults only
/// emitted regions, so unselected automation remains outside the request.
fn audit_selected_claim_rewrite(
    sites: &[AuditSite],
    worker: &mut AuditSessionWorker,
    limits: &AuditLimits,
    deadline: Instant,
) -> Result<String, String> {
    let first = &sites[0];
    let positions = sites
        .iter()
        .map(|site| site.click_position.clone())
        .collect::<Vec<_>>();
    let source = &worker.source;
    let (artifact, expansion) = run_phase("expansion", limits.expansion.within(deadline)?, || {
        use click::surface::*;
        match (&source.project, &source.inputs) {
            (Some(project), inputs) => {
                expand_project_tactics_source_at(project, &inputs.program_inputs(), &positions)
            }
            (None, inputs) => {
                expand_tactics_source_at(&source.click_source, &inputs.program_inputs(), &positions)
            }
        }
        .map_err(|error| error.report())
    })?;
    let ((), fixed_point) = run_phase(
        "selected fixed point",
        limits.expansion.within(deadline)?,
        || {
            let remaining =
                smart_sites_for_source(&artifact.source, &source.inputs, source.project.as_ref())?;
            let positions = remaining
                .into_iter()
                .map(|site| ((site.position.line, site.position.column), site.tactic_name))
                .collect::<BTreeMap<_, _>>();
            let (mut line, mut column, mut region) = (1, 1, 0);
            for (offset, character) in artifact.source.char_indices() {
                while artifact
                    .replacement_spans
                    .get(region)
                    .is_some_and(|span| span.end <= offset)
                {
                    region += 1;
                }
                if artifact
                    .replacement_spans
                    .get(region)
                    .is_some_and(|span| span.contains(&offset))
                    && let Some(tactic) = positions.get(&(line, column))
                {
                    return Err(format!(
                        "selected expansion introduced smart tactic `{tactic}`; its rewrite is not a fixed point"
                    ));
                }
                if character == '\n' {
                    line += 1;
                    column = 1;
                } else {
                    column += 1;
                }
            }
            Ok(())
        },
    )?;
    let expanded = if let Some(mdtest) = &source.mdtest {
        mdtest.replace_click_source(&source.container_source, &artifact.source)?
    } else {
        artifact.source
    };
    if expanded == source.container_source {
        return Err("expansion returned the original sidecar unchanged".into());
    }
    let original = source.container_source.clone();
    let original_cost = cold_verify(
        &original,
        source,
        &first.claim,
        limits.verification.within(deadline)?,
        "original proof-unit verification",
    )?;
    let expanded_cost = cold_verify(
        &expanded,
        source,
        &first.claim,
        limits.verification.within(deadline)?,
        "expanded proof-unit verification",
    )?;
    if let Some(regression) =
        performance_regression(original_cost, expanded_cost, limits.performance_slack)
    {
        return Err(regression);
    }
    let retained = verify_rewrite_in_session(worker, &first.claim, &expanded, limits, deadline)?;
    Ok(format!(
        "expand {expansion}, fixed point {fixed_point}, verify {retained}, cold original {original_cost}, cold rewritten {expanded_cost}"
    ))
}

/// The proof container with every smart site of `claim_label` expanded.
fn expand_claim_with_source(
    click_path: &Path,
    source: &AuditSource,
    claim_label: &str,
) -> Result<String, String> {
    let expanded_click = match (&source.project, &source.inputs) {
        (Some(project), inputs) => {
            expand_project_claim_source_by_label(project, &inputs.program_inputs(), claim_label)
        }
        (None, CInput::Bundle(sources)) => expand_c0_claim_source_by_label(
            &source.click_source,
            &source_refs(sources),
            claim_label,
        ),
        (None, CInput::Prepared(imports)) => {
            expand_c0_prepared_claim_source_by_label(&source.click_source, imports, claim_label)
        }
        (None, CInput::PreparedProgram(import)) => {
            expand_program_prepared_claim_source_by_label(&source.click_source, import, claim_label)
        }
    }
    .map_err(|error| error.report())?;
    if looks_like_mdtest(click_path) {
        source
            .mdtest
            .as_ref()
            .expect("markdown audit sources retain their parsed container")
            .replace_click_source(&source.container_source, &expanded_click)
    } else {
        Ok(expanded_click)
    }
}

/// The names of the smart tactics the inventory finds in `claim_label`.
fn claim_smart_sites(
    source: &str,
    inputs: &CInput,
    project: Option<&ClickProject>,
    claim_label: &str,
) -> Result<Vec<String>, String> {
    smart_sites_for_source(source, inputs, project).map(|sites| {
        sites
            .into_iter()
            .filter(|site| site.claim_label == claim_label)
            .map(|site| site.tactic_name)
            .collect()
    })
}

fn smart_sites_for_source(
    source: &str,
    inputs: &CInput,
    project: Option<&ClickProject>,
) -> Result<Vec<click::surface::SmartTacticSourceSite>, String> {
    let sites = match (project, inputs) {
        (Some(project), _) => project_smart_tactic_source_sites(
            &project.with_entry_source(source.to_string()),
            &inputs.program_inputs(),
        ),
        (None, inputs) => smart_tactic_source_sites(source, &inputs.program_inputs()),
    };
    sites.map_err(|error| error.report())
}

fn audit_site_rewrite(
    site: &AuditSite,
    worker: &mut AuditSessionWorker,
    limits: &AuditLimits,
    cold_reverify: bool,
    deadline: Instant,
) -> Result<SiteRewrite, String> {
    let location = format!(
        "{}:{}:{}",
        site.click_path.display(),
        site.position.line,
        site.position.column
    );
    let (expanded, expansion) = run_phase("expansion", limits.expansion.within(deadline)?, || {
        expand_location_with_source(&location, &worker.source)
    })?;
    let original = worker.source.container_source.clone();
    if expanded == original {
        return Err("expansion returned the original sidecar unchanged".to_string());
    }
    let expanded_click_source = rewritten_click_source(&worker.source, &expanded)
        .map_err(|error| format!("expanded proof container did not parse: {error}"))?;
    // The rewritten claim must still be found: expansion can insert or
    // remove lines at the selected tactic, so later checks resolve the proof
    // unit by claim rather than by its now-stale source coordinate.
    claim_source_position_for_source(&worker.source, &expanded_click_source, &site.claim)?;

    // Checklist step 6: reverify the rewritten proof unit from normal
    // inputs by running the direct targeted entry point under
    // the verification limits. The retained session checks the
    // rewrite changed nothing outside the audited proof unit, so the other
    // units' outcomes cannot change; a whole-file pass here would redo them
    // all per site, which made auditing a project cost sites x whole-file
    // time. The cold direct pass catches anything the retained session's
    // cached environment masks, which one site per claim already
    // exercises — repeating it for every site of a many-site claim would
    // double the whole audit for no additional coverage.
    let cold_verification = if cold_reverify {
        let original_cost = cold_verify(
            &original,
            &worker.source,
            &site.claim,
            limits.verification.within(deadline)?,
            "original proof-unit verification",
        )?;
        let expanded_cost = cold_verify(
            &expanded,
            &worker.source,
            &site.claim,
            limits.verification.within(deadline)?,
            "expanded proof-unit verification",
        )?;
        if let Some(regression) =
            performance_regression(original_cost, expanded_cost, limits.performance_slack)
        {
            let artifact = audit_artifact_path(&site.click_path);
            return Err(format!(
                "{regression}; reproduce the exact expanded workload with:\n  \
                 click expand --time-limit {} --output {} {}\n  \
                 click profile {}",
                format_duration(limits.expansion.time),
                shell_quote(&artifact.display().to_string()),
                shell_quote(&location),
                shell_quote(&artifact.display().to_string()),
            ));
        }
        Some((original_cost, expanded_cost))
    } else {
        None
    };

    // Checklist step 7: re-expanding the same claim against the rewritten
    // source must be a fixed point, byte for byte. The site is re-resolved
    // by claim because the rewrite moves and replaces tactics.
    let (reexpanded, reexpansion) =
        run_phase("re-expansion", limits.expansion.within(deadline)?, || {
            reexpand_source_with_inputs(
                &worker.source,
                &site.claim,
                &expanded_click_source,
                &expanded,
            )
        })?;
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

    Ok(SiteRewrite {
        expanded,
        expansion,
        cold_verification,
        reexpansion,
    })
}

/// The single contiguous edit that turns `original` into `rewritten`.
fn rewrite_edit<'a>(original: &str, rewritten: &'a str) -> (std::ops::Range<usize>, &'a str) {
    let mut prefix = original
        .bytes()
        .zip(rewritten.bytes())
        .take_while(|(left, right)| left == right)
        .count();
    while !original.is_char_boundary(prefix) || !rewritten.is_char_boundary(prefix) {
        prefix -= 1;
    }
    let limit = original.len().min(rewritten.len()) - prefix;
    let mut suffix = original
        .bytes()
        .rev()
        .zip(rewritten.bytes().rev())
        .take(limit)
        .take_while(|(left, right)| left == right)
        .count();
    while !original.is_char_boundary(original.len() - suffix)
        || !rewritten.is_char_boundary(rewritten.len() - suffix)
    {
        suffix -= 1;
    }
    (
        prefix..original.len() - suffix,
        &rewritten[prefix..rewritten.len() - suffix],
    )
}

/// Applies every single-site rewrite of `original` to one copy of it.
/// `None` when two rewrites touch the same text, so they cannot be applied
/// independently.
fn combine_rewrites(original: &str, rewrites: &[&str]) -> Option<String> {
    let mut edits = rewrites
        .iter()
        .map(|rewritten| rewrite_edit(original, rewritten))
        .collect::<Vec<_>>();
    edits.sort_by_key(|(span, _)| (span.start, span.end));
    if edits
        .windows(2)
        .any(|pair| pair[0].0.end > pair[1].0.start || pair[0].0 == pair[1].0)
    {
        return None;
    }
    let mut combined = String::with_capacity(original.len());
    let mut cursor = 0;
    for (span, replacement) in edits {
        combined.push_str(&original[cursor..span.start]);
        combined.push_str(replacement);
        cursor = span.end;
    }
    combined.push_str(&original[cursor..]);
    Some(combined)
}

fn verify_rewrite_in_session(
    worker: &mut AuditSessionWorker,
    claim: &str,
    rewritten_container: &str,
    limits: &AuditLimits,
    deadline: Instant,
) -> Result<PhaseCost, String> {
    let click_source = rewritten_click_source(&worker.source, rewritten_container)
        .map_err(|error| format!("expanded proof container did not parse: {error}"))?;
    let position = claim_source_position_for_source(&worker.source, &click_source, claim)?;
    worker.verify(
        &click_source,
        position,
        limits.verification.within(deadline)?,
    )
}

/// Verifies the rewrites of one claim's sites in the retained session.
///
/// Verifying each site's rewrite alone runs the whole claim once per site.
/// The rewrites of one claim are disjoint edits of one proof, so they are
/// applied together and the claim is verified once. Only when that fails, or
/// two edits overlap, is each rewrite verified alone, which names the site
/// whose rewrite fails; `Err` carries the failing sites by position in
/// `rewrites`.
fn verify_claim_rewrites(
    worker: &mut AuditSessionWorker,
    claim: &str,
    rewrites: &[&str],
    limits: &AuditLimits,
    deadline: Instant,
) -> Result<PhaseCost, Vec<(usize, String)>> {
    let original = worker.source.container_source.clone();
    let combined_failure = match combine_rewrites(&original, rewrites) {
        Some(combined) => {
            match verify_rewrite_in_session(worker, claim, &combined, limits, deadline) {
                Ok(cost) => return Ok(cost),
                Err(message) if message == RUN_LIMIT_EXHAUSTED => return Err(vec![(0, message)]),
                Err(message) => Some(message),
            }
        }
        None => None,
    };
    if !worker.is_alive() {
        return Err(vec![(
            0,
            combined_failure.unwrap_or_else(|| "the verification session stopped".to_string()),
        )]);
    }
    let mut total = PhaseCost {
        work: 0,
        elapsed: Duration::ZERO,
    };
    let mut failures = Vec::new();
    for (index, rewritten) in rewrites.iter().enumerate() {
        match verify_rewrite_in_session(worker, claim, rewritten, limits, deadline) {
            Ok(cost) => {
                total.work += cost.work;
                total.elapsed += cost.elapsed;
            }
            Err(message) => {
                let stop = message == RUN_LIMIT_EXHAUSTED || !worker.is_alive();
                failures.push((index, message));
                if stop {
                    break;
                }
            }
        }
    }
    match (failures.is_empty(), combined_failure) {
        (true, None) => Ok(total),
        (true, Some(message)) => Err(vec![(
            0,
            format!(
                "each of the claim's {} rewrites verifies alone, but they do not verify \
                 together: {message}",
                rewrites.len()
            ),
        )]),
        (false, _) => Err(failures),
    }
}

fn cold_verify(
    source: &str,
    original: &AuditSource,
    claim_label: &str,
    limit: PhaseLimit,
    label: &str,
) -> Result<PhaseCost, String> {
    let ((), cost) = run_phase(label, limit, || {
        let rewritten_click_source = rewritten_click_source(original, source)?;
        verify_rewritten_with_inputs(original, claim_label, &rewritten_click_source)
    })?;
    Ok(cost)
}

/// Whether the expanded proof's deterministic work regressed: over twice the
/// original's and more than `performance_slack` units over it.
fn verification_regressed(original: usize, expanded: usize, performance_slack: usize) -> bool {
    expanded > original.saturating_mul(2) && expanded > original.saturating_add(performance_slack)
}

/// The performance comparison's verdict on cold verification of the original
/// and expanded proof unit. Work units are deterministic, so one comparison
/// decides on any machine under any load; wall-clock time is information.
fn performance_regression(
    original: PhaseCost,
    expanded: PhaseCost,
    performance_slack: usize,
) -> Option<String> {
    verification_regressed(original.work, expanded.work, performance_slack).then(|| {
        format!(
            "expanded proof-unit verification spent {} deterministic work units against the \
             original's {} (failure requires over 2x and over {performance_slack} units more; \
             wall clock {} -> {}, information only)",
            expanded.work,
            original.work,
            format_duration(original.elapsed),
            format_duration(expanded.elapsed),
        )
    })
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

#[cfg(test)]
fn expand_location(location: &str) -> Result<String, String> {
    let (click_path, line, column) = cli::parse_source_location(location)?;
    let source = load_audit_source(&click_path)?;
    expand_location_with_source_parts(&click_path, &source, line, column)
}

fn expand_location_with_source(location: &str, source: &AuditSource) -> Result<String, String> {
    let (click_path, line, column) = cli::parse_source_location(location)?;
    expand_location_with_source_parts(&click_path, source, line, column)
}

fn expand_location_with_source_parts(
    click_path: &Path,
    source: &AuditSource,
    line: usize,
    column: usize,
) -> Result<String, String> {
    let click_line = if let Some(mdtest) = &source.mdtest {
        mdtest.click_line(line)?
    } else if line > 0 && line <= source.click_source.lines().count() {
        line
    } else {
        return Err(format!(
            "line {line} is outside the proof container's Click source"
        ));
    };
    let expanded_click = match (&source.project, &source.inputs) {
        (Some(project), inputs) => {
            expand_project_tactic_source_at(project, &inputs.program_inputs(), click_line, column)
        }
        (None, CInput::Bundle(sources)) => expand_c0_tactic_source_at(
            &source.click_source,
            &source_refs(sources),
            click_line,
            column,
        ),
        (None, CInput::Prepared(imports)) => {
            expand_c0_prepared_tactic_source_at(&source.click_source, imports, click_line, column)
        }
        (None, CInput::PreparedProgram(import)) => expand_program_prepared_tactic_source_at(
            &source.click_source,
            import,
            click_line,
            column,
        ),
    }
    .map_err(|error| error.report())?;
    if looks_like_mdtest(click_path) {
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
fn verify_rewritten_with_inputs(
    source: &AuditSource,
    claim_label: &str,
    rewritten_click_source: &str,
) -> Result<(), String> {
    let position = claim_source_position_for_source(source, rewritten_click_source, claim_label)?;
    match (&source.project, &source.inputs) {
        (Some(project), inputs) => verify_project_at(
            &project.with_entry_source(rewritten_click_source.to_string()),
            &inputs.program_inputs(),
            position.line,
            position.column,
        ),
        (None, inputs) => verify_sources_at(
            rewritten_click_source,
            &inputs.program_inputs(),
            position.line,
            position.column,
        ),
    }
    .map(|_| ())
    .map_err(|error| error.report())
}

#[cfg(test)]
fn claim_source_position(
    source: &AuditSource,
    claim_label: &str,
) -> Result<SourcePosition, String> {
    claim_source_position_for_source(source, &source.click_source, claim_label)
}

fn claim_source_position_for_source(
    source: &AuditSource,
    click_source: &str,
    claim_label: &str,
) -> Result<SourcePosition, String> {
    let Some(project) = &source.project else {
        return claim_source_position_for_inputs(click_source, &source.inputs, claim_label);
    };
    let position = project_tactic_source_position(
        &project.with_entry_source(click_source.to_string()),
        &source.inputs.program_inputs(),
        claim_label,
        0,
    );
    position.map_err(|error| {
        format!(
            "could not locate `{claim_label}` in the rewritten sidecar: {}",
            error.report()
        )
    })
}

fn claim_source_position_for_inputs(
    click_source: &str,
    inputs: &CInput,
    claim_label: &str,
) -> Result<SourcePosition, String> {
    let position = tactic_source_position(click_source, &inputs.program_inputs(), claim_label, 0);
    position.map_err(|error| {
        format!(
            "could not locate `{claim_label}` in the rewritten sidecar: {}",
            error.report()
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
#[cfg(test)]
fn reexpand_source(
    click_path: &Path,
    claim_label: &str,
    rewritten: &str,
) -> Result<String, String> {
    let original = load_audit_source(click_path)?;
    let rewritten_source = load_audit_source_from_text(click_path, rewritten.to_string())?;
    reexpand_source_with_inputs(
        &original,
        claim_label,
        &rewritten_source.click_source,
        rewritten,
    )
}

fn reexpand_source_with_inputs(
    original: &AuditSource,
    claim_label: &str,
    rewritten_click_source: &str,
    rewritten_container: &str,
) -> Result<String, String> {
    let claim_sites = |source: &str, inputs: &CInput, project: Option<&ClickProject>| {
        claim_smart_sites(source, inputs, project, claim_label)
    };
    let original_sites = claim_sites(
        &original.click_source,
        &original.inputs,
        original.project.as_ref(),
    )?;
    let rewritten_sites = claim_sites(
        rewritten_click_source,
        &original.inputs,
        original.project.as_ref(),
    )?;
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
    Ok(rewritten_container.to_string())
}

fn rewritten_click_source(source: &AuditSource, rewritten: &str) -> Result<String, String> {
    if source.mdtest.is_some() {
        let mdtest = cli::parse_mdtest(&PathBuf::from("<expanded>"), rewritten)?;
        mdtest
            .click_source
            .ok_or_else(|| "expanded proof container has no ```click block".to_string())
    } else {
        Ok(rewritten.to_string())
    }
}

#[cfg(test)]
#[path = "click-audit/tests.rs"]
mod tests;
