use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fs;
use std::path::{Path, PathBuf};
use std::time::{Duration, Instant};

use click::cli::{
    DEFAULT_EXPANSION_TIME_LIMIT, DEFAULT_SIMPLE_TACTIC_LIMIT, DEFAULT_SMART_TACTIC_LIMIT,
    MdTestExpectation, files_with_extension, find_mdtests, find_projects, format_duration,
    format_fractional_duration, looks_like_mdtest, parse_duration, read_mdtest,
    read_verifying_sources, shell_quote, source_refs,
};
use click::instrumentation::{self, ActiveVerificationWork, TacticEvent, VerificationEvent};
use click::lang::click::{
    SourcePosition, c0_smart_tactic_source_sites, c0_tactic_source_position, verify_c0_sources,
};

const DEFAULT_TIME_LIMIT: Duration = Duration::from_secs(30);
const MATERIAL_UNATTRIBUTED_FLOOR: Duration = Duration::from_millis(250);
const MATERIAL_UNATTRIBUTED_TIME: Duration = Duration::from_secs(1);
const MATERIAL_UNATTRIBUTED_SHARE: f64 = 10.0;
const SIMPLE_AVERAGE_LIMIT: Duration = Duration::from_millis(50);
const CERTIFICATION_PER_CLAIM_LIMIT: Duration = Duration::from_millis(250);
const CERTIFICATION_PER_PATH_LIMIT: Duration = Duration::from_secs(1);
const SETUP_PER_FILE_LIMIT: Duration = Duration::from_millis(250);
const VOLUME_REPORT_THRESHOLD: Duration = Duration::from_secs(1);
const DEFAULT_TOP_ATTRIBUTION_ROWS: usize = 8;

const USAGE: &str = "\
usage: click profile [OPTIONS] <sidecar.click|example-project|examples-directory|mdtest.md|mdtests-directory>

An mdtest is profiled from its embedded ```c and ```click blocks, using the
same extraction the mdtests gate uses. Quarantine does not apply: any mdtest
can be profiled, which is the point when diagnosing a slow one.

Verify first. Use profile for optimization only after the selected proof
verifies. A prompt correctness failure should be repaired before profiling;
profile a non-verifying target only when a timeout or unexpected slowness is
itself the problem being diagnosed. Incomplete runs never offer expansion.

defaults:
  --smart-threshold 2s      smart tactics in verified proofs are expansion candidates
  --simple-threshold 500ms  slow simple tactics are verifier bugs; do not expand them
  --control-threshold 2s    inspect slow control-flow containers and their nested steps
  --time-limit 30s          wall-clock limit per project
  --top 8                   maximum function/claim attribution rows per project

options:
  --smart-threshold <DURATION>
  --simple-threshold <DURATION>
  --control-threshold <DURATION>
  --top <COUNT>
  --threshold <DURATION>    shorthand setting all three thresholds
  --time-limit <DURATION>";

fn main() {
    if let Err(message) = entry() {
        eprintln!("click-profile: {message}");
        std::process::exit(1);
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct Arguments {
    path: PathBuf,
    thresholds: Thresholds,
    time_limit: Duration,
    top_attribution_rows: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
struct Thresholds {
    smart: Duration,
    simple: Duration,
    control: Duration,
}

impl Default for Thresholds {
    fn default() -> Self {
        Self {
            smart: DEFAULT_SMART_TACTIC_LIMIT,
            simple: DEFAULT_SIMPLE_TACTIC_LIMIT,
            control: Duration::from_secs(2),
        }
    }
}

impl Thresholds {
    fn for_category(self, category: TacticCategory) -> Duration {
        match category {
            TacticCategory::Smart => self.smart,
            TacticCategory::Simple => self.simple,
            TacticCategory::Control => self.control,
        }
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum TacticCategory {
    Smart,
    Simple,
    Control,
}

impl TacticCategory {
    fn parse(source: &str) -> Option<Self> {
        match source {
            "smart" => Some(Self::Smart),
            "simple" => Some(Self::Simple),
            "control" => Some(Self::Control),
            _ => None,
        }
    }

    fn label(self) -> &'static str {
        match self {
            Self::Smart => "SMART",
            Self::Simple => "SIMPLE",
            Self::Control => "CONTROL",
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct StepKey {
    source_path: PathBuf,
    claim: String,
    tactic_index: usize,
    source_index: usize,
    tactic_name: String,
    category: TacticCategory,
    statement_index: usize,
    position: Option<SourcePosition>,
}

#[derive(Clone, Debug)]
struct SlowStep {
    key: StepKey,
    elapsed: Duration,
    failed: bool,
}

#[derive(Clone, Debug)]
struct ProjectProfile {
    project: String,
    slow_steps: Vec<SlowStep>,
    active: Vec<StepKey>,
    interrupted: Option<InterruptedWork>,
    timed_out: bool,
    verification_failure: Option<String>,
    /// `click timing:` lines this profiler did not recognize, keyed by the
    /// word after the prefix, with a count and one verbatim example. A
    /// profile that silently drops timing lines is a false green, so these
    /// are reported instead of ignored.
    unknown_timing: BTreeMap<String, UnknownTiming>,
    accounting: TimeAccounting,
    work: WorkMetrics,
    attribution: BTreeMap<String, FunctionAttribution>,
    /// Reasons a reported step's source position could not be resolved,
    /// counted. Auto-planned loop-phase certificates carry synthesized tactic
    /// indices that no surface proof has, so those steps are reported with
    /// their claim and no location rather than sinking the whole profile.
    unresolved_positions: BTreeMap<String, usize>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum InterruptedWork {
    Tactic(StepKey),
    Phase(&'static str),
    Driver,
}

#[derive(Clone, Debug)]
struct UnknownTiming {
    count: usize,
    example: String,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct OperationStats {
    count: usize,
    total: Duration,
    max: Duration,
}

impl OperationStats {
    fn add(&mut self, elapsed: Duration) {
        self.count += 1;
        self.total += elapsed;
        self.max = self.max.max(elapsed);
    }

    fn average(self) -> Duration {
        if self.count == 0 {
            Duration::ZERO
        } else {
            self.total / u32::try_from(self.count).unwrap_or(u32::MAX)
        }
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct WorkMetrics {
    source_files: usize,
    functions: usize,
    claims: usize,
    certification_paths: usize,
    smart_source_sites: usize,
    tactics: BTreeMap<(TacticCategory, String), OperationStats>,
    c_transitions: OperationStats,
    failed_tactics: Vec<StepKey>,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct AttributedBuckets {
    simple: Duration,
    smart: Duration,
    control: Duration,
    certification: Duration,
    verifier_core: Duration,
    smart_attempts: usize,
}

impl AttributedBuckets {
    fn add_tactic(&mut self, category: TacticCategory, elapsed: Duration) {
        match category {
            TacticCategory::Simple => self.simple += elapsed,
            TacticCategory::Smart => {
                self.smart += elapsed;
                self.smart_attempts += 1;
            }
            TacticCategory::Control => self.control += elapsed,
        }
    }

    fn total(self) -> Duration {
        self.simple + self.smart + self.control + self.certification + self.verifier_core
    }
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct ClaimAttribution {
    buckets: AttributedBuckets,
    smart_sites: BTreeSet<(PathBuf, usize)>,
}

#[derive(Clone, Debug, Default, Eq, PartialEq)]
struct FunctionAttribution {
    buckets: AttributedBuckets,
    claims: BTreeMap<String, ClaimAttribution>,
}

impl WorkMetrics {
    fn add_tactic(&mut self, key: &StepKey, elapsed: Duration) {
        self.tactics
            .entry((key.category, key.tactic_name.clone()))
            .or_default()
            .add(elapsed);
        if key.category == TacticCategory::Simple && is_c_transition(&key.tactic_name) {
            self.c_transitions.add(elapsed);
        }
    }

    fn category(&self, category: TacticCategory) -> OperationStats {
        self.tactics
            .iter()
            .filter(|((candidate, _), _)| *candidate == category)
            .fold(OperationStats::default(), |mut total, (_, stats)| {
                total.count += stats.count;
                total.total += stats.total;
                total.max = total.max.max(stats.max);
                total
            })
    }
}

fn is_c_transition(tactic_name: &str) -> bool {
    matches!(tactic_name, "step" | "loop")
}

fn is_retired_internal_tactic_name(name: &str) -> bool {
    matches!(
        name,
        "execute_step"
            | "certified_statement_step"
            | "execute_rest"
            | "symbolic_execute"
            | "bounded_execute"
            | "apply_loop_summary"
            | "certified_loop_summary_step"
            | "certified_fact_transport"
            | "finish_certified_fact_transports"
            | "certified_path_assumption"
            | "certified_frame"
            | "exact_proposition_derivation"
            | "calculate"
            | "advance"
            | "conjunction"
    )
}

fn entry() -> Result<(), String> {
    entry_with(env::args().skip(1))
}

pub(crate) fn entry_with(arguments: impl IntoIterator<Item = String>) -> Result<(), String> {
    let raw_arguments = arguments.into_iter().collect::<Vec<_>>();
    if matches!(raw_arguments.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let arguments = parse_arguments(raw_arguments)?;
    let targets = profile_targets(&arguments.path)?;
    let mut profiles = Vec::new();
    for target in targets {
        profiles.push(profile_target(
            &target,
            arguments.thresholds,
            arguments.time_limit,
        )?);
    }
    print_profiles(
        &profiles,
        arguments.thresholds,
        arguments.time_limit,
        arguments.top_attribution_rows,
    );
    let failed = profiles
        .iter()
        .filter(|profile| profile.verification_failure.is_some())
        .count();
    if failed == 0 {
        Ok(())
    } else {
        Err(format!(
            "{failed} project(s) failed verification; partial profile printed above"
        ))
    }
}

fn parse_arguments(arguments: impl IntoIterator<Item = String>) -> Result<Arguments, String> {
    let mut path = None;
    let mut thresholds = Thresholds::default();
    let mut common_threshold = None;
    let mut class_threshold_supplied = false;
    let mut time_limit = DEFAULT_TIME_LIMIT;
    let mut top_attribution_rows = DEFAULT_TOP_ATTRIBUTION_ROWS;
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
            "--threshold" => {
                if common_threshold.is_some() {
                    return Err("`--threshold` may only be supplied once".to_string());
                }
                let source = arguments
                    .next()
                    .ok_or_else(|| format!("missing duration after `--threshold`\n{USAGE}"))?;
                common_threshold = Some(parse_duration(&source)?);
            }
            "--smart-threshold" => {
                let source = arguments.next().ok_or_else(|| {
                    format!("missing duration after `--smart-threshold`\n{USAGE}")
                })?;
                thresholds.smart = parse_duration(&source)?;
                class_threshold_supplied = true;
            }
            "--simple-threshold" => {
                let source = arguments.next().ok_or_else(|| {
                    format!("missing duration after `--simple-threshold`\n{USAGE}")
                })?;
                thresholds.simple = parse_duration(&source)?;
                class_threshold_supplied = true;
            }
            "--control-threshold" => {
                let source = arguments.next().ok_or_else(|| {
                    format!("missing duration after `--control-threshold`\n{USAGE}")
                })?;
                thresholds.control = parse_duration(&source)?;
                class_threshold_supplied = true;
            }
            "--time-limit" => {
                let source = arguments
                    .next()
                    .ok_or_else(|| format!("missing duration after `--time-limit`\n{USAGE}"))?;
                time_limit = parse_duration(&source)?;
            }
            "--top" => {
                let source = arguments
                    .next()
                    .ok_or_else(|| format!("missing count after `--top`\n{USAGE}"))?;
                top_attribution_rows = source
                    .parse::<usize>()
                    .ok()
                    .filter(|count| *count > 0)
                    .ok_or_else(|| "`--top` must be a positive integer".to_string())?;
            }
            _ if argument.starts_with('-') => {
                return Err(format!("unknown option `{argument}`\n{USAGE}"));
            }
            _ if path.is_none() => path = Some(PathBuf::from(argument)),
            _ => return Err(USAGE.to_string()),
        }
    }
    if common_threshold.is_some() && class_threshold_supplied {
        return Err("`--threshold` cannot be combined with class-specific thresholds".to_string());
    }
    if let Some(threshold) = common_threshold {
        thresholds = Thresholds {
            smart: threshold,
            simple: threshold,
            control: threshold,
        };
    }
    Ok(Arguments {
        path: path.ok_or_else(|| USAGE.to_string())?,
        thresholds,
        time_limit,
        top_attribution_rows,
    })
}

/// Chooses what to profile: a markdown test, a directory of them, or the
/// example projects under a directory.
///
/// Told apart by shape, not by a flag. A `.md` argument names one mdtest.
/// Otherwise example projects win, because they carry `README.md` files that
/// must not be mistaken for mdtests; only a directory with no Click sidecar
/// anywhere under it is read as a directory of mdtests.
fn profile_targets(path: &Path) -> Result<Vec<PathBuf>, String> {
    if looks_like_mdtest(path) {
        return find_mdtests(path);
    }
    if path
        .extension()
        .is_some_and(|extension| extension == "click")
    {
        return Ok(vec![path.to_path_buf()]);
    }
    match find_projects(path) {
        Ok(projects) => Ok(projects),
        Err(message) => {
            if path.is_dir() && !files_with_extension(path, "md")?.is_empty() {
                find_mdtests(path)
            } else {
                Err(message)
            }
        }
    }
}

fn profile_target(
    project: &Path,
    thresholds: Thresholds,
    time_limit: Duration,
) -> Result<ProjectProfile, String> {
    let started = Instant::now();
    let diagnostic_limits = instrumentation::TacticLimits {
        simple: time_limit,
        smart: time_limit,
        control: time_limit,
    };
    let (verification, events) = instrumentation::with_deadline(time_limit, || {
        instrumentation::with_tactic_limits(diagnostic_limits, || {
            instrumentation::collect(|| {
                if looks_like_mdtest(project) {
                    verify_mdtest(project)
                } else {
                    verify_project(project)
                }
            })
        })
    });
    let wall_elapsed = started.elapsed();
    let project_name = project
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_else(|| project.as_os_str().to_str().unwrap_or("example"))
        .to_string();
    let mut profile = profile_from_events(
        &project_name,
        &events,
        thresholds,
        wall_elapsed >= time_limit
            || verification
                .as_ref()
                .is_err_and(|message| message.contains("time limit exceeded")),
    )
    .map_err(|message| format!("while profiling `{}`: {message}", project.display()))?;
    finish_time_accounting(&mut profile, wall_elapsed);
    profile.verification_failure = verification.err();
    profile.work.smart_source_sites = count_smart_source_sites(&events)?;
    resolve_source_positions(&mut profile)?;
    Ok(profile)
}

fn count_smart_source_sites(events: &[VerificationEvent]) -> Result<usize, String> {
    let paths = events
        .iter()
        .filter_map(|event| match event {
            VerificationEvent::Source(path) => Some(path.clone()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    paths.into_iter().try_fold(0usize, |total, path| {
        let source = load_profiled_source(&path)?;
        let c_sources = source
            .c_sources
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        let sites =
            c0_smart_tactic_source_sites(&source.click_source, &c_sources).map_err(|error| {
                format!(
                    "could not inventory `{}`: {}",
                    path.display(),
                    error.message()
                )
            })?;
        Ok(total + sites.len())
    })
}

fn finish_time_accounting(profile: &mut ProjectProfile, wall_elapsed: Duration) {
    profile.accounting.wall_total = wall_elapsed;
    if profile.timed_out {
        let completed = profile.accounting.frontend
            + profile.accounting.environment
            + profile.accounting.tactic_total()
            + profile.accounting.certification
            + profile.accounting.verifier_core();
        profile.accounting.interrupted = wall_elapsed.saturating_sub(completed);
    }
}

/// The prefix every verifier timing line carries.
#[cfg(test)]
const TIMING_PREFIX: &str = "click timing: ";

/// Timing-line kinds the verifier emits that this profiler deliberately does
/// not consume. They are recognized so that a genuinely new or drifted kind
/// stands out instead of blending in with them.
///
/// Keep this list in sync with the `click timing:` emitters (grep for
/// `click timing:` under `src/`). Longer prefixes come first so `claim paths`
/// is not swallowed by `claim`.
///
/// Detailed claim events are consumed as work counts but not as elapsed-time
/// buckets: `contract claims` already owns their time, so adding it again
/// would double-count certification.
#[cfg(test)]
const IGNORED_TIMING_KINDS: &[&str] = &["contract entry resources"];

/// The two `click timing:` kinds that together make up the kernel
/// certification phase of one function.
#[cfg(test)]
const CERTIFICATION_TIMING_KINDS: &[&str] = &["contract execution", "contract claims"];

/// Where a verified function's wall-clock time went.
///
/// Tactic time is *exclusive*: a control container's own row excludes the
/// nested steps it ran, so the four class buckets and the unattributed
/// remainder add up to the total instead of overlapping. Structured start and
/// finish events identify nesting without a text protocol.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct TimeAccounting {
    simple: Duration,
    smart: Duration,
    control: Duration,
    certification: Duration,
    frontend: Duration,
    environment: Duration,
    /// Wall time left in the active operation when a project deadline
    /// interrupted an incomplete run. This is explicit rather than silently
    /// becoming process/driver residual.
    interrupted: Duration,
    /// Sum of the `click timing: function` lines. These cover function proof
    /// and certification work, but not the complete verifier invocation.
    total: Duration,
    /// Driver-observed duration of the direct verification run, including
    /// source I/O and verifier work. Synthetic parser tests leave this zero
    /// and use the function total as their denominator.
    wall_total: Duration,
}

impl TimeAccounting {
    fn add_tactic(&mut self, category: TacticCategory, elapsed: Duration) {
        match category {
            TacticCategory::Simple => self.simple += elapsed,
            TacticCategory::Smart => self.smart += elapsed,
            TacticCategory::Control => self.control += elapsed,
        }
    }

    fn tactic_total(self) -> Duration {
        self.simple + self.smart + self.control
    }

    /// Function time outside tactics and kernel certification. This is the
    /// verifier's orchestration work: proof-unit setup, bookkeeping, and
    /// other measured work inside the function boundary.
    fn verifier_core(self) -> Duration {
        self.total
            .saturating_sub(self.tactic_total() + self.certification)
    }

    /// Direct driver work outside the verifier's emitted phase boundaries,
    /// principally source reads and report setup.
    fn process_driver(self) -> Duration {
        self.wall_total.saturating_sub(
            self.frontend
                + self.environment
                + self.tactic_total()
                + self.certification
                + self.verifier_core()
                + self.interrupted,
        )
    }

    fn attributed(self) -> Duration {
        self.frontend
            + self.environment
            + self.tactic_total()
            + self.certification
            + self.verifier_core()
            + self.interrupted
            + self.process_driver()
    }

    /// Time in the best available denominator that no named, non-overlapping
    /// bucket claims. This should only remain nonzero if the timing protocol
    /// is internally inconsistent or a new event is not understood.
    fn unattributed(self) -> Duration {
        self.denominator().saturating_sub(self.attributed())
    }

    /// The denominator for shares: direct run wall time, falling
    /// back to the reported function total and then measured phases for unit
    /// tests and failures without a parent measurement.
    fn denominator(self) -> Duration {
        if !self.wall_total.is_zero() {
            self.wall_total
        } else if !self.total.is_zero() {
            self.total
        } else {
            self.attributed()
        }
    }

    fn share(self, part: Duration) -> f64 {
        let denominator = self.denominator();
        if denominator.is_zero() {
            return 0.0;
        }
        part.as_secs_f64() / denominator.as_secs_f64() * 100.0
    }

    fn materially_unattributed(self) -> bool {
        let unattributed = self.unattributed();
        unattributed >= MATERIAL_UNATTRIBUTED_TIME
            || (unattributed >= MATERIAL_UNATTRIBUTED_FLOOR
                && !self.denominator().is_zero()
                && self.share(unattributed) >= MATERIAL_UNATTRIBUTED_SHARE)
    }
}

/// One classified `click timing:` line.
#[derive(Clone, Debug)]
enum TimingEvent {
    /// The sidecar whose steps follow.
    Source(PathBuf),
    /// A tactic began; it stays active until its finish line arrives.
    Started(StepKey),
    /// A tactic finished, with its elapsed time.
    Finished(StepKey, Duration),
    /// Verification ultimately returned an error created inside this tactic.
    Failed(StepKey),
    /// One verified function's whole wall-clock time.
    FunctionTotal(String, Duration),
    /// One kernel certification phase of a function.
    Certification(String, Duration),
    /// Parsing C/Click source, lowering declarations, and selecting the
    /// verification dependency closure.
    Frontend(Duration),
    /// Constructing definition/function environments and verifying pure
    /// theorem dependencies before function proofs run.
    Environment(Duration),
    /// Number of certification paths prepared for one function.
    CertificationPaths { function: String, count: usize },
    /// One contract claim completed certification checking.
    ClaimCompleted {
        function: String,
        key: String,
        elapsed: Duration,
    },
    /// Structured snapshot captured at the cooperative deadline checkpoint,
    /// before scope guards close the active tactic or phase.
    Interrupted(InterruptedWork),
    /// A recognized kind the profiler does not consume.
    Ignored,
    /// A `click timing:` line matching no known kind. Counted and reported.
    #[cfg(test)]
    Unknown,
}

fn structured_step(tactic: &TacticEvent, source_path: &Path) -> Result<StepKey, String> {
    Ok(StepKey {
        source_path: source_path.to_path_buf(),
        claim: tactic.claim.clone(),
        tactic_index: tactic.tactic_index,
        source_index: tactic.source_index,
        tactic_name: (!is_retired_internal_tactic_name(&tactic.tactic_name))
            .then(|| tactic.tactic_name.clone())
            .ok_or_else(|| format!("retired internal tactic name `{}`", tactic.tactic_name))?,
        category: TacticCategory::parse(&tactic.class)
            .ok_or_else(|| format!("unknown tactic class `{}`", tactic.class))?,
        statement_index: tactic.statement_index,
        position: None,
    })
}

fn function_name_from_claim(claim: &str) -> &str {
    claim
        .split_once('.')
        .map_or(claim, |(function, _)| function)
}

fn add_attributed_tactic(
    attribution: &mut BTreeMap<String, FunctionAttribution>,
    key: &StepKey,
    elapsed: Duration,
) {
    let function = function_name_from_claim(&key.claim).to_string();
    let function_row = attribution.entry(function).or_default();
    function_row.buckets.add_tactic(key.category, elapsed);
    let claim_row = function_row.claims.entry(key.claim.clone()).or_default();
    claim_row.buckets.add_tactic(key.category, elapsed);
    if key.category == TacticCategory::Smart {
        claim_row
            .smart_sites
            .insert((key.source_path.clone(), key.source_index));
    }
}

fn finish_attribution(
    attribution: &mut BTreeMap<String, FunctionAttribution>,
    function_totals: &BTreeMap<String, Duration>,
    function_certification: &BTreeMap<String, Duration>,
) {
    for (function, row) in attribution {
        row.buckets.certification = function_certification
            .get(function)
            .copied()
            .unwrap_or_default();
        row.buckets.verifier_core = function_totals
            .get(function)
            .copied()
            .unwrap_or_default()
            .saturating_sub(
                row.buckets.simple
                    + row.buckets.smart
                    + row.buckets.control
                    + row.buckets.certification,
            );
        let claim_certification = row
            .claims
            .values()
            .map(|claim| claim.buckets.certification)
            .sum::<Duration>();
        let shared_certification = row
            .buckets
            .certification
            .saturating_sub(claim_certification);
        if !shared_certification.is_zero() || !row.buckets.verifier_core.is_zero() {
            let shared = row
                .claims
                .entry(format!("{function}::<shared verifier work>"))
                .or_default();
            shared.buckets.certification += shared_certification;
            shared.buckets.verifier_core += row.buckets.verifier_core;
        }
    }
}

fn profile_from_events(
    project: &str,
    events: &[VerificationEvent],
    thresholds: Thresholds,
    timed_out: bool,
) -> Result<ProjectProfile, String> {
    let mut classified = Vec::new();
    let mut source_path = PathBuf::new();
    for event in events {
        let event = match event {
            VerificationEvent::Source(path) => {
                source_path = path.clone();
                TimingEvent::Source(path.clone())
            }
            VerificationEvent::TacticStarted(tactic) => {
                TimingEvent::Started(structured_step(tactic, &source_path)?)
            }
            VerificationEvent::TacticFinished { tactic, elapsed } => {
                TimingEvent::Finished(structured_step(tactic, &source_path)?, *elapsed)
            }
            VerificationEvent::TacticFailed(tactic) => {
                TimingEvent::Failed(structured_step(tactic, &source_path)?)
            }
            VerificationEvent::FunctionFinished { name, elapsed } => {
                TimingEvent::FunctionTotal(name.clone(), *elapsed)
            }
            VerificationEvent::ContractExecutionFinished { function, elapsed }
            | VerificationEvent::ContractClaimsFinished { function, elapsed } => {
                TimingEvent::Certification(function.clone(), *elapsed)
            }
            VerificationEvent::PhaseFinished { name, elapsed } => match *name {
                "frontend" => TimingEvent::Frontend(*elapsed),
                "environment" => TimingEvent::Environment(*elapsed),
                _ => TimingEvent::Ignored,
            },
            VerificationEvent::ClaimPathsPrepared {
                function,
                count,
                elapsed: _,
            } => TimingEvent::CertificationPaths {
                function: function.clone(),
                count: *count,
            },
            VerificationEvent::ClaimFinished {
                function,
                key,
                elapsed,
            } => TimingEvent::ClaimCompleted {
                function: function.clone(),
                key: key.clone(),
                elapsed: *elapsed,
            },
            VerificationEvent::DeadlineExceeded(active) => TimingEvent::Interrupted(match active {
                ActiveVerificationWork::Tactic(tactic) => {
                    InterruptedWork::Tactic(structured_step(tactic, &source_path)?)
                }
                ActiveVerificationWork::Phase(name) => InterruptedWork::Phase(name),
                ActiveVerificationWork::Driver => InterruptedWork::Driver,
            }),
            VerificationEvent::PhaseStarted(_) | VerificationEvent::Diagnostic(_) => {
                TimingEvent::Ignored
            }
        };
        classified.push(event);
    }
    build_profile(project, classified, thresholds, timed_out)
}

fn build_profile(
    project: &str,
    events: impl IntoIterator<Item = TimingEvent>,
    thresholds: Thresholds,
    timed_out: bool,
) -> Result<ProjectProfile, String> {
    let mut slow_steps = Vec::new();
    let mut open: Vec<(StepKey, Duration)> = Vec::new();
    let mut accounting = TimeAccounting::default();
    let mut work = WorkMetrics::default();
    let mut attribution: BTreeMap<String, FunctionAttribution> = BTreeMap::new();
    let mut function_totals: BTreeMap<String, Duration> = BTreeMap::new();
    let mut function_certification: BTreeMap<String, Duration> = BTreeMap::new();
    let mut source_files = BTreeSet::new();
    let mut interrupted = None;
    for event in events {
        match event {
            TimingEvent::Source(path) => {
                source_files.insert(path);
            }
            TimingEvent::Started(key) => open.push((key, Duration::ZERO)),
            TimingEvent::Finished(key, elapsed) => {
                let nested = match open.iter().rposition(|(candidate, _)| candidate == &key) {
                    Some(index) => {
                        let (_, nested) = open.remove(index);
                        open.truncate(index);
                        nested
                    }
                    None => Duration::ZERO,
                };
                let exclusive = elapsed.saturating_sub(nested);
                accounting.add_tactic(key.category, exclusive);
                work.add_tactic(&key, exclusive);
                add_attributed_tactic(&mut attribution, &key, exclusive);
                if let Some((_, parent_nested)) = open.last_mut() {
                    *parent_nested += elapsed;
                }
                if exclusive >= thresholds.for_category(key.category) {
                    slow_steps.push(SlowStep {
                        key,
                        elapsed: exclusive,
                        failed: false,
                    });
                }
            }
            TimingEvent::Failed(key) => {
                if let Some(step) = slow_steps.iter_mut().rev().find(|step| step.key == key) {
                    step.failed = true;
                }
                work.failed_tactics.push(key);
            }
            TimingEvent::FunctionTotal(function, elapsed) => {
                accounting.total += elapsed;
                work.functions += 1;
                *function_totals.entry(function.clone()).or_default() += elapsed;
                attribution.entry(function).or_default();
            }
            TimingEvent::Certification(function, elapsed) => {
                accounting.certification += elapsed;
                *function_certification.entry(function.clone()).or_default() += elapsed;
                attribution.entry(function).or_default();
            }
            TimingEvent::Frontend(elapsed) => accounting.frontend += elapsed,
            TimingEvent::Environment(elapsed) => accounting.environment += elapsed,
            TimingEvent::CertificationPaths { function, count } => {
                work.certification_paths += count;
                attribution.entry(function).or_default();
            }
            TimingEvent::ClaimCompleted {
                function,
                key,
                elapsed,
            } => {
                work.claims += 1;
                attribution
                    .entry(function.clone())
                    .or_default()
                    .claims
                    .entry(format!("{function}::{key}"))
                    .or_default()
                    .buckets
                    .certification += elapsed;
            }
            TimingEvent::Interrupted(work) => interrupted = Some(work),
            TimingEvent::Ignored => {}
            #[cfg(test)]
            TimingEvent::Unknown => {}
        }
    }
    finish_attribution(&mut attribution, &function_totals, &function_certification);
    work.source_files = source_files.len();
    let active = open.into_iter().map(|(key, _)| key).collect::<Vec<_>>();
    if timed_out && interrupted.is_none() {
        interrupted = active
            .last()
            .cloned()
            .map(InterruptedWork::Tactic)
            .or(Some(InterruptedWork::Driver));
    }
    Ok(ProjectProfile {
        project: project.to_string(),
        slow_steps,
        active,
        interrupted,
        timed_out,
        verification_failure: None,
        unknown_timing: BTreeMap::new(),
        accounting,
        work,
        attribution,
        unresolved_positions: BTreeMap::new(),
    })
}

#[cfg(test)]
fn parse_profile(
    project: &str,
    output: &str,
    thresholds: Thresholds,
    timed_out: bool,
) -> Result<ProjectProfile, String> {
    let mut slow_steps = Vec::new();
    // Open tactics, innermost last, each carrying the time already spent in
    // the nested steps it started. Popping one turns its reported elapsed
    // time into exclusive time.
    let mut open: Vec<(StepKey, Duration)> = Vec::new();
    let mut accounting = TimeAccounting::default();
    let mut work = WorkMetrics::default();
    let mut attribution: BTreeMap<String, FunctionAttribution> = BTreeMap::new();
    let mut function_totals: BTreeMap<String, Duration> = BTreeMap::new();
    let mut function_certification: BTreeMap<String, Duration> = BTreeMap::new();
    let mut source_files = BTreeSet::new();
    let mut interrupted = None;
    let mut unknown_timing: BTreeMap<String, UnknownTiming> = BTreeMap::new();
    let mut source_path = PathBuf::new();
    for line in output.lines() {
        let line = line.trim_end();
        if !line.starts_with(TIMING_PREFIX) {
            continue;
        }
        match classify_timing_line(line, &source_path)? {
            TimingEvent::Source(path) => {
                source_files.insert(path.clone());
                source_path = path;
            }
            TimingEvent::Started(key) => open.push((key, Duration::ZERO)),
            TimingEvent::Finished(key, elapsed) => {
                let nested = match open.iter().rposition(|(candidate, _)| candidate == &key) {
                    Some(index) => {
                        let (_, nested) = open.remove(index);
                        // Anything opened inside it that never reported a
                        // finish cannot nest in a later step either.
                        open.truncate(index);
                        nested
                    }
                    None => Duration::ZERO,
                };
                let exclusive = elapsed.saturating_sub(nested);
                accounting.add_tactic(key.category, exclusive);
                work.add_tactic(&key, exclusive);
                add_attributed_tactic(&mut attribution, &key, exclusive);
                if let Some((_, parent_nested)) = open.last_mut() {
                    *parent_nested += elapsed;
                }
                if exclusive >= thresholds.for_category(key.category) {
                    slow_steps.push(SlowStep {
                        key,
                        elapsed: exclusive,
                        failed: false,
                    });
                }
            }
            TimingEvent::Failed(key) => {
                if let Some(step) = slow_steps.iter_mut().rev().find(|step| step.key == key) {
                    step.failed = true;
                }
                work.failed_tactics.push(key);
            }
            TimingEvent::FunctionTotal(function, elapsed) => {
                accounting.total += elapsed;
                work.functions += 1;
                *function_totals.entry(function.clone()).or_default() += elapsed;
                attribution.entry(function).or_default();
            }
            TimingEvent::Certification(function, elapsed) => {
                accounting.certification += elapsed;
                *function_certification.entry(function.clone()).or_default() += elapsed;
                attribution.entry(function).or_default();
            }
            TimingEvent::Frontend(elapsed) => accounting.frontend += elapsed,
            TimingEvent::Environment(elapsed) => accounting.environment += elapsed,
            TimingEvent::CertificationPaths { function, count } => {
                work.certification_paths += count;
                attribution.entry(function).or_default();
            }
            TimingEvent::ClaimCompleted {
                function,
                key,
                elapsed,
            } => {
                work.claims += 1;
                attribution
                    .entry(function.clone())
                    .or_default()
                    .claims
                    .entry(format!("{function}::{key}"))
                    .or_default()
                    .buckets
                    .certification += elapsed;
            }
            TimingEvent::Interrupted(work) => interrupted = Some(work),
            TimingEvent::Ignored => {}
            TimingEvent::Unknown => {
                let kind = unknown_timing_kind(line);
                unknown_timing
                    .entry(kind)
                    .and_modify(|seen| seen.count += 1)
                    .or_insert_with(|| UnknownTiming {
                        count: 1,
                        example: line.to_string(),
                    });
            }
        }
    }
    finish_attribution(&mut attribution, &function_totals, &function_certification);
    work.source_files = source_files.len();
    let active = open.into_iter().map(|(key, _)| key).collect::<Vec<_>>();
    if timed_out && interrupted.is_none() {
        interrupted = active
            .last()
            .cloned()
            .map(InterruptedWork::Tactic)
            .or(Some(InterruptedWork::Driver));
    }
    Ok(ProjectProfile {
        project: project.to_string(),
        slow_steps,
        active,
        interrupted,
        timed_out,
        verification_failure: None,
        unknown_timing,
        accounting,
        work,
        attribution,
        unresolved_positions: BTreeMap::new(),
    })
}

/// Classifies one line that already begins with [`TIMING_PREFIX`].
///
/// A line whose kind this profiler depends on but whose structure does not
/// parse is a hard error: the whole report would otherwise be a false green,
/// showing no slow steps because it silently understood none of them.
#[cfg(test)]
fn classify_timing_line(line: &str, source_path: &Path) -> Result<TimingEvent, String> {
    let body = line
        .strip_prefix(TIMING_PREFIX)
        .expect("callers only classify lines carrying the timing prefix")
        .trim_start();
    if let Some(path) = strip_kind(body, "source") {
        if path.is_empty() {
            return Err(drift_message(line));
        }
        return Ok(TimingEvent::Source(PathBuf::from(path.trim_end())));
    }
    if let Some(rest) = strip_kind(body, "started tactic") {
        return parse_step_key(rest, source_path)
            .map(TimingEvent::Started)
            .ok_or_else(|| drift_message(line));
    }
    if let Some(rest) = strip_kind(body, "failed tactic") {
        return parse_step_key(rest, source_path)
            .map(TimingEvent::Failed)
            .ok_or_else(|| drift_message(line));
    }
    if let Some(rest) = strip_kind(body, "tactic") {
        let (rest, elapsed) = split_trailing_seconds(rest).ok_or_else(|| drift_message(line))?;
        let key = parse_step_key(rest, source_path).ok_or_else(|| drift_message(line))?;
        return Ok(TimingEvent::Finished(key, elapsed));
    }
    if let Some(rest) = strip_kind(body, "function") {
        let (name, elapsed) = split_trailing_seconds(rest).ok_or_else(|| drift_message(line))?;
        return Ok(TimingEvent::FunctionTotal(name.trim().to_string(), elapsed));
    }
    if let Some(rest) = strip_kind(body, "phase") {
        let (name, elapsed) = split_trailing_seconds(rest).ok_or_else(|| drift_message(line))?;
        return match name.trim() {
            "frontend" => Ok(TimingEvent::Frontend(elapsed)),
            "environment" => Ok(TimingEvent::Environment(elapsed)),
            _ => Ok(TimingEvent::Unknown),
        };
    }
    for kind in CERTIFICATION_TIMING_KINDS {
        if let Some(rest) = strip_kind(body, kind) {
            let (function, elapsed) =
                split_trailing_seconds(rest).ok_or_else(|| drift_message(line))?;
            return Ok(TimingEvent::Certification(
                function.trim().to_string(),
                elapsed,
            ));
        }
    }
    if let Some(rest) = strip_kind(body, "claim paths") {
        let (head, _elapsed) = split_trailing_seconds(rest).ok_or_else(|| drift_message(line))?;
        let (function, prepared) = head
            .rsplit_once(" prepared ")
            .ok_or_else(|| drift_message(line))?;
        let count = prepared
            .strip_suffix(" in")
            .and_then(|count| count.parse::<usize>().ok())
            .ok_or_else(|| drift_message(line))?;
        return Ok(TimingEvent::CertificationPaths {
            function: function.to_string(),
            count,
        });
    }
    if let Some(rest) = strip_kind(body, "claim") {
        let (head, elapsed) = split_trailing_seconds(rest).ok_or_else(|| drift_message(line))?;
        let (function, key) = head
            .split_once(char::is_whitespace)
            .ok_or_else(|| drift_message(line))?;
        return Ok(TimingEvent::ClaimCompleted {
            function: function.to_string(),
            key: key.trim().to_string(),
            elapsed,
        });
    }
    if IGNORED_TIMING_KINDS
        .iter()
        .any(|kind| strip_kind(body, kind).is_some())
    {
        return Ok(TimingEvent::Ignored);
    }
    Ok(TimingEvent::Unknown)
}

/// Splits a trailing `<seconds>s` field off a timing line body, returning the
/// text before it and the parsed duration.
#[cfg(test)]
fn split_trailing_seconds(rest: &str) -> Option<(&str, Duration)> {
    let (head, elapsed) = rest.trim_end().rsplit_once(char::is_whitespace)?;
    let elapsed = elapsed
        .strip_suffix('s')?
        .parse::<f64>()
        .ok()
        .filter(|seconds| seconds.is_finite() && *seconds >= 0.0)?;
    Some((head, Duration::from_secs_f64(elapsed)))
}

/// Strips a kind keyword, requiring it to end at a word boundary so `tactic`
/// never matches a future `tactical` kind, and returns the rest of the line.
#[cfg(test)]
fn strip_kind<'a>(body: &'a str, kind: &str) -> Option<&'a str> {
    let rest = body.strip_prefix(kind)?;
    if rest.is_empty() || rest.starts_with(char::is_whitespace) {
        Some(rest.trim_start())
    } else {
        None
    }
}

#[cfg(test)]
fn drift_message(line: &str) -> String {
    format!(
        "the verifier timing format this profile depends on has drifted; \
         click-profile could not parse:\n  {line}\n\
         Update the `click timing:` parser in src/bin/click-profile.rs to match \
         the emitter; leaving it stale silently reports no slow steps."
    )
}

/// Groups unrecognized timing lines by the first word after the prefix, so a
/// thousand copies of one new kind collapse to a single counted row.
#[cfg(test)]
fn unknown_timing_kind(line: &str) -> String {
    line.strip_prefix(TIMING_PREFIX)
        .unwrap_or(line)
        .split_whitespace()
        .next()
        .unwrap_or("(empty)")
        .to_string()
}

/// Parses the nine fields shared by started and finished tactic lines:
/// `CLAIM INDEX NAME class CLASS statement INDEX source INDEX`.
#[cfg(test)]
fn parse_step_key(rest: &str, source_path: &Path) -> Option<StepKey> {
    let fields = rest.split_whitespace().collect::<Vec<_>>();
    if fields.len() != 9
        || fields[3] != "class"
        || fields[5] != "statement"
        || fields[7] != "source"
    {
        return None;
    }
    Some(StepKey {
        source_path: source_path.to_path_buf(),
        claim: fields[0].to_string(),
        tactic_index: fields[1].parse().ok()?,
        tactic_name: (!is_retired_internal_tactic_name(fields[2]))
            .then(|| fields[2].to_string())?,
        category: TacticCategory::parse(fields[4])?,
        statement_index: fields[6].parse().ok()?,
        source_index: fields[8].parse().ok()?,
        position: None,
    })
}

/// The Click sidecar behind a `click timing: source` path, plus everything
/// needed to turn a position inside it into a position in that file.
struct ProfiledSource {
    click_source: String,
    c_sources: Vec<(String, String)>,
    /// Added to a one-based line inside the sidecar. Zero for a `.click`
    /// file; the offset of the ```click block for an mdtest, so reported
    /// locations point into the markdown the user actually edits.
    line_offset: usize,
}

fn load_profiled_source(path: &Path) -> Result<ProfiledSource, String> {
    if looks_like_mdtest(path) {
        let mdtest = read_mdtest(path)?;
        let click_source = mdtest
            .click_source
            .ok_or_else(|| format!("mdtest `{}` has no ```click block", path.display()))?;
        return Ok(ProfiledSource {
            click_source,
            c_sources: mdtest.c_sources,
            line_offset: mdtest.click_start_line.saturating_sub(1),
        });
    }
    let click_source = fs::read_to_string(path)
        .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
    let c_sources = read_verifying_sources(path, &click_source)?;
    Ok(ProfiledSource {
        click_source,
        c_sources,
        line_offset: 0,
    })
}

/// Resolves each reported step to a `PATH:LINE:COLUMN` location.
///
/// A step whose location cannot be resolved is still reported, without one.
/// Loop-phase certificates the verifier plans itself index tactics that the
/// surface proof never wrote, so demanding a location for every timed step
/// would make the slowest proofs — exactly the ones worth profiling — the
/// only ones that cannot be profiled.
fn resolve_source_positions(profile: &mut ProjectProfile) -> Result<(), String> {
    let mut sources: BTreeMap<PathBuf, ProfiledSource> = BTreeMap::new();
    let mut unresolved: BTreeMap<String, usize> = BTreeMap::new();
    let interrupted_key = match profile.interrupted.as_mut() {
        Some(InterruptedWork::Tactic(key)) => Some(key),
        Some(InterruptedWork::Phase(_) | InterruptedWork::Driver) | None => None,
    };
    for key in profile
        .slow_steps
        .iter_mut()
        .map(|step| &mut step.key)
        .chain(profile.active.iter_mut())
        .chain(interrupted_key)
    {
        if key.source_path.as_os_str().is_empty() {
            return Err("timing event had no Click source path".to_string());
        }
        let source = match sources.entry(key.source_path.clone()) {
            std::collections::btree_map::Entry::Occupied(entry) => entry.into_mut(),
            std::collections::btree_map::Entry::Vacant(entry) => {
                entry.insert(load_profiled_source(key.source_path.as_path())?)
            }
        };
        let c_sources = source
            .c_sources
            .iter()
            .map(|(name, text)| (name.as_str(), text.as_str()))
            .collect::<Vec<_>>();
        match c0_tactic_source_position(
            &source.click_source,
            &c_sources,
            &key.claim,
            key.source_index,
        ) {
            Ok(position) => {
                key.position = Some(SourcePosition {
                    line: position.line + source.line_offset,
                    column: position.column,
                });
            }
            Err(error) => {
                *unresolved.entry(error.message().to_string()).or_default() += 1;
            }
        }
    }
    profile.unresolved_positions = unresolved;
    Ok(())
}

#[path = "click-profile/rendering.rs"]
mod rendering;

use rendering::print_profiles;
#[cfg(test)]
use rendering::{render_expansion_command, render_profiles, render_profiles_with_top};
/// Verifies one markdown test directly, from the same embedded
/// blocks the mdtests gate extracts.
///
/// An mdtest that declares `fail:` is profiled to its expected failure, so a
/// known-broken test can still be timed; anything else is a real failure.
fn verify_mdtest(path: &Path) -> Result<(), String> {
    let mdtest = read_mdtest(path)?;
    let click_source = mdtest
        .click_source
        .as_deref()
        .ok_or_else(|| format!("mdtest `{}` has no ```click block", path.display()))?;
    let c_sources = source_refs(&mdtest.c_sources);
    if instrumentation::enabled() {
        instrumentation::emit(VerificationEvent::Source(path.to_path_buf()));
    }
    let result = verify_c0_sources(click_source, &c_sources);
    match (mdtest.expectation.as_ref(), result) {
        (Some(MdTestExpectation::FailContains(expected)), Err(error)) => {
            if error.message().contains(expected) {
                Ok(())
            } else {
                Err(format!(
                    "mdtest `{}` expected a failure containing `{expected}`, got: {}",
                    path.display(),
                    error.message()
                ))
            }
        }
        (Some(MdTestExpectation::FailContains(expected)), Ok(_)) => Err(format!(
            "mdtest `{}` expected a failure containing `{expected}`, but passed",
            path.display()
        )),
        (_, Ok(_)) => Ok(()),
        (_, Err(error)) => Err(format!(
            "mdtest `{}` failed: {}",
            path.display(),
            error.message()
        )),
    }
}

fn verify_project(project: &Path) -> Result<(), String> {
    let mut click_paths = if project.is_file()
        && project
            .extension()
            .is_some_and(|extension| extension == "click")
    {
        vec![project.to_path_buf()]
    } else {
        files_with_extension(project, "click")?
    };
    click_paths.sort();
    if click_paths.is_empty() {
        return Err(format!(
            "example project `{}` has no Click sidecar",
            project.display()
        ));
    }
    for click_path in click_paths {
        let click_source = fs::read_to_string(&click_path)
            .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
        let c_sources = read_verifying_sources(&click_path, &click_source)?;
        if instrumentation::enabled() {
            instrumentation::emit(VerificationEvent::Source(click_path.clone()));
        }
        verify_c0_sources(&click_source, &source_refs(&c_sources)).map_err(|error| {
            format!(
                "example sidecar `{}` failed: {}",
                click_path.display(),
                error.message()
            )
        })?;
    }
    Ok(())
}

#[cfg(test)]
#[path = "click-profile/tests.rs"]
mod tests;
