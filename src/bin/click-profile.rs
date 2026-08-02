use std::collections::{BTreeMap, BTreeSet};
use std::env;
use std::fmt::Write as _;
use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;
use std::time::Duration;

use click::cli::{
    BoundedOutput, MdTestExpectation, files_with_extension, find_mdtests, find_projects,
    format_duration, format_fractional_duration, looks_like_mdtest, parse_duration, read_mdtest,
    run_bounded, source_refs,
};
use click::lang::click::{SourcePosition, c0_tactic_source_position, verify_c0_sources};

const DEFAULT_SMART_THRESHOLD: Duration = Duration::from_secs(2);
const DEFAULT_SIMPLE_THRESHOLD: Duration = Duration::from_millis(500);
const DEFAULT_CONTROL_THRESHOLD: Duration = Duration::from_secs(2);
const DEFAULT_TIME_LIMIT: Duration = Duration::from_secs(30);
const EXPANSION_TIME_LIMIT: Duration = Duration::from_secs(60);
const MATERIAL_UNATTRIBUTED_TIME: Duration = Duration::from_millis(250);
const MATERIAL_UNATTRIBUTED_SHARE: f64 = 10.0;
const SIMPLE_AVERAGE_LIMIT: Duration = Duration::from_millis(50);
const CERTIFICATION_PER_CLAIM_LIMIT: Duration = Duration::from_millis(250);
const CERTIFICATION_PER_PATH_LIMIT: Duration = Duration::from_secs(1);
const SETUP_PER_FILE_LIMIT: Duration = Duration::from_millis(250);
const VOLUME_REPORT_THRESHOLD: Duration = Duration::from_secs(1);

const USAGE: &str = "\
usage: click-profile [OPTIONS] <example-project|examples-directory|mdtest.md|mdtests-directory>

An mdtest is profiled from its embedded ```c and ```click blocks, using the
same extraction the mdtests gate uses. Quarantine does not apply: any mdtest
can be profiled, which is the point when diagnosing a slow one.

defaults:
  --smart-threshold 2s      smart tactics are expansion candidates
  --simple-threshold 500ms  slow simple tactics are verifier bugs; do not expand them
  --control-threshold 2s    inspect slow control-flow containers and their nested steps
  --time-limit 30s          wall-clock limit per project

options:
  --smart-threshold <DURATION>
  --simple-threshold <DURATION>
  --control-threshold <DURATION>
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
    child: bool,
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
            smart: DEFAULT_SMART_THRESHOLD,
            simple: DEFAULT_SIMPLE_THRESHOLD,
            control: DEFAULT_CONTROL_THRESHOLD,
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
    timed_out: bool,
    verification_failure: Option<String>,
    /// `click timing:` lines this profiler did not recognize, keyed by the
    /// word after the prefix, with a count and one verbatim example. A
    /// profile that silently drops timing lines is a false green, so these
    /// are reported instead of ignored.
    unknown_timing: BTreeMap<String, UnknownTiming>,
    accounting: TimeAccounting,
    work: WorkMetrics,
    /// Reasons a reported step's source position could not be resolved,
    /// counted. Auto-planned loop-phase certificates carry synthesized tactic
    /// indices that no surface proof has, so those steps are reported with
    /// their claim and no location rather than sinking the whole profile.
    unresolved_positions: BTreeMap<String, usize>,
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
    tactics: BTreeMap<(TacticCategory, String), OperationStats>,
    c_transitions: OperationStats,
    failed_tactics: Vec<StepKey>,
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
    matches!(
        tactic_name,
        "step"
            | "certified_statement_step"
            | "apply_loop_summary"
            | "certified_loop_summary_step"
    )
}

fn entry() -> Result<(), String> {
    let raw_arguments = env::args().skip(1).collect::<Vec<_>>();
    if matches!(raw_arguments.as_slice(), [argument] if argument == "--help" || argument == "-h") {
        println!("{USAGE}");
        return Ok(());
    }
    let arguments = parse_arguments(raw_arguments)?;
    if arguments.child {
        return if looks_like_mdtest(&arguments.path) {
            verify_mdtest(&arguments.path)
        } else {
            verify_project(&arguments.path)
        };
    }

    let targets = profile_targets(&arguments.path)?;
    let mut profiles = Vec::new();
    for target in targets {
        profiles.push(profile_target(
            &target,
            arguments.thresholds,
            arguments.time_limit,
        )?);
    }
    print_profiles(&profiles, arguments.thresholds, arguments.time_limit);
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
    let mut child = false;
    let mut arguments = arguments.into_iter();
    while let Some(argument) = arguments.next() {
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
            "--child" => child = true,
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
        child,
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
    if path.is_file() && path.extension().is_some_and(|extension| extension == "click") {
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
    let executable = env::current_exe()
        .map_err(|error| format!("failed to locate click-profile executable: {error}"))?;
    let mut command = Command::new(executable);
    command
        .arg("--child")
        .arg(project)
        .env("CLICK_TIMINGS", "1")
        .env("CLICK_TIMING_STARTS", "1")
        // Prover recursion follows term structure, which nests deeper than
        // the default stack on the snapshot-heavy proofs worth profiling.
        .env("RUST_MIN_STACK", "67108864");
    let label = format!("profiler for `{}`", project.display());
    let (status, stdout, stderr, wall_elapsed) = match run_bounded(command, time_limit, &label)? {
        BoundedOutput::Completed(output) => (
            Some(output.status),
            output.stdout,
            output.stderr,
            output.elapsed,
        ),
        BoundedOutput::TimedOut {
            stdout,
            stderr,
            elapsed,
        } => (None, stdout, stderr, elapsed),
    };
    let project_name = project
        .file_name()
        .and_then(|name| name.to_str())
        .unwrap_or_else(|| project.as_os_str().to_str().unwrap_or("example"))
        .to_string();
    let stderr = String::from_utf8_lossy(&stderr);
    let mut profile = parse_profile(&project_name, &stderr, thresholds, status.is_none())
        .map_err(|message| format!("while profiling `{}`: {message}", project.display()))?;
    profile.accounting.wall_total = wall_elapsed;
    if status.is_some_and(|status| !status.success()) {
        profile.verification_failure = Some(extract_verification_failure(
            &String::from_utf8_lossy(&stdout),
            &stderr,
            status.expect("failed status should be present"),
        ));
    }
    resolve_source_positions(&mut profile)?;
    Ok(profile)
}

fn extract_verification_failure(
    stdout: &str,
    stderr: &str,
    status: std::process::ExitStatus,
) -> String {
    let diagnostics = stderr
        .lines()
        .filter(|line| !line.starts_with("click timing:"))
        .collect::<Vec<_>>()
        .join("\n");
    let diagnostics = diagnostics
        .trim()
        .strip_prefix("click-profile: ")
        .unwrap_or(diagnostics.trim());
    if !diagnostics.is_empty() {
        diagnostics.to_string()
    } else if !stdout.trim().is_empty() {
        stdout.trim().to_string()
    } else {
        format!("profiler child exited with {status}")
    }
}

/// The prefix every verifier timing line carries.
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
const IGNORED_TIMING_KINDS: &[&str] = &["contract entry resources"];

/// The two `click timing:` kinds that together make up the kernel
/// certification phase of one function.
const CERTIFICATION_TIMING_KINDS: &[&str] = &["contract execution", "contract claims"];

/// Where a verified function's wall-clock time went.
///
/// Tactic time is *exclusive*: a control container's own row excludes the
/// nested steps it ran, so the four class buckets and the unattributed
/// remainder add up to the total instead of overlapping. Exclusive time needs
/// the `started tactic` lines to know what nests inside what, which is why
/// the profiler always runs its child with `CLICK_TIMING_STARTS`.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
struct TimeAccounting {
    simple: Duration,
    smart: Duration,
    control: Duration,
    certification: Duration,
    frontend: Duration,
    environment: Duration,
    /// Sum of the `click timing: function` lines. These cover function proof
    /// and certification work, but not the complete verifier invocation.
    total: Duration,
    /// Parent-observed duration of the bounded child, including process start,
    /// source I/O, and verifier work. Synthetic parser tests leave this zero
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

    fn attributed(self) -> Duration {
        self.frontend
            + self.environment
            + self.simple
            + self.smart
            + self.control
            + self.certification
    }

    /// Time in the best available denominator that no non-overlapping phase or
    /// tactic timing claims. A large share means the profile is incomplete.
    fn unattributed(self) -> Duration {
        self.denominator().saturating_sub(self.attributed())
    }

    /// The denominator for shares: parent-observed child wall time, falling
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
            || (!self.denominator().is_zero()
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
    FunctionTotal(Duration),
    /// One kernel certification phase of a function.
    Certification(Duration),
    /// Parsing C/Click source, lowering declarations, and selecting the
    /// verification dependency closure.
    Frontend(Duration),
    /// Constructing definition/function environments and verifying pure
    /// theorem dependencies before function proofs run.
    Environment(Duration),
    /// Number of certification paths prepared for one function.
    CertificationPaths(usize),
    /// One contract claim completed certification checking.
    ClaimCompleted,
    /// A recognized kind the profiler does not consume.
    Ignored,
    /// A `click timing:` line matching no known kind. Counted and reported.
    Unknown,
}

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
    let mut source_files = BTreeSet::new();
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
            TimingEvent::FunctionTotal(elapsed) => {
                accounting.total += elapsed;
                work.functions += 1;
            }
            TimingEvent::Certification(elapsed) => accounting.certification += elapsed,
            TimingEvent::Frontend(elapsed) => accounting.frontend += elapsed,
            TimingEvent::Environment(elapsed) => accounting.environment += elapsed,
            TimingEvent::CertificationPaths(count) => work.certification_paths += count,
            TimingEvent::ClaimCompleted => work.claims += 1,
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
    work.source_files = source_files.len();
    Ok(ProjectProfile {
        project: project.to_string(),
        slow_steps,
        active: open.into_iter().map(|(key, _)| key).collect(),
        timed_out,
        verification_failure: None,
        unknown_timing,
        accounting,
        work,
        unresolved_positions: BTreeMap::new(),
    })
}

/// Classifies one line that already begins with [`TIMING_PREFIX`].
///
/// A line whose kind this profiler depends on but whose structure does not
/// parse is a hard error: the whole report would otherwise be a false green,
/// showing no slow steps because it silently understood none of them.
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
        let (_, elapsed) = split_trailing_seconds(rest).ok_or_else(|| drift_message(line))?;
        return Ok(TimingEvent::FunctionTotal(elapsed));
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
            let (_, elapsed) = split_trailing_seconds(rest).ok_or_else(|| drift_message(line))?;
            return Ok(TimingEvent::Certification(elapsed));
        }
    }
    if let Some(rest) = strip_kind(body, "claim paths") {
        let (head, _) = split_trailing_seconds(rest).ok_or_else(|| drift_message(line))?;
        let (_, prepared) = head
            .rsplit_once(" prepared ")
            .ok_or_else(|| drift_message(line))?;
        let count = prepared
            .strip_suffix(" in")
            .and_then(|count| count.parse::<usize>().ok())
            .ok_or_else(|| drift_message(line))?;
        return Ok(TimingEvent::CertificationPaths(count));
    }
    if let Some(rest) = strip_kind(body, "claim") {
        split_trailing_seconds(rest).ok_or_else(|| drift_message(line))?;
        return Ok(TimingEvent::ClaimCompleted);
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
fn strip_kind<'a>(body: &'a str, kind: &str) -> Option<&'a str> {
    let rest = body.strip_prefix(kind)?;
    if rest.is_empty() || rest.starts_with(char::is_whitespace) {
        Some(rest.trim_start())
    } else {
        None
    }
}

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
        tactic_name: fields[2].to_string(),
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
    let parent = path.parent().unwrap_or_else(|| Path::new("."));
    let c_sources = files_with_extension(parent, "c")?
        .into_iter()
        .map(|path| {
            let name = path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or_else(|| format!("invalid UTF-8 path `{}`", path.display()))?
                .to_string();
            let source = fs::read_to_string(&path)
                .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
            Ok((name, source))
        })
        .collect::<Result<Vec<_>, String>>()?;
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
    for key in profile
        .slow_steps
        .iter_mut()
        .map(|step| &mut step.key)
        .chain(profile.active.iter_mut())
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

fn print_profiles(profiles: &[ProjectProfile], thresholds: Thresholds, time_limit: Duration) {
    print!("{}", render_profiles(profiles, thresholds, time_limit));
}

fn render_profiles(
    profiles: &[ProjectProfile],
    thresholds: Thresholds,
    time_limit: Duration,
) -> String {
    let mut slow_steps = profiles
        .iter()
        .flat_map(|profile| profile.slow_steps.iter())
        .collect::<Vec<_>>();
    slow_steps.sort_by(|left, right| right.elapsed.cmp(&left.elapsed));

    let mut output = String::new();
    writeln!(
        output,
        "Click proof profile (smart >= {}, simple >= {}, control >= {}; project limit {})",
        format_fractional_duration(thresholds.smart),
        format_fractional_duration(thresholds.simple),
        format_fractional_duration(thresholds.control),
        format_fractional_duration(time_limit),
    )
    .expect("writing a String cannot fail");
    writeln!(
        output,
        "Classification is emitted by the verifier; do not infer it from a tactic's name."
    )
    .expect("writing a String cannot fail");

    render_category(
        &mut output,
        &slow_steps,
        TacticCategory::Simple,
        "SIMPLE — FIX THE ENGINE; DO NOT EXPAND",
        "A slow simple tactic is deterministic certificate replay. Reduce its verifier path and fix that bottleneck before expanding more smart tactics.",
        thresholds,
        time_limit,
    );
    render_category(
        &mut output,
        &slow_steps,
        TacticCategory::Smart,
        "SMART — EXPAND SUCCESSES; REDUCE FAILURES",
        "Expand a successful hotspot and compare its rewritten profile. A failed smart search has no certificate and is a Click bug to reduce.",
        thresholds,
        time_limit,
    );
    render_category(
        &mut output,
        &slow_steps,
        TacticCategory::Control,
        "CONTROL — INSPECT NESTED STEPS",
        "This is a proof container. Use its nested SMART/SIMPLE timings; do not optimize or expand it based on the container row alone.",
        thresholds,
        time_limit,
    );

    render_accounting(&mut output, profiles);
    render_work_metrics(&mut output, profiles);
    render_diagnoses(&mut output, profiles);

    let failed = profiles
        .iter()
        .filter_map(|profile| {
            profile
                .verification_failure
                .as_deref()
                .map(|failure| (profile, failure))
        })
        .collect::<Vec<_>>();
    if !failed.is_empty() {
        writeln!(output, "\nVERIFICATION FAILURES").expect("writing a String cannot fail");
    }
    for (profile, failure) in failed {
        writeln!(output, "  {}:", profile.project).expect("writing a String cannot fail");
        for line in failure.lines() {
            writeln!(output, "    {line}").expect("writing a String cannot fail");
        }
    }

    let timed_out = profiles
        .iter()
        .filter(|profile| profile.timed_out)
        .collect::<Vec<_>>();
    if !timed_out.is_empty() {
        writeln!(output, "\nTIMEOUTS").expect("writing a String cannot fail");
    }
    for profile in timed_out {
        writeln!(
            output,
            "  timed out: {} after {}",
            profile.project,
            format_fractional_duration(time_limit)
        )
        .expect("writing a String cannot fail");
        for key in &profile.active {
            writeln!(
                output,
                "    [{}] {}  {}  {}  statement {}",
                key.category.label(),
                step_location(key),
                key.claim,
                key.tactic_name,
                key.statement_index
            )
            .expect("writing a String cannot fail");
            if key.category == TacticCategory::Smart {
                writeln!(
                    output,
                    "              interrupted before a certificate was produced; reduce the search in Click"
                )
                .expect("writing a String cannot fail");
            }
        }
    }

    let has_simple_problem = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Simple)
        || profiles.iter().any(|profile| {
            (profile.timed_out
                && profile
                    .active
                    .iter()
                    .any(|key| key.category == TacticCategory::Simple))
                || {
                    let simple = profile.work.category(TacticCategory::Simple);
                    simple.count > 0 && simple.average() > SIMPLE_AVERAGE_LIMIT
                }
        });
    let has_smart_candidate = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Smart && !step.failed);
    let has_smart_failure = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Smart && step.failed)
        || profiles.iter().any(|profile| {
            profile.timed_out
                && profile
                    .active
                    .iter()
                    .any(|key| key.category == TacticCategory::Smart)
        });
    let has_control_problem = slow_steps
        .iter()
        .any(|step| step.key.category == TacticCategory::Control)
        || profiles.iter().any(|profile| {
            profile.timed_out
                && profile
                    .active
                    .iter()
                    .any(|key| key.category == TacticCategory::Control)
        });
    let has_certification_problem = profiles.iter().any(|profile| {
        (profile.work.claims > 0
            && average_time(profile.accounting.certification, profile.work.claims)
                > CERTIFICATION_PER_CLAIM_LIMIT)
            || (profile.work.certification_paths > 0
                && average_time(
                    profile.accounting.certification,
                    profile.work.certification_paths,
                ) > CERTIFICATION_PER_PATH_LIMIT)
    });
    let has_setup_problem = profiles.iter().any(|profile| {
        profile.work.source_files > 0
            && (average_time(profile.accounting.frontend, profile.work.source_files)
                > SETUP_PER_FILE_LIMIT
                || average_time(profile.accounting.environment, profile.work.source_files)
                    > SETUP_PER_FILE_LIMIT)
    });
    let unknown_timing = profiles
        .iter()
        .filter(|profile| !profile.unknown_timing.is_empty())
        .collect::<Vec<_>>();
    if !unknown_timing.is_empty() {
        writeln!(output, "\nUNRECOGNIZED TIMING LINES").expect("writing a String cannot fail");
        writeln!(
            output,
            "  This profile skipped verifier timing output it does not understand, so the report below may be incomplete. Teach src/bin/click-profile.rs about these kinds."
        )
        .expect("writing a String cannot fail");
    }
    for profile in &unknown_timing {
        for (kind, seen) in &profile.unknown_timing {
            writeln!(
                output,
                "  {}: {} line{} of kind `{kind}`",
                profile.project,
                seen.count,
                if seen.count == 1 { "" } else { "s" }
            )
            .expect("writing a String cannot fail");
            writeln!(output, "    {}", seen.example).expect("writing a String cannot fail");
        }
    }

    let unresolved = profiles
        .iter()
        .filter(|profile| !profile.unresolved_positions.is_empty())
        .collect::<Vec<_>>();
    if !unresolved.is_empty() {
        writeln!(output, "\nSTEPS WITHOUT A SOURCE LOCATION")
            .expect("writing a String cannot fail");
        writeln!(
            output,
            "  These steps are timed and classified, but the verifier reported a tactic index the surface proof does not have — a certificate the verifier planned itself. Their times above are real; only the location is missing."
        )
        .expect("writing a String cannot fail");
    }
    for profile in &unresolved {
        for (reason, count) in &profile.unresolved_positions {
            writeln!(
                output,
                "  {}: {count} step{} — {reason}",
                profile.project,
                if *count == 1 { "" } else { "s" }
            )
            .expect("writing a String cannot fail");
        }
    }

    let has_unknown_timing = !unknown_timing.is_empty();
    // This is independent of tactic thresholds: a material invisible
    // remainder means the profile is incomplete even if every tactic is fast.
    let materially_unattributed = profiles
        .iter()
        .any(|profile| profile.accounting.materially_unattributed());
    let has_verification_failure = profiles
        .iter()
        .any(|profile| profile.verification_failure.is_some());
    if has_verification_failure {
        writeln!(
            output,
            "\nNEXT: fix the verification failure first. Timings from other projects are preserved, but the failed project profile is incomplete."
        )
        .expect("writing a String cannot fail");
    } else if has_simple_problem {
        writeln!(
            output,
            "\nNEXT: fix or reduce the SIMPLE bottleneck first. Expanding surrounding SMART tactics can only move or expose this deterministic cost."
        )
        .expect("writing a String cannot fail");
    } else if has_smart_failure {
        writeln!(
            output,
            "\nNEXT: reduce the failed or interrupted SMART search in Click. It produced no certificate, so click-expand is not available for this finding."
        )
        .expect("writing a String cannot fail");
    } else if has_smart_candidate {
        writeln!(
            output,
            "\nNEXT: expand one SMART location, apply its output, and rerun this profile to verify the rewrite."
        )
        .expect("writing a String cannot fail");
    } else if has_control_problem {
        writeln!(
            output,
            "\nNEXT: inspect the nested timings inside the CONTROL container; act on a nested SIMPLE or SMART step, not on the container row."
        )
        .expect("writing a String cannot fail");
    } else if has_certification_problem {
        writeln!(
            output,
            "\nNEXT: reduce the CERTIFICATION bottleneck; tactic expansion is not the indicated fix for this rate."
        )
        .expect("writing a String cannot fail");
    } else if has_setup_problem {
        writeln!(
            output,
            "\nNEXT: reduce the SETUP bottleneck in frontend or environment construction."
        )
        .expect("writing a String cannot fail");
    } else if has_unknown_timing {
        writeln!(
            output,
            "\nNEXT: nothing crossed the configured thresholds, but unrecognized timing lines mean this green is not trustworthy. Teach the parser those kinds and rerun."
        )
        .expect("writing a String cannot fail");
    } else if materially_unattributed {
        writeln!(
            output,
            "\nNEXT: nothing crossed the configured thresholds, but a material amount of wall time is UNATTRIBUTED. Instrument that machinery before reading this profile as clean."
        )
        .expect("writing a String cannot fail");
    } else {
        if profiles
            .iter()
            .any(|profile| profile.accounting.denominator() >= VOLUME_REPORT_THRESHOLD)
        {
            writeln!(
                output,
                "\nNEXT: measured cost is HEALTHY VOLUME at the current baselines; reduce proof volume or improve Click's aggregate throughput rather than expanding an arbitrary tactic."
            )
            .expect("writing a String cannot fail");
        } else {
            writeln!(
                output,
                "\nNEXT: the measured run is within the current baselines."
            )
            .expect("writing a String cannot fail");
        }
    }

    output
}

/// Prints where each profiled run's wall-clock time actually went.
///
/// The category sections above only list steps that crossed a threshold, so
/// they answer "what should I act on" but not "is this proof smart-slow or
/// simple-slow overall". This does.
fn render_accounting(output: &mut String, profiles: &[ProjectProfile]) {
    let measured = profiles
        .iter()
        .filter(|profile| !profile.accounting.denominator().is_zero())
        .collect::<Vec<_>>();
    if measured.is_empty() {
        return;
    }
    writeln!(output, "\nTIME ACCOUNTING").expect("writing a String cannot fail");
    writeln!(
        output,
        "  The total is child-process wall time when available. Tactic time is exclusive, and every row is non-overlapping. UNATTRIBUTED includes source I/O, process overhead, and verifier machinery with no recognized phase timing."
    )
    .expect("writing a String cannot fail");
    for profile in measured {
        let accounting = profile.accounting;
        writeln!(
            output,
            "  {}: {} total{}",
            profile.project,
            format_fractional_duration(accounting.denominator()),
            if accounting.wall_total.is_zero() && accounting.total.is_zero() {
                " measured (the run reported no function total, so this is the measured time only)"
            } else {
                ""
            }
        )
        .expect("writing a String cannot fail");
        for (label, part) in [
            ("FRONTEND", accounting.frontend),
            ("ENVIRONMENT", accounting.environment),
            ("SIMPLE", accounting.simple),
            ("SMART", accounting.smart),
            ("CONTROL", accounting.control),
            ("CERTIFICATION", accounting.certification),
            ("UNATTRIBUTED", accounting.unattributed()),
        ] {
            writeln!(
                output,
                "    {label:>13}  {:>10}  {:>5.1}%",
                format_fractional_duration(part),
                accounting.share(part),
            )
            .expect("writing a String cannot fail");
        }
    }
}

fn render_work_metrics(output: &mut String, profiles: &[ProjectProfile]) {
    let measured = profiles
        .iter()
        .filter(|profile| {
            profile.work.source_files > 0
                || profile.work.functions > 0
                || !profile.work.tactics.is_empty()
        })
        .collect::<Vec<_>>();
    if measured.is_empty() {
        return;
    }
    writeln!(output, "\nWORK AND THROUGHPUT").expect("writing a String cannot fail");
    writeln!(
        output,
        "  Counts come from completed verifier operations, not source-line estimates. C transitions are a semantic subset of SIMPLE and are not an additional time bucket."
    )
    .expect("writing a String cannot fail");
    for profile in measured {
        let work = &profile.work;
        writeln!(
            output,
            "  {}: {} file{}, {} function{}, {} claim{}, {} certification path{}",
            profile.project,
            work.source_files,
            if work.source_files == 1 { "" } else { "s" },
            work.functions,
            if work.functions == 1 { "" } else { "s" },
            work.claims,
            if work.claims == 1 { "" } else { "s" },
            work.certification_paths,
            if work.certification_paths == 1 {
                ""
            } else {
                "s"
            },
        )
        .expect("writing a String cannot fail");
        render_operation_stats(output, "C TRANSITIONS", work.c_transitions);
        for category in [
            TacticCategory::Simple,
            TacticCategory::Smart,
            TacticCategory::Control,
        ] {
            render_operation_stats(
                output,
                &format!(
                    "{} {}",
                    category.label(),
                    if category == TacticCategory::Smart {
                        "ATTEMPTS"
                    } else {
                        "COMPLETED"
                    }
                ),
                work.category(category),
            );
        }
        let failed_smart = work
            .failed_tactics
            .iter()
            .filter(|key| key.category == TacticCategory::Smart)
            .count();
        let smart_attempts = work.category(TacticCategory::Smart).count;
        if smart_attempts > 0 || failed_smart > 0 {
            writeln!(
                output,
                "    {:>24}  {:>6} succeeded, {:>6} failed",
                "SMART OUTCOMES",
                smart_attempts.saturating_sub(failed_smart),
                failed_smart,
            )
            .expect("writing a String cannot fail");
        }
        if work.source_files > 0 {
            render_rate(
                output,
                "FRONTEND / FILE",
                profile.accounting.frontend,
                work.source_files,
            );
            render_rate(
                output,
                "ENVIRONMENT / FILE",
                profile.accounting.environment,
                work.source_files,
            );
        }
        if work.claims > 0 {
            render_rate(
                output,
                "CERTIFICATION / CLAIM",
                profile.accounting.certification,
                work.claims,
            );
        }
        if work.certification_paths > 0 {
            render_rate(
                output,
                "CERTIFICATION / PATH",
                profile.accounting.certification,
                work.certification_paths,
            );
        }
        let simple_kinds = work
            .tactics
            .iter()
            .filter(|((category, _), _)| *category == TacticCategory::Simple)
            .collect::<Vec<_>>();
        if !simple_kinds.is_empty() {
            writeln!(output, "    SIMPLE BY KIND").expect("writing a String cannot fail");
            for ((_, name), stats) in simple_kinds {
                render_operation_stats(output, name, *stats);
            }
        }
    }
}

fn render_operation_stats(output: &mut String, label: &str, stats: OperationStats) {
    writeln!(
        output,
        "    {label:>24}  {:>6}  total {:>10}  avg {:>10}  max {:>10}",
        stats.count,
        format_fractional_duration(stats.total),
        format_fractional_duration(stats.average()),
        format_fractional_duration(stats.max),
    )
    .expect("writing a String cannot fail");
}

fn render_rate(output: &mut String, label: &str, total: Duration, count: usize) {
    let average = average_time(total, count);
    writeln!(
        output,
        "    {label:>24}  {:>10}",
        format_fractional_duration(average),
    )
    .expect("writing a String cannot fail");
}

fn average_time(total: Duration, count: usize) -> Duration {
    if count == 0 {
        Duration::ZERO
    } else {
        total / u32::try_from(count).unwrap_or(u32::MAX)
    }
}

fn render_diagnoses(output: &mut String, profiles: &[ProjectProfile]) {
    writeln!(output, "\nDIAGNOSES").expect("writing a String cannot fail");
    writeln!(
        output,
        "  Conservative development baselines: SIMPLE average <= {}, certification <= {}/claim and <= {}/path, frontend/environment <= {}/file. Per-tactic thresholds remain the long-tail guards.",
        format_fractional_duration(SIMPLE_AVERAGE_LIMIT),
        format_fractional_duration(CERTIFICATION_PER_CLAIM_LIMIT),
        format_fractional_duration(CERTIFICATION_PER_PATH_LIMIT),
        format_fractional_duration(SETUP_PER_FILE_LIMIT),
    )
    .expect("writing a String cannot fail");
    for profile in profiles {
        writeln!(output, "  {}:", profile.project).expect("writing a String cannot fail");
        let mut findings = 0;
        let simple = profile.work.category(TacticCategory::Simple);
        let slow_simple = profile
            .slow_steps
            .iter()
            .any(|step| step.key.category == TacticCategory::Simple);
        if slow_simple || (simple.count > 0 && simple.average() > SIMPLE_AVERAGE_LIMIT) {
            findings += 1;
            writeln!(
                output,
                "    SIMPLE ENGINE BUG — deterministic replay crossed a tail or throughput bound; reduce and fix Click."
            )
            .expect("writing a String cannot fail");
        }
        if profile
            .slow_steps
            .iter()
            .any(|step| step.key.category == TacticCategory::Smart && !step.failed)
        {
            findings += 1;
            writeln!(
                output,
                "    SMART HOTSPOT — expand one reported successful smart site, verify the artifact, and compare its profile."
            )
            .expect("writing a String cannot fail");
        }
        if profile
            .slow_steps
            .iter()
            .any(|step| step.key.category == TacticCategory::Smart && step.failed)
            || (profile.timed_out
                && profile
                    .active
                    .iter()
                    .any(|key| key.category == TacticCategory::Smart))
        {
            findings += 1;
            writeln!(
                output,
                "    SMART SEARCH FAILURE — unsuccessful or interrupted smart search crossed its bound; reduce Click because no certificate exists to expand."
            )
            .expect("writing a String cannot fail");
        }
        if profile
            .slow_steps
            .iter()
            .any(|step| step.key.category == TacticCategory::Control)
        {
            findings += 1;
            writeln!(
                output,
                "    CONTROL BOTTLENECK — inspect its exclusive bookkeeping and nested tactic findings."
            )
            .expect("writing a String cannot fail");
        }
        let certification_per_claim =
            average_time(profile.accounting.certification, profile.work.claims);
        let certification_per_path = average_time(
            profile.accounting.certification,
            profile.work.certification_paths,
        );
        if (profile.work.claims > 0
            && certification_per_claim > CERTIFICATION_PER_CLAIM_LIMIT)
            || (profile.work.certification_paths > 0
                && certification_per_path > CERTIFICATION_PER_PATH_LIMIT)
        {
            findings += 1;
            writeln!(
                output,
                "    CERTIFICATION BOTTLENECK — kernel certification is expensive for its measured claims or paths."
            )
            .expect("writing a String cannot fail");
        }
        let frontend_per_file =
            average_time(profile.accounting.frontend, profile.work.source_files);
        let environment_per_file =
            average_time(profile.accounting.environment, profile.work.source_files);
        if profile.work.source_files > 0
            && (frontend_per_file > SETUP_PER_FILE_LIMIT
                || environment_per_file > SETUP_PER_FILE_LIMIT)
        {
            findings += 1;
            writeln!(
                output,
                "    SETUP BOTTLENECK — frontend or environment construction is expensive for its file count."
            )
            .expect("writing a String cannot fail");
        }
        if profile.accounting.materially_unattributed() || !profile.unknown_timing.is_empty() {
            findings += 1;
            writeln!(
                output,
                "    UNEXPLAINED — a material residual or unknown timing event prevents a complete diagnosis."
            )
            .expect("writing a String cannot fail");
        }
        if profile.verification_failure.is_some() {
            findings += 1;
            writeln!(
                output,
                "    INCOMPLETE — verification failed, so counts and rates describe only the completed frontier."
            )
            .expect("writing a String cannot fail");
        }
        if findings == 0 {
            if profile.accounting.denominator() >= VOLUME_REPORT_THRESHOLD {
                writeln!(
                    output,
                    "    HEALTHY VOLUME — no measured operation or normalized rate crossed a bound; total cost comes from work volume at the current baselines."
                )
                .expect("writing a String cannot fail");
            } else {
                writeln!(
                    output,
                    "    WITHIN BASELINE — the measured run is small and no bound was crossed."
                )
                .expect("writing a String cannot fail");
            }
        }
    }
}

fn render_category(
    output: &mut String,
    slow_steps: &[&SlowStep],
    category: TacticCategory,
    title: &str,
    advice: &str,
    thresholds: Thresholds,
    time_limit: Duration,
) {
    writeln!(output, "\n{title}").expect("writing a String cannot fail");
    writeln!(output, "  {advice}").expect("writing a String cannot fail");
    let matching = slow_steps
        .iter()
        .copied()
        .filter(|step| step.key.category == category)
        .collect::<Vec<_>>();
    if matching.is_empty() {
        writeln!(output, "  none completed").expect("writing a String cannot fail");
        return;
    }
    if category == TacticCategory::Simple {
        writeln!(
            output,
            "  WARNING: expanding an enclosing smart tactic is not a fix for the simple steps below."
        )
        .expect("writing a String cannot fail");
    }
    for step in matching {
        writeln!(
            output,
            "  {:>10}  {}  {}  {}  statement {}{}",
            format_fractional_duration(step.elapsed),
            step_location(&step.key),
            step.key.claim,
            step.key.tactic_name,
            step.key.statement_index,
            if step.failed {
                "  FAILED — no certificate to expand"
            } else {
                ""
            },
        )
        .expect("writing a String cannot fail");
        if !step.failed
            && let (TacticCategory::Smart, Some(position)) = (category, step.key.position)
        {
            render_expansion_command(output, &step.key, position, thresholds, time_limit);
        }
    }
}

/// Renders a step's `PATH:LINE:COLUMN`, or just the path when the step has no
/// surface tactic to point at.
fn step_location(key: &StepKey) -> String {
    match key.position {
        Some(position) => format!(
            "{}:{}:{}",
            key.source_path.display(),
            position.line,
            position.column
        ),
        None => format!("{} (no source location)", key.source_path.display()),
    }
}

fn render_expansion_command(
    output: &mut String,
    key: &StepKey,
    position: SourcePosition,
    thresholds: Thresholds,
    time_limit: Duration,
) {
    let artifact = expanded_artifact_path(&key.source_path);
    writeln!(
        output,
        "              expand: cargo run --quiet --bin click-expand -- --time-limit {} {}:{}:{} > {}",
        format_duration(EXPANSION_TIME_LIMIT),
        key.source_path.display(),
        position.line,
        position.column,
        artifact.display(),
    )
    .expect("writing a String cannot fail");
    if !looks_like_mdtest(&artifact) {
        writeln!(
            output,
            "              verify: cargo run --quiet --bin click-verify -- {}",
            artifact.display(),
        )
        .expect("writing a String cannot fail");
    }
    writeln!(
        output,
        "           reprofile: cargo run --quiet --bin click-profile -- --smart-threshold {} --simple-threshold {} --control-threshold {} --time-limit {} {}",
        format_duration(thresholds.smart),
        format_duration(thresholds.simple),
        format_duration(thresholds.control),
        format_duration(time_limit),
        artifact.display(),
    )
    .expect("writing a String cannot fail");
}

fn expanded_artifact_path(source: &Path) -> PathBuf {
    let extension = source
        .extension()
        .and_then(|extension| extension.to_str())
        .unwrap_or("click");
    let stem = source
        .file_stem()
        .and_then(|stem| stem.to_str())
        .unwrap_or("expanded");
    source.with_file_name(format!("{stem}.expanded.{extension}"))
}

/// Verifies one markdown test in the child process, from the same embedded
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
    if env::var_os("CLICK_TIMINGS").is_some() {
        eprintln!("click timing: source {}", path.display());
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
    let (root, mut click_paths) = if project.is_file()
        && project
            .extension()
            .is_some_and(|extension| extension == "click")
    {
        (
            project.parent().unwrap_or_else(|| Path::new(".")),
            vec![project.to_path_buf()],
        )
    } else {
        (project, files_with_extension(project, "click")?)
    };
    let mut c_paths = files_with_extension(root, "c")?;
    c_paths.sort();
    click_paths.sort();
    if click_paths.is_empty() {
        return Err(format!(
            "example project `{}` has no Click sidecar",
            project.display()
        ));
    }
    let c_sources = c_paths
        .iter()
        .map(|path| {
            let filename = path
                .file_name()
                .and_then(|name| name.to_str())
                .ok_or_else(|| format!("invalid UTF-8 path `{}`", path.display()))?
                .to_string();
            let source = fs::read_to_string(path)
                .map_err(|error| format!("failed to read `{}`: {error}", path.display()))?;
            Ok((filename, source))
        })
        .collect::<Result<Vec<_>, String>>()?;
    let source_refs = c_sources
        .iter()
        .map(|(name, source)| (name.as_str(), source.as_str()))
        .collect::<Vec<_>>();
    for click_path in click_paths {
        let click_source = fs::read_to_string(&click_path)
            .map_err(|error| format!("failed to read `{}`: {error}", click_path.display()))?;
        if env::var_os("CLICK_TIMINGS").is_some() {
            eprintln!("click timing: source {}", click_path.display());
        }
        verify_c0_sources(&click_source, &source_refs).map_err(|error| {
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
mod tests {
    use super::*;

    #[test]
    fn parses_timing_events_and_keeps_the_active_stack() {
        let output = r#"
click timing: source examples/sample.click
click timing: started tactic example.contract 2 execute_step class smart statement 4 source 5
click timing: started tactic example.contract 2 certified_statement_step class simple statement 4 source 5
click timing: tactic example.contract 2 certified_statement_step class simple statement 4 source 5 1.250000s
"#;
        let profile = parse_profile("sample", output, Thresholds::default(), true)
            .expect("the current timing format should parse");
        assert_eq!(profile.slow_steps.len(), 1);
        assert_eq!(
            profile.slow_steps[0].key.tactic_name,
            "certified_statement_step"
        );
        assert_eq!(profile.slow_steps[0].key.category, TacticCategory::Simple);
        assert_eq!(profile.active.len(), 1);
        assert_eq!(profile.active[0].tactic_name, "execute_step");
        assert_eq!(profile.active[0].category, TacticCategory::Smart);
        assert!(profile.unknown_timing.is_empty());
    }

    /// The certification timing kinds added on 2026-07-30 share the stderr
    /// stream with the tactic events. The profiler must skip them silently
    /// and, crucially, must not count them as drift.
    #[test]
    fn recognizes_and_skips_the_certification_timing_kinds() {
        let output = r#"
click timing: source examples/sample.click
click timing: function example_function 0.512s
click timing: contract execution example_function 0.400000s
click timing: contract claims example_function 0.090000s
click timing: contract entry resources do not satisfy requirements
click timing: contract entry resources do not certify requirement safety
click timing: claim paths example_function prepared 12 in 0.030000s
click timing: claim example_function Ensure(4) 0.012000s
click timing: tactic example.contract 0 execute_step class smart statement 1 source 2 3.000000s
"#;
        let profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");

        assert_eq!(profile.slow_steps.len(), 1);
        assert_eq!(profile.slow_steps[0].key.tactic_name, "execute_step");
        assert_eq!(profile.work.source_files, 1);
        assert_eq!(profile.work.functions, 1);
        assert_eq!(profile.work.claims, 1);
        assert_eq!(profile.work.certification_paths, 12);
        assert!(
            profile.unknown_timing.is_empty(),
            "certification kinds must be recognized, not counted as drift: {:?}",
            profile.unknown_timing
        );
    }

    /// The report must be able to answer "is this proof smart-slow or
    /// simple-slow overall", which means nested containers cannot double
    /// count: a control container's own share is its time minus the steps it
    /// ran, and the buckets plus the unattributed remainder equal the total.
    #[test]
    fn accounting_splits_the_run_into_exclusive_class_time() {
        let output = r#"
click timing: source examples/sample.click
click timing: started tactic example.contract 0 have class control statement 1 source 0
click timing: started tactic example.contract 1 simp class smart statement 1 source 1
click timing: tactic example.contract 1 simp class smart statement 1 source 1 3.000000s
click timing: started tactic example.contract 2 close_invariants class simple statement 1 source 2
click timing: tactic example.contract 2 close_invariants class simple statement 1 source 2 4.000000s
click timing: tactic example.contract 0 have class control statement 1 source 0 8.000000s
click timing: contract execution example_function 1.000000s
click timing: contract claims example_function 0.500000s
click timing: function example_function 12.000s
"#;
        let profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");

        assert!(profile.unknown_timing.is_empty(), "{:?}", profile.unknown_timing);
        assert_eq!(profile.accounting.total, Duration::from_secs(12));
        assert_eq!(profile.accounting.smart, Duration::from_secs(3));
        assert_eq!(profile.accounting.simple, Duration::from_secs(4));
        // 8s container minus the 3s + 4s it ran.
        assert_eq!(profile.accounting.control, Duration::from_secs(1));
        assert_eq!(profile.accounting.certification, Duration::from_millis(1_500));
        assert_eq!(profile.accounting.unattributed(), Duration::from_millis(2_500));
        assert!(profile.active.is_empty());
        assert_eq!(profile.slow_steps.len(), 2);
        assert!(profile.slow_steps.iter().any(|step| {
            step.key.category == TacticCategory::Smart
                && step.elapsed == Duration::from_secs(3)
        }));
        assert!(profile.slow_steps.iter().any(|step| {
            step.key.category == TacticCategory::Simple
                && step.elapsed == Duration::from_secs(4)
        }));
        assert!(profile
            .slow_steps
            .iter()
            .all(|step| step.key.category != TacticCategory::Control));

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
        assert!(report.contains("TIME ACCOUNTING"), "{report}");
        assert!(report.contains("UNATTRIBUTED"), "{report}");
        assert!(report.contains("12.000s total"), "{report}");
    }

    /// The hole this profiler had was a report that read clean while most of
    /// the run was invisible to it. A run whose unattributed time outweighs
    /// everything it can name must not read as clean.
    #[test]
    fn a_mostly_unattributed_run_does_not_read_as_clean() {
        let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 simp class smart statement 1 source 0 1.000000s
click timing: function example_function 20.000s
"#;
        let profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");
        assert!(
            profile.slow_steps.is_empty(),
            "nothing here crosses a threshold; that is the point"
        );
        assert_eq!(profile.accounting.unattributed(), Duration::from_secs(19));

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

        assert!(report.contains("UNEXPLAINED"), "{report}");
        assert!(!report.contains(
            "NEXT: no completed smart expansion candidates or simple engine bottlenecks"
        ));
    }

    /// A proof that fails never reports a function total, and a failing proof
    /// is exactly the kind worth profiling. Its split must still be readable.
    #[test]
    fn a_failed_run_still_reports_its_class_split() {
        let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 simp class smart statement 1 source 0 6.000000s
click timing: tactic example.contract 1 fold class simple statement 1 source 1 2.000000s
"#;
        let mut profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");
        profile.verification_failure = Some("could not certify the claim".to_string());
        for step in &mut profile.slow_steps {
            step.key.position = Some(SourcePosition { line: 1, column: 1 });
        }

        assert_eq!(profile.accounting.total, Duration::ZERO);
        assert_eq!(profile.accounting.denominator(), Duration::from_secs(8));

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

        assert!(report.contains("TIME ACCOUNTING"), "{report}");
        assert!(report.contains("8.000s total measured"), "{report}");
        assert!(report.contains("SMART      6.000s   75.0%"), "{report}");
        assert!(report.contains("SIMPLE      2.000s   25.0%"), "{report}");
    }

    #[test]
    fn whole_run_accounting_includes_setup_phases_and_wall_residual() {
        let output = r#"
click timing: source examples/sample.click
click timing: phase frontend 0.500000s
click timing: phase environment 1.000000s
click timing: tactic example.contract 0 step class simple statement 1 source 0 0.200000s
click timing: contract execution example_function 1.000000s
click timing: contract claims example_function 1.000000s
click timing: function example_function 2.200s
"#;
        let mut profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");
        profile.accounting.wall_total = Duration::from_secs(4);

        assert_eq!(profile.accounting.frontend, Duration::from_millis(500));
        assert_eq!(profile.accounting.environment, Duration::from_secs(1));
        assert_eq!(profile.accounting.simple, Duration::from_millis(200));
        assert_eq!(profile.accounting.certification, Duration::from_secs(2));
        assert_eq!(profile.accounting.unattributed(), Duration::from_millis(300));
        assert_eq!(profile.work.source_files, 1);
        assert_eq!(profile.work.functions, 1);
        assert_eq!(profile.work.c_transitions.count, 1);
        assert_eq!(profile.work.c_transitions.total, Duration::from_millis(200));

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
        assert!(report.contains("4.000s total"), "{report}");
        assert!(report.contains("FRONTEND"), "{report}");
        assert!(report.contains("ENVIRONMENT"), "{report}");
        assert!(report.contains("UNATTRIBUTED"), "{report}");
        assert!(report.contains("WORK AND THROUGHPUT"), "{report}");
        assert!(report.contains("C TRANSITIONS"), "{report}");
        assert!(report.contains("SIMPLE BY KIND"), "{report}");
        assert!(report.contains("UNEXPLAINED"), "{report}");
    }

    #[test]
    fn fractional_unattributed_time_is_material_below_the_absolute_limit() {
        let output = r#"
click timing: source examples/sample.click
click timing: phase frontend 0.080000s
click timing: function example_function 0.080s
"#;
        let mut profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");
        profile.accounting.wall_total = Duration::from_millis(100);

        assert_eq!(profile.accounting.unattributed(), Duration::from_millis(20));
        assert!(profile.accounting.materially_unattributed());
    }

    /// The kinds the accounting consumes are load-bearing now, so a drifted
    /// one is a loud error rather than a silently missing bucket.
    #[test]
    fn drifted_accounting_timing_lines_are_a_loud_error() {
        for drifted in [
            "click timing: function example_function twelve",
            "click timing: contract execution example_function 1.0",
            "click timing: contract claims example_function",
            "click timing: phase frontend eventually",
        ] {
            let output = format!("click timing: source examples/sample.click\n{drifted}\n");
            let message = parse_profile("sample", &output, Thresholds::default(), false)
                .expect_err(&format!("drifted line should be loud: {drifted}"));
            assert!(message.contains("has drifted"), "{message}");
        }
    }

    /// A step the verifier planned itself can name a tactic index the surface
    /// proof does not have. That must cost the step its location, not the
    /// whole profile — the proofs worth profiling are exactly the ones whose
    /// loop phases are auto-planned.
    #[test]
    fn steps_without_a_source_location_are_reported_not_fatal() {
        let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 7 close_invariants class simple statement 3 source 7 4.000000s
click timing: function example_function 4.000s
"#;
        let mut profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");
        profile
            .unresolved_positions
            .insert("`example.contract` has no source tactic occurrence 7".to_string(), 1);

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

        assert!(report.contains("STEPS WITHOUT A SOURCE LOCATION"), "{report}");
        assert!(report.contains("examples/sample.click (no source location)"), "{report}");
        assert!(report.contains("no source tactic occurrence 7"), "{report}");
        assert!(report.contains("4.000s"), "{report}");
    }

    #[test]
    fn unrecognized_timing_kinds_are_counted_and_reported() {
        let output = r#"
click timing: source examples/sample.click
click timing: gadget alpha 1.000000s
click timing: gadget beta 2.000000s
click timing: widget 0.5s
"#;
        let profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("unknown kinds are a warning, not a parse failure");

        assert_eq!(profile.unknown_timing.len(), 2);
        assert_eq!(profile.unknown_timing["gadget"].count, 2);
        assert_eq!(
            profile.unknown_timing["gadget"].example,
            "click timing: gadget alpha 1.000000s"
        );
        assert_eq!(profile.unknown_timing["widget"].count, 1);

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

        assert!(report.contains("UNRECOGNIZED TIMING LINES"));
        assert!(report.contains("2 lines of kind `gadget`"));
        assert!(report.contains("1 line of kind `widget`"));
        assert!(report.contains("click timing: gadget alpha 1.000000s"));
        assert!(
            report.contains("this green is not trustworthy"),
            "a report that skipped timing lines must not read as clean:\n{report}"
        );
        assert!(!report.contains(
            "NEXT: no completed smart expansion candidates or simple engine bottlenecks"
        ));
    }

    /// Drift in the kinds the profile is built from is a false green, not a
    /// warning: the report would show no slow steps because it understood
    /// none. These must fail loudly.
    #[test]
    fn drifted_tactic_timing_lines_are_a_loud_error() {
        for drifted in [
            // An extra trailing field.
            "click timing: tactic example.contract 0 step class simple statement 1 source 2 nested 3 1.000000s",
            // A renamed structural keyword.
            "click timing: tactic example.contract 0 step kind simple statement 1 source 2 1.000000s",
            // An unknown class.
            "click timing: tactic example.contract 0 step class hybrid statement 1 source 2 1.000000s",
            // A non-numeric elapsed time.
            "click timing: tactic example.contract 0 step class simple statement 1 source 2 slows",
            // The started variant, with a dropped field.
            "click timing: started tactic example.contract 0 step class simple statement 1 source",
            // An empty source path.
            "click timing: source ",
        ] {
            let output = format!("click timing: source examples/sample.click\n{drifted}\n");
            let message = parse_profile("sample", &output, Thresholds::default(), false)
                .expect_err(&format!("drifted line should be loud: {drifted}"));
            assert!(message.contains("has drifted"), "{message}");
            assert!(message.contains(drifted.trim_end()), "{message}");
        }
    }

    #[test]
    fn finished_tactic_lines_tolerate_extra_whitespace_and_precision() {
        let output = "click timing: source examples/sample.click\n\
                      click timing:  tactic  example.contract 0 step class simple statement 1 source 2   0.75s  \n";
        let profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("whitespace variation is not format drift");

        assert_eq!(profile.slow_steps.len(), 1);
        assert_eq!(profile.slow_steps[0].elapsed, Duration::from_millis(750));
    }

    /// An example project directory carries a `README.md`; only a directory
    /// with no Click sidecar under it is a directory of mdtests.
    #[test]
    fn targets_prefer_example_projects_over_stray_markdown() {
        let manifest = PathBuf::from(env!("CARGO_MANIFEST_DIR"));

        let mdtest = manifest.join("mdtests/count_to_three_loop_invariants.md");
        assert_eq!(
            profile_targets(&mdtest),
            Ok(vec![mdtest.clone()]),
            "a `.md` argument names one mdtest"
        );

        let projects = profile_targets(&manifest.join("examples/input-cursor"))
            .expect("an example project with a README is still a project");
        assert_eq!(projects.len(), 1);
        assert!(projects[0].ends_with("input-cursor"), "{projects:?}");

        let mdtests = profile_targets(&manifest.join("mdtests"))
            .expect("a directory of markdown tests profiles all of them");
        assert!(mdtests.len() > 1);
        assert!(mdtests.iter().all(|path| looks_like_mdtest(path)), "{mdtests:?}");

        let sidecar = manifest.join("examples/input-cursor/input_cursor.click");
        assert_eq!(
            profile_targets(&sidecar),
            Ok(vec![sidecar.clone()]),
            "a direct sidecar target is needed to profile an expanded artifact"
        );
    }

    /// Quarantine is a property of the gate, not of the file, so the profiler
    /// must be able to extract and profile a quarantined mdtest.
    #[test]
    fn quarantined_mdtests_are_profileable() {
        let path = PathBuf::from(env!("CARGO_MANIFEST_DIR"))
            .join("mdtests/bubble_sort3_two_pass_sorted.md");
        let source = load_profiled_source(&path).expect("a quarantined mdtest still extracts");

        assert!(source.click_source.contains("bubble_sort3_two_pass"));
        assert!(!source.c_sources.is_empty());
        assert!(
            source.line_offset > 0,
            "positions inside an mdtest sidecar must be offset to the markdown file"
        );
    }

    #[test]
    fn parses_profile_arguments() {
        assert_eq!(
            parse_arguments([
                "--simple-threshold".to_string(),
                "250ms".to_string(),
                "--smart-threshold".to_string(),
                "3s".to_string(),
                "--time-limit".to_string(),
                "2m".to_string(),
                "examples".to_string(),
            ]),
            Ok(Arguments {
                path: PathBuf::from("examples"),
                thresholds: Thresholds {
                    smart: Duration::from_secs(3),
                    simple: Duration::from_millis(250),
                    control: DEFAULT_CONTROL_THRESHOLD,
                },
                time_limit: Duration::from_secs(120),
                child: false,
            })
        );
    }

    #[test]
    fn common_threshold_sets_every_tactic_class() {
        let arguments = parse_arguments([
            "--threshold".to_string(),
            "750ms".to_string(),
            "examples".to_string(),
        ])
        .expect("common threshold should parse");

        assert_eq!(
            arguments.thresholds,
            Thresholds {
                smart: Duration::from_millis(750),
                simple: Duration::from_millis(750),
                control: Duration::from_millis(750),
            }
        );
        assert_eq!(arguments.time_limit, DEFAULT_TIME_LIMIT);
    }

    #[test]
    fn report_separates_actions_and_only_suggests_expanding_smart_tactics() {
        let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 certified_statement_step class simple statement 1 source 10 0.750000s
click timing: tactic example.contract 1 execute_step class smart statement 2 source 20 2.500000s
click timing: tactic example.contract 2 have class control statement 3 source 30 2.100000s
"#;
        let mut profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");
        for (index, step) in profile.slow_steps.iter_mut().enumerate() {
            step.key.position = Some(SourcePosition {
                line: index + 10,
                column: 5,
            });
        }

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

        assert!(report.contains("SIMPLE — FIX THE ENGINE; DO NOT EXPAND"));
        assert!(report.contains("WARNING: expanding an enclosing smart tactic is not a fix"));
        assert!(report.contains("SMART — EXPAND SUCCESSES; REDUCE FAILURES"));
        assert!(report.contains("CONTROL — INSPECT NESTED STEPS"));
        assert!(report.contains("NEXT: fix or reduce the SIMPLE bottleneck first"));
        assert_eq!(report.matches("expand: cargo run").count(), 1);
        assert!(report.contains("--time-limit 1m"));
        assert!(report.contains("sample.expanded.click"), "{report}");
        assert!(report.contains("verify: cargo run --quiet --bin click-verify"), "{report}");
        assert!(report.contains("reprofile: cargo run --quiet --bin click-profile"), "{report}");
        assert!(report.contains("--smart-threshold 2s"), "{report}");
    }

    #[test]
    fn diagnoses_mixed_engine_search_certification_setup_and_residual_findings() {
        let output = r#"
click timing: source examples/sample.click
click timing: phase frontend 0.300000s
click timing: phase environment 0.010000s
click timing: tactic example.contract 0 step class simple statement 1 source 0 0.100000s
click timing: tactic example.contract 1 fold class simple statement 1 source 1 0.100000s
click timing: tactic example.contract 2 unfold class simple statement 1 source 2 0.100000s
click timing: tactic example.contract 3 simp class smart statement 1 source 3 3.000000s
click timing: contract execution example_function 1.000000s
click timing: contract claims example_function 1.000000s
click timing: claim paths example_function prepared 1 in 0.100000s
click timing: claim example_function Ensure(0) 0.100000s
click timing: function example_function 5.300s
"#;
        let mut profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");
        profile.accounting.wall_total = Duration::from_secs(6);

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
        for diagnosis in [
            "SIMPLE ENGINE BUG",
            "SMART HOTSPOT",
            "CERTIFICATION BOTTLENECK",
            "SETUP BOTTLENECK",
            "UNEXPLAINED",
        ] {
            assert!(report.contains(diagnosis), "missing {diagnosis}:\n{report}");
        }
    }

    #[test]
    fn diagnoses_large_healthy_aggregate_as_volume() {
        let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 simp class smart statement 1 source 0 0.400000s
click timing: tactic example.contract 1 simp class smart statement 1 source 1 0.400000s
click timing: tactic example.contract 2 simp class smart statement 1 source 2 0.400000s
click timing: function example_function 1.200s
"#;
        let profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
        assert!(report.contains("HEALTHY VOLUME"), "{report}");
        assert!(report.contains("NEXT: measured cost is HEALTHY VOLUME"), "{report}");
    }

    #[test]
    fn slow_failed_smart_search_is_not_an_expansion_candidate() {
        let output = r#"
click timing: source examples/sample.click
click timing: started tactic example.contract 0 simp class smart statement 1 source 0
click timing: tactic example.contract 0 simp class smart statement 1 source 0 3.000000s
click timing: failed tactic example.contract 0 simp class smart statement 1 source 0
"#;
        let mut profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("a failed tactic outcome should parse");
        profile.slow_steps[0].key.position = Some(SourcePosition {
            line: 10,
            column: 5,
        });

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);
        assert!(report.contains("SMART SEARCH FAILURE"), "{report}");
        assert!(report.contains("FAILED — no certificate to expand"), "{report}");
        assert!(report.contains("0 succeeded,      1 failed"), "{report}");
        assert!(!report.contains("expand: cargo run"), "{report}");
        assert!(report.contains("click-expand is not available"), "{report}");
    }

    #[test]
    fn control_only_report_directs_attention_to_nested_steps() {
        let output = r#"
click timing: source examples/sample.click
click timing: tactic example.contract 0 have class control statement 1 source 10 2.500000s
"#;
        let mut profile = parse_profile("sample", output, Thresholds::default(), false)
            .expect("the current timing format should parse");
        profile.slow_steps[0].key.position = Some(SourcePosition {
            line: 10,
            column: 5,
        });

        let report = render_profiles(&[profile], Thresholds::default(), DEFAULT_TIME_LIMIT);

        assert!(report.contains("NEXT: inspect the nested timings inside the CONTROL container"));
        assert!(!report.contains("expand: cargo run"));
    }

    #[test]
    fn report_preserves_timings_when_another_project_fails_verification() {
        let mut successful = parse_profile(
            "successful",
            r#"
click timing: source examples/successful.click
click timing: tactic example.contract 0 execute_step class smart statement 1 source 10 2.500000s
"#,
            Thresholds::default(),
            false,
        )
        .expect("the current timing format should parse");
        successful.slow_steps[0].key.position = Some(SourcePosition {
            line: 12,
            column: 5,
        });
        let mut failed = parse_profile(
            "failed",
            "click timing: source examples/failed.click",
            Thresholds::default(),
            false,
        )
        .expect("the current timing format should parse");
        failed.verification_failure =
            Some("example sidecar failed: certificate did not replay".to_string());

        let report = render_profiles(
            &[failed, successful],
            Thresholds::default(),
            DEFAULT_TIME_LIMIT,
        );

        assert!(report.contains("VERIFICATION FAILURES"));
        assert!(report.contains("certificate did not replay"));
        assert!(report.contains("examples/successful.click:12:5"));
        assert!(report.contains("fix the verification failure first"));
    }

    #[test]
    fn failure_diagnostic_omits_timing_stream() {
        let status = std::process::Command::new("sh")
            .arg("-c")
            .arg("exit 1")
            .status()
            .expect("test shell should run");
        let diagnostic = extract_verification_failure(
            "",
            "click timing: source example.click\nclick-profile: proof failed",
            status,
        );

        assert_eq!(diagnostic, "proof failed");
    }
}
