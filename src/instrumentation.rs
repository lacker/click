//! Structured verification events shared by the CLI, profiler, and tests.
//!
//! Verification is synchronous, so a thread-local collector gives each run an
//! independent event stream without global environment mutation.  The legacy
//! `CLICK_TIMINGS` text stream remains available for engine debugging, but
//! normal tooling consumes these values directly.

use std::cell::{Cell, RefCell};
use std::path::PathBuf;
use std::time::{Duration, Instant};

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TacticEvent {
    pub claim: String,
    pub tactic_index: usize,
    pub tactic_name: String,
    pub class: String,
    pub statement_index: usize,
    pub source_index: usize,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ActiveVerificationWork {
    Tactic(TacticEvent),
    Phase(&'static str),
    Driver,
}

#[derive(Clone, Debug, PartialEq)]
pub enum VerificationEvent {
    Source(PathBuf),
    PhaseStarted(&'static str),
    PhaseFinished {
        name: &'static str,
        elapsed: Duration,
    },
    TacticStarted(TacticEvent),
    TacticFinished {
        tactic: TacticEvent,
        elapsed: Duration,
        work: usize,
    },
    TacticFailed(TacticEvent),
    TacticWorkBudgetExceeded {
        tactic: TacticEvent,
        used: usize,
        limit: usize,
    },
    FunctionFinished {
        name: String,
        elapsed: Duration,
    },
    ContractExecutionFinished {
        function: String,
        elapsed: Duration,
    },
    ContractClaimsFinished {
        function: String,
        elapsed: Duration,
    },
    ClaimPathsPrepared {
        function: String,
        count: usize,
        elapsed: Duration,
    },
    ClaimFinished {
        function: String,
        key: String,
        elapsed: Duration,
    },
    /// A nested verifier operation reported for hotspot attribution. These
    /// spans may sit inside tactics or certification and therefore are not
    /// added to the top-level non-overlapping accounting buckets.
    OperationFinished {
        function: String,
        claim: String,
        name: String,
        elapsed: Duration,
        work: usize,
    },
    DeadlineExceeded(ActiveVerificationWork),
    Diagnostic(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TacticLimits {
    pub simple: Duration,
    pub smart: Duration,
    pub control: Duration,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TacticWorkLimits {
    /// Cooperative verifier checkpoints available to one simple tactic.
    pub simple: usize,
    /// Cooperative verifier checkpoints available to one smart tactic.
    pub smart: usize,
    /// Cooperative verifier checkpoints available to one control tactic,
    /// excluding work performed by its nested tactics.
    pub control: usize,
}

impl Default for TacticWorkLimits {
    /// The deterministic work budget is the primary per-tactic bound: it
    /// counts cooperative prover checkpoints, so the same source spends the
    /// same units on any machine under any load.
    ///
    /// Simple calibration (2026-08-12, whole-claim-gate base, after the
    /// order-fact and resolution-query memos, measured with budgets
    /// disabled so no cost is clipped): the green example corpus (1,278
    /// simple tactics including the gate's generated-certificate validation) measures
    /// p95 = 1,027 units, p99 = 6,292, max = 16,583; the green mdtest
    /// corpus (6,137 simple tactics across 383 fixtures) measures p99 =
    /// 766, second-largest = 20,796, max = 148,094 (copy3's
    /// `close_invariants`, the corpus outlier); the issue-tracked hot steps
    /// (input-cursor statement 5 and perpetual-service's fold) measure
    /// 35,368 and 46,242. 500,000 gives the corpus maximum 3.4x margin and
    /// everything else at least 10x, and deterministically fails any simple
    /// tactic that grows past roughly three times today's worst known cost.
    /// Changing a budget requires a fresh corpus measurement across BOTH
    /// the examples and the mdtests and a documented reason; it is never a
    /// way to make one proof pass.
    fn default() -> Self {
        Self {
            simple: 500_000,
            smart: 2_000_000,
            control: 2_000_000,
        }
    }
}

impl TacticWorkLimits {
    fn for_class(self, class: &str) -> Option<usize> {
        match class {
            "simple" => Some(self.simple),
            "smart" => Some(self.smart),
            "control" => Some(self.control),
            _ => None,
        }
    }
}

impl Default for TacticLimits {
    /// Real-time limits are a backstop behind the deterministic work
    /// budgets, catching stretches of work the cooperative checkpoints do
    /// not count. The simple limit is deliberately generous: near-threshold
    /// wall-clock enforcement made the same proof pass or fail with machine
    /// load (an idle 209 ms step measured 500 ms on a loaded machine), so
    /// the semantic gate for simple tactics is the work budget, and this
    /// cutoff only stops runaway uncounted loops. Smart search keeps its
    /// short cutoff: it is a heuristic whose latency is itself the product.
    fn default() -> Self {
        Self {
            simple: Duration::from_secs(5),
            smart: Duration::from_secs(2),
            control: Duration::from_secs(6),
        }
    }
}

impl TacticLimits {
    fn for_class(self, class: &str) -> Option<Duration> {
        match class {
            "simple" => Some(self.simple),
            "smart" => Some(self.smart),
            "control" => Some(self.control),
            _ => None,
        }
    }
}

#[derive(Clone, Debug)]
struct ActiveTactic {
    event: TacticEvent,
    exclusive: Duration,
    started_at: TacticInstant,
    running_since: TacticInstant,
    limit: Option<Duration>,
    work_used: usize,
    work_limit: Option<usize>,
    work_exhausted: bool,
    /// Deterministic work by named operation span, populated only while
    /// operation measurement is enabled, so an exhausted budget can report
    /// where its units went instead of only how many there were.
    named_work: std::collections::BTreeMap<String, usize>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum PendingLimitKind {
    Time,
    Work,
}

#[derive(Clone, Debug)]
struct PendingLimit {
    kind: PendingLimitKind,
    message: String,
}

#[derive(Clone, Copy, Debug)]
struct TacticInstant {
    wall: Instant,
    thread_cpu: Option<Duration>,
}

impl TacticInstant {
    fn now() -> Self {
        Self {
            wall: Instant::now(),
            thread_cpu: thread_cpu_time(),
        }
    }

    fn elapsed(self) -> Duration {
        match (self.thread_cpu, thread_cpu_time()) {
            (Some(start), Some(end)) => end.saturating_sub(start),
            _ => self.wall.elapsed(),
        }
    }

    fn duration_since(self, earlier: Self) -> Duration {
        match (earlier.thread_cpu, self.thread_cpu) {
            (Some(start), Some(end)) => end.saturating_sub(start),
            _ => self.wall.saturating_duration_since(earlier.wall),
        }
    }
}

#[cfg(unix)]
fn thread_cpu_time() -> Option<Duration> {
    let mut value = std::mem::MaybeUninit::<libc::timespec>::uninit();
    // SAFETY: `clock_gettime` initializes the supplied `timespec` on success.
    let result = unsafe { libc::clock_gettime(libc::CLOCK_THREAD_CPUTIME_ID, value.as_mut_ptr()) };
    if result != 0 {
        return None;
    }
    // SAFETY: a zero return from `clock_gettime` guarantees initialization.
    let value = unsafe { value.assume_init() };
    let seconds = u64::try_from(value.tv_sec).ok()?;
    let nanoseconds = u32::try_from(value.tv_nsec).ok()?;
    (nanoseconds < 1_000_000_000).then(|| Duration::new(seconds, nanoseconds))
}

#[cfg(not(unix))]
fn thread_cpu_time() -> Option<Duration> {
    None
}

thread_local! {
    static COLLECTORS: RefCell<Vec<Vec<VerificationEvent>>> = const { RefCell::new(Vec::new()) };
    static DEADLINES: RefCell<Vec<Instant>> = const { RefCell::new(Vec::new()) };
    static DEADLINE_CAPTURED: RefCell<Vec<bool>> = const { RefCell::new(Vec::new()) };
    static TACTIC_LIMITS: RefCell<Vec<TacticLimits>> = const { RefCell::new(Vec::new()) };
    static TACTIC_WORK_LIMITS: RefCell<Vec<TacticWorkLimits>> = const { RefCell::new(Vec::new()) };
    static TACTIC_TIME_LIMITS_DISABLED: Cell<usize> = const { Cell::new(0) };
    static ACTIVE_TACTICS: RefCell<Vec<ActiveTactic>> = const { RefCell::new(Vec::new()) };
    static ACTIVE_PHASES: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
    static PENDING_LIMIT: RefCell<Option<PendingLimit>> = const { RefCell::new(None) };
    /// Cooperative verifier checkpoints consumed by nested deterministic-work
    /// measurements. Unlike tactic work, this includes certification and
    /// driver phases, so scaling tests can measure a complete native verifier
    /// transaction without using wall time.
    static WORK_COUNTERS: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
}

struct DeadlineGuard;

impl Drop for DeadlineGuard {
    fn drop(&mut self) {
        DEADLINES.with(|deadlines| {
            deadlines.borrow_mut().pop();
        });
        DEADLINE_CAPTURED.with(|captured| {
            captured.borrow_mut().pop();
        });
    }
}

/// Runs an operation with a cooperative wall-clock deadline. Kernel execution
/// budgets consult this deadline at expression, statement, call, loop, and
/// path checkpoints; verifier phase boundaries consult it as well.
pub fn with_deadline<R>(limit: Duration, operation: impl FnOnce() -> R) -> R {
    DEADLINES.with(|deadlines| deadlines.borrow_mut().push(Instant::now() + limit));
    DEADLINE_CAPTURED.with(|captured| captured.borrow_mut().push(false));
    let _guard = DeadlineGuard;
    operation()
}

struct TacticLimitGuard;

impl Drop for TacticLimitGuard {
    fn drop(&mut self) {
        TACTIC_LIMITS.with(|limits| {
            limits.borrow_mut().pop();
        });
        clear_pending_limit(PendingLimitKind::Time);
    }
}

struct TacticWorkLimitGuard;

impl Drop for TacticWorkLimitGuard {
    fn drop(&mut self) {
        TACTIC_WORK_LIMITS.with(|limits| {
            limits.borrow_mut().pop();
        });
        clear_pending_limit(PendingLimitKind::Work);
    }
}

struct TacticTimeLimitsDisabledGuard;

impl Drop for TacticTimeLimitsDisabledGuard {
    fn drop(&mut self) {
        TACTIC_TIME_LIMITS_DISABLED.with(|depth| depth.set(depth.get() - 1));
    }
}

fn clear_pending_limit(kind: PendingLimitKind) {
    PENDING_LIMIT.with(|pending| {
        let mut pending = pending.borrow_mut();
        if pending.as_ref().is_some_and(|pending| pending.kind == kind) {
            *pending = None;
        }
    });
}

fn tactic_limit_guidance(class: &str) -> &'static str {
    match class {
        "smart" => {
            "; smart search is heuristic, so try a smaller smart tactic or explicit simple tactics"
        }
        "simple" => "; a slow simple tactic is a Click engine bug",
        "control" => "; a slow control tactic is a Click engine bug",
        _ => "",
    }
}

pub fn with_tactic_limits<R>(limits: TacticLimits, operation: impl FnOnce() -> R) -> R {
    TACTIC_LIMITS.with(|installed| installed.borrow_mut().push(limits));
    let _guard = TacticLimitGuard;
    operation()
}

pub fn with_tactic_work_limits<R>(limits: TacticWorkLimits, operation: impl FnOnce() -> R) -> R {
    TACTIC_WORK_LIMITS.with(|installed| installed.borrow_mut().push(limits));
    let _guard = TacticWorkLimitGuard;
    operation()
}

/// Runs fixture verification with deterministic tactic-work budgets but
/// without production's latency-oriented tactic clocks. This does not disable
/// an explicitly installed outer deadline; callers that need hang containment
/// should own it at the process boundary.
pub fn without_tactic_time_limits<R>(operation: impl FnOnce() -> R) -> R {
    TACTIC_TIME_LIMITS_DISABLED.with(|depth| depth.set(depth.get() + 1));
    let _guard = TacticTimeLimitsDisabledGuard;
    operation()
}

pub fn with_default_tactic_limits<R>(operation: impl FnOnce() -> R) -> R {
    if std::env::var_os("CLICK_DISABLE_TACTIC_BUDGETS").is_some() {
        return operation();
    }
    if TACTIC_WORK_LIMITS.with(|limits| limits.borrow().is_empty()) {
        with_tactic_work_limits(TacticWorkLimits::default(), || {
            with_default_tactic_time_limit(operation)
        })
    } else {
        with_default_tactic_time_limit(operation)
    }
}

fn with_default_tactic_time_limit<R>(operation: impl FnOnce() -> R) -> R {
    if TACTIC_TIME_LIMITS_DISABLED.with(|depth| depth.get() > 0) {
        return operation();
    }
    if TACTIC_LIMITS.with(|limits| !limits.borrow().is_empty()) {
        return operation();
    }
    // Concurrent library tests are a deterministic semantic gate. Production
    // builds retain the short real-time cutoff as a separate operational
    // bound; integration fixtures install their outer hang deadline instead.
    #[cfg(test)]
    {
        operation()
    }
    #[cfg(not(test))]
    {
        with_tactic_limits(TacticLimits::default(), operation)
    }
}

pub(crate) fn record_deterministic_work(units: usize) {
    WORK_COUNTERS.with(|counters| {
        for counter in counters.borrow_mut().iter_mut() {
            *counter = counter.saturating_add(units);
        }
    });
}

fn consume_tactic_work(units: usize) -> bool {
    record_deterministic_work(units);
    let exhausted = ACTIVE_TACTICS.with(|active| {
        let mut active = active.borrow_mut();
        let current = active.last_mut()?;
        if current.work_exhausted {
            return Some((
                current.event.clone(),
                current.work_used,
                current.work_limit?,
                current.named_work.clone(),
            ));
        }
        current.work_used = current.work_used.saturating_add(units);
        let limit = current.work_limit?;
        if current.work_used <= limit {
            return None;
        }
        current.work_exhausted = true;
        Some((
            current.event.clone(),
            current.work_used,
            limit,
            current.named_work.clone(),
        ))
    });
    let Some((tactic, used, limit, named_work)) = exhausted else {
        return true;
    };
    let first = PENDING_LIMIT.with(|pending| {
        let mut pending = pending.borrow_mut();
        if pending.is_some() {
            false
        } else {
            *pending = Some(PendingLimit {
                kind: PendingLimitKind::Work,
                message: format!(
                    "tactic `{}` in `{}` exhausted its deterministic {} work budget after {used} units ({limit} limit; statement {}, source tactic {})",
                    tactic.tactic_name,
                    tactic.claim,
                    tactic.class,
                    tactic.statement_index,
                    tactic.source_index,
                ) + &work_attribution_summary(&named_work, used)
                    + tactic_limit_guidance(&tactic.class),
            });
            true
        }
    });
    if first {
        emit(VerificationEvent::TacticWorkBudgetExceeded {
            tactic,
            used,
            limit,
        });
    }
    false
}

/// The top named-operation work consumers for an exhausted budget, or a
/// pointer at how to collect them. Attribution exists only while operation
/// measurement is enabled, so the unmeasured case says how to rerun rather
/// than implying the units are untraceable. Spans still open when the budget
/// dies report their work so far, since their completed attribution does not
/// exist yet.
fn work_attribution_summary(
    named_work: &std::collections::BTreeMap<String, usize>,
    work_used: usize,
) -> String {
    let open = OPEN_OPERATION_SPANS.with(|spans| {
        spans
            .borrow()
            .iter()
            .map(|(name, entry_work)| {
                format!(
                    "`{name}` ({} units in)",
                    work_used.saturating_sub(*entry_work)
                )
            })
            .collect::<Vec<_>>()
    });
    if named_work.is_empty() && open.is_empty() {
        return "\n  named-operation attribution was not collected; rerun under `click profile` or with CLICK_TIMINGS=1 to see where the units went".to_string();
    }
    let mut summary = String::new();
    if !open.is_empty() {
        summary.push_str(&format!("\n  open operation spans: {}", open.join(" > ")));
    }
    if !named_work.is_empty() {
        let mut spans = named_work.iter().collect::<Vec<_>>();
        spans.sort_by(|left, right| right.1.cmp(left.1).then_with(|| left.0.cmp(right.0)));
        let listed = spans
            .iter()
            .take(5)
            .map(|(name, work)| format!("{work} `{name}`"))
            .collect::<Vec<_>>()
            .join(", ");
        summary.push_str(&format!("\n  top completed operation work: {listed}"));
    }
    summary
}

/// Runs one native verifier operation and returns the cooperative work it
/// consumed, including work outside tactic scopes. Measurements nest: an
/// inner counter also contributes to every enclosing counter.
///
/// This is intended for deterministic scaling regressions. It deliberately
/// does not pretend that uninstrumented allocation or copying is free; hot
/// representations must call the ordinary cooperative checkpoint in their
/// traversals so both production budgets and scaling tests see that work.
struct WorkCounterGuard {
    active: bool,
}

impl WorkCounterGuard {
    fn enter() -> Self {
        WORK_COUNTERS.with(|counters| counters.borrow_mut().push(0));
        Self { active: true }
    }

    fn finish(mut self) -> usize {
        self.active = false;
        WORK_COUNTERS.with(|counters| {
            counters
                .borrow_mut()
                .pop()
                .expect("deterministic work counter should remain installed")
        })
    }
}

impl Drop for WorkCounterGuard {
    fn drop(&mut self) {
        if self.active {
            WORK_COUNTERS.with(|counters| {
                counters.borrow_mut().pop();
            });
        }
    }
}

pub fn measure_deterministic_work<R>(operation: impl FnOnce() -> R) -> (R, usize) {
    let counter = WorkCounterGuard::enter();
    let result = operation();
    let work = counter.finish();
    (result, work)
}

pub fn deadline_exceeded() -> bool {
    let work = !consume_tactic_work(1);
    let run = DEADLINES.with(|deadlines| {
        deadlines
            .borrow()
            .iter()
            .min()
            .is_some_and(|deadline| Instant::now() >= *deadline)
    });
    let tactic = ACTIVE_TACTICS.with(|active| {
        let active = active.borrow();
        let active = active.last()?;
        let limit = active.limit?;
        let elapsed = active.exclusive + active.running_since.elapsed();
        (elapsed >= limit).then(|| (active.event.clone(), elapsed, limit))
    });
    if let Some((tactic, elapsed, limit)) = &tactic {
        PENDING_LIMIT.with(|pending| {
            let mut pending = pending.borrow_mut();
            if pending.is_none() {
                *pending = Some(PendingLimit {
                    kind: PendingLimitKind::Time,
                    message: format!(
                        "tactic `{}` in `{}` exceeded its {} {} real-time limit after {:.3}s (statement {}, source tactic {})",
                        tactic.tactic_name,
                        tactic.claim,
                        crate::cli::format_duration(*limit),
                        tactic.class,
                        elapsed.as_secs_f64(),
                        tactic.statement_index,
                        tactic.source_index,
                    ) + tactic_limit_guidance(&tactic.class),
                });
            }
        });
    }
    let pending = PENDING_LIMIT.with(|pending| pending.borrow().as_ref().map(|p| p.kind));
    let exceeded = work || run || tactic.is_some() || pending.is_some();
    if exceeded && !work && pending != Some(PendingLimitKind::Work) {
        capture_active_deadline_work();
    }
    exceeded
}

fn capture_active_deadline_work() {
    let should_capture = DEADLINE_CAPTURED.with(|captured| {
        let mut captured = captured.borrow_mut();
        let Some(current) = captured.last_mut() else {
            return false;
        };
        if *current {
            false
        } else {
            *current = true;
            true
        }
    });
    if !should_capture {
        return;
    }
    let active = ACTIVE_TACTICS
        .with(|tactics| {
            tactics
                .borrow()
                .last()
                .map(|active| ActiveVerificationWork::Tactic(active.event.clone()))
        })
        .or_else(|| {
            ACTIVE_PHASES.with(|phases| {
                phases
                    .borrow()
                    .last()
                    .copied()
                    .map(ActiveVerificationWork::Phase)
            })
        })
        .unwrap_or(ActiveVerificationWork::Driver);
    emit(VerificationEvent::DeadlineExceeded(active));
}

pub fn deadline_context() -> String {
    if let Some(pending) = PENDING_LIMIT.with(|pending| pending.borrow().clone()) {
        return pending.message;
    }
    if DEADLINES.with(|deadlines| {
        deadlines
            .borrow()
            .iter()
            .min()
            .is_some_and(|deadline| Instant::now() >= *deadline)
    }) {
        let active = ACTIVE_TACTICS
            .with(|active| {
                active.borrow().last().map(|active| {
                    format!(
                        "tactic `{}` in `{}`",
                        active.event.tactic_name, active.event.claim
                    )
                })
            })
            .or_else(|| {
                ACTIVE_PHASES
                    .with(|active| active.borrow().last().map(|phase| format!("{phase} phase")))
            })
            .unwrap_or_else(|| "verification driver".to_string());
        return format!("outer wall-clock deadline while running {active}");
    }
    if let Some(active) = ACTIVE_TACTICS.with(|active| active.borrow().last().cloned()) {
        let elapsed = active.exclusive + active.running_since.elapsed();
        let guidance = tactic_limit_guidance(&active.event.class);
        return match active.limit {
            Some(limit) => format!(
                "tactic `{}` in `{}` (class {}, statement {}, source tactic {}, {:.3}s elapsed, {} limit){guidance}",
                active.event.tactic_name,
                active.event.claim,
                active.event.class,
                active.event.statement_index,
                active.event.source_index,
                elapsed.as_secs_f64(),
                crate::cli::format_duration(limit),
            ),
            None => format!(
                "tactic `{}` in `{}` (class {}, statement {}, source tactic {})",
                active.event.tactic_name,
                active.event.claim,
                active.event.class,
                active.event.statement_index,
                active.event.source_index,
            ),
        };
    }
    if let Some(phase) = ACTIVE_PHASES.with(|active| active.borrow().last().copied()) {
        return format!("{phase} phase");
    }
    "verification driver".to_string()
}

/// Describes an ambient verification limit that has already fired, without
/// consuming another deterministic work unit.
///
/// Kernel queries conservatively return `false`/`None` when a cooperative
/// checkpoint observes a deadline or tactic limit. Error construction uses
/// this non-consuming probe so that a semantic-looking diagnostic produced
/// from that conservative answer cannot hide the active limit. Ordinary
/// bounded incompleteness (reasoning fuel, depth guards, and cycle cuts) does
/// not appear here.
pub fn exceeded_verification_limit_context() -> Option<String> {
    if PENDING_LIMIT.with(|pending| pending.borrow().is_some())
        || DEADLINES.with(|deadlines| {
            deadlines
                .borrow()
                .iter()
                .min()
                .is_some_and(|deadline| Instant::now() >= *deadline)
        })
        || ACTIVE_TACTICS.with(|active| {
            let active = active.borrow();
            let Some(active) = active.last() else {
                return false;
            };
            active.work_exhausted
                || active
                    .limit
                    .is_some_and(|limit| active.exclusive + active.running_since.elapsed() >= limit)
        })
    {
        Some(deadline_context())
    } else {
        None
    }
}

/// Runs `operation` while collecting its structured verification events.
pub fn collect<R>(operation: impl FnOnce() -> R) -> (R, Vec<VerificationEvent>) {
    COLLECTORS.with(|collectors| collectors.borrow_mut().push(Vec::new()));
    let result = operation();
    let events = COLLECTORS.with(|collectors| {
        collectors
            .borrow_mut()
            .pop()
            .expect("verification event collector should remain installed")
    });
    (result, events)
}

pub fn enabled() -> bool {
    std::env::var_os("CLICK_TIMINGS").is_some()
        || COLLECTORS.with(|collectors| !collectors.borrow().is_empty())
        || TACTIC_LIMITS.with(|limits| !limits.borrow().is_empty())
        || TACTIC_WORK_LIMITS.with(|limits| !limits.borrow().is_empty())
}

fn operation_measurement_enabled() -> bool {
    std::env::var_os("CLICK_TIMINGS").is_some()
        || COLLECTORS.with(|collectors| !collectors.borrow().is_empty())
}

/// Measures one named nested operation for profiler attribution without
/// making it a new deadline or accounting boundary.
pub fn measure_operation<T>(
    function: &str,
    claim: &str,
    name: impl Into<String>,
    operation: impl FnOnce() -> T,
) -> T {
    if !operation_measurement_enabled() {
        return operation();
    }
    let started = TacticInstant::now();
    let counter = WorkCounterGuard::enter();
    let name = name.into();
    open_operation_span(&name);
    let result = operation();
    close_operation_span();
    let work = counter.finish();
    attribute_tactic_operation_work(&name, work);
    emit(VerificationEvent::OperationFinished {
        function: function.to_string(),
        claim: claim.to_string(),
        name,
        elapsed: started.elapsed(),
        work,
    });
    result
}

/// Adds one finished operation span's work to the innermost active tactic's
/// attribution map, so a later budget exhaustion can name its consumers.
fn attribute_tactic_operation_work(name: &str, work: usize) {
    if work == 0 {
        return;
    }
    ACTIVE_TACTICS.with(|active| {
        if let Some(current) = active.borrow_mut().last_mut() {
            *current.named_work.entry(name.to_string()).or_default() += work;
        }
    });
}

thread_local! {
    /// The stack of operation spans currently open, each with the innermost
    /// tactic's work counter at entry. A budget exhausted mid-span reports
    /// these with their work so far, since their completed attribution does
    /// not exist yet.
    static OPEN_OPERATION_SPANS: RefCell<Vec<(String, usize)>> = const { RefCell::new(Vec::new()) };
}

fn open_operation_span(name: &str) {
    let entry_work = ACTIVE_TACTICS.with(|active| {
        active
            .borrow()
            .last()
            .map(|current| current.work_used)
            .unwrap_or(0)
    });
    OPEN_OPERATION_SPANS.with(|spans| spans.borrow_mut().push((name.to_string(), entry_work)));
}

fn close_operation_span() {
    OPEN_OPERATION_SPANS.with(|spans| {
        spans.borrow_mut().pop();
    });
}

/// RAII form of [`measure_operation`] for code whose control flow cannot be
/// placed in a closure (for example, a loop that mutates and moves outer
/// execution state). Dropping the guard records the completed span.
pub struct OperationTiming {
    measurement: Option<(String, String, String, TacticInstant, WorkCounterGuard)>,
}

impl OperationTiming {
    pub fn new(function: &str, claim: &str, name: impl Into<String>) -> Self {
        Self {
            measurement: operation_measurement_enabled().then(|| {
                let name = name.into();
                open_operation_span(&name);
                (
                    function.to_string(),
                    claim.to_string(),
                    name,
                    TacticInstant::now(),
                    WorkCounterGuard::enter(),
                )
            }),
        }
    }
}

impl Drop for OperationTiming {
    fn drop(&mut self) {
        let Some((function, claim, name, started, counter)) = self.measurement.take() else {
            return;
        };
        close_operation_span();
        let work = counter.finish();
        attribute_tactic_operation_work(&name, work);
        emit(VerificationEvent::OperationFinished {
            function,
            claim,
            name,
            elapsed: started.elapsed(),
            work,
        });
    }
}

pub fn starts_enabled() -> bool {
    std::env::var_os("CLICK_TIMING_STARTS").is_some()
        || COLLECTORS.with(|collectors| !collectors.borrow().is_empty())
        || TACTIC_LIMITS.with(|limits| !limits.borrow().is_empty())
        || TACTIC_WORK_LIMITS.with(|limits| !limits.borrow().is_empty())
}

pub fn emit(mut event: VerificationEvent) {
    match &mut event {
        VerificationEvent::PhaseStarted(name) => {
            ACTIVE_PHASES.with(|active| active.borrow_mut().push(name));
        }
        VerificationEvent::PhaseFinished { name, .. } => {
            ACTIVE_PHASES.with(|active| {
                let mut active = active.borrow_mut();
                if let Some(index) = active.iter().rposition(|candidate| candidate == name) {
                    active.remove(index);
                }
            });
        }
        VerificationEvent::TacticStarted(tactic) => {
            let limit = TACTIC_LIMITS.with(|limits| {
                limits
                    .borrow()
                    .last()
                    .and_then(|limits| limits.for_class(&tactic.class))
            });
            let work_limit = TACTIC_WORK_LIMITS.with(|limits| {
                limits
                    .borrow()
                    .last()
                    .and_then(|limits| limits.for_class(&tactic.class))
            });
            ACTIVE_TACTICS.with(|active| {
                let now = TacticInstant::now();
                let mut active = active.borrow_mut();
                if let Some(parent) = active.last_mut() {
                    parent.exclusive += now.duration_since(parent.running_since);
                }
                active.push(ActiveTactic {
                    event: tactic.clone(),
                    exclusive: Duration::ZERO,
                    started_at: now,
                    running_since: now,
                    limit,
                    work_used: 0,
                    work_limit,
                    work_exhausted: false,
                    named_work: std::collections::BTreeMap::new(),
                });
            });
        }
        VerificationEvent::TacticFinished {
            tactic,
            elapsed,
            work,
        } => {
            ACTIVE_TACTICS.with(|active| {
                let now = TacticInstant::now();
                let mut active = active.borrow_mut();
                if let Some(index) = active
                    .iter()
                    .rposition(|candidate| &candidate.event == tactic)
                {
                    let finished = active.remove(index);
                    *elapsed = now.duration_since(finished.started_at);
                    *work = finished.work_used;
                    let exclusive =
                        finished.exclusive + now.duration_since(finished.running_since);
                    if finished.limit.is_some_and(|limit| exclusive >= limit) {
                        let limit = finished.limit.expect("checked as present");
                        PENDING_LIMIT.with(|pending| {
                            let mut pending = pending.borrow_mut();
                            if pending.is_none() {
                                *pending = Some(PendingLimit {
                                    kind: PendingLimitKind::Time,
                                    message: format!(
                                        "tactic `{}` in `{}` exceeded its {} {} real-time limit after {:.3}s (statement {}, source tactic {})",
                                        finished.event.tactic_name,
                                        finished.event.claim,
                                        crate::cli::format_duration(limit),
                                        finished.event.class,
                                        exclusive.as_secs_f64(),
                                        finished.event.statement_index,
                                        finished.event.source_index,
                                    ) + tactic_limit_guidance(&finished.event.class),
                                });
                            }
                        });
                    }
                    if let Some(parent) = active.last_mut() {
                        parent.running_since = now;
                    }
                }
            });
        }
        VerificationEvent::TacticFailed(tactic) => {
            ACTIVE_TACTICS.with(|active| {
                let now = TacticInstant::now();
                let mut active = active.borrow_mut();
                if let Some(index) = active
                    .iter()
                    .rposition(|candidate| &candidate.event == tactic)
                {
                    active.remove(index);
                    if let Some(parent) = active.last_mut() {
                        parent.running_since = now;
                    }
                }
            });
        }
        VerificationEvent::TacticWorkBudgetExceeded { .. } => {}
        _ => {}
    }
    COLLECTORS.with(|collectors| {
        if let Some(collector) = collectors.borrow_mut().last_mut() {
            collector.push(event.clone());
        }
    });
    if std::env::var_os("CLICK_TIMINGS").is_some() {
        eprintln!("{}", render_legacy(&event));
    }
}

fn tactic_fields(tactic: &TacticEvent) -> String {
    format!(
        "{} {} {} class {} statement {} source {}",
        tactic.claim,
        tactic.tactic_index,
        tactic.tactic_name,
        tactic.class,
        tactic.statement_index,
        tactic.source_index,
    )
}

fn render_legacy(event: &VerificationEvent) -> String {
    match event {
        VerificationEvent::Source(path) => format!("click timing: source {}", path.display()),
        VerificationEvent::PhaseStarted(name) => format!("click timing: started phase {name}"),
        VerificationEvent::PhaseFinished { name, elapsed } => {
            format!("click timing: phase {name} {:.6}s", elapsed.as_secs_f64())
        }
        VerificationEvent::TacticStarted(tactic) => {
            format!("click timing: started tactic {}", tactic_fields(tactic))
        }
        VerificationEvent::TacticFinished {
            tactic,
            elapsed,
            work,
        } => format!(
            "click timing: tactic {} {:.6}s work {work}",
            tactic_fields(tactic),
            elapsed.as_secs_f64()
        ),
        VerificationEvent::TacticFailed(tactic) => {
            format!("click timing: failed tactic {}", tactic_fields(tactic))
        }
        VerificationEvent::TacticWorkBudgetExceeded {
            tactic,
            used,
            limit,
        } => format!(
            "click timing: tactic work budget exceeded {} used {used} limit {limit}",
            tactic_fields(tactic)
        ),
        VerificationEvent::FunctionFinished { name, elapsed } => {
            format!(
                "click timing: function {name} {:.3}s",
                elapsed.as_secs_f64()
            )
        }
        VerificationEvent::ContractExecutionFinished { function, elapsed } => format!(
            "click timing: contract execution {function} {:.6}s",
            elapsed.as_secs_f64()
        ),
        VerificationEvent::ContractClaimsFinished { function, elapsed } => format!(
            "click timing: contract claims {function} {:.6}s",
            elapsed.as_secs_f64()
        ),
        VerificationEvent::ClaimPathsPrepared {
            function,
            count,
            elapsed,
        } => format!(
            "click timing: claim paths {function} prepared {count} in {:.6}s",
            elapsed.as_secs_f64()
        ),
        VerificationEvent::ClaimFinished {
            function,
            key,
            elapsed,
        } => format!(
            "click timing: claim {function} {key} {:.6}s",
            elapsed.as_secs_f64()
        ),
        VerificationEvent::OperationFinished {
            function,
            claim,
            name,
            elapsed,
            work,
        } => format!(
            "click timing: operation {name} {function} {claim} {:.6}s {work} work",
            elapsed.as_secs_f64(),
        ),
        VerificationEvent::DeadlineExceeded(active) => {
            format!("click timing: deadline exceeded in {active:?}")
        }
        VerificationEvent::Diagnostic(message) => format!("click timing: {message}"),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn nested_collectors_are_independent() {
        let (_, outer) = collect(|| {
            emit(VerificationEvent::Diagnostic("outer one".to_string()));
            let (_, inner) = collect(|| {
                emit(VerificationEvent::Diagnostic("inner".to_string()));
            });
            assert_eq!(inner.len(), 1);
            emit(VerificationEvent::Diagnostic("outer two".to_string()));
        });
        assert_eq!(outer.len(), 2);
    }

    fn tactic(class: &str, index: usize) -> TacticEvent {
        TacticEvent {
            claim: "deadline.contract".to_string(),
            tactic_index: index,
            tactic_name: format!("{class}_work"),
            class: class.to_string(),
            statement_index: index,
            source_index: index,
        }
    }

    #[test]
    fn every_tactic_class_has_an_enforced_deadline() {
        for class in ["simple", "smart", "control"] {
            let limits = TacticLimits {
                simple: Duration::ZERO,
                smart: Duration::ZERO,
                control: Duration::ZERO,
            };
            with_tactic_limits(limits, || {
                let tactic = tactic(class, 0);
                emit(VerificationEvent::TacticStarted(tactic.clone()));
                assert!(deadline_exceeded(), "{class} should be bounded");
                assert!(deadline_context().contains(class));
                emit(VerificationEvent::TacticFinished {
                    tactic,
                    elapsed: Duration::ZERO,
                    work: 0,
                });
            });
        }
    }

    #[test]
    fn semantic_unit_tests_use_work_limits_without_production_time_limits() {
        with_default_tactic_limits(|| {
            assert!(
                TACTIC_LIMITS.with(|limits| limits.borrow().is_empty()),
                "semantic unit tests should install a time limit only when testing one"
            );
            assert_eq!(
                TACTIC_WORK_LIMITS.with(|limits| limits.borrow().last().copied()),
                Some(TacticWorkLimits::default()),
                "semantic unit tests should retain deterministic tactic bounds"
            );
        });
    }

    #[test]
    fn every_tactic_class_has_a_deterministic_work_budget() {
        let limits = TacticWorkLimits {
            simple: 1,
            smart: 1,
            control: 1,
        };
        for class in ["simple", "smart", "control"] {
            let (_, events) = with_tactic_work_limits(limits, || {
                collect(|| {
                    let tactic = tactic(class, 0);
                    emit(VerificationEvent::TacticStarted(tactic.clone()));
                    assert!(!deadline_exceeded(), "one unit should fit");
                    assert!(deadline_exceeded(), "the second unit should exhaust");
                    assert!(deadline_context().contains("deterministic"));
                    emit(VerificationEvent::TacticFailed(tactic));
                })
            });
            assert!(events.iter().any(|event| matches!(
                event,
                VerificationEvent::TacticWorkBudgetExceeded {
                    tactic,
                    used: 2,
                    limit: 1,
                } if tactic.class == class
            )));
            assert!(
                !events
                    .iter()
                    .any(|event| matches!(event, VerificationEvent::DeadlineExceeded(_))),
                "work exhaustion must not masquerade as a real-time deadline"
            );
        }
    }

    #[test]
    fn exhausted_work_budget_names_its_operation_spans() {
        let limits = TacticWorkLimits {
            simple: 1000,
            smart: 4,
            control: 1000,
        };
        with_tactic_work_limits(limits, || {
            let ((), _events) = collect(|| {
                let tactic = tactic("smart", 0);
                emit(VerificationEvent::TacticStarted(tactic.clone()));
                measure_operation("kernel", "test", "completed probe span", || {
                    assert!(!deadline_exceeded(), "the first unit should fit");
                });
                measure_operation("kernel", "test", "exhausting probe span", || {
                    while !deadline_exceeded() {}
                    let context = deadline_context();
                    assert!(
                        context.contains("exhausting probe span"),
                        "the open span at exhaustion should be named: {context}"
                    );
                    assert!(
                        context.contains("completed probe span"),
                        "completed spans before exhaustion should be named: {context}"
                    );
                });
                emit(VerificationEvent::TacticFailed(tactic));
            });
        });
    }

    #[test]
    fn nested_tactic_work_is_not_charged_to_its_control_parent() {
        let limits = TacticWorkLimits {
            simple: 1,
            smart: 1,
            control: 1,
        };
        with_tactic_work_limits(limits, || {
            let parent = tactic("control", 0);
            let child = tactic("simple", 1);
            emit(VerificationEvent::TacticStarted(parent.clone()));
            emit(VerificationEvent::TacticStarted(child.clone()));
            assert!(!deadline_exceeded());
            emit(VerificationEvent::TacticFinished {
                tactic: child,
                elapsed: Duration::ZERO,
                work: 0,
            });
            assert!(
                !deadline_exceeded(),
                "the parent should still have its own first unit"
            );
            assert!(deadline_exceeded());
            emit(VerificationEvent::TacticFailed(parent));
        });
    }

    #[test]
    fn sleeping_does_not_consume_deterministic_tactic_work() {
        let limits = TacticWorkLimits {
            simple: 1,
            smart: 1,
            control: 1,
        };
        let tactic = tactic("smart", 0);
        let (_, events) = with_tactic_work_limits(limits, || {
            collect(|| {
                emit(VerificationEvent::TacticStarted(tactic.clone()));
                std::thread::sleep(Duration::from_millis(10));
                assert!(!deadline_exceeded());
                emit(VerificationEvent::TacticFinished {
                    tactic: tactic.clone(),
                    elapsed: Duration::ZERO,
                    work: 0,
                });
            })
        });
        assert!(events.iter().any(|event| matches!(
            event,
            VerificationEvent::TacticFinished {
                tactic: finished,
                work: 1,
                ..
            } if finished == &tactic
        )));
    }

    #[test]
    fn control_deadline_excludes_nested_tactic_time() {
        let limits = TacticLimits {
            simple: Duration::from_secs(1),
            smart: Duration::from_secs(1),
            control: Duration::from_millis(50),
        };
        with_tactic_limits(limits, || {
            let control = tactic("control", 0);
            let child = tactic("simple", 1);
            emit(VerificationEvent::TacticStarted(control.clone()));
            emit(VerificationEvent::TacticStarted(child.clone()));
            std::thread::sleep(Duration::from_millis(100));
            emit(VerificationEvent::TacticFinished {
                tactic: child,
                elapsed: Duration::from_millis(100),
                work: 0,
            });
            assert!(
                !deadline_exceeded(),
                "the control container must not inherit its child's time"
            );
            emit(VerificationEvent::TacticFinished {
                tactic: control,
                elapsed: Duration::from_millis(100),
                work: 0,
            });
        });
    }

    #[cfg(unix)]
    #[test]
    fn tactic_clock_does_not_charge_descheduled_wall_time() {
        let start = TacticInstant::now();
        assert!(start.thread_cpu.is_some());
        std::thread::sleep(Duration::from_millis(50));
        assert!(
            start.elapsed() < Duration::from_millis(25),
            "a sleeping verifier thread should consume negligible tactic budget"
        );
    }

    #[cfg(unix)]
    #[test]
    fn collected_tactic_duration_uses_the_tactic_cpu_clock() {
        let tactic = tactic("smart", 0);
        let (_, events) = collect(|| {
            emit(VerificationEvent::TacticStarted(tactic.clone()));
            std::thread::sleep(Duration::from_millis(50));
            emit(VerificationEvent::TacticFinished {
                tactic: tactic.clone(),
                elapsed: Duration::from_secs(1),
                work: 0,
            });
        });
        let elapsed = events
            .iter()
            .find_map(|event| match event {
                VerificationEvent::TacticFinished {
                    tactic: finished,
                    elapsed,
                    ..
                } if finished == &tactic => Some(*elapsed),
                _ => None,
            })
            .expect("the finished tactic should be collected");
        assert!(
            elapsed < Duration::from_millis(25),
            "structured tactic timing should exclude descheduled wall time: {elapsed:?}"
        );
    }

    #[test]
    fn project_deadline_captures_each_active_tactic_class_before_unwinding() {
        let limits = TacticLimits {
            simple: Duration::from_secs(1),
            smart: Duration::from_secs(1),
            control: Duration::from_secs(1),
        };
        for class in ["simple", "smart", "control"] {
            let (_, events) = with_deadline(Duration::ZERO, || {
                with_tactic_limits(limits, || {
                    collect(|| {
                        let active = tactic(class, 0);
                        emit(VerificationEvent::TacticStarted(active.clone()));
                        assert!(deadline_exceeded());
                        emit(VerificationEvent::TacticFailed(active));
                    })
                })
            });
            assert!(events.iter().any(|event| matches!(
                event,
                VerificationEvent::DeadlineExceeded(ActiveVerificationWork::Tactic(active))
                    if active.class == class
            )));
        }
    }

    #[test]
    fn project_deadline_captures_named_verifier_phases_before_scope_cleanup() {
        for phase in ["frontend", "environment", "certification", "verifier-core"] {
            let (_, events) = with_deadline(Duration::ZERO, || {
                collect(|| {
                    emit(VerificationEvent::PhaseStarted(phase));
                    assert!(deadline_exceeded());
                    assert!(deadline_context().contains("outer wall-clock deadline"));
                    emit(VerificationEvent::PhaseFinished {
                        name: phase,
                        elapsed: Duration::ZERO,
                    });
                })
            });
            assert!(events.iter().any(|event| matches!(
                event,
                VerificationEvent::DeadlineExceeded(ActiveVerificationWork::Phase(active))
                    if active == &phase
            )));
        }
    }

    #[test]
    fn deterministic_work_measurements_include_nested_and_driver_checkpoints() {
        let (((), inner), outer) = measure_deterministic_work(|| {
            assert!(!deadline_exceeded());
            let measured = measure_deterministic_work(|| {
                assert!(!deadline_exceeded());
                assert!(!deadline_exceeded());
            });
            assert!(!deadline_exceeded());
            measured
        });

        assert_eq!(inner, 2);
        assert_eq!(outer, 4);
    }

    #[test]
    fn named_operation_events_include_deterministic_work() {
        let (_, events) = collect(|| {
            measure_operation("function", "claim", "measured operation", || {
                assert!(!deadline_exceeded());
                assert!(!deadline_exceeded());
            });
            let _timing = OperationTiming::new("function", "claim", "guarded operation");
            assert!(!deadline_exceeded());
        });

        assert!(events.iter().any(|event| matches!(
            event,
            VerificationEvent::OperationFinished { name, work: 2, .. }
                if name == "measured operation"
        )));
        assert!(events.iter().any(|event| matches!(
            event,
            VerificationEvent::OperationFinished { name, work: 1, .. }
                if name == "guarded operation"
        )));
    }
}

/// Why opaque-contract certification could not reuse a checked artifact from
/// claim finishing. With artifacts supplied it then produces no paths; only a
/// kernel caller that supplied none gets the kernel's own body execution.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ContractFallback {
    /// No artifact for this function had matching execution metadata.
    NoArtifact,
    /// An artifact at the contract entry state assumed a predicate identity
    /// the reconstructed contract context cannot derive.
    UnauthorizedPredicatePremise,
    /// An artifact at the contract entry state assumed a resource containment
    /// or separation fact the contract context cannot derive.
    UnauthorizedResourcePremise,
    /// An artifact at the contract entry state assumed some other fact the
    /// contract context cannot derive.
    UnauthorizedPremise,
    /// Every metadata-matching artifact started at a different entry state.
    EntryStateDelta,
}

/// The process-wide count of body reruns by reason since the last take.
pub type BodyRerunCensus = std::collections::BTreeMap<ContractFallback, usize>;

static BODY_RERUN_CENSUS: std::sync::Mutex<BodyRerunCensus> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

fn body_rerun_census() -> std::sync::MutexGuard<'static, BodyRerunCensus> {
    BODY_RERUN_CENSUS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

pub fn record_contract_fallback(cause: ContractFallback) {
    *body_rerun_census().entry(cause).or_default() += 1;
}

/// Takes and clears the census. Verification of one corpus runs serially in
/// the fixture harnesses, so the census is theirs alone there.
pub fn take_body_rerun_census() -> BodyRerunCensus {
    std::mem::take(&mut *body_rerun_census())
}

/// The ratchet: `None` when the census equals the pinned baseline exactly,
/// otherwise a message listing every reason whose count rose (a new rerun,
/// which must not land) or fell (lower the pin so it cannot rise back).
pub fn body_rerun_census_mismatch(
    census: &BodyRerunCensus,
    expected_contract: &[(ContractFallback, usize)],
) -> Option<String> {
    fn diff<K: Copy + Ord + std::fmt::Debug>(
        label: &str,
        actual: &std::collections::BTreeMap<K, usize>,
        expected: &[(K, usize)],
        report: &mut Vec<String>,
    ) {
        let expected = expected
            .iter()
            .copied()
            .collect::<std::collections::BTreeMap<_, _>>();
        let keys = actual
            .keys()
            .chain(expected.keys())
            .copied()
            .collect::<std::collections::BTreeSet<_>>();
        for key in keys {
            let was = expected.get(&key).copied().unwrap_or(0);
            let now = actual.get(&key).copied().unwrap_or(0);
            if now > was {
                report.push(format!(
                    "{label} {key:?} rose from {was} to {now}: a proof that used to reuse its checked execution now reruns its body"
                ));
            } else if now < was {
                report.push(format!(
                    "{label} {key:?} fell from {was} to {now}: lower its pin to {now}"
                ));
            }
        }
        if actual.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>()
            != expected.iter().map(|(k, v)| (*k, *v)).collect::<Vec<_>>()
        {
            report.push(format!("{label} census now: {actual:?}"));
        }
    }
    let mut report = Vec::new();
    diff("contract fallback", census, expected_contract, &mut report);
    (!report.is_empty()).then(|| report.join("\n"))
}

#[cfg(test)]
mod body_rerun_census_tests {
    use super::*;

    #[test]
    fn ratchet_reports_rises_and_falls() {
        let census: BodyRerunCensus = [(ContractFallback::EntryStateDelta, 1)]
            .into_iter()
            .collect();
        assert_eq!(
            body_rerun_census_mismatch(&census, &[(ContractFallback::EntryStateDelta, 1)]),
            None
        );
        let rise = body_rerun_census_mismatch(&census, &[]).expect("a rise is reported");
        assert!(rise.contains("EntryStateDelta rose from 0 to 1"), "{rise}");
        let fall = body_rerun_census_mismatch(&census, &[(ContractFallback::EntryStateDelta, 3)])
            .expect("a fall is reported");
        assert!(fall.contains("EntryStateDelta fell from 3 to 1"), "{fall}");
    }
}
