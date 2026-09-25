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

/// One tactic's deterministic work, as its budget was charged: exclusive of
/// nested tactics, and recorded whether the tactic finished or failed.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TacticWorkSample {
    pub tactic: TacticEvent,
    pub work: usize,
    pub failed: bool,
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
    /// Deterministic work units available to one simple tactic.
    pub simple: usize,
    /// Deterministic work units available to one smart tactic.
    pub smart: usize,
    /// Deterministic work units available to one control tactic,
    /// excluding work performed by its nested tactics.
    pub control: usize,
}

impl Default for TacticWorkLimits {
    /// The deterministic work budget is the primary per-tactic bound. It is
    /// charged by every unit of recorded verifier work
    /// (`record_deterministic_work`, and the cooperative checkpoints, which
    /// record through the same path), so the same source spends the same
    /// units on any machine under any load, and a scaling measurement and a
    /// budget verdict count the same units.
    ///
    /// Calibration (2026-09-25, base `57ee1ebf`: the unified work counter
    /// plus the constant-normalization classes that removed the cubic
    /// call-step ensure lowering; `scripts/measure-tactic-work.sh`, which
    /// runs both fixture harnesses with budgets disabled so no cost is
    /// clipped): the corpus is 35 example sidecars and 2,084 mdtests,
    /// counting every tactic including the gate's generated-certificate
    /// checks.
    ///
    /// - simple: 7,990 tactics, p95 = 1,651, p99 = 5,368, second-largest =
    ///   71,392, max = 83,759 (arena `arena_pipeline` `step`s at
    ///   arena_cells.click:4041 and :5092). 750,000 gives the maximum 9.0x
    ///   margin and the second-largest 10.5x; every simple tactic is now at
    ///   least 9x under the budget. The budget is kept at 750,000 rather than
    ///   lowered so that the arena's call steps, which are ordinary
    ///   contract applications, keep the documented 10x headroom.
    /// - smart: 11,280 tactics, p95 = 3,340, p99 = 20,565, second-largest =
    ///   627,309, max = 671,115 (both owned-vector `vector_copy`'s `simp` at
    ///   vector.click:130, run twice). 2,000,000 gives it 3.0x; below it sit
    ///   an mdtest `close_invariants` (494,596), the arena `have`s (450,033
    ///   down to 198,757), branching_graph_dfs's `simp` (263,926), and
    ///   copy_n_segment_invariant's `simp` (218,751); every other smart
    ///   tactic is below 200,000 (10x).
    /// - control: 1,778 tactics, p95 = 5,523, p99 = 33,069, second-largest =
    ///   541,736, max = 745,173 (arena `arena_pipeline` `have`s at
    ///   arena_cells.click:3440 and :3134). 2,500,000 gives the maximum 3.4x;
    ///   the only other control tactic above 250,000 (10x) is the arena
    ///   `have` at :3591 (422,691).
    ///
    /// The tactics named above are the corpus's genuinely slow steps, not
    /// headroom to spend. Changing a budget requires a fresh run of the
    /// script over BOTH the examples and the mdtests and a documented
    /// reason; it is never a way to make one proof pass.
    fn default() -> Self {
        Self {
            simple: 750_000,
            smart: 2_000_000,
            control: 2_500_000,
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
    /// Budget-calibration sinks: each ended tactic's charged work, without
    /// the cost of collecting every verification event.
    static TACTIC_WORK_SINKS: RefCell<Vec<Vec<TacticWorkSample>>> = const { RefCell::new(Vec::new()) };
    /// Deterministic work consumed by nested measurements. Every unit that
    /// charges a tactic budget also lands here; unlike tactic work, this
    /// includes certification and driver phases outside any tactic, so
    /// scaling tests can measure a complete native verifier transaction
    /// without using wall time.
    static WORK_COUNTERS: RefCell<Vec<usize>> = const { RefCell::new(Vec::new()) };
    /// A checked variable collector turns each of its deterministic node
    /// charges into a full checkpoint, so it can stop traversing as soon as
    /// any limit fires. The collector itself lives in the kernel reasoning
    /// module; outside this scope a record charges the same budget but does
    /// not interrupt its caller.
    static CHECKED_COLLECTION_DEPTH: Cell<usize> = const { Cell::new(0) };
    static CHECKED_COLLECTION_EXHAUSTED: Cell<bool> = const { Cell::new(false) };
    /// Monotonic count of checked-collector entry attempts. Unlike tactic
    /// work, this remains observable after exhaustion so regressions can
    /// prove that sibling traversal stopped rather than merely becoming
    /// uncharged.
    #[cfg(test)]
    static CHECKED_COLLECTION_ATTEMPTS: Cell<usize> = const { Cell::new(0) };
}

/// Makes deterministic work recorded by variable collectors a checkpoint
/// (budget and wall clock) until the guard is dropped. Nested scopes share the
/// outer exhaustion state and do not reset it.
pub(crate) struct CheckedCollectionScope;

impl CheckedCollectionScope {
    pub(crate) fn new() -> Self {
        CHECKED_COLLECTION_DEPTH.with(|depth| {
            if depth.get() == 0 {
                CHECKED_COLLECTION_EXHAUSTED.with(|exhausted| exhausted.set(false));
                #[cfg(test)]
                CHECKED_COLLECTION_ATTEMPTS.with(|attempts| attempts.set(0));
            }
            depth.set(depth.get().saturating_add(1));
        });
        Self
    }
}

impl Drop for CheckedCollectionScope {
    fn drop(&mut self) {
        CHECKED_COLLECTION_DEPTH.with(|depth| {
            depth.set(depth.get().saturating_sub(1));
        });
    }
}

pub(crate) fn checked_collection_exhausted() -> bool {
    CHECKED_COLLECTION_DEPTH
        .with(|depth| depth.get() > 0 && CHECKED_COLLECTION_EXHAUSTED.with(Cell::get))
}

#[cfg(test)]
pub(crate) fn checked_collection_attempts() -> usize {
    CHECKED_COLLECTION_ATTEMPTS.with(Cell::get)
}

#[cfg(test)]
pub(crate) fn record_checked_collection_attempt() {
    CHECKED_COLLECTION_DEPTH.with(|depth| {
        if depth.get() > 0 {
            CHECKED_COLLECTION_ATTEMPTS.with(|attempts| {
                attempts.set(attempts.get().saturating_add(1));
            });
        }
    });
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

/// Records `units` of deterministic verifier work.
///
/// This is the one accounting path: every unit charges each enclosing
/// [`measure_deterministic_work`] counter and the innermost active tactic's
/// work budget, whether it arrives here or through a cooperative checkpoint
/// ([`deadline_exceeded`], [`deadline_exceeded_with_work`]). Recording does
/// not interrupt the caller: an exhausted budget becomes a pending limit
/// that the next checkpoint reports, and the verifier checks for one after
/// every function, so no tactic can finish green past its budget. A
/// checkpoint additionally consults the wall-clock deadlines.
///
/// Inside a [`CheckedCollectionScope`] each record is itself a checkpoint,
/// and once one reports exhaustion the rest of the scope stops charging so
/// the collector can unwind.
pub(crate) fn record_deterministic_work(units: usize) {
    if CHECKED_COLLECTION_DEPTH.with(|depth| depth.get() > 0) {
        if CHECKED_COLLECTION_EXHAUSTED.with(Cell::get) {
            return;
        }
        if deadline_exceeded_with_work(units) {
            CHECKED_COLLECTION_EXHAUSTED.with(|flag| flag.set(true));
        }
        return;
    }
    charge_deterministic_work(units);
}

/// Charges `units` to every scaling counter and to the innermost active
/// tactic's budget. Returns `false` when that budget is exhausted; the first
/// exhaustion leaves a pending work limit whose message names the tactic,
/// its units, and where they went, and emits one
/// [`VerificationEvent::TacticWorkBudgetExceeded`].
fn charge_deterministic_work(units: usize) -> bool {
    WORK_COUNTERS.with(|counters| {
        for counter in counters.borrow_mut().iter_mut() {
            *counter = counter.saturating_add(units);
        }
    });
    let exhausted = ACTIVE_TACTICS.with(|active| {
        let mut active = active.borrow_mut();
        let current = active.last_mut()?;
        if current.work_exhausted {
            // Already reported: stay exhausted without rebuilding the
            // message on every later record, unless the pending limit was
            // cleared underneath the still-running tactic.
            if PENDING_LIMIT.with(|pending| pending.borrow().is_some()) {
                return Some(None);
            }
            return Some(Some((
                current.event.clone(),
                current.work_used,
                current.work_limit?,
                current.named_work.clone(),
            )));
        }
        current.work_used = current.work_used.saturating_add(units);
        let limit = current.work_limit?;
        if current.work_used <= limit {
            return None;
        }
        current.work_exhausted = true;
        Some(Some((
            current.event.clone(),
            current.work_used,
            limit,
            current.named_work.clone(),
        )))
    });
    let Some(exhausted) = exhausted else {
        return true;
    };
    let Some((tactic, used, limit, named_work)) = exhausted else {
        return false;
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
/// This is intended for deterministic scaling regressions. It counts exactly
/// the units the tactic budgets are charged, so a scaling measurement and a
/// budget verdict cannot disagree about a step's cost. It deliberately does
/// not pretend that uninstrumented allocation or copying is free; hot
/// representations must record their traversal work so both see it.
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
    deadline_exceeded_with_work(1)
}

/// Bound one magnitude-dependent operation even during setup, before a tactic
/// starts. An outer deadline cannot interrupt a single BigInt allocation, and
/// installing tactic-limit configuration alone does not create an active tactic.
/// Setup uses the configured simple-operation allowance; active tactics retain
/// their own allowance and also consume their cumulative work budget.
pub(crate) fn numeric_operation_work_exceeded(units: usize) -> bool {
    let active_limit =
        ACTIVE_TACTICS.with(|active| active.borrow().last().and_then(|active| active.work_limit));
    let limit = active_limit.unwrap_or_else(|| {
        TACTIC_WORK_LIMITS.with(|limits| limits.borrow().last().copied().unwrap_or_default().simple)
    });
    deadline_exceeded_with_work(units) || units > limit
}

/// Check the active limits before an operation with an explicit work cost.
/// Numeric kernels use this for magnitude-dependent work: a BigInt product
/// must consume its allowance before multiplication, not just count a unit
/// after the result has already been allocated.
pub(crate) fn deadline_exceeded_with_work(units: usize) -> bool {
    let work = !charge_deterministic_work(units);
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

/// Runs `operation` while recording the charged work of every tactic that
/// ends inside it. Tactic accounting runs exactly as under a budget, so this
/// is how budgets are calibrated: install no work limits
/// (`CLICK_DISABLE_TACTIC_BUDGETS`) so no cost is clipped, and read the work
/// every tactic would have charged. Operation spans are not measured.
pub fn collect_tactic_work<R>(operation: impl FnOnce() -> R) -> (R, Vec<TacticWorkSample>) {
    TACTIC_WORK_SINKS.with(|sinks| sinks.borrow_mut().push(Vec::new()));
    let result = operation();
    let samples = TACTIC_WORK_SINKS.with(|sinks| {
        sinks
            .borrow_mut()
            .pop()
            .expect("tactic work sink should remain installed")
    });
    (result, samples)
}

fn record_tactic_work_sample(tactic: &TacticEvent, work: usize, failed: bool) {
    TACTIC_WORK_SINKS.with(|sinks| {
        if let Some(sink) = sinks.borrow_mut().last_mut() {
            sink.push(TacticWorkSample {
                tactic: tactic.clone(),
                work,
                failed,
            });
        }
    });
}

fn tactic_work_sink_installed() -> bool {
    TACTIC_WORK_SINKS.with(|sinks| !sinks.borrow().is_empty())
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
        || tactic_work_sink_installed()
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
        || tactic_work_sink_installed()
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
                    record_tactic_work_sample(&finished.event, finished.work_used, false);
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
                    let failed = active.remove(index);
                    record_tactic_work_sample(&failed.event, failed.work_used, true);
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
    fn weighted_work_consumes_the_active_tactic_budget_before_an_operation() {
        let limits = TacticWorkLimits {
            simple: 100,
            smart: 100,
            control: 100,
        };
        for class in ["simple", "smart", "control"] {
            let (((), work), events) = with_tactic_work_limits(limits, || {
                collect(|| {
                    measure_deterministic_work(|| {
                        let tactic = tactic(class, 0);
                        emit(VerificationEvent::TacticStarted(tactic.clone()));
                        assert!(!deadline_exceeded_with_work(60));
                        assert!(!deadline_exceeded_with_work(40));
                        assert!(deadline_exceeded_with_work(1));
                        assert!(deadline_context().contains("deterministic"));
                        emit(VerificationEvent::TacticFailed(tactic));
                    })
                })
            });
            assert_eq!(work, 101);
            assert!(events.iter().any(|event| matches!(
                event,
                VerificationEvent::TacticWorkBudgetExceeded {
                    tactic,
                    used: 101,
                    limit: 100,
                } if tactic.class == class
            )));
        }
    }

    #[test]
    fn recorded_work_consumes_the_active_tactic_budget() {
        let limits = TacticWorkLimits {
            simple: 10,
            smart: 10,
            control: 10,
        };
        for class in ["simple", "smart", "control"] {
            let tactic = tactic(class, 0);
            let ((((), measured), samples), events) = with_tactic_work_limits(limits, || {
                collect(|| {
                    collect_tactic_work(|| {
                        measure_deterministic_work(|| {
                            emit(VerificationEvent::TacticStarted(tactic.clone()));
                            record_deterministic_work(9);
                            assert!(
                                exceeded_verification_limit_context().is_none(),
                                "nine recorded units fit a ten-unit budget"
                            );
                            assert!(!deadline_exceeded(), "the tenth unit still fits");
                            assert!(
                                deadline_exceeded(),
                                "recorded units and checkpoint units share one budget"
                            );
                            emit(VerificationEvent::TacticFailed(tactic.clone()));
                        })
                    })
                })
            });
            assert_eq!(measured, 11, "the scaling counter sees the same units");
            assert_eq!(
                samples,
                vec![TacticWorkSample {
                    tactic: tactic.clone(),
                    work: 11,
                    failed: true,
                }]
            );
            assert!(events.iter().any(|event| matches!(
                event,
                VerificationEvent::TacticWorkBudgetExceeded {
                    used: 11,
                    limit: 10,
                    ..
                }
            )));
        }
    }

    #[test]
    fn exhaustion_inside_a_record_is_reported_once_at_the_next_checkpoint() {
        let limits = TacticWorkLimits {
            simple: 100,
            smart: 100,
            control: 100,
        };
        let tactic = tactic("simple", 3);
        let (_, events) = with_tactic_work_limits(limits, || {
            collect(|| {
                emit(VerificationEvent::TacticStarted(tactic.clone()));
                record_deterministic_work(60);
                record_deterministic_work(60);
                let context = exceeded_verification_limit_context()
                    .expect("a record past the budget leaves a pending limit");
                assert!(
                    context.contains(
                        "exhausted its deterministic simple work budget after 120 units (100 limit"
                    ),
                    "{context}"
                );
                assert!(
                    context.contains("a slow simple tactic is a Click engine bug"),
                    "{context}"
                );
                // Later records and checkpoints keep failing without
                // re-reporting or growing the reported cost.
                record_deterministic_work(1_000);
                assert!(deadline_exceeded());
                assert!(deadline_exceeded_with_work(5));
                assert_eq!(deadline_context(), context);
                emit(VerificationEvent::TacticFailed(tactic.clone()));
            })
        });
        let reports = events
            .iter()
            .filter(|event| matches!(event, VerificationEvent::TacticWorkBudgetExceeded { .. }))
            .collect::<Vec<_>>();
        assert_eq!(
            reports,
            vec![&VerificationEvent::TacticWorkBudgetExceeded {
                tactic,
                used: 120,
                limit: 100,
            }]
        );
        assert!(
            !events
                .iter()
                .any(|event| matches!(event, VerificationEvent::DeadlineExceeded(_))),
            "work exhaustion must not masquerade as a real-time deadline"
        );
    }

    #[test]
    fn recorded_work_outside_a_tactic_charges_only_the_scaling_counter() {
        let limits = TacticWorkLimits {
            simple: 1,
            smart: 1,
            control: 1,
        };
        let ((), work) = with_tactic_work_limits(limits, || {
            measure_deterministic_work(|| {
                record_deterministic_work(50);
                assert!(exceeded_verification_limit_context().is_none());
                assert!(!deadline_exceeded());
            })
        });
        assert_eq!(work, 51);
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
/// claim finishing. It then produces no paths and the reason; certification
/// never executes a body itself.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum ArtifactReuseRejection {
    /// No supplied artifact for this function had matching execution
    /// metadata, or none was supplied.
    NoMatchingArtifact,
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

/// The process-wide count of artifact reuse rejections by reason since the last take.
pub type ArtifactReuseRejectionCensus = std::collections::BTreeMap<ArtifactReuseRejection, usize>;

static ARTIFACT_REUSE_REJECTION_CENSUS: std::sync::Mutex<ArtifactReuseRejectionCensus> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

fn artifact_reuse_rejection_census() -> std::sync::MutexGuard<'static, ArtifactReuseRejectionCensus>
{
    ARTIFACT_REUSE_REJECTION_CENSUS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
}

pub fn record_artifact_reuse_rejection(cause: ArtifactReuseRejection) {
    *artifact_reuse_rejection_census().entry(cause).or_default() += 1;
}

/// Takes and clears the census. Verification of one corpus runs serially in
/// the fixture harnesses, so the census is theirs alone there.
pub fn take_artifact_reuse_rejection_census() -> ArtifactReuseRejectionCensus {
    std::mem::take(&mut *artifact_reuse_rejection_census())
}

/// How many derivation edges were dropped for pointing at a snapshot that is
/// not younger than their result, by edge kind and by whether the result was
/// its own base.
///
/// A self edge (`"Store (self)"`) is the documented no-op: the snapshot did
/// not change, so there is nothing to record. A *backwards* edge is not:
/// the step ended on an older node, which keeps that node's history and
/// leaves everything in between recorded nowhere. Counting the two apart is
/// how a corpus run says whether any producer still does the second.
pub type BackwardsMemoryDerivationCensus = std::collections::BTreeMap<&'static str, usize>;

static BACKWARDS_MEMORY_DERIVATION_CENSUS: std::sync::Mutex<BackwardsMemoryDerivationCensus> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

pub(crate) fn record_backwards_memory_derivation(kind: &'static str, onto_itself: bool) {
    // Only the genuinely backwards ones are counted. A self edge is the
    // snapshot saying it did not change, which every store of an already
    // stored value produces and which loses no history.
    if onto_itself {
        return;
    }
    *BACKWARDS_MEMORY_DERIVATION_CENSUS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .entry(kind)
        .or_default() += 1;
}

/// Takes and clears the census.
pub fn take_backwards_memory_derivation_census() -> BackwardsMemoryDerivationCensus {
    std::mem::take(
        &mut *BACKWARDS_MEMORY_DERIVATION_CENSUS
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner),
    )
}

/// The ratchet: `None` when the census equals the pinned baseline exactly,
/// otherwise a message listing every reason whose count rose (a new rejection,
/// which must not land) or fell (lower the pin so it cannot rise back).
pub fn artifact_reuse_rejection_census_mismatch(
    census: &ArtifactReuseRejectionCensus,
    expected_rejections: &[(ArtifactReuseRejection, usize)],
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
                    "{label} {key:?} rose from {was} to {now}: a checked execution artifact that used to be reused is now rejected"
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
    diff(
        "artifact reuse rejection",
        census,
        expected_rejections,
        &mut report,
    );
    (!report.is_empty()).then(|| report.join("\n"))
}

#[cfg(test)]
mod artifact_reuse_rejection_census_tests {
    use super::*;

    #[test]
    fn ratchet_reports_rises_and_falls() {
        let census: ArtifactReuseRejectionCensus = [(ArtifactReuseRejection::EntryStateDelta, 1)]
            .into_iter()
            .collect();
        assert_eq!(
            artifact_reuse_rejection_census_mismatch(
                &census,
                &[(ArtifactReuseRejection::EntryStateDelta, 1)]
            ),
            None
        );
        let rise =
            artifact_reuse_rejection_census_mismatch(&census, &[]).expect("a rise is reported");
        assert!(
            rise.contains("artifact reuse rejection EntryStateDelta rose from 0 to 1"),
            "{rise}"
        );
        assert!(
            rise.contains("a checked execution artifact that used to be reused is now rejected"),
            "{rise}"
        );
        let fall = artifact_reuse_rejection_census_mismatch(
            &census,
            &[(ArtifactReuseRejection::EntryStateDelta, 3)],
        )
        .expect("a fall is reported");
        assert!(fall.contains("EntryStateDelta fell from 3 to 1"), "{fall}");
    }
}
