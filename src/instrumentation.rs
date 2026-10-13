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
    pub source_tactic_path: Option<Vec<usize>>,
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
    /// Completion of a pure proof claim, including its tactic checking.
    /// Unlike contract certification this is not an additional time bucket.
    ProofClaimFinished {
        function: String,
        claim: String,
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
    /// The deterministic work budget is the only per-tactic bound: no tactic
    /// has a wall-clock limit. It is charged by every unit of recorded
    /// verifier work (`record_deterministic_work`, and the cooperative
    /// checkpoints, which record through the same path), so the same source
    /// spends the same units on any machine under any load, and a scaling
    /// measurement and a budget verdict count the same units.
    ///
    /// Calibration (2026-09-26, base `a8ad65f7`, when the shipped tools'
    /// per-tactic real-time limits were removed and these budgets became the
    /// only per-tactic verdict everywhere; `scripts/measure-tactic-work.sh`,
    /// which runs both fixture harnesses with budgets disabled so no cost is
    /// clipped): the corpus is 36 example sidecars and 2,354 mdtests,
    /// counting every tactic including the gate's generated-certificate
    /// checks.
    ///
    /// - simple: 9,161 tactics, p95 = 1,540, p99 = 4,847, second-largest =
    ///   59,630, max = 73,463 (arena `arena_pipeline` `step`s at
    ///   arena_cells.click:4041 and :3863). 750,000 gives the maximum 10.2x.
    ///   The simple budget is the detector for a pathological simple tactic
    ///   (a slow simple tactic is a Click engine bug), so it stays an order
    ///   of magnitude above the corpus and no higher.
    /// - smart: 12,200 tactics, p95 = 3,162, p99 = 21,899, second-largest =
    ///   957,192, max = 1,069,444 (the `simp` of
    ///   an_unfolded_constant_composite_range_is_one_run_negative.md:29, and
    ///   the arena `have` at arena_cells.click:3846). 2,000,000 gives the
    ///   maximum 1.87x, down from 3.0x at the 2026-09-25 calibration (max
    ///   671,115). The budget is deliberately not raised to regain headroom:
    ///   the arena `have`s grew from 450,033 to 957,192 in one day, and that
    ///   growth is what the budget exists to surface. (It was reduced
    ///   after this calibration: the rewrite chain's closing probe asks only
    ///   the direct logical closer, and premise surface synthesis is lazy
    ///   and charged; `click profile` then puts the heaviest arena `have`
    ///   at 488,691 units, every one counted.) Below them sit the arena `have` at :4290
    ///   (772,427) and loop_frame_rejects_rewritten_field_of_folded_state's
    ///   `close_invariants` (509,163); every other smart tactic is below
    ///   450,000.
    /// - control: 1,850 tactics, p95 = 4,864, p99 = 17,831, second-largest =
    ///   208,965, max = 288,302 (the since-removed negative arena frame fixture's
    ///   `have`, and the arena `have` at :3591). 2,500,000 gives the maximum 8.7x.
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

#[derive(Clone, Debug)]
struct ActiveTactic {
    event: TacticEvent,
    started_at: TacticInstant,
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
    /// A tactic exhausted its per-class work budget.
    Work,
    /// A whole run exhausted its [`with_run_work_limit`] budget.
    RunWork,
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
    /// Crash-containment bounds: when each expires, and its length for the
    /// message that says which bound stopped the run.
    static DEADLINES: RefCell<Vec<(Instant, Duration)>> = const { RefCell::new(Vec::new()) };
    static DEADLINE_CAPTURED: RefCell<Vec<bool>> = const { RefCell::new(Vec::new()) };
    static TACTIC_WORK_LIMITS: RefCell<Vec<TacticWorkLimits>> = const { RefCell::new(Vec::new()) };
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
    /// Whole-run deterministic work budgets ([`with_run_work_limit`]),
    /// charged by the same units as the tactic budgets and the scaling
    /// counters.
    static RUN_WORK_LIMITS: RefCell<Vec<RunWorkLimit>> = const { RefCell::new(Vec::new()) };
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

/// Runs an operation under a cooperative wall-clock crash-containment bound.
/// Kernel execution consults it at expression, statement, call, loop, and
/// path checkpoints; verifier phase boundaries consult it as well.
///
/// This bound only stops a hung or CPU-starved run. It is never a verdict
/// about a proof: verdicts come from the deterministic work budgets
/// ([`TacticWorkLimits`], [`with_run_work_limit`]), which count the same
/// units on any machine under any load, and the message of an expired bound
/// says so. The command-line tools install it through
/// `click::cli::with_run_limits`.
pub fn with_deadline<R>(limit: Duration, operation: impl FnOnce() -> R) -> R {
    DEADLINES.with(|deadlines| deadlines.borrow_mut().push((Instant::now() + limit, limit)));
    DEADLINE_CAPTURED.with(|captured| captured.borrow_mut().push(false));
    let _guard = DeadlineGuard;
    operation()
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

pub fn with_tactic_work_limits<R>(limits: TacticWorkLimits, operation: impl FnOnce() -> R) -> R {
    TACTIC_WORK_LIMITS.with(|installed| installed.borrow_mut().push(limits));
    let _guard = TacticWorkLimitGuard;
    operation()
}

/// Installs the default per-class tactic work budgets unless the caller
/// installed its own. These budgets, and the whole-run budget of
/// [`with_run_work_limit`], are the only limits that decide a verdict; no
/// tactic has a wall-clock limit, so machine load cannot change one.
pub fn with_default_tactic_limits<R>(operation: impl FnOnce() -> R) -> R {
    if std::env::var_os("CLICK_DISABLE_TACTIC_BUDGETS").is_some() {
        return operation();
    }
    if TACTIC_WORK_LIMITS.with(|limits| limits.borrow().is_empty()) {
        with_tactic_work_limits(TacticWorkLimits::default(), operation)
    } else {
        operation()
    }
}

#[derive(Clone, Copy, Debug)]
struct RunWorkLimit {
    used: usize,
    limit: usize,
    exhausted: bool,
}

struct RunWorkLimitGuard;

impl Drop for RunWorkLimitGuard {
    fn drop(&mut self) {
        let enclosing_exhausted = RUN_WORK_LIMITS.with(|limits| {
            let mut limits = limits.borrow_mut();
            limits.pop();
            limits.iter().any(|limit| limit.exhausted)
        });
        if !enclosing_exhausted {
            clear_pending_limit(PendingLimitKind::RunWork);
        }
    }
}

/// Runs `operation` under a deterministic whole-run work budget of `limit`
/// units: every unit recorded inside it, whether inside a tactic or in a
/// driver, certification, or lowering phase outside any tactic, charges the
/// budget, and the first checkpoint after it is exhausted fails the run with
/// a message naming the budget and what was running. The same source spends
/// the same units on any machine under any load, so this verdict, unlike the
/// crash-containment bound of [`with_deadline`], cannot change with load.
pub fn with_run_work_limit<R>(limit: usize, operation: impl FnOnce() -> R) -> R {
    RUN_WORK_LIMITS.with(|limits| {
        limits.borrow_mut().push(RunWorkLimit {
            used: 0,
            limit,
            exhausted: false,
        })
    });
    let _guard = RunWorkLimitGuard;
    operation()
}

/// The work spent so far under the innermost [`with_run_work_limit`], if
/// any.
pub fn run_work_used() -> Option<usize> {
    RUN_WORK_LIMITS.with(|limits| limits.borrow().last().map(|limit| limit.used))
}

/// The innermost [`with_run_work_limit`]'s units used and limit, if that
/// budget is exhausted.
pub fn run_work_exhaustion() -> Option<(usize, usize)> {
    RUN_WORK_LIMITS.with(|limits| {
        limits
            .borrow()
            .last()
            .filter(|limit| limit.exhausted)
            .map(|limit| (limit.used, limit.limit))
    })
}

/// What is running now, for a limit's message.
fn active_work_description() -> String {
    ACTIVE_TACTICS
        .with(|active| {
            active.borrow().last().map(|active| {
                format!(
                    "tactic `{}` in `{}`",
                    active.event.tactic_name, active.event.claim
                )
            })
        })
        .or_else(active_phase_description)
        .unwrap_or_else(|| "verification driver".to_string())
}

/// The open phases, outermost first, as a limit's message names them:
/// `frontend > program-entry storage phase` says both what the run was
/// doing and which part of it.
fn active_phase_description() -> Option<String> {
    ACTIVE_PHASES.with(|active| {
        let active = active.borrow();
        (!active.is_empty()).then(|| format!("{} phase", active.join(" > ")))
    })
}

/// Charges `units` to every whole-run budget. Returns `false` when one is
/// exhausted; the first exhaustion leaves a pending limit naming the budget
/// and what was running.
fn charge_run_work(units: usize) -> bool {
    let exhausted = RUN_WORK_LIMITS.with(|limits| {
        let mut limits = limits.borrow_mut();
        let mut first = None;
        let mut any = false;
        for limit in limits.iter_mut() {
            limit.used = limit.used.saturating_add(units);
            if limit.used > limit.limit {
                any = true;
                if !limit.exhausted {
                    limit.exhausted = true;
                    first.get_or_insert((limit.used, limit.limit));
                }
            }
        }
        (any, first)
    });
    let (any, first) = exhausted;
    if let Some((used, limit)) = first {
        let active = active_work_description();
        PENDING_LIMIT.with(|pending| {
            let mut pending = pending.borrow_mut();
            if pending.is_none() {
                *pending = Some(PendingLimit {
                    kind: PendingLimitKind::RunWork,
                    message: format!(
                        "the run exhausted its deterministic whole-run work budget after {used} units ({limit} limit) while running {active}; no single tactic exhausted its own budget, so the units went to many tactics or to work outside them (`click profile` shows where)"
                    ),
                });
            }
        });
    }
    !any
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
    #[cfg(debug_assertions)]
    if UNCHARGED_DEBUG_CHECK.with(Cell::get) {
        return;
    }
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

#[cfg(debug_assertions)]
thread_local! {
    static UNCHARGED_DEBUG_CHECK: Cell<bool> = const { Cell::new(false) };
}

/// Runs a debug-build self-check without charging its work: the check
/// recomputes an answer the release build takes on trust, so charging it
/// would make a debug run's deterministic work and budgets differ from the
/// release run's.
///
/// Not charging is not enough on its own: a check that names a value or
/// fills a memo the checked code reads later leaves that later read cheaper
/// in a debug build than in a release one. [`without_debug_checks`] runs an
/// operation with every check skipped, as a release build runs it, so a
/// test can compare the two.
#[cfg(debug_assertions)]
pub(crate) fn uncharged_debug_check(check: impl FnOnce()) {
    if DEBUG_CHECKS_SKIPPED.with(Cell::get) {
        return;
    }
    let previous = UNCHARGED_DEBUG_CHECK.with(|flag| flag.replace(true));
    check();
    UNCHARGED_DEBUG_CHECK.with(|flag| flag.set(previous));
}

/// Whether the caller runs inside an [`uncharged_debug_check`]. A rule that
/// collects side results from a predicate the check re-invokes skips them
/// there, so a debug build collects exactly what a release build does.
pub(crate) fn in_uncharged_debug_check() -> bool {
    #[cfg(debug_assertions)]
    {
        UNCHARGED_DEBUG_CHECK.with(Cell::get)
    }
    #[cfg(not(debug_assertions))]
    {
        false
    }
}

/// Speculative presentation searches belong to a smart proof producer, not
/// to explicit certificate validation or proof finalization.
pub(crate) fn smart_tactic_active() -> bool {
    ACTIVE_TACTICS.with(|active| {
        active
            .borrow()
            .last()
            .is_some_and(|tactic| tactic.event.class == "smart")
    })
}

#[cfg(debug_assertions)]
thread_local! {
    static DEBUG_CHECKS_SKIPPED: Cell<bool> = const { Cell::new(false) };
}

/// Runs `operation` with every [`uncharged_debug_check`] skipped, so a
/// debug build does exactly what a release build does. A release build has
/// no such checks, and this is `operation` itself.
#[cfg(test)]
pub(crate) fn without_debug_checks<R>(operation: impl FnOnce() -> R) -> R {
    #[cfg(debug_assertions)]
    {
        let previous = DEBUG_CHECKS_SKIPPED.with(|flag| flag.replace(true));
        let result = operation();
        DEBUG_CHECKS_SKIPPED.with(|flag| flag.set(previous));
        result
    }
    #[cfg(not(debug_assertions))]
    operation()
}

/// Charges `units` to every scaling counter, to the innermost active
/// tactic's budget, and to every whole-run budget. Returns `false` when a
/// budget is exhausted.
fn charge_deterministic_work(units: usize) -> bool {
    WORK_COUNTERS.with(|counters| {
        for counter in counters.borrow_mut().iter_mut() {
            *counter = counter.saturating_add(units);
        }
    });
    let tactic = charge_tactic_work(units);
    let run = charge_run_work(units);
    tactic && run
}

/// Charges `units` to the innermost active tactic's budget. Returns `false`
/// when that budget is exhausted; the first exhaustion leaves a pending work
/// limit whose message names the tactic, its units, and where they went,
/// and emits one [`VerificationEvent::TacticWorkBudgetExceeded`].
fn charge_tactic_work(units: usize) -> bool {
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
    // A debug-build self-check's checkpoints charge nothing, exactly as its
    // direct records do not (`uncharged_debug_check`).
    #[cfg(debug_assertions)]
    let units = if UNCHARGED_DEBUG_CHECK.with(Cell::get) {
        0
    } else {
        units
    };
    let work = !charge_deterministic_work(units);
    let contained = expired_containment_bound().is_some();
    let pending = PENDING_LIMIT.with(|pending| pending.borrow().as_ref().map(|p| p.kind));
    let exceeded = work || contained || pending.is_some();
    if contained && !work && pending.is_none() {
        capture_active_deadline_work();
    }
    exceeded
}

/// The length of the tightest crash-containment bound that has expired.
pub fn expired_containment_bound() -> Option<Duration> {
    let now = Instant::now();
    DEADLINES.with(|deadlines| {
        deadlines
            .borrow()
            .iter()
            .filter(|(deadline, _)| now >= *deadline)
            .map(|(_, limit)| *limit)
            .min()
    })
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
    if let Some(limit) = expired_containment_bound() {
        return format!(
            "{}, stopped by {}",
            active_work_description(),
            containment_bound_description(limit)
        );
    }
    if let Some(active) = ACTIVE_TACTICS.with(|active| active.borrow().last().cloned()) {
        return format!(
            "tactic `{}` in `{}` (class {}, statement {}, source tactic {})",
            active.event.tactic_name,
            active.event.claim,
            active.event.class,
            active.event.statement_index,
            active.event.source_index,
        );
    }
    active_phase_description().unwrap_or_else(|| "verification driver".to_string())
}

/// How a message names a crash-containment bound of `limit`, with the
/// reminder that it is not a verdict about the proof.
pub fn containment_bound_description(limit: Duration) -> String {
    format!(
        "the {} wall-clock crash-containment bound (containment for a hung or CPU-starved run, not a verdict about the proof; verdicts come from deterministic work budgets)",
        crate::cli::format_duration(limit)
    )
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
        || expired_containment_bound().is_some()
        || ACTIVE_TACTICS.with(|active| {
            active
                .borrow()
                .last()
                .is_some_and(|active| active.work_exhausted)
        })
        || RUN_WORK_LIMITS.with(|limits| limits.borrow().iter().any(|limit| limit.exhausted))
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

/// `CLICK_TIMINGS` is read once per process: these checks run on every
/// measured operation, and `env::var_os` takes the environment lock and
/// allocates each time (about an eighth of all verifier time on
/// `examples/arena`).
fn timings_requested() -> bool {
    static REQUESTED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *REQUESTED.get_or_init(|| std::env::var_os("CLICK_TIMINGS").is_some())
}

fn timing_starts_requested() -> bool {
    static REQUESTED: std::sync::OnceLock<bool> = std::sync::OnceLock::new();
    *REQUESTED.get_or_init(|| std::env::var_os("CLICK_TIMING_STARTS").is_some())
}

pub fn enabled() -> bool {
    timings_requested()
        || COLLECTORS.with(|collectors| !collectors.borrow().is_empty())
        || tactic_work_sink_installed()
        || TACTIC_WORK_LIMITS.with(|limits| !limits.borrow().is_empty())
}

fn operation_measurement_enabled() -> bool {
    timings_requested() || COLLECTORS.with(|collectors| !collectors.borrow().is_empty())
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

/// One named verifier phase, from construction until drop, on every exit
/// path including an early `?`.
///
/// The open phases are what a limit's message names as running (a work
/// budget or the crash-containment bound that fires inside them says
/// "while running frontend > program-entry storage phase"), so every
/// phase of a run, including source loading and program-entry
/// construction before any tactic budget is installed, is named when a
/// limit stops it. Profiling (`CLICK_TIMINGS`, a collector)
/// additionally records its wall time. Phases are coarse, so emitting them
/// unconditionally costs a handful of events per run.
pub struct VerificationPhase {
    name: &'static str,
    started: Instant,
}

impl VerificationPhase {
    pub fn new(name: &'static str) -> Self {
        emit(VerificationEvent::PhaseStarted(name));
        Self {
            name,
            started: Instant::now(),
        }
    }
}

impl Drop for VerificationPhase {
    fn drop(&mut self) {
        emit(VerificationEvent::PhaseFinished {
            name: self.name,
            elapsed: self.started.elapsed(),
        });
    }
}

pub fn starts_enabled() -> bool {
    timing_starts_requested()
        || COLLECTORS.with(|collectors| !collectors.borrow().is_empty())
        || tactic_work_sink_installed()
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
            let work_limit = TACTIC_WORK_LIMITS.with(|limits| {
                limits
                    .borrow()
                    .last()
                    .and_then(|limits| limits.for_class(&tactic.class))
            });
            ACTIVE_TACTICS.with(|active| {
                active.borrow_mut().push(ActiveTactic {
                    event: tactic.clone(),
                    started_at: TacticInstant::now(),
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
                }
            });
        }
        VerificationEvent::TacticFailed(tactic) => {
            ACTIVE_TACTICS.with(|active| {
                let mut active = active.borrow_mut();
                if let Some(index) = active
                    .iter()
                    .rposition(|candidate| &candidate.event == tactic)
                {
                    let failed = active.remove(index);
                    record_tactic_work_sample(&failed.event, failed.work_used, true);
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
    if timings_requested() {
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
        VerificationEvent::ProofClaimFinished {
            function,
            claim,
            elapsed,
        } => format!(
            "click timing: proof claim {function} {claim} {:.6}s",
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
            source_tactic_path: None,
            claim: "deadline.contract".to_string(),
            tactic_index: index,
            tactic_name: format!("{class}_work"),
            class: class.to_string(),
            statement_index: index,
            source_index: index,
        }
    }

    #[test]
    fn default_tactic_limits_are_deterministic_work_budgets() {
        with_default_tactic_limits(|| {
            assert_eq!(
                TACTIC_WORK_LIMITS.with(|limits| limits.borrow().last().copied()),
                Some(TacticWorkLimits::default()),
                "verification should retain deterministic tactic bounds"
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
        for class in ["simple", "smart", "control"] {
            let (_, events) = with_deadline(Duration::ZERO, || {
                collect(|| {
                    let active = tactic(class, 0);
                    emit(VerificationEvent::TacticStarted(active.clone()));
                    assert!(deadline_exceeded());
                    let context = deadline_context();
                    assert!(
                        context.contains("crash-containment bound")
                            && context.contains("not a verdict about the proof")
                            && context.contains(&format!("`{class}_work`")),
                        "{context}"
                    );
                    emit(VerificationEvent::TacticFailed(active));
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
                    assert!(
                        deadline_context()
                            .contains("stopped by the 0s wall-clock crash-containment bound")
                    );
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
    fn a_whole_run_work_budget_charges_work_inside_and_outside_tactics() {
        let limits = TacticWorkLimits {
            simple: 1_000,
            smart: 1_000,
            control: 1_000,
        };
        let (_, events) = with_tactic_work_limits(limits, || {
            collect(|| {
                with_run_work_limit(10, || {
                    // Driver work outside any tactic charges the run budget.
                    record_deterministic_work(6);
                    assert_eq!(run_work_used(), Some(6));
                    let tactic = tactic("simple", 0);
                    emit(VerificationEvent::TacticStarted(tactic.clone()));
                    record_deterministic_work(3);
                    assert!(!deadline_exceeded(), "the tenth unit still fits");
                    assert!(deadline_exceeded(), "the eleventh unit exhausts the run");
                    let context = deadline_context();
                    assert!(
                        context.contains(
                            "exhausted its deterministic whole-run work budget after 11 units (10 limit) while running tactic `simple_work`"
                        ),
                        "{context}"
                    );
                    // It stays exhausted without re-reporting.
                    record_deterministic_work(100);
                    assert!(deadline_exceeded());
                    assert_eq!(deadline_context(), context);
                    emit(VerificationEvent::TacticFailed(tactic));
                });
                assert!(
                    exceeded_verification_limit_context().is_none(),
                    "leaving the run budget clears its pending limit"
                );
            })
        });
        assert!(
            !events.iter().any(|event| matches!(
                event,
                VerificationEvent::DeadlineExceeded(_)
                    | VerificationEvent::TacticWorkBudgetExceeded { .. }
            )),
            "run-budget exhaustion is neither a wall-clock bound nor a tactic budget"
        );
    }

    #[test]
    fn whole_run_work_budgets_nest_and_the_tighter_one_fires() {
        with_run_work_limit(100, || {
            record_deterministic_work(50);
            with_run_work_limit(5, || {
                record_deterministic_work(5);
                assert!(deadline_exceeded());
                assert!(deadline_context().contains("(5 limit)"));
            });
            assert_eq!(run_work_used(), Some(56));
            assert!(!deadline_exceeded(), "the outer budget still has room");
        });
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

/// Where simple statement checking derived a prerequisite that no fact states
/// exactly, by a search whose result the proof does not retain. The
/// simplify-step plan (`issues/simplify-step.md`) moves each of these to an
/// exact check or an expandable `auto`; this census is its ratchet.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Ord, PartialOrd, Hash)]
pub enum HiddenPrerequisiteRoute {
    /// A call or access obligation of a `step()`, derived by
    /// `derive_proposition` over the whole proof context.
    StepObligation,
    /// The same, under the contextual policy loop phases and their re-runs use.
    ContextualObligation,
    /// A condition-transition obligation of a `step()`, decided by a boolean
    /// search over the whole proof context.
    StepCondition,
    /// The same, under the contextual policy.
    ContextualCondition,
    /// The same, under the explicit policy.
    ExplicitCondition,
    /// A refused `step()` re-run contextually over retained `have` facts.
    RetainedHaveRerun,
}

/// The count of hidden prerequisite derivations by route and by the top rule
/// of the derivation (or `"proves"` where the search records none).
pub type HiddenPrerequisiteCensus =
    std::collections::BTreeMap<(HiddenPrerequisiteRoute, &'static str), usize>;

static HIDDEN_PREREQUISITE_CENSUS: std::sync::Mutex<HiddenPrerequisiteCensus> =
    std::sync::Mutex::new(std::collections::BTreeMap::new());

#[cfg(test)]
thread_local! {
    static HIDDEN_PREREQUISITES_ON_THREAD: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

pub(crate) fn record_hidden_prerequisite(route: HiddenPrerequisiteRoute, rule: &'static str) {
    #[cfg(test)]
    HIDDEN_PREREQUISITES_ON_THREAD.with(|count| count.set(count.get() + 1));
    *HIDDEN_PREREQUISITE_CENSUS
        .lock()
        .unwrap_or_else(std::sync::PoisonError::into_inner)
        .entry((route, rule))
        .or_default() += 1;
}

/// Hidden prerequisite derivations recorded on this thread so far. A caller
/// compares two readings to attribute derivations to one operation.
#[cfg(test)]
pub(crate) fn hidden_prerequisites_on_thread() -> usize {
    HIDDEN_PREREQUISITES_ON_THREAD.with(std::cell::Cell::get)
}

/// Takes and clears the census.
pub fn take_hidden_prerequisite_census() -> HiddenPrerequisiteCensus {
    std::mem::take(
        &mut *HIDDEN_PREREQUISITE_CENSUS
            .lock()
            .unwrap_or_else(std::sync::PoisonError::into_inner),
    )
}

/// The ratchet: `None` when every route and rule matches its pin, otherwise a
/// message naming each that rose (a new hidden derivation, which must not
/// land) or fell (lower its pin). A `partial` census, from one shard of a
/// partitioned corpus, can only show a rise: a shard above the whole
/// corpus's pin has one, while a shard below it says nothing about the total.
pub fn hidden_prerequisite_census_mismatch(
    census: &HiddenPrerequisiteCensus,
    expected: &[((HiddenPrerequisiteRoute, &'static str), usize)],
    partial: bool,
) -> Option<String> {
    let expected = expected
        .iter()
        .copied()
        .collect::<std::collections::BTreeMap<_, _>>();
    let keys = census
        .keys()
        .chain(expected.keys())
        .copied()
        .collect::<std::collections::BTreeSet<_>>();
    let mut report = Vec::new();
    for key in keys {
        let was = expected.get(&key).copied().unwrap_or(0);
        let now = census.get(&key).copied().unwrap_or(0);
        if now > was {
            report.push(format!(
                "hidden prerequisite {key:?} rose from {was} to {now}: simple checking derived a prerequisite it does not retain"
            ));
        } else if now < was && !partial {
            report.push(format!(
                "hidden prerequisite {key:?} fell from {was} to {now}: lower its pin to {now}"
            ));
        }
    }
    if report.is_empty() {
        return None;
    }
    report.push(format!("hidden prerequisite census now: {census:?}"));
    Some(report.join("\n"))
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

#[cfg(test)]
mod hidden_prerequisite_census_tests {
    use super::*;

    #[test]
    fn a_shard_reports_only_rises_and_a_whole_run_reports_both() {
        let key = (HiddenPrerequisiteRoute::StepObligation, "And");
        let census = HiddenPrerequisiteCensus::from([(key, 3)]);
        assert!(hidden_prerequisite_census_mismatch(&census, &[(key, 3)], false).is_none());
        assert!(hidden_prerequisite_census_mismatch(&census, &[(key, 4)], true).is_none());
        let fell = hidden_prerequisite_census_mismatch(&census, &[(key, 4)], false)
            .expect("a whole run below its pin must lower the pin");
        assert!(fell.contains("fell from 4 to 3"), "{fell}");
        let rose = hidden_prerequisite_census_mismatch(&census, &[(key, 2)], true)
            .expect("a shard above the whole-corpus pin is a rise");
        assert!(rose.contains("rose from 2 to 3"), "{rose}");
    }
}
