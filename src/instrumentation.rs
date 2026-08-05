//! Structured verification events shared by the CLI, profiler, and tests.
//!
//! Verification is synchronous, so a thread-local collector gives each run an
//! independent event stream without global environment mutation.  The legacy
//! `CLICK_TIMINGS` text stream remains available for engine debugging, but
//! normal tooling consumes these values directly.

use std::cell::RefCell;
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
    },
    TacticFailed(TacticEvent),
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
    DeadlineExceeded(ActiveVerificationWork),
    Diagnostic(String),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct TacticLimits {
    pub simple: Duration,
    pub smart: Duration,
    pub control: Duration,
}

impl Default for TacticLimits {
    fn default() -> Self {
        Self {
            simple: Duration::from_millis(500),
            smart: Duration::from_secs(2),
            control: Duration::from_secs(2),
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
    running_since: Instant,
    limit: Duration,
}

thread_local! {
    static COLLECTORS: RefCell<Vec<Vec<VerificationEvent>>> = const { RefCell::new(Vec::new()) };
    static DEADLINES: RefCell<Vec<Instant>> = const { RefCell::new(Vec::new()) };
    static DEADLINE_CAPTURED: RefCell<Vec<bool>> = const { RefCell::new(Vec::new()) };
    static TACTIC_LIMITS: RefCell<Vec<TacticLimits>> = const { RefCell::new(Vec::new()) };
    static ACTIVE_TACTICS: RefCell<Vec<ActiveTactic>> = const { RefCell::new(Vec::new()) };
    static ACTIVE_PHASES: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
    static PENDING_LIMIT: RefCell<Option<String>> = const { RefCell::new(None) };
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
        PENDING_LIMIT.with(|pending| *pending.borrow_mut() = None);
    }
}

pub fn with_tactic_limits<R>(limits: TacticLimits, operation: impl FnOnce() -> R) -> R {
    TACTIC_LIMITS.with(|installed| installed.borrow_mut().push(limits));
    let _guard = TacticLimitGuard;
    operation()
}

pub fn with_default_tactic_limits<R>(operation: impl FnOnce() -> R) -> R {
    if std::env::var_os("CLICK_DISABLE_TACTIC_BUDGETS").is_some()
        || TACTIC_LIMITS.with(|limits| !limits.borrow().is_empty())
    {
        operation()
    } else {
        with_tactic_limits(TacticLimits::default(), operation)
    }
}

pub fn deadline_exceeded() -> bool {
    let run = DEADLINES.with(|deadlines| {
        deadlines
            .borrow()
            .iter()
            .min()
            .is_some_and(|deadline| Instant::now() >= *deadline)
    });
    let tactic = ACTIVE_TACTICS.with(|active| {
        active
            .borrow()
            .last()
            .is_some_and(|active| active.exclusive + active.running_since.elapsed() >= active.limit)
    });
    let pending = PENDING_LIMIT.with(|pending| pending.borrow().is_some());
    let exceeded = run || tactic || pending;
    if exceeded {
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
    if let Some(message) = PENDING_LIMIT.with(|pending| pending.borrow().clone()) {
        return message;
    }
    if let Some(active) = ACTIVE_TACTICS.with(|active| active.borrow().last().cloned()) {
        let elapsed = active.exclusive + active.running_since.elapsed();
        return format!(
            "tactic `{}` in `{}` (class {}, statement {}, source tactic {}, {:.3}s elapsed, {} limit)",
            active.event.tactic_name,
            active.event.claim,
            active.event.class,
            active.event.statement_index,
            active.event.source_index,
            elapsed.as_secs_f64(),
            crate::cli::format_duration(active.limit),
        );
    }
    if let Some(phase) = ACTIVE_PHASES.with(|active| active.borrow().last().copied()) {
        return format!("{phase} phase");
    }
    "verification driver".to_string()
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
}

pub fn starts_enabled() -> bool {
    std::env::var_os("CLICK_TIMING_STARTS").is_some()
        || COLLECTORS.with(|collectors| !collectors.borrow().is_empty())
        || TACTIC_LIMITS.with(|limits| !limits.borrow().is_empty())
}

pub fn emit(event: VerificationEvent) {
    match &event {
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
            if let Some(limit) = limit {
                ACTIVE_TACTICS.with(|active| {
                    let now = Instant::now();
                    let mut active = active.borrow_mut();
                    if let Some(parent) = active.last_mut() {
                        parent.exclusive += now.duration_since(parent.running_since);
                    }
                    active.push(ActiveTactic {
                        event: tactic.clone(),
                        exclusive: Duration::ZERO,
                        running_since: now,
                        limit,
                    });
                });
            }
        }
        VerificationEvent::TacticFinished { tactic, .. }
        | VerificationEvent::TacticFailed(tactic) => {
            ACTIVE_TACTICS.with(|active| {
                let now = Instant::now();
                let mut active = active.borrow_mut();
                if let Some(index) = active
                    .iter()
                    .rposition(|candidate| &candidate.event == tactic)
                {
                    let finished = active.remove(index);
                    let elapsed = finished.exclusive + now.duration_since(finished.running_since);
                    if elapsed >= finished.limit {
                        PENDING_LIMIT.with(|pending| {
                            *pending.borrow_mut() = Some(format!(
                                "tactic `{}` in `{}` exceeded its {} {} limit after {:.3}s (statement {}, source tactic {})",
                                finished.event.tactic_name,
                                finished.event.claim,
                                crate::cli::format_duration(finished.limit),
                                finished.event.class,
                                elapsed.as_secs_f64(),
                                finished.event.statement_index,
                                finished.event.source_index,
                            ));
                        });
                    }
                    if let Some(parent) = active.last_mut() {
                        parent.running_since = now;
                    }
                }
            });
        }
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
        VerificationEvent::TacticFinished { tactic, elapsed } => format!(
            "click timing: tactic {} {:.6}s",
            tactic_fields(tactic),
            elapsed.as_secs_f64()
        ),
        VerificationEvent::TacticFailed(tactic) => {
            format!("click timing: failed tactic {}", tactic_fields(tactic))
        }
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
                });
            });
        }
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
            });
            assert!(
                !deadline_exceeded(),
                "the control container must not inherit its child's time"
            );
            emit(VerificationEvent::TacticFinished {
                tactic: control,
                elapsed: Duration::from_millis(100),
            });
        });
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
}
