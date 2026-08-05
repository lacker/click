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
    Diagnostic(String),
}

thread_local! {
    static COLLECTORS: RefCell<Vec<Vec<VerificationEvent>>> = const { RefCell::new(Vec::new()) };
    static DEADLINES: RefCell<Vec<Instant>> = const { RefCell::new(Vec::new()) };
    static ACTIVE_TACTICS: RefCell<Vec<TacticEvent>> = const { RefCell::new(Vec::new()) };
    static ACTIVE_PHASES: RefCell<Vec<&'static str>> = const { RefCell::new(Vec::new()) };
}

struct DeadlineGuard;

impl Drop for DeadlineGuard {
    fn drop(&mut self) {
        DEADLINES.with(|deadlines| {
            deadlines.borrow_mut().pop();
        });
    }
}

/// Runs an operation with a cooperative wall-clock deadline. Kernel execution
/// budgets consult this deadline at expression, statement, call, loop, and
/// path checkpoints; verifier phase boundaries consult it as well.
pub fn with_deadline<R>(limit: Duration, operation: impl FnOnce() -> R) -> R {
    DEADLINES.with(|deadlines| deadlines.borrow_mut().push(Instant::now() + limit));
    let _guard = DeadlineGuard;
    operation()
}

pub fn deadline_exceeded() -> bool {
    DEADLINES.with(|deadlines| {
        deadlines
            .borrow()
            .iter()
            .min()
            .is_some_and(|deadline| Instant::now() >= *deadline)
    })
}

pub fn deadline_context() -> String {
    if let Some(tactic) = ACTIVE_TACTICS.with(|active| active.borrow().last().cloned()) {
        return format!(
            "tactic `{}` in `{}` (class {}, statement {}, source tactic {})",
            tactic.tactic_name,
            tactic.claim,
            tactic.class,
            tactic.statement_index,
            tactic.source_index
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
}

pub fn starts_enabled() -> bool {
    std::env::var_os("CLICK_TIMING_STARTS").is_some()
        || COLLECTORS.with(|collectors| !collectors.borrow().is_empty())
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
            ACTIVE_TACTICS.with(|active| active.borrow_mut().push(tactic.clone()));
        }
        VerificationEvent::TacticFinished { tactic, .. }
        | VerificationEvent::TacticFailed(tactic) => {
            ACTIVE_TACTICS.with(|active| {
                let mut active = active.borrow_mut();
                if let Some(index) = active.iter().rposition(|candidate| candidate == tactic) {
                    active.remove(index);
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
}
