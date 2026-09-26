//! The fixture harnesses' one route into verification limits.
//!
//! A gate verdict must come from deterministic tactic-work budgets, never
//! from a wall-clock tactic limit, so machine load cannot turn a passing
//! fixture red. Library verification entry points install production's
//! latency-oriented tactic clocks by default, and those limits are
//! thread-local, so every harness runs each `#[test]` body through
//! [`deterministic`] and starts every verifier thread through [`spawn`] or
//! [`run_parallel`], which re-enter it on the new thread. The work budgets
//! stay in force; nextest's per-test timeout remains the process-level hang
//! containment. The CLI keeps its real-time backstops.
//!
//! `tests/documentation.rs` enforces this over every `tests/*.rs` file; see
//! `docs/internals/testing.md` for how to add a harness.

#![allow(dead_code, reason = "each harness uses only the helpers it needs")]

use click::instrumentation;

/// Runs `operation` with deterministic tactic-work budgets and without
/// wall-clock tactic limits on the current thread.
pub fn deterministic<R>(operation: impl FnOnce() -> R) -> R {
    instrumentation::without_tactic_time_limits(operation)
}

/// Runs `operation` under [`deterministic`] on a named verifier thread with a
/// 64 MiB stack and waits for it. `label` names the thread's role in the
/// start and panic errors.
pub fn spawn<R: Send + 'static>(
    label: &str,
    name: String,
    operation: impl FnOnce() -> R + Send + 'static,
) -> Result<R, String> {
    std::thread::Builder::new()
        .name(name)
        .stack_size(64 * 1024 * 1024)
        .spawn(move || deterministic(operation))
        .map_err(|error| format!("failed to start {label}: {error}"))?
        .join()
        .map_err(|_| format!("{label} panicked"))
}

/// [`click::cli::run_parallel`] with every item run under [`deterministic`]
/// on its worker thread.
pub fn run_parallel<T, F>(items: &[T], workers: usize, run: F) -> Vec<(usize, String)>
where
    T: Sync,
    F: Fn(&T) -> Result<(), String> + Sync,
{
    click::cli::run_parallel(items, workers, |item| deterministic(|| run(item)))
}
