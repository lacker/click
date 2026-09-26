//! Untrusted, bounded search orchestration over immutable [`Proof`] values.
//!
//! These combinators own no semantic authority: every successor they return
//! was produced by the checked operations of the [`Proof`] API, and
//! this module deliberately lives outside the audited proof-object core — it
//! compiles against the same `pub(super)` surface smart tactics use. Because
//! `Proof` is immutable, speculation is naturally transactional: a failed or
//! abandoned candidate is dropped and the root remains the unchanged
//! authority, retained certificate included.
//!
//! The combinators centralize two disciplines that ad-hoc search loops get
//! wrong:
//!
//! 1. **Deadline attribution.** A rejected candidate is an ordinary miss the
//!    search may continue past. An error raised while the global verification
//!    deadline is exceeded is a tooling failure that must abort the search —
//!    it must never masquerade as one more rejection and surface later,
//!    misattributed, from an unrelated fallback path.
//! 2. **Deterministic candidate budgets.** A search over an unbounded
//!    candidate space declares its budget up front; exhaustion is a prompt,
//!    bounded miss rather than an error or an unmeasured stall. Structurally
//!    terminating searches may run [`AttemptBudget::unbounded`].

use super::proof_object::Proof;
use crate::surface::ClickError;
use crate::surface::ProofStep;
use std::cell::RefCell;

const MAX_SEARCH_FAILURES: usize = 8;
const MAX_SEARCH_REASON_BYTES: usize = 512;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct SearchFailure {
    pub(super) strategy: String,
    pub(super) reason: String,
    pub(super) diagnostic: Option<crate::surface::proof_diagnostics::ProofFailureDiagnostic>,
    pub(super) kind: SearchFailureKind,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum SearchFailureKind {
    NotApplicable,
    Rejected,
    Unsupported,
    Exhausted,
    UnclosedGoal,
}

struct SearchFailureFrame {
    strategy: String,
    failures: Vec<SearchFailure>,
}

thread_local! {
    static SEARCH_SCOPES: RefCell<Vec<SearchFailureFrame>> = const { RefCell::new(Vec::new()) };
}

/// Starts a bounded transactional search-diagnostic scope. A successful scope
/// discards its candidate explanations; a failed nested scope contributes its
/// bounded representatives to the enclosing search.
pub(super) fn search_scope(strategy: impl Into<String>) -> SearchScope {
    let strategy = strategy.into();
    let depth = SEARCH_SCOPES.with(|scopes| {
        let mut scopes = scopes.borrow_mut();
        scopes.push(SearchFailureFrame {
            strategy: strategy.clone(),
            failures: Vec::new(),
        });
        scopes.len()
    });
    SearchScope {
        successful: false,
        finished: false,
        depth,
    }
}

pub(super) struct SearchScope {
    successful: bool,
    finished: bool,
    depth: usize,
}

impl SearchScope {
    pub(super) fn succeed(&mut self) {
        self.successful = true;
    }

    pub(super) fn finish(mut self) -> Vec<crate::surface::proof_diagnostics::ProofSearchFailure> {
        assert_eq!(
            SEARCH_SCOPES.with(|scopes| scopes.borrow().len()),
            self.depth,
            "search scopes must finish in nesting order"
        );
        let Some(frame) = SEARCH_SCOPES.with(|scopes| scopes.borrow_mut().pop()) else {
            self.finished = true;
            return Vec::new();
        };
        self.finished = true;
        if self.successful {
            return Vec::new();
        }
        let mut failures = frame.failures;
        failures.truncate(MAX_SEARCH_FAILURES);
        failures
            .into_iter()
            .map(
                |failure| crate::surface::proof_diagnostics::ProofSearchFailure {
                    strategy: failure.strategy,
                    reason: failure.reason,
                    kind: format!("{:?}", failure.kind),
                    diagnostic: failure.diagnostic.map(std::sync::Arc::new),
                },
            )
            .collect()
    }
}

impl Drop for SearchScope {
    fn drop(&mut self) {
        if self.finished {
            return;
        }
        let Some(frame) = SEARCH_SCOPES.with(|scopes| scopes.borrow_mut().pop()) else {
            return;
        };
        if self.successful {
            return;
        }
        let mut failures = frame.failures;
        failures.truncate(MAX_SEARCH_FAILURES);
        SEARCH_SCOPES.with(|scopes| {
            let mut scopes = scopes.borrow_mut();
            if let Some(parent) = scopes.last_mut() {
                for failure in failures {
                    push_failure(parent, failure);
                }
            }
        });
    }
}

fn record_search_failure(error: &ClickError) {
    if crate::instrumentation::deadline_exceeded() {
        return;
    }
    SEARCH_SCOPES.with(|scopes| {
        let mut scopes = scopes.borrow_mut();
        let Some(scope) = scopes.last_mut() else {
            return;
        };
        let mut reason = error.raw_summary().to_owned();
        truncate_reason(&mut reason);
        push_failure(
            scope,
            SearchFailure {
                strategy: scope.strategy.clone(),
                reason,
                diagnostic: error.diagnostic().cloned(),
                kind: SearchFailureKind::Rejected,
            },
        );
    });
}

fn truncate_reason(reason: &mut String) {
    if reason.len() > MAX_SEARCH_REASON_BYTES {
        let mut end = MAX_SEARCH_REASON_BYTES;
        while !reason.is_char_boundary(end) {
            end -= 1;
        }
        reason.truncate(end);
    }
}

pub(super) fn record_search_note(strategy: impl Into<String>, reason: impl Into<String>) {
    SEARCH_SCOPES.with(|scopes| {
        let mut scopes = scopes.borrow_mut();
        let Some(scope) = scopes.last_mut() else {
            return;
        };
        let mut reason = reason.into();
        truncate_reason(&mut reason);
        let kind = if reason.contains("budget exhausted") {
            SearchFailureKind::Exhausted
        } else if reason.contains("unsupported") || reason.contains("no surface") {
            SearchFailureKind::Unsupported
        } else {
            SearchFailureKind::NotApplicable
        };
        push_failure(
            scope,
            SearchFailure {
                strategy: strategy.into(),
                reason,
                diagnostic: None,
                kind,
            },
        );
    });
}

/// Retains a checked proof-state diagnostic for a structurally reached leaf.
/// Unlike a plain note, this candidate carries the lazy goal renderer so the
/// terminal report can expose the actual proposition without formatting it
/// during search.
pub(super) fn record_unclosed_goal(
    strategy: impl Into<String>,
    error: &crate::surface::ClickError,
) {
    if crate::instrumentation::deadline_exceeded() {
        return;
    }
    SEARCH_SCOPES.with(|scopes| {
        let mut scopes = scopes.borrow_mut();
        let Some(scope) = scopes.last_mut() else {
            return;
        };
        let mut reason = error.raw_summary().to_owned();
        truncate_reason(&mut reason);
        push_failure(
            scope,
            SearchFailure {
                strategy: strategy.into(),
                reason,
                diagnostic: error.diagnostic().cloned(),
                kind: SearchFailureKind::UnclosedGoal,
            },
        );
    });
}

fn push_failure(scope: &mut SearchFailureFrame, failure: SearchFailure) {
    if scope.failures.iter().any(|existing| {
        existing.strategy == failure.strategy
            && existing.reason == failure.reason
            && existing.kind == failure.kind
    }) {
        return;
    }
    if scope.failures.len() < MAX_SEARCH_FAILURES {
        scope.failures.push(failure);
    } else if matches!(
        failure.kind,
        SearchFailureKind::Unsupported
            | SearchFailureKind::Exhausted
            | SearchFailureKind::UnclosedGoal
    ) && let Some(index) = scope.failures.iter().position(|existing| {
        matches!(
            existing.kind,
            SearchFailureKind::Rejected | SearchFailureKind::NotApplicable
        )
    }) {
        scope.failures[index] = failure;
    }
}

/// Deterministic candidate budget for one bounded search.
///
/// Every admitted candidate decrements the budget; an exhausted budget turns
/// the remaining search into a miss. Budgets bound smart-layer work only —
/// they are not proof authority and never affect a checked step's meaning.
pub(super) struct AttemptBudget {
    remaining: usize,
}

impl AttemptBudget {
    #[cfg(test)]
    pub(super) fn new(candidates: usize) -> Self {
        Self {
            remaining: candidates,
        }
    }

    /// A budget for searches whose candidate space is already structurally
    /// bounded (for example, refinements that strictly shrink the goal).
    pub(super) fn unbounded() -> Self {
        Self {
            remaining: usize::MAX,
        }
    }

    fn admit(&mut self) -> bool {
        if self.remaining == 0 {
            false
        } else {
            self.remaining -= 1;
            true
        }
    }
}

/// Classifies one checked-candidate outcome.
///
/// A rejection while the global deadline holds is an ordinary miss; an error
/// with the deadline exceeded aborts the search loudly. This is the only
/// place search code converts a checked operation's `Result` into a miss, so
/// a deadline failure cannot be swallowed as one more rejected candidate.
pub(super) fn candidate_outcome<T>(result: Result<T, ClickError>) -> Result<Option<T>, ClickError> {
    match result {
        Ok(success) => Ok(Some(success)),
        Err(error) if crate::instrumentation::deadline_exceeded() => Err(error),
        Err(error) => {
            record_search_failure(&error);
            Ok(None)
        }
    }
}

/// Runs one transactional candidate from `root`.
///
/// The closure receives its own clone of the root and may apply any number
/// of checked operations, including the candidate's entire continuation. A
/// miss leaves `root` the unchanged authority; only a candidate whose
/// complete success condition held is returned.
#[cfg(test)]
pub(super) fn attempt<'a>(
    root: &Proof<'a>,
    budget: &mut AttemptBudget,
    candidate: impl FnOnce(Proof<'a>) -> Result<Option<Proof<'a>>, ClickError>,
) -> Result<Option<Proof<'a>>, ClickError> {
    if !budget.admit() {
        record_search_note("candidate budget", "candidate search budget exhausted");
        return Ok(None);
    }
    candidate(root.clone())
}

/// Returns the first candidate whose transactional attempt succeeds.
///
/// Every attempt starts from the same shared `root`, so trying `N`
/// candidates costs `N` candidate checks plus nothing for the shared
/// prefix that produced `root`.
pub(super) fn first_success<'a, C>(
    root: &Proof<'a>,
    budget: &mut AttemptBudget,
    candidates: impl IntoIterator<Item = C>,
    mut attempt_candidate: impl FnMut(&Proof<'a>, C) -> Result<Option<Proof<'a>>, ClickError>,
) -> Result<Option<Proof<'a>>, ClickError> {
    let mut search = search_scope("candidate search");
    for candidate in candidates {
        if !budget.admit() {
            record_search_note("candidate budget", "candidate search budget exhausted");
            return Ok(None);
        }
        let mut candidate_scope = search_scope("checked candidate");
        if let Some(success) = attempt_candidate(root, candidate)? {
            candidate_scope.succeed();
            search.succeed();
            return Ok(Some(success));
        }
    }
    Ok(None)
}

/// Tries each step as an independent one-step candidate on the same root.
pub(super) fn try_steps<'a>(
    root: &Proof<'a>,
    budget: &mut AttemptBudget,
    steps: impl IntoIterator<Item = ProofStep>,
) -> Result<Option<Proof<'a>>, ClickError> {
    first_success(root, budget, steps, |root, step| {
        candidate_outcome(root.apply_step(step))
    })
}

/// Checks an all-or-nothing step sequence as one candidate.
///
/// The sequence succeeds only if every step is accepted in order; any miss
/// discards the partial descendant and returns the search to `root`.
#[cfg(test)]
pub(super) fn try_sequence<'a>(
    root: &Proof<'a>,
    budget: &mut AttemptBudget,
    steps: &[ProofStep],
) -> Result<Option<Proof<'a>>, ClickError> {
    if !budget.admit() {
        record_search_note("candidate budget", "candidate search budget exhausted");
        return Ok(None);
    }
    let mut proof = root.clone();
    for step in steps {
        match candidate_outcome(proof.apply_step(step.clone()))? {
            Some(next) => proof = next,
            None => return Ok(None),
        }
    }
    Ok(Some(proof))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn rejected_candidate_is_kept_until_failed_scope() {
        let scope = search_scope("test strategy");
        let _ = candidate_outcome::<()>(Err(ClickError::new("candidate rejected"))).unwrap();
        let failures = scope.finish();
        assert_eq!(failures.len(), 1);
        assert_eq!(failures[0].strategy, "test strategy");
        assert_eq!(failures[0].reason, "candidate rejected");
        assert_eq!(failures[0].kind, "Rejected");
    }

    #[test]
    fn successful_scope_discards_rejections_and_clears_previous_claim() {
        let scope = search_scope("failed claim");
        let _ = candidate_outcome::<()>(Err(ClickError::new("stale"))).unwrap();
        assert_eq!(scope.finish().len(), 1);

        let mut scope = search_scope("successful claim");
        let _ = candidate_outcome::<()>(Err(ClickError::new("discarded"))).unwrap();
        scope.succeed();
        assert!(scope.finish().is_empty());
    }

    #[test]
    fn nested_scope_preserves_parent_and_success_discards_child() {
        let outer = search_scope("outer");
        let _ = candidate_outcome::<()>(Err(ClickError::new("outer rejection"))).unwrap();
        let mut inner = search_scope("inner");
        let _ = candidate_outcome::<()>(Err(ClickError::new("inner discarded"))).unwrap();
        inner.succeed();
        drop(inner);
        let failures = outer.finish();
        assert_eq!(failures.len(), 1);
        assert_eq!(failures[0].reason, "outer rejection");
    }

    #[test]
    fn utf8_and_exhaustion_are_bounded() {
        let scope = search_scope("bounded");
        let long = "é".repeat(MAX_SEARCH_REASON_BYTES);
        let _ = candidate_outcome::<()>(Err(ClickError::new(long))).unwrap();
        record_search_note("budget", "budget exhausted");
        let failures = scope.finish();
        assert_eq!(failures.len(), 2);
        assert!(failures[0].reason.len() <= MAX_SEARCH_REASON_BYTES);
        assert!(
            failures[0]
                .reason
                .is_char_boundary(failures[0].reason.len())
        );
        assert!(failures[1].reason.contains("exhausted"));
        assert_eq!(failures[1].kind, "Exhausted");
    }

    #[test]
    fn high_priority_failure_replaces_routine_rejection_at_capacity() {
        let scope = search_scope("priority");
        for index in 0..MAX_SEARCH_FAILURES {
            let _ =
                candidate_outcome::<()>(Err(ClickError::new(format!("routine rejection {index}"))))
                    .unwrap();
        }
        record_search_note("presentation", "unsupported: no surface presentation");
        let failures = scope.finish();
        assert_eq!(failures.len(), MAX_SEARCH_FAILURES);
        assert!(failures.iter().any(|failure| failure.kind == "Unsupported"));
    }

    #[test]
    fn unclosed_goal_survives_saturated_search_frame() {
        let scope = search_scope("priority");
        for index in 0..MAX_SEARCH_FAILURES {
            let _ =
                candidate_outcome::<()>(Err(ClickError::new(format!("routine rejection {index}"))))
                    .unwrap();
        }
        record_unclosed_goal("leaf", &ClickError::new("leaf remained open"));
        let failures = scope.finish();
        assert_eq!(failures.len(), MAX_SEARCH_FAILURES);
        assert!(
            failures
                .iter()
                .any(|failure| failure.kind == "UnclosedGoal")
        );
    }

    #[test]
    fn nested_unsupported_failure_survives_parent_capacity() {
        let outer = search_scope("outer");
        for index in 0..MAX_SEARCH_FAILURES {
            let _ =
                candidate_outcome::<()>(Err(ClickError::new(format!("routine rejection {index}"))))
                    .unwrap();
        }
        let inner = search_scope("inner");
        record_search_note("presentation", "unsupported: missing surface");
        drop(inner);
        let failures = outer.finish();
        assert!(failures.iter().any(|failure| failure.kind == "Unsupported"));
    }

    #[test]
    fn nested_unclosed_goal_survives_parent_capacity() {
        let outer = search_scope("outer");
        for index in 0..MAX_SEARCH_FAILURES {
            let _ =
                candidate_outcome::<()>(Err(ClickError::new(format!("routine rejection {index}"))))
                    .unwrap();
        }
        let inner = search_scope("inner");
        record_unclosed_goal("inner leaf", &ClickError::new("leaf remained open"));
        drop(inner);
        let failures = outer.finish();
        assert!(
            failures
                .iter()
                .any(|failure| failure.kind == "UnclosedGoal")
        );
        assert!(
            failures
                .iter()
                .any(|failure| failure.strategy == "inner leaf")
        );
    }
}
