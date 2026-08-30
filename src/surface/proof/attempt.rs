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
        Err(_) => Ok(None),
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
    for candidate in candidates {
        if !budget.admit() {
            return Ok(None);
        }
        if let Some(success) = attempt_candidate(root, candidate)? {
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
