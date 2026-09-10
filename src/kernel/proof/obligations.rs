//! Surface-independent proof obligations and checked capabilities.
//!
//! These values describe what a checked proof branch still owes. They carry
//! no Surface Click syntax, source selector, diagnostic data, or smart-plan
//! state.

use std::ops::{Deref, DerefMut};
use std::sync::Arc;

use super::storage::SharedValue;
use crate::kernel::{CState, CValue, ExecutionPureFact, Proposition};

/// One open C frontier judgment's remaining semantic obligation.
///
/// A frontier judgment carries no payload of its own: reaching the frontier
/// is the obligation, and every semantic detail lives in the branch state.
#[derive(Clone)]
pub(crate) struct FrontierObligation;

/// One proposition branch obligation with opaque presentation data.
#[derive(Clone)]
pub(crate) struct PropositionObligation<S, O> {
    proposition: Arc<Proposition>,
    pub(crate) presentation: S,
    pub(crate) outcome: Option<O>,
}

impl<S, O> PropositionObligation<S, O> {
    pub(crate) fn new(proposition: Proposition, presentation: S) -> Self {
        Self {
            proposition: Arc::new(proposition),
            presentation,
            outcome: None,
        }
    }

    pub(crate) fn at_outcome(proposition: Proposition, presentation: S, outcome: O) -> Self {
        Self {
            proposition: Arc::new(proposition),
            presentation,
            outcome: Some(outcome),
        }
    }

    pub(crate) fn proposition(&self) -> &Proposition {
        &self.proposition
    }
}

impl<S, O> Deref for PropositionObligation<S, O> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        &self.presentation
    }
}

impl<S, O> DerefMut for PropositionObligation<S, O> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.presentation
    }
}

/// Surface-independent result-aware state for one checked function outcome.
#[derive(Clone)]
pub(crate) struct OutcomeProofCore {
    pub(crate) result: Arc<CValue>,
    pub(crate) state: SharedValue<CState>,
    pub(crate) effect_facts: Arc<Vec<ExecutionPureFact>>,
    pub(crate) execution_pure_facts: Arc<Vec<ExecutionPureFact>>,
    pub(crate) requirement_facts: Arc<Vec<Proposition>>,
}

/// Durable kernel evidence that one exact proposition judgment was closed.
///
/// The proposition, the root assumptions it was closed under, and the optional
/// function outcome all come from the root semantic obligation retained by
/// [`ProofObject`](super::ProofObject); surface provenance cannot manufacture
/// or retarget this value after completion. Retaining the root facts lets a
/// theorem constructor check which assumptions the proof actually stood on
/// instead of re-proving its conclusion. The fact store is persistent, so
/// keeping it costs a shared reference, not a copy of the context.
#[derive(Clone)]
pub(crate) struct CheckedProposition {
    proposition: Arc<Proposition>,
    root_assumptions: super::ProofFacts,
    outcome: Option<OutcomeProofCore>,
}

impl CheckedProposition {
    pub(super) fn new(
        proposition: Proposition,
        root_assumptions: super::ProofFacts,
        outcome: Option<OutcomeProofCore>,
    ) -> Self {
        Self {
            proposition: Arc::new(proposition),
            root_assumptions,
            outcome,
        }
    }

    /// Whether the completed proof stood on no root assumption at all.
    pub(crate) fn is_closed(&self) -> bool {
        self.root_assumptions.is_empty()
    }

    pub(crate) fn proposition(&self) -> &Proposition {
        &self.proposition
    }

    /// The exact facts the root branch assumed. A constructor that turns this
    /// completion into an implication must check them against its own
    /// explicit premises.
    pub(crate) fn root_assumptions(&self) -> &super::ProofFacts {
        &self.root_assumptions
    }

    pub(crate) fn outcome(&self) -> Option<&OutcomeProofCore> {
        self.outcome.as_ref()
    }
}

/// One checked function outcome paired with opaque language presentation.
#[derive(Clone)]
pub(crate) struct OutcomeProofState<S> {
    pub(crate) core: OutcomeProofCore,
    pub(crate) presentation: S,
}

impl<S> OutcomeProofState<S> {
    pub(crate) fn new(core: OutcomeProofCore, presentation: S) -> Self {
        Self { core, presentation }
    }
}

impl<S> Deref for OutcomeProofState<S> {
    type Target = S;

    fn deref(&self) -> &Self::Target {
        &self.presentation
    }
}

impl<S> DerefMut for OutcomeProofState<S> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        &mut self.presentation
    }
}

/// The remaining obligation for one checked returning path, paired with
/// opaque result-presentation data.
#[derive(Clone)]
pub(crate) struct FunctionOutcomeObligation<S> {
    pub(crate) path_index: usize,
    pub(crate) data: S,
}

impl<S> FunctionOutcomeObligation<S> {
    pub(crate) fn new(path_index: usize, data: S) -> Self {
        Self { path_index, data }
    }
}

/// What one open proof branch currently has to establish.
///
/// `P` and `O` are untrusted presentation attachments. Variant identity and
/// every semantic payload remain kernel-owned.
#[derive(Clone)]
pub(crate) enum ProofObligation<P, O> {
    Proposition(PropositionObligation<P, O>),
    Frontier(FrontierObligation),
    FunctionOutcome(FunctionOutcomeObligation<O>),
}
