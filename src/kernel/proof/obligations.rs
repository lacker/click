//! Surface-independent proof obligations and checked capabilities.
//!
//! These values describe what a checked proof branch still owes. They carry
//! no Surface Click syntax, source selector, diagnostic data, or smart-plan
//! state.

use std::ops::{Deref, DerefMut};
use std::sync::Arc;

use super::storage::SharedValue;
use crate::kernel::{CResourceFact, CState, CValue, ExecutionPureFact, Proposition};

/// Diagnostic evidence returned when an allocation-lifetime obligation could
/// not be discharged. The allocation is semantic evidence; the optional
/// holder is diagnostic provenance identifying the declared resource that
/// still accounts for it. This is deliberately distinct from the open proof
/// obligation below: a successful check has no leaked-allocation payload.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct LiveAllocationObligation {
    allocation: CResourceFact,
    holder: Option<CResourceFact>,
}

impl LiveAllocationObligation {
    pub(crate) fn new(allocation: CResourceFact, holder: Option<CResourceFact>) -> Self {
        Self { allocation, holder }
    }

    pub(crate) fn allocation(&self) -> &CResourceFact {
        &self.allocation
    }

    pub(crate) fn holder(&self) -> Option<&CResourceFact> {
        self.holder.as_ref()
    }
}

/// The outcome-owned obligation to account for every live heap allocation at
/// function exit. Its path identity prevents a result-aware claim from
/// accidentally discharging the lifetime check for a sibling outcome.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct AllocationLifetimeObligation {
    path_index: usize,
}

impl AllocationLifetimeObligation {
    pub(crate) fn new(path_index: usize) -> Self {
        Self { path_index }
    }

    pub(crate) fn path_index(&self) -> usize {
        self.path_index
    }
}

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

/// Identity of one producer-owned execution outcome. Proposition scopes
/// retain it even when they allocate their own local proof branch IDs.
#[derive(Clone)]
pub(crate) struct OutcomeIdentity(Arc<()>);
impl OutcomeIdentity {
    pub(crate) fn fresh() -> Self {
        Self(Arc::new(()))
    }
    pub(crate) fn same_as(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

/// Surface-independent payload-aware state for one checked function outcome.
#[derive(Clone)]
pub(crate) struct OutcomeProofCore {
    pub(crate) identity: OutcomeIdentity,
    pub(crate) result: Arc<CValue>,
    pub(crate) store_consequences_available: bool,
    pub(crate) state: SharedValue<CState>,
    pub(crate) is_exceptional: bool,
    pub(crate) effect_facts: Arc<Vec<ExecutionPureFact>>,
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

    /// From a checked P, derive A1 implies ... implies P under the same
    /// root assumptions and outcome. The caller supplies the prefix length,
    /// so checking visits that prefix and compares the terminal body once.
    /// This does not discharge or replace any assumption of the original proof.
    pub(crate) fn with_implication_prefix(
        &self,
        goal: &Proposition,
        prefix_len: usize,
    ) -> Option<Self> {
        let mut body = goal;
        for _ in 0..prefix_len {
            let Proposition::Implies(_, consequent) = body else {
                return None;
            };
            body = consequent;
        }
        if body != self.proposition() {
            return None;
        }
        Some(Self {
            proposition: Arc::new(goal.clone()),
            root_assumptions: self.root_assumptions.clone(),
            outcome: self.outcome.clone(),
        })
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
    pub(crate) allocation_lifetime: AllocationLifetimeObligation,
}

impl<S> FunctionOutcomeObligation<S> {
    pub(crate) fn new(path_index: usize, data: S) -> Self {
        Self {
            path_index,
            data,
            allocation_lifetime: AllocationLifetimeObligation::new(path_index),
        }
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
