//! Persistent checked proof-object state.
//!
//! Language-specific names and presentation records are opaque parameters.
//! The kernel owns the persistent state shape and never treats those
//! attachments as evidence.

use super::{
    BranchId, ProofBranch, ProofBranchState, ProofBranches, ProofExecutionState, ProofFacts,
    ProofObligation,
};
use crate::kernel::Proposition;
use std::ops::Deref;
use std::sync::Arc;

/// The immutable state shared by checked proof successors.
#[derive(Clone)]
pub(crate) struct ProofState<L, O, E> {
    pub(crate) locals: L,
    pub(crate) open_branches: ProofBranches<ProofBranch<O, E>>,
    pub(crate) added_facts: Arc<Vec<Proposition>>,
    pub(crate) checked_facts: Arc<Vec<Proposition>>,
}

/// Opaque handle to one immutable checked proof state and the open branch it
/// addresses.
///
/// Surface-language context and certificate provenance deliberately live
/// outside this handle. They may describe or render a checked derivation, but
/// they are not part of the semantic proof state and cannot change its focus.
#[derive(Clone)]
pub(crate) struct ProofObject<L, O, E> {
    state: Arc<ProofState<L, O, E>>,
    focused_branch: BranchId,
}

/// Borrowed authority that the focused goal is an execution frontier owning
/// checked execution state. Only the kernel can construct this view.
pub(crate) struct ProofExecutionView<'a, S> {
    facts: &'a ProofFacts,
    execution: &'a ProofExecutionState<S>,
}

/// Kernel witness that no checked obligations remain open.
pub(crate) struct ProofCompletion<'a> {
    _proof: std::marker::PhantomData<&'a ()>,
}

impl<'a, S> ProofExecutionView<'a, S> {
    pub(crate) fn facts(&self) -> &'a ProofFacts {
        self.facts
    }

    pub(crate) fn execution(&self) -> &'a ProofExecutionState<S> {
        self.execution
    }
}

impl<L, O, E> ProofObject<L, O, E> {
    pub(crate) fn new(state: ProofState<L, O, E>, focused_branch: BranchId) -> Self {
        Self {
            state: Arc::new(state),
            focused_branch,
        }
    }

    pub(crate) fn from_shared_state(
        state: Arc<ProofState<L, O, E>>,
        focused_branch: BranchId,
    ) -> Self {
        Self {
            state,
            focused_branch,
        }
    }

    pub(crate) fn state(&self) -> &ProofState<L, O, E> {
        self.state.as_ref()
    }

    pub(crate) fn focused_branch(&self) -> BranchId {
        self.focused_branch
    }

    pub(crate) fn shares_state_with(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.state, &other.state)
    }

    pub(crate) fn is_complete(&self) -> bool
    where
        O: Clone,
        E: Clone,
    {
        self.state.open_branches.is_empty()
    }

    pub(crate) fn completion(&self) -> Option<ProofCompletion<'_>>
    where
        O: Clone,
        E: Clone,
    {
        self.is_complete().then_some(ProofCompletion {
            _proof: std::marker::PhantomData,
        })
    }

    pub(crate) fn with_state(&self, state: ProofState<L, O, E>) -> Self {
        Self::new(state, self.focused_branch)
    }

    pub(crate) fn focused_at(&self, focused_branch: BranchId) -> Self {
        Self::from_shared_state(self.state.clone(), focused_branch)
    }

    pub(crate) fn into_state(self) -> ProofState<L, O, E>
    where
        L: Clone,
        O: Clone,
        E: Clone,
    {
        Arc::unwrap_or_clone(self.state)
    }
}

impl<L, P: Clone, O: Clone, S: Clone>
    ProofObject<L, ProofObligation<P, O>, ProofExecutionState<S>>
{
    pub(crate) fn execution_view(&self) -> Option<ProofExecutionView<'_, S>> {
        let branch = self.state.open_branches.get(self.focused_branch)?;
        if !matches!(branch.obligation, ProofObligation::Frontier(_)) {
            return None;
        }
        let execution = branch.state.execution.as_deref()?;
        Some(ProofExecutionView {
            facts: &branch.state.facts,
            execution,
        })
    }

    pub(crate) fn finalization(&self) -> Option<ProofExecutionView<'_, S>> {
        let view = self.execution_view()?;
        view.execution
            .core
            .frontier
            .is_at_function_exit()
            .then_some(view)
    }
}

impl<L, O, E> Deref for ProofObject<L, O, E> {
    type Target = ProofState<L, O, E>;

    fn deref(&self) -> &Self::Target {
        self.state()
    }
}

impl<P: Clone, O: Clone, E: Clone> ProofBranches<ProofBranch<ProofObligation<P, O>, E>> {
    pub(crate) fn obligation(&self, at: BranchId) -> Option<&ProofObligation<P, O>> {
        Some(&self.get(at)?.obligation)
    }

    /// Replaces only what the addressed branch must establish, preserving its
    /// branch-local state.
    pub(crate) fn replace_obligation_at(
        &self,
        at: BranchId,
        obligation: ProofObligation<P, O>,
    ) -> Self {
        let Some(branch) = self.get(at) else {
            unreachable!("obligation refinement requires the addressed open branch");
        };
        self.replace_at(at, branch.with_obligation(obligation))
    }

    /// Retains the addressed obligation under updated branch-local state.
    pub(crate) fn with_branch_state_at(&self, at: BranchId, state: ProofBranchState<E>) -> Self {
        let Some(branch) = self.get(at) else {
            unreachable!("a state successor requires the addressed open branch");
        };
        self.replace_at(at, branch.with_state(state))
    }

    /// Retains the addressed goal under updated facts, preserving any
    /// execution snapshot it already borrowed.
    pub(crate) fn with_facts_at(&self, at: BranchId, facts: ProofFacts) -> Self {
        let Some(branch) = self.get(at) else {
            unreachable!("a fact successor requires the addressed open branch");
        };
        self.with_branch_state_at(
            at,
            ProofBranchState {
                facts,
                unfolded_predicates: branch.state.unfolded_predicates.clone(),
                execution: branch.state.execution.clone(),
            },
        )
    }

    /// Retains the addressed goal under an updated execution snapshot and
    /// facts. The successor preserves the goal's kind.
    pub(crate) fn replace_execution_at(
        &self,
        at: BranchId,
        facts: ProofFacts,
        execution: E,
    ) -> Self {
        let Some(branch) = self.get(at) else {
            unreachable!("an execution successor requires the addressed open branch");
        };
        self.with_branch_state_at(
            at,
            ProofBranchState {
                facts,
                unfolded_predicates: branch.state.unfolded_predicates.clone(),
                execution: Some(Arc::new(execution)),
            },
        )
    }

    /// The strict frontier successor: the addressed obligation must be an
    /// execution frontier.
    pub(crate) fn replace_frontier_at(
        &self,
        at: BranchId,
        facts: ProofFacts,
        execution: E,
    ) -> Self {
        let Some(ProofBranch {
            obligation: ProofObligation::Frontier(_),
            ..
        }) = self.get(at)
        else {
            unreachable!("a frontier transition requires the addressed frontier goal");
        };
        self.replace_execution_at(at, facts, execution)
    }

    pub(crate) fn discharged_if_at(&self, at: BranchId, complete: bool, facts: ProofFacts) -> Self {
        if complete {
            self.close_at(at)
        } else {
            self.with_facts_at(at, facts)
        }
    }

    pub(crate) fn discharged_if_or_execution_at(
        &self,
        at: BranchId,
        complete: bool,
        facts: ProofFacts,
        execution: E,
    ) -> Self {
        if complete {
            self.close_at(at)
        } else {
            self.replace_execution_at(at, facts, execution)
        }
    }

    pub(crate) fn is_discharged(&self) -> bool {
        self.is_empty()
    }
}
