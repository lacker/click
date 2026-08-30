//! Persistent checked proof-object state.
//!
//! Language-specific names and presentation records are opaque parameters.
//! The kernel owns the persistent state shape and never treats those
//! attachments as evidence.

use super::{BranchId, ProofBranch, ProofBranchState, ProofBranches, ProofFacts, ProofObligation};
use crate::kernel::Proposition;
use std::sync::Arc;

/// The immutable state shared by checked proof successors.
#[derive(Clone)]
pub(crate) struct ProofState<L, O, E> {
    pub(crate) locals: L,
    pub(crate) open_branches: ProofBranches<ProofBranch<O, E>>,
    pub(crate) added_facts: Arc<Vec<Proposition>>,
    pub(crate) checked_facts: Arc<Vec<Proposition>>,
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
