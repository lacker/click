//! Persistent checked proof-object infrastructure.
//!
//! This module is the kernel-owned home for proof state, branch topology,
//! checked transitions, and finalization authority. The migration begins with
//! branch topology; the remaining checked representation moves here in
//! independently green slices.

pub(crate) mod arithmetic_special;
mod branches;
pub(crate) mod equality_rewrite;
mod execution;
// `kernel::reasoning` and `kernel::api` reach the snapshot-aware alpha
// identity here for the range-fold congruences, the same way they reach
// `term_rewrite`.
pub(in crate::kernel) mod fact_keys;
pub(crate) mod fact_reasoning;
mod facts;
mod integer_affine_atoms;
pub(crate) mod integer_arithmetic;
#[cfg(test)]
mod integer_arithmetic_soundness_tests;
mod integer_bound_exclusion;
mod integer_cast_identity;
mod integer_division_bounds;
mod integer_multiply_order;
mod integer_polynomial_identity;
mod integer_product_bounds;
mod integer_quotient_bound;
mod integer_quotient_shift;
mod integer_relation_transport;
mod object;
mod obligations;
pub(crate) mod signed_arithmetic;
mod storage;
pub(crate) mod term_rewrite;

pub(crate) use branches::{BranchId, ProofBranch, ProofBranchState, ProofBranches, SplitId};
pub(crate) use execution::{
    CheckedBranchSplit, CheckedBranchSplitError, CheckedCallEvent, CheckedCallEvents,
    CheckedCallOutcomeSplit, CheckedExecutionEvent, CheckedProofCasePartition, EvidenceRefusal,
    ExceptionalContinuation, ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind,
    FrontierPosition, LoopControlExit, OutcomeEvidenceFork, ProofExecutionContinuation,
    ProofExecutionState, checked_branch_fact_is_available, old_reference_state,
    take_unestablished_interface_goal,
};
#[allow(unused_imports)]
pub(crate) use fact_keys::propositions_are_alpha_equal;
pub(crate) use fact_keys::{
    PropositionIdentityKey, QuantifiedEquivalenceKey, SnapshotBlindPropositionKey,
    proposition_identity_key, proposition_identity_key_declines_shape,
    quantified_equivalence_index_key, snapshot_blind_proposition_key,
};
#[cfg(test)]
pub(crate) use fact_keys::{alpha_proposition_key_visits, reset_alpha_proposition_key_visits};
#[cfg(test)]
pub(crate) use facts::take_fact_entry_counts;
pub(crate) use facts::{ProofFacts, PropositionSource, is_definedness_guard};
pub(crate) use object::{
    ExecutionUpdateError, FrontierSplitError, ProofFocusError, ProofJoinError, ProofObject,
    ProofState, PropositionAssumptionContext, PropositionCloseError, PropositionIntroduction,
    PropositionSplitError,
};
pub(crate) use obligations::{
    AllocationLifetimeObligation, CheckedProposition, FrontierObligation,
    FunctionOutcomeObligation, LiveAllocationObligation, OutcomeIdentity, OutcomeProofCore,
    OutcomeProofState, ProofObligation, PropositionObligation,
};
pub(crate) use storage::{
    PersistentOrderedSet, PersistentSequence, PersistentVector, SharedValue, SharedVec,
};

#[cfg(test)]
pub(crate) use facts::take_statement_priority_entries;
