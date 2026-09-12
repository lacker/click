//! Persistent checked proof-object infrastructure.
//!
//! This module is the kernel-owned home for proof state, branch topology,
//! checked transitions, and finalization authority. The migration begins with
//! branch topology; the remaining checked representation moves here in
//! independently green slices.

mod branches;
mod execution;
mod fact_keys;
pub(crate) mod fact_reasoning;
mod facts;
mod integer_affine_atoms;
pub(crate) mod integer_arithmetic;
#[cfg(test)]
mod integer_arithmetic_soundness_tests;
mod object;
mod obligations;
pub(crate) mod signed_arithmetic;
mod storage;
pub(crate) mod term_rewrite;

pub(crate) use branches::{BranchId, ProofBranch, ProofBranchState, ProofBranches, SplitId};
pub(crate) use execution::{
    CheckedBranchSplit, CheckedBranchSplitError, CheckedCallEvent, CheckedCallEvents,
    CheckedExecutionEvent, CheckedProofCasePartition, EvidenceRefusal, ExecutionFrontier,
    ExecutionProofCore, ExecutionRegionKind, FrontierPosition, OutcomeEvidenceFork,
    ProofExecutionContinuation, ProofExecutionState, checked_branch_fact_is_available,
    old_reference_state,
};
#[allow(unused_imports)]
pub(crate) use fact_keys::propositions_are_alpha_equal;
pub(crate) use fact_keys::{
    IntegerEqualityAlphaKey, PropositionIdentityKey, QuantifiedEquivalenceKey,
    SnapshotBlindPropositionKey, integer_equality_alpha_key, proposition_identity_key,
    quantified_equivalence_index_key, snapshot_blind_proposition_key,
};
#[cfg(test)]
pub(crate) use fact_keys::{alpha_proposition_key_visits, reset_alpha_proposition_key_visits};
pub(crate) use facts::ProofFacts;
pub(crate) use object::{
    ExecutionUpdateError, FrontierSplitError, ProofFocusError, ProofJoinError, ProofObject,
    ProofState, PropositionAssumptionContext, PropositionCloseError, PropositionIntroduction,
    PropositionSplitError,
};
pub(crate) use obligations::{
    CheckedProposition, FrontierObligation, FunctionOutcomeObligation, OutcomeProofCore,
    OutcomeProofState, ProofObligation, PropositionObligation,
};
pub(crate) use storage::{
    PersistentOrderedSet, PersistentSequence, PersistentSequenceIter, SharedValue, SharedVec,
};
