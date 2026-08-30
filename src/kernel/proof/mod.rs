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
mod storage;

pub(crate) use branches::{BranchId, ProofBranches, SplitId};
pub(crate) use execution::{
    ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition, LoopEffectGoal,
    ProofExecutionContinuation, old_reference_state,
};
pub(crate) use fact_keys::{
    QuantifiedEquivalenceKey, SnapshotBlindPropositionKey, quantified_equivalence_index_key,
    snapshot_blind_proposition_key,
};
pub(crate) use facts::ProofFacts;
pub(crate) use storage::{
    PersistentOrderedSet, PersistentSequence, PersistentSequenceIter, SharedValue, SharedVec,
};
