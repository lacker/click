//! Persistent checked proof-object infrastructure.
//!
//! This module is the kernel-owned home for proof state, branch topology,
//! checked transitions, and finalization authority. The migration begins with
//! branch topology; the remaining checked representation moves here in
//! independently green slices.

mod branches;
mod execution;
mod storage;

pub(crate) use branches::{BranchId, ProofBranches, SplitId};
pub(crate) use execution::{
    ExecutionFrontier, ExecutionRegionKind, FrontierPosition, LoopEffectGoal,
    ProofExecutionContinuation, old_reference_state,
};
pub(crate) use storage::{
    PersistentOrderedSet, PersistentSequence, PersistentSequenceIter, SharedValue, SharedVec,
};
