//! Persistent checked proof-object infrastructure.
//!
//! This module is the kernel-owned home for proof state, branch topology,
//! checked transitions, and finalization authority. The migration begins with
//! branch topology; the remaining checked representation moves here in
//! independently green slices.

mod branches;

pub(crate) use branches::{BranchId, ProofBranches, SplitId};
