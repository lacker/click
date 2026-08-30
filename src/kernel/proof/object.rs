//! Persistent checked proof-object state.
//!
//! Language-specific names and presentation records are opaque parameters.
//! The kernel owns the persistent state shape and never treats those
//! attachments as evidence.

use super::{ProofBranch, ProofBranches};
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
