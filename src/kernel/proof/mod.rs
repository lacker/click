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
pub(crate) mod preservation;
// `kernel::reasoning` and `kernel::api` reach the state-aware alpha
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
pub(crate) mod integer_cast_identity;
mod integer_division_bounds;
mod integer_multiply_order;
pub(crate) mod integer_operation_identity;
mod integer_polynomial_identity;
mod integer_product_bounds;
mod integer_quotient_bound;
mod integer_quotient_shift;
mod integer_relation_transport;
pub(in crate::kernel) mod machine_source_match;
mod object;
mod obligations;
pub(crate) mod signed_arithmetic;
mod storage;
pub(crate) mod term_rewrite;

pub(crate) use branches::{BranchId, ProofBranch, ProofBranchState, ProofBranches, SplitId};
pub(crate) use execution::{
    CheckedBranchSplit, CheckedBranchSplitError, CheckedCallEvent, CheckedCallEvents,
    CheckedCallOutcomeSplit, CheckedExecutionEvent, CheckedProofCasePartition,
    ContractEntryAuthority, EvidenceRefusal, ExceptionalContinuation, ExecutionEvidence,
    ExecutionFrontier, ExecutionProofCore, ExecutionRegionKind, FrontierPosition, LoopControlExit,
    OpenedContractEntry, OutcomeEvidenceFork, ProofExecutionContinuation, ProofExecutionState,
    RejectedResourceRewriteFact, ResourceRewriteCheckError, UnestablishedInterfaceGoal,
    checked_branch_fact_is_available, old_reference_state, take_unestablished_interface_goal,
};
pub(crate) use execution::{CheckedReturnSeed, OutcomeForkArm};
#[allow(unused_imports)]
pub(crate) use fact_keys::propositions_are_alpha_equal;
pub(crate) use fact_keys::{
    MemoryErasedPropositionKey, PropositionIdentityKey, QuantifiedEquivalenceKey,
    memory_erased_proposition_key, proposition_identity_key,
    proposition_identity_key_declines_shape, quantified_equivalence_index_key,
};
#[cfg(test)]
pub(crate) use fact_keys::{alpha_proposition_key_visits, reset_alpha_proposition_key_visits};
#[cfg(test)]
pub(crate) use facts::reserved_fact_variable_entries;
#[cfg(test)]
pub(crate) use facts::take_fact_entry_counts;
pub(crate) use facts::{ProofFacts, PropositionSource, is_definedness_guard};
pub(in crate::kernel) use facts::{clear_rewritten_load_syntax_cache, clear_selected_atom_cache};
pub(crate) use object::{
    ExecutionUpdateError, FrontierSplitError, ProofFocusError, ProofJoinError, ProofObject,
    ProofState, PropositionCloseError, PropositionIntroduction, PropositionKnownContext,
    PropositionSplitError,
};
pub(crate) use obligations::{
    CheckedProposition, ClaimGoalError, ClaimGoalEvidence, ClaimResourceReceipt,
    ContractClosingGoal, ContractClosingGoals, FrontierObligation, FunctionOutcomeObligation,
    LiveAllocationObligation, OutcomeClaimGoals, OutcomeExecutionFacts, OutcomeGoal,
    OutcomeIdentity, OutcomeProofCore, OutcomeProofState, ProofObligation, PropositionObligation,
};
pub(crate) use storage::{
    PersistentOrderedSet, PersistentSequence, PersistentVector, SharedValue, SharedVec,
};

#[cfg(test)]
pub(crate) use facts::take_statement_priority_entries;
#[cfg(test)]
pub(crate) use storage::measure_sequence_copies;
