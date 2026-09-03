//! Experimental rich kernel for systems-code proofs.
//!
//! This module keeps the LCF shape: `Theorem` is an abstract object whose
//! constructor is not public. Public theorem constructors in this module are
//! Click axioms: trusted built-in operations that produce theorem objects
//! directly.
//!
mod api;
mod assumptions;
mod eval;
mod functions;
mod loops;
mod memory_provenance;
mod primitives;
pub(crate) mod proof;
mod reasoning;
mod spec;
mod termination;

pub use api::*;
pub(crate) use assumptions::{
    PureFactContextIdScope, arm_frame_composite_definitions, capture_implicit_reasoning_provenance,
    collect_reasoning_provenance, finite_forall_goal_instances,
    record_implicit_reasoning_provenance, with_search_attempt_rollback,
};
pub(crate) use eval::canonical_condition_fact;
pub(crate) use eval::canonical_form_of_load;
pub(crate) use eval::canonical_term;
pub(crate) use eval::canonicalized_offset_index_term;
#[cfg(test)]
pub(crate) use eval::count_canonical_at_creation_violations;
pub(crate) use eval::is_load_variable;
pub(crate) use eval::is_load_variable_defining_fact;
#[cfg(test)]
pub(crate) use eval::load_variable_for_cell_with_origin;
pub(crate) use eval::load_variable_for_term;
pub(crate) use eval::offsets_have_same_canonical_form;
pub(crate) use eval::proposition_mentions_registered_load_variable;
pub(crate) use eval::registered_load_for_variable;
pub(crate) use eval::registered_load_origin_for_variable;
pub(crate) use eval::resolve_pending_heap_allocations;
pub(crate) use eval::terms_have_same_canonical_form;
#[cfg(test)]
pub(crate) use eval::{load_variable_registry_len, with_load_variable_registry_capacity};
pub(crate) use functions::unreturned_allocation_at_function_exit;
pub(crate) use loops::{c_loop_condition_may_continue, c_loop_state_components_match_at_back_edge};
pub(crate) use memory_provenance::c_memory_load_is_unchanged;
pub use memory_provenance::*;
pub(crate) use primitives::resource_context_has_symbolic_int32_range_read;
pub use primitives::*;
pub(crate) use reasoning::memory_effect_write_pointers;
pub(crate) use reasoning::resolve_load_variables_from_registry;
pub(crate) use reasoning::resolve_load_variables_via;
pub(crate) use reasoning::resolve_minted_load_variables;
pub(crate) use reasoning::resource_context_has_read;
pub(crate) use reasoning::with_bounded_snapshot_comparison;
pub(crate) use reasoning::with_isolated_memory_resolution_fuel;
pub use termination::c_verified_function_termination_rules;

/// The bitvector variables one condition fact mentions, including those
/// inside load pointers and memories. Facts sharing none of these cannot
/// constrain each other or a goal that mentions none of them, which premise
/// search uses to skip candidate pairs no derivation could connect.
pub(crate) fn condition_fact_variables(
    proposition: &primitives::Proposition,
) -> std::collections::BTreeSet<primitives::Variable> {
    let mut variables = std::collections::BTreeSet::new();
    if let primitives::Proposition::ConditionIs(condition, _) = proposition {
        reasoning::collect_condition_bitvector_variables(condition, &mut variables);
    }
    variables
}

mod prelude {
    pub(super) use super::api::*;
    pub(super) use super::eval::*;
    pub(super) use super::functions::*;
    pub(super) use super::loops::*;
    pub(super) use super::primitives::*;
    pub(super) use super::reasoning::*;
    pub(super) use super::spec::*;
    pub(super) use std::collections::{BTreeMap, BTreeSet};
}

#[cfg(test)]
mod tests;

thread_local! {
    static VERIFICATION_SESSION_DEPTH: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// One verification's worth of kernel thread-local state.
///
/// The kernel keeps per-thread tables that are correct only within one
/// verification: the memory arena (snapshot ids and their DAG derivations;
/// interning dedups by content, so a later verification's snapshot with the
/// same content — a call havoc of a same-named callee, say — would inherit
/// the first verification's derivation and its mutable ranges), the load
/// registry (names are content-addressed, but their origins are live
/// snapshots of the arena that minted them), and the memo tables keyed by
/// arena ids or by fact-set content. Entering a session at the outermost
/// verification boundary starts a fresh arena and empties every such table,
/// so two verifications on one thread are as independent as two threads.
/// Nested entries (a verification inside a verification) keep the session.
/// `verifications_on_one_thread_are_independent` is the regression.
pub struct VerificationSession {
    fresh: bool,
}

impl VerificationSession {
    pub fn enter() -> Self {
        let outermost = VERIFICATION_SESSION_DEPTH.with(|depth| {
            let current = depth.get();
            depth.set(current + 1);
            current == 0
        });
        if outermost {
            primitives::start_fresh_c_memory_arena();
            eval::clear_load_variable_registry();
            eval::clear_load_canonicalization_caches();
            memory_provenance::clear_canonical_form_caches();
            memory_provenance::clear_provenance_memos();
            reasoning::memory_resolution::clear_canonical_memory_cache();
            reasoning::memory_resolution::clear_memory_resolution_memos();
            assumptions::clear_assumption_memos();
            assumptions::clear_context_inconsistency_memos();
            assumptions::clear_frame_expansion_memo();
            api::clear_context_free_forall_cache();
        }
        Self { fresh: outermost }
    }

    /// Whether this entry started the session (and so cleared the kernel's
    /// tables), as opposed to joining an enclosing one. Callers holding
    /// their own per-verification caches of kernel snapshots clear them on
    /// a fresh session.
    pub fn is_fresh(&self) -> bool {
        self.fresh
    }
}

impl Drop for VerificationSession {
    fn drop(&mut self) {
        VERIFICATION_SESSION_DEPTH.with(|depth| depth.set(depth.get() - 1));
    }
}
