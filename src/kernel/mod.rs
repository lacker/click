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
mod reasoning;
mod spec;
mod termination;

pub use api::*;
pub(crate) use assumptions::{
    PureFactContextIdScope, collect_reasoning_provenance, conditions_equal_ignoring_memories,
    finite_forall_goal_instances, record_implicit_reasoning_provenance,
    with_search_attempt_rollback,
};
pub(crate) use eval::canonical_load_variable;
pub(crate) use eval::canonical_load_variable_for_term;
pub(crate) use eval::resolve_pending_heap_allocations;
pub(crate) use functions::unreturned_allocation_at_function_exit;
pub use memory_provenance::*;
pub use primitives::*;
pub(crate) use reasoning::memory_effect_write_pointers;
pub(crate) use reasoning::resolve_minted_load_variables;
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
