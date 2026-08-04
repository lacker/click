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
mod primitives;
mod reasoning;
mod spec;
mod termination;

pub use api::*;
pub(crate) use assumptions::{AssumptionsIdScope, conditions_equal_ignoring_memories};
pub(crate) use eval::resolve_pending_heap_allocations;
pub(crate) use functions::unreturned_allocation_at_function_exit;
pub use primitives::*;
pub(crate) use reasoning::memory_effect_write_pointers;
pub use termination::c_verified_function_termination_rules;

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
