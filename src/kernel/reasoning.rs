use super::prelude::*;

mod order_reasoning;
mod path_facts;
mod substitution;
pub(crate) use substitution::resolve_load_variables_from_registry;
pub(crate) use substitution::resolve_load_variables_via;
pub(crate) use substitution::resolve_minted_load_pointer;
pub(crate) use substitution::resolve_minted_load_variables;
pub(crate) use substitution::resolve_symbolic_pointer_alias;
pub(in crate::kernel) use substitution::substitute_bitvector_variable_in_spec_proposition;
pub(in crate::kernel) mod memory_resolution;
pub(crate) use memory_resolution::pointers_disjoint_by_range_memoized;
pub(crate) use memory_resolution::with_bounded_snapshot_comparison;
pub(in crate::kernel) mod variable_collection;
pub(super) use memory_resolution::*;
pub(super) use order_reasoning::*;
pub(super) use path_facts::*;
pub(crate) use substitution::*;
pub(crate) use variable_collection::resource_context_has_read;
pub(super) use variable_collection::*;

pub(crate) fn memory_effect_write_pointers(facts: &[ExecutionPureFact]) -> BTreeSet<Pointer> {
    collect_memory_effect_write_pointers(facts)
}
