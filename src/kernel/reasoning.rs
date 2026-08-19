use super::prelude::*;

mod order_reasoning;
mod path_facts;
mod substitution;
pub(crate) use substitution::resolve_canonical_load_variables_from_registry;
pub(crate) use substitution::resolve_canonical_load_variables_via;
pub(crate) use substitution::resolve_minted_load_pointer;
pub(crate) use substitution::resolve_minted_load_variables;
pub(in crate::kernel) mod memory_resolution;
pub(in crate::kernel) mod variable_collection;
pub(super) use memory_resolution::*;
pub(super) use order_reasoning::*;
pub(super) use path_facts::*;
pub(super) use substitution::*;
pub(super) use variable_collection::*;

pub(crate) fn memory_effect_write_pointers(facts: &[ExecutionPureFact]) -> BTreeSet<Pointer> {
    collect_memory_effect_write_pointers(facts)
}
