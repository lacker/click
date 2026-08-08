use super::prelude::*;

mod memory_resolution;
mod order_reasoning;
mod path_facts;
mod substitution;
mod variable_collection;
pub(super) use memory_resolution::*;
pub(super) use order_reasoning::*;
pub(super) use path_facts::*;
pub(super) use substitution::*;
pub(super) use variable_collection::*;

pub(crate) fn memory_effect_write_pointers(facts: &[ExecutionPureFact]) -> BTreeSet<Pointer> {
    collect_memory_effect_write_pointers(facts)
}
