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
pub(in crate::kernel) mod variable_collection;
pub(super) use memory_resolution::*;
pub(super) use order_reasoning::*;
pub use path_facts::{LoweringIntroduction, LoweringIntroductions};
pub(super) use path_facts::{
    add_condition_path_fact, add_internal_condition_path_fact, add_path_fact,
    add_pointer_offset_equality_execution_pure_facts, add_proof_obligation,
    add_proof_obligation_with_context, add_required_proof_obligation_with_context,
    add_required_proof_obligation_without_search, append_required_proof_obligations,
    append_required_proof_obligations_under_path_context,
    append_required_proof_obligations_without_search, assumptions_with_path_context,
    assumptions_with_propositions, byte_offset_from_pointer_offset,
    common_pointer_offset_element_width, decide_with_facts, disprove_builtin_prop,
    element_count_from_bytes, element_index_from_offset, forall_int32,
    int32_element_count_from_bytes, int32_element_index_from_offset, memory_effect_execution_facts,
    memory_range_still_available, merge_execution_pure_facts_and_obligations, merge_facts,
    merge_obligations, pointer_byte_offset_from_base, public_execution_pure_facts,
    signed_const_add, solve_builtin_prop, wrap_path_context, wrap_path_context_with_introductions,
    wrap_proof_facts,
};
pub(crate) use substitution::*;
pub(crate) use variable_collection::resource_context_has_read;
pub(crate) use variable_collection::*;

pub(crate) fn memory_effect_write_pointers(facts: &[ExecutionPureFact]) -> BTreeSet<Pointer> {
    collect_memory_effect_write_pointers(facts)
}
