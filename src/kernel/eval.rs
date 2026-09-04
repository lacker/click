use super::prelude::*;

mod expression;
mod memory_loads;
mod operators;
mod statements;

/// Retain each sequential volatile access as a unique, kernel-certified fact.
/// The event id is allocated from the execution's existing fresh-variable
/// stream, so repeated accesses remain distinct even when they have the same
/// address and value. This is deliberately an access trace only: it does not
/// model threads, atomicity, signals, or external device state.
fn volatile_access_fact(
    next_kernel_variable: &mut u64,
    write: bool,
    pointer: Pointer,
    value_type: CType,
    value: CValue,
) -> ExecutionPureFact {
    let event_id = *next_kernel_variable;
    *next_kernel_variable += 1;
    let operation = if write { "write" } else { "read" };
    let pointer_type = value_type.pointer_to().unwrap_or(CType::UInt8Pointer);
    ExecutionPureFact::certified(Proposition::Predicate {
        name: format!("__click_volatile_{operation}_{event_id}"),
        arguments: vec![
            Term::CValue(CValue::typed_pointer(pointer, pointer_type)),
            Term::CValue(value),
        ],
    })
}

pub(super) use expression::*;
pub(crate) use memory_loads::canonical_condition_fact;
pub(crate) use memory_loads::canonical_form_of_load;
pub(crate) use memory_loads::canonical_term;
pub(crate) use memory_loads::canonicalized_offset_index_term;
pub(crate) use memory_loads::check_canonical_at_creation;
#[cfg(test)]
pub(crate) use memory_loads::count_canonical_at_creation_violations;
pub(crate) use memory_loads::is_load_variable;
pub(crate) use memory_loads::is_load_variable_defining_fact;
#[cfg(test)]
pub(crate) use memory_loads::load_variable_for_cell_with_origin;
pub(crate) use memory_loads::load_variable_for_term;
pub(crate) use memory_loads::offsets_have_same_canonical_form;
pub(crate) use memory_loads::proposition_mentions_registered_load_variable;
pub(crate) use memory_loads::registered_load_for_variable;
pub(crate) use memory_loads::registered_load_origin_for_variable;
pub(crate) use memory_loads::terms_have_same_canonical_form;
pub(crate) use memory_loads::viewed_as_memory_load;
pub(super) use memory_loads::*;
pub(crate) use memory_loads::{clear_load_canonicalization_caches, clear_load_variable_registry};
#[cfg(test)]
pub(crate) use memory_loads::{load_variable_registry_len, with_load_variable_registry_capacity};
pub(super) use operators::pointer_offset_by_bytes_paths;
pub(super) use operators::*;
pub(super) use statements::execute_c_realloc_assign_paths;
pub(crate) use statements::resolve_pending_heap_allocations;
pub(super) use statements::*;
