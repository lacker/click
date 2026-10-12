//! Exact object binding for construction returns and ordinary constructors.
use super::*;

fn valid_layout(layout: &CAggregateLayout) -> bool {
    if layout.size_bytes() == 0
        || !layout.size_bytes().is_multiple_of(layout.alignment_bytes())
        || !layout.unions().is_empty()
    {
        return false;
    }
    let mut end = 0;
    for field in layout.fields() {
        crate::instrumentation::record_deterministic_work(1);
        let ty = field.c_type();
        let scalar = ty.is_pointer()
            || matches!(
                ty,
                CType::Bool
                    | CType::Int8
                    | CType::UInt8
                    | CType::Int16
                    | CType::UInt16
                    | CType::Int32
                    | CType::UInt32
                    | CType::Int64
                    | CType::UInt64
                    | CType::Int128
                    | CType::UInt128
                    | CType::Float32
                    | CType::Float64
            );
        if !scalar
            || field.offset_bytes() < end
            || !field.offset_bytes().is_multiple_of(ty.abi_alignment())
            || layout.alignment_bytes() < ty.abi_alignment()
        {
            return false;
        }
        let Some(next) = field.offset_bytes().checked_add(ty.byte_width()) else {
            return false;
        };
        if next > layout.size_bytes() {
            return false;
        }
        end = next;
    }
    true
}

fn destination<'a>(
    state: &'a CState,
    interface: &CFunctionContractInterface,
) -> Option<&'a CAggregateDestination> {
    let selected = state.aggregate_destination.as_deref()?;
    let layout = if let Some((_, layout)) = interface.construction_parameter() {
        if interface.aggregate_return_mode() != CAggregateReturnMode::Copy
            || interface.return_type() != CType::Void
            || interface.return_aggregate_layout().is_some()
        {
            return None;
        }
        layout
    } else {
        if interface.aggregate_return_mode() != CAggregateReturnMode::Construction
            || !interface.return_type().is_pointer()
        {
            return None;
        }
        interface.return_aggregate_layout()?
    };
    let offset = u32::try_from(selected.pointer.offset.as_const()?).ok()?;
    let end = offset.checked_add(layout.size_bytes())?;
    let constructor = interface.construction_parameter().is_some();
    let exact_raw_object = state
        .memory
        .heap
        .uninitialized_objects
        .get(&selected.pointer)
        == Some(&layout.size_bytes());
    let base = Pointer {
        block: selected.pointer.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let within_raw_parent = state
        .memory
        .heap
        .uninitialized_objects
        .get(&base)
        .is_some_and(|extent| end <= *extent);
    let storage_matches = match state.memory.block_size(&selected.pointer.block) {
        Some(size) => {
            let size = size.as_const()?;
            if !constructor && (offset != 0 || size != layout.size_bytes()) {
                return None;
            }
            end <= size
                && (selected.pointer.block.starts_with("local:")
                    || exact_raw_object
                    || within_raw_parent)
        }
        // A constructor entry describes only its object's footprint. Its
        // containing allocation can be larger, so source proof setup supplies
        // field liveness through the contract instead of fixing a block extent.
        None => constructor && (exact_raw_object || within_raw_parent),
    };
    if !interface.exceptional_signature().is_empty()
        || selected.layout != *layout
        || !valid_layout(layout)
        || !state
            .memory
            .has_object_layout_at(&selected.pointer, layout, constructor)
        || !offset.is_multiple_of(layout.alignment_bytes())
        || !storage_matches
        || selected.pointer.is_in_null_block()
        || state
            .memory
            .is_deallocated_heap_address(&selected.pointer, &PureFactContext::new())
        || state.memory.is_ended_local_address(&selected.pointer)
        || state.memory.is_read_only_block(&selected.pointer.block)
        || registered_block_alignment(&selected.pointer.block).unwrap_or(1)
            < u64::from(layout.alignment_bytes())
    {
        return None;
    }
    Some(selected)
}

pub(super) fn bind(
    caller: &CState,
    interface: &CFunctionContractInterface,
    callee: &mut CState,
) -> Option<()> {
    let parameter_destination;
    let selected_state = if let Some((index, layout)) = interface.construction_parameter() {
        let parameter = interface.parameters().get(index)?;
        if !parameter.c_type().is_pointer() || parameter.aggregate_layout().is_some() {
            return None;
        }
        let CValue::Pointer(value) = callee.locals.get(parameter.name())? else {
            return None;
        };
        parameter_destination = caller
            .clone()
            .with_aggregate_return_destination(value.pointer().clone(), layout.clone());
        &parameter_destination
    } else if interface.aggregate_return_mode() == CAggregateReturnMode::Copy {
        return Some(());
    } else {
        caller
    };
    let selected = destination(selected_state, interface)?;
    if interface
        .parameters()
        .iter()
        .any(|parameter| parameter.name() == C_CONTRACT_RESULT_NAME)
    {
        return None;
    }
    let writable = |pointer: &Pointer, bytes| {
        caller
            .resources
            .memory_write_range(pointer, bytes, &PureFactContext::new())
            .is_some()
            && crate::kernel::eval::memory_write_permission_outcome(
                caller,
                pointer,
                bytes,
                &PureFactContext::new(),
            )
            .is_none()
    };
    let authorized = if interface.construction_parameter().is_some() {
        // Native constructor contracts own fields, not padding. The body and
        // its ordinary effect/resource checks still justify every actual write.
        selected.layout.fields().iter().all(|field| {
            crate::instrumentation::record_deterministic_work(1);
            writable(
                &selected.pointer.offset_by_bytes(field.offset_bytes()),
                field.c_type().byte_width(),
            )
        })
    } else {
        writable(&selected.pointer, selected.layout.size_bytes())
    };
    if !authorized {
        return None;
    }
    callee.aggregate_destination = selected_state.aggregate_destination.clone();
    if interface.construction_parameter().is_none() {
        callee.locals.set_aggregate_object_at(
            C_CONTRACT_RESULT_NAME,
            selected.layout.clone(),
            selected.pointer.clone(),
        );
    }
    Some(())
}

pub(super) fn complete(
    state: &CState,
    interface: &CFunctionContractInterface,
    value: CValue,
) -> Result<CValue, AggregateReturnRefusal> {
    let selected = destination(state, interface).ok_or(AggregateReturnRefusal::InvalidValue)?;
    let CValue::Pointer(pointer) = &value else {
        return Err(AggregateReturnRefusal::InvalidValue);
    };
    if pointer.pointer() != &selected.pointer
        || state
            .locals
            .aggregate_object_pointer(C_CONTRACT_RESULT_NAME)
            != Some(&selected.pointer)
    {
        return Err(AggregateReturnRefusal::InvalidValue);
    }
    if aggregate_copy_reads_uninitialized(&state.memory, &selected.pointer, &selected.layout) {
        return Err(AggregateReturnRefusal::UninitializedRead);
    }
    Ok(value)
}

/// Check the entry-bound destination, even if the body reassigns its parameter.
pub(super) fn complete_parameter(
    state: &CState,
    interface: &CFunctionContractInterface,
) -> Option<CRuntimeError> {
    interface.construction_parameter()?;
    let Some(selected) = destination(state, interface) else {
        return Some(CRuntimeError::FunctionContract(
            "constructor destination is no longer live".into(),
        ));
    };
    aggregate_copy_reads_uninitialized(&state.memory, &selected.pointer, &selected.layout).then(
        || CRuntimeError::FunctionContract("constructor must initialize every value field".into()),
    )
}

pub(super) fn summary_result(
    state: &CState,
    interface: &CFunctionContractInterface,
) -> Option<CValue> {
    let selected = destination(state, interface)?;
    // `destination` checked an exact complete-object construction return.
    // Ordinary child constructors return void and never pass through here;
    // selecting their child path from its numeric address would lose the
    // original parent designation.
    let pointer = state
        .memory()
        .declared_aggregate_pointer(&selected.pointer, &selected.layout)?
        .with_type(interface.return_type())
        .with_pointee_constant(interface.return_pointee_is_constant());
    Some(CValue::Pointer(pointer))
}

/// A certified construction rule, or an explicit external construction-return
/// assumption, justifies these initialized fields. Ordinary owns clauses do not.
/// The call's existing effect transition forgets their old values first.
pub(super) fn initialize_summary(state: &mut CState, entry: &CState) {
    let selected = entry
        .aggregate_destination
        .as_ref()
        .expect("checked destination")
        .clone();
    for field in selected.layout.fields() {
        let pointer = selected.pointer.offset_by_bytes(field.offset_bytes());
        state.set_memory(
            state
                .memory
                .clone()
                .with_initialized_object(&pointer, field.c_type().byte_width()),
        );
    }
}
