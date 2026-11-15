//! Program storage at function entry and aggregate values: static and global initialization, symbolic materialization of arrays and aggregate fields, zero initialization, and checked aggregate copies.

use super::*;

pub(super) fn initialize_program_function_globals_owned(
    mut state: ExecutionState,
    function: &ProgramFunction,
    initialize_missing_storage: bool,
) -> ExecutionState {
    for literal in function.string_literals() {
        let slot = Memory::string_literal_pointer(function.name(), literal.name(), literal.bytes());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_read_only_block(slot.block.clone(), literal.bytes().len() as u32),
            );
            for (offset, byte) in literal.bytes().iter().copied().enumerate() {
                if crate::instrumentation::deadline_exceeded() {
                    break;
                }
                state.set_memory(state.memory.clone().store(
                    Pointer {
                        block: slot.block.clone(),
                        offset: PointerOffsetTerm::Constant(offset as i64),
                    },
                    literal.element_value(byte),
                ));
            }
        }
        state.locals.set_array_object_at(
            literal.name().to_string(),
            literal.element_type(),
            literal.bytes().len() as u32,
            slot.clone(),
        );
        let literal_resource = ResourceFact::own_memory(MemoryRange::new_with_element_width(
            slot,
            MachineTerm::constant(0),
            MachineTerm::constant(literal.bytes().len() as u32),
            1,
        ));
        if !function.is_program_entry()
            && !state
                .resources
                .contains_exact_representation(&literal_resource)
        {
            state.resources = state
                .resources
                .clone()
                .unchecked_with_fact(literal_resource);
        }
    }
    for global in function.global_variables() {
        let slot = Memory::global_pointer(global.kernel_name());
        register_block_alignment(&slot.block, global.program_type().abi_alignment());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_classed_block_or_read_only(
                slot.block.clone(),
                global.declared_class(),
                global.program_type().byte_width(),
                global.is_constant(),
            ));
            if initialize_missing_storage || global.is_constant() {
                state.set_memory(
                    state
                        .memory
                        .clone()
                        .store(slot.clone(), global.initial_value().clone()),
                );
            }
        }
        state.locals.set_global_with_all_qualifiers(
            global.kernel_name().to_string(),
            global.program_type(),
            slot.clone(),
            global.is_volatile(),
            global.pointee_is_volatile(),
            global.is_constant(),
            global.pointee_is_constant(),
        );
        if global.kernel_name() != global.name() && !state.locals.contains_name(global.name()) {
            state.locals.set_global_with_all_qualifiers(
                global.name().to_string(),
                global.program_type(),
                slot,
                global.is_volatile(),
                global.pointee_is_volatile(),
                global.is_constant(),
                global.pointee_is_constant(),
            );
        }
    }
    for global_array in function.global_arrays() {
        let slot = Memory::global_pointer(global_array.kernel_name());
        register_block_alignment(&slot.block, global_array.element_type().abi_alignment());
        let bytes = global_array
            .length()
            .checked_mul(global_array.element_type().byte_width())
            .expect("validated C global array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_classed_block_or_read_only(
                slot.block.clone(),
                global_array.declared_class(),
                bytes,
                global_array.is_constant(),
            ));
            if initialize_missing_storage || global_array.is_constant() {
                state.set_memory(store_array_contents(
                    state.memory.clone(),
                    &slot,
                    global_array.element_type(),
                    global_array.initial_values(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            global_array.kernel_name().to_string(),
            global_array.element_type(),
            global_array.length(),
            slot.clone(),
            global_array.is_constant(),
        );
        if global_array.kernel_name() != global_array.name()
            && !state.locals.contains_name(global_array.name())
        {
            state.locals.set_array_object_at_with_constant(
                global_array.name().to_string(),
                global_array.element_type(),
                global_array.length(),
                slot,
                global_array.is_constant(),
            );
        }
    }
    for global_aggregate in function.global_aggregates() {
        let slot = Memory::global_pointer(global_aggregate.kernel_name());
        register_block_alignment(&slot.block, global_aggregate.layout().alignment_bytes());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_classed_block_or_read_only(
                slot.block.clone(),
                global_aggregate.declared_class.clone(),
                global_aggregate.layout().size_bytes(),
                global_aggregate.is_constant(),
            ));
            if initialize_missing_storage || global_aggregate.is_constant() {
                state.set_memory(zero_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate.layout(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate.initializers(),
                ));
            }
        }
        state.locals.set_aggregate_object_at_with_constant(
            global_aggregate.kernel_name().to_string(),
            global_aggregate.layout().clone(),
            slot.clone(),
            global_aggregate.is_constant(),
        );
        if global_aggregate.kernel_name() != global_aggregate.source_name()
            && !state.locals.contains_name(global_aggregate.source_name())
        {
            state.locals.set_aggregate_object_at_with_constant(
                global_aggregate.source_name().to_string(),
                global_aggregate.layout().clone(),
                slot,
                global_aggregate.is_constant(),
            );
        }
    }
    for global_aggregate_array in function.global_aggregate_arrays() {
        let slot = Memory::global_pointer(global_aggregate_array.kernel_name());
        register_block_alignment(
            &slot.block,
            global_aggregate_array.layout().alignment_bytes(),
        );
        let bytes = global_aggregate_array
            .length()
            .checked_mul(global_aggregate_array.layout().size_bytes())
            .expect("validated C global aggregate array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_classed_block_or_read_only(
                slot.block.clone(),
                global_aggregate_array.declared_class.clone(),
                bytes,
                global_aggregate_array.is_constant(),
            ));
            if initialize_missing_storage || global_aggregate_array.is_constant() {
                state.set_memory(zero_aggregate_array_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate_array.layout(),
                    global_aggregate_array.length(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    global_aggregate_array.initializers(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            global_aggregate_array.kernel_name().to_string(),
            ProgramType::UInt8,
            bytes,
            slot.clone(),
            global_aggregate_array.is_constant(),
        );
        if global_aggregate_array.kernel_name() != global_aggregate_array.source_name()
            && !state
                .locals
                .contains_name(global_aggregate_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                global_aggregate_array.source_name().to_string(),
                ProgramType::UInt8,
                bytes,
                slot,
                global_aggregate_array.is_constant(),
            );
        }
    }
    for static_local in function.static_variables() {
        let slot = Memory::static_pointer(function.name(), static_local.kernel_name());
        register_block_alignment(&slot.block, static_local.program_type().abi_alignment());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                static_local.program_type().byte_width(),
                static_local.is_constant(),
            ));
            // A qualified resource can materialize the cell before this
            // function's storage declaration is installed. Adding block
            // metadata must not overwrite that existing value.
            if (initialize_missing_storage || static_local.is_constant())
                && state.memory.known_value(&slot).is_none()
            {
                state.set_memory(
                    state
                        .memory
                        .clone()
                        .store(slot.clone(), static_local.initial_value().clone()),
                );
            }
        }
        state.locals.set_global_with_all_qualifiers(
            static_local.kernel_name().to_string(),
            static_local.program_type(),
            slot.clone(),
            static_local.is_volatile(),
            static_local.pointee_is_volatile(),
            static_local.is_constant(),
            static_local.pointee_is_constant(),
        );
        // Contract C fragments use the source spelling. A nested static may
        // have a kernel-only name to distinguish it from another object in a
        // sibling block; expose the spelling only when the callee has not
        // already installed a parameter or another visible binding with it.
        if static_local.kernel_name() != static_local.source_name()
            && !state.locals.contains_name(static_local.source_name())
        {
            state.locals.set_global_with_all_qualifiers(
                static_local.source_name().to_string(),
                static_local.program_type(),
                slot,
                static_local.is_volatile(),
                static_local.pointee_is_volatile(),
                static_local.is_constant(),
                static_local.pointee_is_constant(),
            );
        }
    }
    for static_array in function.static_arrays() {
        let slot = Memory::static_pointer(function.name(), static_array.kernel_name());
        register_block_alignment(&slot.block, static_array.element_type().abi_alignment());
        let bytes = static_array
            .length()
            .checked_mul(static_array.element_type().byte_width())
            .expect("validated C static local array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                bytes,
                static_array.is_constant(),
            ));
            if initialize_missing_storage || static_array.is_constant() {
                state.set_memory(store_array_contents(
                    state.memory.clone(),
                    &slot,
                    static_array.element_type(),
                    static_array.initial_values(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            static_array.kernel_name().to_string(),
            static_array.element_type(),
            static_array.length(),
            slot.clone(),
            static_array.is_constant(),
        );
        if static_array.kernel_name() != static_array.source_name()
            && !state.locals.contains_name(static_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                static_array.source_name().to_string(),
                static_array.element_type(),
                static_array.length(),
                slot,
                static_array.is_constant(),
            );
        }
    }
    for static_aggregate in function.static_aggregates() {
        let slot = Memory::static_pointer(function.name(), static_aggregate.kernel_name());
        register_block_alignment(&slot.block, static_aggregate.layout().alignment_bytes());
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                static_aggregate.layout().size_bytes(),
                static_aggregate.is_constant(),
            ));
            if initialize_missing_storage || static_aggregate.is_constant() {
                state.set_memory(zero_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate.layout(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate.initializers(),
                ));
            }
        }
        state.locals.set_aggregate_object_at_with_constant(
            static_aggregate.kernel_name().to_string(),
            static_aggregate.layout().clone(),
            slot.clone(),
            static_aggregate.is_constant(),
        );
        if static_aggregate.kernel_name() != static_aggregate.source_name()
            && !state.locals.contains_name(static_aggregate.source_name())
        {
            state.locals.set_aggregate_object_at_with_constant(
                static_aggregate.source_name().to_string(),
                static_aggregate.layout().clone(),
                slot,
                static_aggregate.is_constant(),
            );
        }
    }
    for static_aggregate_array in function.static_aggregate_arrays() {
        let slot = Memory::static_pointer(function.name(), static_aggregate_array.kernel_name());
        register_block_alignment(
            &slot.block,
            static_aggregate_array.layout().alignment_bytes(),
        );
        let bytes = static_aggregate_array
            .length()
            .checked_mul(static_aggregate_array.layout().size_bytes())
            .expect("validated C static aggregate array size");
        if !state.memory.has_block(&slot.block) {
            state.set_memory(state.memory.clone().with_block_or_read_only(
                slot.block.clone(),
                bytes,
                static_aggregate_array.is_constant(),
            ));
            if initialize_missing_storage || static_aggregate_array.is_constant() {
                state.set_memory(zero_aggregate_array_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate_array.layout(),
                    static_aggregate_array.length(),
                ));
                state.set_memory(initialize_aggregate_fields(
                    state.memory.clone(),
                    &slot,
                    static_aggregate_array.initializers(),
                ));
            }
        }
        state.locals.set_array_object_at_with_constant(
            static_aggregate_array.kernel_name().to_string(),
            ProgramType::UInt8,
            bytes,
            slot.clone(),
            static_aggregate_array.is_constant(),
        );
        if static_aggregate_array.kernel_name() != static_aggregate_array.source_name()
            && !state
                .locals
                .contains_name(static_aggregate_array.source_name())
        {
            state.locals.set_array_object_at_with_constant(
                static_aggregate_array.source_name().to_string(),
                ProgramType::UInt8,
                bytes,
                slot,
                static_aggregate_array.is_constant(),
            );
        }
    }
    state
}

/// Stores `contents` into the just-declared array storage at `base`, as a
/// store of each element's value in element order leaves it, at a cost of
/// the elements the initializer wrote rather than the declared length: the
/// elements holding the default are one constant [`CellRun`], and the
/// written ones are stored over it. Where a run is refused
/// ([`Memory::with_constant_run`]) every element is stored one by one.
///
/// [`CellRun`]: crate::kernel::primitives::CellRun
pub(super) fn store_array_contents(
    mut memory: Memory,
    base: &Pointer,
    element_type: ProgramType,
    contents: &crate::kernel::ArrayContents,
) -> Memory {
    let element =
        |index: u32| base.offset_by_bytes(index.saturating_mul(element_type.byte_width()));
    if contents.has_default_elements() {
        match memory.with_constant_run(
            base.clone(),
            element_type,
            contents.length(),
            contents.default_value().clone(),
        ) {
            Ok(mut stored) => {
                for (index, value) in contents.explicit_elements() {
                    // An explicit initializer list is as long as the source
                    // spells it; each element is a checkpoint.
                    if crate::instrumentation::deadline_exceeded() {
                        break;
                    }
                    stored = stored.store(element(*index), value.clone());
                }
                return stored;
            }
            Err(unchanged) => memory = unchanged,
        }
    }
    for index in 0..contents.length() {
        if crate::instrumentation::deadline_exceeded() {
            break;
        }
        memory = memory.store(element(index), contents.value_at(index).clone());
    }
    memory
}

/// The zero-initialized scalar fields of `layout`, as static storage holds
/// them before any initializer: each field's byte offset, how many elements
/// it holds (one, or an inline array's length), each element's width, and
/// the zero every element holds. A field kind with no modeled zero is left
/// out, as it is left without a cell. Unions are not included.
pub(super) fn aggregate_zero_fields(
    layout: &AggregateLayout,
) -> Vec<(u32, u32, u32, ProgramValue)> {
    let mut zero_fields = Vec::with_capacity(layout.fields().len());
    for field in layout.fields() {
        let (element_type, element_count) = match field.program_type() {
            ProgramType::Int8 => (field.program_type(), 1),
            ProgramType::Int16
            | ProgramType::Int32
            | ProgramType::UInt8
            | ProgramType::UInt16
            | ProgramType::UInt32
            | ProgramType::Int64
                | ProgramType::Int128
            | ProgramType::UInt64
                | ProgramType::UInt128
            | ProgramType::Float32
            | ProgramType::Float64
            | ProgramType::VoidPointer
            | ProgramType::Int128Pointer
            | ProgramType::UInt128Pointer
            | ProgramType::Int128PointerPointer
            | ProgramType::UInt128PointerPointer
            | ProgramType::Int32Pointer
            | ProgramType::UInt8Pointer
            // A signed plain `char` pointer field is an `int8*` cell.
            | ProgramType::Int8Pointer
            | ProgramType::Float32Pointer
            | ProgramType::Float64Pointer
            | ProgramType::Int32PointerPointer
            | ProgramType::UInt8PointerPointer
            | ProgramType::Int8PointerPointer
            | ProgramType::Float32PointerPointer
            | ProgramType::Float64PointerPointer
            // Static storage zero-initializes a callback field to a null
            // function pointer, just like a data-pointer field.
            | ProgramType::FunctionPointer(_) => (field.program_type(), 1),
            ProgramType::Int32Array(length) => (ProgramType::Int32, length),
            // A signed plain `char` array field holds `int8` cells.
            ProgramType::Int8Array(length) => (ProgramType::Int8, length),
            ProgramType::Int64Array(length) => (ProgramType::Int64, length),
            ProgramType::Int128Array(length) => (ProgramType::Int128, length),
            ProgramType::UInt64Array(length) => (ProgramType::UInt64, length),
            ProgramType::UInt128Array(length) => (ProgramType::UInt128, length),
            ProgramType::UInt8Array(length) => (ProgramType::UInt8, length),
            ProgramType::Float32Array(length) => (ProgramType::Float32, length),
            ProgramType::Float64Array(length) => (ProgramType::Float64, length),
            ProgramType::PointerArray(element, length) => (element.pointer_type(), length),
            _ => continue,
        };
        let zero = if matches!(field.program_type(), ProgramType::PointerArray(_, _)) {
            ProgramValue::typed_pointer(Pointer::null(), element_type)
        } else {
            match element_type {
                ProgramType::Parameter(_) | ProgramType::ParameterPointer(_) => {
                    unreachable!("an array element is a machine type")
                }
                ProgramType::Bool => ProgramValue::bool_constant(false),
                ProgramType::Int8 => int8(0),
                ProgramType::Int16 => int16(0),
                ProgramType::Int32 => int32(0),
                ProgramType::UInt8 => uint8(0),
                ProgramType::UInt16 => uint16(0),
                ProgramType::UInt32 => uint32(0),
                ProgramType::Int64 => ProgramValue::Int64(MachineTerm::int64_constant(0)),
                ProgramType::UInt64 => ProgramValue::UInt64(MachineTerm::uint64_constant(0)),
                ProgramType::Int128 => MachineIntegerType::Int128
                    .constant_value(
                        MachineIntegerConstant::from_signed(MachineIntegerType::Int128.format(), 0)
                            .unwrap(),
                    )
                    .unwrap(),
                ProgramType::UInt128 => MachineIntegerType::UInt128
                    .constant_value(
                        MachineIntegerConstant::from_unsigned(
                            MachineIntegerType::UInt128.format(),
                            0,
                        )
                        .unwrap(),
                    )
                    .unwrap(),
                ProgramType::Float32 => ProgramValue::Float32(MachineTerm::constant(0)),
                ProgramType::Float64 => ProgramValue::Float64(MachineTerm::uint64_constant(0)),
                ProgramType::Int128Pointer
                | ProgramType::UInt128Pointer
                | ProgramType::Int128PointerPointer
                | ProgramType::UInt128PointerPointer
                | ProgramType::Int32Pointer
                | ProgramType::UInt8Pointer
                | ProgramType::Int8Pointer
                | ProgramType::Float32Pointer
                | ProgramType::Float64Pointer
                | ProgramType::Int32PointerPointer
                | ProgramType::UInt8PointerPointer
                | ProgramType::Int8PointerPointer
                | ProgramType::Float32PointerPointer
                | ProgramType::Float64PointerPointer
                | ProgramType::FunctionPointer(_) => {
                    ProgramValue::typed_pointer(Pointer::null(), element_type)
                }
                ProgramType::Int8Array(_) => {
                    continue;
                }
                ProgramType::PointerArray(_, _) => continue,
                ProgramType::Int16Array(_)
                | ProgramType::Int32Array(_)
                | ProgramType::UInt8Array(_)
                | ProgramType::UInt16Array(_)
                | ProgramType::UInt32Array(_)
                | ProgramType::Int128Array(_)
                | ProgramType::Int64Array(_)
                | ProgramType::UInt128Array(_)
                | ProgramType::UInt64Array(_)
                | ProgramType::Float32Array(_)
                | ProgramType::Float64Array(_)
                | ProgramType::Void
                | ProgramType::VoidPointer
                | ProgramType::VoidPointerPointer => {
                    continue;
                }
                ProgramType::Int16Pointer
                | ProgramType::UInt16Pointer
                | ProgramType::UInt32Pointer
                | ProgramType::Int64Pointer
                | ProgramType::UInt64Pointer
                | ProgramType::Int16PointerPointer
                | ProgramType::UInt16PointerPointer
                | ProgramType::UInt32PointerPointer
                | ProgramType::Int64PointerPointer
                | ProgramType::UInt64PointerPointer => continue,
            }
        };
        zero_fields.push((
            field.offset_bytes(),
            element_count,
            element_type.byte_width(),
            zero,
        ));
    }
    zero_fields
}

pub(super) fn zero_aggregate_fields(
    mut memory: Memory,
    base: &Pointer,
    layout: &AggregateLayout,
) -> Memory {
    for (field_offset, element_count, element_width, zero) in aggregate_zero_fields(layout) {
        for index in 0..element_count {
            if crate::instrumentation::deadline_exceeded() {
                break;
            }
            let offset = field_offset
                .checked_add(
                    index
                        .checked_mul(element_width)
                        .expect("validated aggregate zero field offset"),
                )
                .expect("validated aggregate zero field offset");
            memory = memory.store(base.offset_by_bytes(offset), zero.clone());
        }
    }
    for union in layout.unions() {
        let union_base = base.offset_by_bytes(union.offset_bytes());
        let views = union
            .fields()
            .iter()
            .filter_map(|field| {
                zero_union_member_value(field.program_type()).map(|value| {
                    (
                        union_base.offset_by_bytes(field.offset_bytes()),
                        field.program_type(),
                        value,
                    )
                })
            })
            .collect();
        memory = memory.store_union_views(union_base, union.size_bytes(), views);
    }
    memory
}

pub(super) fn zero_union_member_value(program_type: ProgramType) -> Option<ProgramValue> {
    Some(match program_type {
        ProgramType::Int32 => int32(0),
        ProgramType::UInt8 => uint8(0),
        ProgramType::Int32Pointer
        | ProgramType::UInt8Pointer
        | ProgramType::Int32PointerPointer
        | ProgramType::UInt8PointerPointer
        | ProgramType::FunctionPointer(_) => {
            ProgramValue::typed_pointer(Pointer::null(), program_type)
        }
        _ => return None,
    })
}

pub(super) fn initialize_aggregate_fields(
    mut memory: Memory,
    base: &Pointer,
    initializers: &[AggregateInitializer],
) -> Memory {
    for initializer in initializers {
        memory = memory.store(
            base.offset_by_bytes(initializer.offset_bytes()),
            initializer.value().clone(),
        );
    }
    memory
}

/// The zero contents of `length` consecutive structs of `layout`, as
/// constant runs: a scalar field is one run over every element, stepping by
/// the struct's size, and an inline array field of `n` elements is `n` such
/// runs or, when the array is the longer of the two, one run per struct
/// stepping by the field's element width. So the runs cost the layout, and
/// never more than the struct count per array field, rather than the
/// struct count times the layout. `None` for a layout with unions, whose
/// zero views are typed overlays a run does not stand for.
pub(super) fn aggregate_array_zero_runs(
    layout: &AggregateLayout,
    length: u32,
) -> Option<Vec<ConstantRun>> {
    if !layout.unions().is_empty() || layout.size_bytes() == 0 {
        return None;
    }
    let stride = layout.size_bytes();
    let mut runs = Vec::new();
    for (field_offset, element_count, element_width, zero) in aggregate_zero_fields(layout) {
        if element_count <= length {
            for index in 0..element_count {
                // As in `symbolic_aggregate_cells`: a stopped run falls back
                // to the checkpointed element-by-element zeroing.
                if crate::instrumentation::deadline_exceeded() {
                    return None;
                }
                runs.push(ConstantRun {
                    offset: field_offset.checked_add(index.checked_mul(element_width)?)?,
                    stride,
                    count: length,
                    value: zero.clone(),
                });
            }
        } else {
            for element in 0..length {
                if crate::instrumentation::deadline_exceeded() {
                    return None;
                }
                runs.push(ConstantRun {
                    offset: element.checked_mul(stride)?.checked_add(field_offset)?,
                    stride: element_width,
                    count: element_count,
                    value: zero.clone(),
                });
            }
        }
    }
    Some(runs)
}

pub(super) fn zero_aggregate_array_fields(
    mut memory: Memory,
    base: &Pointer,
    layout: &AggregateLayout,
    length: u32,
) -> Memory {
    if let Some(runs) = aggregate_array_zero_runs(layout, length) {
        match memory.with_constant_runs(base, &runs) {
            Ok(filled) => return filled,
            Err(unchanged) => memory = unchanged,
        }
    }
    for index in 0..length {
        if crate::instrumentation::deadline_exceeded() {
            break;
        }
        let element_base = base.offset_by_bytes(
            index
                .checked_mul(layout.size_bytes())
                .expect("validated aggregate array zero offset"),
        );
        memory = zero_aggregate_fields(memory, &element_base, layout);
    }
    memory
}

/// Copy the modeled cells of an address-backed aggregate into a distinct
/// destination block. Fixed scalar-array fields and flattened embedded-struct
/// array leaves are copied one cell at a time. Pointer fields are
/// shallow-copied: the pointer value is duplicated,
/// but the pointed-to allocation is not. Missing cells in automatic storage
/// remain missing so an uninitialized source field stays uninitialized in the
/// copy; opaque/external source cells are represented by typed symbolic loads.
/// Whether a borrowed local view names storage its block actually has.
///
/// Only a range whose bounds are constant can be placed against the block's
/// extent. One with symbolic bounds keeps the previous treatment: it is the
/// caller's own stack object either way, and tightening that case belongs
/// with the range-arithmetic work rather than here.
pub(super) fn local_view_range_within_block(range: &MemoryRange, memory: &Memory) -> bool {
    // Signed, both endpoints. `as_const` answers `u32`, so a start of `-1`
    // arrived as `4294967295` and `end <= start` short-circuited to "in
    // bounds" for every range that begins below its block — the exact
    // opposite of what this asks. `pair[-1..3]` was placed inside a
    // two-element local while the contained `pair[0..3]` was refused.
    let (Some(start), Some(end)) = (range.signed_constant_start(), range.signed_constant_end())
    else {
        return true;
    };
    // An empty range names no storage, and `end < start` is how a range says
    // so: `memory_range_byte_count` scales the signed count, so this is the
    // same reading the extent guards use.
    if end <= start {
        return true;
    }
    let Some(bytes) = end
        .checked_sub(start)
        .and_then(|count| count.checked_mul(i64::from(range.element_width())))
        .and_then(|bytes| u32::try_from(bytes).ok())
    else {
        return false;
    };
    let base = range.start_pointer();
    memory.access_in_bounds(&base, bytes)
}

/// Check actual argument reads before allocating the callee's private copy.
pub(super) fn aggregate_argument_read_refusal(
    state: &ExecutionState,
    parameters: &[ProgramParameter],
    values: &[ProgramValue],
    assumptions: &PureFactContext,
) -> Option<FunctionOutcome> {
    for (parameter, value) in parameters.iter().zip(values) {
        let Some(layout) = parameter.aggregate_layout() else {
            continue;
        };
        let ProgramValue::Pointer(source) = value else {
            continue;
        };
        if let Some(refusal) = crate::kernel::eval::subobject_access_refusal(
            source.pointer(),
            source.extent(),
            layout.size_bytes(),
            &ExecutionFacts::new(),
            &[],
            assumptions,
        ) {
            return Some(FunctionOutcome::UndefinedBehavior(refusal));
        }
        // Actual calls use the same read boundary as ordinary aggregate
        // assignment. Entry images are evaluated values, not caller reads.
        if let Some(resource) = crate::kernel::eval::missing_aggregate_copy_read_resource(
            state,
            source,
            layout,
            assumptions,
        ) {
            return Some(FunctionOutcome::RuntimeError(
                RuntimeError::MissingResource {
                    resource: Box::new(resource),
                },
            ));
        }
        if aggregate_copy_reads_uninitialized(&state.memory, source.pointer(), layout) {
            return Some(FunctionOutcome::UndefinedBehavior(
                UndefinedBehavior::UninitializedRead,
            ));
        }
    }
    None
}

/// Whole-struct assignment copies every member (C11 6.5.16.1p2), but
/// `copy_aggregate_fields` skips a carried field with no source cell. Copying
/// from never-written source storage would then leave the destination's own
/// cell in place and readable. Every aggregate-copy path (direct assignment,
/// return materialization, return assignment) reports that skipped read as an
/// uninitialized read instead, matching what member-wise assignment reports
/// through the ordinary load path.
pub(super) fn aggregate_copy_reads_uninitialized(
    memory: &Memory,
    source: &Pointer,
    layout: &AggregateLayout,
) -> bool {
    // Mirror the carried-field classification in `copy_aggregate_fields`: a
    // field type this copy cannot carry drops the destination cells instead
    // of leaving them readable, so it cannot go stale here.
    for field in layout.fields() {
        if let ProgramType::UInt32Array(count) = field.program_type() {
            let source_field = source.offset_by_bytes(field.offset_bytes());
            let Some(bytes) = count.checked_mul(4) else {
                return true;
            };
            if bytes == 0
                || memory.has_initialized_bytes_under(&source_field, bytes, &PureFactContext::new())
                || memory.is_zeroed_heap_address(&source_field, bytes, &PureFactContext::new())
            {
                continue;
            }
            if memory.may_read_uninitialized_object(&source_field, bytes)
                || memory.is_uninitialized_heap_address(
                    &source_field,
                    bytes,
                    &PureFactContext::new(),
                )
                || (source_field.block.is_local_block()
                    && memory.access_in_bounds(&source_field, bytes))
            {
                return true;
            }
        }

        let (element_type, element_count) = match field.program_type() {
            ProgramType::Int8 => (field.program_type(), 1),
            ProgramType::Int16
            | ProgramType::Int32
            | ProgramType::UInt8
            | ProgramType::UInt16
            | ProgramType::UInt32
            | ProgramType::Int64
            | ProgramType::Int128
            | ProgramType::UInt64
            | ProgramType::UInt128
            | ProgramType::Float32
            | ProgramType::Float64 => (field.program_type(), 1),
            ProgramType::Int32Array(length) => (ProgramType::Int32, length),
            ProgramType::UInt32Array(length) => (ProgramType::UInt32, length),
            ProgramType::Int64Array(length) => (ProgramType::Int64, length),
            ProgramType::Int128Array(length) => (ProgramType::Int128, length),
            ProgramType::UInt64Array(length) => (ProgramType::UInt64, length),
            ProgramType::UInt128Array(length) => (ProgramType::UInt128, length),
            ProgramType::UInt8Array(length) => (ProgramType::UInt8, length),
            ProgramType::Int32Pointer
            | ProgramType::UInt8Pointer
            | ProgramType::Int32PointerPointer
            | ProgramType::UInt8PointerPointer
            | ProgramType::FunctionPointer(_) => (field.program_type(), 1),
            _ => continue,
        };
        for index in 0..element_count {
            let element_offset = field
                .offset_bytes()
                .checked_add(
                    index
                        .checked_mul(element_type.byte_width())
                        .expect("validated aggregate field offset"),
                )
                .expect("validated aggregate field offset");
            if uninitialized_aggregate_copy_source_cell(
                memory,
                &source.offset_by_bytes(element_offset),
                element_type,
            ) {
                return true;
            }
        }
    }
    for union in layout.unions() {
        let union_source = source.offset_by_bytes(union.offset_bytes());
        // A union with any readable member is initialized storage: the copy
        // carries the active member view and skips the rest, so no member
        // read is uninitialized. Only a wholly unread union can leave the
        // destination holding a stale cell.
        let union_initialized = union.fields().iter().any(|field| {
            let source_field = union_source.offset_by_bytes(field.offset_bytes());
            // Mirror `copy_aggregate_union_member`: a value stored through
            // any member is carried.
            memory
                .known_union_value(&source_field, field.program_type())
                .is_some()
                || memory
                    .known_value(&source_field)
                    .is_some_and(|value| field.program_type().accepts(&value))
                // A member whose cached view was forgotten but whose bytes
                // the initialization record holds was written all the same.
                || memory.has_initialized_bytes_at(&source_field, field.program_type().byte_width())
        });
        if union_initialized {
            continue;
        }
        for field in union.fields() {
            let source_field = union_source.offset_by_bytes(field.offset_bytes());
            if uninitialized_aggregate_copy_source_cell(memory, &source_field, field.program_type())
            {
                return true;
            }
        }
    }
    false
}

/// Mirrors the silent skip in `copy_aggregate_fields`: no source cell, bytes
/// the initialization record does not hold, and not a zeroed heap address.
/// Reading such a cell is a read of uninitialized
/// storage when the address is a live local or an uninitialized heap cell;
/// anything else (external or symbolic memory) reads back as an unconstrained
/// symbolic load rather than stale storage.
pub(super) fn uninitialized_aggregate_copy_source_cell(
    memory: &Memory,
    source_field: &Pointer,
    element_type: ProgramType,
) -> bool {
    if memory.known_value(source_field).is_some()
        || memory.has_initialized_bytes_at(source_field, element_type.byte_width())
    {
        return false;
    }
    if memory.is_zeroed_heap_address(
        source_field,
        element_type.byte_width(),
        &PureFactContext::new(),
    ) {
        return false;
    }
    memory.may_read_uninitialized_object(source_field, element_type.byte_width())
        || memory.is_uninitialized_heap_address(
            source_field,
            element_type.byte_width(),
            &PureFactContext::new(),
        )
        || (source_field.block.is_local_block()
            && memory.access_in_bounds(source_field, element_type.byte_width()))
}

/// Whether a copy's source field is storage of this memory that holds no
/// value the copy can carry: a block it allocates (not symbolic or temporary
/// storage), in bounds, with no cached value or zero guarantee (the callers
/// ask those first) and with bytes the initialization record does not hold.
/// The copy skips such a field, and `aggregate_copy_reads_uninitialized`
/// has already refused it where it is uninitialized. A field whose cached
/// value was forgotten (by a store the facts could not place, or a loop,
/// call or join havoc) but whose bytes the record holds was written all the
/// same: the copy carries its unknown value as the typed load of the source,
/// as for external storage, so the destination is initialized too.
pub(super) fn aggregate_copy_source_holds_nothing(
    memory: &Memory,
    source_field: &Pointer,
    element_type: ProgramType,
) -> bool {
    // Static storage is initialized for the whole run: a field function entry
    // left without a cell holds its entry value, which the copy carries.
    memory.has_block(&source_field.block)
        && !source_field.block.is_static_storage_block()
        && !matches!(
            source_field.block,
            PointerBlock::Symbolic(_) | PointerBlock::Temporary(_)
        )
        && memory.access_in_bounds(source_field, element_type.byte_width())
        && !memory.has_initialized_bytes_at(source_field, element_type.byte_width())
}

/// Every aggregate-copy path goes through this wrapper so a copy from
/// uninitialized source storage is reported as an uninitialized read instead
/// of silently keeping the destination's old value. The raw
/// `copy_aggregate_fields` is deliberately module-private; new call sites in
/// other modules must use this checked form.
pub(in crate::kernel) fn copy_aggregate_fields_checked(
    memory: Memory,
    source: &Pointer,
    destination: &Pointer,
    layout: &AggregateLayout,
) -> Result<Memory, UndefinedBehavior> {
    if aggregate_copy_reads_uninitialized(&memory, source, layout) {
        return Err(UndefinedBehavior::UninitializedRead);
    }
    Ok(copy_aggregate_fields(memory, source, destination, layout))
}

// Module-private on purpose: cross-module aggregate copies must go through
// `copy_aggregate_fields_checked` so the uninitialized-source read is always
// reported. Actual call arguments are checked before binding; entry proof
// images use the raw form because their incoming aggregate values are evaluated.
pub(super) fn copy_aggregate_fields(
    mut memory: Memory,
    source: &Pointer,
    destination: &Pointer,
    layout: &AggregateLayout,
) -> Memory {
    for field in layout.fields() {
        if let ProgramType::UInt32Array(count) = field.program_type() {
            let source_field = source.offset_by_bytes(field.offset_bytes());
            let target_field = destination.offset_by_bytes(field.offset_bytes());
            if let Ok(copied) = memory.clone().write_scalar_array_region(
                &target_field,
                ProgramType::UInt32,
                count,
                ProgramValue::typed_pointer(source_field, ProgramType::UInt32Pointer),
                true,
                false,
                &PureFactContext::new(),
            ) {
                memory = copied;
                continue;
            }
            // Forgotten initialized values stay an immutable typed state,
            // without generating one load for each element of the field.
            if let Ok(copied) = memory.clone().write_scalar_array_state(
                &target_field,
                ProgramType::UInt32,
                count,
                ProgramValue::typed_pointer(
                    source.offset_by_bytes(field.offset_bytes()),
                    ProgramType::UInt32Pointer,
                ),
                true,
                false,
                &PureFactContext::new(),
            ) {
                memory = copied;
                continue;
            }
        }

        let (element_type, element_count) = match field.program_type() {
            ProgramType::Int8 => (field.program_type(), 1),
            ProgramType::Int16
            | ProgramType::Int32
            | ProgramType::UInt8
            | ProgramType::UInt16
            | ProgramType::UInt32
            | ProgramType::Int64
                | ProgramType::Int128
            | ProgramType::UInt64
                | ProgramType::UInt128
            | ProgramType::Float32
            | ProgramType::Float64
            // A generic struct's field of an abstract type parameter.
            | ProgramType::Parameter(_) => (field.program_type(), 1),
            ProgramType::Int32Array(length) => (ProgramType::Int32, length),
            ProgramType::UInt32Array(length) => (ProgramType::UInt32, length),
            ProgramType::Int64Array(length) => (ProgramType::Int64, length),
            ProgramType::Int128Array(length) => (ProgramType::Int128, length),
            ProgramType::UInt64Array(length) => (ProgramType::UInt64, length),
            ProgramType::UInt128Array(length) => (ProgramType::UInt128, length),
            ProgramType::UInt8Array(length) => (ProgramType::UInt8, length),
            ProgramType::Int32Pointer
            | ProgramType::UInt8Pointer
            | ProgramType::Int32PointerPointer
            | ProgramType::UInt8PointerPointer
            // A callback field is an eight-byte pointer value; carry it so a
            // copied table still dispatches to the same concrete target.
            | ProgramType::FunctionPointer(_) => (field.program_type(), 1),
            // A field this copy cannot carry must not leave the destination's
            // previous value in place: C copies every member, so a stale cell
            // would be readable as the destination's old contents. Drop those
            // cells instead, which reads back as unknown rather than wrong.
            unsupported => {
                memory = memory.without_field_cells(destination, field.offset_bytes(), unsupported);
                continue;
            }
        };
        for index in 0..element_count {
            let element_offset = field
                .offset_bytes()
                .checked_add(
                    index
                        .checked_mul(element_type.byte_width())
                        .expect("validated aggregate field offset"),
                )
                .expect("validated aggregate field offset");
            let source_field = source.offset_by_bytes(element_offset);
            let destination_field = destination.offset_by_bytes(element_offset);
            if let Some(value) = memory.known_retained_value(&source_field) {
                memory = memory.store_retained(destination_field, value);
                continue;
            }
            let value = (|| {
                if memory.is_zeroed_heap_address(
                    &source_field,
                    element_type.byte_width(),
                    &PureFactContext::new(),
                ) {
                    return match element_type {
                        ProgramType::Int8 => Some(int8(0)),
                        ProgramType::Int16 => Some(int16(0)),
                        ProgramType::Int32 => Some(int32(0)),
                        ProgramType::UInt8 => Some(uint8(0)),
                        ProgramType::Int32Pointer
                        | ProgramType::UInt8Pointer
                        | ProgramType::Int32PointerPointer
                        | ProgramType::UInt8PointerPointer => {
                            Some(ProgramValue::typed_pointer(Pointer::null(), element_type))
                        }
                        ProgramType::UInt16 => Some(uint16(0)),
                        ProgramType::UInt32 => Some(uint32(0)),
                        ProgramType::Int64 => {
                            Some(ProgramValue::Int64(MachineTerm::int64_constant(0)))
                        }
                        ProgramType::UInt64 => {
                            Some(ProgramValue::UInt64(MachineTerm::uint64_constant(0)))
                        }
                        ProgramType::Float32 => {
                            Some(ProgramValue::Float32(MachineTerm::constant(0)))
                        }
                        ProgramType::Float64 => {
                            Some(ProgramValue::Float64(MachineTerm::uint64_constant(0)))
                        }
                        _ => None,
                    };
                }
                if aggregate_copy_source_holds_nothing(&memory, &source_field, element_type) {
                    return None;
                }
                match element_type {
                    ProgramType::Int8 => {
                        Some(ProgramValue::Int8(crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_memory(memory.clone()),
                            source_field,
                            LoadKind::of_type(element_type)?,
                        )))
                    }
                    ProgramType::Int16 => {
                        Some(ProgramValue::Int16(crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_memory(memory.clone()),
                            source_field,
                            LoadKind::of_type(element_type)?,
                        )))
                    }
                    ProgramType::Int32 => {
                        Some(ProgramValue::Int32(crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_memory(memory.clone()),
                            source_field,
                            LoadKind::of_type(element_type)?,
                        )))
                    }
                    ProgramType::UInt8 => {
                        Some(ProgramValue::UInt8(crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_memory(memory.clone()),
                            source_field,
                            LoadKind::of_type(element_type)?,
                        )))
                    }
                    ProgramType::Int32Pointer
                    | ProgramType::UInt8Pointer
                    | ProgramType::Int32PointerPointer
                    | ProgramType::UInt8PointerPointer => {
                        // An unknown pointer is the value read from this cell,
                        // not an offset in the object holding it. Use the same
                        // canonical typed read as ordinary pointer loads so a
                        // trivial copy preserves provenance and checked aliases.
                        crate::kernel::eval::symbolic_storage_cell_value(
                            &memory,
                            &source_field,
                            element_type,
                            true,
                        )
                    }
                    ProgramType::UInt16 => {
                        Some(ProgramValue::UInt16(crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_memory(memory.clone()),
                            source_field,
                            LoadKind::of_type(element_type)?,
                        )))
                    }
                    ProgramType::UInt32 => {
                        Some(ProgramValue::UInt32(crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_memory(memory.clone()),
                            source_field,
                            LoadKind::of_type(element_type)?,
                        )))
                    }
                    ProgramType::Int64 => {
                        Some(ProgramValue::Int64(crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_memory(memory.clone()),
                            source_field,
                            LoadKind::of_type(element_type)?,
                        )))
                    }
                    ProgramType::UInt64 => {
                        Some(ProgramValue::UInt64(crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_memory(memory.clone()),
                            source_field,
                            LoadKind::of_type(element_type)?,
                        )))
                    }
                    ProgramType::Float32 => Some(ProgramValue::Float32(
                        crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_memory(memory.clone()),
                            source_field,
                            LoadKind::of_type(element_type)?,
                        ),
                    )),
                    ProgramType::Float64 => Some(ProgramValue::Float64(
                        crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_memory(memory.clone()),
                            source_field,
                            LoadKind::of_type(element_type)?,
                        ),
                    )),
                    ProgramType::Parameter(_) => {
                        crate::kernel::eval::symbolic_load_value_unrecorded(
                            &memory,
                            &source_field,
                            element_type,
                        )
                    }
                    _ => None,
                }
            })();
            if let Some(value) = value {
                memory = memory.store(destination_field, value);
            }
        }
    }
    for union in layout.unions() {
        let source_union = source.offset_by_bytes(union.offset_bytes());
        let destination_union = destination.offset_by_bytes(union.offset_bytes());
        let views = union
            .fields()
            .iter()
            .filter_map(|field| {
                let source_field = source_union.offset_by_bytes(field.offset_bytes());
                copy_retained_aggregate_union_member(&memory, &source_field, field.program_type())
                    .map(|value| {
                        (
                            destination_union.offset_by_bytes(field.offset_bytes()),
                            field.program_type(),
                            value,
                        )
                    })
            })
            .collect();
        memory = memory.store_retained_union_views(destination_union, union.size_bytes(), views);
    }
    memory
}

pub(super) fn copy_retained_aggregate_union_member(
    memory: &Memory,
    source_field: &Pointer,
    element_type: ProgramType,
) -> Option<ExecutionValue> {
    if let Some(value) = memory.known_retained_union_value(source_field, element_type) {
        return Some(value);
    }
    if let Some(value) = memory.known_retained_value(source_field)
        && element_type.accepts(&value.native())
    {
        return Some(value);
    }
    if memory.is_zeroed_heap_address(
        source_field,
        element_type.byte_width(),
        &PureFactContext::new(),
    ) {
        return zero_union_member_value(element_type).map(Into::into);
    }
    if aggregate_copy_source_holds_nothing(memory, source_field, element_type) {
        return None;
    }
    // An unknown object pointer is the value read from this cell, as an
    // ordinary pointer field's is: not an address in the object holding it.
    if element_type.is_object_pointer() {
        return crate::kernel::eval::symbolic_storage_cell_value(
            memory,
            source_field,
            element_type,
            true,
        )
        .map(Into::into);
    }
    let load = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_memory(memory.clone()),
        source_field.clone(),
        LoadKind::of_type(element_type)?,
    );
    Some(
        (match element_type {
            ProgramType::Int32 => ProgramValue::Int32(load),
            ProgramType::UInt8 => ProgramValue::UInt8(load),
            ProgramType::Int32Pointer
            | ProgramType::UInt8Pointer
            | ProgramType::Int32PointerPointer
            | ProgramType::UInt8PointerPointer
            | ProgramType::FunctionPointer(_) => {
                let pointer = if matches!(element_type, ProgramType::FunctionPointer(_)) {
                    match load {
                        MachineTerm::Variable(variable) => Pointer::symbolic_function(variable),
                        load => Pointer {
                            block: source_field.block.clone(),
                            offset: PointerOffsetTerm::scale_int32(load, 1),
                        },
                    }
                } else {
                    let pointee_type = element_type.pointee_type()?;
                    Pointer {
                        block: source_field.block.clone(),
                        offset: PointerOffsetTerm::scale_int32(
                            load,
                            i64::from(pointee_type.byte_width()),
                        ),
                    }
                };
                ProgramValue::typed_pointer(pointer, element_type)
            }
            _ => return None,
        })
        .into(),
    )
}
