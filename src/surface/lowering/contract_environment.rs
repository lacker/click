//! The environment a contract or proof-side expression is read in: the
//! values and array references in scope at a state, the state a selector
//! names, and the pointer-offset spelling contract-lowered ranges share with
//! kernel execution. Nothing here evaluates an expression; that is the
//! kernel's, through the elaborated spec form.

use super::*;
use crate::kernel::{bits32_constant, constant_u32};
use crate::surface::diagnostics::describe_program_point_ref;

pub(in crate::surface) fn array_refs_with_memory(
    array_refs: &ClickArrayRefs,
    memory: &Memory,
) -> ClickArrayRefs {
    array_refs
        .iter()
        .map(|(name, array_ref)| {
            (
                name.clone(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: array_ref.pointer.clone(),
                    element_type: array_ref.element_type,
                },
            )
        })
        .collect()
}

pub(in crate::surface) fn contract_environment_at_state(
    parameter_values: &BTreeMap<String, ProgramValue>,
    array_refs: &ClickArrayRefs,
    state: &ExecutionState,
) -> (BTreeMap<String, ProgramValue>, ClickArrayRefs) {
    let mut values = parameter_values.clone();
    values.extend(
        state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone().into_native())),
    );

    let mut state_array_refs = array_refs_with_memory(array_refs, state.memory());
    // A parameter's array reference is read through the variable, exactly as
    // its value is above. `array_refs` was built from the caller's arguments,
    // so after the body assigns a pointer parameter it still holds the entry
    // pointer while `values` holds the current one; a pure function or theorem
    // argument naming that parameter then read two different pointers under
    // one name.
    for (name, value) in state.locals().object_values() {
        if let Some(pointer) = value.pointer()
            && let Some(array_ref) = state_array_refs.get_mut(name)
        {
            array_ref.pointer = pointer.pointer().clone();
        }
    }
    for (name, value, element_type) in state.locals().array_object_values() {
        let ProgramValue::Pointer(pointer) = value.clone() else {
            unreachable!("local array values are pointers")
        };
        // File-scope arrays remain in the state even when a parameter hides
        // their name. They must not replace that parameter's current value.
        if pointer.block.is_global_block() && parameter_values.contains_key(name) {
            continue;
        }
        values.insert(name.to_string(), value);
        state_array_refs.insert(
            name.to_string(),
            ClickArrayRef {
                memory: state.memory().clone(),
                pointer: pointer.pointer().clone(),
                element_type,
            },
        );
    }
    (values, state_array_refs)
}

/// [`contract_environment_at_state`] restricted to `names`: the same entry for
/// each named parameter or local, read by indexed lookups, so building it
/// costs the names a proposition mentions rather than every parameter and
/// local in scope. Without a parameter index, every parameter is read.
pub(in crate::surface) fn contract_environment_for_names(
    parameter_binding: ParameterBinding<'_>,
    names: &BTreeSet<String>,
    state: &ExecutionState,
) -> Result<(BTreeMap<String, ProgramValue>, ClickArrayRefs), ClickError> {
    let mut values = parameter_values_named(parameter_binding, names)?;
    let mut array_refs = array_refs_for_values(parameter_binding, &values, state.memory());
    for name in names {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(value) = state.locals().get(name) {
            // As in `contract_environment_at_state`, a parameter's array
            // reference follows the variable's current pointer.
            if let Some(pointer) = value.pointer()
                && let Some(array_ref) = array_refs.get_mut(name)
            {
                array_ref.pointer = pointer.pointer().clone();
            }
            values.insert(name.clone(), value.clone().into_native());
        } else if let Some((value, element_type)) = state.locals().array_object_value(name) {
            let ProgramValue::Pointer(pointer) = &value else {
                unreachable!("local array values are pointers")
            };
            if pointer.block.is_global_block() && values.contains_key(name) {
                continue;
            }
            array_refs.insert(
                name.clone(),
                ClickArrayRef {
                    memory: state.memory().clone(),
                    pointer: pointer.pointer().clone(),
                    element_type,
                },
            );
            values.insert(name.clone(), value);
        }
    }
    Ok((values, array_refs))
}

pub(in crate::surface) fn selected_program_state<'a>(
    selector: &ProgramPointSelector,
    function_entry_state: &'a ExecutionState,
    recorded_states: &'a RecordedStates,
) -> Result<&'a ExecutionState, String> {
    match selector {
        ProgramPointSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        }) => Ok(function_entry_state),
        ProgramPointSelector::Mark(name) => recorded_states.get(selector).ok_or_else(|| {
            format!(
                "unknown proof mark `{name}`; add `mark {name};` after the proof reaches that frontier"
            )
        }),
        ProgramPointSelector::ProgramPoint(point @ ProgramPointRef {
            region:
                CodeRegionRef::Region(_)
                | CodeRegionRef::Loop(_)
                | CodeRegionRef::Label(_),
            ..
        }) => recorded_states.get(selector).ok_or_else(|| {
            recorded_states
                .ambiguous_exit_refusal(selector)
                .unwrap_or_else(|| format!(
                    "no symbolic state was recorded for `{}`; run `step()` across that statement before using it in `at(...)`",
                    describe_program_point_ref(point)
                ))
        }),
        ProgramPointSelector::ProgramPoint(
            point @ ProgramPointRef {
                region: CodeRegionRef::Path(_),
                ..
            },
        ) => {
            let region = recorded_states.source_point(point)?;
            recorded_states.get(selector).ok_or_else(|| {
                if let Some(refusal) = recorded_states
                    .ambiguous_exit_refusal(&ProgramPointSelector::ProgramPoint(region.clone()))
                {
                    return refusal;
                }
                format!(
                    "no symbolic state was recorded for `{}`, which is `{}`; run `step()` across that statement before using it in `at(...)`",
                    describe_program_point_ref(point),
                    crate::surface::diagnostics::describe_program_point_ref_as_recorded(&region)
                )
            })
        }
        ProgramPointSelector::ProgramPoint(point) => Err(format!(
            "`at({}, ...)` is not supported in concrete evaluation yet",
            describe_program_point_ref(point)
        )),
    }
}

pub(in crate::surface) fn contract_array_ref_element_type(
    array_refs: &ClickArrayRefs,
    expression: &ContractExpression,
) -> Option<ProgramType> {
    match expression {
        ContractExpression::Binding(name)
        | ContractExpression::ProgramExpression(ProgramExpression::Variable(name))
        | ContractExpression::CBinding(name) => {
            array_refs.get(name).map(|array_ref| array_ref.element_type)
        }
        ContractExpression::Old(expression) => {
            contract_array_ref_element_type(array_refs, expression)
        }
        ContractExpression::At { expression, .. } => {
            contract_array_ref_element_type(array_refs, expression)
        }
        ContractExpression::Add(left, right) => contract_array_ref_element_type(array_refs, left)
            .or_else(|| contract_array_ref_element_type(array_refs, right)),
        ContractExpression::Subtract(left, _) => contract_array_ref_element_type(array_refs, left),
        _ => None,
    }
}

pub(in crate::surface) fn program_value_matches_click_type(
    value: &ProgramValue,
    interface_type: InterfaceType,
) -> bool {
    match (value.numeric_value(), interface_type) {
        (
            ProgramValue::Int8(_),
            InterfaceType::Int8
            | InterfaceType::Char(crate::languages::c::syntax::PlainChar::Signed),
        ) => true,
        (ProgramValue::Int16(_), InterfaceType::Int16)
        | (ProgramValue::Int32(_), InterfaceType::Int32)
        | (
            ProgramValue::UInt8(_),
            InterfaceType::Char(crate::languages::c::syntax::PlainChar::Unsigned)
            | InterfaceType::UInt8,
        )
        | (ProgramValue::UInt16(_), InterfaceType::UInt16)
        | (ProgramValue::UInt32(_), InterfaceType::UInt32)
        | (ProgramValue::Int64(_), InterfaceType::Int64(_))
        | (ProgramValue::UInt64(_), InterfaceType::UInt64(_))
        | (ProgramValue::Int128(_), InterfaceType::Int128)
        | (ProgramValue::UInt128(_), InterfaceType::UInt128) => true,
        (ProgramValue::Pointer(pointer), interface_type) if interface_type.is_pointer() => pointer
            .program_type()
            .pointer_types_compatible(interface_type.to_kernel_type()),
        _ => false,
    }
}

/// The built-in allocation authority is byte-addressed independently of the
/// pointer type used by the C caller. Its public declaration keeps the
/// historical `int32*` spelling, but allocator contracts may name any
/// modeled data pointer (including pointer-to-pointer storage).
pub(in crate::surface) fn program_value_matches_allocation_pointer(value: &ProgramValue) -> bool {
    matches!(
        value,
        ProgramValue::Pointer(pointer) if pointer.program_type().pointee_type().is_some()
    )
}

/// An `allocation` byte count: an `int32` or a `uint64` heap extent
/// (`design/heap-extents.md`, D4).
pub(in crate::surface) fn program_value_matches_allocation_extent(value: &ProgramValue) -> bool {
    matches!(
        value.numeric_value(),
        ProgramValue::Int32(_) | ProgramValue::UInt64(_)
    )
}

#[cfg(test)]
pub(in crate::surface) fn offset_pointer_by_int32_elements(
    pointer: Pointer,
    elements: MachineTerm,
) -> Pointer {
    offset_pointer_by_elements(pointer, elements, 4)
}

pub(in crate::surface) fn offset_pointer_by_elements(
    pointer: Pointer,
    elements: MachineTerm,
    element_width: u32,
) -> Pointer {
    // Contract and execution indices retain the same shared structure,
    // including a loaded index's state and read kind. The common producer
    // unwraps transitional registered names before constructing that index.
    let mut discarded_facts = crate::kernel::ExecutionFacts::new();
    let elements = crate::kernel::canonicalized_offset_index_term(elements, &mut discarded_facts);
    Pointer {
        block: pointer.block,
        offset: add_pointer_offset(
            pointer.offset,
            scale_int32_offset(elements, i64::from(element_width)),
        ),
    }
}

pub(in crate::surface) fn add_pointer_offset(
    left: PointerOffsetTerm,
    right: PointerOffsetTerm,
) -> PointerOffsetTerm {
    match (&left, &right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => {
            PointerOffsetTerm::Constant(left + right)
        }
        (PointerOffsetTerm::Constant(0), _) => right,
        (_, PointerOffsetTerm::Constant(0)) => left,
        _ => PointerOffsetTerm::Add(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn scale_int32_offset(
    value: MachineTerm,
    byte_width: i64,
) -> PointerOffsetTerm {
    match value {
        bits32_constant!(value) => {
            PointerOffsetTerm::Constant((constant_u32(value) as i32 as i64) * byte_width)
        }
        value => PointerOffsetTerm::scaled_int32_node(value, byte_width),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn globals(unrelated: usize) -> ExecutionState {
        let arrays = std::iter::once("bytes".to_string())
            .chain((0..unrelated).map(|i| format!("other_{i}")))
            .map(|name| {
                crate::kernel::GlobalArray::new_with_kernel_name(
                    &name,
                    &name,
                    ProgramType::UInt8,
                    2,
                    vec![crate::kernel::uint8(0); 2],
                )
            })
            .collect();
        let function = crate::kernel::ProgramFunction::new(
            ProgramType::Void,
            "shadow",
            vec![],
            crate::kernel::ProgramStatement::Skip,
        )
        .with_global_arrays(arrays);
        crate::kernel::program_function_entry_state(&ExecutionState::new(), &function, &[]).unwrap()
    }

    fn assert_bytes(
        values: &BTreeMap<String, ProgramValue>,
        arrays: &ClickArrayRefs,
        value: &ProgramValue,
        element_type: ProgramType,
    ) {
        assert_eq!(values.get("bytes"), Some(value));
        let ProgramValue::Pointer(pointer) = value else {
            unreachable!()
        };
        assert_eq!(arrays["bytes"].pointer, *pointer.pointer());
        assert_eq!(arrays["bytes"].element_type, element_type);
    }

    #[test]
    fn parameter_array_binding_hides_global_and_follows_reassignment() {
        let state = globals(0);
        let value = ProgramValue::typed_pointer(
            Pointer {
                block: "parameter-bytes".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramType::Int32Pointer,
        );
        let parameters = [crate::languages::interface::ImportedParameter::new(
            InterfaceType::Int32Pointer,
            "bytes".into(),
            None,
        )];
        let arguments = [ProgramExpression::Value(value.clone())];
        let binding = ParameterBinding::new(&parameters, &arguments);
        let values = BTreeMap::from([("bytes".to_string(), value.clone())]);
        let arrays = array_refs_for_parameters(&parameters, &values, state.memory());
        let names = BTreeSet::from(["bytes".to_string()]);
        let reassigned = ProgramValue::typed_pointer(
            Pointer {
                block: "reassigned-bytes".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramType::Int32Pointer,
        );
        for (state, expected) in [
            (state.clone(), value),
            (
                state.clone().with_local("bytes", reassigned.clone()),
                reassigned,
            ),
        ] {
            let (all_values, all_arrays) = contract_environment_at_state(&values, &arrays, &state);
            assert_bytes(&all_values, &all_arrays, &expected, ProgramType::Int32);
            let (named_values, named_arrays) =
                contract_environment_for_names(binding, &names, &state).unwrap();
            assert_bytes(&named_values, &named_arrays, &expected, ProgramType::Int32);
        }
        // Without a shadowing parameter, the same name still denotes the global.
        let expected =
            ProgramValue::typed_pointer(Memory::global_pointer("bytes"), ProgramType::UInt8Pointer);
        let (values, arrays) =
            contract_environment_at_state(&BTreeMap::new(), &BTreeMap::new(), &state);
        assert_bytes(&values, &arrays, &expected, ProgramType::UInt8);
        let (values, arrays) =
            contract_environment_for_names(ParameterBinding::default(), &names, &state).unwrap();
        assert_bytes(&values, &arrays, &expected, ProgramType::UInt8);
    }

    mod scaling_tests {
        include!("../../scaling_tests/surface/lowering/contract_environment.rs");
    }
}
