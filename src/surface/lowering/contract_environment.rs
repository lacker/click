//! The environment a contract or proof-side expression is read in: the
//! values and array references in scope at a state, the snapshot a selector
//! names, and the pointer-offset spelling contract-lowered ranges share with
//! kernel execution. Nothing here evaluates an expression; that is the
//! kernel's, through the elaborated spec form.

use super::*;
use crate::surface::diagnostics::describe_program_point_ref;

pub(in crate::surface) fn array_refs_with_memory(
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
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
    parameter_values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
) -> (BTreeMap<String, CValue>, ClickArrayRefs) {
    let mut values = parameter_values.clone();
    values.extend(
        state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone())),
    );

    let mut state_array_refs = array_refs_with_memory(array_refs, state.memory());
    for (name, value, element_type) in state.locals().array_object_values() {
        let CValue::Pointer(pointer) = value.clone() else {
            unreachable!("local array values are pointers")
        };
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

pub(in crate::surface) fn selected_snapshot_state<'a>(
    selector: &SnapshotSelector,
    function_entry_state: &'a CState,
    recorded_snapshots: &'a RecordedSnapshots,
) -> Result<&'a CState, String> {
    match selector {
        SnapshotSelector::ProgramPoint(ProgramPointRef {
            region: CodeRegionRef::Function,
            kind: ProgramPointKind::Entry,
        }) => Ok(function_entry_state),
        SnapshotSelector::Mark(name) => recorded_snapshots.get(selector).ok_or_else(|| {
            format!(
                "unknown proof mark `{name}`; add `mark {name};` after the proof reaches that frontier"
            )
        }),
        SnapshotSelector::ProgramPoint(point @ ProgramPointRef {
            region:
                CodeRegionRef::Statement(_)
                | CodeRegionRef::Loop(_)
                | CodeRegionRef::Label(_),
            ..
        }) => recorded_snapshots.get(selector).ok_or_else(|| {
            format!(
                "no state snapshot was recorded for `{}`; run `step()` across that statement before using it in `at(...)`",
                describe_program_point_ref(point)
            )
        }),
        SnapshotSelector::ProgramPoint(point) => Err(format!(
            "`at({}, ...)` is not supported in concrete evaluation yet",
            describe_program_point_ref(point)
        )),
    }
}

pub(in crate::surface) fn contract_array_ref_element_type(
    array_refs: &ClickArrayRefs,
    expression: &ContractExpression,
) -> Option<CType> {
    match expression {
        ContractExpression::CFragment(CExpression::Variable(name))
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

pub(in crate::surface) fn c_value_matches_click_type(value: &CValue, c_type: C0Type) -> bool {
    match (value, c_type) {
        (CValue::Int16(_), C0Type::Int16)
        | (CValue::Int32(_), C0Type::Int32)
        | (CValue::UInt8(_), C0Type::UInt8)
        | (CValue::UInt16(_), C0Type::UInt16)
        | (CValue::UInt32(_), C0Type::UInt32) => true,
        (CValue::Pointer(pointer), c_type) if c_type.is_pointer() => {
            pointer.c_type() == c_type.to_kernel_type()
        }
        _ => false,
    }
}

#[cfg(test)]
pub(in crate::surface) fn offset_pointer_by_int32_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
) -> Pointer {
    offset_pointer_by_elements(pointer, elements, 4)
}

pub(in crate::surface) fn offset_pointer_by_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
    element_width: u32,
) -> Pointer {
    // A loaded index never enters a pointer offset as a `MemoryLoad` term:
    // its load variable stands in for it, so contract-side offsets use the
    // same terms kernel execution does. Names are content-addressed, so no
    // fact stream is needed here — the defining equation is emitted wherever
    // the kernel evaluates the same load.
    let mut discarded_facts = Vec::new();
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
    value: Bitvector32Term,
    byte_width: i64,
) -> PointerOffsetTerm {
    match value {
        Bitvector32Term::Constant(value) => {
            PointerOffsetTerm::Constant((value as i32 as i64) * byte_width)
        }
        value => PointerOffsetTerm::Int32Scaled {
            value: Box::new(value),
            byte_width,
        },
    }
}
