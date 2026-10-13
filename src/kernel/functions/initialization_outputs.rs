//! Explicit initialization effects select a mutable entry pointer. Numerical
//! contents and resource ownership never issue an initialization effect.
use super::*;

pub(crate) fn resolve_initialization_output(
    state: &CState,
    interface: &CFunctionContractInterface,
    output: &CInitializationOutput,
) -> Option<CPointerValue> {
    let parameter = interface.parameters().get(output.parameter_index())?;
    let value = if let Some(selection) = output.field() {
        let layout = parameter.aggregate_layout()?;
        if !layout.selects_layout_path(&[], selection.layout()) {
            return None;
        }
        let base = state.locals().aggregate_object_pointer(parameter.name())?;
        let field = layout
            .fields()
            .iter()
            .find(|field| field.name() == selection.path()[0])?;
        let address = base.offset_by_bytes(field.offset_bytes());
        // This is the initialized private image of a by-value argument. Its
        // exact full-width cell, not a byte reconstruction or equality premise,
        // provides the frozen carrier.
        let value = state.memory().known_value(&address)?;
        if value.byte_width() != 8
            || !state
                .memory()
                .has_initialized_bytes_under(&address, 8, &PureFactContext::new())
        {
            return None;
        }
        value
    } else {
        state.locals().get(parameter.name())?.clone()
    };
    let CValue::Pointer(pointer) = value else {
        return None;
    };
    (pointer.c_type() == CType::UInt8Pointer && !pointer.pointee_constant()).then_some(pointer)
}

/// Called after by-value binding and before contract resource naming.
pub(crate) fn mark_initialization_output_fields(
    mut state: CState,
    interface: &CFunctionContractInterface,
) -> Option<CState> {
    for output in interface.initialization_output_selectors()? {
        if output.field().is_none() || output.bytes() == 0 {
            continue;
        }
        let pointer = resolve_initialization_output(&state, interface, &output)?;
        state.set_memory(
            state
                .memory()
                .clone()
                .with_uninitialized_object(pointer.pointer().clone(), output.bytes()),
        );
    }
    Some(state)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        c_function, c_parameter, c_return, c_typed_load, c_variable, c_void_value,
    };

    fn field_output(layout: CAggregateLayout, selected_layout: CAggregateLayout) -> CFunction {
        let selection = Arc::new(CAggregateMemberSelection {
            layout: Arc::new(selected_layout),
            path: vec!["data".into()].into(),
            value_type: CType::UInt8Pointer,
        });
        let expression = c_typed_load(
            CExpression::MemberAddress {
                object: Box::new(c_variable("out")),
                selection,
            },
            CType::UInt8Pointer,
        );
        c_function(
            CType::Void,
            "fill",
            vec![c_parameter("out", CType::Int32Pointer).with_aggregate_layout(layout)],
            c_return(c_void_value()),
        )
        .with_contract(
            vec![],
            vec![SpecProposition::MemoryInitialized {
                memory: SpecMemory::Current,
                base: SpecExpression::LoopEntrySnapshot(Box::new(SpecExpression::CExpression(
                    expression,
                ))),
                bytes: 4,
            }],
            vec![],
            vec![],
            true,
        )
    }

    #[test]
    fn output_field_selector_requires_exact_by_value_layout() {
        let layout = CAggregateLayout::new(
            16,
            8,
            vec![CAggregateField::new("data", 0, CType::UInt8Pointer)],
        );
        let function = field_output(layout.clone(), layout.clone());
        let outputs = function
            .contract_interface()
            .initialization_output_selectors()
            .unwrap();
        assert_eq!(outputs.len(), 1);
        assert!(outputs[0].field().is_some());
        assert!(
            function
                .contract_interface()
                .initialization_outputs()
                .is_none()
        );
        assert!(crate::kernel::c_external_function_rule(function).is_none());
        let wrong = CAggregateLayout::new(
            16,
            8,
            vec![CAggregateField::new("data", 8, CType::UInt8Pointer)],
        );
        assert!(
            field_output(layout, wrong)
                .contract_interface()
                .initialization_output_selectors()
                .is_none()
        );
    }

    #[test]
    fn frozen_output_field_uses_initialized_full_pointer_cell() {
        let layout = CAggregateLayout::new(
            16,
            8,
            vec![CAggregateField::new("data", 0, CType::UInt8Pointer)],
        );
        let function = field_output(layout.clone(), layout.clone());
        let output = function
            .contract_interface()
            .initialization_output_selectors()
            .unwrap()
            .remove(0);
        let descriptor = CMemory::local_pointer("descriptor");
        let target = CPointerValue::new(Pointer::symbolic(Variable(991_010)), CType::UInt8Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(991_010)));
        let mut entry = CState::new().with_memory(
            CMemory::new()
                .with_declared_aggregate_block(descriptor.block.clone(), &layout)
                .store(descriptor.clone(), CValue::Pointer(target.clone())),
        );
        entry
            .locals
            .set_aggregate_object_at("out", layout.clone(), descriptor.clone());
        assert_eq!(
            resolve_initialization_output(&entry, function.contract_interface(), &output),
            Some(target.clone())
        );
        let marked =
            mark_initialization_output_fields(entry.clone(), function.contract_interface())
                .unwrap();
        assert!(marked.memory().may_read_uninitialized_object_under(
            target.pointer(),
            4,
            &PureFactContext::new()
        ));
        let partial = CState::new().with_memory(
            CMemory::new()
                .with_declared_aggregate_block(descriptor.block.clone(), &layout)
                .store(
                    descriptor.clone(),
                    CValue::UInt32(Bitvector32Term::Constant(0)),
                ),
        );
        let mut partial = partial;
        partial
            .locals
            .set_aggregate_object_at("out", layout, descriptor);
        assert!(
            resolve_initialization_output(&partial, function.contract_interface(), &output)
                .is_none()
        );
    }
    #[test]
    fn lowered_output_field_selector_refuses_forged_offsets() {
        let layout = CAggregateLayout::new(
            16,
            8,
            vec![CAggregateField::new("data", 0, CType::UInt8Pointer)],
        );
        for (offset, accepted) in [(0u32, true), (4, false), (8, false)] {
            let mut function = field_output(layout.clone(), layout.clone());
            let pointer = if offset == 0 {
                SpecExpression::CExpression(c_variable("out"))
            } else {
                SpecExpression::PointerOffset {
                    pointer: Box::new(SpecExpression::CExpression(c_variable("out"))),
                    elements: Box::new(SpecExpression::Value(CValue::Int32(
                        Bitvector32Term::Constant(offset),
                    ))),
                    byte_width: 1,
                }
            };
            function.contract_interface.contract_ensures =
                vec![SpecProposition::MemoryInitialized {
                    memory: SpecMemory::Current,
                    base: SpecExpression::LoopEntrySnapshot(Box::new(
                        SpecExpression::AggregateFieldValue {
                            parameter: "out".into(),
                            pointer: Box::new(pointer),
                            value_type: CType::UInt8Pointer,
                        },
                    )),
                    bytes: 4,
                }];
            assert_eq!(
                function
                    .contract_interface()
                    .initialization_output_selectors()
                    .is_some(),
                accepted
            );
        }
    }
    #[test]
    fn lowered_output_member_let_checks_its_exact_binder() {
        let layout = CAggregateLayout::new(
            16,
            8,
            vec![CAggregateField::new("data", 0, CType::UInt8Pointer)],
        );
        for (binder, body_name, accepted) in [
            ("bound", "bound", true),
            ("arbitrary_alpha_name", "arbitrary_alpha_name", true),
            ("bound", "wrong", false),
        ] {
            let mut function = field_output(layout.clone(), layout.clone());
            function.contract_interface.contract_ensures =
                vec![SpecProposition::MemoryInitialized {
                    memory: SpecMemory::Current,
                    base: SpecExpression::LoopEntrySnapshot(Box::new(SpecExpression::MemoryLoad {
                        memory: SpecMemory::Current,
                        value_type: CType::UInt8Pointer,
                        pointer: Box::new(SpecExpression::Let {
                            name: binder.into(),
                            value: Box::new(SpecExpression::CExpression(c_variable("out"))),
                            body: Box::new(SpecExpression::CExpression(
                                CExpression::MemberAddress {
                                    object: Box::new(c_variable(body_name)),
                                    selection: Arc::new(CAggregateMemberSelection {
                                        layout: Arc::new(layout.clone()),
                                        path: vec!["data".into()].into(),
                                        value_type: CType::UInt8Pointer,
                                    }),
                                },
                            )),
                        }),
                    })),
                    bytes: 4,
                }];
            assert_eq!(
                function
                    .contract_interface()
                    .initialization_output_selectors()
                    .is_some(),
                accepted
            );
        }
    }
}
