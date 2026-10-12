//! Matching scalar object requirements at symbolic entry and actual calls.
//! These requirements issue neither memory authority nor initialized bytes.
use super::*;

/// Source-obligation setup only. The same interface is validated at actual
/// calls by `bind`; an input spelling is never treated as a fresh allocation.
pub(crate) fn assume_scalar_object_inputs(
    mut state: CState,
    interface: &CFunctionContractInterface,
    arguments: &mut [CExpression],
) -> Result<CState, String> {
    for input in interface.aggregate_object_inputs() {
        let parameter = interface
            .parameters()
            .get(input.parameter_index)
            .ok_or("aggregate object input parameter is missing")?;
        if !parameter.c_type().is_pointer() {
            return Err("aggregate input must be a pointer".into());
        }
        let Some(CExpression::Value(CValue::Pointer(pointer))) =
            arguments.get_mut(input.parameter_index)
        else {
            return Err("aggregate object input is not an entry pointer value".into());
        };
        *pointer = CMemory::aggregate_input_pointer(
            pointer.pointer().clone(),
            &input.layout,
            pointer.c_type(),
        )
        .with_pointee_volatile(pointer.pointee_volatile())
        .with_pointee_constant(pointer.pointee_constant());
        state.set_memory(
            state
                .memory()
                .clone()
                .with_object_input_domain(pointer.pointer().clone(), &input.layout)?,
        );
    }
    for input in interface.scalar_object_inputs() {
        let parameter = interface
            .parameters()
            .get(input.parameter_index)
            .ok_or("scalar object input parameter is missing")?;
        if parameter.c_type().pointee_type() != Some(input.element_type) {
            return Err("scalar object input type does not match its parameter".into());
        }
        let Some(CExpression::Value(CValue::Pointer(pointer))) =
            arguments.get_mut(input.parameter_index)
        else {
            return Err("scalar object input is not an entry pointer value".into());
        };
        let address = pointer.pointer().clone();
        *pointer = pointer
            .clone()
            .with_designation(PointerDesignation::Object {
                root: address.clone(),
                path: Arc::from([]),
                base: address,
                element_type: input.element_type,
                stride: input.element_type.byte_width(),
                count: IntegerTerm::constant_i64(1).into(),
            });
        state.set_memory(
            state
                .memory()
                .clone()
                .with_scalar_input_domain(pointer.clone(), input.element_type)?,
        );
    }
    Ok(state)
}

/// This common hook is used by body execution, contract summaries and contract
/// certification. A raw address, even one equal to a scalar's address, cannot
/// establish the required complete pointer value.
pub(super) fn bind(
    caller: &CState,
    interface: &CFunctionContractInterface,
    callee: &CState,
    assumptions: &PureFactContext,
) -> Option<()> {
    for input in interface.aggregate_object_inputs() {
        let parameter = interface.parameters().get(input.parameter_index)?;
        if !parameter.c_type().is_pointer() {
            return None;
        }
        let CValue::Pointer(pointer) = callee.locals.get(parameter.name())? else {
            return None;
        };
        if !caller
            .memory()
            .has_aggregate_object_domain(pointer, &input.layout)
        {
            let selection = CAggregateMemberSelection {
                layout: input.layout.clone(),
                path: Arc::from([]),
                value_type: CType::UInt8Array(input.layout.size_bytes()),
            };
            let (_, guards) = caller.memory().guarded_native_record_selection(
                pointer,
                &selection,
                assumptions,
            )?;
            if guards
                .iter()
                .any(|guard| assumptions.decide(guard) != Some(true))
            {
                return None;
            }
        }
    }
    for input in interface.scalar_object_inputs() {
        let parameter = interface.parameters().get(input.parameter_index)?;
        if parameter.c_type().pointee_type() != Some(input.element_type) {
            return None;
        }
        let CValue::Pointer(pointer) = callee.locals.get(parameter.name())? else {
            return None;
        };
        let Ok(crate::kernel::eval::pointer_domains::PointerDomainCheck::Checked(guards)) =
            crate::kernel::eval::pointer_domains::checked_typed_pointer_span(
                caller,
                pointer,
                IntegerTerm::constant_i64(0),
                IntegerTerm::constant_i64(1),
                input.element_type,
                assumptions,
            )
        else {
            return None;
        };
        if guards
            .iter()
            .any(|guard| assumptions.decide(guard) != Some(true))
        {
            return None;
        }
    }
    Some(())
}

#[cfg(test)]
mod tests {
    use super::*;

    fn raw_function() -> CFunction {
        c_function(
            CType::Void,
            "scalar_input",
            vec![c_parameter("pointer", CType::Int32Pointer)],
            c_return(CExpression::Value(CValue::Void)),
        )
    }

    fn required_function() -> CFunction {
        raw_function().with_scalar_object_inputs(vec![CScalarObjectInput {
            parameter_index: 0,
            element_type: CType::Int32,
        }])
    }

    #[test]
    fn scalar_object_requirement_is_semantic_interface_identity() {
        let ordinary = raw_function();
        let required = required_function();
        assert_ne!(ordinary, required);
        assert!(
            !ordinary
                .contract_interface()
                .exactly_matches(required.contract_interface())
        );
        assert!(
            !ordinary
                .contract_interface()
                .has_compatible_signature_and_composite_vocabulary(required.contract_interface())
        );
    }

    #[test]
    fn scalar_object_entry_and_shared_call_binding_require_the_same_carrier() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(940_100));
        let raw = CValue::typed_pointer(address.clone(), CType::Int32Pointer);
        let function = required_function();
        let mut arguments = vec![CExpression::Value(raw.clone())];
        assert!(
            bind_c_function_arguments(&CState::new(), &raw_function(), std::slice::from_ref(&raw))
                .is_some()
        );
        assert!(
            bind_c_function_arguments(&CState::new(), &function, std::slice::from_ref(&raw))
                .is_none()
        );
        let state = assume_scalar_object_inputs(
            CState::new(),
            function.contract_interface(),
            &mut arguments,
        )
        .unwrap();
        assert!(!state.memory().has_block(&address.block));
        assert!(
            state.memory().cells.representation_len() == 0,
            "input validity must not seed values"
        );
        let CExpression::Value(actual) = &arguments[0] else {
            panic!()
        };
        assert!(
            bind_c_function_arguments(&state, &function, std::slice::from_ref(actual)).is_some()
        );
        assert!(
            bind_c_contract_arguments(
                &state,
                function.contract_interface(),
                std::slice::from_ref(actual),
                None
            )
            .is_some()
        );
        assert!(bind_c_function_arguments(&state, &function, std::slice::from_ref(&raw)).is_none());
        assert!(
            bind_c_contract_arguments(&state, function.contract_interface(), &[raw], None)
                .is_none()
        );
        let CValue::Pointer(actual) = actual else {
            panic!()
        };
        let different = actual.clone().with_designation(PointerDesignation::Object {
            root: address.clone(),
            path: vec![PointerDomainSelection::Member("different".into())].into(),
            base: address,
            element_type: CType::Int32,
            stride: 4,
            count: IntegerTerm::constant_i64(1).into(),
        });
        assert!(
            bind_c_function_arguments(&state, &function, &[CValue::Pointer(different)]).is_none()
        );
    }
}

#[cfg(test)]
mod member_tests {
    use super::*;

    fn identity(name: &str) -> Option<Arc<CppRecordDeclarationIdentity>> {
        Some(Arc::new(CppRecordDeclarationIdentity::new(
            "member-input-test",
            name,
        )))
    }

    fn child(width: usize) -> CAggregateLayout {
        CAggregateLayout::new(
            (width as u32) * 4,
            4,
            (0..width)
                .map(|i| CAggregateField::new(format!("field{i}"), (i as u32) * 4, CType::Int32))
                .collect(),
        )
        .with_declaration_identity(identity("Child"))
    }

    fn parent(child: &CAggregateLayout) -> CAggregateLayout {
        CAggregateLayout::new(
            child.size_bytes() + 4,
            4,
            child
                .fields()
                .iter()
                .map(|field| {
                    CAggregateField::new(
                        format!("child.{}", field.name()),
                        field.offset_bytes(),
                        field.c_type(),
                    )
                })
                .chain(std::iter::once(CAggregateField::new(
                    "sibling",
                    child.size_bytes(),
                    CType::Int32,
                )))
                .collect(),
        )
        .with_records(vec![
            CAggregateRecord::new("child", 0, child.size_bytes(), 4, None)
                .with_declaration_identity(identity("Child")),
        ])
        .with_declaration_identity(identity("Parent"))
    }

    fn selected(
        memory: &CMemory,
        object: &CPointerValue,
        layout: &CAggregateLayout,
        path: &[&str],
        value_type: CType,
    ) -> CPointerValue {
        memory
            .checked_member_pointer(
                object,
                &CAggregateMemberSelection {
                    layout: Arc::new(layout.clone()),
                    path: path
                        .iter()
                        .map(|part| (*part).into())
                        .collect::<Vec<_>>()
                        .into(),
                    value_type,
                },
            )
            .expect("authenticated explicit member")
    }

    #[test]
    fn member_address_keeps_enclosing_root_through_entry_and_actual_call_binding() {
        let _session = crate::kernel::VerificationSession::enter();
        let child = child(2);
        let layout = parent(&child);
        let address = CMemory::frame_local_pointer(94, "parent");
        let memory = CMemory::new().with_declared_aggregate_block(address.block.clone(), &layout);
        let object = memory
            .declared_aggregate_pointer(&address, &layout)
            .unwrap()
            .with_pointee_constant(true)
            .with_pointee_volatile(true);
        let member = selected(
            &memory,
            &object,
            &layout,
            &["child", "field0"],
            CType::Int32,
        );
        assert!(member.pointee_constant() && member.pointee_volatile());
        assert_eq!(member.pointer(), &address);
        let Some(PointerDesignation::Object { root, path, .. }) = member.designation() else {
            panic!()
        };
        assert_eq!(root, &address);
        assert_eq!(
            path.as_ref(),
            &[
                PointerDomainSelection::Member("child".into()),
                PointerDomainSelection::Member("field0".into())
            ]
        );
        let mut caller = CState::new();
        caller.set_memory(memory.clone());
        let expression = CExpression::MemberAddress {
            object: Box::new(CExpression::Value(CValue::Pointer(object.clone()))),
            selection: Arc::new(CAggregateMemberSelection {
                layout: Arc::new(layout.clone()),
                path: vec!["child".into(), "field0".into()].into(),
                value_type: CType::Int32,
            }),
        };
        let paths = crate::kernel::eval::evaluate_c_expression_paths(
            &caller,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        assert_eq!(
            paths[0].outcome,
            CExpressionOutcome::Value(CValue::Pointer(member.clone()))
        );
        assert!(paths[0].obligations.is_empty() && paths[0].facts.is_empty());
        let wrong_path = CAggregateMemberSelection {
            layout: Arc::new(layout.clone()),
            path: vec!["nonexistent".into()].into(),
            value_type: CType::Int32,
        };
        assert!(
            memory
                .checked_member_pointer(&object, &wrong_path)
                .is_none()
        );
        let function = c_function(
            CType::Void,
            "scalar_member",
            vec![
                c_parameter("pointer", CType::Int32Pointer)
                    .with_pointee_volatile(true)
                    .with_pointee_constant(true),
            ],
            c_return(CExpression::Value(CValue::Void)),
        )
        .with_scalar_object_inputs(vec![CScalarObjectInput {
            parameter_index: 0,
            element_type: CType::Int32,
        }]);
        let actual = CValue::Pointer(member.clone());
        let callee =
            bind_c_function_arguments(&caller, &function, std::slice::from_ref(&actual)).unwrap();
        assert_eq!(callee.locals.get("pointer"), Some(&actual));
        assert!(
            bind_c_contract_arguments(&caller, function.contract_interface(), &[actual], None)
                .is_some()
        );
        // Equal addresses cannot rebase the member to a standalone scalar root.
        let rebased =
            CMemory::aggregate_input_pointer(address.clone(), &layout, CType::Int32Pointer)
                .with_designation(PointerDesignation::Object {
                    root: address.clone(),
                    path: Arc::from([]),
                    base: address.clone(),
                    element_type: CType::Int32,
                    stride: 4,
                    count: IntegerTerm::constant_i64(1).into(),
                });
        assert!(!memory.has_scalar_object_domain(&rebased, CType::Int32));
        assert!(!memory.has_scalar_object_domain(
            &member.clone().with_pointer(address.offset_by_bytes(4)),
            CType::Int32
        ));
        assert!(
            !memory.has_scalar_object_domain(
                &member
                    .clone()
                    .with_pointer(address.offset_by_bytes(child.size_bytes())),
                CType::Int32
            )
        );
        assert!(
            !memory
                .without_local_block(&address.block)
                .has_scalar_object_domain(&member, CType::Int32)
        );
        let raw = CPointerValue::new(address.clone(), object.c_type());
        assert!(
            memory
                .checked_member_pointer(
                    &raw,
                    &CAggregateMemberSelection {
                        layout: Arc::new(layout.clone()),
                        path: vec!["sibling".into()].into(),
                        value_type: CType::Int32
                    }
                )
                .is_none()
        );
        let record = selected(
            &memory,
            &object,
            &layout,
            &["child"],
            CType::UInt8Array(child.size_bytes()),
        );
        assert!(memory.has_aggregate_object_domain(&record, &child));
        // A successful memo must not authenticate a changed nominal definition.
        assert!(!memory.has_aggregate_object_domain(
            &record,
            &child.clone().with_declaration_identity(identity("Other"))
        ));
        let forged_shape = CAggregateLayout::new(
            child.size_bytes(),
            4,
            vec![
                CAggregateField::new("field0", 0, CType::UInt32),
                CAggregateField::new("field1", 4, CType::Int32),
            ],
        )
        .with_declaration_identity(identity("Child"));
        assert!(!memory.has_aggregate_object_domain(&record, &forged_shape));
        let wrong = memory.clone().with_declared_aggregate_block(
            address.block.clone(),
            &layout
                .clone()
                .with_declaration_identity(identity("OtherParent")),
        );
        assert!(!wrong.has_aggregate_object_domain(&object, &layout));
        assert!(
            wrong
                .checked_member_pointer(
                    &object,
                    &CAggregateMemberSelection {
                        layout: Arc::new(layout.clone()),
                        path: vec!["child".into(), "field0".into()].into(),
                        value_type: CType::Int32
                    }
                )
                .is_none()
        );
        assert!(!memory.has_initialized_bytes_under(&address, 4, &PureFactContext::new()));
    }

    #[test]
    fn aggregate_input_requirement_has_entry_actual_and_contract_parity_without_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = Arc::new(child(2));
        let function = c_function(
            CType::Void,
            "record_input",
            vec![c_parameter("pointer", CType::Int32Pointer)],
            c_return(CExpression::Value(CValue::Void)),
        )
        .with_aggregate_object_inputs(vec![CAggregateObjectInput {
            parameter_index: 0,
            layout: layout.clone(),
        }]);
        let address = Pointer::symbolic(Variable(940_300));
        let raw = CValue::typed_pointer(address.clone(), CType::Int32Pointer);
        assert!(
            bind_c_function_arguments(&CState::new(), &function, std::slice::from_ref(&raw))
                .is_none()
        );
        let mut arguments = vec![CExpression::Value(raw.clone())];
        let state = assume_scalar_object_inputs(
            CState::new(),
            function.contract_interface(),
            &mut arguments,
        )
        .unwrap();
        let CExpression::Value(actual) = &arguments[0] else {
            panic!()
        };
        assert!(
            bind_c_function_arguments(&state, &function, std::slice::from_ref(actual)).is_some()
        );
        assert!(
            bind_c_contract_arguments(
                &state,
                function.contract_interface(),
                std::slice::from_ref(actual),
                None
            )
            .is_some()
        );
        assert!(!state.memory.has_block(&address.block));
        assert_eq!(state.memory.cells.representation_len(), 0);
        assert!(!state.memory.has_initialized_bytes_under(
            &address,
            layout.size_bytes(),
            &PureFactContext::new()
        ));
        assert!(state.resources().is_empty());
        let wrong =
            state
                .memory
                .clone()
                .with_declared_scalar_block(address.block.clone(), 4, CType::Int32);
        let CValue::Pointer(actual) = actual else {
            panic!()
        };
        assert!(!wrong.has_aggregate_object_domain(actual, &layout));
    }

    #[test]
    fn member_address_selection_ignores_unrelated_fields_and_memoizes_large_selected_children() {
        let mut fixed = Vec::new();
        let mut nested = Vec::new();
        for width in [16, 128, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let child = child(width);
            let layout = parent(&child);
            let address = CMemory::frame_local_pointer(95, "parent");
            let memory =
                CMemory::new().with_declared_aggregate_block(address.block.clone(), &layout);
            let object = memory
                .declared_aggregate_pointer(&address, &layout)
                .unwrap();
            let record = selected(
                &memory,
                &object,
                &layout,
                &["child"],
                CType::UInt8Array(child.size_bytes()),
            );
            assert!(memory.has_aggregate_object_domain(&record, &child)); // charge selected-shape admission once
            let fixed_selection = CAggregateMemberSelection {
                layout: Arc::new(layout.clone()),
                path: vec!["sibling".into()].into(),
                value_type: CType::Int32,
            };
            let child_selection = CAggregateMemberSelection {
                layout: Arc::new(child.clone()),
                path: vec!["field0".into()].into(),
                value_type: CType::Int32,
            };
            let fixed_expression = CExpression::MemberAddress {
                object: Box::new(CExpression::Value(CValue::Pointer(object.clone()))),
                selection: Arc::new(fixed_selection),
            };
            let child_expression = CExpression::MemberAddress {
                object: Box::new(CExpression::Value(CValue::Pointer(record.clone()))),
                selection: Arc::new(child_selection),
            };
            let mut state = CState::new();
            state.set_memory(memory.clone());
            let exercise = |expression: &CExpression| {
                let mut hash = std::collections::hash_map::DefaultHasher::new();
                std::hash::Hash::hash(expression, &mut hash);
                assert_eq!(
                    expression.cmp(&expression.clone()),
                    std::cmp::Ordering::Equal
                );
                let paths = crate::kernel::eval::evaluate_c_expression_paths(
                    &state,
                    expression,
                    &PureFactContext::new(),
                    &mut ExecutionBudget::default(),
                )
                .unwrap();
                assert!(matches!(
                    paths.as_slice(),
                    [CExpressionPath {
                        outcome: CExpressionOutcome::Value(CValue::Pointer(_)),
                        ..
                    }]
                ));
            };
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..32 {
                    exercise(&fixed_expression);
                }
            });
            fixed.push(work);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..32 {
                    exercise(&child_expression);
                }
            });
            nested.push(work);
        }
        assert!(
            fixed.iter().all(|work| *work <= fixed[0].max(1) * 2),
            "{fixed:?}"
        );
        assert!(
            nested.iter().all(|work| *work <= nested[0].max(1) * 2),
            "{nested:?}"
        );
    }

    #[test]
    fn relative_child_selection_preserves_the_authenticated_enclosing_record() {
        let _session = crate::kernel::VerificationSession::enter();
        let child = child(2);
        let layout = parent(&child);
        let address = CMemory::frame_local_pointer(949_020, "record");
        let memory = CMemory::new().with_declared_aggregate_block(address.block.clone(), &layout);
        let object = memory
            .declared_aggregate_pointer(&address, &layout)
            .unwrap();
        let record = selected(&memory, &object, &layout, &["child"], CType::UInt8Array(8));
        let direct = selected(
            &memory,
            &object,
            &layout,
            &["child", "field1"],
            CType::Int32,
        );
        let relative = memory
            .checked_member_pointer_by_path(&record, &["field1".into()])
            .unwrap();
        assert_eq!(relative, direct);
        assert!(
            memory.checked_member_array_pointer(&record).is_none(),
            "record storage is not a byte array"
        );
        assert!(
            memory
                .checked_member_pointer_by_path(&record, &["sibling".into()])
                .is_none()
        );
        assert!(
            memory
                .checked_member_pointer_by_path(&relative, &["field0".into()])
                .is_none()
        );
        let raw = CPointerValue::new(record.pointer().clone(), record.c_type());
        assert!(
            memory
                .checked_member_pointer_by_path(&raw, &["field0".into()])
                .is_none()
        );
        let shifted = record.clone().with_pointer(record.offset_by_bytes(4));
        assert!(
            memory
                .checked_member_pointer_by_path(&shifted, &["field0".into()])
                .is_none()
        );
        let expired = memory.without_local_block(&address.block);
        assert!(
            expired
                .checked_member_pointer_by_path(&record, &["field0".into()])
                .is_none()
        );
    }
}

#[cfg(test)]
mod array_reference_tests {
    use super::*;

    fn function() -> CFunction {
        c_function(
            CType::Void,
            "array_element_reference",
            vec![c_parameter("pointer", CType::Int32Pointer)],
            c_return(CExpression::Value(CValue::Void)),
        )
        .with_scalar_object_inputs(vec![CScalarObjectInput {
            parameter_index: 0,
            element_type: CType::Int32,
        }])
    }

    fn array() -> (CState, CPointerValue) {
        let base = CMemory::frame_local_pointer(949_010, "array");
        let memory = CMemory::new()
            .with_declared_array_block(base.block.clone(), CType::Int32, 4)
            .unwrap();
        let pointer = memory
            .declared_array_pointer(&base, CType::Int32, 4)
            .unwrap();
        (CState::new().with_memory(memory), pointer)
    }

    fn bind_both(state: &CState, pointer: &CPointerValue, assumptions: &PureFactContext) -> bool {
        let function = function();
        let arguments = [CValue::Pointer(pointer.clone())];
        let body =
            bind_c_function_arguments_with_assumptions(state, &function, &arguments, assumptions);
        let summary = bind_c_contract_arguments_with_assumptions(
            state,
            function.contract_interface(),
            &arguments,
            None,
            assumptions,
        );
        assert_eq!(body.is_some(), summary.is_some());
        for callee in body.iter().chain(summary.iter()) {
            assert_eq!(callee.locals().get("pointer"), Some(&arguments[0]));
            assert_eq!(callee.memory(), state.memory());
        }
        body.is_some()
    }

    #[test]
    fn scalar_reference_binding_preserves_the_containing_array_domain() {
        let _session = crate::kernel::VerificationSession::enter();
        let (state, pointer) = array();
        for offset in [0, 4, 12] {
            let element = pointer
                .clone()
                .with_pointer(pointer.offset_by_bytes(offset));
            assert!(bind_both(&state, &element, &PureFactContext::new()));
        }
        for offset in [1, 16, 20] {
            let element = pointer
                .clone()
                .with_pointer(pointer.offset_by_bytes(offset));
            assert!(!bind_both(&state, &element, &PureFactContext::new()));
        }
        let raw = CPointerValue::new(pointer.offset_by_bytes(4), CType::Int32Pointer);
        assert!(!bind_both(&state, &raw, &PureFactContext::new()));
        let Some(PointerDesignation::Object {
            root, path, base, ..
        }) = pointer.designation()
        else {
            panic!()
        };
        let forged = pointer
            .clone()
            .with_designation(PointerDesignation::Object {
                root: root.clone(),
                path: path.clone(),
                base: base.clone(),
                element_type: CType::Int32,
                stride: 4,
                count: IntegerTerm::constant_i64(5).into(),
            });
        assert!(!bind_both(&state, &forged, &PureFactContext::new()));
        let expired = state
            .clone()
            .with_memory(state.memory().without_local_block(&pointer.block));
        assert!(!bind_both(&expired, &pointer, &PureFactContext::new()));
        assert_eq!(state.memory().cells.representation_len(), 0);
        assert!(state.resources().facts().is_empty());
    }

    #[test]
    fn symbolic_array_reference_binding_uses_the_actual_caller_guards() {
        let _session = crate::kernel::VerificationSession::enter();
        let (state, pointer) = array();
        let index = Bitvector32Term::Variable(Variable(949_011));
        let element = pointer.clone().with_pointer(Pointer {
            block: pointer.block.clone(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(index),
                byte_width: 4,
            },
        });
        let crate::kernel::eval::pointer_domains::PointerDomainCheck::Checked(guards) =
            crate::kernel::eval::pointer_domains::checked_pointer_access(
                &state,
                &element,
                CType::Int32,
                4,
                crate::kernel::eval::pointer_domains::PointerDomainView::Typed,
                &PureFactContext::new(),
            )
            .unwrap()
        else {
            panic!()
        };
        assert!(!guards.is_empty());
        assert!(!bind_both(&state, &element, &PureFactContext::new()));
        let context = guards
            .iter()
            .fold(PureFactContext::new(), |context, guard| {
                context.assume_condition(guard.clone(), true)
            });
        assert!(bind_both(&state, &element, &context));
        let missing = guards
            .iter()
            .skip(1)
            .fold(PureFactContext::new(), |context, guard| {
                context.assume_condition(guard.clone(), true)
            });
        assert!(!bind_both(&state, &element, &missing));
        let arguments = [CExpression::Value(CValue::Pointer(element.clone()))];
        assert!(c_function_entry_state(&state, &function(), &arguments).is_none());
        let entry =
            c_function_entry_state_with_assumptions(&state, &function(), &arguments, &context)
                .unwrap();
        assert_eq!(
            entry.locals().get("pointer"),
            Some(&CValue::Pointer(element))
        );
    }
}

#[cfg(test)]
mod member_array_tests {
    use super::*;

    fn fixture(unrelated: u32) -> (CMemory, CPointerValue, CAggregateLayout) {
        let layout =
            CAggregateLayout::new(
                16 + unrelated * 4,
                4,
                vec![CAggregateField::new("items", 0, CType::Int32Array(4))]
                    .into_iter()
                    .chain((0..unrelated).map(|i| {
                        CAggregateField::new(format!("other{i}"), 16 + i * 4, CType::Int32)
                    }))
                    .collect(),
            );
        let address = CMemory::frame_local_pointer(949_030, "member_array");
        let memory = CMemory::new().with_declared_aggregate_block(address.block.clone(), &layout);
        let object = memory
            .declared_aggregate_pointer(&address, &layout)
            .unwrap();
        let member = memory
            .checked_member_pointer(
                &object,
                &CAggregateMemberSelection {
                    layout: Arc::new(layout.clone()),
                    path: vec!["items".into()].into(),
                    value_type: CType::Int32Array(4),
                },
            )
            .unwrap();
        (memory, member, layout)
    }

    #[test]
    fn member_array_decay_authenticates_the_actual_array_without_losing_its_parent() {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, member, _) = fixture(2);
        let array = memory.checked_member_array_pointer(&member).unwrap();
        let Some(PointerDesignation::Object {
            root,
            path,
            base,
            element_type,
            stride,
            count,
        }) = array.designation()
        else {
            panic!()
        };
        assert_eq!(root, &CMemory::frame_local_pointer(949_030, "member_array"));
        assert_eq!(
            path.as_ref(),
            &[PointerDomainSelection::Member("items".into())]
        );
        assert_eq!(base, member.pointer());
        assert_eq!(*element_type, CType::Int32);
        assert_eq!(*stride, 4);
        assert_eq!(
            *count,
            SharedIntegerTerm::from(IntegerTerm::constant_i64(4))
        );
        let element = array.clone().with_pointer(array.offset_by_bytes(12));
        assert!(memory.authenticated_pointer_domain_at_base(&element));
        let state = CState::new().with_memory(memory.clone());
        let function = c_function(
            CType::Void,
            "member_array_ref",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(CExpression::Value(CValue::Void)),
        )
        .with_scalar_object_inputs(vec![CScalarObjectInput {
            parameter_index: 0,
            element_type: CType::Int32,
        }]);
        assert!(
            bind_c_function_arguments_with_assumptions(
                &state,
                &function,
                &[CValue::Pointer(element.clone())],
                &PureFactContext::new()
            )
            .is_some()
        );
        let one_past = array.clone().with_pointer(array.offset_by_bytes(16));
        assert!(
            bind_c_function_arguments_with_assumptions(
                &state,
                &function,
                &[CValue::Pointer(one_past)],
                &PureFactContext::new()
            )
            .is_none()
        );
        let forged = array.clone().with_designation(PointerDesignation::Object {
            root: root.clone(),
            path: path.clone(),
            base: base.clone(),
            element_type: *element_type,
            stride: *stride,
            count: IntegerTerm::constant_i64(5).into(),
        });
        assert!(!memory.authenticated_pointer_domain_at_base(&forged));
        assert!(
            memory
                .checked_member_array_pointer(&CPointerValue::new(
                    member.pointer().clone(),
                    member.c_type()
                ))
                .is_none()
        );
        assert_eq!(memory.cells.representation_len(), 0);
        assert!(!memory.has_initialized_bytes_under(member.pointer(), 16, &PureFactContext::new()));
        assert!(
            !memory
                .without_local_block(&root.block)
                .authenticated_pointer_domain_at_base(&array)
        );
    }

    #[test]
    fn selected_member_array_queries_ignore_unrelated_record_fields() {
        let mut samples = Vec::new();
        for unrelated in [16, 128, 1024] {
            let _session = crate::kernel::VerificationSession::enter();
            let (memory, member, _) = fixture(unrelated);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..32 {
                    let array = memory.checked_member_array_pointer(&member).unwrap();
                    assert!(memory.authenticated_pointer_domain_at_base(&array));
                }
            });
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "selected member work grew: {samples:?}"
        );
    }
}

#[cfg(test)]
mod opaque_record_binding_tests {
    use super::*;

    #[test]
    fn opaque_record_binding_requires_the_exact_carrier_and_layout() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = Arc::new(CAggregateLayout::new(
            8,
            8,
            vec![CAggregateField::new("next", 0, CType::Int32Pointer)],
        ));
        let identity = Variable(988_330);
        let pointer = CPointerValue::new(Pointer::symbolic(identity), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(identity));
        let memory = CMemory::new()
            .with_native_record_input(pointer.clone(), layout.clone())
            .unwrap();
        let caller = CState::new().with_memory(memory);
        let function = c_function(
            CType::Void,
            "record_helper",
            vec![c_parameter("record", CType::Int32Pointer)],
            c_return(CExpression::Value(CValue::Void)),
        )
        .with_aggregate_object_inputs(vec![CAggregateObjectInput {
            parameter_index: 0,
            layout: layout.clone(),
        }]);
        let assumptions = PureFactContext::new();
        let callee = CState::new().with_local("record", CValue::Pointer(pointer.clone()));
        assert!(
            bind(
                &caller,
                function.contract_interface(),
                &callee,
                &assumptions
            )
            .is_some()
        );
        for wrong in [
            CPointerValue::new(pointer.pointer().clone(), pointer.c_type()),
            pointer
                .clone()
                .with_designation(PointerDesignation::Unresolved(Variable(988_331))),
        ] {
            let callee = CState::new().with_local("record", CValue::Pointer(wrong));
            assert!(
                bind(
                    &caller,
                    function.contract_interface(),
                    &callee,
                    &assumptions
                )
                .is_none()
            );
        }
        let wrong_layout = Arc::new(CAggregateLayout::new(
            8,
            8,
            vec![CAggregateField::new("other", 0, CType::Int64)],
        ));
        let wrong_function = function.with_aggregate_object_inputs(vec![CAggregateObjectInput {
            parameter_index: 0,
            layout: wrong_layout,
        }]);
        assert!(
            bind(
                &caller,
                wrong_function.contract_interface(),
                &callee,
                &assumptions
            )
            .is_none()
        );
    }
}
