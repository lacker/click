use super::*;

pub(crate) fn root(
    state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    selector: &CPointerEffectRoot,
) -> Option<CPointerValue> {
    match selector {
        CPointerEffectRoot::Parameter(index) => {
            let CValue::Pointer(pointer) = arguments.get(*index)? else {
                return None;
            };
            // Keep scalar carriers unchanged; record witnesses authenticate
            // unresolved/loaded carriers without changing their numeric value.
            Some(
                state
                    .memory()
                    .checked_native_record_pointer(pointer)
                    .unwrap_or_else(|| pointer.clone()),
            )
        }
        CPointerEffectRoot::ConstructionDestination => {
            if interface.aggregate_return_mode() != CAggregateReturnMode::Construction {
                return None;
            }
            let destination = state.aggregate_destination.as_deref()?;
            state
                .memory()
                .declared_aggregate_pointer(&destination.pointer, &destination.layout)
        }
    }
}

pub(crate) fn selected(
    state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    selector: &CPointerEffectRoot,
    path: &[String],
) -> Option<CPointerValue> {
    let pointer = if path.is_empty() {
        match selector {
            CPointerEffectRoot::Parameter(index) => {
                let CValue::Pointer(pointer) = arguments.get(*index)? else {
                    return None;
                };
                pointer.clone()
            }
            _ => root(state, interface, arguments, selector)?,
        }
    } else {
        root(state, interface, arguments, selector)?
    };
    if path.is_empty() {
        Some(pointer)
    } else {
        state
            .memory()
            .checked_member_pointer_by_path(&pointer, path)
    }
}

pub(crate) fn selected_element_type(
    state: &CState,
    pointer: &CPointerValue,
    assumptions: &PureFactContext,
) -> Option<CType> {
    match pointer.designation()? {
        PointerDesignation::Object { element_type, .. } => Some(*element_type),
        PointerDesignation::InputSelected { element_type, .. } => {
            let guards = state
                .memory()
                .authenticated_input_selection(pointer, assumptions)?;
            guards
                .iter()
                .all(|guard| {
                    required_obligation_is_exactly_discharged(
                        assumptions,
                        &Proposition::ConditionIs(guard.clone(), true),
                    )
                })
                .then_some(*element_type)
        }
        _ => None,
    }
}

pub(crate) fn record_layout(
    state: &CState,
    pointer: &CPointerValue,
) -> Option<Arc<CAggregateLayout>> {
    match pointer.designation() {
        Some(PointerDesignation::Object { root, .. }) => match state
            .memory()
            .blocks
            .get(&root.block)
            .and_then(|block| block.declared_object.as_ref())
        {
            Some(CDeclaredObject::Aggregate(layout)) => Some(layout.clone()),
            Some(_) => None,
            None => state.memory().heap.object_input_domains.get(root).cloned(),
        },
        Some(PointerDesignation::InputSelected { .. }) => {
            state.memory().input_record_layout(pointer)
        }
        _ => None,
    }
}

/// Observe one exact initialized full pointer field under the input snapshot's
/// existing read authority. A cast is executed by the ordinary checked rules,
/// never represented by copying a designation onto an unrelated raw address.
pub(crate) fn field_source(
    state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    source: &CPointerFieldSource,
    output_type: CType,
    assumptions: &PureFactContext,
) -> Option<CPointerValue> {
    field_source_in(
        state,
        interface,
        arguments,
        source,
        output_type,
        assumptions,
        true,
    )
}

fn field_source_in(
    state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    source: &CPointerFieldSource,
    output_type: CType,
    assumptions: &PureFactContext,
    check_qualifiers: bool,
) -> Option<CPointerValue> {
    if !source.value_type.is_pointer()
        || source.value_type.byte_width() != 8
        || !output_type.is_pointer()
    {
        return None;
    }
    let member = declared_field_address(state, interface, arguments, source, assumptions)?;
    if !state
        .memory()
        .has_initialized_bytes_under(member.pointer(), 8, assumptions)
    {
        return None;
    }
    let load = c_typed_load(
        CExpression::Value(CValue::Pointer(member)),
        source.value_type,
    );
    let loaded = observe_field_pointer(state, &load, assumptions)?;
    if check_qualifiers
        && (loaded.pointee_constant() != source.pointee_constant
            || loaded.pointee_volatile() != source.pointee_volatile)
    {
        return None;
    }
    if output_type == source.value_type {
        return Some(loaded);
    }
    if output_type != CType::UInt8Pointer
        || source.value_type != CType::UInt32Pointer
        || state.typed_access_policy() != CTypedAccessPolicy::NativeObjectOnly
    {
        return None;
    }
    observe_field_pointer(
        state,
        &c_cast(CExpression::Value(CValue::Pointer(loaded)), output_type),
        assumptions,
    )
}

/// Select declared storage through the source language's existing member
/// operation. C allocated-access rules do not establish a native record domain.
fn declared_field_address(
    state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    source: &CPointerFieldSource,
    assumptions: &PureFactContext,
) -> Option<CPointerValue> {
    let owner = root(
        state,
        interface,
        arguments,
        &CPointerEffectRoot::Parameter(source.parameter),
    )?;
    let selection = CAggregateMemberSelection {
        layout: source.layout.clone(),
        path: source.path.clone(),
        value_type: source.value_type,
    };
    if let Some((member, guards)) =
        state
            .memory()
            .guarded_native_record_selection(&owner, &selection, assumptions)
    {
        if selected_element_type(state, &member, assumptions)? != source.value_type
            || !guards.iter().all(|guard| {
                required_obligation_is_exactly_discharged(
                    assumptions,
                    &Proposition::ConditionIs(guard.clone(), true),
                )
            })
        {
            return None;
        }
        return Some(member);
    }
    if state.typed_access_policy() != CTypedAccessPolicy::CAllocatedAccessAllowed
        || interface.typed_access_policy() != CTypedAccessPolicy::CAllocatedAccessAllowed
        || owner.designation().is_some()
    {
        return None;
    }
    // The checked expression validates the declaration/path/type. It returns
    // an ordinary C address; no input witness or child designation is admitted.
    observe_field_pointer(
        state,
        &CExpression::MemberAddress {
            object: Box::new(CExpression::Value(CValue::Pointer(owner))),
            selection: selection.into(),
        },
        assumptions,
    )
}

fn observe_field_pointer(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
) -> Option<CPointerValue> {
    let context = assumptions.clone().require_owned_expression_loads();
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = evaluate_c_expression_paths(state, expression, &context, &mut budget).ok()?;
    let [path] = paths.as_slice() else {
        return None;
    };
    let CExpressionOutcome::Value(CValue::Pointer(pointer)) = &path.outcome else {
        return None;
    };
    let context = assumptions_with_path_context(&context, &path.facts, &[]);
    path.obligations
        .iter()
        .all(|goal| required_obligation_is_exactly_discharged(&context, goal.proposition()))
        .then(|| pointer.clone())
}

pub(crate) fn field_sources(
    state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    assumptions: &PureFactContext,
) -> Vec<CPointerFieldSource> {
    let mut sources = Vec::new();
    for parameter in 0..interface.parameters().len() {
        let Some(owner) = root(
            state,
            interface,
            arguments,
            &CPointerEffectRoot::Parameter(parameter),
        ) else {
            continue;
        };
        let Some(layout) = record_layout(state, &owner) else {
            continue;
        };
        for (path, value_type) in pointer_fields(state, &owner) {
            let mut selector = CPointerFieldSource {
                parameter,
                layout: layout.clone(),
                path: path.into(),
                value_type,
                pointee_constant: false,
                pointee_volatile: false,
            };
            let Some(observed) = field_source_in(
                state,
                interface,
                arguments,
                &selector,
                value_type,
                assumptions,
                false,
            ) else {
                continue;
            };
            selector.pointee_constant = observed.pointee_constant();
            selector.pointee_volatile = observed.pointee_volatile();
            sources.push(selector);
        }
    }
    sources
}

pub(crate) fn pointer_fields(state: &CState, pointer: &CPointerValue) -> Vec<(Vec<String>, CType)> {
    let layout = match pointer.designation() {
        Some(PointerDesignation::Object { root, .. }) => match state
            .memory()
            .blocks
            .get(&root.block)
            .and_then(|block| block.declared_object.as_ref())
        {
            Some(CDeclaredObject::Aggregate(layout)) => Some(layout.clone()),
            Some(_) => None,
            None => state.memory().heap.object_input_domains.get(root).cloned(),
        },
        Some(PointerDesignation::InputSelected { .. }) => {
            state.memory().input_record_layout(pointer)
        }
        _ => None,
    };
    let Some(layout) = layout else {
        return Vec::new();
    };
    layout
        .fields()
        .iter()
        .filter_map(|field| {
            crate::instrumentation::record_deterministic_work(1);
            if !field.c_type.is_pointer() {
                return None;
            }
            let path = field
                .name()
                .split('.')
                .map(str::to_owned)
                .collect::<Vec<_>>();
            let selected = state
                .memory()
                .checked_member_pointer_by_path(pointer, &path)?;
            let element_type = match selected.designation()? {
                PointerDesignation::Object { element_type, .. }
                | PointerDesignation::InputSelected { element_type, .. } => *element_type,
                _ => return None,
            };
            (element_type == field.c_type).then_some((path, field.c_type))
        })
        .collect()
}

pub(super) fn writes_authorized(
    state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    effects: &[CPointerStoreEffect],
    assumptions: &PureFactContext,
) -> bool {
    effects.iter().all(|effect| {
        let Some(destination) = selected(
            state,
            interface,
            arguments,
            &effect.destination,
            &effect.destination_path,
        ) else {
            return false;
        };
        let bytes = effect.value_type.byte_width();
        state
            .resources()
            .memory_write_range(destination.pointer(), bytes, assumptions)
            .is_some()
            && crate::kernel::eval::memory_write_permission_outcome(
                state,
                destination.pointer(),
                bytes,
                assumptions,
            )
            .is_none()
    })
}

pub(super) fn apply(
    state: &CState,
    source_state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    effects: &[CPointerStoreEffect],
    assumptions: &PureFactContext,
) -> Result<CMemory, String> {
    let mut memory = state.memory().clone();
    for effect in effects {
        let destination = selected(
            state,
            interface,
            arguments,
            &effect.destination,
            &effect.destination_path,
        )
        .ok_or("certified pointer cell destination is not a declared member")?;
        let Some(element_type) = selected_element_type(state, &destination, assumptions) else {
            return Err("certified pointer cell lacks its retained member type".into());
        };
        if element_type != effect.value_type
            || !effect.value_type.is_pointer()
            || !memory.has_initialized_bytes_under(
                destination.pointer(),
                effect.value_type.byte_width(),
                assumptions,
            )
        {
            return Err(
                "certified pointer cell is not initialized at its full declared width".into(),
            );
        }
        let source = if let Some(field) = &effect.source_field {
            field_source(
                source_state,
                interface,
                arguments,
                field,
                effect.value_type,
                assumptions,
            )
        } else {
            selected(
                source_state,
                interface,
                arguments,
                &effect.source,
                &effect.source_path,
            )
            .filter(|source| source.designation().is_some())
            .map(|source| source.with_type(effect.value_type))
        }
        .ok_or("certified stored pointer source lacks its checked input carrier")?;
        // This is an authenticated final-cell equation from complete body
        // certification. Existing initialization and ownership are prerequisites;
        // the equation transports the full source carrier, not a fresh address.
        memory = memory
            .with_certified_pointer_cell(destination.pointer().clone(), source, assumptions)
            .ok_or("certified pointer cell lost its initialized storage prerequisite")?;
    }
    Ok(memory)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn c_field_observation_preserves_value_without_admitting_native_record() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = Arc::new(CAggregateLayout::new(
            16,
            8,
            vec![
                CAggregateField::new("length", 0, CType::Int32),
                CAggregateField::new("data", 8, CType::Int32Pointer),
            ],
        ));
        let address = CMemory::local_pointer("c_field_owner");
        let backing = CMemory::local_pointer("c_field_backing");
        let memory = CMemory::new()
            .with_block(address.block.clone(), 16)
            .with_declared_scalar_block(backing.block.clone(), 4, CType::Int32);
        let value = memory
            .declared_scalar_pointer(&backing, CType::Int32)
            .unwrap();
        let owner = CPointerValue::new(address.clone(), CType::Int32Pointer);
        let field = address.offset_by_bytes(8);
        let memory = memory.store(field.clone(), CValue::Pointer(value.clone()));
        let state = CState::new().with_memory(memory).with_resource_context(
            ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(field.clone(), 0.into(), 1.into(), 8),
            )),
        );
        let interface = c_function(
            CType::Int32Pointer,
            "field",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_skip(),
        )
        .contract_interface()
        .clone();
        let args = [CValue::Pointer(owner.clone())];
        let selector = CPointerFieldSource {
            parameter: 0,
            layout,
            path: vec!["data".into()].into(),
            value_type: CType::Int32Pointer,
            pointee_constant: false,
            pointee_volatile: false,
        };
        let facts = PureFactContext::new();
        let observe = |state: &CState, source: &CPointerFieldSource| {
            field_source(
                state,
                &interface,
                &args,
                source,
                CType::Int32Pointer,
                &facts,
            )
        };
        assert_eq!(observe(&state, &selector), Some(value));
        assert!(
            state
                .memory()
                .checked_native_record_pointer(&owner)
                .is_none()
        );
        assert!(owner.designation().is_none());
        assert!(
            observe(
                &state
                    .clone()
                    .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly),
                &selector
            )
            .is_none()
        );
        let mut native_interface = interface.clone();
        native_interface.typed_access_policy = CTypedAccessPolicy::NativeObjectOnly;
        assert!(
            field_source(
                &state,
                &native_interface,
                &args,
                &selector,
                CType::Int32Pointer,
                &facts
            )
            .is_none()
        );
        assert!(
            observe(
                &state.clone().with_resource_context(ResourceContext::new()),
                &selector
            )
            .is_none()
        );
        let partial = state.clone().with_memory(
            CMemory::new()
                .with_block(address.block.clone(), 16)
                .store(field, int32(0)),
        );
        assert!(observe(&partial, &selector).is_none());
        let mut wrong = selector.clone();
        wrong.path = vec!["length".into()].into();
        assert!(observe(&state, &wrong).is_none());
        wrong = selector.clone();
        wrong.pointee_constant = true;
        assert!(observe(&state, &wrong).is_none());
    }

    #[test]
    fn pointer_field_source_requires_exact_full_initialized_typed_cell() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = Arc::new(CAggregateLayout::new(
            8,
            8,
            vec![CAggregateField::new("pointer", 0, CType::Int32Pointer)],
        ));
        let address = CMemory::local_pointer("field_source_record");
        let backing = CMemory::local_pointer("field_source_backing");
        let memory = CMemory::new()
            .with_declared_aggregate_block(address.block.clone(), &layout)
            .with_declared_scalar_block(backing.block.clone(), 4, CType::Int32);
        let owner = memory
            .declared_aggregate_pointer(&address, &layout)
            .unwrap();
        let source_pointer = memory
            .declared_scalar_pointer(&backing, CType::Int32)
            .unwrap();
        let memory = memory.store(address.clone(), CValue::Pointer(source_pointer.clone()));
        let fact = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            address.clone(),
            0u32.into(),
            1u32.into(),
            8,
        ));
        let state = CState::new()
            .with_memory(memory)
            .with_resource_context(ResourceContext::new().unchecked_with_fact(fact));
        let interface = c_function(
            CType::Int32Pointer,
            "field",
            vec![c_parameter("p", owner.c_type())],
            c_skip(),
        )
        .contract_interface()
        .clone();
        let args = [CValue::Pointer(owner)];
        let selector = CPointerFieldSource {
            parameter: 0,
            layout: layout.clone(),
            path: vec!["pointer".into()].into(),
            value_type: CType::Int32Pointer,
            pointee_constant: false,
            pointee_volatile: false,
        };
        let context = PureFactContext::new();
        assert_eq!(
            field_source(
                &state,
                &interface,
                &args,
                &selector,
                CType::Int32Pointer,
                &context
            ),
            Some(source_pointer.clone())
        );
        let missing = state.clone().with_resource_context(ResourceContext::new());
        assert!(
            field_source(
                &missing,
                &interface,
                &args,
                &selector,
                CType::Int32Pointer,
                &context
            )
            .is_none()
        );
        // An unwritten marker is an initial footprint, not revocation of a
        // later checked store. Start without the positive case's write history.
        let uninitialized = state.clone().with_memory(
            CMemory::new()
                .with_declared_aggregate_block(address.block.clone(), &layout)
                .with_declared_scalar_block(backing.block.clone(), 4, CType::Int32)
                .with_uninitialized_object(address.clone(), 8),
        );
        assert!(
            field_source(
                &uninitialized,
                &interface,
                &args,
                &selector,
                CType::Int32Pointer,
                &context
            )
            .is_none()
        );
        let mut wrong_qualifier = selector.clone();
        wrong_qualifier.pointee_constant = true;
        assert!(
            field_source(
                &state,
                &interface,
                &args,
                &wrong_qualifier,
                CType::Int32Pointer,
                &context
            )
            .is_none()
        );
        wrong_qualifier.pointee_constant = false;
        wrong_qualifier.pointee_volatile = true;
        assert!(
            field_source(
                &state,
                &interface,
                &args,
                &wrong_qualifier,
                CType::Int32Pointer,
                &context
            )
            .is_none()
        );
        let mut wrong_layout = selector.clone();
        wrong_layout.layout = Arc::new(CAggregateLayout::new(
            8,
            8,
            vec![CAggregateField::new("different", 0, CType::Int32Pointer)],
        ));
        assert!(
            field_source(
                &state,
                &interface,
                &args,
                &wrong_layout,
                CType::Int32Pointer,
                &context
            )
            .is_none()
        );
        let partial = state.clone().with_memory(
            CMemory::new()
                .with_declared_aggregate_block(address.block.clone(), &layout)
                .store(address.clone(), int32(0)),
        );
        assert!(
            field_source(
                &partial,
                &interface,
                &args,
                &selector,
                CType::Int32Pointer,
                &context
            )
            .is_none()
        );
        let raw = CPointerValue::new(source_pointer.pointer().clone(), source_pointer.c_type());
        let changed = state
            .clone()
            .with_memory(state.memory().clone().store(address, CValue::Pointer(raw)));
        let observed = field_source(
            &changed,
            &interface,
            &args,
            &selector,
            CType::Int32Pointer,
            &context,
        )
        .unwrap();
        assert_ne!(
            observed, source_pointer,
            "equal numeric addresses do not recover the old origin"
        );
    }

    #[test]
    fn stored_carrier_equation_requires_initialization_and_preserves_exact_source() {
        let layout = CAggregateLayout::new(
            C_POINTER_BYTE_WIDTH,
            C_POINTER_BYTE_WIDTH,
            vec![CAggregateField::new("kid", 0, CType::Int32Pointer)],
        );
        let address = CMemory::local_pointer("effect_cell");
        let memory = CMemory::new().with_declared_aggregate_block(address.block.clone(), &layout);
        let destination = memory
            .declared_aggregate_pointer(&address, &layout)
            .unwrap();
        let source_address = CMemory::local_pointer("effect_source");
        let memory =
            memory.with_declared_scalar_block(source_address.block.clone(), 4, CType::Int32);
        let source = memory
            .declared_scalar_pointer(&source_address, CType::Int32)
            .unwrap();
        let interface = c_function(
            CType::Void,
            "put",
            vec![
                c_parameter("p", destination.c_type()),
                c_parameter("q", source.c_type()),
            ],
            c_return(c_void_value()),
        )
        .contract_interface()
        .clone();
        let effect = CPointerStoreEffect {
            destination: CPointerEffectRoot::Parameter(0),
            destination_path: vec!["kid".into()].into(),
            value_type: CType::Int32Pointer,
            source: CPointerEffectRoot::Parameter(1),
            source_path: Default::default(),
            source_field: None,
        };
        let args = [
            CValue::Pointer(destination),
            CValue::Pointer(source.clone()),
        ];
        let state = CState::new().with_memory(memory);
        assert!(
            apply(
                &state,
                &state,
                &interface,
                &args,
                std::slice::from_ref(&effect),
                &PureFactContext::new()
            )
            .is_err()
        );
        assert!(!writes_authorized(
            &state,
            &interface,
            &args,
            std::slice::from_ref(&effect),
            &PureFactContext::new()
        ));
        let range = CMemoryRange::new_with_element_width(
            address.clone(),
            0u32.into(),
            1u32.into(),
            C_POINTER_BYTE_WIDTH,
        );
        let readonly = state.clone().with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(CResourceFact::View(CResource::Memory(range.clone()))),
        );
        assert!(!writes_authorized(
            &readonly,
            &interface,
            &args,
            std::slice::from_ref(&effect),
            &PureFactContext::new()
        ));
        let owned = state.clone().with_resource_context(
            ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(range)),
        );
        assert!(writes_authorized(
            &owned,
            &interface,
            &args,
            std::slice::from_ref(&effect),
            &PureFactContext::new()
        ));
        let initialized = state.memory().clone().store(
            address.clone(),
            CValue::typed_pointer(Pointer::symbolic(Variable(9_898_203)), CType::Int32Pointer),
        );
        let marks = initialized.heap.initialized.clone();
        let state = state.with_memory(initialized);
        let after = apply(
            &state,
            &state,
            &interface,
            &args,
            &[effect],
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(after.known_value(&address), Some(CValue::Pointer(source)));
        assert_eq!(after.heap.initialized, marks);
    }
}
