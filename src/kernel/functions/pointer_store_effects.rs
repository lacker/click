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
pub(crate) fn declared_field_address(
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

#[cfg(test)]
thread_local! {
    static C_FIELD_DECLARATION_VISITS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}
#[cfg(test)]
pub(crate) fn take_c_field_declaration_visits() -> usize {
    C_FIELD_DECLARATION_VISITS.with(|visits| visits.replace(0))
}

/// Source selectors are candidates only. Complete independent body checking
/// decides which final-cell equations become reusable effects.
pub(in crate::kernel) fn c_declared_fields(function: &CFunction) -> Vec<CPointerFieldSource> {
    if function.contract_interface().typed_access_policy()
        != CTypedAccessPolicy::CAllocatedAccessAllowed
    {
        return Vec::new();
    }
    c_declared_fields_in_body(
        function.parameters().iter().map(|parameter| {
            (
                parameter.name(),
                parameter.c_type().is_pointer() && parameter.aggregate_layout().is_none(),
            )
        }),
        function.body(),
    )
}

pub(crate) fn c_body_has_pointer_field_candidates(function: &CFunction) -> bool {
    !c_declared_fields(function).is_empty()
}

pub(crate) fn c_body_has_pointer_field_candidates_for_formals<'a>(
    formals: impl IntoIterator<Item = (&'a str, bool)>,
    body: &CStatement,
) -> bool {
    !c_declared_fields_in_body(formals, body).is_empty()
}

/// Prefer opaque values only for direct C copy operands that have no other
/// body use. This predicts a checkable entry recipe; it proves no effect and
/// supplies no native access permission.
pub(crate) fn c_body_opaque_pointer_copy_inputs(function: &CFunction) -> BTreeSet<usize> {
    if function.contract_interface().typed_access_policy()
        != CTypedAccessPolicy::CAllocatedAccessAllowed
    {
        return BTreeSet::new();
    }
    let metadata = c_field_body_metadata(
        function.parameters().iter().map(|parameter| {
            (
                parameter.name(),
                parameter.c_type().is_pointer() && parameter.aggregate_layout().is_none(),
            )
        }),
        function.body(),
    );
    metadata.1
}

fn c_declared_fields_in_body<'a>(
    formals: impl IntoIterator<Item = (&'a str, bool)>,
    body: &CStatement,
) -> Vec<CPointerFieldSource> {
    c_field_body_metadata(formals, body).0
}

/// Declaration-only metadata over the selected body. It predicts dependencies;
/// only complete independent body certification can establish an effect.
fn c_field_body_metadata<'a>(
    formals: impl IntoIterator<Item = (&'a str, bool)>,
    body: &CStatement,
) -> (Vec<CPointerFieldSource>, BTreeSet<usize>) {
    enum Node<'a> {
        Statement(&'a CStatement),
        Expression(&'a CExpression),
    }
    let parameters = formals
        .into_iter()
        .enumerate()
        .filter_map(|(index, (name, eligible_pointer))| eligible_pointer.then_some((name, index)))
        .collect::<BTreeMap<_, _>>();
    let mut pending = vec![Node::Statement(body)];
    let mut fields = BTreeSet::new();
    let mut copied = BTreeSet::new();
    let mut other_uses = BTreeSet::new();
    while let Some(node) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        #[cfg(test)]
        C_FIELD_DECLARATION_VISITS.with(|visits| visits.set(visits.get() + 1));
        match node {
            Node::Statement(statement) => match statement {
                CStatement::Scope { body } => pending.push(Node::Statement(body)),
                CStatement::While {
                    condition, body, ..
                } => {
                    pending.push(Node::Expression(condition));
                    pending.push(Node::Statement(body));
                }
                CStatement::Seq(left, right) => {
                    pending.push(Node::Statement(right));
                    pending.push(Node::Statement(left));
                }
                CStatement::If {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(Node::Expression(condition));
                    pending.push(Node::Statement(then_branch));
                    pending.push(Node::Statement(else_branch));
                }
                CStatement::Store { pointer, value }
                | CStatement::TypedStore { pointer, value, .. } => {
                    pending.push(Node::Expression(pointer));
                    if let CExpression::MemberAddress { object, selection } = pointer
                        && matches!(object.as_ref(), CExpression::Variable(name)
                            if parameters.contains_key(name.as_str()))
                        && selection.value_type.is_pointer()
                        && let CExpression::Variable(name) = value
                        && let Some(parameter) = parameters.get(name.as_str())
                    {
                        copied.insert(*parameter);
                    } else {
                        pending.push(Node::Expression(value));
                    }
                }
                CStatement::Assign { expression, .. }
                | CStatement::Return(expression)
                | CStatement::Throw(expression) => pending.push(Node::Expression(expression)),
                CStatement::Declare {
                    initializer: Some(expression),
                    ..
                } => pending.push(Node::Expression(expression)),
                CStatement::Call { arguments, .. } | CStatement::CallAssign { arguments, .. } => {
                    pending.extend(arguments.iter().map(Node::Expression))
                }
                CStatement::ForStep { step, .. } => pending.push(Node::Statement(step)),
                CStatement::TryCatchInt32 {
                    try_body, handler, ..
                } => {
                    pending.push(Node::Statement(try_body));
                    pending.push(Node::Statement(handler));
                }
                CStatement::Switch { expression, cases } => {
                    pending.push(Node::Expression(expression));
                    pending.extend(cases.iter().map(|case| Node::Statement(&case.body)));
                }
                CStatement::HeapAllocate { bytes, .. } => pending.push(Node::Expression(bytes)),
                CStatement::HeapFree { pointer } => pending.push(Node::Expression(pointer)),
                CStatement::Assert { condition, .. } => pending.push(Node::Expression(condition)),
                CStatement::CopyAggregate { target, source, .. }
                | CStatement::InitializeScalarArray { target, source, .. } => {
                    pending.push(Node::Expression(target));
                    pending.push(Node::Expression(source));
                }
                CStatement::Update {
                    target, operand, ..
                } => {
                    pending.push(Node::Expression(target));
                    pending.push(Node::Expression(operand));
                }
                _ => {}
            },
            Node::Expression(expression) => match expression {
                CExpression::MemberAddress { object, selection } => {
                    if let CExpression::Variable(name) = object.as_ref()
                        && let Some(parameter) = parameters.get(name.as_str())
                        && selection.value_type.is_pointer()
                        && selection.value_type.byte_width() == C_POINTER_BYTE_WIDTH
                    {
                        fields.insert(CPointerFieldSource {
                            parameter: *parameter,
                            layout: selection.layout.clone(),
                            path: selection.path.clone().into(),
                            value_type: selection.value_type,
                            pointee_constant: false,
                            pointee_volatile: false,
                        });
                    }
                    pending.push(Node::Expression(object));
                }
                CExpression::Cast { expression, .. }
                | CExpression::FloatClassification { expression, .. } => {
                    pending.push(Node::Expression(expression))
                }
                CExpression::FloatNegate(value)
                | CExpression::AddressOf(value)
                | CExpression::CheckedObjectAddress(value)
                | CExpression::Not(value)
                | CExpression::BitwiseNot(value)
                | CExpression::Load(value) => pending.push(Node::Expression(value)),
                CExpression::TypedLoad { pointer, .. }
                | CExpression::PointerOffsetBytes { pointer, .. }
                | CExpression::PointerAligned { pointer, .. } => {
                    pending.push(Node::Expression(pointer))
                }
                CExpression::Conditional {
                    condition,
                    then_branch,
                    else_branch,
                } => {
                    pending.push(Node::Expression(condition));
                    pending.push(Node::Expression(then_branch));
                    pending.push(Node::Expression(else_branch));
                }
                CExpression::ArrayRowAddress {
                    array: pointer,
                    index,
                    ..
                }
                | CExpression::RecordPointerOffset { pointer, index, .. } => {
                    pending.push(Node::Expression(pointer));
                    pending.push(Node::Expression(index));
                }
                CExpression::LessThan(left, right)
                | CExpression::LessEqual(left, right)
                | CExpression::GreaterThan(left, right)
                | CExpression::GreaterEqual(left, right)
                | CExpression::Equal(left, right)
                | CExpression::NotEqual(left, right)
                | CExpression::And(left, right)
                | CExpression::Or(left, right)
                | CExpression::Add(left, right)
                | CExpression::Subtract(left, right)
                | CExpression::Multiply(left, right)
                | CExpression::Divide(left, right)
                | CExpression::Remainder(left, right)
                | CExpression::ShiftLeft(left, right)
                | CExpression::ShiftRight(left, right)
                | CExpression::BitwiseAnd(left, right)
                | CExpression::BitwiseOr(left, right)
                | CExpression::BitwiseXor(left, right)
                | CExpression::Index(left, right) => {
                    pending.push(Node::Expression(left));
                    pending.push(Node::Expression(right));
                }
                CExpression::Variable(name) => {
                    if let Some(parameter) = parameters.get(name.as_str()) {
                        other_uses.insert(*parameter);
                    }
                }
                CExpression::Value(_) | CExpression::FunctionAddress(_) => {}
            },
        }
    }
    (
        fields.into_iter().collect(),
        copied.difference(&other_uses).copied().collect(),
    )
}

pub(crate) fn observed_field_selector(
    state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    field: &CPointerFieldSource,
    assumptions: &PureFactContext,
) -> Option<CPointerFieldSource> {
    let value = field_source_in(
        state,
        interface,
        arguments,
        field,
        field.value_type,
        assumptions,
        false,
    )?;
    let mut field = field.clone();
    field.pointee_constant = value.pointee_constant();
    field.pointee_volatile = value.pointee_volatile();
    Some(field)
}

pub(crate) fn preserves_input_field(effect: &CPointerStoreEffect) -> bool {
    effect.destination_field.as_ref().is_some_and(|field| {
        effect.source_field.as_ref() == Some(field)
            && effect.destination == CPointerEffectRoot::Parameter(field.parameter)
            && effect.source == effect.destination
            && effect.destination_path.as_ref() == field.path.as_ref()
            && effect.source_path.is_empty()
            && effect.value_type == field.value_type
    })
}

pub(crate) fn destination(
    state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    effect: &CPointerStoreEffect,
    assumptions: &PureFactContext,
) -> Option<(CPointerValue, CType)> {
    if let Some(field) = &effect.destination_field {
        // A write selects declared C storage without reading its old value.
        // The independent body check certifies the complete source value;
        // this selector supplies neither that evidence nor native authority.
        if effect.destination != CPointerEffectRoot::Parameter(field.parameter)
            || effect.destination_path.as_ref() != field.path.as_ref()
            || effect.value_type != field.value_type
            || !field.value_type.is_pointer()
        {
            return None;
        }
        Some((
            declared_field_address(state, interface, arguments, field, assumptions)?,
            field.value_type,
        ))
    } else {
        let pointer = selected(
            state,
            interface,
            arguments,
            &effect.destination,
            &effect.destination_path,
        )?;
        let element_type = selected_element_type(state, &pointer, assumptions)?;
        Some((pointer, element_type))
    }
}
pub(super) fn is_c_parameter_field_copy(
    interface: &CFunctionContractInterface,
    effect: &CPointerStoreEffect,
) -> bool {
    interface.typed_access_policy() == CTypedAccessPolicy::CAllocatedAccessAllowed
        && effect.destination_field.is_some()
        && effect.source_field.is_none()
        && effect.source_path.is_empty()
        && matches!(effect.source, CPointerEffectRoot::Parameter(_))
}

pub(super) fn writes_authorized(
    state: &CState,
    interface: &CFunctionContractInterface,
    arguments: &[CValue],
    effects: &[CPointerStoreEffect],
    assumptions: &PureFactContext,
    source_observations: Option<&CState>,
) -> bool {
    effects.iter().all(|effect| {
        let Some((destination, _)) = destination(state, interface, arguments, effect, assumptions)
        else {
            return false;
        };
        let bytes = effect.value_type.byte_width();
        if preserves_input_field(effect) {
            let readable = source_observations.unwrap_or(state);
            return resource_context_has_read(
                readable.resources(),
                destination.pointer(),
                bytes,
                assumptions,
            );
        }
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
    source_observations: Option<&CState>,
) -> Result<CMemory, String> {
    let mut memory = state.memory().clone();
    for effect in effects {
        let (destination, element_type) =
            destination(state, interface, arguments, effect, assumptions)
                .ok_or("certified pointer cell destination lacks its checked selection")?;
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
            let readable = if preserves_input_field(effect) {
                source_observations.unwrap_or(source_state)
            } else {
                source_state
            };
            field_source_in(
                readable,
                interface,
                arguments,
                field,
                effect.value_type,
                assumptions,
                !preserves_input_field(effect),
            )
        } else {
            selected(
                source_state,
                interface,
                arguments,
                &effect.source,
                &effect.source_path,
            )
            .filter(|source| {
                source.designation().is_some()
                    || source.is_null()
                    || (state.typed_access_policy() == CTypedAccessPolicy::CAllocatedAccessAllowed
                        && is_c_parameter_field_copy(interface, effect))
            })
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
    fn pointer_field_dependency_reads_include_loop_tests_but_not_private_images() {
        let layout = Arc::new(CAggregateLayout::new(
            8,
            8,
            vec![CAggregateField::new("data", 0, CType::Int32Pointer)],
        ));
        let read = c_typed_load(
            CExpression::MemberAddress {
                object: Box::new(c_variable("owner")),
                selection: Arc::new(CAggregateMemberSelection {
                    layout: layout.clone(),
                    path: vec!["data".into()].into(),
                    value_type: CType::Int32Pointer,
                }),
            },
            CType::Int32Pointer,
        );
        let body = c_while(
            c_not_equal(read, CExpression::Value(CValue::pointer(Pointer::null()))),
            vec![],
            c_skip(),
        );
        assert!(c_body_has_pointer_field_candidates_for_formals(
            [("owner", true)],
            &body
        ));
        assert!(!c_body_has_pointer_field_candidates_for_formals(
            [("owner", false)],
            &body
        ));
        assert!(!c_body_has_pointer_field_candidates_for_formals(
            [("other", true)],
            &body
        ));
        let ordinary = c_function(
            CType::Void,
            "loop_test",
            vec![c_parameter("owner", CType::Int32Pointer)],
            body.clone(),
        );
        assert!(c_body_has_pointer_field_candidates(&ordinary));
        let private = c_function(
            CType::Void,
            "private_test",
            vec![crate::kernel::c_parameter_with_aggregate_layout(
                "owner",
                CType::Int32Pointer,
                (*layout).clone(),
            )],
            body,
        );
        assert!(!c_body_has_pointer_field_candidates(&private));
    }

    #[test]
    fn c_field_candidate_inventory_ignores_unread_record_members() {
        let mut samples = Vec::new();
        for size in [0, 16, 64, 256] {
            let mut fields = vec![CAggregateField::new("data", 0, CType::Int32Pointer)];
            fields.extend((0..size).map(|index| {
                CAggregateField::new(format!("unused{index}"), 8 + index * 4, CType::Int32)
            }));
            let layout = Arc::new(CAggregateLayout::new(8 + size * 4, 8, fields));
            let selection = Arc::new(CAggregateMemberSelection {
                layout,
                path: vec!["data".into()].into(),
                value_type: CType::Int32Pointer,
            });
            let function = c_function(
                CType::Int32Pointer,
                "read_field",
                vec![c_parameter("p", CType::Int32Pointer)],
                c_return(c_typed_load(
                    CExpression::MemberAddress {
                        object: Box::new(c_variable("p")),
                        selection,
                    },
                    CType::Int32Pointer,
                )),
            );
            let (fields, work) =
                crate::instrumentation::measure_deterministic_work(|| c_declared_fields(&function));
            assert_eq!(fields.len(), 1);
            assert_eq!(fields[0].path.as_ref(), ["data"]);
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] + 8),
            "{samples:?}"
        );
    }

    #[test]
    fn c_copy_input_recipe_is_bounded_to_exclusive_value_operands() {
        let mut samples = Vec::new();
        for size in [0, 16, 64, 256] {
            let mut fields = vec![CAggregateField::new("data", 0, CType::Int32Pointer)];
            fields.extend((0..size).map(|index| {
                CAggregateField::new(format!("unused{index}"), 8 + index * 4, CType::Int32)
            }));
            let target = CExpression::MemberAddress {
                object: Box::new(c_variable("owner")),
                selection: Arc::new(CAggregateMemberSelection {
                    layout: Arc::new(CAggregateLayout::new(8 + size * 4, 8, fields)),
                    path: vec!["data".into()].into(),
                    value_type: CType::Int32Pointer,
                }),
            };
            let function = |body| {
                c_function(
                    CType::Void,
                    "copy_recipe",
                    vec![
                        c_parameter("owner", CType::Int32Pointer),
                        c_parameter("input", CType::Int32Pointer),
                    ],
                    c_seq(body, c_return(c_void_value())),
                )
            };
            let store = c_typed_store(target.clone(), c_variable("input"), CType::Int32Pointer);
            let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
                c_body_opaque_pointer_copy_inputs(&function(store.clone()))
            });
            assert_eq!(selected, BTreeSet::from([1]));
            samples.push(work);
            let writes_through_source = c_seq(
                c_typed_store(c_variable("input"), c_int32_literal(7), CType::Int32),
                store,
            );
            assert!(c_body_opaque_pointer_copy_inputs(&function(writes_through_source)).is_empty());
            let self_copy = c_typed_store(target, c_variable("owner"), CType::Int32Pointer);
            assert!(c_body_opaque_pointer_copy_inputs(&function(self_copy)).is_empty());
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] + 8),
            "{samples:?}"
        );
    }

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
    fn c_field_copy_destination_requires_exact_selector_and_existing_storage_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = Arc::new(CAggregateLayout::new(
            16,
            8,
            vec![
                CAggregateField::new("length", 0, CType::Int32),
                CAggregateField::new("data", 8, CType::Int32Pointer),
            ],
        ));
        let address = CMemory::local_pointer("c_copy_owner");
        let owner = CPointerValue::new(address.clone(), CType::Int32Pointer);
        let field_address = address.offset_by_bytes(8);
        let input = CPointerValue::new(Pointer::symbolic(Variable(9_899_501)), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(9_899_501)));
        let memory = CMemory::new().with_block(address.block.clone(), 16).store(
            field_address.clone(),
            CValue::UInt64(Bitvector32Term::UInt64Constant(0)),
        );
        let state = CState::new().with_memory(memory).with_resource_context(
            ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(field_address.clone(), 0.into(), 1.into(), 8),
            )),
        );
        let interface = c_function(
            CType::Int32,
            "copy_field",
            vec![
                c_parameter("owner", CType::Int32Pointer),
                c_parameter("input", CType::Int32Pointer),
            ],
            c_skip(),
        )
        .contract_interface()
        .clone();
        let arguments = [
            CValue::Pointer(owner.clone()),
            CValue::Pointer(input.clone()),
        ];
        let field = CPointerFieldSource {
            parameter: 0,
            layout,
            path: vec!["data".into()].into(),
            value_type: CType::Int32Pointer,
            pointee_constant: false,
            pointee_volatile: false,
        };
        let effect = CPointerStoreEffect {
            destination: CPointerEffectRoot::Parameter(0),
            destination_path: field.path.clone(),
            destination_field: Some(field),
            value_type: CType::Int32Pointer,
            source: CPointerEffectRoot::Parameter(1),
            source_path: Default::default(),
            source_field: None,
        };
        let facts = PureFactContext::new();
        assert!(!preserves_input_field(&effect));
        assert!(writes_authorized(
            &state,
            &interface,
            &arguments,
            std::slice::from_ref(&effect),
            &facts,
            None
        ));
        let memory = apply(
            &state,
            &state,
            &interface,
            &arguments,
            std::slice::from_ref(&effect),
            &facts,
            None,
        )
        .unwrap();
        assert_eq!(
            memory.known_value(&field_address),
            Some(CValue::Pointer(input.clone()))
        );
        assert!(memory.checked_native_record_pointer(&owner).is_none());
        assert!(memory.native_input_span(&input).is_none());
        for source in [
            CPointerValue::new(Pointer::symbolic(Variable(9_899_502)), CType::Int32Pointer),
            CPointerValue::new(Pointer::null(), CType::Int32Pointer),
        ] {
            let arguments = [
                CValue::Pointer(owner.clone()),
                CValue::Pointer(source.clone()),
            ];
            let memory = apply(
                &state,
                &state,
                &interface,
                &arguments,
                std::slice::from_ref(&effect),
                &facts,
                None,
            )
            .unwrap();
            assert_eq!(
                memory.known_value(&field_address),
                Some(CValue::Pointer(source))
            );
        }
        let native_layout = &effect.destination_field.as_ref().unwrap().layout;
        let native_memory = state
            .memory()
            .clone()
            .with_declared_aggregate_block(address.block.clone(), native_layout);
        let native_owner = native_memory
            .declared_aggregate_pointer(&address, native_layout)
            .unwrap()
            .with_type(CType::Int32Pointer);
        let native_state = state
            .clone()
            .with_memory(native_memory)
            .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
        let mut strict_interface = interface.clone();
        strict_interface.typed_access_policy = CTypedAccessPolicy::NativeObjectOnly;
        let null = CPointerValue::new(Pointer::null(), CType::Int32Pointer);
        let native_arguments = [
            CValue::Pointer(native_owner.clone()),
            CValue::Pointer(null.clone()),
        ];
        let copied = apply(
            &native_state,
            &native_state,
            &strict_interface,
            &native_arguments,
            std::slice::from_ref(&effect),
            &facts,
            None,
        )
        .unwrap();
        assert_eq!(
            copied.known_value(&field_address),
            Some(CValue::Pointer(null))
        );
        let legacy =
            CPointerValue::new(Pointer::symbolic(Variable(9_899_503)), CType::Int32Pointer);
        let native_arguments = [CValue::Pointer(native_owner), CValue::Pointer(legacy)];
        assert!(
            apply(
                &native_state,
                &native_state,
                &strict_interface,
                &native_arguments,
                std::slice::from_ref(&effect),
                &facts,
                None
            )
            .is_err()
        );
        let no_resources = state.clone().with_resource_context(ResourceContext::new());
        assert!(!writes_authorized(
            &no_resources,
            &interface,
            &arguments,
            std::slice::from_ref(&effect),
            &facts,
            None
        ));
        let partial = state.clone().with_memory(
            CMemory::new()
                .with_block(address.block.clone(), 16)
                .store(field_address.clone(), int32(0)),
        );
        assert!(
            apply(
                &partial,
                &state,
                &interface,
                &arguments,
                std::slice::from_ref(&effect),
                &facts,
                None
            )
            .is_err()
        );
        assert!(
            destination(
                &state
                    .clone()
                    .with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly),
                &interface,
                &arguments,
                &effect,
                &facts
            )
            .is_none()
        );
        let mut native_interface = interface.clone();
        native_interface.typed_access_policy = CTypedAccessPolicy::NativeObjectOnly;
        assert!(destination(&state, &native_interface, &arguments, &effect, &facts).is_none());
        let mut wrong = effect.clone();
        wrong.destination = CPointerEffectRoot::Parameter(1);
        assert!(destination(&state, &interface, &arguments, &wrong, &facts).is_none());
        wrong = effect.clone();
        wrong.destination_path = vec!["length".into()].into();
        assert!(destination(&state, &interface, &arguments, &wrong, &facts).is_none());
        wrong = effect.clone();
        wrong.value_type = CType::UInt64;
        assert!(destination(&state, &interface, &arguments, &wrong, &facts).is_none());
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
            destination_field: None,
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
                &PureFactContext::new(),
                None,
            )
            .is_err()
        );
        assert!(!writes_authorized(
            &state,
            &interface,
            &args,
            std::slice::from_ref(&effect),
            &PureFactContext::new(),
            None,
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
            &PureFactContext::new(),
            None,
        ));
        let owned = state.clone().with_resource_context(
            ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(range)),
        );
        assert!(writes_authorized(
            &owned,
            &interface,
            &args,
            std::slice::from_ref(&effect),
            &PureFactContext::new(),
            None,
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
            None,
        )
        .unwrap();
        assert_eq!(after.known_value(&address), Some(CValue::Pointer(source)));
        assert_eq!(after.heap.initialized, marks);
    }
}
