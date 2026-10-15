use super::*;
use crate::kernel::{CResourceTerm, ResourceFieldSchema, c_int32_literal, c_variable};

pub(in crate::surface) fn construction_result_layout(
    parsed: &syntax::C0Function,
) -> Option<&crate::kernel::CAggregateLayout> {
    let interface = parsed.prelowered_kernel_function()?.contract_interface();
    (interface.aggregate_return_mode() == crate::kernel::CAggregateReturnMode::Construction)
        .then(|| interface.return_aggregate_layout())
        .flatten()
}

/// The frontend's result object is an implicit in/out resource. Its authority
/// originates with the caller's storage, not with the destination binding.
pub(in crate::surface) fn construction_result_resource(
    parsed: &syntax::C0Function,
) -> Result<Option<CResourceSpec>, ClickError> {
    let Some(layout) = construction_result_layout(parsed) else {
        return Ok(None);
    };
    if layout.size_bytes() > i32::MAX as u32 {
        return Err(ClickError::new(
            "construction result exceeds the supported byte-range size",
        ));
    }
    Ok(Some(CResourceSpec::owned_memory(
        CMemorySegment::new(
            c_variable(crate::kernel::C_CONTRACT_RESULT_NAME),
            c_int32_literal(0),
            c_int32_literal(layout.size_bytes()),
        )
        .with_element_width(1),
    )))
}

/// Retain typed access separately from the clause's byte permission and
/// snapshot loadability. The bounded constructor profile admits one scalar
/// at a direct parameter; a raw pointer signature alone contributes nothing.
pub(in crate::surface) fn scalar_object_inputs_for_contract(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    function: &CFunction,
) -> Result<Vec<crate::kernel::CScalarObjectInput>, ClickError> {
    let mut inputs = function
        .contract_interface()
        .scalar_object_inputs()
        .iter()
        .map(|input| (input.parameter_index, input.element_type))
        .collect::<BTreeMap<_, _>>();
    let Some((destination, _)) = function.contract_interface().construction_parameter() else {
        return Ok(function
            .contract_interface()
            .scalar_object_inputs()
            .to_vec());
    };
    fn parameter_root(expression: &CExpression) -> Option<&str> {
        match expression {
            CExpression::Variable(name) => Some(name),
            CExpression::Add(pointer, _)
            | CExpression::Subtract(pointer, _)
            | CExpression::Cast {
                expression: pointer,
                ..
            }
            | CExpression::PointerOffsetBytes { pointer, .. } => parameter_root(pointer),
            _ => None,
        }
    }
    fn visit(
        resource: &ResourceClause,
        parameters: &[syntax::C0Parameter],
        destination: usize,
        guarded: bool,
        inputs: &mut BTreeMap<usize, CType>,
    ) -> Result<(), ClickError> {
        let segments: &[ContractSegment] = match resource {
            ResourceClause::OwnMemory(segment) | ResourceClause::ViewMemory(segment) => {
                std::slice::from_ref(segment)
            }
            ResourceClause::MemoryAggregate { segments, .. } => segments,
            ResourceClause::Named { resource, .. } => {
                return visit(resource, parameters, destination, guarded, inputs);
            }
            ResourceClause::Conditional { resource, .. }
            | ResourceClause::Quantified { resource, .. } => {
                return visit(resource, parameters, destination, true, inputs);
            }
            ResourceClause::Declared { .. } | ResourceClause::Iterated(_) => return Ok(()),
        };
        for segment in segments {
            let Some(parameter_index) = parameter_root(&segment.base).and_then(|name| {
                parameters
                    .iter()
                    .position(|parameter| parameter.name() == name)
            }) else {
                continue;
            };
            if parameter_index == destination {
                continue;
            }
            let parameter = &parameters[parameter_index];
            let element_type = contract_segment_element_type(parameters, segment);
            let exact_bound = |expression: &CExpression, expected| matches!(expression, CExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))) if *value == expected);
            if guarded
                || !matches!(segment.base, CExpression::Variable(_))
                || !exact_bound(&segment.start, 0)
                || !exact_bound(&segment.end, 1)
                || parameter.pointee_struct_layout().is_some()
                || !matches!(element_type, CType::Int32 | CType::Int64)
                || parameter.to_kernel_parameter().c_type().pointee_type() != Some(element_type)
            {
                return Err(ClickError::new(
                    "constructor scalar input requires an unconditional direct int32 or int64 parameter cell at [0..1]",
                ));
            }
            if inputs
                .insert(parameter_index, element_type)
                .is_some_and(|held| held != element_type)
            {
                return Err(ClickError::new(
                    "conflicting constructor scalar input types",
                ));
            }
        }
        Ok(())
    }
    for requirement in requires {
        if let Requirement::Resource(resource) = requirement {
            visit(resource, parameters, destination, false, &mut inputs)?;
        }
    }
    Ok(inputs
        .into_iter()
        .map(
            |(parameter_index, element_type)| crate::kernel::CScalarObjectInput {
                parameter_index,
                element_type,
            },
        )
        .collect())
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct ConcreteMemoryRangeSeed {
    pub(in crate::surface) base: Pointer,
    pub(in crate::surface) bytes: u32,
    pub(in crate::surface) element_width: u32,
    /// `None` denotes a range whose logical elements are aggregates, such as
    /// C structs. Those ranges are materialized one typed field at a time
    /// using `struct_layout`.
    pub(in crate::surface) element_type: Option<CType>,
    pub(in crate::surface) observation_count: Option<u32>,
    pub(in crate::surface) struct_layout: Option<syntax::C0StructLayout>,
}

// Input addresses from different function proofs must not share load/type
// metadata. A context-local parameter index alone names unrelated universal
// inputs with the same term, e.g. an eight-byte `self->slot` and a four-byte
// caller `value[0]`. Keep content-based names collision-checked and outside
// the scalar-load and ordinary lexical-variable namespaces. Inputs occupy
// `100_000 .. 1_000_000`, below execution and load names so ordinary inputs
// remain preferred canonical address representatives.
thread_local! {
    static INPUT_SCOPES: std::cell::RefCell<std::collections::HashMap<u64, String>> = Default::default();
    static INPUT_POINTER_PLACES: std::cell::RefCell<std::collections::HashMap<Variable, (u64, usize, crate::kernel::CPointerValue)>> = Default::default();
    static INPUT_VARIABLES: std::cell::RefCell<std::collections::HashMap<(u64, usize), Variable>> = Default::default();
}

pub(in crate::surface) fn input_scope(name: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    name.hash(&mut hasher);
    let mut slot = hasher.finish();
    INPUT_SCOPES.with(|scopes| {
        let mut scopes = scopes.borrow_mut();
        loop {
            match scopes.get(&slot) {
                Some(known) if known == name => return slot,
                Some(_) => slot = slot.wrapping_add(1),
                None => {
                    scopes.insert(slot, name.to_string());
                    return slot;
                }
            }
        }
    })
}

fn input_pointer_variable(scope: u64, index: usize) -> Result<Variable, ClickError> {
    INPUT_VARIABLES.with(|variables| {
        let mut variables = variables.borrow_mut();
        if let Some(variable) = variables.get(&(scope, index)) {
            return Ok(*variable);
        }
        let name = POINTER_ARGUMENT_VARIABLE_BASE + variables.len() as u64;
        if name >= 1_000_000 {
            return Err(ClickError::new(
                "pointer input variable namespace exhausted",
            ));
        }
        let variable = Variable(name);
        variables.insert((scope, index), variable);
        Ok(variable)
    })
}

// Resolve only an exact universal input, including its physical stride and type.
// This index is populated during lowering, so expansion scopes may be entered
// before the function is verified. No unrelated function inputs are searched.
pub(in crate::surface) fn input_pointer_parameter(
    scope: u64,
    pointer: &crate::kernel::CPointerValue,
) -> Option<usize> {
    let variable = input_pointer_identity(pointer)?;
    crate::instrumentation::record_deterministic_work(1);
    INPUT_POINTER_PLACES.with(|places| {
        let places = places.borrow();
        let (owner, index, original) = places.get(&variable)?;
        (*owner == scope && original == pointer).then_some(*index)
    })
}

/// Source member access implies a valid enclosing declared record independently
/// of the byte authority granted by its clause. A signature or numeric address
/// alone cannot supply this requirement. Entry assumes exactly the interface
/// requirement that native calls discharge.
pub(in crate::surface) fn aggregate_object_inputs_for_contract(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    function: &CFunction,
) -> Result<Vec<crate::kernel::CAggregateObjectInput>, ClickError> {
    let parameter_indices = parameters
        .iter()
        .enumerate()
        .map(|(index, parameter)| (parameter.name(), index))
        .collect::<BTreeMap<_, _>>();
    let mut inputs = function
        .contract_interface()
        .aggregate_object_inputs()
        .iter()
        .map(|input| (input.parameter_index, input.layout.clone()))
        .collect::<BTreeMap<_, _>>();
    fn member_path<'a>(
        expression: &'a ContractExpression,
        path: &mut Vec<String>,
    ) -> Option<&'a str> {
        match expression {
            ContractExpression::Field { base, field, .. } => {
                let root = member_path(base, path)?;
                path.push(field.clone());
                Some(root)
            }
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => Some(name),
            _ => None,
        }
    }
    fn visit(
        resource: &ResourceClause,
        parameters: &[syntax::C0Parameter],
        parameter_indices: &BTreeMap<&str, usize>,
        inputs: &mut BTreeMap<usize, std::sync::Arc<crate::kernel::CAggregateLayout>>,
    ) -> Result<(), ClickError> {
        let segments: &[ContractSegment] = match resource {
            ResourceClause::OwnMemory(segment) | ResourceClause::ViewMemory(segment) => {
                std::slice::from_ref(segment)
            }
            ResourceClause::MemoryAggregate { segments, .. } => segments,
            ResourceClause::Named { resource, .. } => {
                return visit(resource, parameters, parameter_indices, inputs);
            }
            // Guarded, quantified and instantiated resource obligations do not
            // supply an unconditional direct native parameter requirement.
            _ => return Ok(()),
        };
        for segment in segments {
            let mut path = Vec::new();
            let (root, member_type, object_name) = match &segment.surface {
                ContractSegmentSurface::Range {
                    base:
                        ContractExpression::CUnary {
                            operand,
                            lowered: CExpression::AddressOf(_),
                        },
                    ..
                } => {
                    let ContractExpression::Field {
                        lowered: CExpression::TypedLoad { value_type, .. },
                        ..
                    } = operand.as_ref()
                    else {
                        continue;
                    };
                    let Some(root) = member_path(operand, &mut path) else {
                        continue;
                    };
                    (root, Some(*value_type), None)
                }
                ContractSegmentSurface::Range {
                    base:
                        expression @ ContractExpression::Field {
                            lowered: CExpression::TypedLoad { value_type, .. },
                            ..
                        },
                    ..
                } if value_type.array_element_and_count().is_some() => {
                    let Some(root) = member_path(expression, &mut path) else {
                        continue;
                    };
                    (root, Some(*value_type), None)
                }
                ContractSegmentSurface::Field {
                    base: Some(base),
                    name,
                    element_type: Some(value_type),
                    ..
                } => {
                    let Some(root) = member_path(base, &mut path) else {
                        continue;
                    };
                    path.push(name.clone());
                    (root, Some(*value_type), None)
                }
                ContractSegmentSurface::Field {
                    base: None,
                    name,
                    element_type: Some(value_type),
                    ..
                } => {
                    // The aggregate-place producer retains declared dotted
                    // leaf names beside its exact root variable. Indexed
                    // backing leaves do not describe a bounded record path.
                    let CExpression::Variable(root) = &segment.base else {
                        continue;
                    };
                    if name.contains('[') {
                        continue;
                    }
                    path.extend(name.split('.').map(str::to_string));
                    (root.as_str(), Some(*value_type), None)
                }
                ContractSegmentSurface::Object(name) => {
                    let CExpression::Variable(root) = &segment.base else {
                        continue;
                    };
                    (root.as_str(), None, Some(name.as_str()))
                }
                _ => continue,
            };
            let Some(&parameter_index) = parameter_indices.get(root) else {
                continue;
            };
            let parameter = &parameters[parameter_index];
            if parameter.is_struct_value()
                || parameter.array_element_width().is_some()
                || !parameter.is_native_pointer_input()
            {
                continue;
            }
            let Some(source_layout) = parameter.pointee_struct_layout() else {
                continue;
            };
            if object_name.is_some_and(|name| parameter.struct_name() != Some(name)) {
                continue;
            }
            let layout = if let Some(layout) = inputs.get(&parameter_index) {
                layout.clone()
            } else {
                std::sync::Arc::new(source_layout.to_kernel_aggregate_layout())
            };
            if !layout.unions().is_empty() {
                // Overlapping member lifetimes are outside the bounded record profile.
                continue;
            }
            if let Some(member_type) = member_type
                && layout
                    .member_at_path(&path)
                    .is_none_or(|(_, declared)| declared != member_type)
            {
                continue;
            }
            inputs.insert(parameter_index, layout);
        }
        Ok(())
    }
    for requirement in requires {
        if let Requirement::Resource(resource) = requirement {
            visit(resource, parameters, &parameter_indices, &mut inputs)?;
        }
    }
    Ok(inputs
        .into_iter()
        .map(
            |(parameter_index, layout)| crate::kernel::CAggregateObjectInput {
                parameter_index,
                layout,
            },
        )
        .collect())
}

/// Native validity comes from an explicit typed source place, independently
/// of its normalized byte permission. Numeric offsets and equality are never
/// used to discover a declaration or a loaded carrier.
pub(in crate::surface) fn native_record_places_for_resource(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    layouts: &BTreeMap<String, syntax::C0StructLayout>,
) -> Result<Vec<crate::kernel::CNativeRecordPlaceRequirement>, ClickError> {
    fn carrier(
        expression: &ContractExpression,
        parameters: &[syntax::C0Parameter],
        layouts: &BTreeMap<String, syntax::C0StructLayout>,
        places: &mut Vec<crate::kernel::CNativeRecordPlaceRequirement>,
    ) -> Option<(CExpression, String)> {
        let (value, name) = match expression {
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => {
                let parameter = parameters
                    .iter()
                    .find(|parameter| parameter.name() == name)?;
                if !parameter.c_type().is_pointer()
                    || parameter.is_struct_value()
                    || parameter.array_element_width().is_some()
                {
                    return None;
                }
                (c_variable(name), parameter.struct_name()?.to_string())
            }
            ContractExpression::Field {
                base,
                field,
                lowered,
                offset_bytes,
            } => {
                let (parent, name) = carrier(base, parameters, layouts, places)?;
                let layout = layouts.get(&name)?;
                let declared = layout.field(field)?;
                if declared.offset_bytes() != *offset_bytes {
                    return None;
                }
                let CExpression::TypedLoad { value_type, .. } = lowered else {
                    return None;
                };
                if *value_type != declared.c_type().to_kernel_type() {
                    return None;
                }
                let name = declared.struct_name()?.to_string();
                if declared.c_type().is_pointer() {
                    (lowered.clone(), name)
                } else {
                    // Embedded storage is selected by the enclosing record's
                    // declaration; it does not become a new abstract root.
                    return Some((
                        crate::kernel::c_pointer_offset_bytes(parent, *offset_bytes),
                        name,
                    ));
                }
            }
            _ => return None,
        };
        let layout = std::sync::Arc::new(layouts.get(&name)?.to_kernel_aggregate_layout());
        if !layout.unions().is_empty() {
            return None;
        }
        if !places
            .iter()
            .any(|place| place.carrier == value && place.layout == layout)
        {
            places.push(crate::kernel::CNativeRecordPlaceRequirement {
                carrier: value.clone(),
                layout,
                prefix_count: None,
            });
        }
        Some((value, name))
    }
    fn native_count(
        source: &ContractExpression,
        lowered: &CExpression,
        parameters: &[syntax::C0Parameter],
        layouts: &BTreeMap<String, syntax::C0StructLayout>,
    ) -> bool {
        match (source, lowered) {
            (_, CExpression::Value(CValue::Int32(Bitvector32Term::Constant(value)))) => {
                i32::try_from(*value).is_ok_and(|value| value > 0)
            }
            (_, CExpression::Value(CValue::Int64(Bitvector32Term::Int64Constant(value)))) => {
                *value > 0
            }
            (
                ContractExpression::Binding(name)
                | ContractExpression::CBinding(name)
                | ContractExpression::CFragment(CExpression::Variable(name)),
                CExpression::Variable(lowered),
            ) => {
                name == lowered
                    && parameters.iter().any(|parameter| {
                        parameter.name() == name
                            && matches!(
                                parameter.c_type(),
                                syntax::C0Type::Int32 | syntax::C0Type::Int64(_)
                            )
                    })
            }
            (
                ContractExpression::Field {
                    base,
                    field,
                    lowered: source_lowered,
                    offset_bytes,
                },
                _,
            ) => {
                let mut ignored = Vec::new();
                let Some((_, name)) = carrier(base, parameters, layouts, &mut ignored) else {
                    return false;
                };
                let Some(declared) = layouts.get(&name).and_then(|layout| layout.field(field))
                else {
                    return false;
                };
                source_lowered == lowered
                    && declared.offset_bytes() == *offset_bytes
                    && matches!(
                        declared.c_type(),
                        syntax::C0Type::Int32 | syntax::C0Type::Int64(_)
                    )
                    && matches!(lowered, CExpression::TypedLoad { value_type, .. } if *value_type == declared.c_type().to_kernel_type())
            }
            _ => false,
        }
    }
    fn segment(
        segment: &ContractSegment,
        parameters: &[syntax::C0Parameter],
        layouts: &BTreeMap<String, syntax::C0StructLayout>,
        places: &mut Vec<crate::kernel::CNativeRecordPlaceRequirement>,
    ) {
        let mut candidate = Vec::new();
        if let ContractSegmentSurface::StructRange {
            base, end, layout, ..
        } = &segment.surface
        {
            if !matches!(
                &segment.start,
                CExpression::Value(CValue::Int32(Bitvector32Term::Constant(0)))
            ) || !native_count(end, &segment.end, parameters, layouts)
            {
                return;
            }
            let Some((value, name)) = carrier(base, parameters, layouts, &mut candidate) else {
                return;
            };
            if name != layout.name || layouts.get(&name) != Some(&layout.layout) {
                return;
            }
            let Some(place) = candidate.iter_mut().find(|place| place.carrier == value) else {
                return;
            };
            place.prefix_count = Some(segment.end.clone());
            for place in candidate {
                if !places.iter().any(|existing| existing == &place) {
                    places.push(place);
                }
            }
            return;
        }

        let (base, path, expected) = match &segment.surface {
            ContractSegmentSurface::Field {
                base,
                name,
                element_type: Some(ty),
                ..
            } => {
                if name.contains('[') {
                    return;
                }
                let base = base
                    .as_deref()
                    .cloned()
                    .unwrap_or_else(|| ContractExpression::CFragment(segment.base.clone()));
                (
                    base,
                    name.split('.').map(str::to_string).collect::<Vec<_>>(),
                    Some(*ty),
                )
            }
            ContractSegmentSurface::IndexedField {
                place,
                element_type,
                element_width,
            } => {
                let mut selected = place.as_ref();
                let mut dimensions = 0;
                while let ContractExpression::Index(base, _) = selected {
                    dimensions += 1;
                    selected = base.as_ref();
                }
                let ContractExpression::Field {
                    base,
                    field,
                    lowered: CExpression::TypedLoad { value_type, .. },
                    offset_bytes,
                } = selected
                else {
                    return;
                };
                let Some((element, _)) = value_type.array_element_and_count() else {
                    return;
                };
                if element != *element_type || element.byte_width() != *element_width {
                    return;
                }
                let Some((_, name)) = carrier(base, parameters, layouts, &mut candidate) else {
                    return;
                };
                let Some(declared) = layouts.get(&name).and_then(|layout| layout.field(field))
                else {
                    return;
                };
                if declared.c_type().to_kernel_type() != *value_type
                    || declared.offset_bytes() != *offset_bytes
                    || declared.array_shape().map_or(1, <[u32]>::len) != dimensions
                    || declared.struct_name().is_some()
                {
                    return;
                }
                ((**base).clone(), vec![field.clone()], Some(*value_type))
            }
            ContractSegmentSurface::ObjectAt { name, base } => {
                let Some((_, actual)) = carrier(base, parameters, layouts, &mut candidate) else {
                    return;
                };
                if &actual != name {
                    return;
                }
                for place in candidate {
                    if !places.iter().any(|existing| existing == &place) {
                        places.push(place);
                    }
                }
                return;
            }
            ContractSegmentSurface::Object(name) => {
                let expression = ContractExpression::CFragment(segment.base.clone());
                let Some((_, actual)) = carrier(&expression, parameters, layouts, &mut candidate)
                else {
                    return;
                };
                if &actual != name {
                    return;
                }
                places.extend(candidate);
                return;
            }
            ContractSegmentSurface::Range { base, .. } => {
                let field = match base {
                    ContractExpression::CUnary {
                        operand,
                        lowered: CExpression::AddressOf(_),
                    } => operand.as_ref(),
                    ContractExpression::Field {
                        lowered: CExpression::TypedLoad { value_type, .. },
                        ..
                    } if value_type.array_element_and_count().is_some() => base,
                    _ => return,
                };
                let ContractExpression::Field {
                    base,
                    field,
                    lowered: CExpression::TypedLoad { value_type, .. },
                    ..
                } = field
                else {
                    return;
                };
                ((**base).clone(), vec![field.clone()], Some(*value_type))
            }
            _ => return,
        };
        let Some((_, name)) = carrier(&base, parameters, layouts, &mut candidate) else {
            return;
        };
        let Some(layout) = layouts.get(&name) else {
            return;
        };
        let layout = layout.to_kernel_aggregate_layout();
        if layout
            .member_at_path(&path)
            .is_none_or(|(_, ty)| Some(ty) != expected)
        {
            return;
        }
        for place in candidate {
            if !places.iter().any(|existing| existing == &place) {
                places.push(place);
            }
        }
    }
    let mut places = Vec::new();
    match resource {
        ResourceClause::OwnMemory(value) | ResourceClause::ViewMemory(value) => {
            segment(value, parameters, layouts, &mut places)
        }
        ResourceClause::MemoryAggregate { segments, .. } => {
            for value in segments {
                segment(value, parameters, layouts, &mut places);
            }
        }
        ResourceClause::Named { resource, .. } => {
            return native_record_places_for_resource(resource, parameters, layouts);
        }
        // Instantiated/guarded resources expose their checked body requirements
        // through kernel occurrence exchange, never an eager source scan.
        _ => {}
    }
    Ok(places)
}

/// Preserve a bounded typed prefix from its source pointer declaration, not
/// from an ownership interval, a cast, or aggregate byte storage.
pub(in crate::surface) fn native_span_requirements_for_resource(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    layouts: &BTreeMap<String, syntax::C0StructLayout>,
) -> Result<Vec<crate::kernel::CNativeSpanRequirement>, ClickError> {
    fn declared_type(
        expression: &ContractExpression,
        parameters: &[syntax::C0Parameter],
        layouts: &BTreeMap<String, syntax::C0StructLayout>,
    ) -> Option<(syntax::C0Type, Option<String>, CExpression)> {
        match expression {
            ContractExpression::CFragment(
                expression @ CExpression::TypedLoad {
                    pointer,
                    value_type: CType::UInt64,
                    ..
                },
            ) if matches!(pointer.as_ref(), CExpression::MemberAddress { selection, .. }
                if selection.layout.declaration_identity().is_some()
                    && selection.value_type == CType::UInt64
                    && selection.layout.member_at_path(&selection.path)
                        .is_some_and(|(_, ty)| ty == CType::UInt64)) =>
            {
                Some((
                    syntax::C0Type::UInt64(syntax::LongRank::Long),
                    None,
                    expression.clone(),
                ))
            }

            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => {
                let parameter = parameters
                    .iter()
                    .find(|parameter| parameter.name() == name)?;
                Some((
                    parameter.c_type(),
                    parameter.struct_name().map(str::to_string),
                    c_variable(name),
                ))
            }
            ContractExpression::Field {
                base,
                field,
                lowered,
                offset_bytes,
            } => {
                let (_, name, parent) = declared_type(base, parameters, layouts)?;
                let layout = layouts.get(name.as_ref()?)?;
                let declared = layout.field(field)?;
                if declared.offset_bytes() != *offset_bytes {
                    return None;
                }
                let native_layout = std::sync::Arc::new(layout.to_kernel_aggregate_layout());
                let path = std::sync::Arc::from([field.clone()]);
                if !declared.c_type().is_pointer()
                    && let Some(child_name) = declared.struct_name()
                {
                    // Imported embedded records use a nominal Int32 source
                    // placeholder and lower to an address, not a scalar load.
                    // Select the genuine retained record boundary instead of
                    // treating that placeholder as scalar storage or a span.
                    let child = layouts.get(child_name)?;
                    let (offset, value_type) = native_layout.member_at_path(&path)?;
                    if offset != *offset_bytes
                        || value_type != CType::UInt8Array(child.size_bytes())
                    {
                        return None;
                    }
                    return Some((
                        declared.c_type(),
                        Some(child_name.to_string()),
                        CExpression::MemberAddress {
                            object: Box::new(parent),
                            selection: std::sync::Arc::new(
                                crate::kernel::CAggregateMemberSelection {
                                    layout: native_layout,
                                    path,
                                    value_type,
                                },
                            ),
                        },
                    ));
                }
                let CExpression::TypedLoad { value_type, .. } = lowered else {
                    return None;
                };
                if declared.c_type().to_kernel_type() != *value_type {
                    return None;
                }
                if native_layout
                    .member_at_path(&path)
                    .is_none_or(|(offset, ty)| offset != *offset_bytes || ty != *value_type)
                {
                    return None;
                }
                let mut native_load = lowered.clone();
                let CExpression::TypedLoad { pointer, .. } = &mut native_load else {
                    unreachable!()
                };
                **pointer = CExpression::MemberAddress {
                    object: Box::new(parent),
                    selection: std::sync::Arc::new(crate::kernel::CAggregateMemberSelection {
                        layout: native_layout,
                        path,
                        value_type: *value_type,
                    }),
                };
                Some((
                    declared.c_type(),
                    declared.struct_name().map(str::to_string),
                    native_load,
                ))
            }
            _ => None,
        }
    }
    fn nonnegative_bound(expression: &CExpression) -> Option<u64> {
        match expression {
            CExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))) => {
                i32::try_from(*value).ok().map(|value| value as u64)
            }
            CExpression::Value(CValue::Int64(Bitvector32Term::Int64Constant(value))) => {
                u64::try_from(*value).ok()
            }
            CExpression::Value(CValue::UInt32(Bitvector32Term::Constant(value))) => {
                Some(u64::from(*value))
            }
            CExpression::Value(CValue::UInt64(Bitvector32Term::UInt64Constant(value))) => {
                Some(*value)
            }
            _ => None,
        }
    }
    fn positive_bound(expression: &CExpression) -> Option<u64> {
        nonnegative_bound(expression).filter(|value| *value > 0)
    }
    fn native_object_pointer_source(
        expression: &ContractExpression,
        parameters: &[syntax::C0Parameter],
        layouts: &BTreeMap<String, syntax::C0StructLayout>,
    ) -> bool {
        match expression {
            ContractExpression::Binding(name)
            | ContractExpression::CBinding(name)
            | ContractExpression::CFragment(CExpression::Variable(name)) => parameters
                .iter()
                .find(|parameter| parameter.name() == name)
                .is_some_and(syntax::C0Parameter::has_explicit_native_pointer_input),
            ContractExpression::Field { base, .. } => {
                native_object_pointer_source(base, parameters, layouts)
                    || declared_type(base, parameters, layouts)
                        .and_then(|(_, name, _)| name)
                        .and_then(|name| layouts.get(&name))
                        .is_some_and(syntax::C0StructLayout::has_cpp_declaration_identity)
            }
            _ => false,
        }
    }
    let mut spans = Vec::new();
    let segments = match resource {
        ResourceClause::OwnMemory(segment) | ResourceClause::ViewMemory(segment) => {
            std::slice::from_ref(segment)
        }
        ResourceClause::MemoryAggregate { segments, .. } => segments,
        ResourceClause::Named { resource, .. } => {
            return native_span_requirements_for_resource(resource, parameters, layouts);
        }
        _ => return Ok(spans),
    };
    for segment in segments {
        let ContractSegmentSurface::Range { base, end, .. } = &segment.surface else {
            continue;
        };
        let Some(start) = nonnegative_bound(&segment.start) else {
            continue;
        };
        if let Some(end) = nonnegative_bound(&segment.end) {
            // An empty interval promises no formation/access. Invalid ranges
            // are refused by ordinary range lowering, never made into witnesses.
            if start >= end {
                continue;
            }
        } else if start != 0 {
            // Nonliteral displaced windows need a separately checked ordering
            // recipe. Preserve the existing symbolic zero-prefix boundary.
            continue;
        }
        let (source_pointer, mut count_expression, count_surface) = match base {
            ContractExpression::CUnary {
                operand,
                lowered: CExpression::AddressOf(_),
            } if matches!(
                &segment.end,
                CExpression::Value(CValue::Int32(Bitvector32Term::Constant(1)))
            ) =>
            {
                let ContractExpression::Index(pointer, index) = operand.as_ref() else {
                    continue;
                };
                if let ContractExpression::CFragment(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Constant(index),
                ))) = index.as_ref()
                {
                    let Some(count) = index
                        .checked_add(1)
                        .filter(|count| i32::try_from(*count).is_ok())
                    else {
                        continue;
                    };
                    (pointer.as_ref(), c_int32_literal(count), None)
                } else if let ContractExpression::Subtract(bound, one) = index.as_ref()
                    && resource_argument_to_c_expression(one).ok()
                        == Some(crate::kernel::c_uint64_literal(1))
                    && let Some((syntax::C0Type::UInt64(_), None, lowered)) =
                        declared_type(bound, parameters, layouts)
                {
                    // A typed last-element place promises the prefix geometry
                    // ending at its retained native size, not byte authority
                    // or initialization of any preceding element.
                    (pointer.as_ref(), lowered, Some(bound.as_ref()))
                } else {
                    continue;
                }
            }
            _ => (base, segment.end.clone(), Some(end)),
        };
        let constant_count = positive_bound(&count_expression);
        if constant_count.is_none() {
            // Retain only an explicit native integer count from this exact
            // source range. Its value, positivity, and byte extent are checked
            // by the selected typed-prefix query; it is not an array bound.
            let Some((declared, nominal_record, lowered)) =
                declared_type(count_surface.unwrap_or(end), parameters, layouts)
            else {
                continue;
            };
            if nominal_record.is_some()
                || !matches!(
                    declared,
                    syntax::C0Type::Int32
                        | syntax::C0Type::UInt32
                        | syntax::C0Type::Int64(_)
                        | syntax::C0Type::UInt64(_)
                )
                || resource_argument_to_c_expression(count_surface.unwrap_or(end))
                    .ok()
                    .as_ref()
                    != Some(&count_expression)
            {
                continue;
            }
            count_expression = lowered;
        }
        let Some((declared, nominal_record, carrier)) =
            declared_type(source_pointer, parameters, layouts)
        else {
            continue;
        };
        if nominal_record.is_some() {
            continue;
        }
        let element_type = match declared {
            syntax::C0Type::Int32Pointer => CType::Int32,
            syntax::C0Type::UInt32Pointer => CType::UInt32,
            syntax::C0Type::Int64Pointer(_) => CType::Int64,
            syntax::C0Type::UInt8Pointer => CType::UInt8,
            _ => continue,
        };
        // C character pointers may designate another object's representation;
        // its byte permission does not promise a native UInt8 element array.
        // Enroll this typed obligation only at authenticated native declarations.
        // This source boundary itself grants no representation access authority.
        if element_type == CType::UInt8
            && !native_object_pointer_source(source_pointer, parameters, layouts)
        {
            continue;
        }
        // A literal native prefix follows the same signed pointer-displacement
        // extent as a symbolic wide range, without narrowing its count to u32.
        if constant_count
            .is_some_and(|count| count > i64::MAX as u64 / u64::from(element_type.byte_width()))
        {
            continue;
        }
        spans.push(crate::kernel::CNativeSpanRequirement {
            access_policy: if native_object_pointer_source(source_pointer, parameters, layouts) {
                crate::kernel::CTypedAccessPolicy::NativeObjectOnly
            } else {
                crate::kernel::CTypedAccessPolicy::CAllocatedAccessAllowed
            },
            carrier,
            element_type,
            count: count_expression,
        });
    }
    Ok(spans)
}

fn input_pointer_identity(pointer: &crate::kernel::CPointerValue) -> Option<Variable> {
    if pointer.pointer().block != PointerBlock::ExternalArgument {
        return None;
    }
    match &pointer.pointer().offset {
        PointerOffsetTerm::Int32Scaled { value, .. } => match value.as_ref() {
            Bitvector32Term::Variable(variable) => Some(*variable),
            _ => None,
        },
        _ => None,
    }
}

/// Select only formals named by retained typed-prefix metadata. The marker
/// gives an input a stable carrier identity; admission below still checks the
/// exact requirement and adds no storage, initialization, or byte authority.
fn native_span_input_parameters(
    parameters: &[syntax::C0Parameter],
    specs: &[CResourceSpec],
    definitions: &[CCompositeResourceDefinition],
) -> BTreeSet<usize> {
    let kernel_parameters = parameters
        .iter()
        .map(syntax::C0Parameter::to_kernel_parameter)
        .collect::<Vec<_>>();
    crate::kernel::CFunctionContractInterface::declared_span_identity_parameters(
        &kernel_parameters,
        specs,
        definitions,
    )
    .into_iter()
    .collect()
}

/// Constructor fields preserve the opaque identity of actual C formals.
/// A held model equation supplies no object extent or native validity row.
fn native_model_input_parameters(
    parameters: &[syntax::C0Parameter],
    specs: &[CResourceSpec],
    requirements: &[SpecProposition],
) -> BTreeSet<usize> {
    use crate::kernel::{
        AlgebraicValueType, ResourceFieldType, SpecAlgebraicExpression,
        SpecAlgebraicExpressionNode, SpecAlgebraicValue,
    };
    let heads = specs
        .iter()
        .filter_map(|spec| {
            let CResourceTerm::Instance {
                identity, schema, ..
            } = spec.term()
            else {
                return None;
            };
            Some((*identity, schema))
        })
        .collect::<BTreeMap<_, _>>();
    let formals = parameters
        .iter()
        .enumerate()
        .filter(|(_, p)| p.c_type().is_pointer())
        .map(|(i, p)| (p.name(), (i, p.c_type().to_kernel_type())))
        .collect::<BTreeMap<_, _>>();
    fn constructor(
        expression: &SpecAlgebraicExpression,
        formals: &BTreeMap<&str, (usize, CType)>,
        selected: &mut BTreeSet<usize>,
    ) {
        let SpecAlgebraicExpressionNode::Constructor { variant, fields } = &expression.node else {
            return;
        };
        let Some(declaration) = expression
            .algebraic_type
            .variants
            .iter()
            .find(|v| &v.name == variant)
        else {
            return;
        };
        if declaration.fields.len() != fields.len() {
            return;
        }
        for (field, expected) in fields.iter().zip(&declaration.fields) {
            match (field, expected) {
                (
                    SpecAlgebraicValue::C(SpecExpression::CExpression(CExpression::Variable(name))),
                    AlgebraicValueType::C(ty),
                ) if ty.is_object_pointer() => {
                    if let Some(&(index, actual)) = formals.get(name.as_str())
                        && actual == *ty
                    {
                        selected.insert(index);
                    }
                }
                (
                    SpecAlgebraicValue::Algebraic(nested),
                    AlgebraicValueType::Algebraic { name, arguments },
                ) if nested.algebraic_type.name == *name
                    && nested.algebraic_type.arguments == *arguments =>
                {
                    constructor(nested, formals, selected);
                }
                _ => {}
            }
        }
    }
    let mut selected = BTreeSet::new();
    let mut pending = requirements.iter().collect::<Vec<_>>();
    while let Some(proposition) = pending.pop() {
        match proposition {
            SpecProposition::And(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            SpecProposition::ValidPlace {
                memory: crate::kernel::SpecMemory::Current,
                pointer: crate::kernel::SpecExpression::CExpression(CExpression::Variable(name)),
                ..
            } => {
                if let Some((index, _)) = formals.get(name.as_str()) {
                    selected.insert(*index);
                }
            }
            SpecProposition::AlgebraicComparison {
                left,
                equal: true,
                right,
            } => {
                for (head, value) in [(left, right), (right, left)] {
                    let SpecAlgebraicExpressionNode::ResourceField(projection) = &head.node else {
                        continue;
                    };
                    if !projection.children.is_empty() {
                        continue;
                    }
                    let Some(schema) = heads.get(&projection.identity) else {
                        continue;
                    };
                    let Some((_, ResourceFieldType::Algebraic(ty))) =
                        schema.fields().get(projection.field_index)
                    else {
                        continue;
                    };
                    if ty == &head.algebraic_type && ty == &value.algebraic_type {
                        constructor(value, &formals, &mut selected);
                    }
                }
            }
            _ => {}
        }
    }
    selected
}

pub(in crate::surface) fn initial_call_state(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    function: &CFunction,
    composite_definitions: &[CCompositeResourceDefinition],
) -> Result<(CState, Vec<CExpression>), ClickError> {
    let input_function = function
        .clone()
        .with_scalar_object_inputs(scalar_object_inputs_for_contract(
            requires, parameters, function,
        )?)
        .with_aggregate_object_inputs(aggregate_object_inputs_for_contract(
            requires, parameters, function,
        )?);
    let function = &input_function;
    if parameters.len() as u64 >= POINTER_ARGUMENT_VARIABLE_BASE {
        return Err(ClickError::new(
            "function parameter variable namespace exhausted",
        ));
    }
    let aggregate_parameters = parameters
        .iter()
        .filter(|parameter| parameter.is_struct_value())
        .map(|parameter| parameter.name())
        .collect::<BTreeSet<_>>();
    for requirement in requires {
        if let Requirement::Resource(resource) = requirement {
            reject_aggregate_parameter_storage_resource(resource, &aggregate_parameters)?;
        }
    }
    let mut arguments = Vec::new();
    let scope = input_scope(function.name());

    for (index, parameter) in parameters.iter().enumerate() {
        if parameter.is_struct_value() {
            arguments.push(c_typed_pointer_value(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(input_pointer_variable(scope, index)?),
                        1,
                    ),
                },
                parameter.to_kernel_parameter().c_type(),
            ));
            continue;
        }
        match parameter.c_type() {
            C0Type::Int128 => {
                arguments.push(CExpression::Value(CValue::Int128(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::UInt128 => {
                arguments.push(CExpression::Value(CValue::UInt128(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }

            C0Type::Void => {
                return Err(ClickError::new(format!(
                    "parameter `{}` cannot have type void",
                    parameter.name()
                )));
            }
            C0Type::Bool => {
                arguments.push(CExpression::Value(crate::kernel::bool_value(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::VoidPointer | C0Type::VoidPointerPointer => {
                arguments.push(c_typed_pointer_value(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(input_pointer_variable(scope, index)?),
                            1,
                        ),
                    },
                    parameter.to_kernel_parameter().c_type(),
                ));
            }
            C0Type::FunctionPointer(_) => {
                arguments.push(c_typed_pointer_value(
                    Pointer::symbolic_function(input_pointer_variable(scope, index)?),
                    parameter.c_type().to_kernel_type(),
                ));
            }
            C0Type::Int8Pointer | C0Type::Int8PointerPointer => {
                let c_type = parameter.c_type();
                let kernel_c_type = parameter.to_kernel_parameter().c_type();
                // Struct array parameters are lowered to byte pointers in the
                // kernel, so their symbolic external argument address uses
                // byte-pointer identity. The struct stride is retained only
                // when indexing the parameter and lowering its resource
                // clauses.
                let element_width = parameter.array_element_width().map_or_else(
                    || {
                        c_type
                            .pointee_type()
                            .expect("pointer parameter has a pointee")
                            .to_kernel_type()
                            .byte_width()
                    },
                    |_| 1,
                );
                arguments.push(c_typed_pointer_value(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(input_pointer_variable(scope, index)?),
                            i64::from(element_width),
                        ),
                    },
                    kernel_c_type,
                ));
            }
            C0Type::Int16Pointer
            | C0Type::UInt16Pointer
            | C0Type::Int32Pointer
            | C0Type::CharPointer(_)
            | C0Type::UInt8Pointer
            | C0Type::UInt32Pointer
            | C0Type::Int128Pointer
            | C0Type::Int64Pointer(_)
            | C0Type::UInt128Pointer
            | C0Type::UInt64Pointer(_)
            | C0Type::Int16PointerPointer
            | C0Type::UInt16PointerPointer
            | C0Type::Int32PointerPointer
            | C0Type::CharPointerPointer(_)
            | C0Type::UInt8PointerPointer
            | C0Type::UInt32PointerPointer
            | C0Type::Int128PointerPointer
            | C0Type::Int64PointerPointer(_)
            | C0Type::UInt128PointerPointer
            | C0Type::UInt64PointerPointer(_)
            | C0Type::Float32Pointer
            | C0Type::Float64Pointer
            | C0Type::Float32PointerPointer
            | C0Type::Float64PointerPointer => {
                let c_type = parameter.c_type();
                let kernel_c_type = parameter.to_kernel_parameter().c_type();
                // Struct array parameters are lowered to byte pointers in the
                // kernel, so their symbolic external argument address uses
                // byte-pointer identity. The struct stride is retained only
                // when indexing the parameter and lowering its resource
                // clauses.
                let element_width = parameter.array_element_width().map_or_else(
                    || {
                        c_type
                            .pointee_type()
                            .expect("pointer parameter has a pointee")
                            .to_kernel_type()
                            .byte_width()
                    },
                    |_| 1,
                );
                arguments.push(c_typed_pointer_value(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: scale_int32_offset(
                            Bitvector32Term::Variable(input_pointer_variable(scope, index)?),
                            i64::from(element_width),
                        ),
                    },
                    kernel_c_type,
                ));
            }
            C0Type::Int8 => {
                arguments.push(CExpression::Value(CValue::Int8(Bitvector32Term::Variable(
                    Variable(arguments.len() as u64),
                ))));
            }
            C0Type::Int16 => {
                arguments.push(CExpression::Value(CValue::Int16(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::Int32 => {
                arguments.push(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::Char(crate::languages::c::syntax::PlainChar::Signed) => {
                arguments.push(CExpression::Value(CValue::Int8(Bitvector32Term::Variable(
                    Variable(arguments.len() as u64),
                ))));
            }
            C0Type::Char(crate::languages::c::syntax::PlainChar::Unsigned) | C0Type::UInt8 => {
                arguments.push(CExpression::Value(CValue::UInt8(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::UInt16 => {
                arguments.push(CExpression::Value(CValue::UInt16(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::UInt32 => {
                arguments.push(CExpression::Value(CValue::UInt32(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::Int64(_) => {
                arguments.push(CExpression::Value(CValue::Int64(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::UInt64(_) => {
                arguments.push(CExpression::Value(CValue::UInt64(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::Float32 => {
                arguments.push(CExpression::Value(CValue::Float32(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::Float64 => {
                arguments.push(CExpression::Value(CValue::Float64(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::Int8Array(_) => {
                return Err(ClickError::new(format!(
                    "array parameter `{}` should have lowered to a pointer",
                    parameter.name()
                )));
            }
            C0Type::Int32Array(_)
            | C0Type::CharArray(_, _)
            | C0Type::UInt8Array(_)
            | C0Type::Int16Array(_)
            | C0Type::UInt16Array(_)
            | C0Type::UInt32Array(_)
            | C0Type::Int128Array(_)
            | C0Type::Int64Array(_, _)
            | C0Type::UInt128Array(_)
            | C0Type::UInt64Array(_, _)
            | C0Type::Float32Array(_)
            | C0Type::Float64Array(_) => {
                return Err(ClickError::new(format!(
                    "array parameter `{}` should have lowered to a pointer",
                    parameter.name()
                )));
            }
            C0Type::PointerArray(_, _, _) => {
                return Err(ClickError::new(format!(
                    "array parameter `{}` should have lowered to a pointer",
                    parameter.name()
                )));
            }
        }
    }

    let native_span_inputs = native_span_input_parameters(
        parameters,
        function.resource_requires(),
        composite_definitions,
    );
    let native_model_inputs = native_model_input_parameters(
        parameters,
        function.resource_requires(),
        function.contract_requires(),
    );
    let opaque_copy_inputs = crate::kernel::c_body_opaque_pointer_copy_inputs(function);
    // Direct C copy-only operands retain full value identities without a native
    // input promise. Other C pointer uses keep their existing entry recipe.
    // Explicit native source inputs, nominal C++ record inputs and selected
    // prefix/model requirements retain unresolved semantic identities. A C
    // record type alone leaves an unprofiled input on its legacy path.
    // None of these markers establishes an object; exact requirements below
    // must authenticate every executable native selection.
    for (index, parameter) in parameters.iter().enumerate() {
        if (parameter.is_native_pointer_input()
            || function
                .parameters()
                .get(index)
                .is_some_and(|parameter| parameter.is_native_pointer_input())
            || native_span_inputs.contains(&index)
            || native_model_inputs.contains(&index)
            || opaque_copy_inputs.contains(&index))
            && let CExpression::Value(CValue::Pointer(pointer)) = &mut arguments[index]
        {
            *pointer =
                pointer
                    .clone()
                    .with_designation(crate::kernel::PointerDesignation::Unresolved(
                        input_pointer_variable(scope, index)?,
                    ));
        }
    }

    // Install ordinary function storage before adding symbolic loadable
    // cells. Otherwise a loadable clause can create a block first and leave
    // entry initialization unable to install its stable typed cells.
    let initial = CState::new()
        .with_typed_access_policy(function.contract_interface().typed_access_policy())
        .with_population_creation_tracking();
    let mut state = crate::kernel::initialize_c_function_globals(&initial, function);
    for output in function
        .contract_interface()
        .initialization_output_selectors()
        .ok_or_else(|| {
            ClickError::new(
                "initialization postconditions require fixed entry-bound mutable byte ranges",
            )
        })?
    {
        if output.field().is_some() || output.bytes() == 0 {
            continue;
        }
        let CExpression::Value(CValue::Pointer(pointer)) = &arguments[output.parameter_index()]
        else {
            return Err(ClickError::new(
                "initialization output parameter is not a pointer",
            ));
        };
        state = state.clone().with_memory(
            state
                .memory()
                .clone()
                .with_uninitialized_object(pointer.pointer().clone(), output.bytes()),
        );
    }
    if function.contract_interface().aggregate_return_mode()
        == crate::kernel::CAggregateReturnMode::Construction
    {
        let layout = function
            .contract_interface()
            .return_aggregate_layout()
            .ok_or_else(|| ClickError::new("construction result has no layout"))?
            .clone();
        let destination = Pointer::symbolic(input_pointer_variable(scope, parameters.len())?);
        crate::kernel::register_block_alignment(&destination.block, layout.alignment_bytes());
        let memory = state
            .memory()
            .clone()
            .with_uninitialized_block(destination.block.clone(), layout.size_bytes());
        state = state.with_memory(memory);
        state = state.with_aggregate_return_destination(destination.clone(), layout.clone());
        // Resource preparation evaluates the implicit contract segment before
        // the checked function-entry binder installs its aggregate local.
        state = state.with_local(
            crate::kernel::C_CONTRACT_RESULT_NAME,
            CValue::typed_pointer(destination.clone(), function.return_type()),
        );
        let storage = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            destination,
            0.into(),
            layout.size_bytes().into(),
            1,
        ));
        // Materializing by-value arguments also binds the function's selected
        // return destination. Install its existing implicit byte owner with
        // the raw storage, before that checked binding; requirement lowering
        // below retains the owner rather than manufacturing a second one.
        let resources = state.resources().clone().unchecked_with_fact(storage);
        state = state.with_resource_context(resources);
    }
    if let Some((index, layout)) = function.contract_interface().construction_parameter() {
        parameters
            .get(index)
            .ok_or_else(|| ClickError::new("constructor destination parameter is missing"))?;
        // A symbolic block is an arbitrary input identity, not a fresh local.
        // Record the raw footprint before resource naming can seed typed cells.
        // The constructor can target a subobject, so do not fix its containing
        // allocation's extent. Field liveness comes from the entry contract.
        let destination = Pointer::symbolic(input_pointer_variable(scope, index)?);
        crate::kernel::register_block_alignment(&destination.block, layout.alignment_bytes());
        let pointer =
            crate::kernel::c_construction_contract_input_pointer(function, destination.clone())
                .ok_or_else(|| {
                    ClickError::new("constructor input has no declared object carrier")
                })?;
        arguments[index] = CExpression::Value(CValue::Pointer(pointer));
        let memory = state
            .memory()
            .clone()
            .with_uninitialized_object(destination, layout.size_bytes());
        state = state.with_memory(memory);
    }
    // Native construction requires this selected structural object. Keep that
    // entry requirement separate from raw storage and field permissions; calls
    // must discharge it against the caller's declaration or retained input.
    // Issue native argument domains after destination setup, which replaces
    // the constructor address spelling. Never erase the selected descriptor.
    state = crate::kernel::assume_scalar_object_inputs(
        state,
        function.contract_interface(),
        &mut arguments,
    )
    .map_err(ClickError::new)?;
    state = crate::kernel::c_state_with_construction_contract_input(state, function, &arguments)
        .map_err(ClickError::new)?;
    if parameters
        .iter()
        .any(|parameter| parameter.is_struct_value())
    {
        // A by-value argument is an already-evaluated C value. Materialize its
        // aggregate image using the same typed copy operation as C calls,
        // before resource clauses follow any pointer fields. This image is
        // caller storage; the callee still receives its own fresh copy.
        state = crate::kernel::materialize_symbolic_declaration_parameters(
            &state, function, &arguments,
        )
        .ok_or_else(|| ClickError::new("could not materialize aggregate argument values"))?;
        for (parameter, argument) in parameters.iter().zip(&mut arguments) {
            if parameter.is_struct_value() {
                *argument = c_typed_pointer_value(
                    state
                        .locals()
                        .aggregate_object_pointer(parameter.name())
                        .expect("materialized aggregate argument")
                        .clone(),
                    parameter.to_kernel_parameter().c_type(),
                );
            }
        }
    }
    state = crate::kernel::mark_initialization_output_fields(state, function.contract_interface())
        .ok_or_else(|| {
            ClickError::new("initialization output field requires a defined by-value entry pointer")
        })?;
    let mut loadable_ranges = BTreeMap::new();
    for requirement in requires {
        if let Some((name, bytes)) =
            concrete_loadable_block(requirement, ParameterBinding::new(parameters, &arguments))?
        {
            loadable_ranges.insert(name, bytes);
        }
        if let Requirement::Resource(resource) = requirement {
            for (name, bytes) in concrete_access_resource_blocks(
                resource,
                ParameterBinding::new(parameters, &arguments),
            )? {
                loadable_ranges.insert(name, bytes);
            }
        }
    }

    let memory = memory_with_symbolic_loadable_cells(state.memory().clone(), &loadable_ranges);
    // In particular, a resource such as `pointer[0..1]` must follow the
    // pointer value already present in the entry state, rather than deriving
    // a second pointer from the raw memory-load term for the pointer slot.
    let memory = materialize_symbolic_access_resource_cells(
        memory,
        requires,
        ParameterBinding::new(parameters, &arguments),
        &PureFactContext::new(),
    )?;
    let state = state.with_memory(memory);
    let resources = resource_context_from_requirements(
        requires,
        ParameterBinding::new(parameters, &arguments),
        &state,
    )?;
    let mut state =
        crate::kernel::c_state_with_assumed_mutex_inputs(state.with_resource_context(resources));
    {
        // A standalone helper is proved for an arbitrary population supplied
        // by its caller. Import only the explicitly declared ownership, with
        // no exact total or C creation right; the call site later checks the actual
        // authority and member transfer against its concrete ledger.
        // Index this entry's member inputs by their complete authority scope,
        // not just family: another pool's member is an ordinary frame, not
        // evidence for this pool's population. Include unsupported quantities
        // so they fail checked import instead of becoming authority-only input.
        let mut wildcard_members =
            BTreeMap::<crate::kernel::ResourceDescription, Vec<CResourceFact>>::new();
        for fact in state.resources().facts() {
            let CResourceFact::Own(CResource::Composite { name, arguments }, _) = fact else {
                continue;
            };
            if arguments.len() < 2 {
                continue;
            }
            let scope = crate::kernel::ResourceDescription::new(
                name.clone(),
                vec![arguments[0].clone()].into(),
                ResourceFieldSchema::new(vec![]).expect("empty resource schema"),
            )
            .with_population_arity(arguments.len());
            if let Ok(scope) = scope {
                wildcard_members
                    .entry(scope)
                    .or_default()
                    .push(fact.clone());
            }
        }
        let authorities = state
            .resources()
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), CResource::PopulationAuthority(_)))
            .cloned()
            .collect::<Vec<_>>();
        for authority in authorities {
            let CResource::PopulationAuthority(description) = authority.resource() else {
                unreachable!();
            };
            if description.population_arity().is_some() {
                let Some(members) = wildcard_members.get(description) else {
                    state = state
                        .import_opaque_wildcard_authority(&authority)
                        .map_err(ClickError::new)?;
                    continue;
                };
                if members.len() != 1 {
                    return Err(ClickError::new(
                        "wildcard helper entry currently supports one concrete member",
                    ));
                }
                state = state
                    .import_opaque_wildcard_population(&authority, &members[0])
                    .map_err(ClickError::new)?;
                continue;
            }
            state = state
                .import_opaque_population_inputs(&authority)
                .map_err(ClickError::new)?;
        }
        let controls = state
            .resources()
            .facts()
            .iter()
            .filter_map(|fact| {
                let CResource::Composite { name, .. } = fact.resource() else {
                    return None;
                };
                let definition = composite_definitions
                    .iter()
                    .find(|definition| definition.name() == name)?;
                definition
                    .contains()
                    .iter()
                    .any(|child| matches!(child.term(), CResourceTerm::PopulationAuthority { .. }))
                    .then(|| (fact.clone(), definition))
            })
            .collect::<Vec<_>>();
        for (control, definition) in controls {
            state = state
                .import_opaque_control_wrapper(
                    &control,
                    definition,
                    &PureFactContext::new(),
                    &wildcard_members,
                )
                .map_err(ClickError::new)?;
        }
    }
    INPUT_POINTER_PLACES.with(|places| {
        let mut places = places.borrow_mut();
        for (index, argument) in arguments.iter().take(parameters.len()).enumerate() {
            if let CExpression::Value(CValue::Pointer(pointer)) = argument
                && let Some(variable) = input_pointer_identity(pointer)
            {
                places.insert(variable, (scope, index, pointer.clone()));
            }
        }
    });
    let state = crate::kernel::c_state_with_assumed_native_record_inputs(
        &state,
        function,
        &arguments,
        composite_definitions,
        &PureFactContext::new(),
    )
    .map_err(ClickError::new)?;
    let (state, arguments) =
        crate::kernel::c_independent_function_input_state(&state, function, &arguments)
            .unwrap_or((state, arguments));
    Ok((state, arguments))
}

/// A contract may transfer memory reached through a copied pointer value,
/// but cannot borrow or transfer the callee's private parameter object.
fn reject_aggregate_parameter_storage_resource(
    resource: &ResourceClause,
    parameters: &BTreeSet<&str>,
) -> Result<(), ClickError> {
    fn root(expression: &CExpression) -> Option<&str> {
        match expression {
            CExpression::Variable(name) => Some(name),
            CExpression::PointerOffsetBytes { pointer, .. }
            | CExpression::AddressOf(pointer)
            | CExpression::CheckedObjectAddress(pointer) => root(pointer),
            CExpression::Add(pointer, _) | CExpression::Subtract(pointer, _) => root(pointer),
            CExpression::TypedLoad {
                pointer,
                value_type:
                    CType::Int32Array(_)
                    | CType::UInt32Array(_)
                    | CType::UInt8Array(_)
                    | CType::Int128Array(_)
                    | CType::Int64Array(_)
                    | CType::UInt128Array(_)
                    | CType::UInt64Array(_),
                ..
            } => root(pointer),
            _ => None,
        }
    }
    let segments = match resource {
        ResourceClause::Named { resource, .. } => {
            return reject_aggregate_parameter_storage_resource(resource, parameters);
        }
        ResourceClause::OwnMemory(segment) | ResourceClause::ViewMemory(segment) => {
            std::slice::from_ref(segment)
        }
        ResourceClause::MemoryAggregate { segments, .. } => segments,
        _ => return Ok(()),
    };
    for segment in segments {
        if let Some(parameter) = root(&segment.base).filter(|name| parameters.contains(name)) {
            return Err(ClickError::new(format!(
                "by-value parameter `{parameter}` supplies its field values directly; its private storage cannot be an input resource"
            )));
        }
    }
    Ok(())
}

/// Retry input naming after the kernel has checked the entry clause partition.
/// The names retain the existing snapshot values; separation permits naming
/// initialized inputs, and neither the names nor their DAG edges mark writes.
pub(in crate::surface) fn materialize_checked_entry_input_cells(
    state: CState,
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    assumptions: &PureFactContext,
) -> Result<CState, ClickError> {
    if !state.memory().has_uninitialized_object_footprints() {
        return Ok(state);
    }
    let mut loadable_ranges = BTreeMap::new();
    for requirement in requires {
        if let Some((name, range)) =
            concrete_loadable_block(requirement, ParameterBinding::new(parameters, arguments))?
        {
            loadable_ranges.insert(name, range);
        }
        if let Requirement::Resource(resource) = requirement {
            for (name, range) in concrete_access_resource_blocks(
                resource,
                ParameterBinding::new(parameters, arguments),
            )? {
                loadable_ranges.insert(name, range);
            }
        }
    }
    let memory = memory_with_symbolic_loadable_cells_under(
        state.memory().clone(),
        &loadable_ranges,
        assumptions,
    );
    let memory = materialize_symbolic_access_resource_cells(
        memory,
        requires,
        ParameterBinding::new(parameters, arguments),
        assumptions,
    )?;
    Ok(state.with_memory(memory))
}

pub(in crate::surface) fn memory_with_symbolic_loadable_cells(
    memory: CMemory,
    loadable_ranges: &BTreeMap<String, ConcreteMemoryRangeSeed>,
) -> CMemory {
    memory_with_symbolic_loadable_cells_under(memory, loadable_ranges, &PureFactContext::new())
}

fn memory_with_symbolic_loadable_cells_under(
    mut memory: CMemory,
    loadable_ranges: &BTreeMap<String, ConcreteMemoryRangeSeed>,
    assumptions: &PureFactContext,
) -> CMemory {
    let base_memory = memory.clone();
    for range in loadable_ranges.values() {
        if let Some(layout) = &range.struct_layout {
            let mut offset: u32 = 0;
            while offset
                .checked_add(range.element_width)
                .is_some_and(|end| end <= range.bytes)
            {
                let element_pointer = offset_pointer_by_elements(
                    range.base.clone(),
                    Bitvector32Term::Constant(offset / range.element_width),
                    range.element_width,
                );
                for field in layout.fields().values() {
                    memory = visit_struct_field_cells(
                        field,
                        &element_pointer,
                        memory,
                        |memory, pointer, element_type| {
                            if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
                                return memory;
                            }
                            let value =
                                symbolic_value_for_element(&base_memory, &pointer, element_type);
                            memory.materialize_named_cell_under(pointer, value, assumptions)
                        },
                    );
                }
                offset += range.element_width;
            }
            continue;
        }

        let Some(element_type) = range.element_type else {
            continue;
        };
        // Name initialized input elements as one run, preserving existing
        // cells and leaving raw output footprints unwritten. Naming these
        // observations is not a C store.
        // Aggregate resource coordinates may use four-byte units even for
        // an eight-byte pointer field. A pointer observation names one whole
        // pointer cell, never two overlapping pointer cells four bytes apart.
        let cell_width = if element_type.is_pointer() {
            element_type.byte_width()
        } else {
            range.element_width
        };
        let count = range
            .observation_count
            .unwrap_or_else(|| range.bytes.checked_div(cell_width).unwrap_or(0));
        if count
            .checked_mul(cell_width)
            .is_none_or(|bytes| bytes > range.bytes)
        {
            continue;
        }
        memory = memory.with_proof_entry_cells_under(
            range.base.clone(),
            cell_width,
            element_type,
            0,
            count,
            crate::kernel::intern_c_memory(base_memory.clone()),
            assumptions,
        );
    }
    memory
}

pub(in crate::surface) fn visit_struct_field_cells(
    field: &syntax::C0StructField,
    element_pointer: &Pointer,
    mut memory: CMemory,
    mut visit: impl FnMut(CMemory, Pointer, CType) -> CMemory,
) -> CMemory {
    let field_pointer = element_pointer.offset_by_bytes(field.offset_bytes());
    match field.c_type().to_kernel_type() {
        array_type @ (CType::Int32Array(length)
        | CType::Int128Array(length)
        | CType::Int64Array(length)
        | CType::UInt128Array(length)
        | CType::UInt64Array(length)) => {
            let element_type = match array_type {
                CType::Int64Array(_) => CType::Int64,
                CType::Int128Array(_) => CType::Int128,
                CType::UInt64Array(_) => CType::UInt64,
                CType::UInt128Array(_) => CType::UInt128,
                _ => CType::Int32,
            };
            for index in 0..length {
                memory = visit(
                    memory,
                    field_pointer.offset_by_bytes(
                        index.checked_mul(element_type.byte_width()).expect(
                            "validated integer array field stride must fit in the pointer offset",
                        ),
                    ),
                    element_type,
                );
            }
        }
        CType::UInt8Array(length) => {
            for index in 0..length {
                memory = visit(memory, field_pointer.offset_by_bytes(index), CType::UInt8);
            }
        }
        element_type => memory = visit(memory, field_pointer, element_type),
    }
    memory
}

fn materialize_symbolic_access_resource_cells(
    mut memory: CMemory,
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    assumptions: &PureFactContext,
) -> Result<CMemory, ClickError> {
    for requirement in requires {
        let Requirement::Resource(resource) = requirement else {
            continue;
        };
        match resource {
            ResourceClause::Conditional { .. } => {
                return Err(ClickError::new(
                    "conditional resource assertions are supported only in loop contracts",
                ));
            }
            ResourceClause::Named { .. } => {}
            ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
                memory = materialize_access_segment_cells(
                    memory,
                    segment,
                    parameter_binding,
                    assumptions,
                )?;
            }
            ResourceClause::MemoryAggregate { segments, .. } => {
                for segment in segments {
                    memory = materialize_access_segment_cells(
                        memory,
                        segment,
                        parameter_binding,
                        assumptions,
                    )?;
                }
            }
            ResourceClause::Declared { .. }
            | ResourceClause::Quantified { .. }
            | ResourceClause::Iterated(_) => {}
        }
    }
    Ok(memory)
}

/// Refuses a resource clause whose segment is addressed through a cell the
/// contract does not hold. `views old->left->augmented` reads the parameter
/// cell `old->left` to name its segment, so the entry state must justify
/// that read exactly as it justifies a `requires old->left != 0` reading
/// the same cell. Without this check a clause could address memory through
/// an arbitrary parameter link while a requirement naming the same link was
/// refused, which is how adding a guard to a contract used to make it fail.
///
/// The entry state already carries what every clause of the section supplies,
/// including the cells a folded composite holds, so this decides the whole
/// clause set at once and clause order does not enter into it. That is the
/// same question the kernel's section evaluator answers when it cannot read a
/// clause's base at all, so a refusal here identifies the clause -- or the
/// clauses that stall together -- in the kernel's wording
/// (`resource_clause_position_note`, `resource_clause_stall_note`) rather
/// than inventing a second one for one defect.
pub(in crate::surface) fn check_resource_segment_base_loadability(
    function_block: &FunctionBlock,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    assumptions: &PureFactContext,
) -> Result<(), ClickError> {
    let clauses = function_block
        .requires()
        .iter()
        .filter_map(|requirement| match requirement {
            Requirement::Resource(resource) => Some(resource),
            _ => None,
        })
        .collect::<Vec<_>>();
    // Positions are the clauses the author wrote: a flattened aggregate's
    // members share one, the same numbering the kernel evaluator carries.
    let positions = function_block.resource_requirement_positions();
    let clause_count = positions.first().map_or(clauses.len(), |(_, count)| *count);
    let mut stalled = Vec::new();
    for (flattened, resource) in clauses.iter().enumerate() {
        let position = positions
            .get(flattened)
            .map_or(flattened, |(position, _)| *position);
        if stalled
            .iter()
            .any(|(seen, _, _): &(usize, String, String)| *seen == position)
        {
            continue;
        }
        let segments: &[ContractSegment] = match resource {
            ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
                std::slice::from_ref(segment)
            }
            ResourceClause::MemoryAggregate { segments, .. } => segments,
            ResourceClause::Named { .. }
            | ResourceClause::Conditional { .. }
            | ResourceClause::Declared { .. }
            | ResourceClause::Quantified { .. }
            | ResourceClause::Iterated(_) => continue,
        };
        for segment in segments {
            let Err(message) = check_segment_base_loadability(
                &segment.base,
                parameter_binding,
                state,
                assumptions,
            ) else {
                continue;
            };
            stalled.push((
                position,
                crate::surface::diagnostics::describe_contract_segment(segment),
                message,
            ));
            break;
        }
    }
    let Some((position, segment, message)) = stalled.first() else {
        return Ok(());
    };
    // One unaddressed clause is that clause's own problem. Two or more stall
    // together: no order of them supplies what they read, so name a second
    // position instead of sending the user to whichever was written first.
    let note = match stalled.get(1) {
        Some((other, _, _)) => crate::kernel::resource_clause_stall_note(*position, *other),
        None => crate::kernel::resource_clause_position_note(*position, clause_count),
    };
    Err(ClickError::new(format!(
        "could not address resource clause `{segment}` ({note}): {message}"
    )))
}

/// Checks the loads a segment base performs, innermost first, so a chain
/// such as `old->left->augmented` reports the first cell the contract does
/// not hold rather than the last.
fn check_segment_base_loadability(
    base: &CExpression,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let CExpression::TypedLoad {
        pointer,
        value_type,
        ..
    } = base
    else {
        return Ok(());
    };
    check_segment_base_loadability(pointer, parameter_binding, state, assumptions)?;
    // An inline array field is addressed by a typed load of the array
    // itself. That reads no cell: the elements are the struct's own storage,
    // and the segment covers them directly.
    if matches!(
        value_type,
        CType::Int32Array(_)
            | CType::UInt8Array(_)
            | CType::Int8Array(_)
            | CType::Int16Array(_)
            | CType::UInt16Array(_)
            | CType::UInt32Array(_)
            | CType::Int128Array(_)
            | CType::Int64Array(_)
            | CType::UInt128Array(_)
            | CType::UInt64Array(_)
            | CType::Float32Array(_)
            | CType::Float64Array(_)
    ) {
        return Ok(());
    }
    let Ok(values) = parameter_values(parameter_binding) else {
        return Ok(());
    };
    let array_refs =
        array_refs_for_parameters(parameter_binding.parameters, &values, state.memory());
    // The address of the cell, not its content: a base whose address this
    // entry cannot evaluate is reported by the clause's own lowering.
    let Ok(CValue::Pointer(cell)) = crate::surface::proof::evaluate_c_fragment_through_kernel(
        pointer,
        assumptions,
        ContractEnvironment::new(&values, &array_refs),
        state,
        None,
    ) else {
        return Ok(());
    };
    let obligation = Proposition::CMemoryLoadable {
        memory: state.memory().clone(),
        base: cell.into_pointer(),
        bytes: Bitvector32Term::Constant(value_type.byte_width()),
        wide: false,
    };
    if crate::kernel::c_state_justifies_loadability_obligation(state, &obligation, assumptions) {
        return Ok(());
    }
    Err(format!(
        "{}{}",
        crate::surface::diagnostics::describe_missing_pure_fact(
            &obligation,
            &[],
            &[],
            parameter_binding,
            &[],
        ),
        folded_matched_instance_note(state, parameter_binding, assumptions)
    ))
}

/// Says why the cells a folded matched instance owns are unreadable here.
///
/// A resource whose body is `match model { ... }` exposes nothing until one
/// arm is selected, so a requirement or a resource clause that reads through
/// it fails for a loadability that names no resource at all. Name the instance
/// and the evidence that would select an arm, rather than leaving the reader
/// with an unexplained missing fact.
///
/// The note costs the contract's own resource clauses, never the project: it
/// reads the clause set this entry state already holds.
pub(in crate::surface) fn folded_matched_instance_note(
    state: &CState,
    parameter_binding: ParameterBinding<'_>,
    assumptions: &PureFactContext,
) -> String {
    // Only an instance whose arm nothing selects explains a missing cell. One
    // whose arm is selected already published its cells, so naming it here
    // would send the reader to a clause that is fine.
    fn undecided<'a>(
        instance: &'a crate::kernel::ResourceInstance,
        assumptions: &PureFactContext,
    ) -> Option<(&'a str, Vec<String>)> {
        instance
            .schema()
            .fields()
            .iter()
            .zip(instance.fields())
            .filter_map(|((name, _), value)| match value {
                AlgebraicValue::Algebraic(model) => Some((name.as_str(), model)),
                _ => None,
            })
            .find_map(|(name, model)| {
                let possible = match crate::kernel::decide_resource_model_arm(model, assumptions) {
                    crate::kernel::ResourceModelArmDecision::Selected(_) => return None,
                    crate::kernel::ResourceModelArmDecision::Possible(possible) => possible,
                    crate::kernel::ResourceModelArmDecision::Open => Vec::new(),
                };
                let possible = possible
                    .iter()
                    .map(|variant| format!("{}::{variant}", model.algebraic_type.name))
                    .collect::<Vec<_>>();
                Some((name, possible))
            })
    }
    let Some((instance, field, possible)) = state
        .resources()
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            CResource::Instance(instance) => Some(instance),
            _ => None,
        })
        .find_map(|instance| {
            undecided(instance, assumptions).map(|(field, possible)| (instance, field, possible))
        })
    else {
        return String::new();
    };
    let declared = crate::surface::diagnostics::format_declared_resource(
        instance.name(),
        instance.arguments(),
        parameter_binding,
    );
    // The premises may have refuted some arms without deciding one. Then the
    // cells every surviving arm owns are readable and this cell is not one of
    // them, so name the arms the reader has to reconcile rather than repeating
    // that no arm is selected.
    if possible.len() > 1 {
        return format!(
            "\n  `{declared}` stays folded: the requirements leave the arms {} possible, and this \
             cell is not owned by every one of them, so it is not readable here",
            possible
                .iter()
                .map(|variant| format!("`{variant}`"))
                .collect::<Vec<_>>()
                .join(" and ")
        );
    }
    format!(
        "\n  `{declared}` stays folded: no requirement of this contract selects one arm of its \
         `{field}` field, so the cells its arms own are not readable here",
    )
}

fn materialize_access_segment_cells(
    mut memory: CMemory,
    segment: &ContractSegment,
    parameter_binding: ParameterBinding<'_>,
    assumptions: &PureFactContext,
) -> Result<CMemory, ClickError> {
    let state = CState::new().with_memory(memory.clone());
    let source_segment = segment;
    let Ok(segment) = evaluate_requirement_segment(parameter_binding, &state, source_segment)
    else {
        return Ok(memory);
    };
    let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (&segment.start, &segment.end)
    else {
        return Ok(memory);
    };
    if end < start {
        return Err(ClickError::new(format!(
            "resource segment has an end before its start: {start}..{end}"
        )));
    }

    // A complete object (`*p`) is one struct at the base: its cells
    // take the field types of the layout, so a `uint64` or pointer field
    // reads back with its own type rather than as int32 words.
    if let Some(layout) = object_segment_layout(parameter_binding.parameters, source_segment) {
        let base_memory = memory.clone();
        for field in layout.fields().values() {
            memory = visit_struct_field_cells(
                field,
                &segment.base,
                memory,
                |memory, pointer, element_type| {
                    if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
                        return memory;
                    }
                    let load = crate::kernel::canonical_form_of_typed_load(
                        crate::kernel::intern_c_memory(base_memory.clone()),
                        pointer.clone(),
                        element_type,
                    )
                    .expect("a struct field has a scalar load type");
                    let value = symbolic_value_from_load(&pointer, element_type, load);
                    memory.materialize_named_cell_under(pointer, value, assumptions)
                },
            );
        }
        return Ok(memory);
    }
    if let Some(layout) =
        contract_segment_struct_layout(parameter_binding.parameters, source_segment)
    {
        let base_memory = memory.clone();
        for index in *start..*end {
            let element_pointer = offset_pointer_by_elements(
                segment.base.clone(),
                Bitvector32Term::Constant(index),
                layout.size_bytes(),
            );
            for field in layout.fields().values() {
                memory = visit_struct_field_cells(
                    field,
                    &element_pointer,
                    memory,
                    |memory, pointer, element_type| {
                        if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
                            return memory;
                        }
                        let load = crate::kernel::canonical_form_of_typed_load(
                            crate::kernel::intern_c_memory(base_memory.clone()),
                            pointer.clone(),
                            element_type,
                        )
                        .expect("a struct field has a scalar load type");
                        let value = symbolic_value_from_load(&pointer, element_type, load);
                        memory.materialize_named_cell_under(pointer, value, assumptions)
                    },
                );
            }
        }
        return Ok(memory);
    }

    let element_type = contract_segment_element_type(parameter_binding.parameters, &segment.source);
    let element_width =
        contract_segment_element_width(parameter_binding.parameters, &segment.source);
    let source = crate::kernel::intern_c_memory(memory.clone());
    // Coordinate units belong to the resource. The cached observation has
    // the selected declaration's full physical width, including pointer pairs.
    let cell_width = element_type.byte_width();
    let first_byte = start
        .checked_mul(element_width)
        .ok_or_else(|| ClickError::new("resource observation offset overflows"))?;
    let end_byte = end
        .checked_mul(element_width)
        .ok_or_else(|| ClickError::new("resource observation endpoint overflows"))?;
    if !first_byte.is_multiple_of(cell_width) {
        return Ok(memory);
    }
    let first = first_byte / cell_width;
    let end = if let Some(count) = declared_segment_observation_count(source_segment) {
        let last_byte = first_byte
            .checked_add(
                count
                    .checked_mul(cell_width)
                    .ok_or_else(|| ClickError::new("declared observation extent overflows"))?,
            )
            .ok_or_else(|| ClickError::new("declared observation extent overflows"))?;
        if last_byte > end_byte {
            return Ok(memory);
        }
        first
            .checked_add(count)
            .ok_or_else(|| ClickError::new("declared observation count overflows"))?
    } else {
        if !end_byte.is_multiple_of(cell_width) {
            return Ok(memory);
        }
        end_byte / cell_width
    };
    Ok(memory.with_proof_entry_cells_under(
        segment.base.clone(),
        cell_width,
        element_type,
        first,
        end,
        source,
        assumptions,
    ))
}

pub(in crate::surface) fn requirement_propositions(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Vec<Proposition>, ClickError> {
    requirement_propositions_with_assumptions(
        requires,
        parameter_binding,
        state,
        spec_definitions,
        &PureFactContext::new(),
    )
}

pub(in crate::surface) fn requirement_propositions_with_assumptions(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    spec_definitions: SpecDefinitions<'_>,
    initial_assumptions: &PureFactContext,
) -> Result<Vec<Proposition>, ClickError> {
    Ok(requirement_propositions_with_sources_and_assumptions(
        requires,
        parameter_binding,
        state,
        spec_definitions,
        initial_assumptions,
    )?
    .into_iter()
    .map(|fact| fact.proposition)
    .collect())
}

/// One fact emitted while lowering the function's written requirement list.
///
/// This is construction-time provenance, before later entry-context passes
/// add resource observations or definedness consequences.  Keeping the outer
/// source ordinal here avoids trying to reconstruct it from the final fact
/// vector, whose ordering deliberately differs from requirement order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct LoweredRequirementFact {
    pub(in crate::surface) source_ordinal: usize,
    pub(in crate::surface) role: LoweredRequirementFactRole,
    pub(in crate::surface) proposition: Proposition,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::surface) enum LoweredRequirementFactRole {
    Principal,
    Guard(usize),
}

pub(in crate::surface) fn requirement_propositions_with_sources_and_assumptions(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    spec_definitions: SpecDefinitions<'_>,
    initial_assumptions: &PureFactContext,
) -> Result<Vec<LoweredRequirementFact>, ClickError> {
    // A proposition requirement may contain a memory read whose range is
    // justified by another requirement, such as `1 <= n` before
    // `a[0] == 7` under `views a[0..n]`. Lower requirements independently
    // used to make this valid dependency invisible. Retry clauses that need
    // more facts after successfully lowered clauses have contributed their
    // propositions to the local assumption context. Keeping the result in
    // source order preserves the contract-to-kernel mapping.
    let mut lowered = (0..requires.len())
        .map(|_| None)
        .collect::<Vec<Option<Vec<Proposition>>>>();
    let mut errors = (0..requires.len())
        .map(|_| None)
        .collect::<Vec<Option<ClickError>>>();
    let mut pending = (0..requires.len()).collect::<Vec<_>>();
    let mut assumptions = initial_assumptions.clone();

    // Requirements may be written in either order, so use one retry pass
    // after the first pass has published the facts it could lower. A bounded
    // retry keeps setup work linear in the explicit requirement list rather
    // than turning a long dependency chain into repeated whole-list scans.
    for _ in 0..2 {
        if pending.is_empty() {
            break;
        }
        let mut next_pending = Vec::new();
        let mut made_progress = false;
        for index in std::mem::take(&mut pending) {
            let requirement = &requires[index];
            let result = match requirement {
                Requirement::LoadableSegment { .. } => loadable_requirement_props(
                    requirement,
                    parameter_binding,
                    state.memory(),
                    &assumptions,
                )
                .map(Some),
                Requirement::Proposition(proposition) => {
                    requirement_proposition_and_facts_with_assumptions(
                        parameter_binding,
                        state,
                        proposition,
                        spec_definitions,
                        &assumptions,
                    )
                    .map(|(proposition, facts)| {
                        Some(std::iter::once(proposition).chain(facts).collect())
                    })
                }
                Requirement::Resource(resource) => resource_clause_loadable_props_at_state(
                    resource,
                    parameter_binding,
                    state,
                    &assumptions,
                ),
            };
            let result = match result {
                Ok(Some(propositions)) => Ok(propositions),
                Ok(None) => continue,
                Err(error) => Err(error),
            };
            match result {
                Ok(propositions) => {
                    for proposition in &propositions {
                        assumptions = assumptions.assume_proposition(proposition.clone());
                    }
                    lowered[index] = Some(propositions);
                    made_progress = true;
                }
                Err(error) => {
                    errors[index] = Some(error);
                    next_pending.push(index);
                }
            }
        }
        if !made_progress {
            if next_pending.is_empty() {
                break;
            }
            pending = next_pending;
            break;
        }
        pending = next_pending;
    }

    if let Some(index) = pending.first() {
        return Err(errors[*index]
            .take()
            .expect("pending requirement always has a lowering error"));
    }

    let mut facts = Vec::new();
    let mut guards = Vec::new();
    for (source_ordinal, propositions) in lowered.into_iter().enumerate() {
        let Some(propositions) = propositions else {
            continue;
        };
        let mut propositions = propositions.into_iter();
        if let Some(fact) = propositions.next() {
            facts.push(LoweredRequirementFact {
                source_ordinal,
                role: LoweredRequirementFactRole::Principal,
                proposition: fact,
            });
        }
        guards.extend(
            propositions
                .enumerate()
                .map(|(guard_ordinal, proposition)| LoweredRequirementFact {
                    source_ordinal,
                    role: LoweredRequirementFactRole::Guard(guard_ordinal),
                    proposition,
                }),
        );
    }
    facts.extend(guards);
    Ok(facts)
}

/// Checked definedness facts implicit in accepting arithmetic requirements.
///
/// Evaluating a C comparison containing partial arithmetic first establishes
/// that arithmetic's evaluator guards. Record those guards explicitly so a
/// later call certificate can name the exact fact it consumed instead of
/// asking a simple statement step to repeat arithmetic reasoning.
pub(in crate::surface) fn requirement_definedness_surfaces(
    requires: &[Requirement],
) -> Vec<ClickProposition> {
    fn contains_partial_arithmetic(expression: &ContractExpression) -> bool {
        match expression {
            ContractExpression::Add(_, _)
            | ContractExpression::Subtract(_, _)
            | ContractExpression::Multiply(_, _)
            | ContractExpression::Divide(_, _)
            | ContractExpression::Remainder(_, _)
            | ContractExpression::ShiftLeft(_, _)
            | ContractExpression::ShiftRight(_, _) => true,
            ContractExpression::BitwiseAnd(left, right)
            | ContractExpression::BitwiseOr(left, right)
            | ContractExpression::BitwiseXor(left, right) => {
                contains_partial_arithmetic(left) || contains_partial_arithmetic(right)
            }
            ContractExpression::BitwiseNot(body) => contains_partial_arithmetic(body),
            _ => false,
        }
    }

    fn collect<'a>(
        proposition: &'a ClickProposition,
        expressions: &mut Vec<&'a ContractExpression>,
    ) {
        match proposition {
            ClickProposition::Comparison { left, right, .. } => {
                if contains_partial_arithmetic(left) {
                    expressions.push(left);
                }
                if contains_partial_arithmetic(right) {
                    expressions.push(right);
                }
            }
            ClickProposition::FloatClassification { expression, .. } => {
                if contains_partial_arithmetic(expression) {
                    expressions.push(expression);
                }
            }
            ClickProposition::ValidPlace {
                expression, range, ..
            } => {
                expressions.push(expression);
                if let Some((start, end)) = range {
                    expressions.extend([start, end]);
                }
            }
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                collect(left, expressions);
                collect(right, expressions);
            }
            ClickProposition::Not(body) => collect(body, expressions),
            // Bound-variable definedness must remain under its quantifier.
            ClickProposition::ForAll { .. }
            | ClickProposition::Exists { .. }
            | ClickProposition::RangeAll { .. }
            | ClickProposition::RangeAny { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Initialized { .. }
            | ClickProposition::Loadable { .. }
            | ClickProposition::Defined { .. }
            | ClickProposition::At { .. }
            | ClickProposition::PredicateCall { .. } => {}
        }
    }

    let mut result = Vec::new();
    for requirement in requires {
        let Requirement::Proposition(proposition) = requirement else {
            continue;
        };
        let mut expressions = Vec::new();
        collect(proposition, &mut expressions);
        for expression in expressions {
            if contract_expression_to_c_fragment(expression).is_none() {
                continue;
            }
            let surface = ClickProposition::Defined {
                expression: expression.clone(),
            };
            if !result.contains(&surface) {
                result.push(surface);
            }
        }
    }
    result
}

pub(in crate::surface) fn requirement_definedness_propositions(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Vec<(ClickProposition, Proposition)>, ClickError> {
    let mut result = Vec::new();
    for surface in requirement_definedness_surfaces(requires) {
        let kernel =
            requirement_proposition_prop(parameter_binding, state, &surface, spec_definitions)?;
        if matches!(normalize_proposition(&kernel), SimpProposition::True)
            || result
                .iter()
                .any(|(_, fact): &(ClickProposition, Proposition)| fact == &kernel)
        {
            continue;
        }
        result.push((surface, kernel));
    }
    Ok(result)
}

pub(in crate::surface) fn resource_context_from_requirements(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
) -> Result<ResourceContext, ClickError> {
    let mut context = state.resources().clone();
    // One section-local state, moved forward after each owning requirement.
    // Later references can select earlier binders without cloning the state
    // for every clause or introducing ownership beyond these requirements.
    let mut lowering_state = state.clone();
    for requirement in requires {
        if let Requirement::Resource(resource) = requirement {
            // This lowering path has no proposition assumptions yet. It builds
            // a provisional context; execution paths use checked composition
            // once assumptions are available.  Resource arguments may contain
            // loads whose authority is supplied by another clause, so keep
            // those arguments symbolic here.  The entry context is checked by
            // the kernel section evaluator once all pure requirements and
            // clause supplies are available.
            context = context.unchecked_with_facts(lower_resource_clause_facts_at_state_for_entry(
                resource,
                parameter_binding,
                &lowering_state,
            )?);
            lowering_state = lowering_state.with_resource_context(context.clone());
        }
    }
    Ok(context)
}

#[cfg(test)]
pub(in crate::surface) fn lower_resource_clause(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    memory: &CMemory,
) -> Result<CResourceFact, ClickError> {
    if matches!(resource, ResourceClause::MemoryAggregate { .. }) {
        let mut facts = lower_resource_clause_facts(resource, parameter_binding, memory)?;
        if facts.len() != 1 {
            return Err(ClickError::new(format!(
                "resource clause expands to {} typed memory facts where one fact is required",
                facts.len()
            )));
        }
        return Ok(facts.pop().expect("resource clause fact count was checked"));
    }
    let values =
        parameter_values(parameter_binding).map_err(|error| ClickError::new(error.message))?;
    let state = CState::new().with_memory(memory.clone());
    lower_resource_clause_with_values(
        resource,
        parameter_binding.parameters,
        &values,
        &state,
        None,
    )
}

#[cfg(test)]
pub(in crate::surface) fn lower_resource_clause_facts(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    memory: &CMemory,
) -> Result<Vec<CResourceFact>, ClickError> {
    let values =
        parameter_values(parameter_binding).map_err(|error| ClickError::new(error.message))?;
    let state = CState::new().with_memory(memory.clone());
    lower_resource_clause_facts_with_values(
        resource,
        parameter_binding.parameters,
        &values,
        &state,
        None,
    )
}

pub(in crate::surface) fn lower_resource_clause_at_state(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
) -> Result<CResourceFact, ClickError> {
    if matches!(resource, ResourceClause::MemoryAggregate { .. }) {
        let mut facts = lower_resource_clause_facts_at_state(resource, parameter_binding, state)?;
        if facts.len() != 1 {
            return Err(ClickError::new(format!(
                "resource clause expands to {} typed memory facts where one fact is required",
                facts.len()
            )));
        }
        return Ok(facts.pop().expect("resource clause fact count was checked"));
    }
    let values =
        parameter_values(parameter_binding).map_err(|error| ClickError::new(error.message))?;
    lower_resource_clause_with_values(resource, parameter_binding.parameters, &values, state, None)
}

pub(in crate::surface) fn lower_resource_clause_facts_at_state(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
) -> Result<Vec<CResourceFact>, ClickError> {
    let values =
        parameter_values(parameter_binding).map_err(|error| ClickError::new(error.message))?;
    lower_resource_clause_facts_with_values(
        resource,
        parameter_binding.parameters,
        &values,
        state,
        None,
    )
}

fn lower_resource_clause_facts_at_state_for_entry(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
) -> Result<Vec<CResourceFact>, ClickError> {
    let values =
        parameter_values(parameter_binding).map_err(|error| ClickError::new(error.message))?;
    lower_resource_clause_facts_with_values_mode(
        resource,
        parameter_binding.parameters,
        &values,
        state,
        None,
        true,
    )
}

pub(in crate::surface) fn lower_resource_clause_at_state_with_result(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    result: &CValue,
) -> Result<CResourceFact, ClickError> {
    lower_resource_clause_at_state_with_assumptions(
        resource,
        parameter_binding,
        state,
        Some(result),
        &PureFactContext::new(),
    )
}

/// Lowers a live proof operation's resource clause under its checked context.
/// Retain the persistent assumption handle, including its trusted equality
/// graph; do not reconstruct facts or publish ambient resources at this query.
pub(in crate::surface) fn lower_resource_clause_at_state_with_assumptions(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
) -> Result<CResourceFact, ClickError> {
    let values =
        parameter_values(parameter_binding).map_err(|error| ClickError::new(error.message))?;
    if matches!(resource, ResourceClause::MemoryAggregate { .. }) {
        let mut facts = lower_resource_clause_facts_with_values_mode_at_entry(
            resource,
            parameter_binding.parameters,
            &values,
            state,
            state,
            result,
            false,
            assumptions,
        )?;
        if facts.len() != 1 {
            return Err(ClickError::new(format!(
                "resource clause expands to {} typed memory facts where one fact is required",
                facts.len()
            )));
        }
        return Ok(facts.pop().expect("resource clause fact count was checked"));
    }
    lower_resource_clause_with_values_mode_at_entry(
        resource,
        parameter_binding.parameters,
        &values,
        state,
        state,
        result,
        false,
        assumptions,
    )
}

/// Lowers a proof tactic's resource clause with every C name it mentions read
/// in the state the proof has reached.
///
/// A contract clause speaks about parameters, so its names are the entry
/// argument values and `lower_resource_clause_at_state` is right for it. A
/// proof `fold` names the cursor the execution is standing on: inside a loop
/// body that has reassigned `root`, `fold(ctx_at(root->left), ...)` is the
/// frame of the current node, not of the node the function was called with.
/// The fold's own field values are already read this way
/// ([`contract_environment_at_state`]), so lowering its arguments at entry
/// split one tactic across two states and built the instance at an address
/// its fields did not describe.
pub(in crate::surface) fn lower_resource_clause_at_current_locals(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CResourceFact, ClickError> {
    let values =
        parameter_values(parameter_binding).map_err(|error| ClickError::new(error.message))?;
    let array_refs =
        array_refs_for_parameters(parameter_binding.parameters, &values, state.memory());
    let (values, _) = contract_environment_at_state(&values, &array_refs, state);
    lower_resource_clause_with_values(
        resource,
        parameter_binding.parameters,
        &values,
        state,
        result,
    )
}

/// [`lower_resource_clause_at_current_locals`] under the facts the proof
/// holds, for a join interface. An interface names what the proof holds
/// where its arms end, so a parameter the function has reassigned is read as
/// it stands there, exactly as the `fold` that built the resource read it.
pub(in crate::surface) fn lower_interface_resource_clause(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    assumptions: &PureFactContext,
) -> Result<CResourceFact, ClickError> {
    lower_resource_clause_at_current_locals_with_assumptions(
        resource,
        parameter_binding,
        state,
        None,
        assumptions,
    )
}

/// Lower a proof resource argument at the current C bindings, retaining only
/// the facts already checked at this frontier. These facts can identify an
/// owned cell through an alias; they do not assume the proposed fold's body.
pub(in crate::surface) fn lower_resource_clause_at_current_locals_with_assumptions(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    result: Option<&CValue>,
    assumptions: &PureFactContext,
) -> Result<CResourceFact, ClickError> {
    let values =
        parameter_values(parameter_binding).map_err(|error| ClickError::new(error.message))?;
    let array_refs =
        array_refs_for_parameters(parameter_binding.parameters, &values, state.memory());
    let (values, _) = contract_environment_at_state(&values, &array_refs, state);
    if matches!(resource, ResourceClause::MemoryAggregate { .. }) {
        let mut facts = lower_resource_clause_facts_with_values_mode_at_entry(
            resource,
            parameter_binding.parameters,
            &values,
            state,
            state,
            result,
            false,
            assumptions,
        )?;
        if facts.len() != 1 {
            return Err(ClickError::new(format!(
                "resource clause expands to {} typed memory facts where one fact is required",
                facts.len()
            )));
        }
        return Ok(facts.pop().expect("resource clause fact count was checked"));
    }
    lower_resource_clause_with_values_mode_at_entry(
        resource,
        parameter_binding.parameters,
        &values,
        state,
        state,
        result,
        false,
        assumptions,
    )
}

pub(in crate::surface) fn lower_resource_clause_facts_at_state_with_result_and_entry(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    entry_state: &CState,
    state: &CState,
    result: &CValue,
    base_assumptions: &PureFactContext,
) -> Result<Vec<CResourceFact>, ClickError> {
    let values =
        parameter_values(parameter_binding).map_err(|error| ClickError::new(error.message))?;
    lower_resource_clause_facts_with_values_mode_at_entry(
        resource,
        parameter_binding.parameters,
        &values,
        entry_state,
        state,
        Some(result),
        false,
        base_assumptions,
    )
}

fn lower_resource_clause_with_values(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CResourceFact, ClickError> {
    lower_resource_clause_with_values_mode(resource, parameters, values, state, result, false)
}

fn lower_resource_clause_with_values_mode(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
    allow_symbolic_resource_arguments: bool,
) -> Result<CResourceFact, ClickError> {
    let base_assumptions = PureFactContext::new();
    lower_resource_clause_with_values_mode_at_entry(
        resource,
        parameters,
        values,
        state,
        state,
        result,
        allow_symbolic_resource_arguments,
        &base_assumptions,
    )
}

fn lower_resource_clause_with_values_mode_at_entry(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    entry_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    allow_symbolic_resource_arguments: bool,
    base_assumptions: &PureFactContext,
) -> Result<CResourceFact, ClickError> {
    match resource {
        ResourceClause::Conditional { .. } => Err(ClickError::new(
            "conditional resource assertions require loop-contract lowering",
        )),
        ResourceClause::Named { binding, resource } => {
            let lowered = lower_resource_clause_with_values_mode_at_entry(
                resource,
                parameters,
                values,
                entry_state,
                state,
                result,
                allow_symbolic_resource_arguments,
                base_assumptions,
            )?;
            if matches!(
                lowered.resource(),
                CResource::MutexGuard(_) | CResource::MutexLive(_) | CResource::MutexUse(_)
            ) {
                // This lowering constructs the independent precondition. The
                // kernel subsequently binds its name to the rooted occurrence.
                return Ok(lowered);
            }
            let CResourceFact::Own(CResource::Composite { name, arguments }, _) = lowered else {
                return Err(ClickError::new(
                    "named instance requires an owned resource definition",
                ));
            };
            let schema = binding
                .schema
                .clone()
                .ok_or_else(|| ClickError::new("resource instance has no checked schema"))?;
            // Ownership names select current fields, but the clause still
            // determines the required resource family, arguments, and schema.
            let fields = state
                .owned_resource_instance(binding.identity)
                .map(|instance| instance.fields().to_vec().into())
                .or_else(|| binding.fields.clone())
                .ok_or_else(|| ClickError::new("resource instance has no symbolic field state"))?;
            let instance = crate::kernel::ResourceInstance::new_with_resource_arguments(
                binding.identity,
                name,
                arguments,
                schema,
                fields,
                lower_resource_reference_arguments(resource, state)?,
            )
            .ok_or_else(|| {
                ClickError::new("resource instance fields do not match the declared schema")
            })?;
            Ok(CResourceFact::own(CResource::Instance(instance)))
        }
        ResourceClause::MemoryAggregate { .. } => Err(ClickError::new(
            "aggregate resource clauses require batch lowering",
        )),
        ResourceClause::Iterated(clause) => {
            let assumptions = if allow_symbolic_resource_arguments {
                base_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads()
            } else {
                base_assumptions.clone()
            };
            lower_iterated_clause_with_values(
                clause,
                parameters,
                values,
                state,
                result,
                &assumptions,
            )
        }
        ResourceClause::Quantified { quantity, resource } => {
            let original_quantity = quantity.clone();
            let (quantity, quantity_snapshot) =
                resource_argument_to_typed_c_expression_with_snapshot(
                    quantity,
                    syntax::C0Type::Int32,
                )?;
            let assumptions = if allow_symbolic_resource_arguments {
                base_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads()
            } else {
                base_assumptions.clone()
            };
            let array_refs = array_refs_for_parameters(parameters, values, state.memory());
            let quantity = evaluate_resource_argument_with_snapshot(
                &original_quantity,
                &quantity,
                quantity_snapshot,
                &assumptions,
                ContractEnvironment::new(values, &array_refs),
                entry_state,
                state,
                result,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "could not lower declared resource quantity: {message}"
                ))
            })?;
            let CValue::Int32(quantity) = quantity else {
                return Err(ClickError::new(
                    "declared resource quantity must evaluate to int32",
                ));
            };
            let lowered = lower_resource_clause_with_values_mode_at_entry(
                resource,
                parameters,
                values,
                entry_state,
                state,
                result,
                allow_symbolic_resource_arguments,
                base_assumptions,
            )?;
            let CResourceFact::Own(resource, _) = lowered else {
                return Err(ClickError::new(
                    "declared resource quantity requires owned authority",
                ));
            };
            Ok(CResourceFact::own_quantity(resource, quantity))
        }
        ResourceClause::ViewMemory(segment) => {
            let range = lower_resource_segment_with_values(
                "read",
                segment,
                ContractEnvironment::new(
                    values,
                    &array_refs_for_parameters(parameters, values, state.memory()),
                ),
                state,
                result,
                contract_segment_element_width_for_result_type(
                    parameters,
                    segment,
                    result.and_then(|value| match value {
                        CValue::Pointer(pointer) => Some(pointer.c_type()),
                        _ => None,
                    }),
                ),
            )?;
            Ok(CResourceFact::view_memory(range))
        }
        ResourceClause::OwnMemory(segment) => {
            let range = lower_resource_segment_with_values(
                "write",
                segment,
                ContractEnvironment::new(
                    values,
                    &array_refs_for_parameters(parameters, values, state.memory()),
                ),
                state,
                result,
                contract_segment_element_width_for_result_type(
                    parameters,
                    segment,
                    result.and_then(|value| match value {
                        CValue::Pointer(pointer) => Some(pointer.c_type()),
                        _ => None,
                    }),
                ),
            )?;
            Ok(CResourceFact::own_memory(range))
        }
        ResourceClause::Declared {
            type_schema: _,
            resource_type_arguments,
            resource_arguments: _,
            access,
            kind,
            name,
            arguments: resource_arguments,
            parameter_types,
        } => {
            if !resource_type_arguments.is_empty()
                && (!matches!(
                    name.as_str(),
                    "mutex_use" | "authority" | "publisher" | "subscriber"
                ) || resource_type_arguments.len() != 1)
            {
                return Err(ClickError::new("unsupported resource type arguments"));
            }
            let assumptions = if allow_symbolic_resource_arguments {
                base_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads()
            } else {
                base_assumptions.clone()
            };
            let array_refs = array_refs_for_parameters(parameters, values, state.memory());
            let mut resource_values = Vec::new();
            if resource_arguments.len() != parameter_types.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` has malformed argument type metadata"
                )));
            }
            for (index, (argument, parameter_type)) in
                resource_arguments.iter().zip(parameter_types).enumerate()
            {
                let original_argument = argument.clone();
                let (argument, argument_snapshot) =
                    resource_argument_to_typed_c_expression_with_snapshot(
                        argument,
                        *parameter_type,
                    )?;
                let value = evaluate_resource_argument_with_snapshot(
                    &original_argument,
                    &argument,
                    argument_snapshot,
                    &assumptions,
                    ContractEnvironment::new(values, &array_refs),
                    entry_state,
                    state,
                    result,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "could not lower resource `{name}` argument {index}: {message}"
                    ))
                })?;
                let matches_type = if name == CResourceFact::ALLOCATION_RESOURCE_NAME && index == 0
                {
                    c_value_matches_allocation_pointer(&value)
                } else {
                    c_value_matches_click_type(&value, *parameter_type)
                };
                if !matches_type {
                    let (naming_parameters, naming_arguments) =
                        crate::surface::diagnostics::value_naming_tables(values);
                    return Err(ClickError::new(format!(
                        "resource `{name}` argument {index} `{}` evaluated to `{}` of type `{}`, which does not match the parameter type `{}`",
                        crate::surface::diagnostics::describe_contract_expression(
                            &original_argument
                        ),
                        crate::surface::diagnostics::describe_c_value(
                            &value,
                            ParameterBinding::new(&naming_parameters, &naming_arguments)
                        ),
                        crate::kernel::c_type_spelling(value.c_type()),
                        crate::surface::validation::describe_c0_type(*parameter_type)
                    )));
                }
                resource_values.push(value);
            }
            if name == "mutex_guard" {
                let [CValue::Pointer(mutex)] = resource_values.as_slice() else {
                    return Err(ClickError::new("mutex_guard expects one mutex pointer"));
                };
                let guard = crate::kernel::c_mutex_guard_resource(
                    state,
                    mutex.pointer(),
                    allow_symbolic_resource_arguments,
                )
                .ok_or_else(|| ClickError::new("mutex_guard requires a live acquisition"))?;
                return Ok(match access {
                    ResourceAccessMode::Own => guard,
                    ResourceAccessMode::View => CResourceFact::View(guard.resource().clone()),
                });
            }
            if name == "authority" {
                let [protected] = resource_type_arguments.as_slice() else {
                    return Err(ClickError::new(
                        "authority expects one checked resource type",
                    ));
                };
                let ResourceClause::Declared {
                    type_schema: Some(schema),
                    ..
                } = protected
                else {
                    return Err(ClickError::new(
                        "authority requires a checked resource type",
                    ));
                };
                let mut anchor_clause = protected.clone();
                let population_arity = if let ResourceClause::Declared {
                    arguments,
                    parameter_types,
                    ..
                } = &mut anchor_clause
                {
                    if arguments.len() > 1 {
                        let arity = arguments.len();
                        arguments.truncate(1);
                        parameter_types.truncate(1);
                        Some(arity)
                    } else {
                        None
                    }
                } else {
                    None
                };
                let protected_fact = lower_resource_clause_with_values_mode_at_entry(
                    &anchor_clause,
                    parameters,
                    values,
                    entry_state,
                    state,
                    result,
                    allow_symbolic_resource_arguments,
                    base_assumptions,
                )?;
                let (family, arguments) = match protected_fact.resource() {
                    CResource::Composite { name, arguments }
                    | CResource::Token { name, arguments } => (name, arguments),
                    _ => {
                        return Err(ClickError::new(
                            "authority requires a declared resource type",
                        ));
                    }
                };
                let description = crate::kernel::ResourceDescription::new(
                    family.clone(),
                    arguments.clone(),
                    schema.clone(),
                );
                let description = match population_arity {
                    Some(arity) => description
                        .with_population_arity(arity)
                        .map_err(ClickError::new)?,
                    None => description,
                };
                return Ok(CResourceFact::own(CResource::PopulationAuthority(
                    description,
                )));
            }
            if name == "mutex_live" {
                let [CValue::Pointer(mutex)] = resource_values.as_slice() else {
                    return Err(ClickError::new("mutex_live expects one mutex pointer"));
                };
                let guard = crate::kernel::c_mutex_live_resource(
                    state,
                    mutex.pointer(),
                    allow_symbolic_resource_arguments,
                )
                .ok_or_else(|| ClickError::new("mutex_live requires a live initialization"))?;
                return Ok(match access {
                    ResourceAccessMode::Own => guard,
                    ResourceAccessMode::View => CResourceFact::View(guard.resource().clone()),
                });
            }
            if let Some(side) = crate::kernel::PublicationSide::for_keyword(name) {
                let [CValue::Pointer(flag)] = resource_values.as_slice() else {
                    return Err(ClickError::new(format!(
                        "{name} expects one atomic flag pointer"
                    )));
                };
                let Some(
                    payload @ ResourceClause::Declared {
                        type_schema: Some(schema),
                        ..
                    },
                ) = resource_type_arguments.first()
                else {
                    return Err(ClickError::new(format!(
                        "{name} requires the published resource type"
                    )));
                };
                let fact = lower_resource_clause_with_values_mode_at_entry(
                    payload,
                    parameters,
                    values,
                    entry_state,
                    state,
                    result,
                    allow_symbolic_resource_arguments,
                    base_assumptions,
                )?;
                let CResource::Composite {
                    name: payload_name,
                    arguments,
                } = fact.resource()
                else {
                    return Err(ClickError::new(
                        "the published resource type must be a composite resource",
                    ));
                };
                let right = CResource::Publication(crate::kernel::PublicationRight::new(
                    side,
                    flag.pointer().clone(),
                    crate::kernel::ResourceDescription::new(
                        payload_name.clone(),
                        arguments.clone(),
                        schema.clone(),
                    ),
                ));
                return Ok(match access {
                    ResourceAccessMode::Own => CResourceFact::own(right),
                    ResourceAccessMode::View => CResourceFact::View(right),
                });
            }
            if name == "mutex_use" {
                let [CValue::Pointer(mutex)] = resource_values.as_slice() else {
                    return Err(ClickError::new("mutex_use expects one mutex pointer"));
                };
                let guard = if let Some(protected) = resource_type_arguments.first() {
                    let ResourceClause::Declared {
                        type_schema: Some(schema),
                        ..
                    } = protected
                    else {
                        return Err(ClickError::new(
                            "protected resource type has no checked schema",
                        ));
                    };
                    let fact = lower_resource_clause_with_values_mode_at_entry(
                        protected,
                        parameters,
                        values,
                        entry_state,
                        state,
                        result,
                        allow_symbolic_resource_arguments,
                        base_assumptions,
                    )?;
                    let CResource::Composite { name, arguments } = fact.resource() else {
                        return Err(ClickError::new(
                            "protected resource type must be a composite resource",
                        ));
                    };
                    crate::kernel::c_mutex_use_resource_with_type(
                        state,
                        mutex.pointer(),
                        crate::kernel::ResourceDescription::new(
                            name.clone(),
                            arguments.clone(),
                            schema.clone(),
                        ),
                    )
                } else {
                    crate::kernel::c_mutex_use_resource(state, mutex.pointer())
                };
                return Ok(match access {
                    ResourceAccessMode::Own => guard,
                    ResourceAccessMode::View => CResourceFact::View(guard.resource().clone()),
                });
            }
            let resource = match kind {
                ResourceKind::Composite => CResource::Composite {
                    name: name.clone(),
                    arguments: resource_values.into_iter().map(AlgebraicValue::C).collect(),
                },
                ResourceKind::Token => CResource::Token {
                    name: name.clone(),
                    arguments: resource_values.into_iter().map(AlgebraicValue::C).collect(),
                },
            };
            Ok(match access {
                ResourceAccessMode::Own => CResourceFact::own(resource),
                ResourceAccessMode::View => CResourceFact::View(resource),
            })
        }
    }
}

fn evaluate_resource_argument_with_snapshot(
    original: &ContractExpression,
    lowered: &CExpression,
    snapshot: crate::kernel::CResourceSnapshot,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    entry_state: &CState,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CValue, String> {
    if snapshot == crate::kernel::CResourceSnapshot::Entry {
        let direct = crate::surface::proof::evaluate_fixed_state_expression_through_kernel(
            original,
            assumptions,
            contract_environment,
            FixedStateFrame::new(entry_state, state, result, &RecordedSnapshots::new()),
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(&[]),
            ),
            &BTreeSet::new(),
        )?;
        if !matches!(&direct, CValue::Pointer(pointer) if pointer.is_null()) {
            return Ok(direct);
        }

        // An entry-state external cell may still contain the verifier's
        // placeholder null even though checked execution has established its
        // loadable entry value in a path fact. Re-evaluate only typed loads,
        // using the indexed loadable snapshot for the exact field address.
        // This keeps old resource arguments tied to checked memory evidence;
        // it does not guess from a resource family's argument list.
        let pointer_expression = match lowered {
            CExpression::Load(pointer) | CExpression::TypedLoad { pointer, .. } => pointer,
            _ => return Ok(direct),
        };
        let CValue::Pointer(address) =
            crate::surface::proof::evaluate_resource_fragment_through_kernel(
                pointer_expression,
                assumptions,
                contract_environment,
                entry_state,
                result,
            )?
        else {
            return Ok(direct);
        };
        let mut recovered = Vec::new();
        for proposition in assumptions.memory_loadable_candidates_for_base(address.pointer()) {
            let Proposition::CMemoryLoadable { memory, base, .. } = proposition else {
                continue;
            };
            if base != address.pointer() {
                continue;
            }
            let mut candidate_entry = entry_state.clone();
            candidate_entry.set_memory(memory.clone());
            let value = crate::surface::proof::evaluate_fixed_state_expression_through_kernel(
                original,
                assumptions,
                contract_environment,
                FixedStateFrame::new(&candidate_entry, state, result, &RecordedSnapshots::new()),
                SpecDefinitions::new(
                    &PredicateEnvironment::new(&[]),
                    &ClickFunctionEnvironment::new(&[]),
                ),
                &BTreeSet::new(),
            )?;
            if !recovered.contains(&value) {
                recovered.push(value);
            }
        }
        return if recovered.len() == 1 {
            Ok(recovered.remove(0))
        } else {
            Ok(direct)
        };
    }
    crate::surface::proof::evaluate_resource_argument_through_kernel(
        original,
        lowered,
        assumptions,
        contract_environment,
        state,
        result,
    )
}

fn lower_resource_clause_facts_with_values(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
) -> Result<Vec<CResourceFact>, ClickError> {
    lower_resource_clause_facts_with_values_mode(resource, parameters, values, state, result, false)
}

fn lower_resource_clause_facts_with_values_mode(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
    allow_symbolic_resource_arguments: bool,
) -> Result<Vec<CResourceFact>, ClickError> {
    let base_assumptions = PureFactContext::new();
    lower_resource_clause_facts_with_values_mode_at_entry(
        resource,
        parameters,
        values,
        state,
        state,
        result,
        allow_symbolic_resource_arguments,
        &base_assumptions,
    )
}

fn lower_resource_clause_facts_with_values_mode_at_entry(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    entry_state: &CState,
    state: &CState,
    result: Option<&CValue>,
    allow_symbolic_resource_arguments: bool,
    base_assumptions: &PureFactContext,
) -> Result<Vec<CResourceFact>, ClickError> {
    match resource {
        ResourceClause::MemoryAggregate { access, segments } => segments
            .iter()
            .map(|segment| {
                let leaf = match access {
                    ResourceAccessMode::Own => ResourceClause::OwnMemory(segment.clone()),
                    ResourceAccessMode::View => ResourceClause::ViewMemory(segment.clone()),
                };
                lower_resource_clause_with_values_mode_at_entry(
                    &leaf,
                    parameters,
                    values,
                    entry_state,
                    state,
                    result,
                    allow_symbolic_resource_arguments,
                    base_assumptions,
                )
            })
            .collect(),
        ResourceClause::Quantified { quantity, resource } => {
            let original_quantity = quantity.clone();
            let (quantity, quantity_snapshot) =
                resource_argument_to_typed_c_expression_with_snapshot(
                    quantity,
                    syntax::C0Type::Int32,
                )?;
            let assumptions = if allow_symbolic_resource_arguments {
                base_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads()
            } else {
                base_assumptions.clone()
            };
            let array_refs = array_refs_for_parameters(parameters, values, state.memory());
            let quantity = evaluate_resource_argument_with_snapshot(
                &original_quantity,
                &quantity,
                quantity_snapshot,
                &assumptions,
                ContractEnvironment::new(values, &array_refs),
                entry_state,
                state,
                result,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "could not lower declared resource quantity: {message}"
                ))
            })?;
            let CValue::Int32(quantity) = quantity else {
                return Err(ClickError::new(
                    "declared resource quantity must evaluate to int32",
                ));
            };
            lower_resource_clause_facts_with_values_mode_at_entry(
                resource,
                parameters,
                values,
                entry_state,
                state,
                result,
                allow_symbolic_resource_arguments,
                base_assumptions,
            )?
            .into_iter()
            .map(|lowered| {
                let CResourceFact::Own(resource, _) = lowered else {
                    return Err(ClickError::new(
                        "declared resource quantity requires owned authority",
                    ));
                };
                Ok(CResourceFact::own_quantity(resource, quantity.clone()))
            })
            .collect()
        }
        _ => Ok(vec![lower_resource_clause_with_values_mode_at_entry(
            resource,
            parameters,
            values,
            entry_state,
            state,
            result,
            allow_symbolic_resource_arguments,
            base_assumptions,
        )?]),
    }
}

/// Whether this argument is the C null pointer constant standing at a
/// pointer-typed resource or pure-function parameter.
///
/// A walk that ends at the root of a parent-linked structure reaches a
/// position whose parent is null, and null is the only truthful spelling of
/// that argument: the parameter the body reassigned means its entry value at
/// the boundary, which is a different node. The same holds inside the model:
/// `rb_parent_is(sub, 0)` is how a pure function says "this subtree is the
/// root", and a caller should not have to write the null case out by hand.
/// `0` is already a contract expression, so this is the C null-pointer-constant
/// typing rule rather than new syntax.
pub(in crate::surface) fn argument_is_null_pointer_constant(
    argument: &ContractExpression,
    parameter_type: C0Type,
) -> bool {
    parameter_type.is_pointer()
        && matches!(argument, ContractExpression::IntegerLiteral(text) if text == "0")
}

/// `resource_argument_to_c_expression` with the declared parameter type in
/// hand, so the null pointer constant lowers to that pointer type's null
/// value instead of an `int32` zero.
pub(in crate::surface) fn resource_argument_to_typed_c_expression(
    argument: &ContractExpression,
    parameter_type: C0Type,
) -> Result<CExpression, ClickError> {
    if argument_is_null_pointer_constant(argument, parameter_type) {
        return Ok(c_typed_pointer_value(
            Pointer::null(),
            parameter_type.to_kernel_type(),
        ));
    }
    resource_argument_to_c_expression(argument)
}

/// Lowers a declared-resource argument together with the state that supplies
/// its value.  The surrounding resource clause still has its own snapshot
/// (entry for requirements, post for produced resources); `old(...)` selects
/// the entry state for only this argument.
pub(in crate::surface) fn resource_argument_to_typed_c_expression_with_snapshot(
    argument: &ContractExpression,
    parameter_type: C0Type,
) -> Result<(CExpression, crate::kernel::CResourceSnapshot), ClickError> {
    if let ContractExpression::Old(inner) = argument {
        return Ok((
            resource_argument_to_typed_c_expression(inner, parameter_type)?,
            crate::kernel::CResourceSnapshot::Entry,
        ));
    }
    Ok((
        resource_argument_to_typed_c_expression(argument, parameter_type)?,
        crate::kernel::CResourceSnapshot::Current,
    ))
}

pub(in crate::surface) fn resource_argument_to_c_expression(
    argument: &ContractExpression,
) -> Result<CExpression, ClickError> {
    match argument {
        ContractExpression::IntegerLiteral(text) => {
            let value = text.parse::<u64>().map_err(|_| {
                ClickError::new("an arbitrary Integer literal requires Integer context")
            })?;
            let value = if value <= i32::MAX as u64 {
                CValue::Int32(Bitvector32Term::Constant(value as u32))
            } else if value <= i64::MAX as u64 {
                CValue::Int64(Bitvector32Term::Int64Constant(value as i64))
            } else {
                CValue::UInt64(Bitvector32Term::UInt64Constant(value))
            };
            Ok(CExpression::Value(value))
        }
        ContractExpression::Negate(expression) => {
            if let ContractExpression::IntegerLiteral(text) = expression.as_ref()
                && let Ok(value) = text.parse::<u64>()
                && value <= (i32::MAX as u64) + 1
            {
                return Ok(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Constant(0u32.wrapping_sub(value as u32)),
                )));
            }
            Ok(CExpression::Subtract(
                Box::new(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Constant(0),
                ))),
                Box::new(resource_argument_to_c_expression(expression)?),
            ))
        }
        ContractExpression::ResourceField(_) => Err(ClickError::new(
            "resource fields are symbolic Click values, not C arguments",
        )),
        ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::AlgebraicConstructor { .. }
        | ContractExpression::AlgebraicMatch { .. } => Err(ClickError::new(
            "declared resource arguments do not yet accept algebraic values",
        )),
        ContractExpression::SequenceLiteral(_) | ContractExpression::SequenceConcat(_, _) => Err(
            ClickError::new("declared resource arguments do not yet accept sequence values"),
        ),
        ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::CUnary {
            lowered: expression,
            ..
        }
        | ContractExpression::CFragment(expression) => Ok(expression.clone()),
        ContractExpression::Field { lowered, .. } => Ok(lowered.clone()),
        ContractExpression::ArrayIndex { lowered, .. } => Ok(lowered.clone()),
        ContractExpression::Binding(name) | ContractExpression::CBinding(name) => {
            Ok(CExpression::Variable(name.clone()))
        }
        ContractExpression::Add(left, right) => Ok(CExpression::Add(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Subtract(left, right) => Ok(CExpression::Subtract(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Multiply(left, right) => Ok(CExpression::Multiply(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Divide(left, right) => Ok(CExpression::Divide(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::Remainder(left, right) => Ok(CExpression::Remainder(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Ok(CExpression::ShiftLeft(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Ok(CExpression::ShiftRight(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Ok(CExpression::BitwiseAnd(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Ok(CExpression::BitwiseOr(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Ok(CExpression::BitwiseXor(
            Box::new(resource_argument_to_c_expression(left)?),
            Box::new(resource_argument_to_c_expression(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Ok(CExpression::BitwiseNot(Box::new(
            resource_argument_to_c_expression(expression)?,
        ))),
        ContractExpression::Index(base, index) => Ok(CExpression::Index(
            Box::new(resource_argument_to_c_expression(base)?),
            Box::new(resource_argument_to_c_expression(index)?),
        )),
        ContractExpression::Old(_)
        | ContractExpression::ResourceCount(_)
        | ContractExpression::ResourceWildcard
        | ContractExpression::At { .. }
        | ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Call { .. } => Err(ClickError::new(
            "declared resource arguments currently support current-state C expressions only",
        )),
        ContractExpression::Let { body, .. } => {
            // `apply_contract_lets_to_expression` already substituted every
            // referenced value into the body; the wrapper only preserves
            // sharing for later passes. Unwrap to the substituted body.
            resource_argument_to_c_expression(body)
        }
    }
}

fn lower_resource_segment_with_values(
    resource_name: &str,
    segment: &ContractSegment,
    contract_environment: ContractEnvironment<'_>,
    state: &CState,
    result: Option<&CValue>,
    element_width: u32,
) -> Result<CMemoryRange, ClickError> {
    if segment.state != ContractSegmentState::Current {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: resource segments cannot use `old(...)`"
        )));
    }
    // Resource ranges embed field loads symbolically (the canonical
    // `load(arg-memory@...)` forms), so segment evaluation must not
    // demand concrete loadability.
    let assumptions = PureFactContext::new()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let (surface_base, surface_start, surface_end) = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end }
        | ContractSegmentSurface::StructRange {
            base, start, end, ..
        } => (Some(base), Some(start), Some(end)),
        _ => (None, None, None),
    };
    let evaluate = |expression: &CExpression, original: Option<&ContractExpression>| match original
    {
        Some(original) => crate::surface::proof::evaluate_resource_argument_through_kernel(
            original,
            expression,
            &assumptions,
            contract_environment,
            state,
            result,
        ),
        None => crate::surface::proof::evaluate_resource_fragment_through_kernel(
            expression,
            &assumptions,
            contract_environment,
            state,
            result,
        ),
    };
    let base = evaluate(&segment.base, surface_base).map_err(|message| {
        // A parameter or local has no storage a contract can name.
        if let CExpression::AddressOf(variable) = &segment.base
            && let CExpression::Variable(name) = &**variable
        {
            return ClickError::new(format!(
                "could not lower `{resource_name}` resource: `{name}` alone names the variable itself, which a contract cannot own; write `*{name}` for the object it points at"
            ));
        }
        ClickError::new(format!(
            "could not lower `{resource_name}` resource: {message} (segment {})",
            super::super::diagnostics::describe_contract_segment(segment)
        ))
    })?;
    let CValue::Pointer(base) = base else {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment base did not evaluate to a pointer"
        )));
    };
    let base = base.into_pointer();
    // A bound keeps its own integer type in the contract: a range with a
    // 64-bit bound is wide, and one with two `int32` bounds is not
    // (`design/typed-indices.md`, stage 2).
    let start_value = evaluate(&segment.start, surface_start).map_err(|message| {
        ClickError::new(format!(
            "could not lower `{resource_name}` resource: {message}"
        ))
    })?;
    let end_value = evaluate(&segment.end, surface_end).map_err(|message| {
        ClickError::new(format!(
            "could not lower `{resource_name}` resource: {message}"
        ))
    })?;
    let bound = |value: CValue, which: &str| match value {
        CValue::Int32(term) => Ok(term),
        value if crate::kernel::narrow_range_constant(&value).is_some() => {
            Ok(crate::kernel::narrow_range_constant(&value).expect("checked above"))
        }
        _ => Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment {which} did not evaluate to an integer index"
        ))),
    };
    // The same rule as the kernel's resource and proposition lowering.
    if let Some((start, end)) = crate::kernel::wide_range_bounds(&start_value, &end_value) {
        return Ok(CMemoryRange::new_wide(base, start, end, element_width));
    }
    let start = bound(start_value, "start")?;
    let end = bound(end_value, "end")?;
    if let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) = (&start, &end)
        && end < start
    {
        return Err(ClickError::new(format!(
            "`{resource_name}` segment has an end before its start: {start}..{end}"
        )));
    }
    Ok(CMemoryRange::new_with_element_width(
        base,
        start,
        end,
        element_width,
    ))
}

fn loadable_requirement_props(
    requirement: &Requirement,
    parameter_binding: ParameterBinding<'_>,
    memory: &CMemory,
    assumptions: &PureFactContext,
) -> Result<Vec<Proposition>, ClickError> {
    if let Requirement::LoadableSegment { segment } = requirement
        && segment.state == ContractSegmentState::Current
    {
        let state = CState::new().with_memory(memory.clone());
        let values = parameter_values(parameter_binding)?;
        let range = lower_resource_segment_with_values(
            "viewable",
            segment,
            ContractEnvironment::new(
                &values,
                &array_refs_for_parameters(parameter_binding.parameters, &values, memory),
            ),
            &state,
            None,
            contract_segment_element_width(parameter_binding.parameters, segment),
        )?;
        let guards = memory_range_loadable_guards(&range);
        reject_impossible_range_guards(&guards, assumptions)?;
        let mut propositions = vec![memory_range_loadable_atom_prop(memory, &range)];
        propositions.extend(guards);
        return Ok(propositions);
    }
    let (base, bytes, guards) = loadable_base_and_bytes(requirement, parameter_binding)?;
    reject_impossible_range_guards(&guards, assumptions)?;
    let mut propositions = vec![Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base,
        bytes,
        wide: false,
    }];
    propositions.extend(guards);
    Ok(propositions)
}

pub(in crate::surface) fn resource_clause_loadable_prop(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    memory: &CMemory,
) -> Result<Option<Proposition>, ClickError> {
    resource_clause_loadable_prop_at_state(
        resource,
        parameter_binding,
        &CState::new().with_memory(memory.clone()),
    )
}

pub(in crate::surface) fn resource_clause_loadable_prop_at_state(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
) -> Result<Option<Proposition>, ClickError> {
    let Some(ranges) = resource_clause_memory_ranges_at_state(resource, parameter_binding, state)?
    else {
        return Ok(None);
    };
    let mut propositions = ranges
        .iter()
        .map(|range| memory_range_loadable_atom_prop(state.memory(), range))
        .collect::<Vec<_>>();
    let first = propositions
        .drain(..1)
        .next()
        .expect("memory resource clause has at least one range");
    Ok(Some(propositions.into_iter().fold(first, |left, right| {
        Proposition::And(Box::new(left), Box::new(right))
    })))
}

pub(in crate::surface) fn resource_clause_loadable_props_at_state(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    assumptions: &PureFactContext,
) -> Result<Option<Vec<Proposition>>, ClickError> {
    let Some(ranges) = resource_clause_memory_ranges_at_state(resource, parameter_binding, state)?
    else {
        return Ok(None);
    };
    let loadable = ranges
        .iter()
        .map(|range| memory_range_loadable_atom_prop(state.memory(), range))
        .reduce(|left, right| Proposition::And(Box::new(left), Box::new(right)))
        .expect("memory resource clause has at least one range");
    // Every stated range carries its byte-count guards, whichever clause
    // states it. `owns p[lo..hi]` and an aggregate range mean the same thing
    // about `lo..hi` as `views p[lo..hi]` does, and the loadability rules read
    // all three at element granularity; a guard that rode along with one
    // clause and not another would make the same range mean two things.
    let mut propositions = vec![loadable];
    let guards = ranges
        .iter()
        .flat_map(memory_range_loadable_guards)
        .collect::<Vec<_>>();
    reject_impossible_range_guards(&guards, assumptions)?;
    propositions.extend(guards);
    Ok(Some(propositions))
}

fn reject_impossible_range_guards(
    guards: &[Proposition],
    assumptions: &PureFactContext,
) -> Result<(), ClickError> {
    if guards.iter().any(|guard| match guard {
        Proposition::ConditionIs(ConditionTerm::Constant(false), true) => true,
        Proposition::ConditionIs(condition, true) => assumptions.decide(condition) == Some(false),
        _ => false,
    }) {
        return Err(ClickError::new(
            "memory range requires the verifier to have assumed a condition fact that cannot hold",
        ));
    }
    Ok(())
}

pub(in crate::surface) fn resource_clause_memory_ranges_at_state(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
) -> Result<Option<Vec<CMemoryRange>>, ClickError> {
    let ranges = match resource {
        ResourceClause::Conditional { .. } => return Ok(None),
        ResourceClause::Named { .. } => return Ok(None),
        ResourceClause::ViewMemory(_) | ResourceClause::OwnMemory(_) => {
            let lowered = lower_resource_clause_at_state(resource, parameter_binding, state)?;
            vec![
                lowered
                    .memory_view_range()
                    .or_else(|| lowered.memory_own_range())
                    .expect("memory clause should lower to a memory range")
                    .clone(),
            ]
        }
        ResourceClause::MemoryAggregate { .. } => {
            lower_resource_clause_facts_at_state(resource, parameter_binding, state)?
                .into_iter()
                .map(|lowered| {
                    lowered
                        .memory_view_range()
                        .or_else(|| lowered.memory_own_range())
                        .expect("aggregate memory clause should lower to memory ranges")
                        .clone()
                })
                .collect()
        }
        ResourceClause::Declared { .. }
        | ResourceClause::Quantified { .. }
        | ResourceClause::Iterated(_) => return Ok(None),
    };
    Ok(Some(ranges))
}

pub(in crate::surface) fn memory_range_loadable_prop(
    memory: &CMemory,
    range: &CMemoryRange,
) -> Proposition {
    memory_range_loadable_atom_prop(memory, range)
}

pub(in crate::surface) fn memory_range_loadable_atom_prop(
    memory: &CMemory,
    range: &CMemoryRange,
) -> Proposition {
    if range.wide_bounds().is_some() {
        return range.loadable_fact(memory);
    }
    let (base, bytes) = range.byte_footprint();
    Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base,
        bytes,
        wide: false,
    }
}

pub(in crate::surface) fn memory_range_loadable_guards(range: &CMemoryRange) -> Vec<Proposition> {
    crate::kernel::memory_range_extent_guard_spellings(range)
}

pub(in crate::surface) fn concrete_loadable_block(
    requirement: &Requirement,
    parameter_binding: ParameterBinding<'_>,
) -> Result<Option<(String, ConcreteMemoryRangeSeed)>, ClickError> {
    match requirement {
        Requirement::LoadableSegment { segment } => {
            let state = CState::new();
            let source_segment = segment;
            let Ok(segment) =
                evaluate_requirement_segment(parameter_binding, &state, source_segment)
            else {
                return Ok(None);
            };
            if segment.base.offset != PointerOffsetTerm::Constant(0)
                || segment.start != Bitvector32Term::Constant(0)
            {
                return Ok(None);
            }
            let Bitvector32Term::Constant(end) = segment.end else {
                return Ok(None);
            };
            if let Some(layout) =
                object_segment_layout(parameter_binding.parameters, source_segment)
            {
                return Ok(Some((
                    format!("{:?}", segment.source),
                    object_range_seed(segment.base, layout),
                )));
            }
            let element_width =
                contract_segment_element_width(parameter_binding.parameters, &segment.source);
            let bytes = end
                .checked_mul(element_width)
                .ok_or_else(|| ClickError::new("`viewable` segment overflows byte count"))?;
            Ok(Some((
                format!("{:?}", segment.source),
                ConcreteMemoryRangeSeed {
                    base: segment.base,
                    bytes,
                    element_width,
                    observation_count: declared_segment_observation_count(source_segment),
                    element_type: (!contract_expression_is_struct_array(
                        parameter_binding.parameters,
                        &segment.source.base,
                    ))
                    .then(|| {
                        contract_segment_element_type(parameter_binding.parameters, &segment.source)
                    }),
                    struct_layout: contract_segment_struct_layout(
                        parameter_binding.parameters,
                        source_segment,
                    )
                    .cloned(),
                },
            )))
        }
        Requirement::Resource(_) | Requirement::Proposition(_) => Ok(None),
    }
}

pub(in crate::surface) fn concrete_access_resource_blocks(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
) -> Result<Vec<(String, ConcreteMemoryRangeSeed)>, ClickError> {
    let segments = match resource {
        ResourceClause::Conditional { .. } => return Ok(vec![]),
        ResourceClause::Named { .. } => return Ok(vec![]),
        ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
            vec![segment]
        }
        ResourceClause::MemoryAggregate { segments, .. } => segments.iter().collect(),
        ResourceClause::Declared { .. }
        | ResourceClause::Quantified { .. }
        | ResourceClause::Iterated(_) => {
            return Ok(Vec::new());
        }
    };
    let mut result = Vec::new();
    for segment in segments {
        let state = CState::new();
        let source_segment = segment;
        let Ok(segment) = evaluate_requirement_segment(parameter_binding, &state, source_segment)
        else {
            continue;
        };
        let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
            (&segment.start, &segment.end)
        else {
            continue;
        };
        if end < start {
            return Err(ClickError::new(format!(
                "resource segment has an end before its start: {start}..{end}"
            )));
        }
        if let Some(layout) = object_segment_layout(parameter_binding.parameters, source_segment)
            && *start == 0
        {
            result.push((
                format!("{:?}", segment.source),
                object_range_seed(segment.base, layout),
            ));
            continue;
        }
        let element_width =
            contract_segment_element_width(parameter_binding.parameters, &segment.source);
        let element_count = end - start;
        let bytes = element_count
            .checked_mul(element_width)
            .ok_or_else(|| ClickError::new("`write` segment overflows byte count"))?;
        result.push((
            format!("{:?}", segment.source),
            ConcreteMemoryRangeSeed {
                base: offset_pointer_by_elements(segment.base, segment.start, element_width),
                bytes,
                element_width,
                observation_count: declared_segment_observation_count(source_segment),
                element_type: (!contract_expression_is_struct_array(
                    parameter_binding.parameters,
                    &segment.source.base,
                ))
                .then(|| {
                    contract_segment_element_type(parameter_binding.parameters, &segment.source)
                }),
                struct_layout: contract_segment_struct_layout(
                    parameter_binding.parameters,
                    source_segment,
                )
                .cloned(),
            },
        ));
    }
    Ok(result)
}

pub(in crate::surface) fn loadable_base_and_bytes(
    requirement: &Requirement,
    parameter_binding: ParameterBinding<'_>,
) -> Result<(Pointer, Bitvector32Term, Vec<Proposition>), ClickError> {
    match requirement {
        Requirement::LoadableSegment { segment } => {
            let state = CState::new();
            let segment = evaluate_requirement_segment(parameter_binding, &state, segment)
                .map_err(|message| {
                    ClickError::new(format!("could not lower `viewable` segment: {message}"))
                })?;
            if let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
                (&segment.start, &segment.end)
                && end < start
            {
                return Err(ClickError::new(format!(
                    "`viewable` segment has an end before its start: {start}..{end}"
                )));
            }
            let element_width =
                contract_segment_element_width(parameter_binding.parameters, &segment.source);
            let bytes = crate::kernel::memory_range_byte_count(
                segment.start.clone(),
                segment.end.clone(),
                element_width,
            );
            // A written `viewable(p[a..b])` states the same range a `views
            // p[a..b]` clause does, so it carries the same guards in the same
            // spellings (`memory_range_loadable_guards`): the endpoint form
            // memory reasoning reads and the signed count form a proof can
            // write, such as `n <= 1073741823` for `p[0..n]` of `int32`.
            let guards = memory_range_loadable_guards(&CMemoryRange::new_with_element_width(
                segment.base.clone(),
                segment.start.clone(),
                segment.end.clone(),
                element_width,
            ));
            Ok((
                offset_pointer_by_elements(segment.base, segment.start.clone(), element_width),
                bytes,
                guards,
            ))
        }
        Requirement::Proposition(_) | Requirement::Resource(_) => {
            Err(ClickError::new("expected viewable requirement"))
        }
    }
}

/// The struct layout behind `*p` for a struct-pointer parameter `p`.
/// Such a segment is one complete object, not a run of int32 words, so its
/// cells take the field types of the layout.
pub(in crate::surface) fn object_segment_layout<'a>(
    parameters: &'a [syntax::C0Parameter],
    segment: &'a ContractSegment,
) -> Option<&'a syntax::C0StructLayout> {
    let struct_name = match &segment.surface {
        ContractSegmentSurface::Object(name) | ContractSegmentSurface::ObjectAt { name, .. } => {
            name
        }
        _ => return None,
    };
    // The base is the named parameter while the clause is written against
    // it, and a pointer value once a body has been instantiated for a held
    // resource; in both cases the surface names the struct, whose layout
    // any parameter of that struct type carries.
    if let CExpression::Variable(name) = &segment.base
        && let Some(layout) = parameters
            .iter()
            .find(|parameter| parameter.name() == name)
            .and_then(syntax::C0Parameter::pointee_struct_layout)
    {
        return Some(layout);
    }
    parameters
        .iter()
        .find(|parameter| parameter.struct_name() == Some(struct_name.as_str()))
        .and_then(|parameter| {
            parameter
                .pointee_struct_layout()
                .or_else(|| parameter.struct_layout())
        })
}

/// One complete struct object as a memory range seed: a single element of
/// the layout's size, materialized field by field.
fn object_range_seed(base: Pointer, layout: &syntax::C0StructLayout) -> ConcreteMemoryRangeSeed {
    ConcreteMemoryRangeSeed {
        base,
        bytes: layout.size_bytes(),
        element_width: layout.size_bytes(),
        element_type: None,
        observation_count: None,
        struct_layout: Some(layout.clone()),
    }
}

pub(in crate::surface) fn contract_segment_element_width(
    parameters: &[syntax::C0Parameter],
    segment: &ContractSegment,
) -> u32 {
    contract_segment_element_width_for_result_type(parameters, segment, None)
}

pub(in crate::surface) fn contract_segment_element_width_for_result_type(
    parameters: &[syntax::C0Parameter],
    segment: &ContractSegment,
    result_type: Option<CType>,
) -> u32 {
    if let Some(element_width) = segment.field_element_width() {
        return element_width;
    }
    if matches!(&segment.base, CExpression::Variable(name)
        if name == crate::kernel::C_CONTRACT_RESULT_NAME
            || (name == "result" && !matches!(&segment.surface,
                ContractSegmentSurface::Range { base: ContractExpression::CBinding(_), .. })))
        && let Some(element_width) = result_type
            .and_then(CType::pointee_type)
            .map(CType::byte_width)
    {
        return element_width;
    }
    contract_expression_element_width(parameters, &segment.base).unwrap_or(4)
}

/// Loop locals have frontend-declared types even before execution binds values.
/// Preserve explicit field layouts and parameter ABI widths before consulting
/// that index. No scalar declaration itself supplies a readable range.
pub(in crate::surface) fn contract_segment_element_width_with_pointer_types(
    parameters: &[syntax::C0Parameter],
    segment: &ContractSegment,
    result_type: Option<CType>,
    pointer_types: Option<&BTreeMap<String, CType>>,
) -> u32 {
    fn local_element(expression: &CExpression, types: &BTreeMap<String, CType>) -> Option<CType> {
        match expression {
            CExpression::Variable(name) => types.get(name).copied(),
            CExpression::Add(left, right) => {
                local_element(left, types).or_else(|| local_element(right, types))
            }
            CExpression::Subtract(left, _) => local_element(left, types),
            CExpression::MemberAddress { selection, .. } => Some(selection.value_type),
            CExpression::PointerOffsetBytes { pointer, .. } => local_element(pointer, types),
            _ => None,
        }
    }
    if segment.field_element_width().is_some()
        || contract_expression_element_width(parameters, &segment.base).is_some()
        || matches!(&segment.base, CExpression::Variable(name)
            if name == crate::kernel::C_CONTRACT_RESULT_NAME
                || (name == "result" && !matches!(&segment.surface,
                    ContractSegmentSurface::Range { base: ContractExpression::CBinding(_), .. })))
    {
        return contract_segment_element_width_for_result_type(parameters, segment, result_type);
    }
    pointer_types
        .and_then(|types| local_element(&segment.base, types))
        .map(CType::byte_width)
        .unwrap_or_else(|| {
            contract_segment_element_width_for_result_type(parameters, segment, result_type)
        })
}

pub(in crate::surface) fn declared_segment_observation_count(
    segment: &ContractSegment,
) -> Option<u32> {
    segment.field_element_type()?;
    match &segment.base {
        CExpression::TypedLoad { value_type, .. } => value_type
            .array_element_and_count()
            .map(|(_, count)| count)
            .or(Some(1)),
        _ => Some(1),
    }
}

pub(in crate::surface) fn contract_segment_element_type(
    parameters: &[syntax::C0Parameter],
    segment: &ContractSegment,
) -> CType {
    segment
        .field_element_type()
        .or_else(|| contract_expression_element_type(parameters, &segment.base))
        .unwrap_or(CType::Int32)
}

fn contract_expression_is_struct_array(
    parameters: &[syntax::C0Parameter],
    expression: &CExpression,
) -> bool {
    match expression {
        CExpression::Variable(name) => parameters
            .iter()
            .find(|parameter| parameter.name() == name)
            .is_some_and(|parameter| parameter.array_element_width().is_some()),
        CExpression::Add(left, right) => {
            contract_expression_is_struct_array(parameters, left)
                || contract_expression_is_struct_array(parameters, right)
        }
        CExpression::Subtract(left, _) => contract_expression_is_struct_array(parameters, left),
        _ => false,
    }
}

fn contract_expression_struct_layout<'a>(
    parameters: &'a [syntax::C0Parameter],
    expression: &CExpression,
) -> Option<&'a syntax::C0StructLayout> {
    match expression {
        CExpression::Variable(name) => parameters
            .iter()
            .find(|parameter| parameter.name() == name)
            .and_then(|parameter| {
                (parameter.array_element_width().is_some() || parameter.is_struct_value())
                    .then(|| parameter.struct_layout())
                    .flatten()
            }),
        CExpression::Add(left, right) => contract_expression_struct_layout(parameters, left)
            .or_else(|| contract_expression_struct_layout(parameters, right)),
        CExpression::Subtract(left, _) => contract_expression_struct_layout(parameters, left),
        _ => None,
    }
}

fn contract_segment_struct_layout<'a>(
    parameters: &'a [syntax::C0Parameter],
    segment: &'a ContractSegment,
) -> Option<&'a syntax::C0StructLayout> {
    if let ContractSegmentSurface::StructRange { layout, .. } = &segment.surface {
        return Some(&layout.layout);
    }
    // A field segment already carries the leaf's physical type and width.
    // Treating its base as an aggregate range would expand every struct field
    // at the leaf's address, which can install a different typed cell there.
    if segment.field_element_type().is_some() {
        return None;
    }
    contract_expression_struct_layout(parameters, &segment.base)
}

fn contract_expression_element_type(
    parameters: &[syntax::C0Parameter],
    expression: &CExpression,
) -> Option<CType> {
    match expression {
        CExpression::MemberAddress { selection, .. } => Some(selection.value_type),
        // An indexed place becomes `&base[index]` when used as ownership.
        // Its address still points to the base's element type.
        CExpression::AddressOf(place) => match place.as_ref() {
            CExpression::Index(base, _) => contract_expression_element_type(parameters, base),
            _ => None,
        },
        CExpression::Value(value) => value.c_type().pointee_type(),
        CExpression::Cast { target_type, .. } => target_type.pointee_type(),
        CExpression::Variable(name) => parameters
            .iter()
            .find(|parameter| parameter.name() == name)
            .and_then(|parameter| parameter.c_type().pointee_type())
            .map(C0Type::to_kernel_type),
        CExpression::Add(left, right) => contract_expression_element_type(parameters, left)
            .or_else(|| contract_expression_element_type(parameters, right)),
        CExpression::Subtract(left, _) => contract_expression_element_type(parameters, left),
        CExpression::TypedLoad { value_type, .. } => match value_type {
            CType::Int32Array(_) => Some(CType::Int32),
            CType::UInt8Array(_) => Some(CType::UInt8),
            CType::Int8Array(_) => Some(CType::Int8),
            CType::Int16Array(_) => Some(CType::Int16),
            CType::UInt16Array(_) => Some(CType::UInt16),
            CType::UInt32Array(_) => Some(CType::UInt32),
            CType::Int64Array(_) => Some(CType::Int64),
            CType::Int128Array(_) => Some(CType::Int128),
            CType::UInt64Array(_) => Some(CType::UInt64),
            CType::UInt128Array(_) => Some(CType::UInt128),
            value_type => value_type.pointee_type(),
        },
        _ => None,
    }
}

pub(in crate::surface) fn contract_expression_element_width(
    parameters: &[syntax::C0Parameter],
    expression: &CExpression,
) -> Option<u32> {
    match expression {
        CExpression::MemberAddress { selection, .. } => Some(selection.value_type.byte_width()),
        CExpression::AddressOf(place) => match place.as_ref() {
            CExpression::Index(base, _) => contract_expression_element_width(parameters, base),
            _ => None,
        },
        CExpression::Value(value) => value.c_type().pointee_type().map(CType::byte_width),
        CExpression::Cast { target_type, .. } => target_type.pointee_type().map(CType::byte_width),
        CExpression::Variable(name) => parameters
            .iter()
            .find(|parameter| parameter.name() == name)
            .and_then(|parameter| {
                if parameter.is_struct_value() {
                    Some(4)
                } else {
                    parameter
                        .array_element_width()
                        .or_else(|| match parameter.c_type() {
                            c_type if c_type.is_pointer() => c_type
                                .pointee_type()
                                .map(C0Type::to_kernel_type)
                                .map(CType::byte_width),
                            C0Type::Int32Array(_) => Some(4),
                            C0Type::CharArray(_, _) => Some(1),
                            C0Type::UInt8Array(_) => Some(1),
                            C0Type::Int8Array(_) => Some(1),
                            C0Type::Int16Array(_) | C0Type::UInt16Array(_) => Some(2),
                            C0Type::UInt32Array(_) => Some(4),
                            C0Type::Int64Array(_, _) | C0Type::UInt64Array(_, _) => Some(8),
                            C0Type::Int128Array(_) | C0Type::UInt128Array(_) => Some(16),
                            _ => None,
                        })
                }
            }),
        CExpression::Add(left, right) => contract_expression_element_width(parameters, left)
            .or_else(|| contract_expression_element_width(parameters, right)),
        CExpression::Subtract(left, _) => contract_expression_element_width(parameters, left),
        CExpression::TypedLoad { value_type, .. } => match value_type {
            c_type if c_type.is_pointer() => c_type.pointee_type().map(CType::byte_width),
            CType::Int32Array(_) => Some(4),
            CType::UInt8Array(_) => Some(1),
            CType::Int8Array(_) => Some(1),
            CType::Int16Array(_) | CType::UInt16Array(_) => Some(2),
            CType::UInt32Array(_) => Some(4),
            CType::Int64Array(_) | CType::UInt64Array(_) => Some(8),
            CType::Int128Array(_) | CType::UInt128Array(_) => Some(16),
            _ => None,
        },
        _ => None,
    }
}

fn symbolic_value_for_element(memory: &CMemory, pointer: &Pointer, element_type: CType) -> CValue {
    let load = crate::kernel::canonical_form_of_typed_load(
        crate::kernel::intern_c_memory(memory.clone()),
        pointer.clone(),
        element_type,
    )
    .expect("a resource element has a scalar load type");
    symbolic_value_from_load(pointer, element_type, load)
}

pub(in crate::surface) fn symbolic_value_from_load(
    pointer: &Pointer,
    element_type: CType,
    load: Bitvector32Term,
) -> CValue {
    // Share the kernel's seeded-cell constructor, including its retained
    // typed pointer-load definition. Surface entry cells and lazy cell runs
    // must name the same value through later model aliases.
    crate::kernel::cell_run_value(pointer, element_type, load)
}

pub(in crate::surface) fn requirement_proposition_prop(
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, ClickError> {
    requirement_proposition_prop_with_assumptions(
        parameter_binding,
        state,
        proposition,
        spec_definitions,
        &PureFactContext::new(),
    )
}

pub(in crate::surface) fn requirement_proposition_prop_with_assumptions(
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
    assumptions: &PureFactContext,
) -> Result<Proposition, ClickError> {
    requirement_proposition_and_facts_with_assumptions(
        parameter_binding,
        state,
        proposition,
        spec_definitions,
        assumptions,
    )
    .map(|(proposition, _)| proposition)
}

fn requirement_proposition_and_facts_with_assumptions(
    parameter_binding: ParameterBinding<'_>,
    state: &CState,
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
    assumptions: &PureFactContext,
) -> Result<(Proposition, Vec<Proposition>), ClickError> {
    // The requirement is elaborated as the contract elaborates it and
    // lowered by the kernel at the entry state, with the parameters bound
    // to their argument values where the state does not bind them.
    let spec = crate::surface::lowering::elaborate_requirement_proposition(
        parameter_binding.parameters,
        state,
        proposition,
        spec_definitions,
    )
    .map_err(ClickError::new)?;
    let mut lowering_state = state.clone();
    for (name, value) in parameter_values(parameter_binding)? {
        if lowering_state.locals().get(&name).is_none() {
            lowering_state = lowering_state.with_local(name, value);
        }
    }
    let (lowered, facts, obligations) =
        crate::kernel::c_lower_spec_proposition_at_state(&lowering_state, &spec, None, assumptions)
            .map_err(|message| {
                ClickError::new(format!(
                    "could not lower requirement `{}`: {message}",
                    crate::surface::diagnostics::describe_click_proposition(proposition)
                ))
            })?;
    // A requirement may read only memory the function's entry justifies:
    // cells the entry holds, a resource it views or owns, or a loadability
    // the requirements state.
    if let Some(obligation) = obligations.iter().find(|obligation| {
        !crate::kernel::c_state_justifies_loadability_obligation(
            &lowering_state,
            obligation,
            assumptions,
        )
    }) {
        return Err(ClickError::new(format!(
            "{}{}",
            crate::surface::diagnostics::describe_missing_pure_fact(
                obligation,
                &[],
                &[],
                parameter_binding,
                &[],
            ),
            folded_matched_instance_note(&lowering_state, parameter_binding, assumptions)
        )));
    }
    // The kernel selected this lowering path, and every outstanding read
    // obligation was checked above. Its auxiliary facts include the checked
    // population lower bound; retaining them avoids losing ownership-derived
    // facts when the written requirement observes a count.
    let facts = { facts };
    Ok((lowered, facts))
}

pub(in crate::surface) fn parameter_values(
    parameter_binding: ParameterBinding<'_>,
) -> Result<BTreeMap<String, CValue>, ClickError> {
    parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .map(|(parameter, argument)| {
            let CExpression::Value(value) = argument else {
                return Err(ClickError::new(format!(
                    "could not build contract environment for parameter `{}`",
                    parameter.name()
                )));
            };
            Ok((parameter.name().to_string(), value.clone()))
        })
        .collect()
}

pub(in crate::surface) fn array_refs_for_parameters(
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    memory: &CMemory,
) -> ClickArrayRefs {
    parameters
        .iter()
        .filter_map(|parameter| {
            let element_type = click_array_element_type(parameter.c_type())?;
            let Some(CValue::Pointer(pointer)) = values.get(parameter.name()) else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ClickArrayRef {
                    memory: memory.clone(),
                    pointer: pointer.pointer().clone(),
                    element_type,
                },
            ))
        })
        .collect()
}

/// Capturing an argument preserves only its reference, never its current fields
/// or ownership. The retained scope also contains already transferred instances.
pub(in crate::surface) fn lower_resource_reference_arguments(
    resource: &ResourceClause,
    state: &CState,
) -> Result<Vec<crate::kernel::ResourceReference>, ClickError> {
    let ResourceClause::Declared {
        resource_arguments, ..
    } = resource
    else {
        return Ok(Vec::new());
    };
    resource_arguments
        .iter()
        .map(|binding| {
            crate::instrumentation::record_deterministic_work(1);
            state
                .resource_instance_fields(binding.identity)
                .map(crate::kernel::ResourceReference::from_instance)
                .ok_or_else(|| {
                    ClickError::new(format!("Requires resource reference `{}`", binding.name))
                })
        })
        .collect()
}

#[cfg(test)]
mod input_identity_tests {
    use super::*;

    #[test]
    fn pointer_field_input_naming_uses_complete_nonoverlapping_cells() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(crate::kernel::Variable(998_400));
        for (bytes, complete) in [(4, false), (8, true), (16, true)] {
            let ranges = BTreeMap::from([(
                "field".to_string(),
                ConcreteMemoryRangeSeed {
                    base: pointer.clone(),
                    bytes,
                    element_width: 4,
                    element_type: Some(CType::Int32Pointer),
                    observation_count: Some(1),
                    struct_layout: None,
                },
            )]);
            let memory = memory_with_symbolic_loadable_cells(CMemory::new(), &ranges);
            assert_eq!(
                matches!(
                    memory.load(&pointer),
                    CExpressionOutcome::Value(CValue::Pointer(_))
                ),
                complete
            );
            assert!(!matches!(
                memory.load(&pointer.offset_by_bytes(4)),
                CExpressionOutcome::Value(CValue::Pointer(_))
            ));
            assert!(!matches!(
                memory.load(&pointer.offset_by_bytes(8)),
                CExpressionOutcome::Value(CValue::Pointer(_))
            ));
        }
    }

    #[test]
    fn unprofiled_union_record_inputs_keep_legacy_enrollment_without_authority() {
        let ordinary = syntax::parse_function(
            "struct holder { int payload; int other; }; int probe(struct holder *p) { return p->other; }",
        ).unwrap();
        let overlapping = syntax::parse_function(
            "union bits { int value; long wide; }; struct holder { union bits payload; int other; }; int probe(struct holder *p) { return p->other; }",
        ).unwrap();
        for (parsed, unresolved) in [(&ordinary, false), (&overlapping, false)] {
            let (state, arguments) =
                initial_call_state(&[], parsed.parameters(), &parsed.to_kernel_function(), &[])
                    .unwrap();
            let CExpression::Value(CValue::Pointer(pointer)) = &arguments[0] else {
                panic!("record input");
            };
            assert_eq!(pointer.designation().is_some(), unresolved);
            if unresolved {
                assert!(matches!(
                    pointer.designation(),
                    Some(crate::kernel::PointerDesignation::Unresolved(_))
                ));
            }
            assert_eq!(state.memory(), &crate::kernel::CMemory::new());
            assert!(state.resources().facts().is_empty());
        }
        // An explicit authenticated native input remains strict even when a
        // declaration's overlapping geometry cannot be admitted by this profile.
        let parameters = vec![
            overlapping.parameters()[0]
                .clone()
                .with_native_pointer_input(true),
        ];
        let (_, arguments) =
            initial_call_state(&[], &parameters, &overlapping.to_kernel_function(), &[]).unwrap();
        let CExpression::Value(CValue::Pointer(pointer)) = &arguments[0] else {
            panic!("native input");
        };
        assert!(matches!(
            pointer.designation(),
            Some(crate::kernel::PointerDesignation::Unresolved(_))
        ));
        let mut layouts = overlapping.structs().clone();
        let holder = layouts
            .get("holder")
            .unwrap()
            .clone()
            .with_cpp_declaration_identity("authenticated-import", "c:@S@holder");
        layouts.insert("holder".to_string(), holder);
        let native = overlapping.clone().with_parameter_pointee_layouts(&layouts);
        let (_, arguments) =
            initial_call_state(&[], native.parameters(), &native.to_kernel_function(), &[])
                .unwrap();
        let CExpression::Value(CValue::Pointer(pointer)) = &arguments[0] else {
            panic!("authenticated record input");
        };
        assert!(matches!(
            pointer.designation(),
            Some(crate::kernel::PointerDesignation::Unresolved(_))
        ));
    }

    #[test]
    fn constructor_scalar_requirements_come_from_exact_typed_clauses() {
        let parsed =
            syntax::parse_function("void ctor(int* destination, int* slot) { return; }").unwrap();
        let raw = parsed.to_kernel_function();
        let function = raw.clone().with_construction_parameter(
            0,
            crate::kernel::CAggregateLayout::new(
                4,
                4,
                vec![crate::kernel::CAggregateField::new(
                    "value",
                    0,
                    CType::Int32,
                )],
            ),
        );
        assert!(
            scalar_object_inputs_for_contract(&[], parsed.parameters(), &function)
                .unwrap()
                .is_empty()
        );
        let file = crate::surface::parser::parse(
            "void ctor(int32* destination, int32* slot) { owns slot[0..1]; } by { execute(); }",
        )
        .unwrap();
        let requires = file.function_blocks()[0].requires();
        assert!(
            scalar_object_inputs_for_contract(requires, parsed.parameters(), &raw)
                .unwrap()
                .is_empty()
        );
        let inputs =
            scalar_object_inputs_for_contract(requires, parsed.parameters(), &function).unwrap();
        assert_eq!(
            inputs,
            vec![crate::kernel::CScalarObjectInput {
                parameter_index: 1,
                element_type: CType::Int32
            }]
        );
        let native = raw.with_scalar_object_inputs(inputs.clone());
        assert_eq!(
            scalar_object_inputs_for_contract(&[], parsed.parameters(), &native).unwrap(),
            inputs
        );
        let file = crate::surface::parser::parse(
            "void ctor(int32* destination, int32* slot) { owns slot[0..2]; } by { execute(); }",
        )
        .unwrap();
        assert!(
            scalar_object_inputs_for_contract(
                file.function_blocks()[0].requires(),
                parsed.parameters(),
                &function
            )
            .is_err()
        );
    }

    #[test]
    fn ordinary_record_inputs_require_unconditional_declared_member_paths() {
        let parsed = syntax::parse_function("struct Pair { int first; int second; }; int probe(struct Pair* pair) { return pair->second; }").unwrap();
        let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects(
            "int32 probe(struct Pair* pair) { views pair->second; } by { execute(); }",
            crate::surface::parser::ProgramLayouts {
                struct_layouts: parsed.structs().clone(),
                ..Default::default()
            },
        )
        .unwrap();
        let places = native_record_places_for_resource(
            match &file.function_blocks()[0].requires()[0] {
                Requirement::Resource(resource) => resource,
                _ => panic!("typed member resource"),
            },
            parsed.parameters(),
            parsed.structs(),
        )
        .unwrap();
        assert_eq!(places.len(), 1);
        assert_eq!(places[0].carrier, c_variable("pair"));
        let raw = parsed.to_kernel_function();
        let requires = file.function_blocks()[0].requires();
        let direct =
            aggregate_object_inputs_for_contract(requires, parsed.parameters(), &raw).unwrap();
        assert!(
            direct.is_empty(),
            "ordinary C member authority does not activate the native profile"
        );
        let native_parameters = parsed
            .parameters()
            .iter()
            .cloned()
            .map(|parameter| parameter.with_native_pointer_input(true))
            .collect::<Vec<_>>();
        let native =
            aggregate_object_inputs_for_contract(requires, &native_parameters, &raw).unwrap();
        assert_eq!(native.len(), 1);
        assert_eq!(native[0].parameter_index, 0);
        assert!(
            aggregate_object_inputs_for_contract(&[], parsed.parameters(), &raw)
                .unwrap()
                .is_empty()
        );
        let Requirement::Resource(resource) = &requires[0] else {
            panic!("member clause is a resource");
        };
        let guarded = Requirement::Resource(ResourceClause::Conditional {
            condition: ClickProposition::Comparison {
                left: ContractExpression::CFragment(c_int32_literal(1)),
                operator: ComparisonOperator::Equal,
                right: ContractExpression::CFragment(c_int32_literal(1)),
            },
            resource: Box::new(resource.clone()),
        });
        assert!(
            aggregate_object_inputs_for_contract(
                std::slice::from_ref(&guarded),
                parsed.parameters(),
                &raw
            )
            .unwrap()
            .is_empty()
        );
        let error = initial_call_state(
            std::slice::from_ref(&guarded),
            parsed.parameters(),
            &raw,
            &[],
        )
        .expect_err("conditional function-entry resources remain unsupported");
        assert!(
            error
                .message()
                .contains("conditional resource assertions are supported only in loop contracts")
        );
        let (_, arguments) = initial_call_state(&[], parsed.parameters(), &raw, &[]).unwrap();
        let CExpression::Value(CValue::Pointer(pointer)) = &arguments[0] else {
            panic!("record entry argument");
        };
        assert!(
            pointer.designation().is_none(),
            "an unprofiled C record is a legacy input"
        );
        let mut indexed = resource.clone();
        let ResourceClause::ViewMemory(segment) = &mut indexed else {
            panic!("direct view segment");
        };
        let base = match &mut segment.surface {
            ContractSegmentSurface::Range {
                base: ContractExpression::CUnary { operand, .. },
                ..
            } => {
                let ContractExpression::Field { base, .. } = operand.as_mut() else {
                    panic!("source field operand");
                };
                base
            }
            ContractSegmentSurface::Field {
                base: Some(base), ..
            } => base,
            _ => panic!("source member path is retained"),
        };
        **base = ContractExpression::Index(
            base.clone(),
            Box::new(ContractExpression::CFragment(c_int32_literal(0))),
        );
        assert!(
            aggregate_object_inputs_for_contract(
                &[Requirement::Resource(indexed)],
                parsed.parameters(),
                &raw
            )
            .unwrap()
            .is_empty()
        );
    }

    #[test]
    fn record_sequence_requirements_preserve_a_prefix_without_an_exact_array_extent() {
        let parsed = syntax::parse_function("struct cell { int value; int other; }; int read(struct cell *p, int count) { return p[1].other; }").unwrap();
        for (clause, admitted) in [
            ("views p[0..2];", true),
            ("views p[0..count];", true),
            ("views p[1..2];", false),
        ] {
            let source = format!(
                "int32 read(struct cell* p, int32 count) {{ {clause} }} by {{ execute(); }}"
            );
            let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects(
                &source,
                crate::surface::parser::ProgramLayouts {
                    struct_layouts: parsed.structs().clone(),
                    ..Default::default()
                },
            )
            .unwrap();
            let Requirement::Resource(resource) = &file.function_blocks()[0].requires()[0] else {
                panic!("record range");
            };
            let places =
                native_record_places_for_resource(resource, parsed.parameters(), parsed.structs())
                    .unwrap();
            assert_eq!(places.len(), usize::from(admitted), "{clause}");
            if admitted {
                assert_eq!(places[0].carrier, c_variable("p"));
                assert!(places[0].prefix_count.is_some());
                assert_eq!(places[0].layout.size_bytes(), 8);
            }
        }
    }

    #[test]
    fn declared_array_element_places_retain_their_source_member_path() {
        let parsed = syntax::parse_function("struct packet { int values[2][3]; }; int update(struct packet *p) { p->values[1][2] = 7; return p->values[1][2]; }").unwrap();
        let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects(
            "int32 update(struct packet* p) { owns p->values[1][2]; } by { execute(); }",
            crate::surface::parser::ProgramLayouts {
                struct_layouts: parsed.structs().clone(),
                ..Default::default()
            },
        )
        .unwrap();
        let Requirement::Resource(resource) = &file.function_blocks()[0].requires()[0] else {
            panic!("typed array element");
        };
        let ResourceClause::OwnMemory(segment) = resource else {
            panic!("owned element");
        };
        assert!(
            matches!(&segment.surface, ContractSegmentSurface::IndexedField { place, .. } if matches!(place.as_ref(), ContractExpression::Index(_, _)))
        );
        let places =
            native_record_places_for_resource(resource, parsed.parameters(), parsed.structs())
                .unwrap();
        assert_eq!(places.len(), 1);
        assert_eq!(places[0].carrier, c_variable("p"));
    }

    #[test]
    fn loaded_record_place_requirements_retain_the_exact_carrier() {
        let parsed = syntax::parse_function("struct node { int second; struct node *next; }; int probe(struct node *p) { return p->next->second; }").unwrap();
        let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects("int32 probe(struct node* p) { views p->next; views p->next->second; } by { execute(); }", crate::surface::parser::ProgramLayouts { struct_layouts: parsed.structs().clone(), ..Default::default() }).unwrap();
        let requirements = file.function_blocks()[0].requires();
        let places = |index: usize| {
            let Requirement::Resource(resource) = &requirements[index] else {
                panic!("typed resource");
            };
            native_record_places_for_resource(resource, parsed.parameters(), parsed.structs())
                .unwrap()
        };
        let slot = places(0);
        assert_eq!(
            slot.len(),
            1,
            "owning the pointer slot grants no referent validity"
        );
        assert_eq!(slot[0].carrier, c_variable("p"));
        let referent = places(1);
        assert_eq!(referent.len(), 2);
        assert_eq!(referent[0].carrier, c_variable("p"));
        assert!(
            matches!(referent[1].carrier, CExpression::TypedLoad { .. }),
            "the field read remains the semantic carrier"
        );
        assert_eq!(referent[0].layout, referent[1].layout);
        let object_file = crate::surface::parser::parse_with_layouts_and_aggregate_objects(
            "int32 probe(struct node* p) { views p->next; owns *p->next; } by { execute(); }",
            crate::surface::parser::ProgramLayouts {
                struct_layouts: parsed.structs().clone(),
                ..Default::default()
            },
        )
        .unwrap();
        let Requirement::Resource(resource) = &object_file.function_blocks()[0].requires()[1]
        else {
            panic!("whole loaded object");
        };
        let object_places =
            native_record_places_for_resource(resource, parsed.parameters(), parsed.structs())
                .unwrap();
        assert_eq!(object_places, referent);
    }

    #[test]
    fn callback_field_record_requirement_uses_the_declared_signature() {
        let parsed = syntax::parse_function(
            "struct callbacks { void (*propagate)(int *node, int *stop); }; int probe(const struct callbacks *p) { return 0; }",
        ).unwrap();
        let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects("resource suite(p: const struct callbacks*) { owns p->propagate; } int32 probe(const struct callbacks* p) { views suite(p); } by { execute(); }", crate::surface::parser::ProgramLayouts { struct_layouts: parsed.structs().clone(), ..Default::default() }).unwrap();
        let clause = &file.resource_definitions()[0]
            .composite_body()
            .unwrap()
            .contains()[0];
        let places =
            native_record_places_for_resource(clause, parsed.parameters(), parsed.structs())
                .unwrap();
        let layout = parsed.structs()["callbacks"].to_kernel_aggregate_layout();
        assert_eq!(places.len(), 1, "source={clause:?}, declared={layout:?}");
        assert_eq!(places[0].layout.as_ref(), &layout);
        assert!(matches!(
            layout.member_at_path(&["propagate".into()]),
            Some((0, CType::FunctionPointer(_)))
        ));
    }

    #[test]
    fn potential_matched_prefix_enrolls_identity_without_an_active_object() {
        use crate::kernel::{CResourceMatchArm, CResourceMatchBody};
        let parsed = syntax::parse_function("int probe(int *p) { return 0; }").unwrap();
        let span = CResourceSpec::owned_memory(crate::kernel::CMemorySegment::new(
            c_variable("input"),
            c_int32_literal(0),
            c_int32_literal(0),
        ))
        .with_native_span_requirements(vec![crate::kernel::CNativeSpanRequirement {
            access_policy: crate::kernel::CTypedAccessPolicy::NativeObjectOnly,
            carrier: c_variable("input"),
            element_type: CType::Int32,
            count: c_int32_literal(0),
        }]);
        let definition = CCompositeResourceDefinition::new(
            "ConditionalPrefix",
            vec![crate::kernel::c_parameter("input", CType::Int32Pointer)],
            None,
            false,
            vec![],
            vec![],
        )
        .with_resource_match_body(Some(CResourceMatchBody {
            field_index: 0,
            algebraic_type: crate::kernel::AlgebraicType::parameter("Inactive".into()),
            arms: vec![CResourceMatchArm {
                variant: "Inactive".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![span],
                facts: vec![],
                children: vec![],
            }],
        }));
        let head = CResourceSpec::declared(
            crate::kernel::ResourceFamily::Composite,
            crate::kernel::CResourceAccessMode::Own,
            "ConditionalPrefix".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
            crate::kernel::CResourceTransferRole::Consume,
            crate::kernel::CResourceSnapshot::Entry,
        )
        .unwrap();
        assert_eq!(
            native_span_input_parameters(
                parsed.parameters(),
                std::slice::from_ref(&head),
                std::slice::from_ref(&definition)
            ),
            BTreeSet::from([0])
        );
        let function = parsed
            .to_kernel_function()
            .with_resource_summary(vec![head], vec![]);
        let (state, arguments) =
            initial_call_state(&[], parsed.parameters(), &function, &[definition]).unwrap();
        assert_eq!(state.memory(), &CMemory::new());
        let CExpression::Value(CValue::Pointer(pointer)) = &arguments[0] else {
            panic!("pointer");
        };
        assert!(matches!(
            pointer.designation(),
            Some(crate::kernel::PointerDesignation::Unresolved(_))
        ));
    }

    #[test]
    fn scalar_prefix_entry_marks_only_exact_declared_formals_before_capture() {
        let parsed =
            syntax::parse_function("int probe(int *p, int *raw, long long *wide) { return p[1]; }")
                .unwrap();
        let file = crate::surface::parser::parse(
            "int32 probe(int32* p, int32* raw, int64* wide) { views p[0..2]; } by { execute(); }",
        )
        .unwrap();
        let span = crate::kernel::CNativeSpanRequirement {
            access_policy: crate::kernel::CTypedAccessPolicy::NativeObjectOnly,
            carrier: c_variable("p"),
            element_type: CType::Int32,
            count: c_int32_literal(2),
        };
        let spec = CResourceSpec::viewed_memory(
            crate::kernel::CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(2),
            )
            .with_element_width(4),
        )
        .with_native_span_requirements(vec![span.clone()]);
        let function = parsed
            .to_kernel_function()
            .with_resource_summary(vec![spec.clone()], vec![]);
        let (state, arguments) = initial_call_state(
            file.function_blocks()[0].requires(),
            parsed.parameters(),
            &function,
            &[],
        )
        .unwrap();
        let values =
            parameter_values(ParameterBinding::new(parsed.parameters(), &arguments)).unwrap();
        for (index, parameter) in parsed.parameters().iter().enumerate() {
            let CExpression::Value(CValue::Pointer(pointer)) = &arguments[index] else {
                panic!("pointer input");
            };
            assert_eq!(values[parameter.name()], CValue::Pointer(pointer.clone()));
            if index == 0 {
                assert!(matches!(
                    pointer.designation(),
                    Some(crate::kernel::PointerDesignation::Unresolved(_))
                ));
                let offset =
                    CExpression::Add(Box::new(c_variable("p")), Box::new(c_int32_literal(1)));
                let evaluation = state
                    .clone()
                    .with_local("p", CValue::Pointer(pointer.clone()));
                let theorem = crate::kernel::prove_c_expression_evaluation(evaluation, offset)
                    .expect("admitted scalar prefix permits the selected native element step");
                assert!(
                    matches!(
                        theorem.proposition(),
                        crate::kernel::Proposition::CExpressionEvaluates {
                            outcome: crate::kernel::CExpressionOutcome::Value(CValue::Pointer(_)),
                            ..
                        }
                    ),
                    "{:?}",
                    theorem.proposition()
                );
            } else {
                assert!(pointer.designation().is_none());
            }
        }
        assert_eq!(state.resources().facts().len(), 1);
        assert_eq!(
            native_span_input_parameters(parsed.parameters(), &[spec], &[]),
            BTreeSet::from([0])
        );
        for carrier in [
            c_variable("wide"),
            CExpression::PointerOffsetBytes {
                pointer: Box::new(c_variable("raw")),
                bytes: 0,
            },
        ] {
            let wrong = CResourceSpec::viewed_memory(crate::kernel::CMemorySegment::new(
                c_variable("raw"),
                c_int32_literal(0),
                c_int32_literal(2),
            ))
            .with_native_span_requirements(vec![
                crate::kernel::CNativeSpanRequirement {
                    access_policy: crate::kernel::CTypedAccessPolicy::NativeObjectOnly,
                    carrier,
                    ..span.clone()
                },
            ]);
            assert!(native_span_input_parameters(parsed.parameters(), &[wrong], &[]).is_empty());
        }
        assert!(native_span_input_parameters(parsed.parameters(), &[], &[]).is_empty());
    }

    #[test]
    fn scalar_constant_start_ranges_preserve_the_required_end_prefix() {
        let parsed = syntax::parse_function("int32 probe(int32* p) { return 0; }").unwrap();
        let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects("int32 probe(int32* p) { owns p[0..1]; owns p[1..2]; views p[4..5]; views p[2..2]; } by { execute(); }", crate::surface::parser::ProgramLayouts { ..Default::default() }).unwrap();
        let mut spans = Vec::new();
        for requirement in file.function_blocks()[0].requires() {
            let Requirement::Resource(resource) = requirement else {
                continue;
            };
            spans.extend(
                native_span_requirements_for_resource(
                    resource,
                    parsed.parameters(),
                    parsed.structs(),
                )
                .unwrap(),
            );
        }
        assert_eq!(
            spans
                .iter()
                .map(|span| span.count.clone())
                .collect::<Vec<_>>(),
            vec![c_int32_literal(1), c_int32_literal(2), c_int32_literal(5)]
        );
        for span in spans {
            assert_eq!(span.carrier, c_variable("p"));
            assert_eq!(span.element_type, CType::Int32);
            assert_eq!(
                span.access_policy,
                crate::kernel::CTypedAccessPolicy::CAllocatedAccessAllowed
            );
        }
    }

    #[test]
    fn loaded_scalar_prefix_entry_selects_the_declared_pointer_field() {
        let parsed = syntax::parse_function(
            "struct holder { int *pointer; }; int probe(struct holder *h) { return *h->pointer; }",
        )
        .unwrap();
        let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects("int32 probe(struct holder* h) { views h->pointer; views h->pointer[0..1]; } by { execute(); }", crate::surface::parser::ProgramLayouts { struct_layouts: parsed.structs().clone(), ..Default::default() }).unwrap();
        let Requirement::Resource(resource) = &file.function_blocks()[0].requires()[1] else {
            panic!("referent resource");
        };
        let spans =
            native_span_requirements_for_resource(resource, parsed.parameters(), parsed.structs())
                .unwrap();
        let CExpression::TypedLoad {
            pointer,
            value_type,
            ..
        } = &spans[0].carrier
        else {
            panic!("pointer field read");
        };
        assert_eq!(*value_type, CType::Int32Pointer);
        let CExpression::MemberAddress { object, selection } = pointer.as_ref() else {
            panic!("checked declaration path");
        };
        assert_eq!(object.as_ref(), &c_variable("h"));
        assert_eq!(selection.path(), &["pointer".to_string()]);
        let spec = CResourceSpec::viewed_memory(
            crate::kernel::CMemorySegment::new(
                spans[0].carrier.clone(),
                c_int32_literal(0),
                c_int32_literal(1),
            )
            .with_element_width(4),
        )
        .with_native_span_requirements(spans);
        let function = parsed
            .to_kernel_function()
            .with_resource_summary(vec![spec], vec![]);
        let (state, _) = initial_call_state(
            file.function_blocks()[0].requires(),
            parsed.parameters(),
            &function,
            &[],
        )
        .unwrap();
        assert_eq!(state.resources().facts().len(), 2);
    }

    #[test]
    fn source_typed_prefix_policy_distinguishes_c_and_native_parameters() {
        let parsed = syntax::parse_function("void probe(int *p) { return; }").unwrap();
        let file = crate::surface::parser::parse(
            "void probe(int32* p) { views p[0..1]; } by { execute(); }",
        )
        .unwrap();
        let Requirement::Resource(resource) = &file.function_blocks()[0].requires()[0] else {
            panic!("typed prefix");
        };
        let c =
            native_span_requirements_for_resource(resource, parsed.parameters(), parsed.structs())
                .unwrap();
        let native_parameters: Vec<_> = parsed
            .parameters()
            .iter()
            .cloned()
            .map(|parameter| parameter.with_native_pointer_input(true))
            .collect();
        let native =
            native_span_requirements_for_resource(resource, &native_parameters, parsed.structs())
                .unwrap();
        assert_eq!(
            c[0].access_policy,
            crate::kernel::CTypedAccessPolicy::CAllocatedAccessAllowed
        );
        assert_eq!(
            native[0].access_policy,
            crate::kernel::CTypedAccessPolicy::NativeObjectOnly
        );
        assert_ne!(c, native);
    }

    #[test]
    fn scalar_prefix_literal_counts_keep_wide_native_extent_without_allocating_cells() {
        let parsed = syntax::parse_function("void probe(int *p) { return; }").unwrap();
        let limit = i64::MAX as u64 / 4;
        for (count, admitted) in [
            (u64::from(u32::MAX), true),
            (limit, true),
            (limit + 1, false),
            (u64::MAX, false),
        ] {
            // Exercise only source parsing and metadata production. Prefixes
            // describe a validity premise, not per-element storage allocation.
            let source =
                format!("void probe(int32* p) {{ views p[0..{count}u64]; }} by {{ execute(); }}");
            let file = crate::surface::parser::parse(&source).unwrap();
            let Requirement::Resource(resource) = &file.function_blocks()[0].requires()[0] else {
                panic!("native prefix resource");
            };
            let spans = native_span_requirements_for_resource(
                resource,
                parsed.parameters(),
                parsed.structs(),
            )
            .unwrap();
            assert_eq!(spans.len(), usize::from(admitted), "{count}");
            if admitted {
                assert_eq!(spans[0].carrier, c_variable("p"));
                assert_eq!(spans[0].element_type, CType::Int32);
                assert_eq!(
                    spans[0].count,
                    CExpression::Value(CValue::UInt64(Bitvector32Term::UInt64Constant(count))),
                );
            }
        }
    }

    #[test]
    fn scalar_prefix_requirements_retain_exact_native_symbolic_counts() {
        let parsed = syntax::parse_function(
            "struct holder { int *pointer; int capacity; }; int probe(struct holder *h, int *p, int count) { return count; }",
        ).unwrap();
        let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects("int32 probe(struct holder* h, int32* p, int32 count) { views p[0..count]; views h->pointer[0..h->capacity]; views p[1..count]; } by { execute(); }", crate::surface::parser::ProgramLayouts { struct_layouts: parsed.structs().clone(), ..Default::default() }).unwrap();
        let spans = file.function_blocks()[0]
            .requires()
            .iter()
            .map(|requirement| {
                let Requirement::Resource(resource) = requirement else {
                    panic!("resource range");
                };
                native_span_requirements_for_resource(
                    resource,
                    parsed.parameters(),
                    parsed.structs(),
                )
                .unwrap()
            })
            .collect::<Vec<_>>();
        assert_eq!(spans[0].len(), 1);
        assert_eq!(spans[0][0].carrier, c_variable("p"));
        assert_eq!(spans[0][0].count, c_variable("count"));
        assert_eq!(spans[1].len(), 1);
        assert!(matches!(
            spans[1][0].carrier,
            CExpression::TypedLoad {
                value_type: CType::Int32Pointer,
                ..
            }
        ));
        assert!(matches!(
            spans[1][0].count,
            CExpression::TypedLoad {
                value_type: CType::Int32,
                ..
            }
        ));
        assert!(spans[2].is_empty());
    }

    #[test]
    fn scalar_prefix_requirements_use_declared_pointer_types_and_positive_literals() {
        let parsed = syntax::parse_function("struct holder { int *pointer; }; int probe(struct holder *h, int *p, char *bytes) { return h->pointer[0]; }").unwrap();
        for (clause, count, loaded) in [
            ("views h->pointer[0..1];", 1, true),
            ("owns p[0..2];", 1, false),
            ("views p[1];", 1, false),
            ("views *p;", 1, false),
            ("views bytes[0..2];", 0, false),
            ("views p[0..0];", 0, false),
            ("views p[1..2];", 1, false),
        ] {
            let source = format!(
                "int32 probe(struct holder* h, int32* p, uint8* bytes) {{ {clause} }} by {{ execute(); }}"
            );
            let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects(
                &source,
                crate::surface::parser::ProgramLayouts {
                    struct_layouts: parsed.structs().clone(),
                    ..Default::default()
                },
            )
            .unwrap();
            let Requirement::Resource(resource) = &file.function_blocks()[0].requires()[0] else {
                panic!("resource clause");
            };
            let spans = native_span_requirements_for_resource(
                resource,
                parsed.parameters(),
                parsed.structs(),
            )
            .unwrap();
            assert_eq!(spans.len(), count, "{clause}");
            if count != 0 {
                assert_eq!(
                    spans[0].element_type,
                    if clause.contains("bytes") {
                        CType::UInt8
                    } else {
                        CType::Int32
                    }
                );
                assert_eq!(
                    matches!(spans[0].carrier, CExpression::TypedLoad { .. }),
                    loaded
                );
            }
        }
    }

    #[test]
    fn byte_prefix_enrollment_requires_an_authenticated_cpp_declaration() {
        let parsed = syntax::parse_function(
            "struct holder { unsigned char *pointer; }; int probe(struct holder *h, unsigned char *bytes) { return 0; }",
        ).unwrap();
        let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects("int32 probe(struct holder* h, uint8* bytes) { views bytes[0..2]; views h->pointer[0..2]; } by { execute(); }", crate::surface::parser::ProgramLayouts { struct_layouts: parsed.structs().clone(), ..Default::default() }).unwrap();
        let resources = file.function_blocks()[0]
            .requires()
            .iter()
            .map(|requirement| {
                let Requirement::Resource(resource) = requirement else {
                    panic!("resource clause");
                };
                resource
            })
            .collect::<Vec<_>>();
        for resource in &resources {
            assert!(
                native_span_requirements_for_resource(
                    resource,
                    parsed.parameters(),
                    parsed.structs(),
                )
                .unwrap()
                .is_empty(),
                "C character storage is not a typed byte array promise"
            );
        }
        let mut parameters = parsed.parameters().to_vec();
        parameters[1] = parameters[1].clone().with_native_pointer_input(true);
        let direct =
            native_span_requirements_for_resource(resources[0], &parameters, parsed.structs())
                .unwrap();
        assert_eq!(direct.len(), 1);
        assert_eq!(direct[0].element_type, CType::UInt8);
        assert_eq!(direct[0].carrier, c_variable("bytes"));
        assert!(
            native_span_requirements_for_resource(resources[1], &parameters, parsed.structs(),)
                .unwrap()
                .is_empty(),
            "a native formal does not authenticate a C record field"
        );
        let mut layouts = parsed.structs().clone();
        let holder = layouts
            .get("holder")
            .unwrap()
            .clone()
            .with_cpp_declaration_identity("authenticated-import", "c:@S@holder");
        layouts.insert("holder".to_string(), holder);
        let field =
            native_span_requirements_for_resource(resources[1], parsed.parameters(), &layouts)
                .unwrap();
        assert_eq!(field.len(), 1);
        assert_eq!(field[0].element_type, CType::UInt8);
        assert!(matches!(
            field[0].carrier,
            CExpression::TypedLoad {
                value_type: CType::UInt8Pointer,
                ..
            }
        ));
    }

    #[test]
    fn input_pointer_places_are_exact_and_do_not_scan_unrelated_functions() {
        let selected = input_scope("certificate-selected");
        let variable = input_pointer_variable(selected, 1).unwrap();
        let pointer = crate::kernel::CPointerValue::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: scale_int32_offset(Bitvector32Term::Variable(variable), 4),
            },
            CType::Int32Pointer,
        );
        INPUT_POINTER_PLACES.with(|places| {
            places
                .borrow_mut()
                .insert(variable, (selected, 1, pointer.clone()));
        });
        for size in [16, 64, 256] {
            for index in 0..size {
                let scope = input_scope(&format!("certificate-unrelated-{index}"));
                let other = input_pointer_variable(scope, 0).unwrap();
                let mut value = pointer.clone();
                value.replace_pointer(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: scale_int32_offset(Bitvector32Term::Variable(other), 4),
                });
                INPUT_POINTER_PLACES.with(|places| {
                    places.borrow_mut().insert(other, (scope, 0, value));
                });
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..64 {
                    assert_eq!(input_pointer_parameter(selected, &pointer), Some(1));
                }
            });
            assert_eq!(work, 64, "unrelated input count: {size}");
        }
        assert_eq!(
            input_pointer_parameter(input_scope("certificate-other"), &pointer),
            None
        );
        assert_eq!(
            input_pointer_parameter(selected, &pointer.clone().with_type(CType::Int8Pointer)),
            None
        );
        let mut wrong_stride = pointer.clone();
        wrong_stride.replace_pointer(Pointer {
            block: PointerBlock::ExternalArgument,
            offset: scale_int32_offset(Bitvector32Term::Variable(variable), 1),
        });
        assert_eq!(input_pointer_parameter(selected, &wrong_stride), None);
        let mut unknown = pointer;
        unknown.replace_pointer(Pointer {
            block: PointerBlock::ExternalArgument,
            offset: scale_int32_offset(Bitvector32Term::Variable(Variable(999_999)), 4),
        });
        assert_eq!(input_pointer_parameter(selected, &unknown), None);
    }

    #[test]
    fn pointer_input_names_are_stable_and_function_specific() {
        let first = input_scope("input-identity-first");
        let second = input_scope("input-identity-second");
        assert_eq!(
            input_pointer_variable(first, 0).unwrap(),
            input_pointer_variable(input_scope("input-identity-first"), 0).unwrap()
        );
        assert_ne!(
            input_pointer_variable(first, 0).unwrap(),
            input_pointer_variable(first, 1).unwrap()
        );
        assert!(
            input_pointer_variable(first, 0).unwrap() < input_pointer_variable(first, 1).unwrap()
        );
        assert_ne!(
            input_pointer_variable(first, 0).unwrap(),
            input_pointer_variable(second, 0).unwrap()
        );
    }
}

#[cfg(test)]
mod global_native_place_metadata_tests {
    use super::*;

    #[test]
    fn global_loaded_pointer_requires_its_explicit_typed_place_guarantee() {
        let source = "int32 value = 7; int32* alias = &value; int32 probe() { return *alias; }";
        let positive = "verifying \"global.c\"; int32 probe() { owns alias[0]; ensures result == old(alias[0]); } by { execute(); simp(); }";
        crate::surface::verify_c0_sources(positive, &[("global.c", source)])
            .expect("an explicit global pointer place supplies typed validity and its permission");
        for requirements in ["", "requires alias == &value;"] {
            let proof = format!(
                "verifying \"global.c\"; int32 probe() {{ {requirements} ensures result == result; }} by {{ execute(); simp(); }}"
            );
            let error = crate::surface::verify_c0_sources(&proof, &[("global.c", source)])
                .expect_err(
                    "a global pointer declaration or address equality cannot grant a referent",
                );
            assert!(
                error.message().contains("invalid memory access")
                    || error.message().contains("missing resource fact"),
                "{}",
                error.message()
            );
        }
    }

    #[test]
    fn explicit_global_pointer_range_uses_the_actual_declaration_without_adding_parameters() {
        let parsed = syntax::parse_function(
            "const int32* const alias = 0; int32 probe() { return *alias; }",
        )
        .unwrap();
        let declarations = parsed.native_resource_pointer_declarations();
        let declaration = declarations
            .iter()
            .find(|declaration| declaration.name() == "alias")
            .unwrap();
        assert_eq!(declaration.c_type(), syntax::C0Type::Int32Pointer);
        assert!(declaration.is_constant());
        assert!(declaration.pointee_is_constant());
        assert!(parsed.parameters().is_empty());
        assert!(parsed.to_kernel_function().parameters().is_empty());
        let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects(
            "int32 probe(int32* alias, int32* undeclared) { views alias[0..1]; views undeclared[0..1]; requires alias == undeclared; } by { execute(); }",
            Default::default(),
        ).unwrap();
        let resources = file.function_blocks()[0]
            .requires()
            .iter()
            .filter_map(|requirement| {
                if let Requirement::Resource(resource) = requirement {
                    Some(resource)
                } else {
                    None
                }
            })
            .collect::<Vec<_>>();
        let spans =
            native_span_requirements_for_resource(resources[0], &declarations, parsed.structs())
                .unwrap();
        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].carrier, c_variable("alias"));
        assert_eq!(spans[0].element_type, CType::Int32);
        assert_eq!(
            spans[0].access_policy,
            crate::kernel::CTypedAccessPolicy::CAllocatedAccessAllowed
        );
        assert!(
            native_span_requirements_for_resource(resources[1], &declarations, parsed.structs())
                .unwrap()
                .is_empty()
        );
        assert!(
            native_span_requirements_for_resource(
                resources[0],
                parsed.parameters(),
                parsed.structs()
            )
            .unwrap()
            .is_empty()
        );
    }
}

#[cfg(test)]
#[test]
fn parsed_record_pointer_field_keeps_declared_storage_type_during_entry_naming() {
    let parsed = syntax::parse_function("struct Node { int* self; int value; }; int probe(struct Node* target, const struct Node* source) { return 0; }").unwrap();
    let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects(
        "int32 probe(struct Node* target, const struct Node* source) { owns target->self; owns target->value; views source->self; views source->value; } by { execute(); }",
        crate::surface::parser::ProgramLayouts { struct_layouts: parsed.structs().clone(), ..Default::default() },
    ).unwrap();
    let parameters = parsed.parameters();
    let arguments = vec![
        CExpression::Value(CValue::typed_pointer(
            Pointer::symbolic(Variable(991_200)),
            CType::Int32Pointer,
        )),
        CExpression::Value(CValue::typed_pointer(
            Pointer::symbolic(Variable(991_201)),
            CType::Int32Pointer,
        )),
    ];
    let requirements = file.function_blocks()[0].requires();
    for index in [0usize, 2] {
        let Requirement::Resource(resource) = &requirements[index] else {
            panic!("field resource");
        };
        let seeds = concrete_access_resource_blocks(
            resource,
            ParameterBinding::new(parameters, &arguments),
        )
        .unwrap();
        let [(_, seed)] = seeds.as_slice() else {
            panic!("one selected leaf seed");
        };
        let base = seed.base.clone();
        assert_eq!(seed.element_type, Some(CType::Int32Pointer));
        assert_eq!(seed.bytes, 8);
        let named = memory_with_symbolic_loadable_cells(
            CMemory::new(),
            &seeds.into_iter().collect::<BTreeMap<_, _>>(),
        );
        let CExpressionOutcome::Value(value) = named.load(&base) else {
            panic!("selected pointer cell");
        };
        assert_eq!(value.c_type(), CType::Int32Pointer);
        assert!(matches!(
            named.load(&base.offset_by_bytes(4)),
            CExpressionOutcome::UndefinedBehavior(crate::kernel::CUndefinedBehavior::InvalidMemory)
        ));
    }
    // The value clause owns its ABI tail padding, but only the one declared
    // scalar field supplies an input value; padding remains unnamed.
    let Requirement::Resource(resource) = &requirements[1] else {
        panic!("scalar field");
    };
    let seeds =
        concrete_access_resource_blocks(resource, ParameterBinding::new(parameters, &arguments))
            .unwrap();
    let base = seeds[0].1.base.clone();
    assert_eq!(seeds[0].1.observation_count, Some(1));
    let named = memory_with_symbolic_loadable_cells(
        CMemory::new(),
        &seeds.into_iter().collect::<BTreeMap<_, _>>(),
    );
    let CExpressionOutcome::Value(value) = named.load(&base) else {
        panic!("selected scalar cell");
    };
    assert_eq!(value.c_type(), CType::Int32);
    assert!(matches!(
        named.load(&base.offset_by_bytes(4)),
        CExpressionOutcome::UndefinedBehavior(crate::kernel::CUndefinedBehavior::InvalidMemory)
    ));
}

#[cfg(test)]
mod embedded_reference_span_metadata_tests {
    use super::*;

    #[test]
    fn nested_reference_pointer_prefix_selects_declared_record_before_loaded_leaf() {
        let child = syntax::C0StructLayout::from_explicit_fields(
            vec![("pointer".to_string(), syntax::C0Type::Int32Pointer, 0, 8)],
            8,
            8,
        )
        .unwrap()
        .with_cpp_declaration_identity("reference-fixture", "Child");
        let mut layouts = BTreeMap::from([("Child".to_string(), child)]);
        let outer = syntax::C0StructLayout::from_explicit_fields_with_structs(
            vec![
                (
                    "child".to_string(),
                    syntax::C0Type::Int32,
                    Some("Child".to_string()),
                    0,
                    8,
                ),
                ("stamp".to_string(), syntax::C0Type::Int32, None, 8, 4),
            ],
            16,
            8,
            &layouts,
        )
        .unwrap()
        .with_cpp_declaration_identity("reference-fixture", "Outer");
        layouts.insert("Outer".to_string(), outer.clone());
        let parameter = syntax::C0Parameter::new(
            syntax::C0Type::Int32Pointer,
            syntax::reference_carrier_name("state"),
            None,
        )
        .with_pointee_struct_layout("Outer".to_string(), outer)
        .with_reference(true)
        .with_pointee_constant(true)
        .with_native_pointer_input(true);
        let file = crate::surface::parser::parse_with_layouts_and_aggregate_objects(
            "int32 probe(const struct Outer& state) { views state.child.pointer; views state.child.pointer[0..1]; } by { execute(); }",
            crate::surface::parser::ProgramLayouts { struct_layouts: layouts.clone(), ..Default::default() },
        ).unwrap();
        let Requirement::Resource(resource) = &file.function_blocks()[0].requires()[1] else {
            panic!("pointer prefix");
        };
        let spans = native_span_requirements_for_resource(
            resource,
            std::slice::from_ref(&parameter),
            &layouts,
        )
        .unwrap();
        assert_eq!(spans.len(), 1);
        assert_eq!(spans[0].element_type, CType::Int32);
        assert_eq!(
            spans[0].access_policy,
            crate::kernel::CTypedAccessPolicy::NativeObjectOnly
        );
        let CExpression::TypedLoad {
            pointer,
            value_type,
            pointee_constant,
            ..
        } = &spans[0].carrier
        else {
            panic!("declared pointer leaf");
        };
        assert_eq!(*value_type, CType::Int32Pointer);
        assert!(!pointee_constant);
        let CExpression::MemberAddress { object, selection } = pointer.as_ref() else {
            panic!("leaf selection");
        };
        assert_eq!(selection.path(), &["pointer".to_string()]);
        let CExpression::MemberAddress {
            object: root,
            selection,
        } = object.as_ref()
        else {
            panic!("embedded record address");
        };
        assert_eq!(root.as_ref(), &c_variable("&state"));
        assert_eq!(selection.path(), &["child".to_string()]);
        assert_eq!(selection.value_type(), CType::UInt8Array(8));
        assert!(parameter.is_reference());
        assert!(parameter.pointee_is_constant());
        assert!(
            native_span_requirements_for_resource(resource, &[], &layouts)
                .unwrap()
                .is_empty()
        );
    }
}
