use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::lang::click) struct ConcreteMemoryRangeSeed {
    pub(in crate::lang::click) base: Pointer,
    pub(in crate::lang::click) bytes: u32,
    pub(in crate::lang::click) element_width: u32,
}

pub(in crate::lang::click) fn initial_call_state(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
) -> Result<(CState, Vec<CExpression>), ClickError> {
    let mut arguments = Vec::new();

    for (index, parameter) in parameters.iter().enumerate() {
        match parameter.c_type() {
            C0Type::Void => {
                return Err(ClickError::new(format!(
                    "parameter `{}` cannot have type void",
                    parameter.name()
                )));
            }
            C0Type::Int32Pointer => {
                arguments.push(c_pointer_value(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        4,
                    ),
                }));
            }
            C0Type::UInt8Pointer => {
                arguments.push(c_pointer_value(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        1,
                    ),
                }));
            }
            C0Type::Int32 => {
                arguments.push(CExpression::Value(CValue::Int32(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::UInt8 => {
                arguments.push(CExpression::Value(CValue::UInt8(
                    Bitvector32Term::Variable(Variable(arguments.len() as u64)),
                )));
            }
            C0Type::Int32Array(_) | C0Type::UInt8Array(_) => {
                return Err(ClickError::new(format!(
                    "array parameter `{}` should have lowered to a pointer",
                    parameter.name()
                )));
            }
        }
    }

    let mut loadable_ranges = BTreeMap::new();
    for requirement in requires {
        if let Some((name, bytes)) = concrete_loadable_block(requirement, parameters, &arguments)? {
            loadable_ranges.insert(name, bytes);
        }
        if let Requirement::Resource(resource) = requirement.inner()
            && let Some((name, bytes)) =
                concrete_access_resource_block(resource, parameters, &arguments)?
        {
            loadable_ranges.insert(name, bytes);
        }
    }

    let mut memory = CMemory::new();
    memory = memory_with_symbolic_loadable_cells(memory, &loadable_ranges);
    memory = materialize_symbolic_access_resource_cells(memory, requires, parameters, &arguments)?;
    let resources = resource_context_from_requirements(requires, parameters, &arguments, &memory)?;
    Ok((
        CState::new()
            .with_memory(memory)
            .with_resource_context(resources),
        arguments,
    ))
}

pub(in crate::lang::click) fn memory_with_symbolic_loadable_cells(
    mut memory: CMemory,
    loadable_ranges: &BTreeMap<String, ConcreteMemoryRangeSeed>,
) -> CMemory {
    let base_memory = memory.clone();
    for range in loadable_ranges.values() {
        let mut offset: u32 = 0;
        match range.element_width {
            1 => {
                while offset < range.bytes {
                    let pointer = offset_pointer_by_elements(
                        range.base.clone(),
                        Bitvector32Term::Constant(offset),
                        1,
                    );
                    let value = CValue::UInt8(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(base_memory.clone()),
                        Box::new(pointer.clone()),
                    ));
                    memory = memory.store(pointer, value);
                    offset += 1;
                }
            }
            _ => {
                while offset.checked_add(4).is_some_and(|end| end <= range.bytes) {
                    let pointer = offset_pointer_by_int32_elements(
                        range.base.clone(),
                        Bitvector32Term::Constant(offset / 4),
                    );
                    let value = CValue::Int32(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(base_memory.clone()),
                        Box::new(pointer.clone()),
                    ));
                    memory = memory.store(pointer, value);
                    offset += 4;
                }
            }
        }
    }
    memory
}

fn materialize_symbolic_access_resource_cells(
    mut memory: CMemory,
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<CMemory, ClickError> {
    for requirement in requires {
        let Requirement::Resource(ResourceClause::Read(segment) | ResourceClause::Write(segment)) =
            requirement.inner()
        else {
            continue;
        };
        memory = materialize_access_segment_cells(memory, segment, parameters, arguments)?;
    }
    Ok(memory)
}

fn materialize_access_segment_cells(
    mut memory: CMemory,
    segment: &ContractSegment,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<CMemory, ClickError> {
    let state = CState::new().with_memory(memory.clone());
    let Ok(segment) = evaluate_requirement_segment(parameters, arguments, &state, segment) else {
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

    let element_width = contract_segment_element_width(parameters, &segment.source);
    let base_memory = memory.clone();
    for index in *start..*end {
        let pointer = offset_pointer_by_elements(
            segment.base.clone(),
            Bitvector32Term::Constant(index),
            element_width,
        );
        if matches!(memory.load(&pointer), CExpressionOutcome::Value(_)) {
            continue;
        }
        let load = Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(base_memory.clone()),
            Box::new(pointer.clone()),
        );
        let value = match element_width {
            1 => CValue::UInt8(load),
            _ => CValue::Int32(load),
        };
        memory = memory.store(pointer, value);
    }
    Ok(memory)
}

pub(in crate::lang::click) fn requirement_propositions(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<Proposition>, ClickError> {
    let mut propositions = Vec::new();
    for requirement in requires {
        let proposition = match requirement.inner() {
            Requirement::LoadableSegment { .. } => {
                loadable_requirement_prop(requirement, parameters, arguments, memory)?
            }
            Requirement::Proposition(proposition) => requirement_proposition_prop(
                parameters,
                arguments,
                memory,
                proposition,
                predicate_environment,
                click_function_environment,
            )?,
            Requirement::Resource(resource) => {
                let Some(proposition) =
                    resource_clause_loadable_prop(resource, parameters, arguments, memory)?
                else {
                    continue;
                };
                proposition
            }
            Requirement::Labeled { .. } => unreachable!("requirement.inner() removes labels"),
        };
        propositions.push(proposition);
    }
    Ok(propositions)
}

pub(in crate::lang::click) fn resource_context_from_requirements(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<ResourceContext, ClickError> {
    let mut context = ResourceContext::new();
    for requirement in requires {
        if let Requirement::Resource(resource) = requirement.inner() {
            // This lowering path has no proposition assumptions yet. It builds
            // a provisional context; execution paths use checked composition
            // once assumptions are available.
            context = context.unchecked_with_fact(lower_resource_clause(
                resource, parameters, arguments, memory,
            )?);
        }
    }
    Ok(context)
}

pub(in crate::lang::click) fn lower_resource_clause(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<CResourceFact, ClickError> {
    let values =
        parameter_values(parameters, arguments).map_err(|error| ClickError::new(error.message))?;
    let state = CState::new().with_memory(memory.clone());
    lower_resource_clause_with_values(resource, &values, &state, None)
}

pub(in crate::lang::click) fn lower_resource_clause_at_state(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
) -> Result<CResourceFact, ClickError> {
    let mut values =
        parameter_values(parameters, arguments).map_err(|error| ClickError::new(error.message))?;
    values.extend(
        state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone())),
    );
    lower_resource_clause_with_values(resource, &values, state, None)
}

pub(in crate::lang::click) fn lower_resource_clause_at_state_with_result(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    result: &CValue,
) -> Result<CResourceFact, ClickError> {
    let mut values =
        parameter_values(parameters, arguments).map_err(|error| ClickError::new(error.message))?;
    values.extend(
        state
            .locals()
            .object_values()
            .map(|(name, value)| (name.to_string(), value.clone())),
    );
    lower_resource_clause_with_values(resource, &values, state, Some(result))
}

fn lower_resource_clause_with_values(
    resource: &ResourceClause,
    values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CResourceFact, ClickError> {
    match resource {
        ResourceClause::Read(segment) => {
            let range = lower_resource_segment_with_values("read", segment, values, state, result)?;
            Ok(CResourceFact::view_memory(range))
        }
        ResourceClause::Write(segment) => {
            let range =
                lower_resource_segment_with_values("write", segment, values, state, result)?;
            Ok(CResourceFact::own_memory(range))
        }
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments: resource_arguments,
            parameter_types,
        } => {
            let assumptions = Assumptions::new();
            let mut resource_values = Vec::new();
            if resource_arguments.len() != parameter_types.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` has malformed argument type metadata"
                )));
            }
            for (index, (argument, parameter_type)) in
                resource_arguments.iter().zip(parameter_types).enumerate()
            {
                let argument = resource_argument_to_c_expression(argument)?;
                let value =
                    evaluate_c_contract_expression(values, state, result, &assumptions, &argument)
                        .map_err(|message| {
                            ClickError::new(format!(
                                "could not lower resource `{name}` argument {index}: {message}"
                            ))
                        })?;
                if !c_value_matches_click_type(&value, *parameter_type) {
                    return Err(ClickError::new(format!(
                        "resource `{name}` argument {index} evaluated to {value:?}, which does not match {:?}",
                        parameter_type
                    )));
                }
                resource_values.push(value);
            }
            let resource = match kind {
                ResourceKind::Composite => CResource::Composite {
                    name: name.clone(),
                    arguments: resource_values,
                },
                ResourceKind::Token => CResource::Token {
                    name: name.clone(),
                    arguments: resource_values,
                },
            };
            Ok(match access {
                ResourceAccessMode::Own => CResourceFact::Own(resource),
                ResourceAccessMode::View => CResourceFact::View(resource),
            })
        }
    }
}

pub(in crate::lang::click) fn resource_argument_to_c_expression(
    argument: &ContractExpression,
) -> Result<CExpression, ClickError> {
    match argument {
        ContractExpression::CFragment(expression) => Ok(expression.clone()),
        ContractExpression::Field { lowered, .. } => Ok(lowered.clone()),
        ContractExpression::CBinding(name) => Ok(CExpression::Variable(name.clone())),
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
        | ContractExpression::At { .. }
        | ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Let { .. }
        | ContractExpression::Call { .. } => Err(ClickError::new(
            "declared resource arguments currently support current-state C expressions only",
        )),
    }
}

fn lower_resource_segment_with_values(
    resource_name: &str,
    segment: &ContractSegment,
    values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CMemoryRange, ClickError> {
    if segment.state != ContractSegmentState::Current {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: resource segments cannot use `old(...)`"
        )));
    }
    // Resource ranges embed field loads symbolically (the canonical
    // `load(arg-memory@...)` spellings), so segment evaluation must not
    // demand concrete loadability.
    let assumptions = Assumptions::new()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads();
    let base = evaluate_c_contract_expression(values, state, result, &assumptions, &segment.base)
        .map_err(|message| {
        ClickError::new(format!(
            "could not lower `{resource_name}` resource: {message}"
        ))
    })?;
    let CValue::Pointer(base) = base else {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment base did not evaluate to a pointer"
        )));
    };
    let start = evaluate_c_contract_expression(values, state, result, &assumptions, &segment.start)
        .map_err(|message| {
            ClickError::new(format!(
                "could not lower `{resource_name}` resource: {message}"
            ))
        })?;
    let CValue::Int32(start) = start else {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment start did not evaluate to int32"
        )));
    };
    let end = evaluate_c_contract_expression(values, state, result, &assumptions, &segment.end)
        .map_err(|message| {
            ClickError::new(format!(
                "could not lower `{resource_name}` resource: {message}"
            ))
        })?;
    let CValue::Int32(end) = end else {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment end did not evaluate to int32"
        )));
    };
    if let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) = (&start, &end)
        && end < start
    {
        return Err(ClickError::new(format!(
            "`{resource_name}` segment has an end before its start: {start}..{end}"
        )));
    }
    Ok(CMemoryRange::new(base, start, end))
}

pub(in crate::lang::click) fn loadable_requirement_prop(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<Proposition, ClickError> {
    let (base, bytes) = loadable_base_and_bytes(requirement, parameters, arguments)?;
    Ok(Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base,
        bytes,
    })
}

pub(in crate::lang::click) fn resource_clause_loadable_prop(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<Option<Proposition>, ClickError> {
    let (segment, range) = match resource {
        ResourceClause::Read(segment) => {
            let lowered = lower_resource_clause(resource, parameters, arguments, memory)?;
            let range = lowered
                .memory_view_range()
                .expect("viewed memory clause should lower to viewed memory");
            (segment, range.clone())
        }
        ResourceClause::Write(segment) => {
            let lowered = lower_resource_clause(resource, parameters, arguments, memory)?;
            let range = lowered
                .memory_own_range()
                .expect("owned memory clause should lower to owned memory");
            (segment, range.clone())
        }
        ResourceClause::Declared { .. } => return Ok(None),
    };
    let element_width = contract_segment_element_width(parameters, segment);
    Ok(Some(memory_range_loadable_prop(
        memory,
        &range,
        element_width,
    )))
}

pub(in crate::lang::click) fn memory_range_loadable_prop(
    memory: &CMemory,
    range: &CMemoryRange,
    element_width: u32,
) -> Proposition {
    let element_count = bitvector32_subtract(range.end().clone(), range.start().clone());
    let bytes = bitvector32_multiply(element_count, Bitvector32Term::Constant(element_width));
    Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: offset_pointer_by_elements(
            range.base().clone(),
            range.start().clone(),
            element_width,
        ),
        bytes,
    }
}

pub(in crate::lang::click) fn concrete_loadable_block(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<Option<(String, ConcreteMemoryRangeSeed)>, ClickError> {
    match requirement.inner() {
        Requirement::LoadableSegment { segment } => {
            let state = CState::new();
            let Ok(segment) = evaluate_requirement_segment(parameters, arguments, &state, segment)
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
            let element_width = contract_segment_element_width(parameters, &segment.source);
            let bytes = end
                .checked_mul(element_width)
                .ok_or_else(|| ClickError::new("`loadable` segment overflows byte count"))?;
            Ok(Some((
                format!("{:?}", segment.source),
                ConcreteMemoryRangeSeed {
                    base: segment.base,
                    bytes,
                    element_width,
                },
            )))
        }
        Requirement::Labeled { .. } | Requirement::Resource(_) | Requirement::Proposition(_) => {
            Ok(None)
        }
    }
}

pub(in crate::lang::click) fn concrete_access_resource_block(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<Option<(String, ConcreteMemoryRangeSeed)>, ClickError> {
    let segment = match resource {
        ResourceClause::Read(segment) | ResourceClause::Write(segment) => segment,
        ResourceClause::Declared { .. } => return Ok(None),
    };
    let state = CState::new();
    let Ok(segment) = evaluate_requirement_segment(parameters, arguments, &state, segment) else {
        return Ok(None);
    };
    let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (&segment.start, &segment.end)
    else {
        return Ok(None);
    };
    if end < start {
        return Err(ClickError::new(format!(
            "resource segment has an end before its start: {start}..{end}"
        )));
    }
    let element_width = contract_segment_element_width(parameters, &segment.source);
    let element_count = end - start;
    let bytes = element_count
        .checked_mul(element_width)
        .ok_or_else(|| ClickError::new("`write` segment overflows byte count"))?;
    Ok(Some((
        format!("{:?}", segment.source),
        ConcreteMemoryRangeSeed {
            base: offset_pointer_by_elements(segment.base, segment.start, element_width),
            bytes,
            element_width,
        },
    )))
}

pub(in crate::lang::click) fn loadable_base_and_bytes(
    requirement: &Requirement,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<(Pointer, Bitvector32Term), ClickError> {
    match requirement.inner() {
        Requirement::LoadableSegment { segment } => {
            let state = CState::new();
            let segment = evaluate_requirement_segment(parameters, arguments, &state, segment)
                .map_err(|message| {
                    ClickError::new(format!("could not lower `loadable` segment: {message}"))
                })?;
            if let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
                (&segment.start, &segment.end)
                && end < start
            {
                return Err(ClickError::new(format!(
                    "`loadable` segment has an end before its start: {start}..{end}"
                )));
            }
            let element_count = bitvector32_subtract(segment.end.clone(), segment.start.clone());
            let element_width = contract_segment_element_width(parameters, &segment.source);
            let bytes =
                bitvector32_multiply(element_count, Bitvector32Term::Constant(element_width));
            Ok((
                offset_pointer_by_elements(segment.base, segment.start, element_width),
                bytes,
            ))
        }
        Requirement::Labeled { .. } | Requirement::Proposition(_) | Requirement::Resource(_) => {
            Err(ClickError::new("expected loadable requirement"))
        }
    }
}

pub(in crate::lang::click) fn loadable_segment_prop(
    memory: &CMemory,
    segment: EvaluatedContractSegment,
    element_width: u32,
) -> Result<Proposition, ClickError> {
    if let (Bitvector32Term::Constant(start), Bitvector32Term::Constant(end)) =
        (&segment.start, &segment.end)
        && end < start
    {
        return Err(ClickError::new(format!(
            "`loadable` segment has an end before its start: {start}..{end}"
        )));
    }
    let element_count = bitvector32_subtract(segment.end.clone(), segment.start.clone());
    let bytes = bitvector32_multiply(element_count, Bitvector32Term::Constant(element_width));
    Ok(Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: offset_pointer_by_elements(segment.base, segment.start, element_width),
        bytes,
    })
}

pub(in crate::lang::click) fn contract_segment_element_width(
    parameters: &[syntax::C0Parameter],
    segment: &ContractSegment,
) -> u32 {
    contract_expression_element_width(parameters, &segment.base).unwrap_or(4)
}

pub(in crate::lang::click) fn contract_expression_element_width(
    parameters: &[syntax::C0Parameter],
    expression: &CExpression,
) -> Option<u32> {
    match expression {
        CExpression::Variable(name) => parameters
            .iter()
            .find(|parameter| parameter.name() == name)
            .and_then(|parameter| match parameter.c_type() {
                C0Type::Int32Pointer => Some(4),
                C0Type::UInt8Pointer => Some(1),
                _ => None,
            }),
        CExpression::Add(left, right) => contract_expression_element_width(parameters, left)
            .or_else(|| contract_expression_element_width(parameters, right)),
        CExpression::Subtract(left, _) => contract_expression_element_width(parameters, left),
        CExpression::TypedLoad { value_type, .. } => match value_type {
            CType::Int32Pointer => Some(4),
            CType::UInt8Pointer => Some(1),
            _ => None,
        },
        _ => None,
    }
}

pub(in crate::lang::click) fn contract_segment_element_width_from_array_refs(
    array_refs: &ClickArrayRefs,
    segment: &ContractSegment,
) -> Option<u32> {
    contract_expression_element_width_from_array_refs(array_refs, &segment.base)
}

pub(in crate::lang::click) fn contract_expression_element_width_from_array_refs(
    array_refs: &ClickArrayRefs,
    expression: &CExpression,
) -> Option<u32> {
    match expression {
        CExpression::Variable(name) => array_refs
            .get(name)
            .map(|array_ref| array_ref.element_type.byte_width()),
        CExpression::Add(left, right) => {
            contract_expression_element_width_from_array_refs(array_refs, left)
                .or_else(|| contract_expression_element_width_from_array_refs(array_refs, right))
        }
        CExpression::Subtract(left, _) => {
            contract_expression_element_width_from_array_refs(array_refs, left)
        }
        CExpression::TypedLoad { value_type, .. } => match value_type {
            CType::Int32Pointer => Some(4),
            CType::UInt8Pointer => Some(1),
            _ => None,
        },
        _ => None,
    }
}

pub(in crate::lang::click) fn requirement_proposition_prop(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, ClickError> {
    let parameter_values = parameter_values(parameters, arguments)?;
    let array_refs = array_refs_for_parameters(parameters, &parameter_values, memory);
    let mut lowerer = KernelPropositionLowerer::new(
        parameter_values,
        array_refs,
        memory.clone(),
        predicate_environment,
        click_function_environment,
    );
    lowerer.lower_requirement_proposition(proposition)
}

pub(in crate::lang::click) fn parameter_values(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<BTreeMap<String, CValue>, ClickError> {
    parameters
        .iter()
        .zip(arguments)
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

pub(in crate::lang::click) fn array_refs_for_parameters(
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
                    pointer: pointer.clone(),
                    element_type,
                },
            ))
        })
        .collect()
}
