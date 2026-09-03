use super::*;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct ConcreteMemoryRangeSeed {
    pub(in crate::surface) base: Pointer,
    pub(in crate::surface) bytes: u32,
    pub(in crate::surface) element_width: u32,
    /// `None` denotes a range whose logical elements are aggregates, such as
    /// C structs. Those ranges are materialized one typed field at a time
    /// using `struct_layout`.
    pub(in crate::surface) element_type: Option<CType>,
    pub(in crate::surface) struct_layout: Option<syntax::C0StructLayout>,
}

pub(in crate::surface) fn initial_call_state(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
) -> Result<(CState, Vec<CExpression>), ClickError> {
    let mut arguments = Vec::new();

    for (index, parameter) in parameters.iter().enumerate() {
        if parameter.is_struct_value() {
            arguments.push(c_typed_pointer_value(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: scale_int32_offset(
                        Bitvector32Term::Variable(Variable(
                            POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                        )),
                        1,
                    ),
                },
                parameter.to_kernel_parameter().c_type(),
            ));
            continue;
        }
        match parameter.c_type() {
            C0Type::Void => {
                return Err(ClickError::new(format!(
                    "parameter `{}` cannot have type void",
                    parameter.name()
                )));
            }
            C0Type::FunctionPointer(_) => {
                arguments.push(c_typed_pointer_value(
                    Pointer::symbolic_function(Variable(
                        POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                    )),
                    parameter.c_type().to_kernel_type(),
                ));
            }
            C0Type::Int32Pointer
            | C0Type::UInt8Pointer
            | C0Type::Int32PointerPointer
            | C0Type::UInt8PointerPointer => {
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
                            Bitvector32Term::Variable(Variable(
                                POINTER_ARGUMENT_VARIABLE_BASE + index as u64,
                            )),
                            i64::from(element_width),
                        ),
                    },
                    kernel_c_type,
                ));
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

pub(in crate::surface) fn memory_with_symbolic_loadable_cells(
    mut memory: CMemory,
    loadable_ranges: &BTreeMap<String, ConcreteMemoryRangeSeed>,
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
                            let value =
                                symbolic_value_for_element(&base_memory, &pointer, element_type);
                            memory.store(pointer, value)
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
        let mut offset: u32 = 0;
        while offset
            .checked_add(range.element_width)
            .is_some_and(|end| end <= range.bytes)
        {
            let pointer = offset_pointer_by_elements(
                range.base.clone(),
                Bitvector32Term::Constant(offset / range.element_width),
                range.element_width,
            );
            let value = symbolic_value_for_element(&base_memory, &pointer, element_type);
            memory = memory.store(pointer, value);
            offset += range.element_width;
        }
    }
    memory
}

fn visit_struct_field_cells(
    field: &syntax::C0StructField,
    element_pointer: &Pointer,
    mut memory: CMemory,
    mut visit: impl FnMut(CMemory, Pointer, CType) -> CMemory,
) -> CMemory {
    let field_pointer = element_pointer.offset_by_bytes(field.offset_bytes());
    match field.c_type().to_kernel_type() {
        CType::Int32Array(length) => {
            for index in 0..length {
                memory = visit(
                    memory,
                    field_pointer.offset_by_bytes(
                        index.checked_mul(CType::Int32.byte_width()).expect(
                            "validated int32 array field stride must fit in the pointer offset",
                        ),
                    ),
                    CType::Int32,
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<CMemory, ClickError> {
    for requirement in requires {
        let Requirement::Resource(
            ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment),
        ) = requirement.inner()
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

    if let Some(layout) = contract_expression_struct_layout(parameters, &segment.source.base) {
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
                        let load = crate::kernel::canonical_form_of_load(
                            crate::kernel::intern_c_memory(base_memory.clone()),
                            pointer.clone(),
                        );
                        let value = symbolic_value_from_load(&pointer, element_type, load);
                        memory.store(pointer, value)
                    },
                );
            }
        }
        return Ok(memory);
    }

    let element_type = contract_segment_element_type(parameters, &segment.source);
    let element_width = element_type.byte_width();
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
        let load = crate::kernel::canonical_form_of_load(
            crate::kernel::intern_c_memory(base_memory.clone()),
            pointer.clone(),
        );
        let value = symbolic_value_from_load(&pointer, element_type, load);
        memory = memory.store(pointer, value);
    }
    Ok(memory)
}

pub(in crate::surface) fn requirement_propositions(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<Proposition>, ClickError> {
    requirement_propositions_with_assumptions(
        requires,
        parameters,
        arguments,
        state,
        predicate_environment,
        click_function_environment,
        &PureFactContext::new(),
    )
}

pub(in crate::surface) fn requirement_propositions_with_assumptions(
    requires: &[Requirement],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    initial_assumptions: &PureFactContext,
) -> Result<Vec<Proposition>, ClickError> {
    // A proposition requirement may contain a memory read whose range is
    // justified by another requirement, such as `1 <= n` before
    // `a[0] == 7` under `views a[0..n]`. Lower requirements independently
    // used to make this valid dependency invisible. Retry clauses that need
    // more facts after successfully lowered clauses have contributed their
    // propositions to the local assumption context. Keeping the result in
    // source order preserves the contract-to-kernel mapping.
    let mut lowered = (0..requires.len())
        .map(|_| None)
        .collect::<Vec<Option<Proposition>>>();
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
            let result = match requirement.inner() {
                Requirement::LoadableSegment { .. } => {
                    loadable_requirement_prop(requirement, parameters, arguments, state.memory())
                        .map(Some)
                }
                Requirement::Proposition(proposition) => {
                    requirement_proposition_prop_with_assumptions(
                        parameters,
                        arguments,
                        state,
                        proposition,
                        predicate_environment,
                        click_function_environment,
                        &assumptions,
                    )
                    .map(Some)
                }
                Requirement::Resource(resource) => {
                    resource_clause_loadable_prop(resource, parameters, arguments, state.memory())
                }
                Requirement::Labeled { .. } => unreachable!("requirement.inner() removes labels"),
            };
            let result = match result {
                Ok(Some(proposition)) => Ok(proposition),
                Ok(None) => continue,
                Err(error) => Err(error),
            };
            match result {
                Ok(proposition) => {
                    assumptions = assumptions.assume_proposition(proposition.clone());
                    lowered[index] = Some(proposition);
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

    Ok(lowered.into_iter().flatten().collect())
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
            | ClickProposition::Loadable { .. }
            | ClickProposition::Defined { .. }
            | ClickProposition::At { .. }
            | ClickProposition::PredicateCall { .. } => {}
        }
    }

    let mut result = Vec::new();
    for requirement in requires {
        let Requirement::Proposition(proposition) = requirement.inner() else {
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
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Vec<(ClickProposition, Proposition)>, ClickError> {
    let mut result = Vec::new();
    for surface in requirement_definedness_surfaces(requires) {
        let kernel = requirement_proposition_prop(
            parameters,
            arguments,
            state,
            &surface,
            predicate_environment,
            click_function_environment,
        )?;
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

pub(in crate::surface) fn lower_resource_clause(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<CResourceFact, ClickError> {
    let values =
        parameter_values(parameters, arguments).map_err(|error| ClickError::new(error.message))?;
    let state = CState::new().with_memory(memory.clone());
    lower_resource_clause_with_values(resource, parameters, &values, &state, None)
}

pub(in crate::surface) fn lower_resource_clause_at_state(
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
    lower_resource_clause_with_values(resource, parameters, &values, state, None)
}

pub(in crate::surface) fn lower_resource_clause_at_state_with_result(
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
    lower_resource_clause_with_values(resource, parameters, &values, state, Some(result))
}

fn lower_resource_clause_with_values(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
) -> Result<CResourceFact, ClickError> {
    match resource {
        ResourceClause::Quantified { quantity, resource } => {
            let quantity = resource_argument_to_c_expression(quantity)?;
            let assumptions = PureFactContext::new();
            let array_refs = array_refs_for_parameters(parameters, values, state.memory());
            let quantity = crate::surface::proof::evaluate_c_fragment_through_kernel(
                &quantity,
                &assumptions,
                values,
                &array_refs,
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
            let lowered =
                lower_resource_clause_with_values(resource, parameters, values, state, result)?;
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
                values,
                &array_refs_for_parameters(parameters, values, state.memory()),
                state,
                result,
                contract_segment_element_width(parameters, segment),
            )?;
            Ok(CResourceFact::view_memory(range))
        }
        ResourceClause::OwnMemory(segment) => {
            let range = lower_resource_segment_with_values(
                "write",
                segment,
                values,
                &array_refs_for_parameters(parameters, values, state.memory()),
                state,
                result,
                contract_segment_element_width(parameters, segment),
            )?;
            Ok(CResourceFact::own_memory(range))
        }
        ResourceClause::Declared {
            access,
            kind,
            name,
            arguments: resource_arguments,
            parameter_types,
        } => {
            let assumptions = PureFactContext::new();
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
                let argument = resource_argument_to_c_expression(argument)?;
                let value = crate::surface::proof::evaluate_c_fragment_through_kernel(
                    &argument,
                    &assumptions,
                    values,
                    &array_refs,
                    state,
                    result,
                )
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
                ResourceAccessMode::Own => CResourceFact::own(resource),
                ResourceAccessMode::View => CResourceFact::View(resource),
            })
        }
    }
}

pub(in crate::surface) fn resource_argument_to_c_expression(
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
        | ContractExpression::ResourceCount(_)
        | ContractExpression::ResourceWildcard
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
    array_refs: &ClickArrayRefs,
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
    let evaluate = |expression: &CExpression| {
        crate::surface::proof::evaluate_c_fragment_through_kernel(
            expression,
            &assumptions,
            values,
            array_refs,
            state,
            result,
        )
    };
    let base = evaluate(&segment.base).map_err(|message| {
        ClickError::new(format!(
            "could not lower `{resource_name}` resource: {message}"
        ))
    })?;
    let CValue::Pointer(base) = base else {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment base did not evaluate to a pointer"
        )));
    };
    let base = base.into_pointer();
    let start = evaluate(&segment.start).map_err(|message| {
        ClickError::new(format!(
            "could not lower `{resource_name}` resource: {message}"
        ))
    })?;
    let CValue::Int32(start) = start else {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment start did not evaluate to int32"
        )));
    };
    let end = evaluate(&segment.end).map_err(|message| {
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
    Ok(CMemoryRange::new_with_element_width(
        base,
        start,
        end,
        element_width,
    ))
}

pub(in crate::surface) fn loadable_requirement_prop(
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

pub(in crate::surface) fn resource_clause_loadable_prop(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    memory: &CMemory,
) -> Result<Option<Proposition>, ClickError> {
    let range = match resource {
        ResourceClause::ViewMemory(_) => {
            let lowered = lower_resource_clause(resource, parameters, arguments, memory)?;
            let range = lowered
                .memory_view_range()
                .expect("viewed memory clause should lower to viewed memory");
            range.clone()
        }
        ResourceClause::OwnMemory(_) => {
            let lowered = lower_resource_clause(resource, parameters, arguments, memory)?;
            let range = lowered
                .memory_own_range()
                .expect("owned memory clause should lower to owned memory");
            range.clone()
        }
        ResourceClause::Declared { .. } | ResourceClause::Quantified { .. } => return Ok(None),
    };
    Ok(Some(memory_range_loadable_prop(memory, &range)))
}

pub(in crate::surface) fn memory_range_loadable_prop(
    memory: &CMemory,
    range: &CMemoryRange,
) -> Proposition {
    let (base, bytes) = range.byte_footprint();
    Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base,
        bytes,
    }
}

pub(in crate::surface) fn concrete_loadable_block(
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
                    element_type: (!contract_expression_is_struct_array(
                        parameters,
                        &segment.source.base,
                    ))
                    .then(|| contract_segment_element_type(parameters, &segment.source)),
                    struct_layout: contract_expression_struct_layout(
                        parameters,
                        &segment.source.base,
                    )
                    .cloned(),
                },
            )))
        }
        Requirement::Labeled { .. } | Requirement::Resource(_) | Requirement::Proposition(_) => {
            Ok(None)
        }
    }
}

pub(in crate::surface) fn concrete_access_resource_block(
    resource: &ResourceClause,
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
) -> Result<Option<(String, ConcreteMemoryRangeSeed)>, ClickError> {
    let segment = match resource {
        ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => segment,
        ResourceClause::Declared { .. } | ResourceClause::Quantified { .. } => return Ok(None),
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
            element_type: (!contract_expression_is_struct_array(parameters, &segment.source.base))
                .then(|| contract_segment_element_type(parameters, &segment.source)),
            struct_layout: contract_expression_struct_layout(parameters, &segment.source.base)
                .cloned(),
        },
    )))
}

pub(in crate::surface) fn loadable_base_and_bytes(
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

pub(in crate::surface) fn contract_segment_element_width(
    parameters: &[syntax::C0Parameter],
    segment: &ContractSegment,
) -> u32 {
    contract_expression_element_width(parameters, &segment.base).unwrap_or(4)
}

fn contract_segment_element_type(
    parameters: &[syntax::C0Parameter],
    segment: &ContractSegment,
) -> CType {
    contract_expression_element_type(parameters, &segment.base).unwrap_or(CType::Int32)
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

fn contract_expression_element_type(
    parameters: &[syntax::C0Parameter],
    expression: &CExpression,
) -> Option<CType> {
    match expression {
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
                            C0Type::UInt8Array(_) => Some(1),
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
            _ => None,
        },
        _ => None,
    }
}

fn symbolic_value_for_element(memory: &CMemory, pointer: &Pointer, element_type: CType) -> CValue {
    let load = crate::kernel::canonical_form_of_load(
        crate::kernel::intern_c_memory(memory.clone()),
        pointer.clone(),
    );
    symbolic_value_from_load(pointer, element_type, load)
}

fn symbolic_value_from_load(
    pointer: &Pointer,
    element_type: CType,
    load: Bitvector32Term,
) -> CValue {
    match element_type {
        CType::Int32 => CValue::Int32(load),
        CType::UInt8 => CValue::UInt8(load),
        c_type if c_type.is_pointer() => CValue::typed_pointer(
            Pointer {
                block: pointer.block.clone(),
                offset: PointerOffsetTerm::scale_int32(
                    load,
                    i64::from(
                        c_type
                            .pointee_type()
                            .expect("pointer element type has a pointee")
                            .byte_width(),
                    ),
                ),
            },
            c_type,
        ),
        _ => unreachable!("memory ranges cannot contain aggregate elements"),
    }
}

pub(in crate::surface) fn requirement_proposition_prop(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<Proposition, ClickError> {
    requirement_proposition_prop_with_assumptions(
        parameters,
        arguments,
        state,
        proposition,
        predicate_environment,
        click_function_environment,
        &PureFactContext::new(),
    )
}

pub(in crate::surface) fn requirement_proposition_prop_with_assumptions(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    state: &CState,
    proposition: &ClickProposition,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    assumptions: &PureFactContext,
) -> Result<Proposition, ClickError> {
    // The requirement is elaborated as the contract elaborates it and
    // lowered by the kernel at the entry state, with the parameters bound
    // to their argument values where the state does not bind them.
    let spec = crate::surface::lowering::elaborate_requirement_proposition(
        parameters,
        proposition,
        predicate_environment,
        click_function_environment,
    )
    .map_err(ClickError::new)?;
    let mut lowering_state = state.clone();
    for (name, value) in parameter_values(parameters, arguments)? {
        if lowering_state.locals().get(&name).is_none() {
            lowering_state = lowering_state.with_local(name, value);
        }
    }
    let (lowered, _, obligations) =
        crate::kernel::c_lower_spec_proposition_at_state(&lowering_state, &spec, None, assumptions)
            .map_err(ClickError::new)?;
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
        return Err(ClickError::new(
            crate::surface::diagnostics::describe_missing_pure_fact(
                obligation,
                &[],
                &[],
                parameters,
                arguments,
                &[],
            ),
        ));
    }
    Ok(lowered)
}

pub(in crate::surface) fn parameter_values(
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
