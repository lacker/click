//! Independent input construction for inferred native semantic effects.
//! A checked execution under a caller's concrete cells is not a reusable
//! domain promise. Rebuild the supported input from declarations/contracts.
use super::*;

#[derive(Clone)]
pub(crate) struct IndependentEntry {
    pub(crate) caller: CState,
    pub(crate) arguments: Vec<CExpression>,
}

/// Reproduce only declared C storage observations from an opaque input head.
/// The resource remains folded and supplies no native object designation.
fn name_c_composite_input_cells(
    state: &CState,
    definition: &CCompositeResourceDefinition,
    fact: &CResourceFact,
) -> Option<(CState, Vec<CResourceFact>)> {
    if state.typed_access_policy() != CTypedAccessPolicy::CAllocatedAccessAllowed
        || state.memory().has_uninitialized_object_footprints()
        || fact.owned_quantity() != Some(1)
        || definition.matched.is_some()
        || definition.condition().is_some()
        || !definition
            .contains()
            .iter()
            .any(|spec| spec.declared_storage_type().is_some())
    {
        return Some((state.clone(), Vec::new()));
    }
    let CResource::Composite { arguments, .. } = fact.resource() else {
        return None;
    };
    let mut scope = state.clone();
    let mut body_resources = ResourceContext::new();
    for (formal, actual) in definition.parameters().iter().zip(arguments.iter()) {
        let value = actual.as_c_value()?;
        if value.c_type() != formal.c_type() {
            return None;
        }
        scope
            .locals
            .set_typed(formal.name().to_string(), value.clone(), formal.c_type());
    }
    let source = intern_c_memory_ref(state.memory());
    let empty = PureFactContext::new();
    let mut budget = ExecutionBudget::beside_live_state();
    for spec in definition.contains() {
        if spec.guard().is_some() || !matches!(spec.term(), CResourceTerm::Memory(_)) {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        let Ok(Ok(fact)) = evaluate_function_resource_spec(&scope, spec, &empty, &mut budget)
        else {
            return None;
        };
        let named =
            name_direct_input_from_source(&scope, spec, &fact, &empty, Some(source.clone()))?;
        scope.set_memory(named.memory().clone());
        body_resources = body_resources.unchecked_with_fact(fact.clone());
        // Earlier clauses supply scratch read authority for a later address
        // through a pointer field. Keep it out of the returned folded input.
        scope = scope
            .clone()
            .with_resource_context(scope.resources().clone().unchecked_with_fact(fact));
    }
    let cores = body_resources
        .facts()
        .iter()
        .filter_map(|fact| fact.core_with_assumptions(&empty))
        .filter(|fact| fact.memory_view_range().is_some())
        .collect();
    Some((state.clone().with_memory(scope.memory().clone()), cores))
}

fn binder(value: &CValue, ty: CType) -> Option<Variable> {
    match value {
        CValue::Pointer(pointer) => match (&pointer.pointer().block, &pointer.pointer().offset) {
            (PointerBlock::Symbolic(variable), PointerOffsetTerm::Constant(0)) => Some(*variable),
            (
                PointerBlock::ExternalArgument,
                PointerOffsetTerm::Int32Scaled { value, byte_width },
            ) if *byte_width == i64::from(ty.pointee_type().map_or(1, CType::byte_width)) => {
                let Bitvector32Term::Variable(variable) = value.as_ref() else {
                    return None;
                };
                Some(*variable)
            }
            _ => None,
        },
        CValue::Bool(Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        }) => {
            let ConditionTerm::Bitvector32Equal(left, right) = condition.as_ref() else {
                return None;
            };
            let Bitvector32Term::Variable(variable) = left.as_ref() else {
                return None;
            };
            (**right == Bitvector32Term::Constant(0)
                && **then_term == Bitvector32Term::Constant(0)
                && **else_term == Bitvector32Term::Constant(1))
            .then_some(*variable)
        }
        CValue::Bool(Bitvector32Term::Variable(variable))
        | CValue::Int8(Bitvector32Term::Variable(variable))
        | CValue::UInt8(Bitvector32Term::Variable(variable))
        | CValue::Int16(Bitvector32Term::Variable(variable))
        | CValue::UInt16(Bitvector32Term::Variable(variable))
        | CValue::Int32(Bitvector32Term::Variable(variable))
        | CValue::UInt32(Bitvector32Term::Variable(variable))
        | CValue::Int64(Bitvector32Term::Variable(variable))
        | CValue::UInt64(Bitvector32Term::Variable(variable))
        | CValue::Int128(Bitvector32Term::Variable(variable))
        | CValue::UInt128(Bitvector32Term::Variable(variable))
        | CValue::Float32(Bitvector32Term::Variable(variable))
        | CValue::Float64(Bitvector32Term::Variable(variable)) => Some(*variable),
        _ => None,
    }
}

fn expression_value(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    let mut budget = ExecutionBudget::beside_live_state();
    let observation = assumptions.clone().observe_pointer_addresses();
    let paths = evaluate_c_expression_paths(state, expression, &observation, &mut budget).ok()?;
    let [path] = paths.as_slice() else {
        return None;
    };
    let CExpressionOutcome::Value(value) = &path.outcome else {
        return None;
    };
    let facts = assumptions_with_path_context(&observation, &path.facts, &[]);
    if path
        .obligations
        .iter()
        .any(|goal| !required_obligation_is_exactly_discharged(&facts, goal.proposition()))
    {
        return None;
    }
    Some(value.clone())
}

fn name_direct_input(
    state: &CState,
    spec: &CResourceSpec,
    fact: &CResourceFact,
    assumptions: &PureFactContext,
) -> Option<CState> {
    name_direct_input_from_source(state, spec, fact, assumptions, None)
}

fn name_direct_input_from_source(
    state: &CState,
    spec: &CResourceSpec,
    fact: &CResourceFact,
    assumptions: &PureFactContext,
    source: Option<SharedCMemory>,
) -> Option<CState> {
    let CResourceTerm::Memory(segment) = spec.term() else {
        return Some(state.clone());
    };
    let range = fact.memory_range()?;
    let (Some(start), Some(end)) = (range.constant_start(), range.constant_end()) else {
        // Symbolic typed prefixes have witnesses, but no guessed initialized values.
        return Some(state.clone());
    };
    let CValue::Pointer(base) = expression_value(state, &segment.base, assumptions)? else {
        return None;
    };
    // Member evaluation above authenticates the retained declaration/path.
    // Its leaf type is storage type; the resource's coordinate stride can be
    // four-byte aggregate coordinates even for one eight-byte pointer field.
    let selected_element = spec
        .declared_storage_type()
        .or_else(|| match &segment.base {
            CExpression::MemberAddress { selection, .. } => Some(selection.value_type()),
            _ => None,
        });
    let element = selected_element.or_else(|| base.c_type().pointee_type())?;
    let mut memory = state.memory().clone();
    let source = source.unwrap_or_else(|| crate::kernel::intern_c_memory(memory.clone()));
    if selected_element.is_some() && LoadKind::of_type(element).is_some() {
        let width = element.byte_width();
        let first_byte = start.checked_mul(range.element_width())?;
        let end_byte = end.checked_mul(range.element_width())?;
        if !first_byte.is_multiple_of(width) {
            return None;
        }
        let first = first_byte / width;
        let end = if let Some(count) = spec.declared_storage_count() {
            if first_byte.checked_add(count.checked_mul(width)?)? > end_byte {
                return None;
            }
            first.checked_add(count)?
        } else {
            if !end_byte.is_multiple_of(width) {
                return None;
            }
            end_byte / width
        };
        memory = memory.with_proof_entry_cells_under(
            range.base().clone(),
            width,
            element,
            first,
            end,
            source,
            assumptions,
        );
    } else if element.byte_width() == range.element_width() {
        memory = memory.with_proof_entry_cells_under(
            range.base().clone(),
            range.element_width(),
            element,
            start,
            end,
            source,
            assumptions,
        );
    } else {
        // A whole-record clause explicitly promises its declared scalar fields.
        let layout = spec.native_record_places().iter().find_map(|requirement| {
            let CValue::Pointer(pointer) =
                expression_value(state, &requirement.carrier, assumptions)?
            else {
                return None;
            };
            (pointer.pointer() == range.base()
                && requirement.layout.size_bytes() == range.element_width())
            .then_some(requirement.layout.clone())
        })?;
        if start != 0 || end != 1 {
            return None;
        }
        for field in layout.fields() {
            crate::instrumentation::record_deterministic_work(1);
            let pointer = range.base().offset_by_bytes(field.offset_bytes());
            match field.c_type() {
                CType::Int32Array(count) => {
                    memory = memory.with_proof_entry_cells_under(
                        pointer,
                        4,
                        CType::Int32,
                        0,
                        count,
                        source.clone(),
                        assumptions,
                    )
                }
                CType::UInt8Array(count) => {
                    memory = memory.with_proof_entry_cells_under(
                        pointer,
                        1,
                        CType::UInt8,
                        0,
                        count,
                        source.clone(),
                        assumptions,
                    )
                }
                ty if LoadKind::of_type(ty).is_some() => {
                    memory = memory.with_proof_entry_cells_under(
                        pointer,
                        ty.byte_width(),
                        ty,
                        0,
                        1,
                        source.clone(),
                        assumptions,
                    )
                }
                _ => return None,
            }
        }
    }
    Some(state.clone().with_memory(memory))
}

/// Bind declaration expressions before their required field ownership exists.
/// This scratch scope creates no resource, memory observation or program entry.
fn declaration_scope(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
) -> Option<CState> {
    let mut scope = state.clone();
    for (parameter, argument) in function.parameters().iter().zip(arguments) {
        let CExpression::Value(value) = argument else {
            return None;
        };
        if value.c_type() != parameter.c_type() {
            return None;
        }
        if let Some(layout) = parameter.aggregate_layout() {
            let CValue::Pointer(pointer) = value else {
                return None;
            };
            scope.locals.set_aggregate_object_at(
                parameter.name().to_string(),
                layout.clone(),
                pointer.pointer().clone(),
            );
            continue;
        }
        scope.locals.set_typed_with_all_qualifiers(
            parameter.name().to_string(),
            value
                .clone()
                .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
                .with_pointer_pointee_constant(parameter.pointee_is_constant()),
            parameter.c_type(),
            parameter.is_volatile(),
            parameter.pointee_is_volatile(),
            parameter.is_constant(),
            parameter.pointee_is_constant(),
        );
    }
    Some(scope)
}

/// Construct only declared globals and inputs. No cell or ledger from the
/// actual caller is used to create this state.
pub(crate) fn construct(
    function: &CFunction,
    arguments: &[CExpression],
    destination: Option<&Pointer>,
    track_creation: bool,
) -> Option<IndependentEntry> {
    let interface = function.contract_interface();
    if arguments.len() != interface.parameters().len() {
        return None;
    }
    // The same declaration-only query as source entry selects opaque
    // identities; it neither opens a child nor grants a native prefix.
    let span_formals = CFunctionContractInterface::declared_span_identity_parameters(
        interface.parameters(),
        interface.resource_requires(),
        interface.composite_resource_definitions(),
    );
    let mut ids = BTreeSet::new();
    let mut canonical = arguments.to_vec();
    for (index, ((argument, original), parameter)) in canonical
        .iter_mut()
        .zip(arguments)
        .zip(interface.parameters())
        .enumerate()
    {
        let CExpression::Value(value) = original else {
            return None;
        };
        if value.c_type() != parameter.c_type() {
            return None;
        }
        let input = if parameter.aggregate_layout().is_some() {
            let CValue::Pointer(pointer) = value else {
                return None;
            };
            let source = registered_aggregate_argument_source(&pointer.pointer().block)?;
            let input = CValue::typed_pointer(source, parameter.c_type());
            *argument = CExpression::Value(input.clone());
            input
        } else {
            value.clone()
        };
        let variable = binder(&input, parameter.c_type())?;
        if !ids.insert(variable)
            || crate::kernel::eval::registered_load_term_for_variable(&variable).is_some()
        {
            return None;
        }
        if parameter.aggregate_layout().is_none()
            && let CValue::Pointer(pointer) = value
        {
            let construction_layout = interface
                .construction_parameter()
                .filter(|(parameter_index, _)| *parameter_index == index)
                .map(|(_, layout)| layout);
            // An opaque full input value is not a native object promise.
            // Preserve only the declaration's canonical binder, never a
            // caller's object geometry or an unrelated unresolved identity.
            let opaque_value_input = matches!(pointer.designation(),
                Some(PointerDesignation::Unresolved(identity)) if *identity == variable);
            let mut pointer = if construction_layout.is_some() {
                crate::kernel::c_construction_contract_input_pointer(
                    function,
                    pointer.pointer().clone(),
                )?
            } else {
                CPointerValue::new(pointer.pointer().clone(), pointer.c_type())
                    .with_pointee_constant(pointer.pointee_constant())
                    .with_pointee_volatile(pointer.pointee_volatile())
            };
            if construction_layout.is_none()
                && (opaque_value_input
                    || parameter.is_native_pointer_input()
                    || span_formals.contains(&index))
            {
                pointer = pointer.with_designation(PointerDesignation::Unresolved(variable));
            }
            *argument = CExpression::Value(CValue::Pointer(pointer));
        }
    }
    let initial = if track_creation {
        CState::new().with_population_creation_tracking()
    } else {
        CState::new()
    };
    let mut state = initialize_c_function_globals(
        &initial.with_typed_access_policy(interface.typed_access_policy()),
        function,
    );
    for output in interface.initialization_output_selectors()? {
        if output.field().is_some() || output.bytes() == 0 {
            continue;
        }
        let CExpression::Value(CValue::Pointer(pointer)) =
            canonical.get(output.parameter_index())?
        else {
            return None;
        };
        state.set_memory(
            state
                .memory()
                .clone()
                .with_uninitialized_object(pointer.pointer().clone(), output.bytes()),
        );
    }
    let mut implicit_result_requirement = None;
    if interface.aggregate_return_mode() == CAggregateReturnMode::Construction {
        let destination = destination?;
        let (PointerBlock::Symbolic(variable), PointerOffsetTerm::Constant(0)) =
            (&destination.block, &destination.offset)
        else {
            return None;
        };
        if !ids.insert(*variable)
            || crate::kernel::eval::registered_load_term_for_variable(variable).is_some()
        {
            return None;
        }
        let layout = interface.return_aggregate_layout()?.clone();
        crate::kernel::register_block_alignment(&destination.block, layout.alignment_bytes());
        state.set_memory(
            state
                .memory()
                .clone()
                .with_uninitialized_block(destination.block.clone(), layout.size_bytes()),
        );
        state = state.with_aggregate_return_destination(destination.clone(), layout.clone());
        // The hidden result is the declared aggregate place selected by the
        // checked construction binder, not an ordinary pointer local.
        state.locals.set_aggregate_object_at(
            C_CONTRACT_RESULT_NAME,
            layout.clone(),
            destination.clone(),
        );
        let implicit_spec = CResourceSpec::owned_memory(
            CMemorySegment::new(
                c_variable(C_CONTRACT_RESULT_NAME),
                c_int32_literal(0),
                c_int32_literal(layout.size_bytes()),
            )
            .with_element_width(1),
        )
        .with_snapshot(CResourceSnapshot::Entry);
        if interface.resource_requires().last() == Some(&implicit_spec) {
            implicit_result_requirement = Some(implicit_spec);
        }
        state = state.with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                destination.clone(),
                0u32.into(),
                layout.size_bytes().into(),
                1,
            )),
        ));
    } else if destination.is_some() {
        return None;
    }
    if let Some((index, layout)) = interface.construction_parameter() {
        let CExpression::Value(CValue::Pointer(pointer)) = canonical.get(index)? else {
            return None;
        };
        crate::kernel::register_block_alignment(&pointer.pointer().block, layout.alignment_bytes());
        state.set_memory(
            state
                .memory()
                .clone()
                .with_uninitialized_object(pointer.pointer().clone(), layout.size_bytes()),
        );
    }
    state =
        constructor_input::assume_scalar_object_inputs(state, interface, &mut canonical).ok()?;
    state = crate::kernel::c_state_with_construction_contract_input(state, function, &canonical)
        .ok()?;
    if interface
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some())
    {
        // Start from declarations and arbitrary source reads only. Never copy
        // the actual caller's aggregate cells into a reusable effect proof.
        let caller_resources = state.resources().clone();
        state = constructor_input::materialize_symbolic_declaration_parameters(
            &state, function, &canonical,
        )?
        .with_resource_context(caller_resources);
        // The staging image supplies arbitrary argument fields, not an extra
        // caller resource. The real entry owns its own by-value copy. Source
        // entry likewise replaces staging authority with declared inputs.
        for (parameter, argument) in interface.parameters().iter().zip(&mut canonical) {
            if parameter.aggregate_layout().is_some() {
                *argument = CExpression::Value(CValue::typed_pointer(
                    state
                        .locals()
                        .aggregate_object_pointer(parameter.name())?
                        .clone(),
                    parameter.c_type(),
                ));
            }
        }
    }
    state = initialization_outputs::mark_initialization_output_fields(state, interface)?;
    // Only native promise producers may add designations to independent binders.
    let empty = PureFactContext::new();
    let mut entry = declaration_scope(&state, function, &canonical)?;
    let root_specs = interface
        .resource_requires()
        .iter()
        .map(|spec| {
            let places = spec
                .native_record_places()
                .iter()
                .filter(|place| matches!(&place.carrier, CExpression::Variable(_)))
                .cloned()
                .collect();
            spec.clone()
                .with_native_record_places(places)
                .with_native_span_requirements(Vec::new())
        })
        .collect::<Vec<_>>();
    entry = native_record_inputs::assume_native_record_specs(&entry, &root_specs, &empty).ok()?;
    state.set_memory(entry.memory().clone());
    let mut budget = ExecutionBudget::beside_live_state();
    let mut c_input_cores = Vec::new();
    // A supported entry recipe consumes explicit input clauses once, in
    // declaration order. A later prerequisite is unsupported rather than a
    // reason to repeatedly rescan all pending clauses.
    for (index, spec) in interface.resource_requires().iter().enumerate() {
        // This final reserved clause is the source-generated implicit in/out
        // owner already installed before binding. Written duplicates remain
        // separate inputs and are never deduplicated here.
        if index + 1 == interface.resource_requires().len()
            && implicit_result_requirement.as_ref() == Some(spec)
        {
            continue;
        }
        crate::instrumentation::record_deterministic_work(1);
        let entry = declaration_scope(&state, function, &canonical)?;
        let Ok(Ok(fact)) = evaluate_function_resource_spec(&entry, spec, &empty, &mut budget)
        else {
            return None;
        };
        let direct_memory = match fact.resource() {
            CResource::Memory(_) => true,
            CResource::Composite { name, .. } => {
                let CResourceTerm::Composite {
                    name: declared_name,
                    parameter_types,
                    ..
                } = spec.term()
                else {
                    return None;
                };
                let definition = interface.composite_resource_definition(name)?;
                if name != declared_name
                    || definition.parameters().len() != parameter_types.len()
                    || definition
                        .parameters()
                        .iter()
                        .zip(parameter_types)
                        .any(|(formal, actual)| formal.c_type() != *actual)
                    || definition.instance_field_schema().is_some()
                    || !definition.resource_parameters().is_empty()
                    || definition.reaches_population
                    || definition.contains_mutex_authority
                {
                    return None;
                }
                // Reconstruct only the explicitly declared opaque input head.
                // Its body contributes neither cells nor guessed child facts.
                false
            }
            // Protocol and selected-instance entry recipes remain unsupported.
            _ => return None,
        };
        let resources = state.resources().clone().unchecked_with_fact(fact.clone());
        state = state.with_resource_context(resources);
        if direct_memory {
            let bound = declaration_scope(&state, function, &canonical)?;
            state.set_memory(
                name_direct_input(&bound, spec, &fact, &empty)?
                    .memory()
                    .clone(),
            );
        } else if let CResource::Composite { name, .. } = fact.resource() {
            let (named, cores) = name_c_composite_input_cells(
                &state,
                interface.composite_resource_definition(name)?,
                &fact,
            )?;
            state = named;
            if !cores.is_empty() {
                c_input_cores.push((fact, cores));
            }
        }
    }
    state = native_record_inputs::c_state_with_assumed_native_record_inputs(
        &state,
        function,
        &canonical,
        interface.composite_resource_definitions(),
        &empty,
    )
    .ok()?;
    // Match the checked section producer used at source entry. Rebuild only
    // the independently declared inputs, including any private argument
    // storage, so adjacent memory clauses have one canonical representation.
    let resources = ResourceContext::new_with_equalities(&empty)
        .try_compose_with_facts(state.resources().facts().iter().cloned(), &empty)
        .ok()?;
    state = state.with_resource_context(resources);
    // Source entry attaches the declared one-level read observations to the
    // exact owned head. Rebuild them after canonical composition, so dropping
    // that owner also drops its observations. No child owner is installed.
    for (head, cores) in c_input_cores {
        let occurrence = *state
            .resources()
            .owned_occurrences_for_fact(&head)
            .first()?;
        let fresh = cores
            .into_iter()
            .filter(|core| !state.resources().contains_exact_representation(core))
            .collect::<Vec<_>>();
        let resources = state
            .resources()
            .clone()
            .unchecked_with_supported_facts_from_occurrence_with_memory(
                occurrence,
                &head,
                fresh,
                state.memory(),
            );
        state = state.with_resource_context(resources);
    }
    // A declared read-only head also supplies its unconditional direct memory
    // views at the proof entry. Reproduce those projections from the definition,
    // never from caller facts; leave nested/conditional recipes unsupported.
    let mut projected_views = Vec::new();
    for fact in state.resources().facts() {
        let CResourceFact::View(CResource::Composite { name, arguments }) = fact else {
            continue;
        };
        let definition = interface.composite_resource_definition(name)?;
        if definition.matched.is_some()
            || definition.condition().is_some()
            || !definition.resource_parameters().is_empty()
        {
            continue;
        }
        if definition.parameters().len() != arguments.len() {
            return None;
        }
        let mut scope = state.clone();
        for (formal, argument) in definition.parameters().iter().zip(arguments.iter()) {
            let value = argument.as_c_value()?;
            if value.c_type() != formal.c_type() {
                return None;
            }
            scope
                .locals
                .set_typed(formal.name().to_string(), value.clone(), formal.c_type());
        }
        for spec in definition.contains() {
            if spec.guard().is_some() || !matches!(spec.term(), CResourceTerm::Memory(_)) {
                continue;
            }
            let Ok(Ok(view)) = evaluate_function_resource_spec(&scope, spec, &empty, &mut budget)
            else {
                return None;
            };
            projected_views.push(CResourceFact::View(view.resource().clone()));
        }
    }
    if !projected_views.is_empty() {
        let resources = state
            .resources()
            .clone()
            .unchecked_with_facts(projected_views);
        state = state.with_resource_context(resources);
    }
    // Source entry names inputs beside raw construction outputs only after
    // the kernel has checked the whole declared clause partition. Reconstruct
    // that same stage, using its own premises and one immutable source image.
    // No caller facts or cached caller cells are imported.
    if state.memory().has_uninitialized_object_footprints() {
        let assumptions = crate::kernel::c_function_contract_entry(&state, function, &canonical)
            .ok()?
            .into_assumptions();
        let source = crate::kernel::intern_c_memory(state.memory().clone());
        for spec in interface.resource_requires() {
            if !matches!(spec.term(), CResourceTerm::Memory(_)) {
                continue;
            }
            let bound = declaration_scope(&state, function, &canonical)?;
            let Ok(Ok(fact)) =
                evaluate_function_resource_spec(&bound, spec, &assumptions, &mut budget)
            else {
                return None;
            };
            state.set_memory(
                name_direct_input_from_source(
                    &bound,
                    spec,
                    &fact,
                    &assumptions,
                    Some(source.clone()),
                )?
                .memory()
                .clone(),
            );
        }
    }
    // Geometry can depend on the function's own declared preconditions (for
    // example a span's count is one). Derive those premises through the same
    // checked entry builder used for certification before validating geometry.
    crate::kernel::c_function_contract_entry(&state, function, &canonical).ok()?;
    Some(IndependentEntry {
        caller: state,
        arguments: canonical,
    })
}

/// Match source/caller naming only after independently checking its complete
/// physical input state. Entry premises are independently regenerated too.
pub(crate) fn matches(
    function: &CFunction,
    arguments: &[CExpression],
    actual: &CState,
    actual_premises: &PureFactContext,
    checked_case: Option<&crate::kernel::api::CCheckedResourceGuardCase>,
) -> bool {
    let destination = actual
        .aggregate_destination
        .as_deref()
        .map(|destination| &destination.pointer);
    let Some(mut expected) = construct(
        function,
        arguments,
        destination,
        actual.population_effects.creation.is_some(),
    ) else {
        return false;
    };
    if expected.arguments != arguments {
        return false;
    }
    let Ok(contract) =
        crate::kernel::c_function_contract_entry(&expected.caller, function, &expected.arguments)
    else {
        return false;
    };
    let mut premises = contract.into_assumptions();
    if function.contract_interface().aggregate_return_mode() == CAggregateReturnMode::Construction {
        // The source producer evaluates the complete declared clause list in
        // order, including its trailing implicit destination requirement.
        let Some(bound) = declaration_scope(&expected.caller, function, arguments) else {
            return false;
        };
        let mut budget = ExecutionBudget::beside_live_state();
        let Ok(Ok((resources, _))) = evaluate_function_resource_context_with_metadata(
            &bound,
            function.resource_requires(),
            function.composite_resource_definitions(),
            &premises,
            &mut budget,
        ) else {
            return false;
        };
        expected.caller = expected.caller.with_resource_context(resources);
    }
    // Supported producers share canonical forms. Refuse alternate-cell
    // recipes instead of invoking the general source-by-target cell search.
    // Exact equality includes all physical and native authority metadata.
    if expected.caller.memory() != actual.memory() {
        return false;
    }
    // Require exact declared resource content and support/expansion graph.
    // Preserve occurrence identity only after this check, and independently
    // rebuild view bindings instead of importing the caller's loan authority.
    let mut named_resources = actual.resources().clone();
    named_resources.loan_dependencies = expected.caller.resources().loan_dependencies.clone();
    if &named_resources != expected.caller.resources() {
        return false;
    }
    expected.caller = expected.caller.with_resource_context(named_resources);
    if let Some(events) = actual.population_effects.creation.as_ref() {
        if !events.records_nothing() {
            return false;
        }
        Arc::make_mut(&mut expected.caller.population_effects).creation = Some(events.clone());
    }
    // Source certification observes the entry after its declared read views
    // have been rooted. Rebuild that producer from independent input authority
    // before comparing the exact premise context, including loan metadata.
    if actual.loan_ledger().is_some() {
        let Ok(rooted) = crate::kernel::c_state_with_borrowed_contract_inputs(
            expected.caller,
            function,
            arguments,
            &premises,
        ) else {
            return false;
        };
        let Ok(contract) =
            crate::kernel::c_function_contract_entry(&rooted, function, &expected.arguments)
        else {
            return false;
        };
        premises = contract.into_assumptions();
        expected.caller = rooted;
    }
    let expected_actual_premises = if let Some(case) = checked_case {
        let Some(entry_assumptions) =
            case.entry_assumptions(function, arguments, actual, actual_premises)
        else {
            return false;
        };
        for guard in case.guards() {
            premises = premises.assume_proposition(guard.clone());
        }
        entry_assumptions
    } else {
        actual_premises
    };
    if &premises != expected_actual_premises {
        return false;
    }
    expected.caller.equal_up_to_unused_creation_ledgers(actual)
}

/// Only interface-selected roots can yield the bounded member-store summary.
/// Primitive scalar-array inputs have no declared record member paths.
pub(crate) fn has_store_roots(interface: &CFunctionContractInterface) -> bool {
    if interface.aggregate_return_mode() == CAggregateReturnMode::Construction
        || interface.construction_parameter().is_some()
    {
        return true;
    }
    if !interface
        .parameters()
        .iter()
        .any(|parameter| parameter.c_type().is_pointer())
    {
        return false;
    }
    interface
        .aggregate_object_inputs()
        .iter()
        .any(|input| input.layout.scalar_array().is_none())
        || interface.resource_requires().iter().any(|spec| {
            !spec.native_record_places().is_empty()
                || (interface.typed_access_policy() == CTypedAccessPolicy::CAllocatedAccessAllowed
                    && spec.declared_storage_type().is_some_and(CType::is_pointer))
                || matches!(spec.term(), CResourceTerm::Composite { .. })
        })
}
pub(crate) fn native_output_entry_is_relevant(interface: &CFunctionContractInterface) -> bool {
    interface_has_native_output_places(interface)
        && !(interface.return_aggregate_layout().is_none()
            && !interface.return_type().is_pointer()
            && !has_store_roots(interface)
            && !interface.aggregate_object_inputs().is_empty()
            && interface
                .aggregate_object_inputs()
                .iter()
                .all(|input| input.layout.scalar_array().is_some())
            && interface.resource_ensures().iter().all(|spec| {
                matches!(spec.term(), CResourceTerm::Memory(_))
                    && spec.native_record_places().is_empty()
            }))
}
fn relevant_interface(interface: &CFunctionContractInterface) -> bool {
    (interface.return_type().is_pointer() && interface.return_aggregate_layout().is_none())
        || has_store_roots(interface)
        || native_output_entry_is_relevant(interface)
        || interface
            .initialization_output_selectors()
            .is_some_and(|outputs| !outputs.is_empty())
}

/// Shared source producer. The actual state supplies only destination identity
/// and whether to track creation; no caller cell is imported.
pub(crate) fn c_independent_function_input_state(
    actual: &CState,
    function: &CFunction,
    arguments: &[CExpression],
) -> Option<(CState, Vec<CExpression>)> {
    if !relevant_interface(function.contract_interface()) {
        return None;
    }
    let destination = actual.aggregate_destination.as_deref().map(|d| &d.pointer);
    construct(
        function,
        arguments,
        destination,
        actual.population_effects.creation.is_some(),
    )
    .filter(|entry| entry.arguments == arguments)
    .map(|entry| (entry.caller, entry.arguments))
}

#[cfg(test)]
mod tests {
    use super::*;

    fn opaque_input() -> (CFunction, Vec<CExpression>, Pointer, CResourceFact) {
        let pointer = Pointer::symbolic(Variable(9_898_401));
        let value = CValue::typed_pointer(pointer.clone(), CType::Int32Pointer);
        let head = CResourceFact::own(CResource::Composite {
            name: "opaque_cell".into(),
            arguments: vec![AlgebraicValue::C(value.clone())].into(),
        });
        let input = CResourceSpec::composite(
            CResourceAccessMode::Own,
            "opaque_cell".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
        );
        let definition = CCompositeResourceDefinition::new(
            "opaque_cell",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::owned_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            Vec::new(),
        );
        let function = c_function(
            CType::Void,
            "opaque_input",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_void_value()),
        )
        .with_resource_summary(vec![input.clone()], vec![input])
        .with_composite_resource_definitions(vec![definition]);
        (function, vec![CExpression::Value(value)], pointer, head)
    }

    #[test]
    fn declared_readonly_heads_reconstruct_only_their_direct_memory_views() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(9_898_451));
        let value = CValue::Pointer(
            CPointerValue::new(pointer.clone(), CType::Int32Pointer)
                .with_designation(PointerDesignation::Unresolved(Variable(9_898_451))),
        );
        let input = CResourceSpec::composite(
            CResourceAccessMode::View,
            "readable".into(),
            vec![c_variable("p")],
            vec![CType::Int32Pointer],
        );
        let definition = CCompositeResourceDefinition::new(
            "readable",
            vec![c_parameter("p", CType::Int32Pointer)],
            None,
            false,
            vec![CResourceSpec::viewed_memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            Vec::new(),
        );
        let function = c_function(
            CType::Int32Pointer,
            "readonly_identity",
            vec![c_parameter("p", CType::Int32Pointer)],
            c_return(c_variable("p")),
        )
        .with_resource_summary(vec![input], Vec::new())
        .with_composite_resource_definitions(vec![definition]);
        let arguments = vec![CExpression::Value(value)];
        let entry = construct(&function, &arguments, None, false).unwrap();
        let view =
            CResourceFact::view_memory(CMemoryRange::new(pointer.clone(), 0.into(), 1.into()));
        assert!(
            entry
                .caller
                .resources()
                .contains_exact_representation(&view)
        );
        assert!(!entry.caller.resources().contains_exact_representation(
            &CResourceFact::own_memory(CMemoryRange::new(pointer, 0.into(), 1.into()))
        ));
        let premises =
            crate::kernel::c_function_contract_entry(&entry.caller, &function, &arguments)
                .unwrap()
                .into_assumptions();
        assert!(matches(
            &function,
            &arguments,
            &entry.caller,
            &premises,
            None
        ));
        let other = CMemoryRange::new(Pointer::symbolic(Variable(9_898_452)), 0.into(), 1.into());
        for extra in [
            CResourceFact::view_memory(other.clone()),
            CResourceFact::own_memory(other),
        ] {
            let wrong = entry
                .caller
                .clone()
                .with_resource_context(entry.caller.resources().clone().unchecked_with_fact(extra));
            assert!(!matches(&function, &arguments, &wrong, &premises, None));
        }
    }

    #[test]
    fn canonical_opaque_c_pointer_values_are_independent_without_object_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let (function, arguments, pointer, legacy_head) = opaque_input();
        let CExpression::Value(CValue::Pointer(input)) = &arguments[0] else {
            panic!()
        };
        let variable = binder(&CValue::Pointer(input.clone()), input.c_type()).unwrap();
        let opaque = input
            .clone()
            .with_designation(PointerDesignation::Unresolved(variable));
        let arguments = vec![CExpression::Value(CValue::Pointer(opaque.clone()))];
        let mut samples = Vec::new();
        for size in [0_u64, 16, 64, 256] {
            let mut actual = CState::new();
            for index in 0..size {
                actual.set_memory(actual.memory().clone().store(
                    Pointer::symbolic(Variable(9_896_000 + index)),
                    int32(index as u32),
                ));
            }
            let (entry, work) = crate::instrumentation::measure_deterministic_work(|| {
                c_independent_function_input_state(&actual, &function, &arguments)
            });
            let (state, normalized) = entry.expect("a canonical opaque C value is parametric");
            assert_eq!(normalized, arguments);
            assert_eq!(state.memory(), &CMemory::new());
            assert!(
                state
                    .memory()
                    .checked_native_record_pointer(&opaque)
                    .is_none()
            );
            assert!(state.memory().native_input_span(&opaque).is_none());
            assert!(state.memory().allocated_scalar_extent(&opaque).is_none());
            assert_eq!(state.memory().known_value(&pointer), None);
            let premises = crate::kernel::c_function_contract_entry(&state, &function, &arguments)
                .unwrap()
                .into_assumptions();
            assert!(matches(&function, &arguments, &state, &premises, None));
            let wrong = state.clone().with_resource_context(
                ResourceContext::new().unchecked_with_fact(legacy_head.clone()),
            );
            assert!(
                !matches(&function, &arguments, &wrong, &premises, None),
                "address equality cannot erase the opaque input identity"
            );
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] + 64),
            "{samples:?}"
        );
    }

    #[test]
    fn opaque_c_input_normalization_rejects_other_identities_and_object_hints() {
        let _session = crate::kernel::VerificationSession::enter();
        let (function, arguments, pointer, _) = opaque_input();
        let CExpression::Value(CValue::Pointer(input)) = &arguments[0] else {
            panic!()
        };
        let cases = [
            input
                .clone()
                .with_designation(PointerDesignation::Unresolved(Variable(9_898_402))),
            input.clone().with_designation(PointerDesignation::Object {
                root: pointer.clone(),
                path: Arc::from([]),
                base: pointer,
                element_type: CType::Int32,
                stride: 4,
                count: crate::kernel::IntegerTerm::constant_i64(8).into(),
            }),
        ];
        for supplied in cases {
            let arguments = vec![CExpression::Value(CValue::Pointer(supplied))];
            assert!(
                c_independent_function_input_state(&CState::new(), &function, &arguments).is_none(),
                "caller geometry and unrelated identities are not canonical input values"
            );
            let rebuilt = construct(&function, &arguments, None, false).unwrap();
            let CExpression::Value(CValue::Pointer(rebuilt)) = &rebuilt.arguments[0] else {
                panic!()
            };
            assert!(rebuilt.designation().is_none());
        }
    }

    #[test]
    fn declared_c_input_observations_are_parametric_and_attached_to_the_owner() {
        let _session = crate::kernel::VerificationSession::enter();
        for count in [0, 16, 64, 256] {
            let (function, arguments, pointer, head) = opaque_input();
            let definition = CCompositeResourceDefinition::new(
                "opaque_cell",
                vec![c_parameter("p", CType::Int32Pointer)],
                None,
                false,
                vec![
                    CResourceSpec::owned_memory(CMemorySegment::new(
                        c_variable("p"),
                        c_int32_literal(0),
                        c_int32_literal(count),
                    ))
                    .with_declared_storage_observation(Some((CType::Int32, count))),
                ],
                vec![],
            );
            let function = function.with_composite_resource_definitions(vec![definition.clone()]);
            let entry = construct(&function, &arguments, None, false).unwrap();
            let premises =
                crate::kernel::c_function_contract_entry(&entry.caller, &function, &arguments)
                    .unwrap()
                    .into_assumptions();
            assert!(matches(
                &function,
                &arguments,
                &entry.caller,
                &premises,
                None
            ));
            assert!(
                entry
                    .caller
                    .resources()
                    .facts()
                    .iter()
                    .all(|fact| fact.memory_own_range().is_none()),
                "observations cannot become child ownership"
            );
            if count > 0 {
                assert!(matches!(
                    entry.caller.memory().load(&pointer),
                    CExpressionOutcome::Value(CValue::Int32(_))
                ));
                let view = CResourceFact::view_memory(CMemoryRange::new(
                    pointer.clone(),
                    0.into(),
                    count.into(),
                ));
                assert!(
                    entry
                        .caller
                        .resources()
                        .contains_exact_representation(&view)
                );
                let retired = entry
                    .caller
                    .resources()
                    .clone()
                    .without_exact_representation(&head)
                    .unwrap();
                assert!(
                    !retired.contains_exact_representation(&view),
                    "observations retire with their exact owner"
                );
                let specialized = entry.caller.clone().with_memory(
                    entry
                        .caller
                        .memory()
                        .clone()
                        .store(pointer.clone(), int32(7)),
                );
                assert!(!matches(
                    &function,
                    &arguments,
                    &specialized,
                    &premises,
                    None
                ));
            }
            for unsupported in [
                CResourceFact::view_composite(
                    "opaque_cell".into(),
                    vec![CValue::pointer(pointer.clone())],
                ),
                CResourceFact::own_quantity(head.resource().clone(), 0.into()),
                CResourceFact::own_quantity(head.resource().clone(), 2.into()),
            ] {
                let state = CState::new().with_resource_context(
                    ResourceContext::new().unchecked_with_fact(unsupported.clone()),
                );
                let (named, cores) =
                    name_c_composite_input_cells(&state, &definition, &unsupported).unwrap();
                assert_eq!(named.memory(), state.memory());
                assert!(cores.is_empty());
            }
        }
    }

    #[test]
    fn independent_composite_input_keeps_only_its_declared_head() {
        let _session = crate::kernel::VerificationSession::enter();
        let (function, arguments, pointer, head) = opaque_input();
        let entry =
            construct(&function, &arguments, None, false).expect("declared opaque composite input");
        assert_eq!(entry.arguments, arguments);
        assert_eq!(entry.caller.memory(), &CMemory::new());
        assert_eq!(entry.caller.memory().known_value(&pointer), None);
        assert_eq!(
            entry.caller.resources(),
            &ResourceContext::new().unchecked_with_fact(head.clone())
        );
        let premises =
            crate::kernel::c_function_contract_entry(&entry.caller, &function, &entry.arguments)
                .expect("declared contract entry")
                .into_assumptions();
        assert!(matches(
            &function,
            &arguments,
            &entry.caller,
            &premises,
            None
        ));

        let specialized = entry.caller.clone().with_memory(
            entry
                .caller
                .memory()
                .clone()
                .store(pointer.clone(), int32(7)),
        );
        assert!(
            !matches(&function, &arguments, &specialized, &premises, None),
            "a caller-specific child cell is not part of the opaque input recipe"
        );
        let different_carrier = CResourceFact::own(CResource::Composite {
            name: "opaque_cell".into(),
            arguments: vec![AlgebraicValue::C(CValue::Pointer(
                CPointerValue::new(pointer, CType::Int32Pointer)
                    .with_designation(PointerDesignation::Unresolved(Variable(9_898_401))),
            ))]
            .into(),
        });
        let specialized = entry
            .caller
            .clone()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(different_carrier));
        assert!(
            !matches(&function, &arguments, &specialized, &premises, None),
            "numeric equality does not replace the declared head's complete carrier"
        );
        let extra_premise = premises.assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(Bitvector32Term::Variable(Variable(9_898_402)), 1u32.into()),
            true,
        ));
        assert!(!matches(
            &function,
            &arguments,
            &entry.caller,
            &extra_premise,
            None
        ));
    }

    #[test]
    fn independent_composite_input_requires_its_exact_declared_signature() {
        let _session = crate::kernel::VerificationSession::enter();
        let (function, arguments, _, _) = opaque_input();
        let missing = function
            .clone()
            .with_composite_resource_definitions(Vec::new());
        assert!(construct(&missing, &arguments, None, false).is_none());
        let mismatched =
            function.with_composite_resource_definitions(vec![CCompositeResourceDefinition::new(
                "opaque_cell",
                vec![c_parameter("p", CType::UInt32Pointer)],
                None,
                false,
                Vec::new(),
                Vec::new(),
            )]);
        assert!(construct(&mismatched, &arguments, None, false).is_none());
    }
}

#[cfg(test)]
mod eligibility_tests {
    use super::*;

    #[test]
    fn constructor_receiver_uses_the_same_declared_carrier_in_source_and_canonical_entry() {
        let layout =
            CAggregateLayout::new(4, 4, vec![CAggregateField::new("value", 0, CType::Int32)]);
        let function = c_function(
            CType::Void,
            "receiver",
            vec![c_parameter("this", CType::UInt8Pointer).with_native_pointer_input(true)],
            c_return(c_void_value()),
        )
        .with_construction_parameter(0, layout.clone())
        .with_resource_summary(
            vec![CResourceSpec::owned_memory(CMemorySegment::new(
                CExpression::MemberAddress {
                    object: Box::new(c_variable("this")),
                    selection: Arc::new(CAggregateMemberSelection {
                        layout: Arc::new(layout),
                        path: Arc::from(["value".to_string()]),
                        value_type: CType::Int32,
                    }),
                },
                c_int32_literal(0),
                c_int32_literal(1),
            ))],
            vec![],
        );
        let pointer = crate::kernel::c_construction_contract_input_pointer(
            &function,
            Pointer::symbolic(Variable(9_898_242)),
        )
        .expect("declared constructor receiver");
        assert!(
            matches!(pointer.designation(), Some(PointerDesignation::Object { path, .. }) if path.is_empty())
        );
        let arguments = vec![CExpression::Value(CValue::Pointer(pointer))];
        let entry =
            construct(&function, &arguments, None, false).expect("independent constructor entry");
        assert_eq!(entry.arguments, arguments);
        let assumptions =
            crate::kernel::c_function_contract_entry(&entry.caller, &function, &arguments)
                .expect("constructor contract entry")
                .into_assumptions();
        assert!(matches(
            &function,
            &arguments,
            &entry.caller,
            &assumptions,
            None
        ));
    }

    #[test]
    fn scalar_array_interfaces_skip_semantic_entry_reconstruction_at_every_extent() {
        let mut samples = Vec::new();
        for count in [8u32, 1024, 1_000_000] {
            let layout = Arc::new(
                CAggregateLayout::new_scalar_array_with_fields(CType::UInt32, count, Vec::new())
                    .unwrap(),
            );
            assert!(layout.scalar_array().is_some());
            let function = c_function(
                CType::Void,
                "scalar_array_input",
                vec![c_parameter("p", CType::UInt32Pointer)],
                c_return(c_void_value()),
            )
            .with_aggregate_object_inputs(vec![CAggregateObjectInput {
                parameter_index: 0,
                layout,
            }])
            .with_resource_summary(
                vec![],
                vec![
                    CResourceSpec::owned_memory(
                        CMemorySegment::new(
                            c_variable("p"),
                            c_int32_literal(0),
                            c_int32_literal(count),
                        )
                        .with_element_width(4),
                    )
                    .with_native_span_requirements(vec![
                        CNativeSpanRequirement {
                            access_policy: crate::kernel::CTypedAccessPolicy::NativeObjectOnly,
                            carrier: c_variable("p"),
                            element_type: CType::UInt32,
                            count: c_int32_literal(count),
                        },
                    ]),
                ],
            );
            assert!(interface_has_native_output_places(
                function.contract_interface()
            ));
            assert!(!native_output_entry_is_relevant(
                function.contract_interface()
            ));
            let state = CState::new();
            let arguments = [CExpression::Value(CValue::typed_pointer(
                Pointer::symbolic(Variable(9_898_241)),
                CType::UInt32Pointer,
            ))];
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                c_independent_function_input_state(&state, &function, &arguments)
            });
            assert!(
                result.is_none(),
                "scalar-array source recipe must stay compressed"
            );
            samples.push(work);
        }
        assert!(
            samples.iter().all(|work| *work == samples[0]),
            "{samples:?}"
        );
    }
}

#[cfg(test)]
#[test]
fn independent_member_input_names_one_full_pointer_in_word_coordinates() {
    let layout = CAggregateLayout::new(
        8,
        8,
        vec![CAggregateField::new("data", 0, CType::Int32Pointer)],
    );
    let address = Pointer::symbolic(Variable(991_100));
    let origin = CPointerValue::new(address.clone(), CType::Int32Pointer)
        .with_designation(PointerDesignation::Unresolved(Variable(991_100)));
    let memory = CMemory::new()
        .with_native_record_input(origin.clone(), Arc::new(layout.clone()))
        .unwrap();
    let state = CState::new()
        .with_memory(memory)
        .with_local("owner", CValue::Pointer(origin));
    let base = CExpression::MemberAddress {
        object: Box::new(c_variable("owner")),
        selection: Arc::new(CAggregateMemberSelection {
            layout: Arc::new(layout),
            path: vec!["data".into()].into(),
            value_type: CType::Int32Pointer,
        }),
    };
    let spec = CResourceSpec::owned_memory(
        CMemorySegment::new(base, c_int32_literal(0), c_int32_literal(2)).with_element_width(4),
    );
    let fact = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        address.clone(),
        0u32.into(),
        2u32.into(),
        4,
    ));
    let erased = CResourceSpec::owned_memory(
        CMemorySegment::new(c_variable("owner"), c_int32_literal(0), c_int32_literal(2))
            .with_element_width(4),
    )
    .with_declared_storage_observation(Some((CType::Int32Pointer, 1)));
    let reconstructed = name_direct_input(&state, &erased, &fact, &PureFactContext::new()).unwrap();
    assert_eq!(
        reconstructed
            .memory()
            .known_value(&address)
            .unwrap()
            .c_type(),
        CType::Int32Pointer
    );
    assert!(
        reconstructed
            .memory()
            .known_value(&address.offset_by_bytes(4))
            .is_none()
    );
    assert_ne!(
        erased,
        erased
            .clone()
            .with_declared_storage_observation(Some((CType::Int32, 1)))
    );
    let named = name_direct_input(&state, &spec, &fact, &PureFactContext::new()).unwrap();
    assert_eq!(
        named.memory().known_value(&address).unwrap().c_type(),
        CType::Int32Pointer
    );
    assert!(
        named
            .memory()
            .known_value(&address.offset_by_bytes(4))
            .is_none()
    );
}

#[cfg(test)]
#[test]
fn independent_by_value_argument_image_does_not_add_caller_ownership() {
    let _session = crate::kernel::VerificationSession::enter();
    let layout = CAggregateLayout::new(4, 4, vec![CAggregateField::new("value", 0, CType::Int32)]);
    let function = c_function(
        CType::Void,
        "private_value",
        vec![c_parameter_with_aggregate_layout(
            "copy",
            CType::VoidPointer,
            layout,
        )],
        c_return(c_void_value()),
    );
    let arguments = vec![CExpression::Value(CValue::typed_pointer(
        Pointer::symbolic(Variable(995_100)),
        CType::VoidPointer,
    ))];
    let staging = constructor_input::materialize_symbolic_declaration_parameters(
        &CState::new(),
        &function,
        &arguments,
    )
    .expect("declared argument image");
    let image = staging.locals().aggregate_object_pointer("copy").unwrap();
    let image_arguments = vec![CExpression::Value(CValue::typed_pointer(
        image.clone(),
        CType::VoidPointer,
    ))];
    let entry =
        construct(&function, &image_arguments, None, false).expect("independent by-value input");
    assert!(entry.caller.resources().facts().is_empty());
    assert!(entry.caller.memory().blocks.contains_key(&image.block));
    let body_entry =
        crate::kernel::c_function_entry_state(&entry.caller, &function, &entry.arguments).unwrap();
    assert_eq!(body_entry.resources().facts().len(), 1);
}
