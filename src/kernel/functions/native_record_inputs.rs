use super::*;

fn requirement_pointer(
    state: &CState,
    requirement: &CNativeRecordPlaceRequirement,
    assumptions: &PureFactContext,
    source_entry: bool,
) -> Result<CPointerValue, String> {
    let _entry_observation = source_entry.then(crate::kernel::eval::SpecificationReadScope::enter);
    let observer = if source_entry {
        assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .observe_pointer_addresses()
    } else {
        assumptions.clone().observe_pointer_addresses()
    };
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = evaluate_c_expression_paths(state, &requirement.carrier, &observer, &mut budget)
        .map_err(|_| "native record place evaluation exceeded its budget".to_string())?;
    let [path] = paths.as_slice() else {
        return Err("native record place needs one established carrier".into());
    };
    if path
        .facts
        .iter()
        .any(|fact| !required_obligation_is_exactly_discharged(&observer, fact.proposition()))
        || path
            .obligations
            .iter()
            .any(|goal| !required_obligation_is_exactly_discharged(&observer, goal.proposition()))
    {
        return Err("native record place has an unproved carrier condition".into());
    }
    let CExpressionOutcome::Value(CValue::Pointer(pointer)) = &path.outcome else {
        return Err("native record place requires a defined pointer carrier".into());
    };
    // Normalize only against the carrier's own retained descriptor. Raw
    // address equality never chooses a different domain or declaration.
    if let Some(PointerDesignation::Object { base, .. }) = pointer.designation()
        && pointer.pointer() != base
        && pointers_proven_equal_for_memory_resolution(pointer.pointer(), base, assumptions)
    {
        return Ok(pointer.clone().with_pointer(base.clone()));
    }
    Ok(pointer.clone())
}

fn requirement_count(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
) -> Result<(SharedIntegerTerm, PureFactContext), String> {
    let observer = assumptions
        .clone()
        .observe_pointer_addresses()
        .require_owned_expression_loads();
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = evaluate_c_expression_paths(state, expression, &observer, &mut budget)
        .map_err(|_| "native record prefix count evaluation exceeded its budget".to_string())?;
    let [path] = paths.as_slice() else {
        return Err("native record prefix needs one established count".into());
    };
    let context = assumptions_with_path_context(&observer, &path.facts, &[]);
    if path
        .obligations
        .iter()
        .any(|goal| !required_obligation_is_exactly_discharged(&context, goal.proposition()))
    {
        return Err("native record prefix has an unproved count condition".into());
    }
    let CExpressionOutcome::Value(value) = &path.outcome else {
        return Err("native record prefix count is undefined".into());
    };
    let kind = MachineIntegerType::from_c_type(value.c_type())
        .filter(|kind| {
            matches!(
                kind,
                MachineIntegerType::Int32
                    | MachineIntegerType::Int64
                    | MachineIntegerType::UInt32
                    | MachineIntegerType::UInt64
            )
        })
        .ok_or("native record prefix count is not a native integer")?;
    let count = crate::kernel::eval::pointer_domains::native_count_observation(
        kind,
        crate::kernel::spec::c_value_bitvector_term(value)
            .ok_or("native record prefix count lacks an exact native observation")?,
    )
    .ok_or("native record prefix count has an incompatible format")?;
    Ok((count.into(), context))
}

/// Validate typed place metadata against existing semantic authority. This is
/// deliberately separate from address-only resource-expression evaluation.
pub(crate) fn check_native_record_specs(
    state: &CState,
    specs: &[CResourceSpec],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let mut budget = ExecutionBudget::beside_live_state();
    for spec in specs {
        if spec.native_record_places().is_empty() {
            continue;
        }
        let active = resource_spec_guard_is_active(state, state, spec, assumptions, &mut budget)
            .map_err(|_| "native record guard evaluation exceeded its budget".to_string())?
            .map_err(|_| "native record place guard is not established".to_string())?;
        if !active {
            continue;
        }
        for requirement in spec.native_record_places() {
            if let Some(count) = &requirement.prefix_count {
                let (count, context) = requirement_count(state, count, assumptions)?;
                if count
                    .as_const()
                    .is_some_and(|value| value == &num_bigint::BigInt::from(0))
                    || context.decide(&ConditionTerm::integer_equal(
                        count.as_ref().clone(),
                        IntegerTerm::constant_i64(0),
                    )) == Some(true)
                {
                    continue;
                }
                let pointer = requirement_pointer(state, requirement, &context, false)?;
                let selection = CAggregateMemberSelection {
                    layout: requirement.layout.clone(),
                    path: Arc::from([]),
                    value_type: CType::UInt8Array(requirement.layout.size_bytes()),
                };
                let Some((_, guards)) = state
                    .memory()
                    .guarded_native_record_selection(&pointer, &selection, &context)
                else {
                    return Err(
                        "native record prefix has no matching declared record layout".into(),
                    );
                };
                if guards
                    .iter()
                    .any(|guard| context.decide(guard) != Some(true))
                {
                    return Err(
                        "native record prefix layout selection has an unproved position".into(),
                    );
                }
                let span = crate::kernel::eval::pointer_domains::checked_pointer_span(
                    state,
                    &pointer,
                    IntegerTerm::constant_i64(0),
                    count.as_ref().clone(),
                    requirement.layout.size_bytes(),
                    crate::kernel::eval::pointer_domains::PointerDomainView::Typed,
                    &context,
                );
                if !matches!(span, Ok(crate::kernel::eval::pointer_domains::PointerDomainCheck::Checked(guards)) if guards.iter().all(|guard| context.decide(guard) == Some(true)))
                {
                    return Err("native record prefix exceeds the retained record sequence".into());
                }
                continue;
            }
            check_record_place(state, requirement, assumptions)?;
        }
    }
    super::native_span_inputs::check_native_span_specs(state, specs, assumptions)
}

pub(super) fn check_record_place(
    state: &CState,
    requirement: &CNativeRecordPlaceRequirement,
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let pointer = requirement_pointer(state, requirement, assumptions, false)?;
    let checked = state
        .memory()
        .checked_native_record_pointer(&pointer)
        .ok_or("native record place has no authenticated input or declaration")?;
    if !state
        .memory()
        .has_aggregate_object_domain(&checked, &requirement.layout)
    {
        return Err("native record place disagrees with its retained declaration".into());
    }
    Ok(())
}

/// Only symbolic entry or an authenticated opening of this exact body may
/// install these rows. The resulting state gains no ownership or loadability.
pub(crate) fn assume_native_record_specs(
    state: &CState,
    specs: &[CResourceSpec],
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    assume_native_record_specs_in(state, specs, assumptions, false)
}

fn assume_native_record_specs_in(
    state: &CState,
    specs: &[CResourceSpec],
    assumptions: &PureFactContext,
    source_entry: bool,
) -> Result<CState, String> {
    let mut next = state.clone();
    let mut budget = ExecutionBudget::beside_live_state();
    for spec in specs {
        if spec.native_record_places().is_empty() {
            continue;
        }
        let active =
            match resource_spec_guard_is_active(state, state, spec, assumptions, &mut budget) {
                Ok(Ok(active)) => active,
                Ok(Err(_)) => continue,
                Err(_) => return Err("native record guard evaluation exceeded its budget".into()),
            };
        if !active {
            continue;
        }
        for requirement in spec.native_record_places() {
            if let Some(count) = &requirement.prefix_count {
                let (count, context) = requirement_count(&next, count, assumptions)?;
                if count
                    .as_const()
                    .is_some_and(|value| value == &num_bigint::BigInt::from(0))
                    || context.decide(&ConditionTerm::integer_equal(
                        count.as_ref().clone(),
                        IntegerTerm::constant_i64(0),
                    )) == Some(true)
                {
                    continue;
                }
                let pointer = requirement_pointer(&next, requirement, &context, source_entry)?;
                next.set_memory(next.memory().clone().with_native_record_prefix(
                    pointer,
                    requirement.layout.clone(),
                    count,
                )?);
                continue;
            }
            let pointer = requirement_pointer(&next, requirement, assumptions, source_entry)?;
            next.set_memory(
                next.memory()
                    .clone()
                    .with_native_record_input(pointer, requirement.layout.clone())?,
            );
        }
    }
    super::native_span_inputs::assume_native_span_specs_in(&next, specs, assumptions, source_entry)
}

/// Assumes only the direct declared bodies of occurrences actually held here.
/// It never visits child resources or an unselected match arm.
pub(super) fn specs_have_native_places(specs: &[CResourceSpec]) -> bool {
    specs.iter().any(|spec| {
        !spec.native_record_places().is_empty() || !spec.native_span_requirements().is_empty()
    })
}

pub(crate) fn interface_has_native_output_places(interface: &CFunctionContractInterface) -> bool {
    specs_have_native_places(interface.resource_ensures())
        || interface
            .resource_ensures()
            .iter()
            .filter_map(CResourceSpec::declared_name)
            .any(|name| {
                indexed_native_definition(interface.composite_resource_definitions(), name)
                    .is_some_and(|definition| {
                        specs_have_native_places(definition.contains())
                            || definition.matched.as_ref().is_some_and(|body| {
                                body.arms
                                    .iter()
                                    .any(|arm| specs_have_native_places(&arm.contains))
                            })
                    })
            })
}

pub(crate) fn check_native_output_places(
    state: &CState,
    interface: &CFunctionContractInterface,
    assumptions: &PureFactContext,
) -> Result<(), String> {
    check_native_record_specs(state, interface.resource_ensures(), assumptions)?;
    let mut budget = ExecutionBudget::beside_live_state();
    for spec in interface.resource_ensures() {
        if spec.declared_name().is_none() {
            continue;
        }
        let active = resource_spec_guard_is_active(state, state, spec, assumptions, &mut budget)
            .map_err(|_| "native output guard evaluation exceeded its budget".to_string())?
            .map_err(|_| "native output guard is not established".to_string())?;
        if !active {
            continue;
        }
        let fact = evaluate_function_resource_spec(state, spec, assumptions, &mut budget)
            .map_err(|_| "native output evaluation exceeded its budget".to_string())?
            .map_err(|_| "native output carrier cannot be evaluated".to_string())?;
        check_native_composite_formation(
            state,
            &fact,
            interface.composite_resource_definitions(),
            assumptions,
        )?;
        if !check_native_required_formations(
            state,
            &fact,
            interface.composite_resource_definitions(),
            assumptions,
        ) {
            return Err("native output body places are not established".into());
        }
    }
    Ok(())
}

pub(crate) fn assume_checked_native_output_places(
    state: &CState,
    outputs: &ResourceContext,
    interface: &CFunctionContractInterface,
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    if !interface_has_native_output_places(interface) {
        return Ok(state.clone());
    }
    let evaluation = assume_native_record_specs(state, interface.resource_ensures(), assumptions)?;
    let output_scope = evaluation.clone().with_resource_context(outputs.clone());
    let assumed = assume_held_native_record_places(
        &output_scope,
        interface.composite_resource_definitions(),
        assumptions,
    )?;
    // The selected output heads authorize admission; reading their carrier
    // expressions can also need a caller's preserved descriptor views. Check
    // the admitted geometry in the original observation context, without
    // publishing any scratch output-body resources.
    let checked = state.clone().with_memory(assumed.memory().clone());
    check_native_output_places(&checked, interface, assumptions)?;
    Ok(checked)
}

fn indexed_native_definition<'a>(
    definitions: &'a [CCompositeResourceDefinition],
    name: &str,
) -> Option<&'a CCompositeResourceDefinition> {
    let index = definitions
        .binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(name)
        })
        .ok()?;
    Some(&definitions[index])
}

/// Authenticate formation of this head from its actual retained carriers.
/// This checks only its immediate declared body and never installs witnesses.
pub(crate) fn check_native_composite_formation(
    state: &CState,
    composite: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let CResource::Composite { name, arguments } = composite.resource() else {
        return Ok(());
    };
    let Some(definition) = indexed_native_definition(definitions, name) else {
        return Ok(());
    };
    if !specs_have_native_places(definition.contains()) {
        return Ok(());
    }
    if composite.has_proven_zero_quantity(assumptions) {
        return Ok(());
    }
    if definition.instance_schema.is_some()
        || definition.matched.is_some()
        || definition.parameters().len() != arguments.len()
    {
        return Err("native composite formation requires its exact plain body".into());
    }
    let mut evaluation = state.clone();
    for (parameter, argument) in definition.parameters().iter().zip(arguments.iter()) {
        let value = argument
            .as_c_value()
            .ok_or("native composite requires C arguments")?;
        if value.c_type() != parameter.c_type() {
            return Err("native composite argument type mismatch".into());
        }
        evaluation.locals.set_typed(
            parameter.name().to_string(),
            value.clone(),
            parameter.c_type(),
        );
    }
    bind_composite_witnesses(definition, arguments, &mut evaluation, assumptions)
        .ok_or("native composite witness arguments are not established")?;
    // A held checked head already carries its immediate body's authority.
    // Expose only that actual supporting occurrence while rechecking native
    // carrier reads; an absent requested head must supply its real body units.
    if let Some(held) = state
        .resources()
        .directly_supporting_fact(composite, assumptions)
        && let Some(expanded) = expand_composite_resource_fact(
            evaluation.resources(),
            held,
            definitions,
            evaluation.memory(),
            assumptions,
        )
    {
        evaluation = evaluation.with_resource_context(expanded);
    }
    let mut budget = ExecutionBudget::beside_live_state();
    match evaluate_composite_resource_body_condition(
        definition,
        &evaluation,
        assumptions,
        &mut budget,
    ) {
        Some(false) => Ok(()),
        Some(true) => check_native_record_specs(&evaluation, definition.contains(), assumptions),
        None => Err("native composite body guard is not established".into()),
    }
}

/// Validate each absent head before raw body containment could create it.
/// Existing exact heads carry their already-checked promises; child resources
/// are visited only along this requested formation, never by an ambient scan.
pub(crate) fn check_native_required_formations(
    state: &CState,
    required: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> bool {
    fn walk(
        state: &CState,
        required: &CResourceFact,
        definitions: &[CCompositeResourceDefinition],
        assumptions: &PureFactContext,
        seen: &mut BTreeSet<CResourceFact>,
    ) -> bool {
        if !matches!(required.resource(), CResource::Composite { .. })
            || state.resources().satisfies_fact(required, assumptions)
        {
            return true;
        }
        if !seen.insert(required.clone()) {
            return true;
        }
        if check_native_composite_formation(state, required, definitions, assumptions).is_err() {
            return false;
        }
        let singleton =
            ResourceContext::new_with_equalities(assumptions).unchecked_with_fact(required.clone());
        let Some(expanded) = expand_composite_resource_fact(
            &singleton,
            required,
            definitions,
            state.memory(),
            assumptions,
        ) else {
            return true;
        };
        if expanded == singleton {
            return true;
        }
        expanded
            .facts()
            .iter()
            .all(|child| walk(state, child, definitions, assumptions, seen))
    }
    walk(
        state,
        required,
        definitions,
        assumptions,
        &mut BTreeSet::new(),
    )
}

fn assume_held_native_record_places(
    state: &CState,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    assume_selected_held_native_record_places(state, definitions, assumptions, None)
}

/// Reconstruct only the native metadata admitted by this exact held head.
/// Ambient resources remain available for evaluating its explicit carrier expressions.
pub(crate) fn assume_checked_native_composite_places(
    state: &CState,
    selected: &CResourceFact,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    let Some(authority) = state
        .resources()
        .directly_supporting_fact(selected, assumptions)
    else {
        return Ok(state.clone());
    };
    assume_selected_held_native_record_places(state, definitions, assumptions, Some(authority))
}

fn assume_selected_held_native_record_places(
    state: &CState,
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
    selected: Option<&CResourceFact>,
) -> Result<CState, String> {
    let mut next = state.clone();
    for fact in state.resources().facts() {
        if selected.is_some_and(|selected| selected != fact) {
            continue;
        }
        if fact.is_own() && !fact.has_proven_positive_quantity(assumptions) {
            continue;
        }
        let (name, arguments, instance) = match fact.resource() {
            CResource::Composite { name, arguments } => (name.as_str(), arguments.as_ref(), None),
            CResource::Instance(instance) => {
                (instance.name(), instance.arguments(), Some(instance))
            }
            _ => continue,
        };
        let Ok(index) = definitions.binary_search_by(|definition| {
            crate::instrumentation::record_deterministic_work(1);
            definition.name().cmp(name)
        }) else {
            continue;
        };
        let definition = &definitions[index];
        if definition.parameters.len() != arguments.len() {
            continue;
        }
        let mut evaluation = if let Some(instance) = instance {
            instance_body_evaluation(&next, instance, definition)
                .map_err(|_| "could not bind the held native record instance".to_string())?
        } else {
            if definition.instance_schema.is_some() {
                continue;
            }
            let mut evaluation = next.clone();
            for (parameter, argument) in definition.parameters().iter().zip(arguments) {
                let value = argument
                    .as_c_value()
                    .ok_or("native record body requires C arguments")?;
                if value.c_type() != parameter.c_type() {
                    return Err("native record body argument type mismatch".into());
                }
                evaluation.locals.set_typed(
                    parameter.name().to_string(),
                    value.clone(),
                    parameter.c_type(),
                );
            }
            if bind_composite_witnesses(definition, arguments, &mut evaluation, assumptions)
                .is_none()
            {
                continue;
            }
            evaluation
        };
        let specs = if let Some(instance) = instance.filter(|_| definition.matched.is_some()) {
            let Ok((arm, constructor)) =
                selected_instance_match_arm(instance, definition, definitions, assumptions)
            else {
                continue;
            };
            let AlgebraicTermNode::Constructor { fields, .. } = constructor.node else {
                continue;
            };
            for (name, value) in arm.bindings.iter().zip(&fields) {
                if let AlgebraicValue::C(value) = value {
                    let value = arm_binding_program_spelling(value, assumptions)
                        .unwrap_or_else(|| value.clone());
                    let ty = value.c_type();
                    evaluation.locals.set_typed(name.clone(), value, ty);
                }
            }
            arm.contains.as_slice()
        } else {
            if definition.matched.is_some() {
                continue;
            }
            definition.contains()
        };
        let mut budget = ExecutionBudget::beside_live_state();
        if evaluate_composite_resource_body_condition(
            definition,
            &evaluation,
            assumptions,
            &mut budget,
        ) != Some(true)
        {
            continue;
        }
        // The selected held occurrence already carries its checked body
        // authority. Expose that exact one-level body only in the scratch
        // evaluation used to read typed input carriers; native execution still
        // sees the caller's opaque head until an explicit opening exchanges it.
        if instance.is_none()
            && let Some(expanded) = expand_composite_resource_fact(
                evaluation.resources(),
                fact,
                definitions,
                evaluation.memory(),
                assumptions,
            )
        {
            evaluation = evaluation.with_resource_context(expanded);
        }
        if instance.is_some() {
            // The selected held instance carries only this immediate body.
            // Keep the projection in scratch state so field carriers can be
            // read without publishing any body ownership to native execution.
            let body = evaluate_function_resource_context_with_normalization(
                &evaluation,
                specs,
                &[],
                assumptions,
                &mut budget,
                false,
            )
            .map_err(|_| "held instance native carrier evaluation exceeded its budget".to_string())?
            .map_err(|_| "could not evaluate held instance native carrier body".to_string())?
            .0;
            evaluation = evaluation.with_resource_context(body);
        }
        let assumed = assume_native_record_specs(&evaluation, specs, assumptions)?;
        next.set_memory(assumed.memory().clone());
    }
    Ok(next)
}

/// Source symbolic-entry admission: bind in a scratch state, retain exact
/// held occurrences, and return only the resulting memory map to the caller.
pub(crate) fn c_state_with_assumed_native_record_inputs(
    state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    definitions: &[CCompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    let held_has_places = state.resources().facts().iter().any(|fact| {
        if fact.is_own() && !fact.has_proven_positive_quantity(assumptions) {
            return false;
        }
        let name = match fact.resource() {
            CResource::Composite { name, .. } => name.as_str(),
            CResource::Instance(instance) => instance.name(),
            _ => return false,
        };
        indexed_native_definition(definitions, name).is_some_and(|definition| {
            specs_have_native_places(definition.contains())
                || definition.matched.as_ref().is_some_and(|body| {
                    body.arms
                        .iter()
                        .any(|arm| specs_have_native_places(&arm.contains))
                })
        })
    });
    if function
        .contract_interface()
        .native_span_expression_inputs()
        .is_empty()
        && !specs_have_native_places(function.resource_requires())
        && !super::valid_places::has_entry_requirements(
            function.contract_interface().contract_requires(),
        )
        && !held_has_places
    {
        return Ok(state.clone());
    }
    if function.parameters().len() != arguments.len() {
        return Err("native input argument count mismatch".into());
    }
    let mut entry = state.clone();
    for (parameter, argument) in function.parameters().iter().zip(arguments) {
        let CExpression::Value(value) = argument else {
            return Err("native inputs require evaluated arguments".into());
        };
        if value.c_type() != parameter.c_type() {
            return Err("native input argument type mismatch".into());
        }
        if let Some(layout) = parameter.aggregate_layout() {
            let Some(CLocalBinding::AggregateObject {
                slot, layout: held, ..
            }) = state.locals.binding(parameter.name())
            else {
                return Err("native aggregate input must already be materialized".into());
            };
            if held != layout
                || !matches!(value, CValue::Pointer(pointer) if pointer.pointer() == slot)
            {
                return Err(
                    "native aggregate input differs from its retained parameter object".into(),
                );
            }
        } else {
            entry.locals.set_typed(
                parameter.name().to_string(),
                value.clone(),
                parameter.c_type(),
            );
        }
    }
    let entry =
        assume_native_record_specs_in(&entry, function.resource_requires(), assumptions, true)?;
    let entry = assume_held_native_record_places(&entry, definitions, assumptions)?;
    let entry = super::valid_places::assume_entry_requirements(
        &entry,
        function.contract_interface().contract_requires(),
        assumptions,
    )?;
    let entry = super::native_span_inputs::assume_native_span_requirements_in(
        &entry,
        function
            .contract_interface()
            .native_span_expression_inputs(),
        assumptions,
        true,
    )?;
    Ok(state.clone().with_memory(entry.memory().clone()))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn source_entry_carrier_observation_does_not_relax_checked_call_reads() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = Arc::new(CAggregateLayout::new(
            8,
            8,
            vec![CAggregateField::new("next", 0, CType::Int32Pointer)],
        ));
        let input = Variable(988_229);
        let owner = CPointerValue::new(Pointer::symbolic(input), CType::UInt8Pointer)
            .with_designation(PointerDesignation::Unresolved(input));
        let memory = CMemory::new()
            .with_native_record_input(owner.clone(), layout.clone())
            .unwrap();
        let state = CState::new()
            .with_memory(memory)
            .with_local("owner", CValue::Pointer(owner));
        let requirement = CNativeRecordPlaceRequirement {
            carrier: c_typed_load(
                CExpression::MemberAddress {
                    object: Box::new(c_variable("owner")),
                    selection: Arc::new(CAggregateMemberSelection {
                        layout,
                        path: vec!["next".into()].into(),
                        value_type: CType::Int32Pointer,
                    }),
                },
                CType::Int32Pointer,
            ),
            layout: Arc::new(CAggregateLayout::new(
                4,
                4,
                vec![CAggregateField::new("value", 0, CType::Int32)],
            )),
            prefix_count: None,
        };
        let assumptions = PureFactContext::new();
        let pointer = requirement_pointer(&state, &requirement, &assumptions, true).unwrap();
        assert!(matches!(
            pointer.designation(),
            Some(PointerDesignation::Loaded(_))
        ));
        assert!(requirement_pointer(&state, &requirement, &assumptions, false).is_err());
        assert!(
            check_native_record_specs(
                &state,
                &[CResourceSpec::owned_memory(CMemorySegment::new(
                    c_variable("owner"),
                    c_int32_literal(0),
                    c_int32_literal(1)
                ),)
                .with_native_record_places(vec![requirement])],
                &assumptions
            )
            .is_err()
        );
    }

    #[test]
    fn held_native_prefix_reads_only_checked_body_authority_in_scratch_state() {
        let _session = crate::kernel::VerificationSession::enter();
        let layout = Arc::new(CAggregateLayout::new(
            8,
            8,
            vec![CAggregateField::new("data", 0, CType::Int32Pointer)],
        ));
        let identity = Variable(988_220);
        let address = Pointer::symbolic(identity);
        let origin = CPointerValue::new(address.clone(), CType::UInt8Pointer)
            .with_designation(PointerDesignation::Unresolved(identity));
        let before = CMemory::new()
            .with_native_record_input(origin.clone(), layout.clone())
            .unwrap();
        let pointer = before.checked_native_record_pointer(&origin).unwrap();
        let carrier = c_typed_load(
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
        let definition = |field_width| {
            CCompositeResourceDefinition::new(
                "HeldPrefix",
                vec![c_parameter("owner", pointer.c_type())],
                None,
                false,
                vec![
                    CResourceSpec::owned_memory(
                        CMemorySegment::new(
                            c_variable("owner"),
                            c_int32_literal(0),
                            c_int32_literal(1),
                        )
                        .with_element_width(field_width),
                    )
                    .with_native_record_places(vec![
                        CNativeRecordPlaceRequirement {
                            carrier: c_variable("owner"),
                            layout: layout.clone(),
                            prefix_count: None,
                        },
                    ]),
                    CResourceSpec::owned_memory(
                        CMemorySegment::new(
                            carrier.clone(),
                            c_int32_literal(0),
                            c_int32_literal(1),
                        )
                        .with_element_width(4),
                    )
                    .with_native_span_requirements(vec![
                        CNativeSpanRequirement {
                            access_policy: crate::kernel::CTypedAccessPolicy::NativeObjectOnly,
                            carrier: carrier.clone(),
                            element_type: CType::Int32,
                            count: c_int32_literal(1),
                        },
                    ]),
                ],
                vec![],
            )
        };
        let head = CResourceFact::own_composite(
            "HeldPrefix".into(),
            vec![CValue::Pointer(pointer.clone())],
        );
        let assumptions = PureFactContext::new();
        for (field_width, initialized) in [(8, true), (4, true), (8, false)] {
            let memory = if initialized {
                before.clone().with_initialized_object(&address, 8)
            } else {
                before.clone().with_uninitialized_object(address.clone(), 8)
            };
            let state = CState::new()
                .with_memory(memory)
                .with_local("owner", CValue::Pointer(pointer.clone()))
                .with_resource_context(ResourceContext::new().unchecked_with_fact(head.clone()));
            let definition = definition(field_width);
            let admitted = assume_checked_native_composite_places(
                &state,
                &head,
                std::slice::from_ref(&definition),
                &assumptions,
            );
            if field_width == 8 && initialized {
                let admitted = admitted.unwrap();
                assert_eq!(admitted.resources(), state.resources());
                assert_eq!(admitted.locals(), state.locals());
                assert_eq!(
                    admitted.memory().heap.initialized,
                    state.memory().heap.initialized
                );
                assert_eq!(admitted.memory().cells, state.memory().cells);
                assert_eq!(
                    admitted.memory().heap.native_record_inputs.len(),
                    before.heap.native_record_inputs.len() + 1
                );
                check_native_composite_formation(
                    &admitted,
                    &head,
                    std::slice::from_ref(&definition),
                    &assumptions,
                )
                .expect("the actual held head supplies its scratch field-read authority");
                let witness_without_authority = admitted
                    .clone()
                    .with_resource_context(ResourceContext::new());
                assert!(
                    check_native_composite_formation(
                        &witness_without_authority,
                        &head,
                        std::slice::from_ref(&definition),
                        &assumptions,
                    )
                    .is_err(),
                    "a retained input witness must not supply absent field-read authority"
                );
                let paths = evaluate_c_expression_paths(
                    &admitted,
                    &carrier,
                    &assumptions,
                    &mut ExecutionBudget::default(),
                )
                .unwrap();
                assert!(paths.iter().all(|path| matches!(
                    path.outcome,
                    CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
                )));
                let absent = state.clone().with_resource_context(ResourceContext::new());
                let unchanged = assume_checked_native_composite_places(
                    &absent,
                    &head,
                    std::slice::from_ref(&definition),
                    &assumptions,
                )
                .unwrap();
                assert_eq!(unchanged, absent);
            } else {
                assert!(
                    admitted.is_err(),
                    "field_width={field_width}, initialized={initialized}"
                );
            }
        }
    }

    fn definition() -> (Arc<CAggregateLayout>, CCompositeResourceDefinition) {
        let layout = Arc::new(CAggregateLayout::new(
            4,
            4,
            vec![CAggregateField::new("value", 0, CType::Int32)],
        ));
        let body = CResourceSpec::owned_memory(
            CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(1))
                .with_element_width(4),
        )
        .with_native_record_places(vec![CNativeRecordPlaceRequirement {
            carrier: c_variable("p"),
            layout: layout.clone(),
            prefix_count: None,
        }]);
        (
            layout,
            CCompositeResourceDefinition::new(
                "NativeCell",
                vec![c_parameter("p", CType::Int32Pointer)],
                None,
                false,
                vec![body],
                vec![],
            ),
        )
    }

    fn head(pointer: CPointerValue, quantity: Option<u32>) -> CResourceFact {
        let resource = CResource::Composite {
            name: "NativeCell".into(),
            arguments: vec![AlgebraicValue::C(CValue::Pointer(pointer))].into(),
        };
        match quantity {
            Some(quantity) => {
                CResourceFact::Own(resource, Box::new(Bitvector32Term::Constant(quantity)))
            }
            None => CResourceFact::View(resource),
        }
    }

    #[test]
    fn native_record_zero_count_does_not_mint_validity_but_positive_heads_and_views_do() {
        let (layout, definition) = definition();
        let variable = Variable(988_210);
        let pointer = CPointerValue::new(Pointer::symbolic(variable), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(variable));
        for quantity in [Some(0), Some(1), None] {
            let state = CState::new().with_resource_context(
                ResourceContext::new().unchecked_with_fact(head(pointer.clone(), quantity)),
            );
            let assumed = assume_held_native_record_places(
                &state,
                std::slice::from_ref(&definition),
                &PureFactContext::new(),
            )
            .unwrap();
            let checked = assumed.memory().checked_native_record_pointer(&pointer);
            if quantity == Some(0) {
                assert!(checked.is_none());
                assert_eq!(state.memory(), assumed.memory());
            } else {
                assert!(
                    assumed
                        .memory()
                        .has_aggregate_object_domain(&checked.unwrap(), &layout)
                );
            }
            assert_eq!(state.resources(), assumed.resources());
            assert_eq!(state.locals(), assumed.locals());
            assert_eq!(assumed.memory().cells.representation_len(), 0);
        }
    }

    #[test]
    fn native_composite_formation_requires_carrier_type_even_with_identical_owned_bytes() {
        let (layout, definition) = definition();
        for native_record in [false, true] {
            let address = CMemory::local_pointer("native-formation");
            let memory = if native_record {
                CMemory::new().with_declared_aggregate_block(address.block.clone(), &layout)
            } else {
                CMemory::new().with_declared_scalar_block(address.block.clone(), 4, CType::Int32)
            };
            let pointer = if native_record {
                memory
                    .declared_aggregate_pointer(&address, &layout)
                    .unwrap()
                    .with_type(CType::Int32Pointer)
            } else {
                memory
                    .declared_scalar_pointer(&address, CType::Int32)
                    .unwrap()
            };
            let available = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(address, 0u32.into(), 1u32.into(), 4),
            ));
            let required = head(pointer, Some(1));
            let assumptions = PureFactContext::new();
            let state = CState::new()
                .with_memory(memory.clone())
                .with_resource_context(available.clone());
            assert_eq!(
                check_native_required_formations(
                    &state,
                    &required,
                    std::slice::from_ref(&definition),
                    &assumptions
                ),
                native_record
            );
            assert_eq!(
                resource_context_satisfies_definitional_fact(
                    &available,
                    &required,
                    std::slice::from_ref(&definition),
                    &memory,
                    &assumptions
                ),
                native_record
            );
            assert_eq!(
                consume_resource_fact_definitionally(
                    &available,
                    &required,
                    std::slice::from_ref(&definition),
                    &memory,
                    &assumptions
                )
                .is_some(),
                native_record
            );
        }
    }
}
