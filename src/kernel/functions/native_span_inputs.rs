//! Native typed-prefix requirements are separate from byte authority and
//! initialization. Only symbolic entry or a selected held occurrence assumes
//! them; actual calls and resource creation check the retained full carrier.
use super::*;

/// Transport only explicitly selected typed prefixes across an interface.
/// The concrete arm proves geometry; admission names the successor's exact
/// fresh carrier and contributes neither bytes nor initialized values.
pub(crate) fn project_interface_native_spans(
    arm: &CState,
    successor: &CState,
    specs: &[CResourceSpec],
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    check_native_span_specs(arm, specs, assumptions)?;
    let successor_specs = specs
        .iter()
        .map(|spec| {
            let requirements = spec
                .native_span_requirements()
                .iter()
                .map(|requirement| {
                    let mut requirement = requirement.clone();
                    if let CExpression::Variable(name) = &requirement.carrier
                        && successor.global_object_type(name).is_none()
                        && successor.local_object_type(name).is_some()
                        && let Some(value @ CValue::Pointer(_)) = successor.locals().get(name)
                    {
                        // The independently reconstructed abstract local binding is
                        // the complete phi carrier. Reading its private stack slot
                        // would incorrectly require byte authority the join dropped.
                        requirement.carrier = CExpression::Value(value.clone());
                    }
                    requirement
                })
                .collect();
            spec.clone().with_native_span_requirements(requirements)
        })
        .collect::<Vec<_>>();
    assume_native_span_specs(successor, &successor_specs, assumptions)
}

fn is_declared_private_member_read(state: &CState, expression: &CExpression) -> bool {
    let CExpression::TypedLoad {
        pointer,
        value_type,
        ..
    } = expression
    else {
        return false;
    };
    let CExpression::MemberAddress { object, selection } = pointer.as_ref() else {
        return false;
    };
    let CExpression::Variable(name) = object.as_ref() else {
        return false;
    };
    let Some(CLocalBinding::AggregateObject { layout, .. }) = state.locals().binding(name) else {
        return false;
    };
    layout == selection.layout.as_ref()
        && *value_type == selection.value_type
        && LoadKind::of_type(*value_type).is_some()
        && layout
            .member_at_path(&selection.path)
            .is_some_and(|(_, declared)| declared == *value_type)
}

pub(super) fn component(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    source_entry: bool,
) -> Result<(CValue, PureFactContext), String> {
    // Symbolic source entry observes the exact contract carrier through the
    // same selected-snapshot mode as record-place admission. Other observations
    // use checked local/global access or require the full byte owner.
    let _entry_observation = source_entry.then(crate::kernel::eval::SpecificationReadScope::enter);
    let executable = if source_entry {
        assumptions
            .clone()
            .allow_symbolic_contract_loads()
            .observe_pointer_addresses()
    } else if is_declared_private_member_read(state, expression) {
        // Private by-value storage uses ordinary executable local access. The
        // evaluator still checks the layout, lifetime and complete initialized
        // read; this does not enable symbolic or address-only observation.
        assumptions.clone().without_pointer_address_observation()
    } else if matches!(expression, CExpression::Variable(name) if matches!(
        state.locals().binding(name),
        Some(CLocalBinding::GlobalObject { .. })
    )) {
        // A direct declared global slot has the same storage-read authority
        // here as in executable C. Its initialized complete pointer value is
        // still loaded normally; this does not authorize its referent or any
        // read through a pointer field or an address-equal alias.
        assumptions.clone().without_pointer_address_observation()
    } else {
        assumptions
            .clone()
            .without_pointer_address_observation()
            .require_owned_expression_loads()
    };
    let mut budget = ExecutionBudget::beside_live_state();
    let paths = evaluate_c_expression_paths(state, expression, &executable, &mut budget)
        .map_err(|_| "native span evaluation exceeded its budget".to_string())?;
    let [path] = paths.as_slice() else {
        return Err("native span needs one established expression value".into());
    };
    let CExpressionOutcome::Value(value) = &path.outcome else {
        return Err("native span requires a defined expression value".into());
    };
    let context = assumptions_with_path_context(&executable, &path.facts, &[]);
    if path
        .obligations
        .iter()
        .any(|goal| !required_obligation_is_exactly_discharged(&context, goal.proposition()))
    {
        return Err("native span has an unproved expression condition".into());
    }
    Ok((value.clone(), context))
}

fn requirement_values(
    state: &CState,
    requirement: &CNativeSpanRequirement,
    assumptions: &PureFactContext,
    source_entry: bool,
) -> Result<(CPointerValue, SharedIntegerTerm, PureFactContext), String> {
    let (carrier, context) = component(state, &requirement.carrier, assumptions, source_entry)?;
    let CValue::Pointer(pointer) = carrier else {
        return Err("native span carrier is not a pointer".into());
    };
    if pointer.c_type().pointee_type() != Some(requirement.element_type)
        || !matches!(
            requirement.element_type,
            CType::Int32 | CType::UInt32 | CType::Int64 | CType::UInt8
        )
    {
        return Err("native span disagrees with its declared scalar pointer type".into());
    }
    let (count, context) = component(state, &requirement.count, &context, source_entry)?;
    let ty = MachineIntegerType::from_c_type(count.c_type())
        .filter(|ty| {
            matches!(
                ty,
                MachineIntegerType::Int32
                    | MachineIntegerType::Int64
                    | MachineIntegerType::UInt32
                    | MachineIntegerType::UInt64
            )
        })
        .ok_or("native span count is not an admitted native integer")?;
    let count = crate::kernel::eval::pointer_domains::native_count_observation(
        ty,
        crate::kernel::spec::c_value_bitvector_term(&count)
            .ok_or("native span count has no exact native observation")?,
    )
    .ok_or("native span count has an incompatible native format")?;
    Ok((pointer, count.into(), context))
}

pub(super) fn span_holds(
    state: &CState,
    pointer: &CPointerValue,
    element_type: CType,
    count: &SharedIntegerTerm,
    access_policy: CTypedAccessPolicy,
    assumptions: &PureFactContext,
) -> bool {
    // An empty prefix carries no object claim. Its witness separately grants
    // no pointer formation or access until a positive-count guard is known.
    if count
        .as_const()
        .is_some_and(|value| value == &num_bigint::BigInt::from(0))
        || [
            crate::kernel::eval::pointer_domains::domain_less_equal(
                IntegerTerm::constant_i64(0),
                count.as_ref().clone(),
            ),
            crate::kernel::eval::pointer_domains::domain_less_equal(
                count.as_ref().clone(),
                IntegerTerm::constant_i64(0),
            ),
        ]
        .iter()
        .all(|guard| assumptions.decide(guard) == Some(true))
    {
        return true;
    }
    let check = span_geometry(
        state,
        pointer,
        element_type,
        count,
        access_policy,
        assumptions,
    );
    matches!(check, Ok(crate::kernel::eval::pointer_domains::PointerDomainCheck::Checked(guards))
        if guards.iter().all(|guard| assumptions.decide(guard) == Some(true)))
}

fn span_geometry(
    state: &CState,
    pointer: &CPointerValue,
    element_type: CType,
    count: &SharedIntegerTerm,
    access_policy: CTypedAccessPolicy,
    assumptions: &PureFactContext,
) -> Result<
    crate::kernel::eval::pointer_domains::PointerDomainCheck,
    crate::kernel::eval::pointer_domains::PointerDomainRefusal,
> {
    if access_policy == CTypedAccessPolicy::NativeObjectOnly && element_type == CType::UInt8 {
        return crate::kernel::eval::pointer_domains::checked_native_byte_pointer_span(
            state,
            pointer,
            IntegerTerm::constant_i64(0),
            count.as_ref().clone(),
            assumptions,
        );
    }
    let check_span = match access_policy {
        CTypedAccessPolicy::NativeObjectOnly => {
            crate::kernel::eval::pointer_domains::checked_typed_pointer_span
        }
        CTypedAccessPolicy::CAllocatedAccessAllowed => {
            crate::kernel::eval::pointer_domains::checked_c_typed_pointer_span
        }
    };
    check_span(
        state,
        pointer,
        IntegerTerm::constant_i64(0),
        count.as_ref().clone(),
        element_type,
        assumptions,
    )
}

pub(super) fn check_native_span_requirements(
    state: &CState,
    requirements: &[CNativeSpanRequirement],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    for requirement in requirements {
        let values = requirement_values(state, requirement, assumptions, false);
        let (pointer, count, context) = values?;
        if !span_holds(
            state,
            &pointer,
            requirement.element_type,
            &count,
            requirement.access_policy,
            &context,
        ) {
            return Err("native scalar prefix has no checked full-carrier witness".into());
        }
    }
    Ok(())
}

// Resource annotations preserve the ordinary C allocated-access boundary.
// Absence of a typed domain is compatibility, not evidence for valid_place.
fn legacy_resource_span(
    state: &CState,
    requirement: &CNativeSpanRequirement,
    assumptions: &PureFactContext,
    source_entry: bool,
) -> Result<bool, String> {
    if state.typed_access_policy() != CTypedAccessPolicy::CAllocatedAccessAllowed
        || requirement.access_policy != CTypedAccessPolicy::CAllocatedAccessAllowed
    {
        return Ok(false);
    }
    let (pointer, count, context) =
        requirement_values(state, requirement, assumptions, source_entry)?;
    Ok(matches!(
        span_geometry(
            state,
            &pointer,
            requirement.element_type,
            &count,
            requirement.access_policy,
            &context
        ),
        Ok(crate::kernel::eval::pointer_domains::PointerDomainCheck::Legacy)
    ))
}

pub(super) fn check_native_span_specs(
    state: &CState,
    specs: &[CResourceSpec],
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let mut budget = ExecutionBudget::beside_live_state();
    for spec in specs {
        if spec.native_span_requirements().is_empty() {
            continue;
        }
        let active = resource_spec_guard_is_active(state, state, spec, assumptions, &mut budget)
            .map_err(|_| "native span guard evaluation exceeded its budget".to_string())?
            .map_err(|_| "native span guard is not established".to_string())?;
        if !active {
            continue;
        }
        for requirement in spec.native_span_requirements() {
            if !legacy_resource_span(state, requirement, assumptions, false)? {
                check_native_span_requirements(
                    state,
                    std::slice::from_ref(requirement),
                    assumptions,
                )?;
            }
        }
    }
    Ok(())
}

pub(super) fn assume_native_span_specs(
    state: &CState,
    specs: &[CResourceSpec],
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    assume_native_span_specs_in(state, specs, assumptions, false)
}

pub(super) fn assume_native_span_requirements_in(
    state: &CState,
    requirements: &[CNativeSpanRequirement],
    assumptions: &PureFactContext,
    source_entry: bool,
) -> Result<CState, String> {
    if requirements.is_empty() {
        return Ok(state.clone());
    }
    let mut next = state.clone();
    for requirement in requirements {
        let (pointer, count, context) =
            requirement_values(&next, requirement, assumptions, source_entry)?;
        if span_holds(
            &next,
            &pointer,
            requirement.element_type,
            &count,
            requirement.access_policy,
            &context,
        ) {
            continue;
        }
        if next.memory().native_input_is_slice(&pointer) {
            // Slice signatures already authenticate this exact carrier's
            // geometry. Entry setup precedes pure preconditions, so retain
            // that witness when the requested prefix bounds are undecided.
            // Calls still check this requirement under their actual facts.
            match span_geometry(
                &next,
                &pointer,
                requirement.element_type,
                &count,
                requirement.access_policy,
                &context,
            ) {
                Ok(crate::kernel::eval::pointer_domains::PointerDomainCheck::Checked(guards))
                    if guards
                        .iter()
                        .all(|guard| context.decide(guard) != Some(false)) =>
                {
                    continue;
                }
                _ => return Err("native prefix contradicts its retained slice carrier".into()),
            }
        }
        // Definite declared/carried geometry remains decisive. An input
        // assumption cannot widen an existing complete object domain.
        if matches!(
            pointer.designation(),
            Some(PointerDesignation::Object { .. })
        ) || crate::kernel::memory_provenance::resolve_loaded_pointer_carrier(&pointer, &context)
            .is_some_and(|resolved| {
                matches!(
                    resolved.designation(),
                    Some(PointerDesignation::Object { .. })
                )
            })
        {
            return Err("native prefix contradicts its retained complete carrier".into());
        }
        next.set_memory(next.memory().clone().with_typed_input_span(
            pointer,
            requirement.element_type,
            count,
            requirement.access_policy,
        )?);
    }
    Ok(next)
}

pub(super) fn assume_native_span_specs_in(
    state: &CState,
    specs: &[CResourceSpec],
    assumptions: &PureFactContext,
    source_entry: bool,
) -> Result<CState, String> {
    let mut next = state.clone();
    let mut budget = ExecutionBudget::beside_live_state();
    for spec in specs {
        if spec.native_span_requirements().is_empty() {
            continue;
        }
        let active =
            match resource_spec_guard_is_active(state, state, spec, assumptions, &mut budget) {
                Ok(Ok(active)) => active,
                Ok(Err(_)) => continue,
                Err(_) => return Err("native span guard evaluation exceeded its budget".into()),
            };
        if !active {
            continue;
        }
        for requirement in spec.native_span_requirements() {
            if !legacy_resource_span(&next, requirement, assumptions, source_entry)? {
                next = assume_native_span_requirements_in(
                    &next,
                    std::slice::from_ref(requirement),
                    assumptions,
                    source_entry,
                )?;
            }
        }
    }
    Ok(next)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn private_descriptor_observation_keeps_executable_read_checks() {
        let _session = crate::kernel::VerificationSession::enter();
        for value in [
            CValue::typed_pointer(Pointer::null(), CType::UInt8Pointer),
            CValue::UInt64(Bitvector32Term::UInt64Constant(1)),
        ] {
            let value_type = value.c_type();
            let layout =
                CAggregateLayout::new(8, 8, vec![CAggregateField::new("data", 0, value_type)]);
            let slot = CMemory::local_pointer("private-span-descriptor");
            let memory = CMemory::new()
                .with_declared_aggregate_block(slot.block.clone(), &layout)
                .store(slot.clone(), value);
            let mut state = CState::new().with_memory(memory.clone());
            state
                .locals
                .set_aggregate_object_at("out", layout.clone(), slot.clone());
            let expression = c_typed_load(
                CExpression::MemberAddress {
                    object: Box::new(c_variable("out")),
                    selection: Arc::new(CAggregateMemberSelection {
                        layout: Arc::new(layout),
                        path: vec!["data".into()].into(),
                        value_type,
                    }),
                },
                value_type,
            );
            let assumptions = PureFactContext::new();
            assert!(component(&state, &expression, &assumptions, false).is_ok());
            let undefined = state.clone().with_memory(
                CMemory::new()
                    .with_declared_aggregate_block(
                        slot.block.clone(),
                        match state.locals().binding("out") {
                            Some(CLocalBinding::AggregateObject { layout, .. }) => layout,
                            _ => unreachable!(),
                        },
                    )
                    .with_uninitialized_object(slot.clone(), 8),
            );
            assert!(component(&undefined, &expression, &assumptions, false).is_err());
            let expired = state
                .clone()
                .with_memory(memory.without_local_block(&slot.block));
            assert!(component(&expired, &expression, &assumptions, false).is_err());
            // Pointer/reference bindings do not own the descriptor's private slot.
            let external =
                state.with_local("out", CValue::typed_pointer(slot, CType::Int32Pointer));
            assert!(!is_declared_private_member_read(&external, &expression));
            assert!(component(&external, &expression, &assumptions, false).is_err());
        }
    }

    #[test]
    fn legacy_resource_span_never_establishes_explicit_typed_validity() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = CPointerValue::new(Pointer::symbolic(Variable(989_792)), CType::Int32Pointer);
        let state = CState::new().with_local("p", CValue::Pointer(pointer.clone()));
        let requirement = CNativeSpanRequirement {
            carrier: c_variable("p"),
            count: c_int32_literal(1),
            element_type: CType::Int32,
            access_policy: CTypedAccessPolicy::CAllocatedAccessAllowed,
        };
        let spec =
            span(c_variable("p"), 1).with_native_span_requirements(vec![requirement.clone()]);
        let context = PureFactContext::new();
        assert!(check_native_span_specs(&state, std::slice::from_ref(&spec), &context).is_ok());
        assert_eq!(
            assume_native_span_specs(&state, std::slice::from_ref(&spec), &context).unwrap(),
            state
        );
        assert!(!super::super::valid_places::holds(
            state.memory(),
            &pointer,
            &CPlaceType::Scalar(CType::Int32),
            CTypedAccessPolicy::CAllocatedAccessAllowed,
            &context
        ));
        assert!(
            check_native_span_requirements(&state, std::slice::from_ref(&requirement), &context)
                .is_err()
        );
        assert!(
            assume_native_span_requirements_in(&state, &[requirement], &context, false).is_err()
        );
        let strict = state.with_typed_access_policy(CTypedAccessPolicy::NativeObjectOnly);
        assert!(check_native_span_specs(&strict, std::slice::from_ref(&spec), &context).is_err());
        assert!(assume_native_span_specs(&strict, &[spec], &context).is_err());
    }

    #[test]
    fn c_resource_span_compatibility_never_widens_a_known_domain() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = CMemory::local_pointer("known-c-resource-domain");
        let memory = CMemory::new()
            .with_declared_array_block(address.block.clone(), CType::Int32, 1)
            .unwrap();
        let pointer = memory
            .declared_array_pointer(&address, CType::Int32, 1)
            .unwrap();
        let state = CState::new()
            .with_memory(memory)
            .with_local("p", CValue::Pointer(pointer));
        let spec =
            span(c_variable("p"), 2).with_native_span_requirements(vec![CNativeSpanRequirement {
                carrier: c_variable("p"),
                count: c_int32_literal(2),
                element_type: CType::Int32,
                access_policy: CTypedAccessPolicy::CAllocatedAccessAllowed,
            }]);
        let context = PureFactContext::new();
        assert!(check_native_span_specs(&state, std::slice::from_ref(&spec), &context).is_err());
        assert!(assume_native_span_specs(&state, &[spec], &context).is_err());
    }

    #[test]
    fn actual_span_observation_preserves_stored_carrier_under_address_observer() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = CMemory::local_pointer("stored-span-carrier");
        let value = CValue::Pointer(
            CPointerValue::new(Pointer::symbolic(Variable(989_790)), CType::Int32Pointer)
                .with_designation(PointerDesignation::Unresolved(Variable(989_791))),
        );
        let memory = CMemory::new()
            .with_declared_scalar_block(slot.block.clone(), 8, CType::Int32Pointer)
            .store(slot.clone(), value.clone());
        let storage = memory
            .declared_scalar_pointer(&slot, CType::Int32Pointer)
            .unwrap();
        let expression = c_typed_load(
            CExpression::Value(CValue::Pointer(storage)),
            CType::Int32Pointer,
        );
        let assumptions = PureFactContext::new().observe_pointer_addresses();
        let state = CState::new().with_memory(memory);
        assert!(component(&state, &expression, &assumptions, false).is_err());
        let readable = state.with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::view_memory(CMemoryRange::new_with_element_width(
                slot,
                0.into(),
                1.into(),
                8,
            )),
        ));
        assert_eq!(
            component(&readable, &expression, &assumptions, false)
                .unwrap()
                .0,
            value
        );
    }

    #[test]
    fn standalone_span_prerequisite_checks_geometry_without_byte_authority() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = CMemory::local_pointer("standalone-uninitialized-word");
        let memory = CMemory::new()
            .with_declared_scalar_block(address.block.clone(), 4, CType::UInt32)
            .with_uninitialized_object(address.clone(), 4);
        let pointer = memory
            .declared_scalar_pointer(&address, CType::UInt32)
            .unwrap();
        let state = CState::new().with_memory(memory);
        let requirement = CNativeSpanRequirement {
            carrier: CExpression::Value(CValue::Pointer(pointer.clone())),
            count: c_int32_literal(1),
            element_type: CType::UInt32,
            access_policy: CTypedAccessPolicy::NativeObjectOnly,
        };
        let assumptions = PureFactContext::new();
        assert!(
            check_native_span_requirements(
                &state,
                std::slice::from_ref(&requirement),
                &assumptions
            )
            .is_ok()
        );
        assert!(state.resources().facts().is_empty());
        assert!(
            !state
                .memory()
                .has_initialized_bytes_under(&address, 4, &assumptions)
        );
        let mut too_long = requirement.clone();
        too_long.count = c_int32_literal(2);
        assert!(check_native_span_requirements(&state, &[too_long], &assumptions).is_err());
        let mut raw = requirement;
        raw.carrier = CExpression::Value(CValue::Pointer(CPointerValue::new(
            pointer.pointer().clone(),
            pointer.c_type(),
        )));
        assert!(check_native_span_requirements(&state, &[raw], &assumptions).is_err());
    }

    #[test]
    fn actual_call_cannot_use_symbolic_span_assumption_staging() {
        let _session = crate::kernel::VerificationSession::enter();
        let input = Variable(991_341);
        let pointer = CPointerValue::new(Pointer::symbolic(input), CType::UInt32Pointer)
            .with_designation(PointerDesignation::Unresolved(input));
        let function = c_function(
            CType::Void,
            "needs-span",
            vec![c_parameter("p", CType::UInt32Pointer)],
            c_skip(),
        )
        .with_native_span_expression_inputs(vec![CNativeSpanRequirement {
            carrier: c_variable("p"),
            count: c_int32_literal(1),
            element_type: CType::UInt32,
            access_policy: CTypedAccessPolicy::NativeObjectOnly,
        }]);
        let state = CState::new().with_local("p", CValue::Pointer(pointer));
        let assumptions = PureFactContext::new();
        assert!(
            super::super::constructor_input::bind(
                &state,
                function.contract_interface(),
                &state,
                &assumptions
            )
            .is_none()
        );
        let assumed = assume_native_span_requirements_in(
            &state,
            function
                .contract_interface()
                .native_span_expression_inputs(),
            &assumptions,
            true,
        )
        .unwrap();
        assert!(
            super::super::constructor_input::bind(
                &assumed,
                function.contract_interface(),
                &assumed,
                &assumptions
            )
            .is_some()
        );
        assert!(assumed.resources().facts().is_empty());
    }

    #[test]
    fn native_byte_prefix_preserves_the_declared_word_and_its_uninitialized_bytes() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = CMemory::local_pointer("byte-prefix-word");
        let memory = CMemory::new()
            .with_declared_scalar_block(address.block.clone(), 4, CType::UInt32)
            .with_uninitialized_object(address.clone(), 4);
        let word = memory
            .declared_scalar_pointer(&address, CType::UInt32)
            .unwrap();
        let bytes = word.clone().with_type(CType::UInt8Pointer);
        let state = CState::new()
            .with_memory(memory)
            .with_local("p", CValue::Pointer(bytes.clone()));
        let assumptions = PureFactContext::new();
        let requirement = |count| {
            CResourceSpec::owned_memory(
                CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(count))
                    .with_element_width(1),
            )
            .with_native_span_requirements(vec![CNativeSpanRequirement {
                carrier: c_variable("p"),
                element_type: CType::UInt8,
                count: c_int32_literal(count),
                access_policy: CTypedAccessPolicy::NativeObjectOnly,
            }])
        };
        assert!(check_native_span_specs(&state, &[requirement(4)], &assumptions).is_ok());
        assert!(check_native_span_specs(&state, &[requirement(5)], &assumptions).is_err());
        assert_eq!(
            assume_native_span_specs(&state, &[requirement(4)], &assumptions).unwrap(),
            state
        );
        assert_eq!(bytes.designation(), word.designation());
        assert!(state.resources().facts().is_empty());
        assert!(
            !state
                .memory()
                .has_initialized_bytes_under(&address, 4, &assumptions)
        );
        assert!(
            state
                .memory()
                .declared_scalar_pointer(&address, CType::UInt8)
                .is_none()
        );
        let dead = state
            .clone()
            .with_memory(state.memory().clone().without_local_block(&address.block));
        assert!(check_native_span_specs(&dead, &[requirement(4)], &assumptions).is_err());
    }

    #[test]
    fn native_slice_entry_defers_only_undecided_prefix_bounds_without_replacing_geometry() {
        let _session = crate::kernel::VerificationSession::enter();
        let identity = Variable(989_810);
        let pointer = CPointerValue::new(Pointer::symbolic(identity), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(identity));
        let length = Bitvector32Term::Variable(Variable(989_811));
        let count = crate::kernel::eval::pointer_domains::native_count_observation(
            MachineIntegerType::UInt64,
            length.clone(),
        )
        .unwrap();
        let state = CState::new()
            .with_memory(
                CMemory::new()
                    .with_native_slice_input(pointer.clone(), CType::Int32, count.into())
                    .unwrap(),
            )
            .with_local("p", CValue::Pointer(pointer.clone()));
        let empty = PureFactContext::new();
        let spec = span(c_variable("p"), 1);
        let assumed =
            assume_native_span_specs(&state, std::slice::from_ref(&spec), &empty).unwrap();
        assert_eq!(
            assumed, state,
            "entry preserves the exact slice row and its length"
        );
        assert!(assumed.memory().native_input_is_slice(&pointer));
        assert!(check_native_span_specs(&assumed, std::slice::from_ref(&spec), &empty).is_err());
        let bounded = empty.clone().assume_condition(
            ConditionTerm::uint64_equal(length.clone(), Bitvector32Term::UInt64Constant(1)),
            true,
        );
        assert!(check_native_span_specs(&assumed, std::slice::from_ref(&spec), &bounded).is_ok());
        let too_short = empty.clone().assume_condition(
            ConditionTerm::uint64_equal(length, Bitvector32Term::UInt64Constant(0)),
            true,
        );
        assert!(assume_native_span_specs(&state, std::slice::from_ref(&spec), &too_short).is_err());
        assert!(check_native_span_specs(&state, std::slice::from_ref(&spec), &too_short).is_err());
        let fixed_empty = CState::new()
            .with_memory(
                CMemory::new()
                    .with_native_slice_input(
                        pointer.clone(),
                        CType::Int32,
                        IntegerTerm::constant_i64(0).into(),
                    )
                    .unwrap(),
            )
            .with_local("p", CValue::Pointer(pointer.clone()));
        assert!(
            assume_native_span_specs(&fixed_empty, std::slice::from_ref(&spec), &empty).is_err()
        );
        let incompatible = state.with_local(
            "p",
            CValue::Pointer(pointer.with_type(CType::UInt32Pointer)),
        );
        let wrong_type = spec
            .clone()
            .with_native_span_requirements(vec![CNativeSpanRequirement {
                carrier: c_variable("p"),
                element_type: CType::UInt32,
                count: c_int32_literal(1),
                access_policy: CTypedAccessPolicy::NativeObjectOnly,
            }]);
        assert!(assume_native_span_specs(&incompatible, &[wrong_type], &empty).is_err());

        let local = CMemory::local_pointer("native-slice-dead");
        let dead_pointer = CPointerValue::new(local.clone(), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(989_812)));
        let memory = CMemory::new()
            .with_block(local.block.clone(), 4)
            .with_native_slice_input(
                dead_pointer.clone(),
                CType::Int32,
                IntegerTerm::constant_i64(1).into(),
            )
            .unwrap()
            .without_local_block(&local.block);
        let dead = CState::new()
            .with_memory(memory)
            .with_local("p", CValue::Pointer(dead_pointer));
        assert!(assume_native_span_specs(&dead, &[spec], &empty).is_err());
    }

    #[test]
    fn interface_prefix_checks_each_arm_and_preserves_only_phi_geometry() {
        let _session = crate::kernel::VerificationSession::enter();
        let arm = |name| {
            let address = CMemory::local_pointer(name);
            let memory =
                CMemory::new().with_declared_scalar_block(address.block.clone(), 4, CType::Int32);
            let pointer = memory
                .declared_scalar_pointer(&address, CType::Int32)
                .unwrap();
            (
                CState::new()
                    .with_memory(memory)
                    .with_local("p", CValue::Pointer(pointer.clone())),
                pointer,
            )
        };
        let (left, left_pointer) = arm("prefix-left");
        let (right, _) = arm("prefix-right");
        let identity = Variable(989_699);
        let phi = CPointerValue::new(Pointer::symbolic(identity), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(identity));
        let successor = CState::new()
            .with_local("p", CValue::Pointer(phi.clone()))
            .with_resource_context(ResourceContext::new());
        let context = PureFactContext::new();
        let specs = [span(c_variable("p"), 1)];
        let joined_left =
            project_interface_native_spans(&left, &successor, &specs, &context).unwrap();
        let joined_right =
            project_interface_native_spans(&right, &successor, &specs, &context).unwrap();
        assert_eq!(joined_left, joined_right);
        assert_eq!(joined_left.resources(), successor.resources());
        assert_eq!(
            joined_left.memory().cells.representation_len(),
            successor.memory().cells.representation_len()
        );
        assert!(
            !joined_left
                .memory()
                .has_initialized_bytes_under(phi.pointer(), 4, &context)
        );
        assert!(joined_left.memory().native_input_span(&phi).is_some());
        assert!(
            project_interface_native_spans(
                &left,
                &successor,
                &[span(c_variable("p"), 2)],
                &context
            )
            .is_err()
        );
        let past = left_pointer
            .clone()
            .with_pointer(left_pointer.pointer().offset_by_bytes(4));
        let past_arm = left.clone().with_local("p", CValue::Pointer(past));
        assert!(project_interface_native_spans(&past_arm, &successor, &specs, &context).is_err());
        let legacy = left.with_local(
            "p",
            CValue::typed_pointer(left_pointer.pointer().clone(), CType::Int32Pointer),
        );
        assert!(project_interface_native_spans(&legacy, &successor, &specs, &context).is_err());
    }

    fn span(carrier: CExpression, count: u32) -> CResourceSpec {
        CResourceSpec::owned_memory(CMemorySegment::new(
            carrier.clone(),
            c_int32_literal(0),
            c_int32_literal(count),
        ))
        .with_native_span_requirements(vec![CNativeSpanRequirement {
            access_policy: crate::kernel::CTypedAccessPolicy::NativeObjectOnly,
            carrier,
            element_type: CType::Int32,
            count: c_int32_literal(count),
        }])
    }

    #[test]
    fn native_prefix_admission_retains_opaque_carrier_without_authority_or_extent() {
        let _session = crate::kernel::VerificationSession::enter();
        let identity = Variable(989_600);
        let pointer = CPointerValue::new(Pointer::symbolic(identity), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(identity));
        let state = CState::new().with_local("p", CValue::Pointer(pointer.clone()));
        let spec = span(c_variable("p"), 2);
        let assumed = assume_native_record_specs(
            &state,
            std::slice::from_ref(&spec),
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(assumed.locals.get("p"), state.locals.get("p"));
        assert!(assumed.resources().facts().is_empty());
        assert_eq!(assumed.memory().cells.representation_len(), 0);
        assert!(!assumed.memory().has_initialized_bytes_under(
            pointer.pointer(),
            8,
            &PureFactContext::new()
        ));
        assert!(check_native_record_specs(&assumed, &[spec], &PureFactContext::new()).is_ok());
        assert!(matches!(
            pointer.designation(),
            Some(PointerDesignation::Unresolved(_))
        ));
        let endpoint = pointer.offset_by_bytes(8);
        let formation = crate::kernel::eval::pointer_domains::checked_pointer_formation(
            &assumed,
            &pointer,
            &endpoint,
            4,
            crate::kernel::eval::pointer_domains::PointerDomainView::Typed,
            &PureFactContext::new(),
        )
        .unwrap();
        assert!(
            matches!(formation, crate::kernel::eval::pointer_domains::PointerDomainCheck::Checked(guards)
            if guards.iter().all(|guard| PureFactContext::new().decide(guard) == Some(true)))
        );
        let byte_cast = pointer.clone().with_type(CType::UInt8Pointer);
        assert!(
            crate::kernel::eval::pointer_domains::checked_pointer_access(
                &assumed,
                &byte_cast,
                CType::UInt8,
                1,
                crate::kernel::eval::pointer_domains::PointerDomainView::ObjectRepresentationBytes,
                &PureFactContext::new(),
            )
            .is_err()
        );
        let expression = c_typed_load(c_variable("p"), CType::Int32);
        let paths = evaluate_c_expression_paths(
            &assumed,
            &expression,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert!(paths.iter().all(|path| matches!(
            path.outcome,
            CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource { .. })
        )));
        for (offset, expected) in [(0, true), (4, true), (8, false)] {
            let value = pointer
                .clone()
                .with_pointer(pointer.offset_by_bytes(offset));
            let check = crate::kernel::eval::pointer_domains::checked_pointer_access(
                &assumed,
                &value,
                CType::Int32,
                4,
                crate::kernel::eval::pointer_domains::PointerDomainView::Typed,
                &PureFactContext::new(),
            )
            .unwrap();
            assert!(
                matches!(check, crate::kernel::eval::pointer_domains::PointerDomainCheck::Checked(guards)
                if guards.iter().all(|guard| PureFactContext::new().decide(guard) == Some(true)) == expected)
            );
        }
        let legacy = CState::new().with_local(
            "p",
            CValue::typed_pointer(pointer.pointer().clone(), CType::Int32Pointer),
        );
        let spec = span(c_variable("p"), 2);
        assert!(
            check_native_record_specs(
                &legacy,
                std::slice::from_ref(&spec),
                &PureFactContext::new()
            )
            .is_err()
        );
        assert!(assume_native_record_specs(&legacy, &[spec], &PureFactContext::new()).is_err());
        let empty = span(c_variable("p"), 0);
        let unchanged =
            assume_native_record_specs(&state, &[empty], &PureFactContext::new()).unwrap();
        assert_eq!(unchanged, state);
        assert!(
            crate::kernel::eval::pointer_domains::checked_pointer_formation(
                &unchanged,
                &pointer,
                pointer.pointer(),
                4,
                crate::kernel::eval::pointer_domains::PointerDomainView::Typed,
                &PureFactContext::new(),
            )
            .is_err()
        );
    }

    #[test]
    fn native_prefix_checks_element_type_without_requiring_nonempty_symbolic_count() {
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let spec = span(c_variable("p"), 1);
        for element_type in [CType::Int32, CType::Float32, CType::UInt64] {
            let address = CMemory::local_pointer("typed-prefix-element");
            let memory = CMemory::new().with_declared_scalar_block(
                address.block.clone(),
                element_type.byte_width(),
                element_type,
            );
            let pointer = memory
                .declared_scalar_pointer(&address, element_type)
                .unwrap()
                .with_type(CType::Int32Pointer);
            let state = CState::new()
                .with_memory(memory)
                .with_local("p", CValue::Pointer(pointer.clone()));
            // Width-only span geometry is intentionally insufficient to
            // authenticate a promise of an int32 object through a cast.
            if element_type.byte_width() == 4 {
                assert!(
                    matches!(crate::kernel::eval::pointer_domains::checked_pointer_span(
                &state, &pointer, IntegerTerm::constant_i64(0), IntegerTerm::constant_i64(1),
                4, crate::kernel::eval::pointer_domains::PointerDomainView::Typed, &context,
            ), Ok(crate::kernel::eval::pointer_domains::PointerDomainCheck::Checked(guards))
                if guards.iter().all(|guard| context.decide(guard) == Some(true)))
                );
            }
            assert_eq!(
                check_native_span_specs(&state, std::slice::from_ref(&spec), &context).is_ok(),
                element_type == CType::Int32
            );
            let variable = Bitvector32Term::Variable(Variable(989_621));
            let count = IntegerTerm::from_machine(MachineIntegerType::Int32, variable.clone())
                .unwrap()
                .into();
            let bounded = context
                .clone()
                .assume_condition(
                    ConditionTerm::signed_less_equal(0.into(), variable.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_equal(variable.clone(), 1.into()),
                    true,
                );
            assert_eq!(
                span_holds(
                    &state,
                    &pointer,
                    CType::Int32,
                    &count,
                    CTypedAccessPolicy::NativeObjectOnly,
                    &bounded
                ),
                element_type == CType::Int32
            );
            let empty = bounded.assume_condition(ConditionTerm::equal(variable, 0.into()), true);
            assert!(span_holds(
                &state,
                &pointer,
                CType::Int32,
                &count,
                CTypedAccessPolicy::NativeObjectOnly,
                &empty
            ));
            assert!(state.resources().facts().is_empty());
            assert!(
                !state
                    .memory()
                    .has_initialized_bytes_under(&address, 4, &context)
            );
        }
    }

    #[test]
    fn native_prefix_checks_preserve_complete_array_extent_and_selected_position() {
        let _session = crate::kernel::VerificationSession::enter();
        let address = CMemory::local_pointer("prefix-array");
        let memory = CMemory::new()
            .with_declared_array_block(address.block.clone(), CType::Int32, 4)
            .unwrap();
        let pointer = memory
            .declared_array_pointer(&address, CType::Int32, 4)
            .unwrap();
        let state = CState::new().with_memory(memory).with_local(
            "p",
            CValue::Pointer(pointer.clone().with_pointer(pointer.offset_by_bytes(4))),
        );
        let spec = span(c_variable("p"), 3);
        assert!(
            check_native_record_specs(&state, std::slice::from_ref(&spec), &PureFactContext::new())
                .is_ok()
        );
        let assumed = assume_native_record_specs(&state, &[spec], &PureFactContext::new()).unwrap();
        assert_eq!(assumed, state);
        let too_long = span(c_variable("p"), 4);
        assert!(
            check_native_record_specs(
                &state,
                std::slice::from_ref(&too_long),
                &PureFactContext::new()
            )
            .is_err()
        );
        assert!(assume_native_record_specs(&state, &[too_long], &PureFactContext::new()).is_err());
        let mut wrong_type = span(c_variable("p"), 1);
        wrong_type = wrong_type.with_native_span_requirements(vec![CNativeSpanRequirement {
            access_policy: crate::kernel::CTypedAccessPolicy::NativeObjectOnly,
            carrier: c_variable("p"),
            element_type: CType::Int64,
            count: c_int32_literal(1),
        }]);
        assert!(check_native_record_specs(&state, &[wrong_type], &PureFactContext::new()).is_err());
    }

    #[test]
    fn c_typed_input_guarantee_cannot_be_reused_as_native_object_evidence() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = CPointerValue::new(Pointer::symbolic(Variable(989_780)), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(989_781)));
        let state = CState::new().with_local("p", CValue::Pointer(pointer));
        let native = span(c_variable("p"), 1);
        let c_place = native
            .clone()
            .with_native_span_requirements(vec![CNativeSpanRequirement {
                carrier: c_variable("p"),
                element_type: CType::Int32,
                count: c_int32_literal(1),
                access_policy: CTypedAccessPolicy::CAllocatedAccessAllowed,
            }]);
        let context = PureFactContext::new();
        let assumed =
            assume_native_span_specs(&state, std::slice::from_ref(&c_place), &context).unwrap();
        assert!(
            check_native_span_specs(&assumed, std::slice::from_ref(&c_place), &context).is_ok()
        );
        assert!(
            check_native_span_specs(&assumed, std::slice::from_ref(&native), &context).is_err()
        );
        assert!(
            assume_native_span_specs(&assumed, std::slice::from_ref(&native), &context).is_err()
        );
        assert_eq!(assumed.resources(), state.resources());
        let native_entry = assume_native_span_specs(&state, &[native], &context).unwrap();
        assert!(check_native_span_specs(&native_entry, &[c_place], &context).is_ok());
    }

    #[test]
    fn native_loaded_prefix_requires_full_initialized_pointer_cell_read() {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = CMemory::local_pointer("prefix-pointer-cell");
        let memory =
            CMemory::new().with_declared_scalar_block(slot.block.clone(), 8, CType::Int32Pointer);
        let storage = memory
            .declared_scalar_pointer(&slot, CType::Int32Pointer)
            .unwrap();
        let carrier = c_typed_load(
            CExpression::Value(CValue::Pointer(storage)),
            CType::Int32Pointer,
        );
        let spec = span(carrier, 1);
        let resources = |bytes| {
            ResourceContext::new().unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(slot.clone(), 0.into(), 1.into(), bytes),
            ))
        };
        let raw = CState::new()
            .with_memory(memory.clone().with_uninitialized_object(slot.clone(), 8))
            .with_resource_context(resources(8));
        assert!(
            assume_native_record_specs(&raw, std::slice::from_ref(&spec), &PureFactContext::new())
                .is_err()
        );
        let initialized = memory.with_initialized_object(&slot, 8);
        let short = CState::new()
            .with_memory(initialized.clone())
            .with_resource_context(resources(4));
        assert!(
            assume_native_record_specs(
                &short,
                std::slice::from_ref(&spec),
                &PureFactContext::new()
            )
            .is_err()
        );
        let readable = CState::new()
            .with_memory(initialized)
            .with_resource_context(resources(8));
        let assumed = assume_native_record_specs(
            &readable,
            std::slice::from_ref(&spec),
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(assumed.resources(), readable.resources());
        assert_eq!(
            assumed.memory().cells.representation_len(),
            readable.memory().cells.representation_len()
        );
        assert!(check_native_record_specs(&assumed, &[spec], &PureFactContext::new()).is_ok());
    }
}
