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

fn component(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
) -> Result<(CValue, PureFactContext), String> {
    // A carrier expression may read a pointer field. Such a read still needs
    // its existing byte permission and loadability, including its full pair.
    let executable = assumptions.clone().require_owned_expression_loads();
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
) -> Result<(CPointerValue, SharedIntegerTerm, PureFactContext), String> {
    let (carrier, context) = component(state, &requirement.carrier, assumptions)?;
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
    let (count, context) = component(state, &requirement.count, &context)?;
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

fn span_holds(
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
    let check_span = match access_policy {
        CTypedAccessPolicy::NativeObjectOnly => {
            crate::kernel::eval::pointer_domains::checked_typed_pointer_span
        }
        CTypedAccessPolicy::CAllocatedAccessAllowed => {
            crate::kernel::eval::pointer_domains::checked_c_typed_pointer_span
        }
    };
    let check = check_span(
        state,
        pointer,
        IntegerTerm::constant_i64(0),
        count.as_ref().clone(),
        element_type,
        assumptions,
    );
    matches!(check, Ok(crate::kernel::eval::pointer_domains::PointerDomainCheck::Checked(guards))
        if guards.iter().all(|guard| assumptions.decide(guard) == Some(true)))
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
            let (pointer, count, context) = requirement_values(state, requirement, assumptions)?;
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
    }
    Ok(())
}

pub(super) fn assume_native_span_specs(
    state: &CState,
    specs: &[CResourceSpec],
    assumptions: &PureFactContext,
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
            let (pointer, count, context) = requirement_values(&next, requirement, assumptions)?;
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
            // Definite declared/carried geometry remains decisive. An input
            // assumption cannot widen an existing complete object domain.
            if matches!(
                pointer.designation(),
                Some(PointerDesignation::Object { .. })
            ) || crate::kernel::memory_provenance::resolve_loaded_pointer_carrier(
                &pointer, &context,
            )
            .is_some_and(|resolved| {
                matches!(
                    resolved.designation(),
                    Some(PointerDesignation::Object { .. })
                )
            }) {
                return Err("native prefix contradicts its retained complete carrier".into());
            }
            next.set_memory(next.memory().clone().with_typed_input_span(
                pointer,
                requirement.element_type,
                count,
                requirement.access_policy,
            )?);
        }
    }
    Ok(next)
}

#[cfg(test)]
mod tests {
    use super::*;

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
        let assumed =
            assume_native_record_specs(&state, &[spec.clone()], &PureFactContext::new()).unwrap();
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
            check_native_record_specs(&legacy, &[spec.clone()], &PureFactContext::new()).is_err()
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
                check_native_span_specs(&state, &[spec.clone()], &context).is_ok(),
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
            check_native_record_specs(&state, &[spec.clone()], &PureFactContext::new()).is_ok()
        );
        let assumed = assume_native_record_specs(&state, &[spec], &PureFactContext::new()).unwrap();
        assert_eq!(assumed, state);
        let too_long = span(c_variable("p"), 4);
        assert!(
            check_native_record_specs(&state, &[too_long.clone()], &PureFactContext::new())
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
        let assumed = assume_native_span_specs(&state, &[c_place.clone()], &context).unwrap();
        assert!(check_native_span_specs(&assumed, &[c_place.clone()], &context).is_ok());
        assert!(check_native_span_specs(&assumed, &[native.clone()], &context).is_err());
        assert!(assume_native_span_specs(&assumed, &[native.clone()], &context).is_err());
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
            assume_native_record_specs(&raw, &[spec.clone()], &PureFactContext::new()).is_err()
        );
        let initialized = memory.with_initialized_object(&slot, 8);
        let short = CState::new()
            .with_memory(initialized.clone())
            .with_resource_context(resources(4));
        assert!(
            assume_native_record_specs(&short, &[spec.clone()], &PureFactContext::new()).is_err()
        );
        let readable = CState::new()
            .with_memory(initialized)
            .with_resource_context(resources(8));
        let assumed =
            assume_native_record_specs(&readable, &[spec.clone()], &PureFactContext::new())
                .unwrap();
        assert_eq!(assumed.resources(), readable.resources());
        assert_eq!(
            assumed.memory().cells.representation_len(),
            readable.memory().cells.representation_len()
        );
        assert!(check_native_record_specs(&assumed, &[spec], &PureFactContext::new()).is_ok());
    }
}
