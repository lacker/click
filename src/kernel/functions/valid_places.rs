//! Typed location validity is independent of resource access and initialization.
//! Entry assumptions authenticate an exact complete carrier. Calls only check
//! those guarantees; numeric address equalities never introduce them.
use super::*;

pub(crate) fn holds(
    memory: &CMemory,
    pointer: &CPointerValue,
    place_type: &CPlaceType,
    access_policy: CTypedAccessPolicy,
    assumptions: &PureFactContext,
) -> bool {
    let state = CState::new()
        .with_memory(memory.clone())
        .with_typed_access_policy(access_policy);
    match place_type {
        CPlaceType::Record(layout) => {
            let requirement = CNativeRecordPlaceRequirement {
                carrier: CExpression::Value(CValue::Pointer(pointer.clone())),
                layout: layout.clone(),
                prefix_count: None,
            };
            native_record_inputs::check_record_place(&state, &requirement, assumptions).is_ok()
        }
        CPlaceType::Scalar(element_type) => native_span_inputs::span_holds(
            &state,
            pointer,
            *element_type,
            &IntegerTerm::constant_i64(1).into(),
            access_policy,
            assumptions,
        ),
    }
}

pub(super) fn has_entry_requirements(specs: &[SpecProposition]) -> bool {
    let mut pending = specs.iter().collect::<Vec<_>>();
    while let Some(spec) = pending.pop() {
        match spec {
            SpecProposition::ValidPlace {
                memory: SpecMemory::Current,
                ..
            } => return true,
            SpecProposition::And(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            _ => {}
        }
    }
    false
}

pub(super) fn assume_entry_requirements(
    state: &CState,
    specs: &[SpecProposition],
    assumptions: &PureFactContext,
) -> Result<CState, String> {
    let mut next = state.clone();
    let mut pending = specs.iter().rev().collect::<Vec<_>>();
    let observer = assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .observe_pointer_addresses();
    let _entry_observation = crate::kernel::eval::SpecificationReadScope::enter();
    let mut budget = ExecutionBudget::beside_live_state();
    while let Some(spec) = pending.pop() {
        match spec {
            SpecProposition::And(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            SpecProposition::ValidPlace {
                memory: SpecMemory::Current,
                pointer: expression,
                place_type,
                access_policy,
            } => {
                let paths = crate::kernel::spec::evaluate_spec_expression_paths_with_loop_entry(
                    &next,
                    expression,
                    Some(&next),
                    &observer,
                    &mut budget,
                )
                .map_err(|_| "valid_place entry evaluation exceeded its budget")?;
                let [path] = paths.as_slice() else {
                    return Err("valid_place requires one defined entry carrier".into());
                };
                let CValue::Pointer(pointer) = &path.value else {
                    return Err("valid_place requires a defined object pointer".into());
                };
                let context = assumptions_with_path_context(&observer, &path.facts, &[]);
                if path.obligations.iter().any(|goal| {
                    !required_obligation_is_exactly_discharged(&context, goal.proposition())
                }) {
                    return Err("valid_place entry carrier has an unproved condition".into());
                }
                match place_type {
                    CPlaceType::Record(layout) => next.set_memory(
                        next.memory()
                            .clone()
                            .with_native_record_input(pointer.clone(), layout.clone())?,
                    ),
                    CPlaceType::Scalar(element_type) => {
                        let requirement = CNativeSpanRequirement {
                            carrier: CExpression::Value(CValue::Pointer(pointer.clone())),
                            count: c_int32_literal(1),
                            element_type: *element_type,
                            access_policy: *access_policy,
                        };
                        next = native_span_inputs::assume_native_span_requirements_in(
                            &next,
                            &[requirement],
                            &context,
                            true,
                        )?;
                    }
                }
            }
            // A disjunction, implication or quantified requirement is not an
            // unconditional entry promise. Its written proposition is checked
            // normally, without assuming either arm or instantiating a binder.
            _ => {}
        }
    }
    Ok(next)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn scalar_requirement(pointer: CPointerValue) -> SpecProposition {
        SpecProposition::ValidPlace {
            memory: SpecMemory::Current,
            pointer: SpecExpression::Value(CValue::Pointer(pointer)),
            place_type: CPlaceType::Scalar(CType::Int32),
            access_policy: CTypedAccessPolicy::NativeObjectOnly,
        }
    }

    #[test]
    fn valid_place_entry_assumption_grants_geometry_only() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(992_001);
        let pointer = CPointerValue::new(Pointer::symbolic(variable), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(variable));
        let state = CState::new();
        let context = PureFactContext::new();
        let place_type = CPlaceType::Scalar(CType::Int32);
        assert!(!holds(
            state.memory(),
            &pointer,
            &place_type,
            CTypedAccessPolicy::NativeObjectOnly,
            &context
        ));
        let admitted =
            assume_entry_requirements(&state, &[scalar_requirement(pointer.clone())], &context)
                .unwrap();
        assert!(holds(
            admitted.memory(),
            &pointer,
            &place_type,
            CTypedAccessPolicy::NativeObjectOnly,
            &context
        ));
        assert_eq!(admitted.resources(), state.resources());
        assert!(
            !admitted
                .memory()
                .has_initialized_bytes_under(pointer.pointer(), 4, &context)
        );
        assert_eq!(
            admitted.memory().cells.representation_len(),
            state.memory().cells.representation_len()
        );
        let proposition = Proposition::CValidPlace {
            memory: admitted.memory().clone(),
            pointer: pointer.clone(),
            place_type: place_type.clone(),
            access_policy: CTypedAccessPolicy::NativeObjectOnly,
        };
        assert!(context.proves_atomic_without_search(&proposition));
        assert!(context.proves_atomic_memory_or_resource(&proposition));
        // The same address without the complete promised carrier has no such guarantee.
        let numeric_alias = CPointerValue::new(pointer.pointer().clone(), pointer.c_type());
        assert!(!holds(
            admitted.memory(),
            &numeric_alias,
            &place_type,
            CTypedAccessPolicy::NativeObjectOnly,
            &context
        ));
        assert!(!holds(
            admitted.memory(),
            &pointer,
            &CPlaceType::Scalar(CType::Int64),
            CTypedAccessPolicy::NativeObjectOnly,
            &context
        ));
    }

    #[test]
    fn valid_place_does_not_assume_a_disjunct_or_snapshot() {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = Variable(992_002);
        let pointer = CPointerValue::new(Pointer::symbolic(variable), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(variable));
        let requirement = scalar_requirement(pointer);
        let disjunction =
            SpecProposition::Or(Box::new(requirement.clone()), Box::new(requirement.clone()));
        let state = CState::new();
        assert_eq!(
            assume_entry_requirements(&state, &[disjunction], &PureFactContext::new()).unwrap(),
            state
        );
        let SpecProposition::ValidPlace {
            pointer,
            place_type,
            access_policy,
            ..
        } = requirement
        else {
            unreachable!()
        };
        let old = SpecProposition::ValidPlace {
            memory: SpecMemory::FunctionEntry,
            pointer,
            place_type,
            access_policy,
        };
        assert_eq!(
            assume_entry_requirements(&state, &[old], &PureFactContext::new()).unwrap(),
            state
        );
    }

    #[test]
    fn valid_place_record_checks_lifetime_identity_and_not_padding_initialization() {
        let _session = crate::kernel::VerificationSession::enter();
        let root = CMemory::local_pointer("valid-place-record");
        let layout = Arc::new(CAggregateLayout::new(
            8,
            4,
            vec![CAggregateField::new("value", 0, CType::Int32)],
        ));
        let memory = CMemory::new().with_declared_aggregate_block(root.block.clone(), &layout);
        let pointer = memory.declared_aggregate_pointer(&root, &layout).unwrap();
        let place = CPlaceType::Record(layout.clone());
        let context = PureFactContext::new();
        assert!(holds(
            &memory,
            &pointer,
            &place,
            CTypedAccessPolicy::NativeObjectOnly,
            &context
        ));
        assert!(!memory.has_initialized_bytes_under(&root, 8, &context));
        let native = Arc::new(
            layout
                .as_ref()
                .clone()
                .with_declaration_identity(Some(Arc::new(CppRecordDeclarationIdentity::new(
                    "valid-place-test",
                    "Record",
                )))),
        );
        assert!(!holds(
            &memory,
            &pointer,
            &CPlaceType::Record(native),
            CTypedAccessPolicy::NativeObjectOnly,
            &context
        ));
        let expired = memory.without_local_block(&root.block);
        assert!(!holds(
            &expired,
            &pointer,
            &place,
            CTypedAccessPolicy::NativeObjectOnly,
            &context
        ));
    }
}
