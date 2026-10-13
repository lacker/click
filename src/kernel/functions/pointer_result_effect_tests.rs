use super::*;

fn designated(variable: u64) -> CValue {
    CValue::Pointer(
        CPointerValue::new(Pointer::symbolic(Variable(variable)), CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(variable))),
    )
}

fn certified_identity(argument: CValue) -> CVerifiedFunctionRule {
    let function = c_function(
        CType::Int32Pointer,
        "pointer_identity",
        vec![
            c_parameter("p", CType::Int32Pointer).with_native_pointer_input(
                matches!(&argument, CValue::Pointer(p) if p.designation().is_some()),
            ),
        ],
        c_return(c_variable("p")),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    certify(function, vec![CExpression::Value(argument)])
}

fn certify(function: CFunction, arguments: Vec<CExpression>) -> CVerifiedFunctionRule {
    certify_in_state(CState::new(), function, arguments)
}

fn certify_in_state(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
) -> CVerifiedFunctionRule {
    let artifact = prove_checked_c_function_execution_with_environment(
        state.clone(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let execution = prove_c_function_contract_execution_paths_with_checked_artifacts(
        state,
        function.clone(),
        arguments,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
        &[artifact],
    );
    let claims = c_verified_function_contract_claims(&function, &execution).unwrap_or_else(|| {
        panic!(
            "body contract certification refused: {:?}",
            c_unverified_function_contract_claims(&function, &execution)
        )
    });
    c_verified_function_rule(function.clone(), &claims).unwrap_or_else(|| {
        panic!(
            "rule packaging refused; missing/failed claims: {:?}; direct interface supported: {}",
            c_unverified_function_contract_claims(&function, &execution),
            function.verified_direct_contract_supported()
        )
    })
}

#[test]
fn pointer_result_effect_is_inferred_from_checked_body_and_instantiated_modularly() {
    let rule = certified_identity(designated(9_898_001));
    assert!(
        rule.pointer_result_effects
            .contains(&CPointerResultEffect::FromParameter {
                parameter: 0,
                child_path: Default::default()
            })
    );
    let argument = designated(9_898_002);
    let environment = CExecutionEnvironment::new().with_verified_function_rule(rule.clone());
    let paths = execute_c_function_call_paths(
        &CState::new().with_population_creation_tracking(),
        &rule.function,
        &[CExpression::Value(argument.clone())],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("modular identity call");
    let [path] = paths.as_slice() else {
        panic!("one modular outcome expected")
    };
    let CFunctionOutcome::Return {
        value: CValue::Pointer(result),
        ..
    } = &path.outcome
    else {
        panic!("unexpected summary outcome: {:?}", path.outcome);
    };
    let CValue::Pointer(input) = argument else {
        unreachable!()
    };
    assert_eq!(result.designation(), input.designation());
    assert_eq!(
        result.pointer(),
        input.pointer(),
        "a certified identity returns the complete actual carrier"
    );
}

#[test]
fn absent_designation_does_not_certify_a_pointer_result_effect() {
    let rule = certified_identity(CValue::typed_pointer(
        Pointer::symbolic(Variable(9_898_003)),
        CType::Int32Pointer,
    ));
    assert!(rule.pointer_result_effects.is_empty());
}

#[test]
fn result_effect_does_not_upgrade_an_actual_undesignated_argument() {
    let effect = CPointerResultEffect::FromParameter {
        parameter: 0,
        child_path: Default::default(),
    };
    let result = CValue::typed_pointer(Pointer::symbolic(Variable(9_898_004)), CType::Int32Pointer);
    let input = CValue::typed_pointer(Pointer::symbolic(Variable(9_898_005)), CType::Int32Pointer);
    assert_eq!(
        instantiate_pointer_result_effect(result.clone(), &[effect], &[input], &CMemory::new()),
        result
    );
}

#[test]
fn uncertified_pointer_result_preserves_integer_origin_boundary() {
    let result_variable = Variable(9_898_042);
    let result = CValue::typed_pointer(Pointer::symbolic(result_variable), CType::Int32Pointer);
    for has_designation in [false, true] {
        let origin =
            CPointerValue::new(Pointer::symbolic(Variable(9_898_043)), CType::Int32Pointer);
        let origin = if has_designation {
            origin.with_designation(PointerDesignation::Unresolved(Variable(9_898_044)))
        } else {
            origin
        };
        let argument = CValue::PointerInteger(Arc::new(
            CPointerIntegerValue::from_pointer(origin, CType::UInt64).unwrap(),
        ));
        let observed =
            instantiate_pointer_result_effect(result.clone(), &[], &[argument], &CMemory::new());
        let CValue::Pointer(pointer) = observed else {
            unreachable!()
        };
        assert_eq!(pointer.pointer(), &Pointer::symbolic(result_variable));
        if has_designation {
            assert_eq!(
                pointer.designation(),
                Some(&PointerDesignation::Unresolved(result_variable))
            );
        } else {
            assert!(pointer.designation().is_none());
        }
    }
}

#[test]
fn disagreeing_normal_return_domains_do_not_infer_an_effect() {
    let function = c_function(
        CType::Int32Pointer,
        "pointer_choice",
        vec![
            c_parameter("flag", CType::Bool),
            c_parameter("p", CType::Int32Pointer),
            c_parameter("q", CType::Int32Pointer),
        ],
        c_if(
            c_variable("flag"),
            c_return(c_variable("p")),
            c_return(c_variable("q")),
        ),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let rule = certify(
        function,
        vec![
            CExpression::Value(bool_value(Bitvector32Term::Variable(Variable(9_898_006)))),
            CExpression::Value(designated(9_898_007)),
            CExpression::Value(designated(9_898_008)),
        ],
    );
    assert_eq!(
        rule.pointer_result_effects.as_ref(),
        &[CPointerResultEffect::Opaque]
    );
}

#[test]
fn raw_address_equality_does_not_select_a_different_designation() {
    let address = Pointer::symbolic(Variable(9_898_009));
    let input = CPointerValue::new(address.clone(), CType::Int32Pointer)
        .with_designation(PointerDesignation::Unresolved(Variable(9_898_010)));
    let result = CValue::Pointer(
        CPointerValue::new(address, CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(Variable(9_898_011))),
    );
    let preserved = instantiate_pointer_result_effect(
        result,
        &[CPointerResultEffect::FromParameter {
            parameter: 0,
            child_path: Default::default(),
        }],
        &[CValue::Pointer(input.clone())],
        &CMemory::new(),
    );
    let CValue::Pointer(preserved) = preserved else {
        unreachable!()
    };
    assert_eq!(preserved.designation(), input.designation());
    let no_effect = instantiate_pointer_result_effect(
        CValue::typed_pointer(input.pointer().clone(), CType::Int32Pointer),
        &[],
        &[CValue::Pointer(input)],
        &CMemory::new(),
    );
    let CValue::Pointer(no_effect) = no_effect else {
        unreachable!()
    };
    assert!(
        matches!(no_effect.designation(), Some(PointerDesignation::Unresolved(variable))
        if *variable == Variable(9_898_009))
    );
}

#[test]
fn concrete_condition_cannot_specialize_a_pointer_result_effect() {
    let function = c_function(
        CType::Int32Pointer,
        "specialized_choice",
        vec![
            c_parameter("flag", CType::Bool),
            c_parameter("p", CType::Int32Pointer),
            c_parameter("q", CType::Int32Pointer),
        ],
        c_if(
            c_variable("flag"),
            c_return(c_variable("p")),
            c_return(c_variable("q")),
        ),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let rule = certify(
        function,
        vec![
            CExpression::Value(bool_value(Bitvector32Term::Constant(1))),
            CExpression::Value(designated(9_898_012)),
            CExpression::Value(designated(9_898_013)),
        ],
    );
    assert!(
        rule.pointer_result_effects
            .iter()
            .all(|effect| matches!(effect, CPointerResultEffect::Opaque))
    );
}

#[test]
fn equal_parameter_addresses_with_different_domains_cannot_certify_preservation() {
    let address = Pointer::symbolic(Variable(9_898_014));
    let input = |domain| {
        CExpression::Value(CValue::Pointer(
            CPointerValue::new(address.clone(), CType::Int32Pointer)
                .with_designation(PointerDesignation::Unresolved(Variable(domain))),
        ))
    };
    let function = c_function(
        CType::Int32Pointer,
        "aliased_entry",
        vec![
            c_parameter("p", CType::Int32Pointer),
            c_parameter("q", CType::Int32Pointer),
        ],
        c_return(c_variable("q")),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let rule = certify(function, vec![input(9_898_014), input(9_898_015)]);
    assert!(
        rule.pointer_result_effects
            .iter()
            .all(|effect| matches!(effect, CPointerResultEffect::Opaque))
    );
}

#[test]
fn aliased_parameter_domains_do_not_certify_a_universal_effect() {
    let input = designated(9_898_016);
    let function = c_function(
        CType::Int32Pointer,
        "aliased_domain_entry",
        vec![
            c_parameter("p", CType::Int32Pointer),
            c_parameter("q", CType::Int32Pointer),
        ],
        c_return(c_variable("q")),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let rule = certify(
        function,
        vec![CExpression::Value(input.clone()), CExpression::Value(input)],
    );
    assert!(
        rule.pointer_result_effects
            .iter()
            .all(|effect| matches!(effect, CPointerResultEffect::Opaque))
    );
}

#[test]
fn canonical_external_input_binder_certifies_domain_transport() {
    let variable = Variable(9_898_017);
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(variable)),
            byte_width: 4,
        },
    };
    let argument = CValue::Pointer(
        CPointerValue::new(pointer, CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(variable)),
    );
    let rule = certified_identity(argument);
    assert!(
        rule.pointer_result_effects
            .contains(&CPointerResultEffect::FromParameter {
                parameter: 0,
                child_path: Default::default(),
            })
    );
}

#[test]
fn noncanonical_external_input_scale_cannot_certify_transport() {
    let variable = Variable(9_898_018);
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(variable)),
            byte_width: 8,
        },
    };
    let rule = certified_identity(CValue::Pointer(
        CPointerValue::new(pointer, CType::Int32Pointer)
            .with_designation(PointerDesignation::Unresolved(variable)),
    ));
    assert!(
        rule.pointer_result_effects
            .iter()
            .all(|effect| matches!(effect, CPointerResultEffect::Opaque))
    );
}

#[test]
fn no_argument_global_pointer_result_remains_opaque_modularly() {
    // Kernel global installation deliberately retains legacy storage. Seed a
    // native declaration witness and use its authenticated carrier directly.
    let address = CMemory::global_pointer("value");
    let memory = CMemory::new().with_declared_scalar_block(address.block.clone(), 4, CType::Int32);
    let global = memory
        .declared_scalar_pointer(&address, CType::Int32)
        .unwrap();
    let function = c_function(
        CType::Int32Pointer,
        "global_address",
        vec![],
        c_return(CExpression::Value(CValue::Pointer(global))),
    )
    .with_global_variables(vec![CGlobal::new("value", CType::Int32, int32(7))])
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let rule = certify_in_state(CState::new().with_memory(memory), function, vec![]);
    assert_eq!(
        rule.pointer_result_effects.as_ref(),
        &[CPointerResultEffect::Opaque]
    );
    let environment = CExecutionEnvironment::new().with_verified_function_rule(rule.clone());
    let paths = execute_c_function_call_paths(
        &CState::new().with_population_creation_tracking(),
        &rule.function,
        &[],
        &PureFactContext::new(),
        CExecutionContext::apply_verified_rules(&environment),
        &mut ExecutionBudget::new(),
    )
    .expect("opaque global result call");
    let [path] = paths.as_slice() else {
        panic!("one call outcome expected")
    };
    let CFunctionOutcome::Return {
        value: CValue::Pointer(result),
        ..
    } = &path.outcome
    else {
        panic!("unexpected call outcome: {:?}", path.outcome);
    };
    assert!(matches!(
        result.designation(),
        Some(PointerDesignation::Unresolved(_))
    ));
}

#[test]
fn ordinary_ensure_claim_retains_independently_checked_body_pointer_effect() {
    let function = c_function(
        CType::Int32Pointer,
        "ensured_identity",
        vec![c_parameter("p", CType::Int32Pointer).with_native_pointer_input(true)],
        c_return(c_variable("p")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable(C_CONTRACT_RESULT_NAME)),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("p")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let arguments = vec![CExpression::Value(designated(9_898_031))];
    let artifact = prove_checked_c_function_execution_with_environment(
        CState::new(),
        function.clone(),
        arguments.clone(),
        PureFactContext::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let execution = prove_c_function_contract_execution_paths_with_checked_artifacts(
        CState::new(),
        function.clone(),
        arguments,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
        &[artifact],
    );
    let claims = c_verified_function_contract_claims(&function, &execution).unwrap();
    assert_eq!(claims.len(), 1);
    assert_eq!(claims[0].key(), &CFunctionContractClaimKey::Ensure(0));
    let rule = c_verified_function_rule(function.clone(), &claims).unwrap();
    assert!(
        rule.pointer_result_effects
            .contains(&CPointerResultEffect::FromParameter {
                parameter: 0,
                child_path: Default::default(),
            })
    );

    let mut incomplete = execution.clone();
    incomplete.cases.clear();
    assert!(c_verified_function_contract_claims(&function, &incomplete).is_none());
    let mut unprepared = execution;
    unprepared.cases[0][0].paths[0].theorem = Theorem::new(Proposition::ConditionIs(
        ConditionTerm::Constant(true),
        true,
    ));
    assert!(c_verified_function_contract_claims(&function, &unprepared).is_none());
}

#[test]
fn complete_body_certifies_a_full_pointer_member_store() {
    let layout = Arc::new(CAggregateLayout::new(
        C_POINTER_BYTE_WIDTH,
        C_POINTER_BYTE_WIDTH,
        vec![CAggregateField::new("kid", 0, CType::Int32Pointer)],
    ));
    let target = CExpression::MemberAddress {
        object: Box::new(c_variable("p")),
        selection: Arc::new(CAggregateMemberSelection {
            layout: layout.clone(),
            path: vec!["kid".to_string()].into(),
            value_type: CType::Int32Pointer,
        }),
    };
    let storage = CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable("p"),
        c_int32_literal(0),
        c_int32_literal(C_POINTER_BYTE_WIDTH / 4),
    ));
    let function = c_function(
        CType::Void,
        "put_semantic_pointer",
        vec![
            c_parameter("p", CType::Int32Pointer),
            c_parameter("kid", CType::Int32Pointer).with_native_pointer_input(true),
        ],
        c_seq(
            c_typed_store(target, c_variable("kid"), CType::Int32Pointer),
            c_return(c_void_value()),
        ),
    )
    .with_aggregate_object_inputs(vec![CAggregateObjectInput {
        parameter_index: 0,
        layout: layout.clone(),
    }])
    .with_resource_summary(vec![storage.clone()], vec![storage])
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_resource(0, 0),
        ],
        true,
    );
    let entry = independent_entry::construct(
        &function,
        &[
            CExpression::Value(CValue::typed_pointer(
                Pointer::symbolic(Variable(9_898_201)),
                CType::Int32Pointer,
            )),
            CExpression::Value(designated(9_898_202)),
        ],
        None,
        false,
    )
    .expect("independent input recipe");
    let rule = certify_in_state(entry.caller, function, entry.arguments);
    assert!(rule.pointer_store_effects.contains(&CPointerStoreEffect {
        destination: CPointerEffectRoot::Parameter(0),
        destination_path: vec!["kid".into()].into(),
        value_type: CType::Int32Pointer,
        source: CPointerEffectRoot::Parameter(1),
        source_path: Default::default(),
        source_field: None,
    }));
}

#[test]
fn specialized_entry_pointer_cell_cannot_certify_parameter_transport() {
    for self_store in [false, true] {
        let layout = Arc::new(CAggregateLayout::new(
            C_POINTER_BYTE_WIDTH,
            C_POINTER_BYTE_WIDTH,
            vec![CAggregateField::new("kid", 0, CType::Int32Pointer)],
        ));
        let address = Pointer::symbolic(Variable(9_898_211));
        let source = designated(9_898_212);
        let memory = CMemory::new()
            .with_declared_aggregate_block(address.block.clone(), &layout)
            .store(address.clone(), source.clone());
        let destination = memory
            .declared_aggregate_pointer(&address, &layout)
            .unwrap()
            .with_type(CType::Int32Pointer);
        let field = CExpression::MemberAddress {
            object: Box::new(c_variable("p")),
            selection: Arc::new(CAggregateMemberSelection {
                layout: layout.clone(),
                path: vec!["kid".to_string()].into(),
                value_type: CType::Int32Pointer,
            }),
        };
        let load = c_typed_load(field.clone(), CType::Int32Pointer);
        let body = if self_store {
            c_seq(
                c_typed_store(field, load.clone(), CType::Int32Pointer),
                c_return(load),
            )
        } else {
            c_return(load)
        };
        let storage = CResourceSpec::owned_memory(CMemorySegment::new(
            c_variable("p"),
            c_int32_literal(0),
            c_int32_literal(C_POINTER_BYTE_WIDTH / 4),
        ));
        let function = c_function(
            CType::Int32Pointer,
            "read_specialized_cell",
            vec![
                c_parameter("p", CType::Int32Pointer),
                c_parameter("q", CType::Int32Pointer),
            ],
            body,
        )
        .with_aggregate_object_inputs(vec![CAggregateObjectInput {
            parameter_index: 0,
            layout,
        }])
        .with_resource_summary(vec![storage.clone()], vec![storage])
        .with_contract(
            Vec::new(),
            Vec::new(),
            Vec::new(),
            vec![
                CFunctionContractClaim::body_safety(),
                CFunctionContractClaim::ensure_resource(0, 0),
            ],
            true,
        );
        let state = CState::new().with_memory(memory).with_resource_context(
            ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(
                    address,
                    0u32.into(),
                    (C_POINTER_BYTE_WIDTH / 4).into(),
                    4,
                ),
            )),
        );
        let rule = certify_in_state(
            state,
            function,
            vec![
                CExpression::Value(CValue::Pointer(destination)),
                CExpression::Value(source),
            ],
        );
        assert!(
            !rule.pointer_result_effects.iter().any(|effect| matches!(
                effect,
                CPointerResultEffect::FromParameter { parameter: 1, .. }
            )),
            "caller-specific entry cell is not a universal parameter relationship"
        );
        assert!(
            rule.pointer_store_effects.is_empty(),
            "self-store cannot authenticate the caller-specific source relation"
        );
    }
}

#[test]
fn extra_entry_premise_cannot_authorize_a_universal_pointer_effect() {
    let argument = designated(9_898_221);
    let rule = certified_identity(argument.clone());
    assert!(
        rule.pointer_result_effects
            .contains(&CPointerResultEffect::FromParameter {
                parameter: 0,
                child_path: Default::default(),
            })
    );
    let arguments = vec![CExpression::Value(argument)];
    let state = CState::new();
    let canonical = crate::kernel::c_function_contract_entry(&state, &rule.function, &arguments)
        .expect("canonical contract entry")
        .into_assumptions();
    assert!(independent_entry::matches(
        &rule.function,
        &arguments,
        &state,
        &canonical,
        None,
    ));
    let specialized = canonical.assume_proposition(Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(Bitvector32Term::Variable(Variable(9_898_222))),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    ));
    assert!(
        !independent_entry::matches(&rule.function, &arguments, &state, &specialized, None),
        "an additional caller fact is not a universally declared entry premise"
    );
}

#[test]
fn certified_pointer_result_keeps_local_storage_and_result_qualifiers() {
    let address = Pointer {
        block: "local:identity-array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new()
        .with_declared_array_block(address.block.clone(), CType::Int32, 3)
        .expect("actual scalar array declaration");
    let input = memory
        .declared_array_pointer(&address, CType::Int32, 3)
        .expect("actual declaration authenticates the complete array");
    let result = CPointerValue::new(Pointer::symbolic(Variable(9_898_020)), CType::Int32Pointer)
        .with_pointee_constant(true);
    let value = instantiate_pointer_result_effect(
        CValue::Pointer(result.clone()),
        &[
            CPointerResultEffect::FromParameter {
                parameter: 0,
                child_path: Default::default(),
            },
            CPointerResultEffect::ExactFromParameter {
                parameter: 0,
                child_path: Default::default(),
            },
        ],
        &[CValue::Pointer(input.clone())],
        &memory,
    );
    assert_eq!(
        value,
        CValue::Pointer(input.with_type(result.c_type()).with_pointee_constant(true))
    );
    let opaque = instantiate_pointer_result_effect(
        CValue::Pointer(result.clone()),
        &[CPointerResultEffect::Opaque],
        &[value],
        &memory,
    );
    let CValue::Pointer(opaque) = opaque else {
        unreachable!()
    };
    assert_eq!(opaque.pointer(), result.pointer());
    assert!(matches!(
        opaque.designation(),
        Some(PointerDesignation::Unresolved(_))
    ));
}

#[test]
fn displaced_return_keeps_domain_effect_without_certifying_exact_parameter_address() {
    let span = CResourceSpec::viewed_memory(CMemorySegment::new(
        c_variable("p"),
        c_int32_literal(0),
        c_int32_literal(3),
    ))
    .with_native_span_requirements(vec![CNativeSpanRequirement {
        carrier: c_variable("p"),
        element_type: CType::Int32,
        count: c_int32_literal(3),
        access_policy: CTypedAccessPolicy::NativeObjectOnly,
    }]);
    let function = c_function(
        CType::Int32Pointer,
        "displaced_result",
        vec![c_parameter("p", CType::Int32Pointer).with_native_pointer_input(true)],
        c_return(c_add(c_variable("p"), c_int32_literal(1))),
    )
    .with_resource_summary(vec![span], vec![])
    .with_contract(
        vec![],
        vec![],
        vec![],
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let entry = independent_entry::construct(
        &function,
        &[CExpression::Value(designated(9_898_221))],
        None,
        false,
    )
    .expect("independent typed span entry");
    let rule = certify_in_state(entry.caller, function, entry.arguments);
    assert!(
        rule.pointer_result_effects
            .contains(&CPointerResultEffect::FromParameter {
                parameter: 0,
                child_path: Default::default()
            })
    );
    assert!(
        !rule
            .pointer_result_effects
            .iter()
            .any(|effect| matches!(effect, CPointerResultEffect::ExactFromParameter { .. }))
    );
    let input = designated(9_898_222);
    let result = CValue::typed_pointer(Pointer::symbolic(Variable(9_898_223)), CType::Int32Pointer);
    let value = instantiate_pointer_result_effect(
        result.clone(),
        &rule.pointer_result_effects,
        std::slice::from_ref(&input),
        &CMemory::new(),
    );
    let (CValue::Pointer(value), CValue::Pointer(result), CValue::Pointer(input)) =
        (value, result, input)
    else {
        unreachable!()
    };
    assert_eq!(value.pointer(), result.pointer());
    assert_eq!(value.designation(), input.designation());
}

#[test]
fn private_by_value_pointer_store_is_not_exported_to_the_argument_image() {
    let _session = crate::kernel::VerificationSession::enter();
    let layout = Arc::new(CAggregateLayout::new(
        8,
        8,
        vec![CAggregateField::new("kid", 0, CType::Int32Pointer)],
    ));
    let field = CExpression::MemberAddress {
        object: Box::new(c_variable("copy")),
        selection: Arc::new(CAggregateMemberSelection {
            layout: layout.clone(),
            path: vec!["kid".into()].into(),
            value_type: CType::Int32Pointer,
        }),
    };
    let function = c_function(
        CType::Void,
        "retarget_private_copy",
        vec![
            c_parameter_with_aggregate_layout("copy", CType::VoidPointer, layout.as_ref().clone()),
            c_parameter("kid", CType::Int32Pointer).with_native_pointer_input(true),
        ],
        c_seq(
            c_typed_store(field, c_variable("kid"), CType::Int32Pointer),
            c_return(c_void_value()),
        ),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let incoming = vec![
        CExpression::Value(CValue::typed_pointer(
            Pointer::symbolic(Variable(9_898_301)),
            CType::VoidPointer,
        )),
        CExpression::Value(designated(9_898_302)),
    ];
    let staging = constructor_input::materialize_symbolic_declaration_parameters(
        &CState::new(),
        &function,
        &incoming,
    )
    .unwrap();
    let image = staging.locals().aggregate_object_pointer("copy").unwrap();
    let arguments = vec![
        CExpression::Value(CValue::typed_pointer(image.clone(), CType::VoidPointer)),
        incoming[1].clone(),
    ];
    let entry = independent_entry::construct(&function, &arguments, None, false).unwrap();
    let rule = certify_in_state(entry.caller, function, entry.arguments);
    assert!(
        rule.pointer_store_effects.is_empty(),
        "private stores do not modify the caller's value image"
    );
}

#[test]
fn aggregate_contract_views_bind_incoming_images_even_with_a_caller_name_collision() {
    let layout = CAggregateLayout::new(4, 4, vec![CAggregateField::new("value", 0, CType::Int32)]);
    let function = c_function(
        CType::Void,
        "observe_copy",
        vec![c_parameter_with_aggregate_layout(
            "copy",
            CType::VoidPointer,
            layout.clone(),
        )],
        c_return(c_void_value()),
    );
    let image = Pointer::symbolic(Variable(9_898_401));
    let arguments = [CValue::typed_pointer(image.clone(), CType::VoidPointer)];
    for collision in [false, true] {
        let mut caller = CState::new();
        if collision {
            caller.locals.set_aggregate_object_at(
                "copy",
                layout.clone(),
                Pointer::symbolic(Variable(9_898_402)),
            );
        }
        let view = with_contract_interface_argument_views(
            &caller,
            function.contract_interface(),
            &arguments,
        );
        assert_eq!(view.locals().aggregate_object_pointer("copy"), Some(&image));
        assert_eq!(view.resources(), caller.resources());
    }
}
