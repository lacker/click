use super::*;

#[test]
fn resource_call_arguments_are_checked_in_kernel_and_fields_are_fresh() {
    let schema = ResourceFieldSchema::new(vec![(
        "revision".into(),
        ResourceFieldType::C(CType::Int32),
    )])
    .unwrap();
    let parameter = |identity| {
        CResourceSpec::instance(
            Variable(identity),
            format!("cell{identity}"),
            schema.clone(),
            CResourceSpec::composite(CResourceAccessMode::Own, "marker".into(), vec![], vec![]),
            CResourceTransferRole::Consume,
            CResourceSnapshot::Current,
        )
        .unwrap()
    };
    let function = c_function(CType::Void, "touch", vec![], CStatement::Skip)
        .with_contract(vec![], vec![], vec![], vec![], true)
        .with_resource_summary(vec![parameter(0)], vec![parameter(0)]);
    let contract = CFunctionContract::new("Touch", function)
        .unwrap()
        .with_proof_parameters(vec![parameter(0)]);
    // Reserve the identifier immediately after the call's memory/result IDs.
    // Post-field generation must skip it, not accidentally preserve the field.
    let before = ResourceInstance::new(
        Variable(10),
        "marker".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::C(symbolic_call_result(
            CType::Int32,
            Variable(1_000_002),
        ))]
        .into(),
    )
    .unwrap();
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(before.clone()))),
    );
    let environment = CExecutionEnvironment::new()
        .with_selected_call_contract("Touch")
        .with_selected_call_resource_arguments(vec![Variable(10)]);
    let run =
        |state: &CState, contract: &CFunctionContract, environment: &CExecutionEnvironment| {
            execute_c_function_contracts_paths(
                state,
                &[contract],
                &[],
                &PureFactContext::new(),
                environment,
                &mut ExecutionBudget::default(),
            )
            .unwrap()
        };
    let paths = run(&state, &contract, &environment);
    let CFunctionOutcome::Return { state: after, .. } = &paths[0].outcome else {
        panic!("call failed: {:?}", paths[0].outcome);
    };
    assert!(after.resource_bindings.is_none());
    let returned = after.owned_resource_instance(Variable(10)).unwrap();
    assert_ne!(returned.fields(), before.fields());
    for (state, contract, environment) in [
        (CState::new(), contract.clone(), environment.clone()),
        (
            state.clone(),
            contract.clone(),
            environment
                .clone()
                .with_selected_call_resource_arguments(vec![]),
        ),
        (
            state.clone(),
            contract
                .clone()
                .with_proof_parameters(vec![parameter(0), parameter(1)]),
            environment
                .clone()
                .with_selected_call_resource_arguments(vec![Variable(10), Variable(10)]),
        ),
        (
            state.clone(),
            contract.clone(),
            environment
                .clone()
                .with_selected_call_resource_arguments(vec![Variable(99)]),
        ),
    ] {
        assert!(matches!(
            run(&state, &contract, &environment)[0].outcome,
            CFunctionOutcome::RuntimeError(_)
        ));
    }
}

#[test]
fn resource_transition_retains_borrow_role_for_owned_entry_fact() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:borrow-role:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    );
    let requirement = CResourceSpec::owned_memory(CMemorySegment::new(
        CExpression::Variable("p".into()),
        CExpression::Value(int32(0)),
        CExpression::Value(int32(1)),
    ))
    .with_role(CResourceTransferRole::Borrow)
    .with_snapshot(CResourceSnapshot::Entry);
    let function = c_function(
        CType::Void,
        "borrow_role",
        vec![c_parameter("p", CType::Int32Pointer)],
        CStatement::Skip,
    )
    .with_contract(vec![], vec![], vec![], vec![], true)
    .with_resource_summary(vec![requirement], vec![]);
    let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(range));
    let state = CState::new()
        .with_local("p", CValue::pointer(pointer.clone()))
        .with_memory(CMemory::new().with_block(pointer.block.clone(), 4))
        .with_resource_context(resources);
    let transfer = prepare_contract_resource_transfer(
        &state,
        &state,
        function.name(),
        function.contract_interface(),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
        false,
    )
    .unwrap()
    .unwrap();
    assert_eq!(transfer.borrowed_inputs.len(), 1);
    assert!(transfer.consumed_inputs.is_empty());
    assert_eq!(
        transfer.borrowed_inputs[0].snapshot,
        CResourceSnapshot::Entry
    );
    assert_eq!(
        transfer.borrowed_inputs[0].role,
        CResourceTransferRole::Borrow
    );
}

#[test]
fn named_contract_application_discards_template_body_and_storage() {
    let body_variable = Variable(987_654);
    let pointer_parameter = c_parameter("p", CType::UInt8Pointer);
    let body_with_load = CStatement::Return(CExpression::Load(Box::new(CExpression::Variable(
        "p".into(),
    ))));
    let body_with_variable = CStatement::Return(CExpression::Value(CValue::Int32(
        Bitvector32Term::Variable(body_variable),
    )));
    let with_body_and_storage = c_function(
        CType::Void,
        "callback_template",
        vec![pointer_parameter.clone()],
        body_with_load,
    )
    .with_string_literals(vec![CStringLiteral::new("literal", b"x\0".to_vec())]);
    let with_different_body = c_function(
        CType::Void,
        "callback_template",
        vec![pointer_parameter],
        body_with_variable,
    );
    let first = CFunctionContract::new("BodyIndependent", with_body_and_storage).unwrap();
    let second = CFunctionContract::new("BodyIndependent", with_different_body).unwrap();

    // The named-contract identity contains only the nominal name and the
    // interface. In particular, body/storage differences cannot become
    // callback identity or callback facts.
    assert_eq!(first, second);
    let environment = CExecutionEnvironment::new().with_function_contract(first.clone());
    let variables = crate::kernel::reasoning::execution_environment_variable_index(&environment);
    assert!(
        !variables.contains(&body_variable),
        "named-contract variable collection must not inspect its discarded body"
    );

    let argument = CExpression::Value(CValue::typed_pointer(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        },
        CType::UInt8Pointer,
    ));
    let run = |contract: &CFunctionContract| {
        execute_c_function_contracts_paths(
            &CState::new(),
            &[contract],
            std::slice::from_ref(&argument),
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
    };
    let first_paths = run(&first);
    let second_paths = run(&second);
    assert_eq!(first_paths, second_paths);
    assert!(matches!(
        first_paths[0].outcome,
        CFunctionOutcome::Return { .. }
    ));
}

#[test]
fn resource_constructors_are_direct_only_and_part_of_identity() {
    let constructor = CResourceSpec::token(
        CResourceAccessMode::Own,
        "constructed_token".into(),
        vec![c_int32_literal(7)],
        vec![CType::Int32],
    );
    let function = c_function(
        CType::Void,
        "construct_token",
        vec![],
        c_return(c_void_value()),
    )
    .with_resource_constructors(vec![constructor]);
    let constructed = CResourceFact::own_token("constructed_token".into(), vec![int32(7)]);
    let state = construct_c_function_resource(
        &CState::new(),
        &function,
        &[],
        &CValue::Void,
        &constructed,
        &PureFactContext::new(),
    )
    .unwrap()
    .unwrap();
    assert!(
        state
            .resources()
            .satisfies_fact(&constructed, &PureFactContext::new())
    );

    // Named callback contracts cannot expose a zero-source transition that
    // their application engine does not perform. Direct outcome construction
    // remains supported, while formation and refinement fail closed.
    assert!(CFunctionContract::new("ConstructCallback", function.clone()).is_none());
    let without_constructor = c_function(
        CType::Void,
        "construct_token",
        vec![],
        c_return(c_void_value()),
    );
    let contract =
        CFunctionContract::new("ConstructCallback", without_constructor.clone()).unwrap();
    assert!(!contract.exactly_matches(&function));
    assert!(
        !crate::kernel::api::proof_evidence_function_refines_same_source(
            &without_constructor,
            &function,
        )
    );
}

fn direct_and_callback_resource_transition(
    function: &CFunction,
    state: &CState,
    contract: &CFunctionContract,
    environment: &CExecutionEnvironment,
) -> (CState, CState) {
    let direct_outcome = CFunctionOutcome::Return {
        value: CValue::Void,
        state: state.clone(),
    };
    let (direct_outcome, direct_obligations) = apply_c_function_contract_resource_transition(
        state,
        function,
        &[],
        direct_outcome,
        &PureFactContext::new(),
    )
    .expect("direct resource transition should check");
    assert!(direct_obligations.is_empty());
    let CFunctionOutcome::Return {
        value: direct_value,
        state: direct_state,
    } = direct_outcome
    else {
        panic!("direct resource transition did not return");
    };
    assert_eq!(direct_value, CValue::Void);

    let paths = execute_c_function_contracts_paths(
        state,
        &[contract],
        &[],
        &PureFactContext::new(),
        environment,
        &mut ExecutionBudget::default(),
    )
    .expect("callback resource transition should check");
    assert_eq!(paths.len(), 1);
    assert!(paths[0].obligations.is_empty());
    let CFunctionOutcome::Return {
        value: callback_value,
        state: callback_state,
    } = &paths[0].outcome
    else {
        panic!("callback resource transition did not return");
    };
    assert_eq!(callback_value, &CValue::Void);
    assert_eq!(direct_state.memory(), callback_state.memory());
    assert_eq!(
        direct_state.counted_populations().collect::<Vec<_>>(),
        callback_state.counted_populations().collect::<Vec<_>>()
    );
    (direct_state, callback_state.clone())
}

#[test]
fn direct_and_named_callback_resource_interfaces_agree_across_families() {
    let memory_pointer = Pointer {
        block: "parity-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory_spec = CResourceSpec::owned_memory(CMemorySegment::new(
        c_pointer_value(memory_pointer.clone()),
        c_int32_literal(0),
        c_int32_literal(1),
    ));
    let memory_function = c_function(CType::Void, "parity_memory", vec![], CStatement::Skip)
        .with_resource_summary(vec![memory_spec.clone()], vec![memory_spec]);
    let memory_state = CState::new()
        .with_memory(CMemory::new().with_block(memory_pointer.block.clone(), 4))
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_memory(CMemoryRange::new(
                memory_pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
        ));
    let memory_contract = CFunctionContract::new("ParityMemory", memory_function.clone()).unwrap();
    let (direct, callback) = direct_and_callback_resource_transition(
        &memory_function,
        &memory_state,
        &memory_contract,
        &CExecutionEnvironment::new(),
    );
    assert_eq!(direct.resources(), callback.resources());

    let token_spec = CResourceSpec::token(
        CResourceAccessMode::Own,
        "parity_token".into(),
        vec![c_int32_literal(7)],
        vec![CType::Int32],
    );
    let token_function = c_function(CType::Void, "parity_token", vec![], CStatement::Skip)
        .with_resource_summary(vec![token_spec.clone()], vec![token_spec]);
    let token_state =
        CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_token("parity_token".into(), vec![int32(7)]),
        ));
    let token_contract = CFunctionContract::new("ParityToken", token_function.clone()).unwrap();
    let (direct, callback) = direct_and_callback_resource_transition(
        &token_function,
        &token_state,
        &token_contract,
        &CExecutionEnvironment::new(),
    );
    assert_eq!(direct.resources(), callback.resources());

    let composite_spec = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "parity_composite".into(),
        vec![c_int32_literal(11)],
        vec![CType::Int32],
    );
    let composite_function = c_function(CType::Void, "parity_composite", vec![], CStatement::Skip)
        .with_resource_summary(vec![composite_spec.clone()], vec![composite_spec])
        .with_composite_resource_definitions(vec![CCompositeResourceDefinition::new(
            "parity_composite",
            vec![c_parameter("value", CType::Int32)],
            None,
            true,
            vec![],
            vec![],
        )]);
    let composite_state =
        CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_composite("parity_composite".into(), vec![int32(11)]),
        ));
    let composite_contract =
        CFunctionContract::new("ParityComposite", composite_function.clone()).unwrap();
    let (direct, callback) = direct_and_callback_resource_transition(
        &composite_function,
        &composite_state,
        &composite_contract,
        &CExecutionEnvironment::new(),
    );
    assert_eq!(direct.resources(), callback.resources());

    let schema =
        ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let identity = Variable(700);
    let instance_resource = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "parity_instance".into(),
        vec![c_int32_literal(13)],
        vec![CType::Int32],
    );
    let instance_spec = CResourceSpec::instance(
        identity,
        "item".into(),
        schema.clone(),
        instance_resource,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    let instance = ResourceInstance::new(
        identity,
        "parity_instance".into(),
        vec![int32(13).into()].into(),
        schema.clone(),
        vec![int32(3).into()].into(),
    )
    .unwrap();
    let instance_function = c_function(CType::Void, "parity_instance", vec![], CStatement::Skip)
        .with_resource_summary(vec![instance_spec.clone()], vec![instance_spec.clone()]);
    let instance_state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance))),
    );
    let instance_contract = CFunctionContract::new("ParityInstance", instance_function.clone())
        .unwrap()
        .with_proof_parameters(vec![instance_spec]);
    let instance_environment = CExecutionEnvironment::new()
        .with_selected_call_contract("ParityInstance")
        .with_selected_call_resource_arguments(vec![identity]);
    let (direct, callback) = direct_and_callback_resource_transition(
        &instance_function,
        &instance_state,
        &instance_contract,
        &instance_environment,
    );
    let direct_instance = direct
        .owned_resource_instance(identity)
        .expect("direct transition must retain instance identity");
    let callback_instance = callback
        .owned_resource_instance(identity)
        .expect("callback transition must retain instance identity");
    assert_eq!(direct_instance.identity(), callback_instance.identity());
    assert_eq!(direct_instance.name(), callback_instance.name());
    assert_eq!(direct_instance.arguments(), callback_instance.arguments());
    assert_eq!(direct_instance.schema(), callback_instance.schema());
    assert_eq!(
        direct_instance.fields().len(),
        callback_instance.fields().len()
    );
}

#[test]
fn executed_refinement_checks_the_exact_call_and_source_premises() {
    check_executed_refinement_shape(CType::Void, false);
}

#[test]
fn executed_refinement_requires_forwarding_the_exact_typed_call_result() {
    for return_type in [CType::Int32, CType::Int64, CType::Int32Pointer] {
        check_executed_refinement_shape(return_type, false);
        check_executed_refinement_shape(return_type, true);
    }
}

fn check_executed_refinement_shape(return_type: CType, alter_result: bool) {
    let template = c_function(
        return_type,
        "interface",
        vec![c_parameter("x", CType::Int32)],
        CStatement::Skip,
    )
    .with_contract(vec![], vec![], vec![], vec![], true);
    let source = CFunctionContract::new("Source", template.clone()).unwrap();
    let target = CFunctionContract::new("Target", template.clone()).unwrap();
    let pointer_type = source.function_pointer_type();
    let premise = SpecProposition::Predicate {
        name: source.predicate_name(),
        arguments: vec![SpecPredicateArgument::Value(SpecExpression::CExpression(
            c_variable("callback"),
        ))],
    };
    let conclusion = Proposition::Predicate {
        name: target.predicate_name(),
        arguments: vec![
            Term::CState(CState::new()),
            Term::CValue(CValue::Pointer(CPointerValue::new(
                Pointer {
                    block: PointerBlock::FunctionSymbolic(Variable(0)),
                    offset: PointerOffsetTerm::Constant(0),
                },
                pointer_type,
            ))),
        ],
    };
    let environment = CExecutionEnvironment::new()
        .with_function_contract(source)
        .with_function_contract(target);
    // Isolate the implication boundary: its input is an already trusted rule.
    // Ordinary execution certification is covered by the mdtests.
    for (callee, argument, sources, extra_premise, valid) in [
        ("callback", c_variable("x"), vec!["Source"], false, true),
        ("other", c_variable("x"), vec!["Source"], false, false),
        ("callback", c_int32_literal(1), vec!["Source"], false, false),
        ("callback", c_variable("x"), vec!["Target"], false, false),
        ("callback", c_variable("x"), vec![], false, false),
        ("callback", c_variable("x"), vec!["Source"], true, false),
    ] {
        let mut requirements = vec![premise.clone()];
        if extra_premise {
            requirements.insert(0, premise.clone());
        }
        let function = c_function(
            return_type,
            "wrapper",
            vec![
                c_parameter("x", CType::Int32),
                c_parameter("callback", pointer_type),
            ],
            if return_type == CType::Void {
                CStatement::Call {
                    function_name: callee.to_string(),
                    arguments: vec![argument],
                }
            } else {
                c_seq(
                    c_call_assign("result", callee, vec![argument]),
                    c_return(if alter_result {
                        c_int32_literal(0)
                    } else {
                        c_variable("result")
                    }),
                )
            },
        )
        .with_contract(requirements, vec![], vec![], vec![], true);
        assert_eq!(
            crate::kernel::prove_executed_contract_refinement(
                &environment,
                &sources,
                "Target",
                conclusion.clone(),
                &CVerifiedFunctionRule { function },
            )
            .is_some(),
            valid && !alter_result
        );
    }
}

#[test]
fn pure_callback_preparation_does_not_enumerate_the_resource_frame() {
    let contract = interface(0);
    for count in [0, 16, 64, 256] {
        let resources = ResourceContext::new().unchecked_with_facts(
            (0..count).map(|index| CResourceFact::own_token(format!("token{index}"), vec![])),
        );
        assert!(resources.storage.materialized.get().is_none());
        let state = CState::new().with_resource_context(resources.clone());
        let transfer = prepare_contract_resource_transfer(
            &state,
            &CState::new(),
            contract.name(),
            contract.interface(),
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
            false,
        )
        .unwrap()
        .unwrap();
        assert!(transfer.callee_resources.is_empty());
        assert!(std::sync::Arc::ptr_eq(
            &resources.storage,
            &transfer.caller_resources_after_requirements.storage
        ));
        assert!(
            resources.storage.materialized.get().is_none(),
            "preparation must not enumerate {count} unrelated resources"
        );
    }
}

#[test]
fn authoritative_memory_projection_scales_with_used_members_not_unrelated_frames() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:projection:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::pointer(pointer.clone()))
        .with_memory(CMemory::new().with_block(pointer.block.clone(), 512));
    let mut samples = Vec::new();
    for used_members in [1usize, 4, 16, 64] {
        let mut memory = state.memory.clone();
        for unrelated in 0..256 {
            memory = memory.with_block(format!("local:projection:frame:{unrelated}"), 4);
        }
        let state = state.clone().with_memory(memory);
        let function = c_function(
            CType::Void,
            format!("project_{used_members}"),
            vec![c_parameter("p", CType::Int32Pointer)],
            CStatement::Skip,
        )
        .with_contract(
            vec![],
            vec![],
            (0..used_members)
                .map(|index| {
                    CMemorySegment::new(
                        c_variable("p"),
                        c_int32_literal(index as u32),
                        c_int32_literal(index as u32 + 1),
                    )
                })
                .collect(),
            vec![],
            true,
        );
        let mut budget = ExecutionBudget::default();
        let (projection, work) = crate::instrumentation::measure_deterministic_work(|| {
            project_contract_memory_effects(
                &state,
                function.contract_interface(),
                None,
                &PureFactContext::new(),
                &mut budget,
            )
        });
        assert_eq!(projection.unwrap().unwrap().ranges.len(), used_members);
        samples.push((used_members, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0).max(1) + 64,
            "memory projection should charge used members, not unrelated frames: {samples:?}"
        );
    }

    // Resource-derived frames use the checked transition as their source of
    // memory authority. A bare resource summary without this marker must not
    // turn an abstract callback into an unconditional memory havoc.
    let resource = CResourceSpec::owned_memory(CMemorySegment::new(
        c_variable("p"),
        c_int32_literal(0),
        c_int32_literal(1),
    ));
    let resource_function = c_function(
        CType::Void,
        "project_resource",
        vec![c_parameter("p", CType::Int32Pointer)],
        CStatement::Skip,
    )
    .with_resource_summary(vec![resource], vec![])
    .with_resource_derived_mutable_frame();
    let checked_resources = [CCheckedResourceFact {
        fact: CResourceFact::own_memory(CMemoryRange::new(
            pointer,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )),
        role: CResourceTransferRole::Consume,
        snapshot: CResourceSnapshot::Entry,
        clause_position: None,
    }];
    let projection = project_contract_memory_effects(
        &state,
        resource_function.contract_interface(),
        Some(&checked_resources),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap()
    .unwrap();
    assert_eq!(projection.ranges.len(), 1);
}

#[test]
fn checked_transition_projection_ignores_unrelated_caller_frame() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:transition:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for used_members in [1usize, 4, 16, 64] {
        let requirements = (0..used_members)
            .map(|index| {
                CResourceSpec::owned_memory(CMemorySegment::new(
                    CExpression::Variable("p".into()),
                    CExpression::Value(int32(index as u32)),
                    CExpression::Value(int32(index as u32 + 1)),
                ))
            })
            .collect::<Vec<_>>();
        let owned = (0..used_members)
            .map(|index| {
                CResourceFact::own_memory(CMemoryRange::new(
                    pointer.clone(),
                    Bitvector32Term::Constant(index as u32),
                    Bitvector32Term::Constant(index as u32 + 1),
                ))
            })
            .chain((0..256).map(|index| {
                CResourceFact::own_token(format!("unrelated_transition_token_{index}"), vec![])
            }))
            .collect::<Vec<_>>();
        let state = CState::new()
            .with_local("p", CValue::pointer(pointer.clone()))
            .with_memory(CMemory::new().with_block(pointer.block.clone(), 512))
            .with_resource_context(ResourceContext::new().unchecked_with_facts(owned));
        let function = c_function(
            CType::Void,
            format!("transition_projection_{used_members}"),
            vec![c_parameter("p", CType::Int32Pointer)],
            CStatement::Skip,
        )
        .with_contract(vec![], vec![], vec![], vec![], true)
        .with_resource_summary(requirements, vec![])
        .with_resource_derived_mutable_frame();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let transfer = prepare_contract_resource_transfer(
                &state,
                &state,
                function.name(),
                function.contract_interface(),
                &PureFactContext::new(),
                &mut ExecutionBudget::default(),
                false,
            )
            .unwrap()
            .unwrap();
            let mut inputs = transfer.borrowed_inputs.clone();
            inputs.extend(transfer.consumed_inputs.clone());
            project_contract_memory_effects(
                &state,
                function.contract_interface(),
                Some(&inputs),
                &PureFactContext::new(),
                &mut ExecutionBudget::default(),
            )
        });
        assert_eq!(result.unwrap().unwrap().ranges.len(), used_members);
        samples.push((used_members, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0).max(1) + 128,
            "checked transition work should charge used members, not unrelated frame: {samples:?}"
        );
    }
}

#[test]
fn checked_wrapper_projection_scales_with_used_members() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:wrapper:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for used_members in [1usize, 4, 16, 64] {
        let contains = (0..used_members)
            .map(|index| {
                CResourceSpec::owned_memory(CMemorySegment::new(
                    CExpression::Variable("data".into()),
                    CExpression::Value(int32(index as u32)),
                    CExpression::Value(int32(index as u32 + 1)),
                ))
            })
            .collect();
        let definition = CCompositeResourceDefinition::new(
            "TransitionWrapper",
            vec![c_parameter("data", CType::Int32Pointer)],
            None,
            false,
            contains,
            vec![],
        );
        let requirement = CResourceSpec::composite(
            CResourceAccessMode::Own,
            "TransitionWrapper".into(),
            vec![CExpression::Variable("p".into())],
            vec![CType::Int32Pointer],
        );
        let state = CState::new()
            .with_local("p", CValue::pointer(pointer.clone()))
            .with_memory(CMemory::new().with_block(pointer.block.clone(), 512))
            .with_resource_context(ResourceContext::new().unchecked_with_fact(
                CResourceFact::own_composite(
                    "TransitionWrapper".into(),
                    vec![CValue::pointer(pointer.clone())],
                ),
            ));
        let function = c_function(
            CType::Void,
            format!("wrapper_projection_{used_members}"),
            vec![c_parameter("p", CType::Int32Pointer)],
            CStatement::Skip,
        )
        .with_contract(vec![], vec![], vec![], vec![], true)
        .with_resource_summary(vec![requirement], vec![])
        .with_composite_resource_definitions(vec![definition])
        .with_resource_derived_mutable_frame();
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            let transfer = prepare_contract_resource_transfer(
                &state,
                &state,
                function.name(),
                function.contract_interface(),
                &PureFactContext::new(),
                &mut ExecutionBudget::default(),
                false,
            )
            .unwrap()
            .unwrap();
            let mut inputs = transfer.borrowed_inputs.clone();
            inputs.extend(transfer.consumed_inputs.clone());
            project_contract_memory_effects(
                &state,
                function.contract_interface(),
                Some(&inputs),
                &PureFactContext::new(),
                &mut ExecutionBudget::default(),
            )
        });
        // Adjacent body members are normalized to one physical range; the
        // curve still charges their checked expansion and effect projection.
        assert_eq!(result.unwrap().unwrap().ranges.len(), 1);
        samples.push((used_members, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * (pair[1].0 / pair[0].0).max(1) + 256,
            "wrapper projection should charge used members: {samples:?}"
        );
    }
}

#[test]
fn resource_derived_refinement_compares_checked_ranges() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:resource-refinement:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::pointer(pointer.clone()))
        .with_memory(CMemory::new().with_block(pointer.block.clone(), 8));
    let resource = |start| {
        CResourceSpec::owned_memory(CMemorySegment::new(
            CExpression::Variable("p".into()),
            CExpression::Value(int32(start)),
            CExpression::Value(int32(start + 1)),
        ))
    };
    let target = c_function(CType::Void, "resource_target", vec![], CStatement::Skip)
        .with_contract(vec![], vec![], vec![], vec![], true)
        .with_resource_summary(vec![resource(0)], vec![])
        .with_resource_derived_mutable_frame();
    let implementation = c_function(
        CType::Void,
        "resource_implementation",
        vec![],
        CStatement::Skip,
    )
    .with_contract(vec![], vec![], vec![], vec![], true)
    .with_resource_summary(vec![resource(1)], vec![])
    .with_resource_derived_mutable_frame();
    assert!(
        !mutable_footprint_is_compatible(
            &target,
            &implementation,
            &state,
            &state,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
    );
}

#[test]
fn resource_derived_frame_rejects_mixed_explicit_effect_metadata() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:mixed-resource-frame:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::pointer(pointer.clone()))
        .with_memory(CMemory::new().with_block(pointer.block.clone(), 4));
    let function = c_function(
        CType::Void,
        "mixed_resource_frame",
        vec![],
        CStatement::Skip,
    )
    .with_contract(
        vec![],
        vec![],
        vec![
            CMemorySegment::new(
                CExpression::Variable("p".into()),
                CExpression::Value(int32(0)),
                CExpression::Value(int32(1)),
            ),
            CMemorySegment::new(
                CExpression::Variable("p".into()),
                CExpression::Value(int32(2)),
                CExpression::Value(int32(3)),
            ),
        ],
        vec![],
        true,
    )
    .with_resource_summary(
        vec![CResourceSpec::owned_memory(CMemorySegment::new(
            CExpression::Variable("p".into()),
            CExpression::Value(int32(0)),
            CExpression::Value(int32(1)),
        ))],
        vec![],
    )
    .with_resource_derived_mutable_frame();
    let projection = project_contract_memory_effects(
        &state,
        function.contract_interface(),
        None,
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(projection.is_err());
}

#[test]
fn resource_derived_loop_frame_rejects_wrapper_range_disagreement() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:loop-wrapper:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let definition = CCompositeResourceDefinition::new(
        "LoopWrapper",
        vec![c_parameter("data", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment::new(
            CExpression::Variable("data".into()),
            CExpression::Value(int32(0)),
            CExpression::Value(int32(1)),
        ))],
        vec![],
    );
    let requirement = CResourceSpec::composite(
        CResourceAccessMode::Own,
        "LoopWrapper".into(),
        vec![CExpression::Variable("p".into())],
        vec![CType::Int32Pointer],
    );
    let wrong_loop_frame = CLoopEffectCheck::new_with_origin(
        CLoopEffect::Mutable(vec![CMemorySegment::new(
            CExpression::Variable("p".into()),
            CExpression::Value(int32(1)),
            CExpression::Value(int32(2)),
        )]),
        CLoopEffectSpan::Whole,
        CLoopEffectOrigin::InheritedResourceDerived,
        Some("loop 0 inherited owned resource frame".into()),
    );
    let body = CStatement::While {
        condition: c_int32_literal(0),
        invariant: vec![],
        invariant_checks: vec![],
        effect_checks: vec![wrong_loop_frame],
        resource_specs: vec![],
        ranking_measures: vec![],
        structural_measure: None,
        do_while: false,
        body: Box::new(CStatement::Skip),
    };
    let function = c_function(
        CType::Void,
        "wrong_loop_wrapper_frame",
        vec![c_parameter("p", CType::Int32Pointer)],
        body,
    )
    .with_contract(vec![], vec![], vec![], vec![], true)
    .with_resource_summary(vec![requirement], vec![])
    .with_composite_resource_definitions(vec![definition])
    .with_resource_derived_mutable_frame();
    let state = CState::new()
        .with_local("p", CValue::pointer(pointer.clone()))
        .with_memory(CMemory::new().with_block(pointer.block, 4));
    let result = validate_resource_derived_loop_frames(
        &function,
        &state,
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(result.is_err());
}

#[test]
fn resource_derived_loop_setup_does_not_fallback_to_surface_metadata() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:loop-fallback:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let source_segment = CMemorySegment::new(
        CExpression::Variable("p".into()),
        CExpression::Value(int32(0)),
        CExpression::Value(int32(1)),
    );
    let token = CResourceSpec::declared(
        ResourceFamily::Token,
        CResourceAccessMode::Own,
        "slot".into(),
        vec![],
        vec![],
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    let quantity = CResourceSpec::quantified(
        CExpression::Variable("missing_quantity".into()),
        token,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    let inherited = CLoopEffectCheck::new_with_origin(
        CLoopEffect::Mutable(vec![source_segment.clone()]),
        CLoopEffectSpan::Whole,
        CLoopEffectOrigin::InheritedResourceDerived,
        Some("loop 0 inherited owned resource frame".into()),
    );
    let function = c_function(
        CType::Void,
        "reject_loop_surface_fallback",
        vec![c_parameter("p", CType::Int32Pointer)],
        CStatement::While {
            condition: c_int32_literal(0),
            invariant: vec![],
            invariant_checks: vec![],
            effect_checks: vec![inherited],
            resource_specs: vec![],
            ranking_measures: vec![],
            structural_measure: None,
            do_while: false,
            body: Box::new(CStatement::Skip),
        },
    )
    .with_contract(vec![], vec![], vec![], vec![], true)
    .with_resource_summary(vec![quantity], vec![])
    .with_resource_derived_mutable_frame()
    .with_resource_derived_mutable_segments(vec![source_segment]);
    let state = CState::new()
        .with_local("p", CValue::pointer(pointer.clone()))
        .with_memory(CMemory::new().with_block(pointer.block, 4));
    let result = establish_resource_derived_loop_frames(
        function,
        &state,
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(
        result.is_err(),
        "unchecked metadata must not authorize a loop frame"
    );
}

#[test]
fn unresolved_call_requirements_retain_selected_source_site_identity() {
    let function = c_function(
        CType::Int32,
        "requires_positive",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("x")),
            operator: CComparisonOperator::GreaterThan,
            right: SpecExpression::Value(int32(0)),
        }],
        vec![],
        vec![],
        vec![],
        true,
    );
    let contract = CFunctionContract::new("RequiresPositive", function).unwrap();
    let arguments = vec![c_int32_literal(0)];
    let first_state = CState::new().with_memory(CMemory::new().with_block("first", 4));
    let second_state = CState::new().with_memory(CMemory::new().with_block("second", 4));
    let run = |state: &CState| {
        execute_c_function_contracts_paths(
            state,
            &[&contract],
            &arguments,
            &PureFactContext::new(),
            &CExecutionEnvironment::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
    };
    let first = run(&first_state);
    let second = run(&second_state);
    let first_site = first[0].obligations[0]
        .call_requirement_site()
        .expect("the first required call should carry source identity");
    let second_site = second[0].obligations[0]
        .call_requirement_site()
        .expect("the second required call should carry source identity");
    assert_eq!(first_site.callee, "requires_positive");
    assert_eq!(second_site.callee, "requires_positive");
    assert_eq!(first_site.interface.as_ref(), "RequiresPositive");
    assert_eq!(second_site.interface.as_ref(), "RequiresPositive");
    assert_eq!(first_site.candidate_ordinal, 0);
    assert_eq!(second_site.candidate_ordinal, 0);
    assert_eq!(first_site.requirement_ordinal, 0);
    assert_eq!(second_site.requirement_ordinal, 0);
    assert_eq!(first_site.source_requirement_ordinal, None);
    assert_eq!(second_site.source_requirement_ordinal, None);
    assert!(!first_site.source_requirement_is_state_independent);
    assert!(!second_site.source_requirement_is_state_independent);
    assert_eq!(first_site.source_arguments.as_slice(), arguments.as_slice());
    assert_eq!(
        second_site.source_arguments.as_slice(),
        arguments.as_slice()
    );
    assert_eq!(
        first_site.source_snapshot,
        CMemorySnapshotIdentity::of(first_state.memory())
    );
    assert_eq!(
        second_site.source_snapshot,
        CMemorySnapshotIdentity::of(second_state.memory())
    );
    assert_ne!(
        first_site.source_snapshot, second_site.source_snapshot,
        "same callee and arguments must remain separated by source snapshot identity"
    );
}

#[test]
fn selected_contract_and_requirement_ordinals_stay_with_their_call() {
    let template = c_function(
        CType::Int32,
        "same_target",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![
            SpecProposition::Predicate {
                name: "first_requirement".to_string(),
                arguments: vec![],
            },
            SpecProposition::Predicate {
                name: "second_requirement".to_string(),
                arguments: vec![],
            },
        ],
        vec![],
        vec![],
        vec![],
        true,
    )
    .with_contract_requirement_sources(vec![None, Some(1)]);
    let first = CFunctionContract::new("FirstInterface", template.clone()).unwrap();
    let second = CFunctionContract::new("SecondInterface", template).unwrap();
    let paths = execute_c_function_contracts_paths(
        &CState::new(),
        &[&first, &second],
        &[c_int32_literal(0)],
        &PureFactContext::new(),
        &CExecutionEnvironment::new().with_selected_call_contract("SecondInterface"),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let sources = paths[0]
        .obligations
        .iter()
        .filter_map(|obligation| obligation.call_requirement_site())
        .collect::<Vec<_>>();
    assert_eq!(sources.len(), 2);
    assert!(
        sources
            .iter()
            .all(|source| source.interface.as_ref() == "SecondInterface")
    );
    assert!(sources.iter().all(|source| source.callee == "same_target"));
    assert!(sources.iter().all(|source| source.candidate_ordinal == 1));
    assert_eq!(sources[0].requirement_ordinal, 0);
    assert_eq!(sources[1].requirement_ordinal, 1);
    assert_eq!(sources[0].source_requirement_ordinal, None);
    assert_eq!(sources[1].source_requirement_ordinal, Some(1));
    assert!(!sources[0].source_requirement_is_state_independent);
    assert!(!sources[1].source_requirement_is_state_independent);
    assert!(std::sync::Arc::ptr_eq(&sources[0].site, &sources[1].site));
}

#[test]
fn requirement_capability_describes_the_complete_source_tree() {
    let pure_disjunction = SpecProposition::Or(
        Box::new(SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("x")),
            operator: CComparisonOperator::GreaterThan,
            right: SpecExpression::Value(int32(100)),
        }),
        Box::new(SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("x")),
            operator: CComparisonOperator::LessThan,
            right: SpecExpression::Value(int32(0)),
        }),
    );
    // This shape is the arithmetic guard beneath the existential witnesses
    // used by cstr-style predicates. Its enclosing source requirement still
    // reads memory, so a lowered arithmetic leaf must not advertise the
    // whole requirement as state independent.
    let stateful_exists = SpecProposition::ExistsInt32 {
        name: "len".to_string(),
        variable: Variable(900),
        body: Box::new(SpecProposition::MemoryLoadable {
            memory: SpecMemory::Current,
            base: SpecExpression::CExpression(c_variable("p")),
            start: SpecExpression::Value(int32(0)),
            end: SpecExpression::Value(int32(1)),
            element_width: 4,
        }),
    };
    let function = c_function(
        CType::Int32,
        "capability_source",
        vec![
            c_parameter("p", CType::Int32Pointer),
            c_parameter("x", CType::Int32),
        ],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![pure_disjunction, stateful_exists],
        vec![],
        vec![],
        vec![],
        true,
    )
    .with_contract_requirement_sources(vec![Some(0), Some(1)]);
    let contract = CFunctionContract::new("CapabilitySource", function).unwrap();
    let paths = execute_c_function_contracts_paths(
        &CState::new(),
        &[&contract],
        &[
            c_typed_pointer_value(Pointer::symbolic(Variable(901)), CType::Int32Pointer),
            c_int32_literal(7),
        ],
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    let sources = paths[0]
        .obligations
        .iter()
        .filter_map(|obligation| obligation.call_requirement_site())
        .collect::<Vec<_>>();
    let pure_source = sources
        .iter()
        .find(|source| source.requirement_ordinal == 0)
        .expect("the pure source requirement should remain an obligation");
    let stateful_source = sources
        .iter()
        .find(|source| source.requirement_ordinal == 1)
        .expect("the stateful source requirement should remain an obligation");
    assert!(pure_source.source_requirement_is_state_independent);
    assert!(
        sources
            .iter()
            .filter(|source| source.requirement_ordinal == 1)
            .all(|source| !source.source_requirement_is_state_independent)
    );
    assert_eq!(pure_source.source_requirement_ordinal, Some(0));
    assert_eq!(stateful_source.source_requirement_ordinal, Some(1));
    assert!(std::sync::Arc::ptr_eq(
        &pure_source.site,
        &stateful_source.site
    ));
}

#[test]
fn generated_requirement_source_cannot_advertise_state_independence() {
    let site = std::sync::Arc::new(CallRequirementSite::for_requirement(
        "generated",
        "Generated",
        0,
        &[],
        &CMemory::new(),
    ));
    let source = CallRequirementSource::new(site, 0, None, true, None);
    assert!(!source.source_requirement_is_state_independent);
}

#[test]
fn calls_without_unresolved_requirements_do_not_construct_call_site_metadata() {
    let function = c_function(
        CType::Int32,
        "established",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_variable("x")),
    )
    .with_contract(vec![], vec![], vec![], vec![], true);
    let contract = CFunctionContract::new("Established", function).unwrap();

    CallRequirementSite::reset_test_construction_count();
    let paths = execute_c_function_contracts_paths(
        &CState::new(),
        &[&contract],
        &[c_int32_literal(7)],
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();

    assert!(matches!(paths[0].outcome, CFunctionOutcome::Return { .. }));
    assert_eq!(
        CallRequirementSite::test_construction_count(),
        0,
        "established calls must not construct or intern carrier metadata"
    );
}

#[test]
fn missing_contract_requirement_source_map_fails_closed() {
    let function = c_function(
        CType::Int32,
        "missing_map",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![SpecProposition::Predicate {
            name: "requirement".to_string(),
            arguments: vec![],
        }],
        vec![],
        vec![],
        vec![],
        true,
    )
    .without_test_contract_requirement_sources();
    let contract = CFunctionContract::new("MissingMap", function).unwrap();
    let paths = execute_c_function_contracts_paths(
        &CState::new(),
        &[&contract],
        &[c_int32_literal(0)],
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(
        paths[0].outcome,
        CFunctionOutcome::RuntimeError(CRuntimeError::FunctionContract(ref message))
            if message.contains("source map")
    ));
    assert!(paths[0].obligations.is_empty());
}

#[test]
fn contract_source_maps_do_not_change_function_semantic_identity() {
    let requirements = vec![SpecProposition::Predicate {
        name: "requirement".to_string(),
        arguments: vec![],
    }];
    let base = c_function(
        CType::Int32,
        "same_identity",
        vec![],
        c_return(c_int32_literal(0)),
    )
    .with_contract(requirements, vec![], vec![], vec![], true);
    let mapped = base
        .clone()
        .with_contract_requirement_sources(vec![Some(0)]);
    assert_eq!(base, mapped);
    assert_eq!(base.cmp(&mapped), std::cmp::Ordering::Equal);
    use std::hash::{Hash, Hasher};
    let mut base_hasher = std::collections::hash_map::DefaultHasher::new();
    let mut mapped_hasher = std::collections::hash_map::DefaultHasher::new();
    base.hash(&mut base_hasher);
    mapped.hash(&mut mapped_hasher);
    assert_eq!(base_hasher.finish(), mapped_hasher.finish());
}

#[test]
fn call_snapshot_identity_work_does_not_scale_with_unrelated_memory() {
    let small = CMemory::new();
    let large = (0..256).fold(CMemory::new(), |memory, index| {
        memory.with_block(format!("unrelated{index}"), 4)
    });
    let (_, small_work) =
        crate::instrumentation::measure_deterministic_work(|| CMemorySnapshotIdentity::of(&small));
    let (_, large_work) =
        crate::instrumentation::measure_deterministic_work(|| CMemorySnapshotIdentity::of(&large));
    assert_eq!(
        small_work, large_work,
        "snapshot identity must not scan unrelated memory"
    );
}

#[test]
fn empty_requirement_lowering_retains_selected_call_source() {
    let function = c_function(
        CType::Int32,
        "empty_requirement_path",
        vec![],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("missing")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        vec![],
        vec![],
        vec![],
        true,
    );
    let contract = CFunctionContract::new("EmptyRequirement", function).unwrap();
    let paths = execute_c_function_contracts_paths(
        &CState::new(),
        &[&contract],
        &[],
        &PureFactContext::new(),
        &CExecutionEnvironment::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert_eq!(paths[0].obligations.len(), 1);
    let source = paths[0].obligations[0]
        .call_requirement_site()
        .expect("empty lowering path is still a selected call requirement");
    assert_eq!(source.interface.as_ref(), "EmptyRequirement");
    assert_eq!(source.requirement_ordinal, 0);
    assert_eq!(source.source_requirement_ordinal, None);
}

#[test]
fn source_load_snapshot_collection_is_iterative_and_bounded() {
    let leaf = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    // The condition node is visited in addition to the proposition nodes.
    let within_limit = (0..4094).fold(leaf.clone(), |body, _| Proposition::Not(Box::new(body)));
    assert!(
        source_load_snapshot_for_proposition(&within_limit)
            .expect("the bounded collector should handle deep logical structure")
            .is_none()
    );
    let over_limit = Proposition::Not(Box::new(within_limit));
    assert_eq!(
        source_load_snapshot_for_proposition(&over_limit),
        Err(ExecutionLimit::ExpressionSteps),
        "metadata collection must propagate structural exhaustion"
    );
}

fn interface(index: usize) -> CFunctionContract {
    let function = c_function(
        CType::Int32,
        format!("Bound{index}"),
        vec![c_parameter("value", CType::Int32)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::GreaterEqual,
            right: SpecExpression::Value(int32((-(index as i32)) as u32)),
        }],
        vec![],
        vec![],
        true,
    );
    CFunctionContract::new(format!("Bound{index}"), function).unwrap()
}

#[test]
fn callback_conjunction_shares_call_budget_and_scales_with_interfaces() {
    check_callback_interface_scaling(false);
}

#[test]
fn selected_callback_shares_call_budget_and_scales_with_interfaces() {
    check_callback_interface_scaling(true);
}

fn check_callback_interface_scaling(select: bool) {
    let mut samples = Vec::new();
    for count in [1, 8, 32, 128] {
        let contracts = (0..count).map(interface).collect::<Vec<_>>();
        let contracts = contracts.iter().collect::<Vec<_>>();
        let mut budget = ExecutionBudget::default()
            .with_function_calls(1)
            .with_paths(1);
        let initial_expressions = budget.expression_steps;
        let environment = if select {
            CExecutionEnvironment::new().with_selected_call_contract(&format!("Bound{}", count - 1))
        } else {
            CExecutionEnvironment::new()
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_c_function_contracts_paths(
                &CState::new(),
                &contracts,
                &[c_int32_literal(7)],
                &PureFactContext::new(),
                &environment,
                &mut budget,
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert!(matches!(paths[0].outcome, CFunctionOutcome::Return { .. }));
        assert!(paths[0].obligations.is_empty());
        assert!(paths[0].facts.len() >= count);
        assert_eq!(budget.function_calls, 0);
        assert_eq!(budget.next_kernel_variable(), 2);
        samples.push((count, work, initial_expressions - budget.expression_steps));
    }
    for pair in samples.windows(2) {
        let ratio = pair[1].0 / pair[0].0;
        assert!(
            pair[1].1 <= (pair[0].1 + 16) * ratio,
            "conjunction work must scale with relevant interfaces: {samples:?}"
        );
        assert!(
            pair[1].2 <= (pair[0].2 + 4) * ratio,
            "conjunction expression work must scale linearly: {samples:?}"
        );
    }
}

#[test]
fn callback_conjunction_does_not_visit_unrelated_functions() {
    check_unrelated_functions(false);
}

#[test]
fn selected_callback_does_not_visit_unrelated_functions() {
    check_unrelated_functions(true);
}

#[test]
fn callback_fact_lookup_scales_with_calls_not_unrelated_supported_facts() {
    fn callback_fact(name: &str, pointer: Pointer, state: CState) -> Proposition {
        Proposition::Predicate {
            name: CFunctionContract::predicate_name_for(name),
            arguments: vec![
                Term::CState(state),
                Term::CValue(CValue::typed_pointer(
                    pointer,
                    CType::FunctionPointer(CallbackSignature::from_encoded(91_000)),
                )),
            ],
        }
    }

    let target = Pointer::symbolic_function(Variable(92_000));
    let mut samples = Vec::new();
    for calls in [1usize, 2, 4, 8, 16] {
        for unrelated in [4usize, 16, 64, 256, 1024] {
            let mut assumptions = PureFactContext::new().assume_proposition(callback_fact(
                "Target",
                target.clone(),
                CState::new(),
            ));
            for index in 0..unrelated {
                assumptions = assumptions.assume_proposition(callback_fact(
                    "Unrelated",
                    Pointer::symbolic_function(Variable(93_000 + index as u64)),
                    CState::new(),
                ));
            }
            let before_allocations = crate::persistent::persistent_node_allocations();
            let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
                (0..calls)
                    .map(|_| assumptions.function_contract_facts_for(&target).count())
                    .sum::<usize>()
            });
            let allocations = crate::persistent::persistent_node_allocations() - before_allocations;
            assert_eq!(found, calls);
            assert_eq!(
                allocations, 0,
                "lookup must not allocate for unrelated facts"
            );
            samples.push((calls, unrelated, work));
        }
    }

    for calls in [1usize, 2, 4, 8, 16] {
        let row = samples
            .iter()
            .filter(|(sample_calls, _, _)| *sample_calls == calls)
            .collect::<Vec<_>>();
        assert!(
            row.windows(2).all(|pair| pair[1].2 == pair[0].2),
            "unrelated supported callback facts changed lookup work at {calls} calls: {row:?}"
        );
    }
    for pair in samples
        .iter()
        .filter(|(_, unrelated, _)| *unrelated == 4)
        .collect::<Vec<_>>()
        .windows(2)
    {
        assert!(
            pair[1].2 <= pair[0].2 * 2,
            "callback lookup work should grow linearly with selected calls: {samples:?}"
        );
    }
}

fn check_unrelated_functions(select: bool) {
    let contracts = [interface(0), interface(1)];
    let contracts = contracts.iter().collect::<Vec<_>>();
    let mut samples = Vec::new();
    for count in [0, 16, 64, 256] {
        let mut environment = CExecutionEnvironment::new();
        for index in 0..count {
            environment = environment.with_function(c_function(
                CType::Int32,
                format!("unrelated{index}"),
                vec![],
                c_return(c_int32_literal(0)),
            ));
        }
        let mut budget = ExecutionBudget::default()
            .with_function_calls(1)
            .with_paths(1);
        if select {
            let selected = environment.clone().with_selected_call_contract("Bound1");
            assert!(selected.shares_all_storage_with(&environment));
            assert_ne!(selected, environment);
            assert!(environment.selected_call_contract.is_none());
            environment = selected;
        }
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_c_function_contracts_paths(
                &CState::new(),
                &contracts,
                &[c_int32_literal(7)],
                &PureFactContext::new(),
                &environment,
                &mut budget,
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        samples.push((work, budget));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated functions must not change call work: {samples:?}"
    );
}

/// Contract refinement decides one named clause by the exact routes only:
/// indexed exact membership and the frozen condition checker on a bare
/// condition. Neither a decided clause nor a rejected one may scan the
/// ambient facts, so growing the unrelated context must not change the work.
#[test]
fn contract_refinement_work_is_flat_in_unrelated_facts() {
    let variable = |index| Bitvector32Term::Variable(Variable(index));
    let bound = ConditionTerm::signed_less_than(variable(70_001), Bitvector32Term::Constant(10));
    let equality = ConditionTerm::equal(variable(70_002), variable(70_003));
    let refuted = ConditionTerm::signed_less_than(variable(70_005), Bitvector32Term::Constant(0));
    let unproved = Proposition::Predicate {
        name: "unproved_refinement_clause".to_string(),
        arguments: vec![],
    };
    // An exactly available bare condition.
    let exact = Proposition::ConditionIs(equality.clone(), true);
    // A bare condition the frozen checker decides against, read through `not`.
    let negated = Proposition::Not(Box::new(Proposition::ConditionIs(refuted.clone(), true)));
    // Compound clauses no exact route establishes. The logical descent that
    // used to split these now belongs to the refinement theorem's proof, so
    // the kernel answers no — and must do so without an ambient scan.
    let structural = Proposition::And(
        Box::new(Proposition::ConditionIs(bound.clone(), true)),
        Box::new(Proposition::Or(
            Box::new(Proposition::ConditionIs(equality.clone(), true)),
            Box::new(unproved.clone()),
        )),
    );
    let guarded = Proposition::Implies(
        Box::new(Proposition::ConditionIs(refuted.clone(), true)),
        Box::new(unproved),
    );

    let samples = [16, 64, 256, 1024]
        .into_iter()
        .map(|size| {
            let mut assumptions = PureFactContext::new()
                .assume_condition(bound.clone(), true)
                .assume_condition(equality.clone(), true)
                .assume_condition(refuted.clone(), false);
            for index in 0..size {
                assumptions = assumptions.assume_condition(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(71_000 + index as u64)),
                        Bitvector32Term::Constant(index as u32 + 1),
                    ),
                    true,
                );
            }
            let measure = |goal: &Proposition, expected: bool| {
                let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                    contract_refinement_proves(&assumptions, goal)
                });
                assert_eq!(
                    proved, expected,
                    "refinement answer changed with {size} unrelated facts"
                );
                work
            };
            (
                size,
                measure(&exact, true),
                measure(&negated, true),
                measure(&structural, false),
                measure(&guarded, false),
            )
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| {
            pair[0].1 == pair[1].1
                && pair[0].2 == pair[1].2
                && pair[0].3 == pair[1].3
                && pair[0].4 == pair[1].4
        }),
        "refinement checking must not scan unrelated ambient facts: {samples:?}"
    );
}
