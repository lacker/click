use super::*;

#[test]
fn resource_call_arguments_are_checked_in_kernel_and_fields_are_fresh() {
    let schema = ResourceFieldSchema::new(vec![(
        "revision".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let parameter = |identity| {
        ResourceSpec::instance(
            Variable(identity),
            format!("cell{identity}"),
            schema.clone(),
            ResourceSpec::composite(ResourceAccessMode::Own, "marker".into(), vec![], vec![]),
            ResourceTransferRole::Consume,
            ResourceStateSource::Current,
        )
        .unwrap()
    };
    // `marker` is an ordinary resource: declaring it lets the kernel see that
    // this assumed contract reaches no population.
    let function = program_function(ProgramType::Void, "touch", vec![], ProgramStatement::Skip)
        .with_contract(vec![], vec![], vec![], vec![], true)
        .with_resource_summary(vec![parameter(0)], vec![parameter(0)])
        .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
            "marker",
            vec![],
            None,
            false,
            vec![],
            vec![],
        )]);
    let contract = FunctionContract::new("Touch", function)
        .unwrap()
        .with_proof_parameters(vec![parameter(0)]);
    // Reserve the identifier immediately after the call's memory/result IDs.
    // Post-field generation must skip it, not accidentally preserve the field.
    let before = ResourceInstance::new(
        Variable(10),
        "marker".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::Program(symbolic_call_result(
            ProgramType::Int32,
            Variable(1_000_002),
        ))]
        .into(),
    )
    .unwrap();
    let state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(before.clone()))),
        );
    let environment = ExecutionEnvironment::new()
        .with_selected_call_contract("Touch")
        .with_selected_call_resource_arguments(vec![Variable(10)]);
    let run = |state: &ExecutionState,
               contract: &FunctionContract,
               environment: &ExecutionEnvironment| {
        execute_program_function_contracts_paths(
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
    let FunctionOutcome::Return { state: after, .. } = &paths[0].outcome else {
        panic!("call failed: {:?}", paths[0].outcome);
    };
    assert!(after.resource_bindings.is_none());
    let returned = after.owned_resource_instance(Variable(10)).unwrap();
    assert_ne!(returned.fields(), before.fields());
    for (state, contract, environment) in [
        (
            ExecutionState::new().with_population_creation_tracking(),
            contract.clone(),
            environment.clone(),
        ),
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
            FunctionOutcome::RuntimeError(_)
        ));
    }
}

#[test]
fn direct_call_map_is_checked_in_kernel_like_named_proof_arguments() {
    let schema = ResourceFieldSchema::new(vec![(
        "revision".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let parameter = |identity| {
        ResourceSpec::instance(
            Variable(identity),
            format!("cell{identity}"),
            schema.clone(),
            ResourceSpec::composite(ResourceAccessMode::Own, "marker".into(), vec![], vec![]),
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        )
        .unwrap()
    };
    let function = program_function(ProgramType::Void, "touch", vec![], ProgramStatement::Skip)
        .with_contract(vec![], vec![], vec![], vec![], true)
        .with_resource_summary(
            vec![parameter(0), parameter(1)],
            vec![parameter(0), parameter(1)],
        );
    let owned = |identity: u64| {
        ResourceFact::own(Resource::Instance(
            ResourceInstance::new(
                Variable(identity),
                "marker".into(),
                vec![].into(),
                schema.clone(),
                vec![AlgebraicValue::Program(symbolic_call_result(
                    ProgramType::Int32,
                    Variable(1_000_000 + identity),
                ))]
                .into(),
            )
            .unwrap(),
        ))
    };
    let state = ExecutionState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_facts([owned(10), owned(11)]));
    let bind = |callee: &str, pairs: &[(u64, u64)]| {
        let environment = ExecutionEnvironment::new().with_selected_call_binders(
            callee,
            0,
            pairs
                .iter()
                .map(|(binder, instance)| (Variable(*binder), Variable(*instance)))
                .collect(),
        );
        selected_call_binder_application(
            "touch",
            function.contract_interface(),
            &state,
            &environment,
            None,
        )
    };
    let application = bind("touch", &[(0, 10), (1, 11)])
        .unwrap()
        .expect("a map naming this callee binds it");
    assert_eq!(application.parameters.len(), 2);
    assert_eq!(application.bindings.len(), 2);
    assert!(
        bind("other", &[(0, 10), (1, 11)]).unwrap().is_none(),
        "a map for another callee binds nothing here"
    );
    // The same two refusals the named proof arguments get, from the same
    // constructor: one instance for two binders, and an instance the caller
    // does not own.
    assert_eq!(
        bind("touch", &[(0, 10), (1, 10)]).unwrap_err(),
        "duplicate exclusive resource proof argument"
    );
    assert_eq!(
        bind("touch", &[(0, 99), (1, 11)]).unwrap_err(),
        "resource proof argument is not owned"
    );
}

#[test]
fn resource_transition_retains_borrow_role_for_owned_entry_fact() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:borrow-role:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = MemoryRange::new(
        pointer.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    let requirement = ResourceSpec::owned_memory(MemorySegment::new(
        ProgramExpression::Variable("p".into()),
        ProgramExpression::Value(int32(0)),
        ProgramExpression::Value(int32(1)),
    ))
    .with_role(ResourceTransferRole::Borrow)
    .with_state_source(ResourceStateSource::Entry);
    let function = program_function(
        ProgramType::Void,
        "borrow_role",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        ProgramStatement::Skip,
    )
    .with_contract(vec![], vec![], vec![], vec![], true)
    .with_resource_summary(vec![requirement], vec![]);
    let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(range));
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(pointer.clone()))
        .with_memory(Memory::new().with_block(pointer.block.clone(), 4))
        .with_resource_context(resources);
    let transfer = prepare_contract_resource_transfer(
        &state,
        &state,
        function.name(),
        function.contract_interface(),
        &PureFactContext::new(),
        &mut ExecutionBudget::default(),
        false,
        ResourceTransitionPurpose::FunctionBoundary,
    )
    .unwrap()
    .unwrap();
    assert_eq!(transfer.borrowed_inputs.len(), 1);
    assert!(transfer.consumed_inputs.is_empty());
    assert_eq!(
        transfer.borrowed_inputs[0].state_source,
        ResourceStateSource::Entry
    );
    assert_eq!(
        transfer.borrowed_inputs[0].role,
        ResourceTransferRole::Borrow
    );
}

#[test]
fn call_site_and_function_boundary_transitions_agree_on_the_callee_entry() {
    let block = |name: &str| Pointer {
        block: PointerBlock::Concrete(format!("local:purpose:{name}")),
        offset: PointerOffsetTerm::Constant(0),
    };
    let (owned, viewed) = (block("owned"), block("viewed"));
    let range = |pointer: &Pointer| {
        MemoryRange::new(
            pointer.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )
    };
    let segment = |name: &str| {
        MemorySegment::new(
            ProgramExpression::Variable(name.into()),
            ProgramExpression::Value(int32(0)),
            ProgramExpression::Value(int32(1)),
        )
    };
    let function = program_function(
        ProgramType::Void,
        "purpose_agreement",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("q", ProgramType::Int32Pointer),
        ],
        ProgramStatement::Skip,
    )
    .with_contract(vec![], vec![], vec![], vec![], true)
    .with_resource_summary(
        vec![
            ResourceSpec::owned_memory(segment("p")).with_role(ResourceTransferRole::Borrow),
            ResourceSpec::viewed_memory(segment("q")),
            ResourceSpec::token(ResourceAccessMode::Own, "spare".into(), vec![], vec![])
                .with_role(ResourceTransferRole::Consume),
        ],
        vec![],
    );
    let resources = ResourceContext::new().unchecked_with_facts([
        ResourceFact::own_memory(range(&owned)),
        ResourceFact::own_memory(range(&viewed)),
        ResourceFact::own_token("spare".into(), vec![]),
        ResourceFact::own_token("unrelated".into(), vec![]),
    ]);
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(owned.clone()))
        .with_local("q", ProgramValue::pointer(viewed.clone()))
        .with_memory(
            Memory::new()
                .with_block(owned.block.clone(), 4)
                .with_block(viewed.block.clone(), 4),
        )
        .with_resource_context(resources);
    let assumptions = PureFactContext::new();
    let prepare = |purpose| {
        prepare_contract_resource_transfer(
            &state,
            &state,
            function.name(),
            function.contract_interface(),
            &assumptions,
            &mut ExecutionBudget::default(),
            false,
            purpose,
        )
        .unwrap()
        .unwrap()
    };
    let call_site = prepare(ResourceTransitionPurpose::CallSite);
    let boundary = prepare(ResourceTransitionPurpose::FunctionBoundary);
    assert!(call_site.stable_view_plan.is_some(), "a call site lends");
    assert!(boundary.stable_view_plan.is_none(), "a boundary does not");

    // The same requirements are checked in, with the same roles.
    let facts = |checked: &[CheckedResourceFact]| {
        checked
            .iter()
            .map(|checked| (checked.fact.clone(), checked.role))
            .collect::<BTreeSet<_>>()
    };
    assert_eq!(
        facts(&call_site.borrowed_inputs),
        facts(&boundary.borrowed_inputs)
    );
    assert_eq!(
        facts(&call_site.consumed_inputs),
        facts(&boundary.consumed_inputs)
    );
    assert_eq!(call_site.memory_effects, boundary.memory_effects);

    // The callee enters with the same authority on either route: every
    // declared requirement is satisfied, and the unrelated token stays with
    // the caller on both.
    for checked in call_site
        .borrowed_inputs
        .iter()
        .chain(&call_site.consumed_inputs)
    {
        assert!(
            call_site
                .callee_resources
                .satisfies_fact(&checked.fact, &assumptions),
            "call site callee lacks {:?}",
            checked.fact
        );
        assert!(
            boundary
                .callee_resources
                .satisfies_fact(&checked.fact, &assumptions),
            "boundary callee lacks {:?}",
            checked.fact
        );
    }
    let unrelated = ResourceFact::own_token("unrelated".into(), vec![]);
    for transfer in [&call_site, &boundary] {
        assert!(
            !transfer
                .callee_resources
                .satisfies_fact(&unrelated, &assumptions)
        );
        assert!(
            transfer
                .caller_resources_after_requirements
                .satisfies_fact(&unrelated, &assumptions)
        );
        assert!(
            !transfer.caller_resources_after_requirements.satisfies_fact(
                &ResourceFact::own_token("spare".into(), vec![]),
                &assumptions
            ),
            "a consumed token leaves the caller on both routes"
        );
    }
}

#[test]
fn stable_view_refinement_uses_checked_variance_for_subranges() {
    let base = Pointer {
        block: PointerBlock::Concrete("refinement:stable-view".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local(
            "p",
            ProgramValue::typed_pointer(base, ProgramType::Int32Pointer),
        )
        .with_memory(Memory::new().with_block("refinement:stable-view", 8));
    let segment = |end| {
        MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(end),
        )
    };
    let interface = |name: &str, requirement| {
        program_function(
            ProgramType::Void,
            name,
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            ProgramStatement::Skip,
        )
        .with_resource_summary(vec![requirement], Vec::new())
    };
    let owned = interface("owned_target", ResourceSpec::owned_memory(segment(2)));
    let reader = interface(
        "view_implementation",
        ResourceSpec::viewed_memory(segment(1)),
    );
    assert_eq!(
        checked_access_mode_refinement_adapter(
            owned.contract_interface(),
            reader.contract_interface(),
            &state,
            &state,
            &state,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .expect("refinement planning should stay bounded"),
        Some(true),
        "a proper owned superrange must enter through the checked loan adapter"
    );

    let viewed = interface("view_target", ResourceSpec::viewed_memory(segment(2)));
    let writer = interface(
        "owned_implementation",
        ResourceSpec::owned_memory(segment(1)),
    );
    assert_eq!(
        checked_access_mode_refinement_adapter(
            viewed.contract_interface(),
            writer.contract_interface(),
            &state,
            &state,
            &state,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .expect("reverse refinement should be decided"),
        Some(false),
        "a view cannot refine an implementation's ownership requirement"
    );
}

#[test]
fn stable_view_refinement_does_not_confuse_disjoint_same_mode_inputs() {
    let base = Pointer {
        block: PointerBlock::Concrete("refinement:mixed".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local(
            "p",
            ProgramValue::typed_pointer(base.clone(), ProgramType::Int32Pointer),
        )
        .with_local(
            "q",
            ProgramValue::typed_pointer(base.offset_by_bytes(4), ProgramType::Int32Pointer),
        )
        .with_memory(Memory::new().with_block("refinement:mixed", 8));
    let segment = |name: &str| {
        MemorySegment::new(
            crate::kernel::program_expression::variable(name),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        )
    };
    let requirements = vec![
        ResourceSpec::viewed_memory(segment("p")),
        ResourceSpec::owned_memory(segment("q")),
    ];
    let target = program_function(
        ProgramType::Void,
        "mixed_target",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("q", ProgramType::Int32Pointer),
        ],
        ProgramStatement::Skip,
    )
    .with_resource_summary(requirements.clone(), Vec::new());
    let implementation = program_function(
        ProgramType::Void,
        "mixed_implementation",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("q", ProgramType::Int32Pointer),
        ],
        ProgramStatement::Skip,
    )
    .with_resource_summary(requirements, Vec::new());
    assert_eq!(
        checked_access_mode_refinement_adapter(
            target.contract_interface(),
            implementation.contract_interface(),
            &state,
            &state,
            &state,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .expect("same-mode refinement should be decided"),
        None,
        "a view of one cell and ownership of another need no variance adapter"
    );
}

#[test]
fn named_contract_application_discards_template_body_and_storage() {
    let body_variable = Variable(987_654);
    let pointer_parameter = program_parameter("p", ProgramType::UInt8Pointer);
    let body_with_load = ProgramStatement::Return(ProgramExpression::Load(Box::new(
        ProgramExpression::Variable("p".into()),
    )));
    let body_with_variable = ProgramStatement::Return(ProgramExpression::Value(
        ProgramValue::Int32(MachineTerm::Variable(body_variable)),
    ));
    let with_body_and_storage = program_function(
        ProgramType::Void,
        "callback_template",
        vec![pointer_parameter.clone()],
        body_with_load,
    )
    .with_string_literals(vec![StringLiteral::new("literal", b"x\0".to_vec())]);
    let with_different_body = program_function(
        ProgramType::Void,
        "callback_template",
        vec![pointer_parameter],
        body_with_variable,
    );
    let first = FunctionContract::new("BodyIndependent", with_body_and_storage).unwrap();
    let second = FunctionContract::new("BodyIndependent", with_different_body).unwrap();

    // The named-contract identity contains only the nominal name and the
    // interface. In particular, body/storage differences cannot become
    // callback identity or callback facts.
    assert_eq!(first, second);
    let environment = ExecutionEnvironment::new().with_function_contract(first.clone());
    let variables = crate::kernel::reasoning::execution_environment_variable_index(&environment);
    assert!(
        !variables.contains(&body_variable),
        "named-contract variable collection must not inspect its discarded body"
    );

    let argument = ProgramExpression::Value(ProgramValue::typed_pointer(
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramType::UInt8Pointer,
    ));
    // One caller state, so both applications start from one creation ledger.
    let caller = ExecutionState::new().with_population_creation_tracking();
    let run = |contract: &FunctionContract| {
        execute_program_function_contracts_paths(
            &caller,
            &[contract],
            std::slice::from_ref(&argument),
            &PureFactContext::new(),
            &ExecutionEnvironment::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
    };
    let first_paths = run(&first);
    let second_paths = run(&second);
    assert_eq!(first_paths, second_paths);
    assert!(matches!(
        first_paths[0].outcome,
        FunctionOutcome::Return { .. }
    ));
}

#[test]
fn resource_constructors_are_direct_only_and_part_of_identity() {
    let constructor = ResourceSpec::token(
        ResourceAccessMode::Own,
        "constructed_token".into(),
        vec![crate::kernel::program_expression::int32_literal(7)],
        vec![ProgramType::Int32],
    );
    let function = program_function(
        ProgramType::Void,
        "construct_token",
        vec![],
        program_return(program_void_value()),
    )
    .with_resource_constructors(vec![constructor]);
    // Generic construction would create members without population
    // authority, so it is refused; a member is created by folding it.
    let constructed = ResourceFact::own_token("constructed_token".into(), vec![int32(7)]);
    let refusal = construct_program_function_resource(
        &ExecutionState::new().with_population_creation_tracking(),
        &function,
        &[],
        &ProgramValue::Void,
        &constructed,
        &PureFactContext::new(),
    )
    .unwrap()
    .unwrap_err();
    assert_eq!(
        refusal,
        RuntimeError::FunctionContract(
            "generic resource construction cannot create members".into()
        )
    );

    // Named callback contracts cannot expose a zero-source transition that
    // their application engine does not perform. Direct outcome construction
    // remains supported, while formation and refinement fail closed.
    assert!(FunctionContract::new("ConstructCallback", function.clone()).is_none());
    let without_constructor = program_function(
        ProgramType::Void,
        "construct_token",
        vec![],
        program_return(program_void_value()),
    );
    let contract = FunctionContract::new("ConstructCallback", without_constructor.clone()).unwrap();
    assert!(!contract.exactly_matches(&function));
    assert!(!without_constructor.has_same_entry_and_source(&function));
}

fn direct_and_callback_resource_transition(
    function: &ProgramFunction,
    state: &ExecutionState,
    contract: &FunctionContract,
    environment: &ExecutionEnvironment,
) -> (ExecutionState, ExecutionState) {
    let direct_outcome = FunctionOutcome::Return {
        value: ProgramValue::Void.into(),
        state: Box::new(state.clone()),
    };
    let (direct_outcome, direct_obligations) = apply_program_function_contract_resource_transition(
        state,
        function,
        &[],
        direct_outcome,
        &PureFactContext::new(),
    )
    .expect("direct resource transition should check");
    assert!(direct_obligations.is_empty());
    let FunctionOutcome::Return {
        value: direct_value,
        state: direct_state,
    } = direct_outcome
    else {
        panic!("direct resource transition did not return");
    };
    assert_eq!(*direct_value.native(), ProgramValue::Void);

    let paths = execute_program_function_contracts_paths(
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
    let FunctionOutcome::Return {
        value: callback_value,
        state: callback_state,
    } = &paths[0].outcome
    else {
        panic!(
            "callback resource transition did not return: {:?}",
            paths[0].outcome
        );
    };
    assert_eq!(callback_value.native().as_ref(), &ProgramValue::Void);
    assert_eq!(direct_state.memory(), callback_state.memory());
    assert_eq!(
        direct_state.observed_population_families,
        callback_state.observed_population_families
    );
    (*direct_state, *callback_state.clone())
}

#[test]
fn direct_and_named_callback_resource_interfaces_agree_across_families() {
    let memory_pointer = Pointer {
        block: "parity-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory_spec = ResourceSpec::owned_memory(MemorySegment::new(
        crate::kernel::program_expression::pointer_value(memory_pointer.clone()),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    ));
    let memory_function = program_function(
        ProgramType::Void,
        "parity_memory",
        vec![],
        ProgramStatement::Skip,
    )
    .with_resource_summary(vec![memory_spec.clone()], vec![memory_spec]);
    let memory_state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(Memory::new().with_block(memory_pointer.block.clone(), 4))
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(
                memory_pointer,
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            )),
        ));
    let memory_contract = FunctionContract::new("ParityMemory", memory_function.clone()).unwrap();
    let (direct, callback) = direct_and_callback_resource_transition(
        &memory_function,
        &memory_state,
        &memory_contract,
        &ExecutionEnvironment::new(),
    );
    assert_eq!(direct.resources(), callback.resources());

    let token_spec = ResourceSpec::token(
        ResourceAccessMode::Own,
        "parity_token".into(),
        vec![crate::kernel::program_expression::int32_literal(7)],
        vec![ProgramType::Int32],
    );
    let token_function = program_function(
        ProgramType::Void,
        "parity_token",
        vec![],
        ProgramStatement::Skip,
    )
    .with_resource_summary(vec![token_spec.clone()], vec![token_spec])
    .with_ordinary_abstract_families(vec!["parity_token".into()]);
    let token_state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_token("parity_token".into(), vec![int32(7)]),
        ));
    let token_contract = FunctionContract::new("ParityToken", token_function.clone()).unwrap();
    let (direct, callback) = direct_and_callback_resource_transition(
        &token_function,
        &token_state,
        &token_contract,
        &ExecutionEnvironment::new(),
    );
    assert_eq!(direct.resources(), callback.resources());

    let composite_spec = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "parity_composite".into(),
        vec![crate::kernel::program_expression::int32_literal(11)],
        vec![ProgramType::Int32],
    );
    let composite_function = program_function(
        ProgramType::Void,
        "parity_composite",
        vec![],
        ProgramStatement::Skip,
    )
    .with_resource_summary(vec![composite_spec.clone()], vec![composite_spec])
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
        "parity_composite",
        vec![program_parameter("value", ProgramType::Int32)],
        None,
        true,
        vec![],
        vec![],
    )]);
    let composite_state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_composite("parity_composite".into(), vec![int32(11)]),
        ));
    let composite_contract =
        FunctionContract::new("ParityComposite", composite_function.clone()).unwrap();
    let (direct, callback) = direct_and_callback_resource_transition(
        &composite_function,
        &composite_state,
        &composite_contract,
        &ExecutionEnvironment::new(),
    );
    assert_eq!(direct.resources(), callback.resources());

    let schema = ResourceFieldSchema::new(vec![(
        "value".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let identity = Variable(700);
    let instance_resource = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "parity_instance".into(),
        vec![crate::kernel::program_expression::int32_literal(13)],
        vec![ProgramType::Int32],
    );
    let instance_spec = ResourceSpec::instance(
        identity,
        "item".into(),
        schema.clone(),
        instance_resource,
        ResourceTransferRole::Consume,
        ResourceStateSource::Current,
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
    let instance_function = program_function(
        ProgramType::Void,
        "parity_instance",
        vec![],
        ProgramStatement::Skip,
    )
    .with_resource_summary(vec![instance_spec.clone()], vec![instance_spec.clone()])
    .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
        "parity_instance",
        vec![program_parameter("value", ProgramType::Int32)],
        None,
        false,
        vec![],
        vec![],
    )]);
    let instance_state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_resource_context(
            ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance))),
        );
    let instance_contract = FunctionContract::new("ParityInstance", instance_function.clone())
        .unwrap()
        .with_proof_parameters(vec![instance_spec]);
    let instance_environment = ExecutionEnvironment::new()
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
    check_executed_refinement_shape(ProgramType::Void, false);
}

#[test]
fn executed_refinement_requires_forwarding_the_exact_typed_call_result() {
    for return_type in [
        ProgramType::Int32,
        ProgramType::Int64,
        ProgramType::Int32Pointer,
    ] {
        check_executed_refinement_shape(return_type, false);
        check_executed_refinement_shape(return_type, true);
    }
}

fn check_executed_refinement_shape(return_type: ProgramType, alter_result: bool) {
    let template = program_function(
        return_type,
        "interface",
        vec![program_parameter("x", ProgramType::Int32)],
        ProgramStatement::Skip,
    )
    .with_contract(vec![], vec![], vec![], vec![], true);
    let source = FunctionContract::new("Source", template.clone()).unwrap();
    let target = FunctionContract::new("Target", template.clone()).unwrap();
    let pointer_type = source.function_pointer_type();
    let premise = SpecProposition::Predicate {
        resource_state_dependent: false,
        name: source.predicate_name(),
        arguments: vec![SpecPredicateArgument::Value(
            SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "callback",
            )),
        )],
    };
    let conclusion = Proposition::Predicate {
        name: target.predicate_name(),
        arguments: vec![
            Term::ExecutionState(Box::new(ExecutionState::new())),
            Term::ProgramValue(ProgramValue::Pointer(PointerValue::new(
                Pointer {
                    block: PointerBlock::FunctionSymbolic(Variable(0)),
                    offset: PointerOffsetTerm::Constant(0),
                },
                pointer_type,
            ))),
        ],
    };
    let environment = ExecutionEnvironment::new()
        .with_function_contract(source)
        .with_function_contract(target);
    // Isolate the implication boundary: its input is an already trusted rule.
    // Ordinary execution certification is covered by the mdtests.
    for (callee, argument, sources, extra_premise, valid) in [
        (
            "callback",
            crate::kernel::program_expression::variable("x"),
            vec!["Source"],
            false,
            true,
        ),
        (
            "other",
            crate::kernel::program_expression::variable("x"),
            vec!["Source"],
            false,
            false,
        ),
        (
            "callback",
            crate::kernel::program_expression::int32_literal(1),
            vec!["Source"],
            false,
            false,
        ),
        (
            "callback",
            crate::kernel::program_expression::variable("x"),
            vec!["Target"],
            false,
            false,
        ),
        (
            "callback",
            crate::kernel::program_expression::variable("x"),
            vec![],
            false,
            false,
        ),
        (
            "callback",
            crate::kernel::program_expression::variable("x"),
            vec!["Source"],
            true,
            false,
        ),
    ] {
        let mut requirements = vec![premise.clone()];
        if extra_premise {
            requirements.insert(0, premise.clone());
        }
        let function = program_function(
            return_type,
            "wrapper",
            vec![
                program_parameter("x", ProgramType::Int32),
                program_parameter("callback", pointer_type),
            ],
            if return_type == ProgramType::Void {
                ProgramStatement::Call {
                    function_name: callee.to_string(),
                    arguments: vec![argument],
                    callee: None,
                }
            } else {
                let (call, result) = program_call_value(0, callee, vec![argument]);
                program_seq(
                    call,
                    program_return(if alter_result {
                        crate::kernel::program_expression::int32_literal(0)
                    } else {
                        result
                    }),
                )
            },
        )
        .with_contract(requirements, vec![], vec![], vec![], true);
        assert_eq!(
            crate::kernel::prove_executed_contract_refinement(
                &environment,
                &sources
                    .iter()
                    .map(|source| (*source, Vec::new()))
                    .collect::<Vec<_>>(),
                "Target",
                conclusion.clone(),
                &VerifiedFunctionRule {
                    pointer_result: None,
                    function,
                    loop_semantics: LoopSemantics::Verify,
                    checked_callees: None,
                    applied_tactics: Default::default(),
                },
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
            (0..count).map(|index| ResourceFact::own_token(format!("token{index}"), vec![])),
        );
        assert!(resources.storage.materialized.get().is_none());
        let state = ExecutionState::new().with_resource_context(resources.clone());
        let transfer = prepare_contract_resource_transfer(
            &state,
            &ExecutionState::new(),
            contract.name(),
            contract.interface(),
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
            false,
            ResourceTransitionPurpose::FunctionBoundary,
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
fn resource_derived_refinement_compares_checked_ranges() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:resource-refinement:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(pointer.clone()))
        .with_memory(Memory::new().with_block(pointer.block.clone(), 8));
    let resource = |start| {
        ResourceSpec::owned_memory(MemorySegment::new(
            ProgramExpression::Variable("p".into()),
            ProgramExpression::Value(int32(start)),
            ProgramExpression::Value(int32(start + 1)),
        ))
    };
    let target = program_function(
        ProgramType::Void,
        "resource_target",
        vec![],
        ProgramStatement::Skip,
    )
    .with_contract(vec![], vec![], vec![], vec![], true)
    .with_resource_summary(vec![resource(0)], vec![])
    .with_resource_derived_mutable_frame();
    let implementation = program_function(
        ProgramType::Void,
        "resource_implementation",
        vec![],
        ProgramStatement::Skip,
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
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(pointer.clone()))
        .with_memory(Memory::new().with_block(pointer.block.clone(), 4));
    let function = program_function(
        ProgramType::Void,
        "mixed_resource_frame",
        vec![],
        ProgramStatement::Skip,
    )
    .with_contract(
        vec![],
        vec![],
        vec![
            MemorySegment::new(
                ProgramExpression::Variable("p".into()),
                ProgramExpression::Value(int32(0)),
                ProgramExpression::Value(int32(1)),
            ),
            MemorySegment::new(
                ProgramExpression::Variable("p".into()),
                ProgramExpression::Value(int32(2)),
                ProgramExpression::Value(int32(3)),
            ),
        ],
        vec![],
        true,
    )
    .with_resource_summary(
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            ProgramExpression::Variable("p".into()),
            ProgramExpression::Value(int32(0)),
            ProgramExpression::Value(int32(1)),
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
    let definition = CompositeResourceDefinition::new(
        "LoopWrapper",
        vec![program_parameter("data", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            ProgramExpression::Variable("data".into()),
            ProgramExpression::Value(int32(0)),
            ProgramExpression::Value(int32(1)),
        ))],
        vec![],
    );
    let requirement = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "LoopWrapper".into(),
        vec![ProgramExpression::Variable("p".into())],
        vec![ProgramType::Int32Pointer],
    );
    let wrong_loop_frame = LoopEffectCheck::new_with_origin(
        LoopEffect::Mutable(vec![MemorySegment::new(
            ProgramExpression::Variable("p".into()),
            ProgramExpression::Value(int32(1)),
            ProgramExpression::Value(int32(2)),
        )]),
        LoopEffectSpan::Whole,
        LoopEffectOrigin::InheritedResourceDerived,
        Some("loop 0 inherited owned resource frame".into()),
    );
    let body = ProgramStatement::While {
        condition: crate::kernel::program_expression::int32_literal(0),
        invariant: vec![],
        invariant_checks: vec![],
        effect_checks: vec![wrong_loop_frame],
        resource_specs: vec![],
        ranking_measures: vec![],
        structural_measure: None,
        do_while: false,
        backedge_target: None,
        natural_exit_target: None,
        body: Box::new(ProgramStatement::Skip),
    };
    let function = program_function(
        ProgramType::Void,
        "wrong_loop_wrapper_frame",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        body,
    )
    .with_contract(vec![], vec![], vec![], vec![], true)
    .with_resource_summary(vec![requirement], vec![])
    .with_composite_resource_definitions(vec![definition])
    .with_resource_derived_mutable_frame();
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(pointer.clone()))
        .with_memory(Memory::new().with_block(pointer.block, 4));
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
fn declared_loop_frame_is_installed_from_the_loop_specs_not_from_segments() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:loop-declared:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let definition = CompositeResourceDefinition::new(
        "LoopWrapper",
        vec![program_parameter("data", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            ProgramExpression::Variable("data".into()),
            ProgramExpression::Value(int32(0)),
            ProgramExpression::Value(int32(1)),
        ))],
        vec![],
    );
    let spec = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "LoopWrapper".into(),
        vec![ProgramExpression::Variable("p".into())],
        vec![ProgramType::Int32Pointer],
    );
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(pointer.clone()))
        .with_memory(Memory::new().with_block(pointer.block.clone(), 4))
        .with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own_composite(
                "LoopWrapper".into(),
                vec![ProgramValue::pointer(pointer.clone())],
            ),
        ));
    // The surface lowers no segments for a declared frame; a stale or
    // hostile segment list here must be ignored either way.
    let declared = LoopEffectCheck::new_with_origin(
        LoopEffect::Mutable(vec![MemorySegment::new(
            ProgramExpression::Variable("p".into()),
            ProgramExpression::Value(int32(5)),
            ProgramExpression::Value(int32(9)),
        )]),
        LoopEffectSpan::Whole,
        LoopEffectOrigin::DeclaredResource,
        Some("loop 0 declared owned resource frame".into()),
    );
    let assumptions = PureFactContext::new();
    let head = |definitions: &[CompositeResourceDefinition]| {
        let mut budget = ExecutionBudget::default();
        let mut variables = KernelVariableGenerator::fresh_for_execution(BTreeSet::new());
        crate::kernel::loops::prepare_loop_top_state(
            &state,
            std::slice::from_ref(&declared),
            &[],
            std::slice::from_ref(&spec),
            definitions,
            &ProgramStatement::Skip,
            &assumptions,
            &mut budget,
            &mut variables,
        )
        .unwrap()
    };

    // With the loop's spec, the frame is the composite's expanded memory,
    // read from the kernel's evaluation of that spec: not the segments.
    let installed = head(std::slice::from_ref(&definition));
    assert!(installed.resource_failures.is_empty());
    let ranges = installed.effect_checks[0]
        .validated_ranges()
        .expect("a declared frame is installed at loop entry");
    assert_eq!(ranges.len(), 1);
    assert_eq!(ranges[0].base(), &pointer);
    assert_eq!(ranges[0].start(), &MachineTerm::constant(0));
    assert_eq!(ranges[0].end(), &MachineTerm::constant(1));

    // When the kernel cannot read the spec (no definition to expand it
    // through), the frame stays uninstalled and the back edge refuses it;
    // the segments are never a fallback. A spec the entering context holds
    // no resource for is installed from its denotation, exactly as before,
    // and the loop's declaration failure is the verdict for that case.
    let bare = head(&[]);
    assert!(bare.effect_checks[0].validated_ranges().is_none());
    let obligations = crate::kernel::loops::collect_loop_effect_check_obligations(
        &state,
        &state,
        &bare.effect_checks,
        &[],
        &[],
        &assumptions,
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(
        !obligations.is_empty(),
        "an uninstalled declared frame must be refused"
    );
}

#[test]
fn resource_derived_loop_setup_does_not_fallback_to_surface_metadata() {
    let pointer = Pointer {
        block: PointerBlock::Concrete("local:loop-fallback:data".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let source_segment = MemorySegment::new(
        ProgramExpression::Variable("p".into()),
        ProgramExpression::Value(int32(0)),
        ProgramExpression::Value(int32(1)),
    );
    let token = ResourceSpec::declared(
        ResourceFamily::Token,
        ResourceAccessMode::Own,
        "slot".into(),
        vec![],
        vec![],
        ResourceTransferRole::Consume,
        ResourceStateSource::Current,
    )
    .unwrap();
    let quantity = ResourceSpec::quantified(
        ProgramExpression::Variable("missing_quantity".into()),
        token,
        ResourceTransferRole::Consume,
        ResourceStateSource::Current,
    )
    .unwrap();
    let inherited = LoopEffectCheck::new_with_origin(
        LoopEffect::Mutable(vec![source_segment.clone()]),
        LoopEffectSpan::Whole,
        LoopEffectOrigin::InheritedResourceDerived,
        Some("loop 0 inherited owned resource frame".into()),
    );
    let function = program_function(
        ProgramType::Void,
        "reject_loop_surface_fallback",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        ProgramStatement::While {
            condition: crate::kernel::program_expression::int32_literal(0),
            invariant: vec![],
            invariant_checks: vec![],
            effect_checks: vec![inherited],
            resource_specs: vec![],
            ranking_measures: vec![],
            structural_measure: None,
            do_while: false,
            backedge_target: None,
            natural_exit_target: None,
            body: Box::new(ProgramStatement::Skip),
        },
    )
    .with_contract(vec![], vec![], vec![], vec![], true)
    .with_resource_summary(vec![quantity], vec![])
    .with_resource_derived_mutable_frame();
    let state = ExecutionState::new()
        .with_local("p", ProgramValue::pointer(pointer.clone()))
        .with_memory(Memory::new().with_block(pointer.block, 4));
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
    let function = program_function(
        ProgramType::Int32,
        "requires_positive",
        vec![program_parameter("x", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "x",
            )),
            operator: ComparisonOperator::GreaterThan,
            right: SpecExpression::Value(int32(0)),
        }],
        vec![],
        vec![],
        vec![],
        true,
    );
    let contract = FunctionContract::new("RequiresPositive", function).unwrap();
    let arguments = vec![crate::kernel::program_expression::int32_literal(0)];
    let first_state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(Memory::new().with_block("first", 4));
    let second_state = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(Memory::new().with_block("second", 4));
    let run = |state: &ExecutionState| {
        execute_program_function_contracts_paths(
            state,
            &[&contract],
            &arguments,
            &PureFactContext::new(),
            &ExecutionEnvironment::new(),
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
        first_site.source_memory_state,
        MemoryStateIdentity::of(first_state.memory())
    );
    assert_eq!(
        second_site.source_memory_state,
        MemoryStateIdentity::of(second_state.memory())
    );
    assert_ne!(
        first_site.source_memory_state, second_site.source_memory_state,
        "same callee and arguments must remain separated by source state identity"
    );
}

#[test]
fn selected_contract_and_requirement_ordinals_stay_with_their_call() {
    let template = program_function(
        ProgramType::Int32,
        "same_target",
        vec![program_parameter("x", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        vec![
            SpecProposition::Predicate {
                resource_state_dependent: true,
                name: "first_requirement".to_string(),
                arguments: vec![],
            },
            SpecProposition::Predicate {
                resource_state_dependent: true,
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
    let first = FunctionContract::new("FirstInterface", template.clone()).unwrap();
    let second = FunctionContract::new("SecondInterface", template).unwrap();
    let paths = execute_program_function_contracts_paths(
        &ExecutionState::new(),
        &[&first, &second],
        &[crate::kernel::program_expression::int32_literal(0)],
        &PureFactContext::new(),
        &ExecutionEnvironment::new().with_selected_call_contract("SecondInterface"),
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
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "x",
            )),
            operator: ComparisonOperator::GreaterThan,
            right: SpecExpression::Value(int32(100)),
        }),
        Box::new(SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "x",
            )),
            operator: ComparisonOperator::LessThan,
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
            base: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "p",
            )),
            start: SpecExpression::Value(int32(0)),
            end: SpecExpression::Value(int32(1)),
            element_width: 4,
        }),
    };
    let function = program_function(
        ProgramType::Int32,
        "capability_source",
        vec![
            program_parameter("p", ProgramType::Int32Pointer),
            program_parameter("x", ProgramType::Int32),
        ],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        vec![pure_disjunction, stateful_exists],
        vec![],
        vec![],
        vec![],
        true,
    )
    .with_contract_requirement_sources(vec![Some(0), Some(1)]);
    let contract = FunctionContract::new("CapabilitySource", function).unwrap();
    let paths = execute_program_function_contracts_paths(
        &ExecutionState::new().with_population_creation_tracking(),
        &[&contract],
        &[
            crate::kernel::program_expression::typed_pointer_value(
                Pointer::symbolic(Variable(901)),
                ProgramType::Int32Pointer,
            ),
            crate::kernel::program_expression::int32_literal(7),
        ],
        &PureFactContext::new(),
        &ExecutionEnvironment::new(),
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
        &Memory::new(),
    ));
    let source = CallRequirementSource::new(site, 0, None, true, None);
    assert!(!source.source_requirement_is_state_independent);
}

#[test]
fn calls_without_unresolved_requirements_do_not_construct_call_site_metadata() {
    let function = program_function(
        ProgramType::Int32,
        "established",
        vec![program_parameter("x", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::variable("x")),
    )
    .with_contract(vec![], vec![], vec![], vec![], true);
    let contract = FunctionContract::new("Established", function).unwrap();

    CallRequirementSite::reset_test_construction_count();
    let paths = execute_program_function_contracts_paths(
        &ExecutionState::new().with_population_creation_tracking(),
        &[&contract],
        &[crate::kernel::program_expression::int32_literal(7)],
        &PureFactContext::new(),
        &ExecutionEnvironment::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();

    assert!(matches!(paths[0].outcome, FunctionOutcome::Return { .. }));
    assert_eq!(
        CallRequirementSite::test_construction_count(),
        0,
        "established calls must not construct or intern carrier metadata"
    );
}

#[test]
fn missing_contract_requirement_source_map_fails_closed() {
    let function = program_function(
        ProgramType::Int32,
        "missing_map",
        vec![program_parameter("x", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        vec![SpecProposition::Predicate {
            resource_state_dependent: true,
            name: "requirement".to_string(),
            arguments: vec![],
        }],
        vec![],
        vec![],
        vec![],
        true,
    )
    .without_test_contract_requirement_sources();
    let contract = FunctionContract::new("MissingMap", function).unwrap();
    let paths = execute_program_function_contracts_paths(
        &ExecutionState::new(),
        &[&contract],
        &[crate::kernel::program_expression::int32_literal(0)],
        &PureFactContext::new(),
        &ExecutionEnvironment::new(),
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert!(matches!(
        paths[0].outcome,
        FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(ref message))
            if message.contains("source map")
    ));
    assert!(paths[0].obligations.is_empty());
}

#[test]
fn contract_source_maps_do_not_change_function_semantic_identity() {
    let requirements = vec![SpecProposition::Predicate {
        resource_state_dependent: true,
        name: "requirement".to_string(),
        arguments: vec![],
    }];
    let base = program_function(
        ProgramType::Int32,
        "same_identity",
        vec![],
        program_return(crate::kernel::program_expression::int32_literal(0)),
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
fn call_state_identity_work_does_not_scale_with_unrelated_memory() {
    let small = Memory::new();
    let large = (0..256).fold(Memory::new(), |memory, index| {
        memory.with_block(format!("unrelated{index}"), 4)
    });
    let (_, small_work) =
        crate::instrumentation::measure_deterministic_work(|| MemoryStateIdentity::of(&small));
    let (_, large_work) =
        crate::instrumentation::measure_deterministic_work(|| MemoryStateIdentity::of(&large));
    assert_eq!(
        small_work, large_work,
        "state identity must not scan unrelated memory"
    );
}

#[test]
fn empty_requirement_lowering_retains_selected_call_source() {
    let function = program_function(
        ProgramType::Int32,
        "empty_requirement_path",
        vec![],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                "missing",
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        vec![],
        vec![],
        vec![],
        true,
    );
    let contract = FunctionContract::new("EmptyRequirement", function).unwrap();
    let paths = execute_program_function_contracts_paths(
        &ExecutionState::new().with_population_creation_tracking(),
        &[&contract],
        &[],
        &PureFactContext::new(),
        &ExecutionEnvironment::new(),
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
fn source_load_state_collection_is_iterative_and_bounded() {
    let leaf = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    // The condition node is visited in addition to the proposition nodes.
    let within_limit = (0..4094).fold(leaf.clone(), |body, _| Proposition::Not(Box::new(body)));
    assert!(
        source_load_state_for_proposition(&within_limit)
            .expect("the bounded collector should handle deep logical structure")
            .is_none()
    );
    let over_limit = Proposition::Not(Box::new(within_limit));
    assert_eq!(
        source_load_state_for_proposition(&over_limit),
        Err(ExecutionLimit::ExpressionSteps),
        "metadata collection must propagate structural exhaustion"
    );
}

fn interface(index: usize) -> FunctionContract {
    let function = program_function(
        ProgramType::Int32,
        format!("Bound{index}"),
        vec![program_parameter("value", ProgramType::Int32)],
        program_return(crate::kernel::program_expression::int32_literal(0)),
    )
    .with_contract(
        vec![],
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable(
                C_CONTRACT_RESULT_NAME,
            )),
            operator: ComparisonOperator::GreaterEqual,
            right: SpecExpression::Value(int32((-(index as i32)) as u32)),
        }],
        vec![],
        vec![],
        true,
    );
    FunctionContract::new(format!("Bound{index}"), function).unwrap()
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
            ExecutionEnvironment::new().with_selected_call_contract(&format!("Bound{}", count - 1))
        } else {
            ExecutionEnvironment::new()
        };
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            execute_program_function_contracts_paths(
                &ExecutionState::new().with_population_creation_tracking(),
                &contracts,
                &[crate::kernel::program_expression::int32_literal(7)],
                &PureFactContext::new(),
                &environment,
                &mut budget,
            )
            .unwrap()
        });
        assert_eq!(paths.len(), 1);
        assert!(matches!(paths[0].outcome, FunctionOutcome::Return { .. }));
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

fn check_unrelated_functions(select: bool) {
    let contracts = [interface(0), interface(1)];
    let contracts = contracts.iter().collect::<Vec<_>>();
    let mut samples = Vec::new();
    for count in [0, 16, 64, 256] {
        // Keep term-bridge imports cold at every sample size.
        crate::kernel::clear_integer_bridge_memo();
        let mut environment = ExecutionEnvironment::new();
        for index in 0..count {
            environment = environment.with_function(program_function(
                ProgramType::Int32,
                format!("unrelated{index}"),
                vec![],
                program_return(crate::kernel::program_expression::int32_literal(0)),
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
            execute_program_function_contracts_paths(
                &ExecutionState::new().with_population_creation_tracking(),
                &contracts,
                &[crate::kernel::program_expression::int32_literal(7)],
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

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/functions/callback_contract_tests.rs");
}
