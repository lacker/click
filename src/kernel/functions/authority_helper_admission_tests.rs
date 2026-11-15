use super::*;

#[test]
fn quantity_exchange_net_certification_scales_beside_unrelated_populations() {
    let samples = [(2, 16), (64, 64), (65536, 256)].map(|(amount, unrelated)| {
        let pointer = ProgramValue::typed_pointer(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            ProgramType::Int32Pointer,
        );
        let description = ResourceDescription::new(
            "member".into(),
            vec![pointer.clone().into()].into(),
            ResourceFieldSchema::new(vec![]).unwrap(),
        );
        let authority = ResourceFact::own(Resource::PopulationAuthority(description.clone()));
        let resource = Resource::Composite {
            name: "member".into(),
            arguments: vec![pointer.clone().into()].into(),
        };
        let member = ResourceFact::own_quantity(resource, MachineTerm::constant(amount));
        let mut entry = ExecutionState::new()
            .with_population_creation_tracking()
            .with_local("p", pointer)
            .with_resource_context(
                ResourceContext::new().unchecked_with_facts([authority.clone(), member.clone()]),
            )
            .import_opaque_population_quantity(&authority, &member)
            .unwrap();
        for index in 1..=unrelated {
            let other = ResourceDescription::new(
                "unrelated".into(),
                vec![
                    ProgramValue::pointer(Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: PointerOffsetTerm::Variable(Variable(950_000 + index as u64)),
                    })
                    .into(),
                ]
                .into(),
                ResourceFieldSchema::new(vec![]).unwrap(),
            );
            let authority = ResourceFact::own(Resource::PopulationAuthority(other));
            entry = entry
                .clone()
                .with_resource_context(
                    entry
                        .resources()
                        .clone()
                        .unchecked_with_fact(authority.clone()),
                )
                .import_opaque_population(&authority, 0)
                .unwrap();
        }
        let member_spec = ResourceSpec::composite(
            ResourceAccessMode::Own,
            "member".into(),
            vec![crate::kernel::program_expression::variable("p")],
            vec![ProgramType::Int32Pointer],
        );
        let authority_spec = ResourceSpec::new(
            ResourceTerm::PopulationAuthority {
                protected: Box::new(ResourceTypeSpec {
                    resource: Box::new(member_spec.clone()),
                    schema: ResourceFieldSchema::new(vec![]).unwrap(),
                }),
                population_arity: None,
                state_source: ResourceStateSource::Current,
            },
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        )
        .unwrap();
        let consumed = ResourceSpec::new(
            member_spec.term().clone(),
            ResourceAccessMode::Own,
            ResourceQuantity::Count(crate::kernel::program_expression::int32_literal(amount)),
            ResourceTransferRole::Consume,
            ResourceStateSource::Entry,
        )
        .unwrap();
        let produced = ResourceSpec::new(
            member_spec.term().clone(),
            ResourceAccessMode::Own,
            ResourceQuantity::Count(crate::kernel::program_expression::int32_literal(amount - 1)),
            ResourceTransferRole::Produce,
            ResourceStateSource::Post,
        )
        .unwrap();
        let function = program_function(
            ProgramType::Void,
            "shrink",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            program_return(program_void_value()),
        )
        .with_resource_summary(
            vec![authority_spec.clone(), consumed],
            vec![authority_spec, produced],
        )
        .with_composite_resource_definitions(vec![CompositeResourceDefinition::new(
            "member",
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            None,
            false,
            vec![],
            vec![],
        )]);
        assert!(authority_supports_resource_contract(
            function.contract_interface()
        ));
        assert!(!authority_preserves_assumed_resource_contract(
            function.contract_interface()
        ));
        let events = entry.population_effects.creation.as_ref().unwrap();
        let count = events.observe_symbolic(&description).unwrap().entry_count;
        let assumptions = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_greater_equal(count.clone(), MachineTerm::constant(amount)),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    count,
                    MachineTerm::constant((i32::MAX - 1) as u32),
                ),
                true,
            );
        let (exit, work) = crate::persistent::measure_persistent_work(|| {
            let spent = events
                .checked_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    &description,
                    false,
                    &MachineTerm::constant(amount),
                    &assumptions,
                )
                .unwrap()
                .0;
            let returned = spent
                .checked_member_exchange_quantity(
                    &PointerBlock::ExternalArgument,
                    &description,
                    true,
                    &MachineTerm::constant(amount - 1),
                    &assumptions,
                )
                .unwrap()
                .0;
            let mut exit = entry.clone();
            Arc::make_mut(&mut exit.population_effects).creation = Some(returned);
            check_quantity_exchange_at_return(
                &entry,
                &exit,
                function.contract_interface(),
                &assumptions,
                &mut ExecutionBudget::beside_live_state(),
            )
            .unwrap()
            .unwrap();
            exit
        });
        assert_eq!(
            exit.population_effects
                .creation
                .as_ref()
                .unwrap()
                .observe_symbolic(&description)
                .unwrap()
                .delta,
            -1
        );
        assert!(
            check_quantity_exchange_at_return(
                &entry,
                &entry,
                function.contract_interface(),
                &assumptions,
                &mut ExecutionBudget::beside_live_state()
            )
            .unwrap()
            .is_err(),
            "an unchanged ledger cannot certify the claimed decrement"
        );
        work
    });
    assert!(samples[0] > 0, "{samples:?}");
    // Each sample quadruples the indexed population count. Permit bounded
    // tree-path growth while excluding work proportional to either the
    // unrelated population count or the exchanged quantity.
    for (index, work) in samples.iter().enumerate() {
        assert!(*work <= samples[0] + 96 * index, "{samples:?}");
    }
}

#[test]
fn contained_transfer_frontier_scales_with_selected_depth_and_indexed_definitions() {
    let pointer = Pointer {
        block: "payload".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new().with_block("payload", 4);
    let assumptions = PureFactContext::new();
    let root =
        ResourceFact::own_composite("wrapper-0000".into(), vec![ProgramValue::pointer(pointer)]);
    let definition = |name: String, next: Option<String>| {
        CompositeResourceDefinition::new(
            name,
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            None,
            false,
            next.into_iter()
                .map(|next| {
                    ResourceSpec::composite(
                        ResourceAccessMode::Own,
                        next,
                        vec![crate::kernel::program_expression::variable("p")],
                        vec![ProgramType::Int32Pointer],
                    )
                })
                .collect(),
            vec![],
        )
    };
    let sample = |depth, unrelated| {
        let mut definitions = (0..depth)
            .map(|index| {
                definition(
                    format!("wrapper-{index:04}"),
                    if index + 1 == depth {
                        None
                    } else {
                        Some(format!("wrapper-{:04}", index + 1))
                    },
                )
            })
            .chain((0..unrelated).map(|index| definition(format!("unrelated-{index:04}"), None)))
            .collect::<Vec<_>>();
        definitions.sort_by(|a, b| a.name().cmp(b.name()));
        let (frontier, work) = crate::instrumentation::measure_deterministic_work(|| {
            population_transfer_frontier(
                std::iter::once(&root),
                &definitions,
                &memory,
                &assumptions,
            )
            .unwrap()
        });
        assert_eq!(frontier.len(), depth);
        work
    };
    let depths = [sample(16, 512), sample(32, 512), sample(64, 512)];
    for pair in depths.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3 + 32,
            "contained transfer rescans ancestors: {depths:?}"
        );
    }
    let frames = [sample(16, 16), sample(16, 64), sample(16, 256)];
    for pair in frames.windows(2) {
        assert!(
            pair[1] <= pair[0] * 2 + 32,
            "contained transfer scans unrelated definitions: {frames:?}"
        );
    }
    let recursive = vec![definition(
        "wrapper-0000".into(),
        Some("wrapper-0000".into()),
    )];
    assert!(
        population_transfer_frontier(std::iter::once(&root), &recursive, &memory, &assumptions)
            .is_err()
    );
}

#[test]
fn boundary_receipt_rejects_other_callers_functions_and_arguments() {
    let caller = ExecutionState::new().with_local("kept", int32(7));
    let function = Arc::new(program_function(
        ProgramType::Void,
        "entry_receipt",
        vec![program_parameter("value", ProgramType::Int32)],
        ProgramStatement::Skip,
    ));
    let arguments = vec![ProgramExpression::Value(int32(3))];
    let receipt = capture_checked_boundary_resource_transfer(
        &caller,
        function.clone(),
        &arguments,
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    assert!(receipt.matches(&caller, &function, &arguments));
    assert_eq!(receipt, receipt.clone());
    let recaptured = capture_checked_boundary_resource_transfer(
        &caller,
        function.clone(),
        &arguments,
        &PureFactContext::new(),
        &mut ExecutionBudget::beside_live_state(),
    )
    .unwrap()
    .unwrap();
    assert_ne!(receipt, recaptured);
    let other_function = function.as_ref().clone();
    let other_caller = caller.clone().with_local("kept", int32(8));
    let other_arguments = vec![ProgramExpression::Value(int32(4))];
    for (candidate_caller, candidate_function, candidate_arguments) in [
        (&other_caller, function.as_ref(), arguments.as_slice()),
        (&caller, &other_function, arguments.as_slice()),
        (&caller, function.as_ref(), other_arguments.as_slice()),
    ] {
        let result = contract_exit_outcome_with_boundary_transfer(
            candidate_caller,
            candidate_function,
            candidate_arguments,
            StatementOutcome::Normal(Box::new(caller.clone())),
            Vec::new(),
            &PureFactContext::new(),
            &mut ExecutionBudget::beside_live_state(),
            ResourceTransitionPurpose::FunctionBoundary,
            Some(&receipt),
        )
        .unwrap();
        assert!(
            matches!(result, Err(RuntimeError::FunctionContract(message))
                if message == "function boundary resource receipt belongs to another entry")
        );
        let deferred = resolve_deferred_contract_exit(
            candidate_caller,
            candidate_function,
            candidate_arguments,
            &FunctionOutcome::Return {
                value: int32(0).into(),
                state: Box::new(caller.clone()),
            },
            Some(&receipt),
            &PureFactContext::new(),
            &mut ExecutionBudget::beside_live_state(),
        )
        .unwrap();
        assert!(
            matches!(deferred, Err(RuntimeError::FunctionContract(message))
                if message == "function boundary resource receipt belongs to another entry")
        );
    }
}

#[test]
fn authority_helper_rejects_resource_constructors() {
    let mut interface = FunctionContractInterface::new(ProgramType::Int32, Vec::new());
    interface.resource_constructors = vec![ResourceSpec::owned_memory(MemorySegment::new(
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    ))];
    assert!(!authority_preserves_resource_contract(&interface));
}
#[test]
fn assumed_authority_contracts_preserve_named_identity_without_lifecycle_rights() {
    assert!(!authority_preserves_assumed_resource_contract(
        &FunctionContractInterface::new(ProgramType::Void, Vec::new())
    ));
    let mut interface = companion_interface("reference");
    interface
        .resource_requires
        .retain(|spec| spec.family() == ResourceFamily::PopulationAuthority);
    interface
        .resource_ensures
        .retain(|spec| spec.family() == ResourceFamily::PopulationAuthority);
    let identity = Variable::allocate_fresh().unwrap();
    let schema = ResourceFieldSchema::new(vec![(
        "serial".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let member = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "ticket".into(),
        vec![crate::kernel::program_expression::variable("p")],
        vec![ProgramType::Int32Pointer],
    );
    let named = ResourceSpec::instance(
        identity,
        "member".into(),
        schema.clone(),
        member.clone(),
        ResourceTransferRole::Borrow,
        ResourceStateSource::Current,
    )
    .unwrap();
    interface.resource_requires.push(named.clone());
    interface.resource_ensures.push(named);
    assert!(authority_preserves_assumed_resource_contract(&interface));
    let mut logical = interface.clone();
    logical
        .resource_requires
        .retain(|spec| spec.family() == ResourceFamily::Instance);
    logical
        .resource_ensures
        .retain(|spec| spec.family() == ResourceFamily::Instance);
    assert!(
        authority_preserves_assumed_resource_contract(&logical),
        "ordinary named models do not need artificial population authority"
    );
    for role in [ResourceTransferRole::Consume, ResourceTransferRole::Produce] {
        let mut changed = interface.clone();
        if role == ResourceTransferRole::Consume {
            let last = changed.resource_requires.last_mut().unwrap();
            *last = last.clone().with_role(role);
            changed.resource_ensures.pop();
        } else {
            changed.resource_requires.pop();
            let last = changed.resource_ensures.last_mut().unwrap();
            *last = last.clone().with_role(role);
        }
        assert!(!authority_preserves_assumed_resource_contract(&changed));
    }
    let mut changed = interface.clone();
    changed.resource_ensures.pop();
    changed.resource_ensures.push(
        ResourceSpec::instance(
            Variable::allocate_fresh().unwrap(),
            "member".into(),
            schema,
            member,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Current,
        )
        .unwrap(),
    );
    assert!(!authority_preserves_assumed_resource_contract(&changed));
    interface.resource_ensures.pop();
    assert!(!authority_preserves_assumed_resource_contract(&interface));
}

fn companion_interface(member_family: &str) -> FunctionContractInterface {
    let member = ResourceSpec::composite(
        ResourceAccessMode::Own,
        member_family.into(),
        vec![crate::kernel::program_expression::variable("p")],
        vec![ProgramType::Int32Pointer],
    );
    let authority = ResourceSpec::new(
        ResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(ResourceTypeSpec {
                resource: Box::new(member.clone()),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            state_source: ResourceStateSource::Current,
        },
        ResourceAccessMode::Own,
        ResourceQuantity::One,
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let memory = ResourceSpec::owned_memory(MemorySegment::new(
        crate::kernel::program_expression::variable("slot"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(1),
    ));
    let parent = ResourceSpec::instance(
        Variable(991_010),
        "link".into(),
        ResourceFieldSchema::new(vec![("tag".into(), ResourceFieldType::Integer)]).unwrap(),
        ResourceSpec::composite(
            ResourceAccessMode::Own,
            "parent".into(),
            vec![crate::kernel::program_expression::variable("slot")],
            vec![ProgramType::Int32Pointer],
        ),
        ResourceTransferRole::Produce,
        ResourceStateSource::Post,
    )
    .unwrap();
    program_function(
        ProgramType::Void,
        "retain_with_companions",
        vec![],
        ProgramStatement::Skip,
    )
    .with_resource_summary(
        vec![
            memory,
            member.clone().with_role(ResourceTransferRole::Borrow),
            authority.clone(),
        ],
        vec![
            parent,
            member.clone().with_role(ResourceTransferRole::Produce),
            member.with_role(ResourceTransferRole::Borrow),
            authority,
        ],
    )
    .contract_interface()
    .clone()
}

#[test]
fn member_effect_is_independent_of_companion_positions_and_borrowed_survivor() {
    let interface = companion_interface("reference");
    let (produce, selected) = authority_member_effect(&interface).unwrap();
    assert!(produce);
    assert!(matches!(selected.term(), ResourceTerm::Composite { name, .. } if name == "reference"));
    assert!(authority_supports_resource_contract(&interface));
}

#[test]
fn member_move_admission_requires_two_scoped_authorities_and_one_unchanged_member() {
    let member = |anchor, trailing| {
        ResourceSpec::composite(
            ResourceAccessMode::Own,
            "slot".into(),
            vec![
                crate::kernel::program_expression::variable(anchor),
                crate::kernel::program_expression::variable(trailing),
            ],
            vec![ProgramType::Int32Pointer, ProgramType::Int32Pointer],
        )
    };
    let authority = |anchor| {
        ResourceSpec::new(
            ResourceTerm::PopulationAuthority {
                population_arity: Some(2),
                protected: Box::new(ResourceTypeSpec {
                    resource: Box::new(ResourceSpec::composite(
                        ResourceAccessMode::Own,
                        "slot".into(),
                        vec![crate::kernel::program_expression::variable(anchor)],
                        vec![ProgramType::Int32Pointer],
                    )),
                    schema: ResourceFieldSchema::new(vec![]).unwrap(),
                }),
                state_source: ResourceStateSource::Current,
            },
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        )
        .unwrap()
    };
    let source = authority("source");
    let destination = authority("destination");
    let interface = program_function(ProgramType::Void, "move", vec![], ProgramStatement::Skip)
        .with_resource_summary(
            vec![
                source.clone(),
                destination.clone(),
                member("source", "p").with_role(ResourceTransferRole::Consume),
            ],
            vec![
                source,
                destination,
                member("destination", "p").with_role(ResourceTransferRole::Produce),
            ],
        )
        .contract_interface()
        .clone();
    assert!(authority_exchanges_member_contract(&interface));
    assert!(authority_supports_resource_contract(&interface));
    assert!(authority_member_effect(&interface).is_none());
    let mut missing = interface.clone();
    missing.resource_requires.remove(1);
    assert!(!authority_supports_resource_contract(&missing));
    let mut changed_member = interface.clone();
    changed_member.resource_ensures[2] =
        member("destination", "q").with_role(ResourceTransferRole::Produce);
    assert!(!authority_supports_resource_contract(&changed_member));
    let mut duplicate = interface.clone();
    duplicate
        .resource_ensures
        .push(duplicate.resource_ensures[2].clone());
    assert!(!authority_supports_resource_contract(&duplicate));
    let mut same_pool = interface.clone();
    same_pool.resource_ensures[2] = member("source", "p").with_role(ResourceTransferRole::Produce);
    assert!(!authority_supports_resource_contract(&same_pool));
    let mut lost_authority = interface;
    lost_authority.resource_ensures.remove(1);
    assert!(!authority_supports_resource_contract(&lost_authority));
}

#[test]
fn family_exchange_admission_requires_both_exact_authorities_and_one_effect_each() {
    let member = |name: &str, arguments: Vec<ProgramExpression>| {
        let types = vec![ProgramType::Int32Pointer; arguments.len()];
        ResourceSpec::composite(ResourceAccessMode::Own, name.into(), arguments, types)
    };
    let authority = |name: &str, arity| {
        ResourceSpec::new(
            ResourceTerm::PopulationAuthority {
                protected: Box::new(ResourceTypeSpec {
                    resource: Box::new(member(
                        name,
                        vec![crate::kernel::program_expression::variable("pool")],
                    )),
                    schema: ResourceFieldSchema::new(vec![]).unwrap(),
                }),
                population_arity: arity,
                state_source: ResourceStateSource::Current,
            },
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        )
        .unwrap()
    };
    let capacity = authority("capacity", None);
    let item = authority("item", Some(2));
    let interface = program_function(
        ProgramType::Void,
        "checkout",
        vec![],
        ProgramStatement::Skip,
    )
    .with_resource_summary(
        vec![
            capacity.clone(),
            item.clone(),
            member(
                "capacity",
                vec![crate::kernel::program_expression::variable("pool")],
            )
            .with_role(ResourceTransferRole::Consume),
        ],
        vec![
            capacity,
            item,
            member(
                "item",
                vec![
                    crate::kernel::program_expression::variable("pool"),
                    crate::kernel::program_expression::variable("p"),
                ],
            )
            .with_role(ResourceTransferRole::Produce),
        ],
    )
    .contract_interface()
    .clone();
    assert!(authority_exchanges_member_contract(&interface));
    for index in [0, 1] {
        let mut missing = interface.clone();
        missing.resource_requires.remove(index);
        assert!(!authority_supports_resource_contract(&missing));
        let mut lost = interface.clone();
        lost.resource_ensures.remove(index);
        assert!(!authority_supports_resource_contract(&lost));
    }
    let mut duplicate = interface.clone();
    duplicate
        .resource_requires
        .push(duplicate.resource_requires[2].clone());
    assert!(!authority_supports_resource_contract(&duplicate));
    let mut duplicate = interface.clone();
    duplicate
        .resource_ensures
        .push(duplicate.resource_ensures[2].clone());
    assert!(!authority_supports_resource_contract(&duplicate));
    let mut wrong_anchor = interface;
    wrong_anchor.resource_ensures[2] = member(
        "item",
        vec![
            crate::kernel::program_expression::variable("other"),
            crate::kernel::program_expression::variable("p"),
        ],
    )
    .with_role(ResourceTransferRole::Produce);
    assert!(!authority_supports_resource_contract(&wrong_anchor));
}

#[test]
fn four_effect_exchange_admission_checks_every_scope_quantity_and_exact_identity() {
    let member = |family: &str, anchor: &str, item: bool| {
        let mut arguments = vec![crate::kernel::program_expression::variable(anchor)];
        if item {
            arguments.push(crate::kernel::program_expression::variable("p"));
        }
        let types = vec![ProgramType::Int32Pointer; arguments.len()];
        ResourceSpec::composite(ResourceAccessMode::Own, family.into(), arguments, types)
    };
    let authority = |family: &str, anchor: &str, item: bool| {
        ResourceSpec::new(
            ResourceTerm::PopulationAuthority {
                population_arity: item.then_some(2),
                protected: Box::new(ResourceTypeSpec {
                    resource: Box::new(member(family, anchor, false)),
                    schema: ResourceFieldSchema::new(vec![]).unwrap(),
                }),
                state_source: ResourceStateSource::Current,
            },
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        )
        .unwrap()
    };
    let authorities = vec![
        authority("slot", "source", false),
        authority("slot", "destination", false),
        authority("item", "source", true),
        authority("item", "destination", true),
    ];
    let mut inputs = authorities.clone();
    inputs.extend([
        member("item", "source", true).with_role(ResourceTransferRole::Consume),
        member("slot", "destination", false).with_role(ResourceTransferRole::Consume),
    ]);
    let mut outputs = authorities;
    outputs.extend([
        member("item", "destination", true).with_role(ResourceTransferRole::Produce),
        member("slot", "source", false).with_role(ResourceTransferRole::Produce),
    ]);
    let interface = program_function(
        ProgramType::Void,
        "exchange",
        vec![],
        ProgramStatement::Skip,
    )
    .with_resource_summary(inputs, outputs)
    .contract_interface()
    .clone();
    assert!(authority_supports_resource_contract(&interface));
    let effects = authority_checked_member_effects(&interface);
    assert_eq!(effects.iter().filter(|(produce, _)| !produce).count(), 2);
    assert_eq!(effects.iter().filter(|(produce, _)| *produce).count(), 2);
    for index in 0..4 {
        let mut missing = interface.clone();
        missing.resource_requires.remove(index);
        assert!(!authority_supports_resource_contract(&missing));
        let mut lost = interface.clone();
        lost.resource_ensures.remove(index);
        assert!(!authority_supports_resource_contract(&lost));
    }
    for index in [4, 5] {
        let mut missing = interface.clone();
        missing.resource_requires.remove(index);
        assert!(!authority_supports_resource_contract(&missing));
        let mut missing = interface.clone();
        missing.resource_ensures.remove(index);
        assert!(!authority_supports_resource_contract(&missing));
    }
    for index in [4, 5] {
        let mut nonunit = interface.clone();
        let original = &nonunit.resource_ensures[index];
        nonunit.resource_ensures[index] = ResourceSpec::new(
            original.term().clone(),
            original.access(),
            ResourceQuantity::Count(crate::kernel::program_expression::int32_literal(2)),
            original.role(),
            original.state_source(),
        )
        .unwrap();
        assert!(!authority_supports_resource_contract(&nonunit));
    }
    let mut changed_item = interface.clone();
    changed_item.resource_ensures[4] = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "item".into(),
        vec![
            crate::kernel::program_expression::variable("destination"),
            crate::kernel::program_expression::variable("q"),
        ],
        vec![ProgramType::Int32Pointer; 2],
    )
    .with_role(ResourceTransferRole::Produce);
    assert!(!authority_supports_resource_contract(&changed_item));
    let mut extra = interface.clone();
    extra
        .resource_ensures
        .push(extra.resource_ensures[5].clone());
    assert!(!authority_supports_resource_contract(&extra));
    let mut wrong_anchor = interface;
    wrong_anchor.resource_ensures[5] =
        member("slot", "other", false).with_role(ResourceTransferRole::Produce);
    assert!(!authority_supports_resource_contract(&wrong_anchor));
}

#[test]
fn two_control_births_require_each_scope_return_and_unit_effect() {
    let composite = |name: &str, anchor: &str| {
        ResourceSpec::composite(
            ResourceAccessMode::Own,
            name.into(),
            vec![crate::kernel::program_expression::variable(anchor)],
            vec![ProgramType::Int32Pointer],
        )
    };
    let authority = ResourceSpec::new(
        ResourceTerm::PopulationAuthority {
            population_arity: None,
            protected: Box::new(ResourceTypeSpec {
                resource: Box::new(composite("slot", "p")),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
            }),
            state_source: ResourceStateSource::Current,
        },
        ResourceAccessMode::Own,
        ResourceQuantity::One,
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let definition = |name: &str| {
        CompositeResourceDefinition::new(
            name,
            vec![program_parameter("p", ProgramType::Int32Pointer)],
            None,
            false,
            vec![authority.clone()],
            vec![],
        )
    };
    let input = |anchor| composite("storage", anchor).with_role(ResourceTransferRole::Consume);
    let output = |anchor| composite("control", anchor).with_role(ResourceTransferRole::Produce);
    let birth = |anchor| composite("slot", anchor).with_role(ResourceTransferRole::Produce);
    let interface = program_function(ProgramType::Void, "pair", vec![], ProgramStatement::Skip)
        .with_resource_summary(
            vec![input("first"), input("second")],
            vec![
                output("first"),
                output("second"),
                birth("first"),
                birth("second"),
            ],
        )
        .with_composite_resource_definitions(vec![definition("storage"), definition("control")])
        .contract_interface()
        .clone();
    assert!(authority_supports_resource_contract(&interface));
    assert_eq!(authority_checked_member_effects(&interface).len(), 2);
    for index in 0..2 {
        let mut missing = interface.clone();
        missing.resource_requires.remove(index);
        assert!(authority_two_control_births(&missing).is_none());
        let mut lost = interface.clone();
        lost.resource_ensures.remove(index);
        assert!(authority_two_control_births(&lost).is_none());
    }
    for index in 2..4 {
        let mut missing = interface.clone();
        missing.resource_ensures.remove(index);
        assert!(authority_two_control_births(&missing).is_none());
        let mut wrong = interface.clone();
        wrong.resource_ensures[index] = birth("other");
        assert!(authority_two_control_births(&wrong).is_none());
        let mut nonunit = interface.clone();
        let old = &nonunit.resource_ensures[index];
        nonunit.resource_ensures[index] = ResourceSpec::new(
            old.term().clone(),
            old.access(),
            ResourceQuantity::Count(crate::kernel::program_expression::int32_literal(2)),
            old.role(),
            old.state_source(),
        )
        .unwrap();
        assert!(authority_two_control_births(&nonunit).is_none());
    }
    let mut duplicate = interface.clone();
    duplicate.resource_ensures[3] = birth("first");
    assert!(authority_two_control_births(&duplicate).is_none());
    let mut changed_control = interface.clone();
    changed_control.resource_ensures[1] = output("other");
    assert!(authority_two_control_births(&changed_control).is_none());
    let mut extra = interface;
    extra.resource_ensures.push(birth("third"));
    assert!(authority_two_control_births(&extra).is_none());
}

#[test]
fn multiple_member_effects_cannot_pass_as_ordinary_companions() {
    let mut interface = companion_interface("reference");
    let member = interface.resource_ensures[1].clone();
    interface.resource_ensures.push(member);
    assert!(authority_member_effect(&interface).is_none());
    assert!(!authority_supports_resource_contract(&interface));
}

#[test]
fn member_effect_requires_its_own_authority_family() {
    let mut interface = companion_interface("reference");
    interface.resource_ensures[1] = ResourceSpec::composite(
        ResourceAccessMode::Own,
        "different".into(),
        vec![crate::kernel::program_expression::variable("p")],
        vec![ProgramType::Int32Pointer],
    )
    .with_role(ResourceTransferRole::Produce);
    assert!(authority_member_effect(&interface).is_none());
    assert!(!authority_produces_member_contract(&interface));
    assert!(!authority_supports_resource_contract(&interface));
}
#[test]
fn effect_cannot_hide_an_unprotected_composite_birth() {
    let mut interface = companion_interface("reference");
    interface.resource_ensures.push(
        ResourceSpec::composite(
            ResourceAccessMode::Own,
            "unprotected".into(),
            vec![crate::kernel::program_expression::variable("p")],
            vec![ProgramType::Int32Pointer],
        )
        .with_role(ResourceTransferRole::Produce),
    );
    assert!(!authority_supports_resource_contract(&interface));
}

#[test]
fn neutral_authority_requires_the_exact_borrowed_return() {
    let mut interface = companion_interface("reference");
    interface
        .resource_requires
        .retain(|spec| spec.family() == ResourceFamily::PopulationAuthority);
    interface.resource_ensures.clear();
    assert!(!authority_supports_resource_contract(&interface));
}
#[test]
fn resource_expansion_diagnostics_bound_the_named_frontier() {
    let resources = ResourceContext::new().unchecked_with_facts((0..32).map(|id| {
        ResourceFact::own(Resource::Composite {
            name: format!("resource_{id}_{}", "x".repeat(1000)),
            arguments: vec![ProgramValue::pointer(Pointer::null()).into()].into(),
        })
    }));
    let diagnostic = bounded_contract_resource_frontier(&resources);
    assert!(diagnostic.len() < 600);
    assert!(diagnostic.contains("and 24 more clauses"));
    assert!(!diagnostic.contains("ResourceContext"));
    assert!(!diagnostic.contains("MemoryLoad"));
}
