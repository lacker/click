// The proposition search these tests exercise is Surface planning now; see
// `src/surface/planning/proposition_search.rs`. The kernel itself never
// calls it, so the tests import the planner explicitly.
use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

#[test]
fn normalized_resource_specs_validate_families_and_preserve_transfer_metadata() {
    let segment = CMemorySegment::new(c_variable("p"), c_int32_literal(0), c_int32_literal(2));
    let memory_view = CResourceSpec::new(
        CResourceTerm::Memory(segment.clone()),
        CResourceAccessMode::View,
        CResourceQuantity::One,
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    assert_eq!(memory_view.family(), ResourceFamily::Memory);
    assert_eq!(memory_view.access(), CResourceAccessMode::View);
    assert_eq!(memory_view.role(), CResourceTransferRole::Borrow);
    assert_eq!(memory_view.snapshot(), CResourceSnapshot::Entry);
    assert_eq!(
        memory_view.clone().with_clause_position(0, 2),
        memory_view.clone().with_clause_position(1, 9)
    );

    let memory_owner = CResourceSpec::new(
        CResourceTerm::Memory(segment),
        CResourceAccessMode::Own,
        CResourceQuantity::One,
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    assert!(memory_owner.memory_segment().is_some());

    let composite_view = CResourceSpec::declared(
        ResourceFamily::Composite,
        CResourceAccessMode::View,
        "box".into(),
        vec![],
        vec![],
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    let token_owner = CResourceSpec::declared(
        ResourceFamily::Token,
        CResourceAccessMode::Own,
        "permit".into(),
        vec![],
        vec![],
        CResourceTransferRole::Produce,
        CResourceSnapshot::Post,
    )
    .unwrap();
    assert_eq!(composite_view.family(), ResourceFamily::Composite);
    assert_eq!(token_owner.family(), ResourceFamily::Token);
    assert_eq!(token_owner.role(), CResourceTransferRole::Produce);
    assert_eq!(token_owner.snapshot(), CResourceSnapshot::Post);

    let counted = CResourceSpec::quantified(
        c_int32_literal(3),
        token_owner.clone(),
        CResourceTransferRole::Consume,
        CResourceSnapshot::Current,
    )
    .unwrap();
    assert!(matches!(counted.quantity(), CResourceQuantity::Count(_)));

    assert!(matches!(
        CResourceSpec::new(
            CResourceTerm::Memory(CMemorySegment::new(
                c_variable("p"),
                c_int32_literal(0),
                c_int32_literal(1),
            )),
            CResourceAccessMode::Own,
            CResourceQuantity::Count(c_int32_literal(2)),
            CResourceTransferRole::Consume,
            CResourceSnapshot::Entry,
        ),
        Err(CResourceSpecError::InvalidQuantity {
            family: ResourceFamily::Memory,
            ..
        })
    ));
    assert!(matches!(
        CResourceSpec::quantified(
            c_int32_literal(2),
            composite_view,
            CResourceTransferRole::Consume,
            CResourceSnapshot::Current,
        ),
        Err(CResourceSpecError::InvalidAccess {
            family: ResourceFamily::Composite,
            access: CResourceAccessMode::View,
        })
    ));

    let schema = ResourceFieldSchema::new(vec![]).unwrap();
    let instance_term = CResourceTerm::Instance {
        identity: Variable(77),
        binder: "cell".into(),
        schema: schema.clone(),
        resource: Box::new(CResourceTerm::Composite {
            name: "cell".into(),
            arguments: vec![],
            parameter_types: vec![],
        }),
    };
    assert!(matches!(
        CResourceSpec::new(
            instance_term.clone(),
            CResourceAccessMode::View,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        ),
        Err(CResourceSpecError::InvalidAccess {
            family: ResourceFamily::Instance,
            access: CResourceAccessMode::View,
        })
    ));
    assert!(
        CResourceSpec::new(
            instance_term,
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        )
        .is_ok()
    );
    assert!(matches!(
        CResourceSpec::new(
            CResourceTerm::Instance {
                identity: Variable(78),
                binder: "token".into(),
                schema,
                resource: Box::new(CResourceTerm::Token {
                    name: "token".into(),
                    arguments: vec![],
                    parameter_types: vec![],
                }),
            },
            CResourceAccessMode::Own,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        ),
        Err(CResourceSpecError::InvalidNestedTerm(_))
    ));
}

#[test]
fn normalized_resource_spec_evaluation_preserves_indexed_lookup_scaling() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let names = (0..size)
                .map(|index| format!("token{index}"))
                .collect::<Vec<_>>();
            let context = ResourceContext::new().unchecked_with_facts(
                names
                    .iter()
                    .cloned()
                    .map(|name| CResourceFact::own_token(name, Vec::new())),
            );
            let spec = CResourceSpec::declared(
                ResourceFamily::Token,
                CResourceAccessMode::Own,
                names[size / 2].clone(),
                Vec::new(),
                Vec::new(),
                CResourceTransferRole::Consume,
                CResourceSnapshot::Current,
            )
            .unwrap();
            let state = CState::new().with_resource_context(context);
            let assumptions = PureFactContext::new();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut budget = ExecutionBudget::default();
                let fact = crate::kernel::functions::evaluate_function_resource_spec(
                    &state,
                    &spec,
                    &assumptions,
                    &mut budget,
                )
                .unwrap()
                .unwrap();
                assert!(state.resources().satisfies_fact(&fact, &assumptions));
                let remaining = state
                    .resources()
                    .clone()
                    .without_fact_delaying_normalization(&fact, &assumptions)
                    .expect("indexed lookup finds the normalized token");
                assert_eq!(remaining.facts().len(), size - 1);
            });
            assert!(work > 0);
            (size, work)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(3) + 64),
        "normalized resource evaluation is superlinear: {samples:?}"
    );
}

#[test]
fn validated_resource_rebuilds_preserve_metadata_and_instance_bodies() {
    let variable = Variable(77_700);
    let quantity = CExpression::Value(int32(Bitvector32Term::Variable(variable)));
    let spec = CResourceSpec::new(
        CResourceTerm::Token {
            name: "permit".into(),
            arguments: vec![quantity.clone()],
            parameter_types: vec![CType::Int32],
        },
        CResourceAccessMode::Own,
        CResourceQuantity::Count(quantity),
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    let substituted = crate::kernel::reasoning::substitute_bitvector_variable_in_resource_spec(
        &spec,
        variable,
        &Bitvector32Term::Constant(3),
    );
    assert_eq!(substituted.access(), CResourceAccessMode::Own);
    assert_eq!(substituted.role(), CResourceTransferRole::Borrow);
    assert_eq!(substituted.snapshot(), CResourceSnapshot::Entry);
    assert!(matches!(
        substituted.quantity(),
        CResourceQuantity::Count(CExpression::Value(CValue::Int32(
            Bitvector32Term::Constant(3)
        )))
    ));
    assert!(matches!(
        substituted.term(),
        CResourceTerm::Token { arguments, .. }
            if matches!(arguments.as_slice(), [CExpression::Value(CValue::Int32(Bitvector32Term::Constant(3)))])
    ));

    let schema = ResourceFieldSchema::new(vec![]).unwrap();
    let instance = CResourceSpec::instance(
        variable,
        "cell".into(),
        schema,
        CResourceSpec::composite(CResourceAccessMode::Own, "cell".into(), vec![], vec![]),
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Entry,
    )
    .unwrap();
    let inner = instance
        .instance_resource_spec()
        .expect("validated instance has a reconstructible inner term");
    assert_eq!(inner.access(), CResourceAccessMode::Own);
    assert_eq!(inner.quantity(), &CResourceQuantity::One);
    assert_eq!(inner.role(), CResourceTransferRole::Borrow);
    assert_eq!(inner.snapshot(), CResourceSnapshot::Entry);

    assert!(matches!(
        CResourceSpec::new(
            CResourceTerm::Instance {
                identity: variable,
                binder: "cell".into(),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
                resource: Box::new(CResourceTerm::Composite {
                    name: "cell".into(),
                    arguments: vec![],
                    parameter_types: vec![],
                }),
            },
            CResourceAccessMode::View,
            CResourceQuantity::One,
            CResourceTransferRole::Borrow,
            CResourceSnapshot::Entry,
        ),
        Err(CResourceSpecError::InvalidAccess {
            family: ResourceFamily::Instance,
            access: CResourceAccessMode::View,
        })
    ));
}

#[test]
fn owned_range_access_survives_learning_a_symbolic_pointer_alias() {
    let cell = Pointer::symbolic(Variable(100));
    let slot = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(101)), 4),
    };
    let unrelated = Pointer::symbolic(Variable(102));
    let range = CMemoryRange::new(
        cell.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    );
    let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(range));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(cell.clone(), slot.clone()),
        true,
    );
    for pointer in [&cell, &slot] {
        assert!(
            resources
                .memory_write_range(pointer, 4, &assumptions)
                .is_some()
        );
    }
    assert!(
        resources
            .memory_write_range(&unrelated, 4, &assumptions)
            .is_none()
    );
    assert!(
        resources
            .memory_write_range(&cell, 16, &assumptions)
            .is_none()
    );
}

fn instance_memory_fixture() -> (ResourceInstance, CCompositeResourceDefinition, CState) {
    let schema =
        ResourceFieldSchema::new(vec![("value".into(), ResourceFieldType::C(CType::Int32))])
            .unwrap();
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(100)), 4),
    };
    let instance = ResourceInstance::new(
        Variable(1),
        "cell".into(),
        vec![CValue::pointer(pointer).into()].into(),
        schema.clone(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let definition = CCompositeResourceDefinition::new(
        "cell",
        vec![c_parameter("p", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment {
            base: c_variable("p"),
            start: c_int32_literal(0),
            end: c_int32_literal(1),
            element_width: 4,
            guard: None,
        })],
        vec![],
    )
    .with_instance_schema(Some(schema));
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone()))),
    );
    (instance, definition, state)
}

fn recursive_child_fixture() -> (ResourceInstance, CCompositeResourceDefinition, CState) {
    let (mut instance, mut definition, _) = instance_memory_fixture();
    let tree = AlgebraicValueType::Algebraic {
        name: "Tree".into(),
        arguments: vec![],
    };
    let ty = resource_index_type(
        "Tree",
        vec![
            AlgebraicValueType::C(CType::Int32Pointer),
            tree.clone(),
            AlgebraicValueType::C(CType::Int32Pointer),
            tree,
        ],
    );
    let empty = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Clear".into(),
            fields: vec![],
        },
    };
    instance.schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(ty.clone()),
    )])
    .unwrap();
    instance.fields = vec![AlgebraicValue::Algebraic(AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Set".into(),
            fields: vec![
                CValue::pointer(Pointer::null()).into(),
                AlgebraicValue::Algebraic(empty.clone()),
                CValue::pointer(Pointer::null()).into(),
                AlgebraicValue::Algebraic(empty),
            ],
        },
    })]
    .into();
    definition.instance_schema = Some(instance.schema.clone());
    definition.matched = Some(CResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            CResourceMatchArm {
                variant: "Clear".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            CResourceMatchArm {
                variant: "Set".into(),
                bindings: vec!["lp".into(), "lm".into(), "rp".into(), "rm".into()],
                binding_types: ty.variants[1].fields.clone(),
                binding_variables: vec![None, None, None, None],
                contains: std::mem::take(&mut definition.contains),
                facts: vec![],
                children: vec![
                    CResourceChildSpec {
                        name: "left".into(),
                        resource: "cell".into(),
                        binding: Variable(90),
                        arguments: vec![c_variable("lp")],
                        field_bindings: vec![1],
                    },
                    CResourceChildSpec {
                        name: "right".into(),
                        resource: "cell".into(),
                        binding: Variable(91),
                        arguments: vec![c_variable("rp")],
                        field_bindings: vec![3],
                    },
                ],
            },
        ],
    });
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone()))),
    );
    (instance, definition, state)
}

#[test]
fn stored_child_arguments_require_owned_memory() {
    let (instance, mut definition, state) = recursive_child_fixture();
    let arm = &mut definition.matched.as_mut().unwrap().arms[1];
    let Some(segment) = arm.contains[0].memory_segment_mut() else {
        unreachable!()
    };
    segment.end = c_int32_literal(2); // one LP64 pointer
    arm.children[0].arguments = vec![CExpression::TypedLoad {
        pointer: Box::new(c_variable("p")),
        value_type: CType::Int32Pointer,
        volatile: false,
    }];
    let children = vec![
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let assumptions = PureFactContext::new();
    let rewrite = |state: &CState,
                   definition: &CCompositeResourceDefinition,
                   assumptions: &PureFactContext,
                   unfold| {
        crate::kernel::rewrite_resource_instance_selecting_children(
            state,
            &instance,
            definition,
            std::slice::from_ref(definition),
            assumptions,
            unfold,
            Some(&children),
        )
    };
    let (open, _) = rewrite(&state, &definition, &assumptions, true).unwrap();
    rewrite(&open, &definition, &assumptions, false).unwrap();
    let mut unreadable = definition.clone();
    unreadable.matched.as_mut().unwrap().arms[1]
        .contains
        .clear();
    // Even a caller using permissive specification lowering cannot grant
    // child construction an unchecked read outside the owned body.
    assert!(
        rewrite(
            &state,
            &unreadable,
            &assumptions.clone().allow_symbolic_contract_loads(),
            true
        )
        .is_err()
    );
    let mut missing = open.clone();
    missing.resources = ResourceContext::new().unchecked_with_facts(
        open.resources()
            .facts()
            .iter()
            .filter(|fact| fact.memory_range().is_none())
            .cloned(),
    );
    assert!(rewrite(&missing, &definition, &assumptions, false).is_err());
    assert!(rewrite(&open, &unreadable, &assumptions, false).is_err());
    let concrete = Pointer {
        block: "unowned-link".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let concrete_state = state.clone().with_memory(
        CMemory::new()
            .with_block("unowned-link", 8)
            .store(concrete.clone(), CValue::pointer(Pointer::null())),
    );
    let mut concrete_definition = definition.clone();
    concrete_definition.matched.as_mut().unwrap().arms[1].children[0].arguments =
        vec![CExpression::TypedLoad {
            pointer: Box::new(c_pointer_value(concrete.clone())),
            value_type: CType::Int32Pointer,
            volatile: false,
        }];
    // A materialized C block is not authority to read a link outside the
    // resource body, even though ordinary C execution can access that block.
    assert!(rewrite(&concrete_state, &concrete_definition, &assumptions, true).is_err());
    concrete_definition.matched.as_mut().unwrap().arms[1]
        .contains
        .push(CResourceSpec::owned_memory(CMemorySegment {
            base: c_pointer_value(concrete),
            start: c_int32_literal(0),
            end: c_int32_literal(2),
            element_width: 4,
            guard: None,
        }));
    rewrite(&concrete_state, &concrete_definition, &assumptions, true).unwrap();
    // The parent's concrete memory may not also be owned by the surrounding
    // frame: unfolding must reject overlapping ownership.
    let mut overlap = state.clone();
    overlap.resources = overlap.resources.unchecked_with_facts(
        open.resources()
            .facts()
            .iter()
            .filter(|fact| fact.memory_range().is_some())
            .cloned(),
    );
    assert!(rewrite(&overlap, &definition, &assumptions, true).is_err());
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut framed = open.clone();
        for i in 0..size {
            let other = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::Variable(Variable(1000 + i)),
                    4,
                ),
            };
            framed.resources = framed
                .resources
                .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    other,
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                )));
        }
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            rewrite(&framed, &definition, &assumptions, false)
        });
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 128, "{samples:?}");
    }
}

#[test]
fn instance_fold_preserves_memory_pieces_without_scanning_unrelated_resources() {
    let (instance, mut definition, _) = instance_memory_fixture();
    definition.contains = (0..3)
        .map(|i| {
            CResourceSpec::owned_memory(CMemorySegment {
                base: c_variable("p"),
                start: c_int32_literal(i),
                end: c_int32_literal(i + 1),
                element_width: 4,
                guard: None,
            })
        })
        .collect();
    let CValue::Pointer(value) = instance.arguments()[0].as_c_value().unwrap() else {
        unreachable!()
    };
    let pointer = value.pointer().clone();
    let pieces = (0..3)
        .map(|i| {
            CResourceFact::own_memory(CMemoryRange::new(
                pointer.clone(),
                Bitvector32Term::Constant(i),
                Bitvector32Term::Constant(i + 1),
            ))
        })
        .collect::<Vec<_>>();
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut resources = ResourceContext::new().unchecked_with_facts(pieces.iter().cloned());
        for i in 0..size {
            let other = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::Variable(Variable(1000 + i)),
                    4,
                ),
            };
            resources =
                resources.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    other,
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                )));
        }
        let state = CState::new().with_resource_context(resources);
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::rewrite_resource_instance_selecting_children(
                &state,
                &instance,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                false,
                Some(&[]),
            )
        });
        result.unwrap();
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 128, "{samples:?}");
    }
}

#[test]
fn independent_children_kernel_consumes_names_and_accepts_replacements() {
    let (instance, definition, state) = recursive_child_fixture();
    let assumptions = PureFactContext::new();
    let children = vec![
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let rewrite =
        |state: &CState, instance: &ResourceInstance, unfold, children: &[(String, Variable)]| {
            crate::kernel::rewrite_resource_instance_selecting_children(
                state,
                instance,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                unfold,
                Some(children),
            )
        };
    let (open, _) = rewrite(&state, &instance, true, &children).unwrap();
    assert!(open.instance_field_scope.is_empty());
    assert!(open.resource_instance_fields(instance.identity()).is_none());
    assert!(
        open.resource_instance_at_path(instance.identity(), &["left".into()])
            .is_none()
    );
    let left = open.owned_resource_instance(Variable(501)).unwrap().clone();
    let (raw, _) = rewrite(&open, &left, true, &[]).unwrap();
    assert!(raw.owned_resource_instance(left.identity()).is_none());
    assert!(rewrite(&raw, &instance, false, &children).is_err());
    let mut replacement = left.clone();
    replacement.identity = Variable(503);
    let (replaced, _) = rewrite(&raw, &replacement, false, &[]).unwrap();
    let selected = vec![
        ("left".into(), Variable(503)),
        ("right".into(), Variable(502)),
    ];
    let (closed, _) = rewrite(&replaced, &instance, false, &selected).unwrap();
    assert_eq!(closed.resources(), state.resources());
    assert!(closed.instance_field_scope.is_empty());
    for bad in [
        vec![],
        vec![("left".into(), Variable(501))],
        vec![
            ("left".into(), Variable(501)),
            ("right".into(), Variable(501)),
        ],
        vec![
            ("left".into(), instance.identity()),
            ("right".into(), Variable(502)),
        ],
    ] {
        assert!(rewrite(&state, &instance, true, &bad).is_err());
    }
    assert!(rewrite(&open, &instance, false, &selected).is_err());
}

#[test]
fn independent_children_kernel_work_ignores_unrelated_instances() {
    let (instance, definition, initial) = recursive_child_fixture();
    let assumptions = PureFactContext::new();
    let children = vec![
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut state = initial.clone();
        for identity in 2..=size {
            let mut unrelated = instance.clone();
            unrelated.identity = Variable(identity);
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::own(CResource::Instance(unrelated)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let (open, _) = crate::kernel::rewrite_resource_instance_selecting_children(
                &state,
                &instance,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                true,
                Some(&children),
            )
            .unwrap();
            assert!(open.instance_field_scope.is_empty());
            crate::kernel::rewrite_resource_instance_selecting_children(
                &open,
                &instance,
                &definition,
                std::slice::from_ref(&definition),
                &assumptions,
                false,
                Some(&children),
            )
            .unwrap()
        });
        assert!(work > 0);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 128, "{samples:?}");
    }
}

#[test]
fn recursive_child_kernel_rejects_implicit_parent_handles() {
    let (instance, definition, state) = recursive_child_fixture();
    let assumptions = PureFactContext::new();
    assert_eq!(
        rewrite_resource_instance(&state, &instance, &definition, &assumptions, true).unwrap_err(),
        "recursive children require explicit independent child selections"
    );
    let children = [
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let (opened, _) = crate::kernel::rewrite_resource_instance_selecting_children(
        &state,
        &instance,
        &definition,
        std::slice::from_ref(&definition),
        &assumptions,
        true,
        Some(&children),
    )
    .unwrap();
    assert!(
        opened
            .resource_instance_fields(instance.identity())
            .is_none()
    );
    assert!(opened.instance_field_scope.is_empty());
    assert!(
        rewrite_resource_instance(&opened, &instance, &definition, &assumptions, false).is_err()
    );
    let mut invalid = definition.clone();
    invalid.matched.as_mut().unwrap().arms[1].children[0].field_bindings = vec![0];
    assert!(
        crate::kernel::rewrite_resource_instance_selecting_children(
            &state,
            &instance,
            &invalid,
            std::slice::from_ref(&invalid),
            &assumptions,
            true,
            Some(&children),
        )
        .is_err()
    );
}

#[test]
fn recursive_child_kernel_keeps_unknown_submodels_folded() {
    let (mut instance, definition, _) = recursive_child_fixture();
    let mut fields = instance.fields.to_vec();
    let AlgebraicValue::Algebraic(model) = &mut fields[0] else {
        unreachable!()
    };
    let unknown = AlgebraicTerm {
        algebraic_type: model.algebraic_type.clone(),
        node: AlgebraicTermNode::Variable(Variable(555)),
    };
    let AlgebraicTermNode::Constructor { fields, .. } = &mut model.node else {
        unreachable!()
    };
    fields[0] = CValue::pointer(Pointer::symbolic(Variable(556))).into();
    fields[1] = AlgebraicValue::Algebraic(unknown.clone());
    // Rebuild the outer argument list after updating only its immediate fields.
    let model = model.clone();
    instance.fields = vec![AlgebraicValue::Algebraic(model)].into();
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone()))),
    );
    let assumptions = PureFactContext::new();
    let children = [
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let (open, _) = crate::kernel::rewrite_resource_instance_selecting_children(
        &state,
        &instance,
        &definition,
        std::slice::from_ref(&definition),
        &assumptions,
        true,
        Some(&children),
    )
    .unwrap();
    let child = open.owned_resource_instance(Variable(501)).unwrap();
    assert_eq!(child.fields(), &[AlgebraicValue::Algebraic(unknown)]);
    assert!(rewrite_resource_instance(&open, child, &definition, &assumptions, true).is_err());
    let (closed, _) = crate::kernel::rewrite_resource_instance_selecting_children(
        &open,
        &instance,
        &definition,
        std::slice::from_ref(&definition),
        &assumptions,
        false,
        Some(&children),
    )
    .unwrap();
    assert_eq!(closed.resources(), state.resources());
}

#[test]
fn instance_memory_guard_requires_a_proved_case_and_exposes_only_that_case() {
    let (instance, mut definition, state) = instance_memory_fixture();
    definition.condition = Some(SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("p")),
        operator: CComparisonOperator::NotEqual,
        right: SpecExpression::CExpression(c_int32_literal(0)),
    });
    let CValue::Pointer(pointer) = instance.arguments()[0].as_c_value().unwrap() else {
        panic!("fixture pointer");
    };
    let guard = ConditionTerm::pointer_equal(pointer.pointer().clone(), Pointer::null());
    let unknown = PureFactContext::new();
    assert!(rewrite_resource_instance(&state, &instance, &definition, &unknown, true).is_err());
    for is_null in [false, true] {
        let assumptions = unknown.clone().assume_condition(guard.clone(), is_null);
        let (open, facts) =
            rewrite_resource_instance(&state, &instance, &definition, &assumptions, true).unwrap();
        assert_eq!(open.resources().is_empty(), is_null);
        assert!(open.resource_instance_fields(instance.identity()).is_none());
        assert!(open.instance_field_scope.is_empty());
        assert_eq!(
            facts
                .iter()
                .any(|fact| matches!(fact, Proposition::CMemoryLoadable { .. })),
            !is_null
        );
        assert!(rewrite_resource_instance(&open, &instance, &definition, &unknown, false).is_err());
        let (closed, _) =
            rewrite_resource_instance(&open, &instance, &definition, &assumptions, false).unwrap();
        assert_eq!(closed, state);
        let raw = CState::new().with_resource_context(open.resources().clone());
        let mut fresh = instance.clone();
        fresh.identity = Variable(999);
        let (constructed, _) =
            rewrite_resource_instance(&raw, &fresh, &definition, &assumptions, false).unwrap();
        assert!(constructed.instance_field_scope.is_empty());
        assert_eq!(
            constructed.owned_resource_instance(fresh.identity()),
            Some(&fresh)
        );
        if is_null {
            let nonnull = unknown.clone().assume_condition(guard.clone(), false);
            assert!(
                rewrite_resource_instance(&open, &instance, &definition, &nonnull, false).is_err()
            );
        }
    }
}

#[test]
fn resource_match_constructor_index_tracks_evidence_and_scales_locally() {
    let ty = resource_index_type("Mark", vec![]);
    let model = resource_index_variable(&ty, 7);
    let constructor = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Set".into(),
            fields: vec![],
        },
    };
    let equality = Proposition::Equal(
        Term::Algebraic(model.clone()),
        Term::Algebraic(constructor.clone()),
    );
    let reversed = Proposition::Equal(
        Term::Algebraic(constructor.clone()),
        Term::Algebraic(model.clone()),
    );
    for fact in [equality.clone(), reversed] {
        let mut assumptions = PureFactContext::new().assume_proposition(fact.clone());
        assert_eq!(
            assumptions.known_algebraic_constructor(&model),
            Some(constructor.clone())
        );
        assumptions.remove_proposition_fact(&fact);
        assert!(assumptions.known_algebraic_constructor(&model).is_none());
        assumptions.insert_proposition_fact(fact.clone());
        assumptions.retain_proposition_facts(|entry| entry != &fact);
        assert!(assumptions.known_algebraic_constructor(&model).is_none());
        assumptions.insert_proposition_fact(fact);
        assumptions.clear_proposition_facts();
        assert!(assumptions.known_algebraic_constructor(&model).is_none());
    }
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut assumptions = PureFactContext::new().assume_proposition(equality.clone());
        for index in 100..100 + size {
            assumptions.insert_proposition_fact(Proposition::Equal(
                Term::Algebraic(resource_index_variable(&ty, index)),
                Term::Algebraic(constructor.clone()),
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                assumptions.known_algebraic_constructor(&model),
                Some(constructor.clone())
            );
        });
        assert!(work > 0, "constructor lookup must count candidate visits");
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 32, "{samples:?}");
    }
}

#[test]
fn resource_match_kernel_checks_schema_case_and_ownership() {
    let (mut instance, mut definition, _) = instance_memory_fixture();
    let ty = resource_index_type("Mark", vec![]);
    let model = resource_index_variable(&ty, 7);
    let constructor = |variant: &str| AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: variant.into(),
            fields: vec![],
        },
    };
    instance.schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(ty.clone()),
    )])
    .unwrap();
    instance.fields = vec![AlgebraicValue::Algebraic(model.clone())].into();
    definition.instance_schema = Some(instance.schema.clone());
    definition.matched = Some(CResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            CResourceMatchArm {
                children: vec![],
                variant: "Clear".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
            },
            CResourceMatchArm {
                variant: "Set".into(),
                children: vec![],
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: std::mem::take(&mut definition.contains),
                facts: vec![],
            },
        ],
    });
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone()))),
    );
    let unknown = PureFactContext::new();
    let set = unknown.clone().assume_proposition(Proposition::Equal(
        Term::Algebraic(model.clone()),
        Term::Algebraic(constructor("Set")),
    ));
    let clear = unknown.clone().assume_proposition(Proposition::Equal(
        Term::Algebraic(model),
        Term::Algebraic(constructor("Clear")),
    ));
    assert!(rewrite_resource_instance(&state, &instance, &definition, &unknown, true).is_err());
    let (empty, facts) =
        rewrite_resource_instance(&state, &instance, &definition, &clear, true).unwrap();
    assert!(empty.resources().is_empty());
    assert!(empty.instance_field_scope.is_empty());
    assert!(
        !facts
            .iter()
            .any(|fact| matches!(fact, Proposition::CMemoryLoadable { .. }))
    );
    assert!(rewrite_resource_instance(&empty, &instance, &definition, &set, false).is_err());
    let (open, _) = rewrite_resource_instance(&state, &instance, &definition, &set, true).unwrap();
    assert!(!open.resources().is_empty());
    assert!(open.instance_field_scope.is_empty());
    let mut fresh = instance.clone();
    fresh.identity = Variable(999);
    fresh.fields = vec![AlgebraicValue::Algebraic(constructor("Set"))].into();
    let raw = CState::new().with_resource_context(open.resources().clone());
    let (constructed, _) =
        rewrite_resource_instance(&raw, &fresh, &definition, &unknown, false).unwrap();
    assert_eq!(
        constructed.owned_resource_instance(fresh.identity()),
        Some(&fresh)
    );
    assert!(constructed.instance_field_scope.is_empty());
    assert!(
        rewrite_resource_instance(&CState::new(), &fresh, &definition, &unknown, false).is_err()
    );
    assert_eq!(
        rewrite_resource_instance(&open, &instance, &definition, &set, false)
            .unwrap()
            .0,
        state
    );
    assert!(rewrite_resource_instance(&open, &instance, &definition, &unknown, false).is_err());
    for mutation in 0..5 {
        let mut invalid = definition.clone();
        let body = invalid.matched.as_mut().unwrap();
        match mutation {
            0 => {
                body.arms.pop();
            }
            1 => {
                body.arms[0].variant = "Set".into();
            }
            2 => {
                body.arms[1].bindings.push("p".into());
            }
            3 => {
                body.field_index = 1;
            }
            _ => {
                body.arms[1]
                    .binding_types
                    .push(AlgebraicValueType::C(CType::Int32));
            }
        }
        assert!(rewrite_resource_instance(&state, &instance, &invalid, &set, true).is_err());
    }
}

#[test]
fn instance_memory_fold_requires_body_ownership_not_an_open_handle() {
    let (instance, definition, state) = instance_memory_fixture();
    let assumptions = PureFactContext::new();
    let (opened, _) =
        rewrite_resource_instance(&state, &instance, &definition, &assumptions, true).unwrap();
    assert!(
        opened
            .owned_resource_instance(instance.identity())
            .is_none()
    );
    assert!(
        opened
            .resource_instance_fields(instance.identity())
            .is_none()
    );
    assert!(opened.instance_field_scope.is_empty());
    assert_eq!(
        rewrite_resource_instance(&opened, &instance, &definition, &assumptions, false)
            .unwrap()
            .0,
        state
    );
    assert!(
        rewrite_resource_instance(&state, &instance, &definition, &assumptions, false).is_err()
    );
    assert!(
        rewrite_resource_instance(&opened, &instance, &definition, &assumptions, true).is_err()
    );
    let mut missing_body = opened.clone();
    missing_body.resources = ResourceContext::new();
    assert!(
        rewrite_resource_instance(&missing_body, &instance, &definition, &assumptions, false)
            .is_err()
    );
    let raw = CState::new().with_resource_context(opened.resources.clone());
    let mut constructed = instance.clone();
    constructed.identity = Variable(2);
    // This fixture's field is unconstrained by its body. Any well-typed value
    // is legitimate; neither its identity nor field must match an old package.
    constructed.fields = vec![int32(8).into()].into();
    let (folded, _) =
        rewrite_resource_instance(&raw, &constructed, &definition, &assumptions, false).unwrap();
    assert_eq!(
        folded.owned_resource_instance(Variable(2)),
        Some(&constructed)
    );
    assert!(folded.instance_field_scope.is_empty());
}

#[test]
fn instance_memory_fold_work_is_local_to_the_selected_instance() {
    let (instance, definition, initial) = instance_memory_fixture();
    let assumptions = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut state = initial.clone();
        for identity in 2..=size {
            let mut unrelated = instance.clone();
            unrelated.identity = Variable(identity);
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::own(CResource::Instance(unrelated)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let (open, _) =
                rewrite_resource_instance(&state, &instance, &definition, &assumptions, true)
                    .unwrap();
            assert!(open.resource_instance_fields(instance.identity()).is_none());
            rewrite_resource_instance(&open, &instance, &definition, &assumptions, false).unwrap()
        });
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] + 128,
            "unrelated handle scaling: {samples:?}"
        );
    }
}

fn field_instance(identity: u64, model: AlgebraicTerm, revision: u32) -> ResourceInstance {
    let schema = ResourceFieldSchema::new(vec![
        (
            "model".into(),
            ResourceFieldType::Algebraic(model.algebraic_type.clone()),
        ),
        ("revision".into(), ResourceFieldType::C(CType::Int32)),
    ])
    .unwrap();
    ResourceInstance::new(
        Variable(identity),
        "marked_cell".into(),
        vec![int32(7).into()].into(),
        schema,
        vec![AlgebraicValue::Algebraic(model), int32(revision).into()].into(),
    )
    .unwrap()
}

#[test]
fn resource_instances_validate_fields_without_expanding_symbolic_values() {
    let ty = resource_index_type("Mark", vec![]);
    let model = resource_index_variable(&ty, 1);
    let instance = field_instance(2, model.clone(), 3);
    assert_eq!(instance.fields()[0], AlgebraicValue::Algebraic(model));
    let make = |schema, fields| {
        ResourceInstance::new(
            Variable(2),
            "marked_cell".into(),
            instance.arguments.clone(),
            schema,
            fields,
        )
    };
    assert!(make(ResourceFieldSchema::new(vec![]).unwrap(), vec![].into()).is_none());
    assert!(make(instance.schema().clone(), vec![].into()).is_none());
    assert!(
        make(
            instance.schema().clone(),
            vec![int32(1).into(), int32(2).into()].into()
        )
        .is_none()
    );
    let wrong = resource_index_variable(&resource_index_type("Other", vec![]), 1);
    assert!(
        make(
            instance.schema().clone(),
            vec![AlgebraicValue::Algebraic(wrong), int32(2).into()].into()
        )
        .is_none()
    );
    let malformed = AlgebraicTerm {
        algebraic_type: ty,
        node: AlgebraicTermNode::Constructor {
            variant: "Missing".into(),
            fields: vec![],
        },
    };
    assert!(
        make(
            instance.schema().clone(),
            vec![AlgebraicValue::Algebraic(malformed), int32(2).into()].into()
        )
        .is_none()
    );
    let copy = instance.clone();
    assert!(std::sync::Arc::ptr_eq(&instance.fields, &copy.fields));
    assert!(std::sync::Arc::ptr_eq(&instance.arguments, &copy.arguments));
}

#[test]
fn resource_instances_are_exclusive_not_counted_or_viewable() {
    let assumptions = PureFactContext::new();
    let ty = resource_index_type("Mark", vec![]);
    let instance = field_instance(2, resource_index_variable(&ty, 1), 0);
    let owned = CResourceFact::own(CResource::Instance(instance.clone()));
    let context = ResourceContext::new()
        .try_compose_with_fact(owned.clone(), &assumptions)
        .unwrap();
    assert!(owned.core().is_none());
    assert!(owned.core_with_assumptions(&assumptions).is_none());
    let mut invalid = vec![CResourceFact::View(owned.resource().clone())];
    invalid.extend([0, 2].map(|q| CResourceFact::own_quantity(owned.resource().clone(), q.into())));
    invalid.push(CResourceFact::own_quantity(
        owned.resource().clone(),
        Bitvector32Term::Variable(Variable(8)),
    ));
    for fact in invalid {
        assert!(matches!(
            ResourceContext::new().try_compose_with_fact(fact.clone(), &assumptions),
            Err(ResourceContextValidityError::InvalidInstanceAccess(_))
        ));
        assert!(!context.satisfies_fact(&fact, &assumptions));
        assert!(
            context
                .clone()
                .without_fact_delaying_normalization(&fact, &assumptions)
                .is_none()
        );
        assert!(
            context
                .clone()
                .without_fact_incrementally(&fact, &assumptions)
                .is_none()
        );
        let invalid_context = ResourceContext::new().unchecked_with_fact(fact);
        assert!(invalid_context.owned_instance(Variable(2)).is_none());
        assert!(
            !invalid_context
                .normalized(&assumptions)
                .is_valid(&assumptions)
        );
    }
    for duplicate in [
        instance,
        field_instance(2, resource_index_variable(&ty, 9), 1),
    ] {
        let fact = CResourceFact::own(CResource::Instance(duplicate));
        assert!(
            context
                .clone()
                .try_compose_into_valid_context_delaying_normalization([fact.clone()], &assumptions)
                .is_err()
        );
        let invalid = context.clone().unchecked_with_fact(fact);
        assert!(invalid.owned_instance(Variable(2)).is_none());
        assert!(!invalid.normalized(&assumptions).is_valid(&assumptions));
    }
    let remaining = context
        .without_fact_delaying_normalization(&owned, &assumptions)
        .unwrap();
    assert!(remaining.owned_instance(Variable(2)).is_none());
    assert!(!remaining.satisfies_fact(&owned, &assumptions));
}

#[test]
fn resource_instances_distinguish_identity_from_equal_field_state() {
    let ty = resource_index_type("Mark", vec![]);
    let m = resource_index_variable(&ty, 1);
    let n = resource_index_variable(&ty, 2);
    let owned = CResourceFact::own(CResource::Instance(field_instance(10, m.clone(), 0)));
    let equal_state = CResourceFact::own(CResource::Instance(field_instance(10, n.clone(), 0)));
    let other_identity = CResourceFact::own(CResource::Instance(field_instance(11, m.clone(), 0)));
    let changed_scalar = CResourceFact::own(CResource::Instance(field_instance(10, m.clone(), 1)));
    let empty = PureFactContext::new();
    let context = ResourceContext::new().unchecked_with_fact(owned.clone());
    assert!(!context.satisfies_fact(&equal_state, &empty));
    let assumptions =
        empty.assume_proposition(Proposition::Equal(Term::Algebraic(m), Term::Algebraic(n)));
    assert!(context.satisfies_fact(&equal_state, &assumptions));
    assert!(c_resources_directly_match(
        owned.resource(),
        equal_state.resource(),
        &assumptions
    ));
    for wrong in [other_identity.clone(), changed_scalar] {
        assert!(!context.satisfies_fact(&wrong, &assumptions));
        assert!(!c_resources_directly_match(
            owned.resource(),
            wrong.resource(),
            &assumptions
        ));
    }
    assert!(
        context
            .clone()
            .try_compose_with_fact(other_identity, &assumptions)
            .is_ok()
    );
    assert!(
        context
            .without_fact_incrementally(&equal_state, &assumptions)
            .unwrap()
            .facts()
            .is_empty()
    );
}

#[test]
fn resource_instance_projections_use_owned_current_or_explicit_entry_state() {
    let ty = resource_index_type("Mark", vec![]);
    let m = resource_index_variable(&ty, 1);
    let n = resource_index_variable(&ty, 2);
    let state = |model, revision| {
        CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own(CResource::Instance(field_instance(10, model, revision))),
        ))
    };
    let entry = state(m.clone(), 3);
    let current = state(n.clone(), 4);
    let empty = PureFactContext::new();
    for (at_entry, expected) in [(false, 4), (true, 3)] {
        let expression = SpecExpression::ResourceField {
            projection: ResourceFieldProjection {
                identity: Variable(10),
                children: vec![],
                field_index: 1,
                at_entry,
            },
            c_type: CType::Int32,
        };
        let paths = crate::kernel::spec::evaluate_spec_expression_paths_with_loop_entry(
            &current,
            &expression,
            Some(&entry),
            &empty,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(paths.len(), 1);
        assert_eq!(paths[0].value, int32(expected));
        assert!(paths[0].facts.is_empty() && paths[0].obligations.is_empty());
    }
    let projection = |at_entry| SpecAlgebraicExpression {
        algebraic_type: ty.clone(),
        node: SpecAlgebraicExpressionNode::ResourceField(ResourceFieldProjection {
            identity: Variable(10),
            children: vec![],
            field_index: 0,
            at_entry,
        }),
    };
    let claim = SpecProposition::AlgebraicComparison {
        left: projection(false),
        equal: true,
        right: projection(true),
    };
    let paths = crate::kernel::spec::lower_spec_proposition_at_state_with_loop_entry(
        &current,
        &claim,
        Some(&entry),
        &empty,
        &mut ExecutionBudget::default(),
    )
    .unwrap();
    assert_eq!(paths.len(), 1);
    assert!(
        !empty.proves(&paths[0].proposition),
        "ownership alone must not imply preservation"
    );
    let equal = empty
        .clone()
        .assume_proposition(Proposition::Equal(Term::Algebraic(n), Term::Algebraic(m)));
    assert!(equal.proves(&paths[0].proposition));
    let missing = CState::new();
    let application = |at_entry| SpecAlgebraicExpression {
        algebraic_type: ty.clone(),
        node: SpecAlgebraicExpressionNode::PureFunctionApplication {
            name: "symbolic_model_function".into(),
            arguments: vec![SpecPureFunctionArgument::Algebraic(projection(at_entry))],
        },
    };
    let application_claim = SpecProposition::AlgebraicComparison {
        left: application(false),
        equal: true,
        right: application(true),
    };
    for (state, should_hold) in [(&entry, true), (&current, false)] {
        let paths = crate::kernel::spec::lower_spec_proposition_at_state_with_loop_entry(
            state,
            &application_claim,
            Some(&entry),
            &empty,
            &mut ExecutionBudget::default(),
        )
        .unwrap();
        assert_eq!(empty.proves(&paths[0].proposition), should_hold);
    }
    for (state, old, claim) in [
        (&missing, Some(&entry), application_claim),
        (&current, None, claim.clone()),
        (&missing, Some(&entry), claim),
        (
            &missing,
            None,
            SpecProposition::AlgebraicComparison {
                left: projection(false),
                equal: true,
                right: projection(false),
            },
        ),
    ] {
        assert!(
            crate::kernel::spec::lower_spec_proposition_at_state_with_loop_entry(
                state,
                &claim,
                old,
                &empty,
                &mut ExecutionBudget::default()
            )
            .is_err()
        );
    }
    for (identity, field_index, c_type) in [
        (99, 1, CType::Int32),
        (10, 2, CType::Int32),
        (10, 0, CType::Int32),
        (10, 1, CType::UInt32),
    ] {
        let expression = SpecExpression::ResourceField {
            projection: ResourceFieldProjection {
                identity: Variable(identity),
                children: vec![],
                field_index,
                at_entry: false,
            },
            c_type,
        };
        assert!(
            crate::kernel::spec::evaluate_spec_expression_paths_with_loop_entry(
                &current,
                &expression,
                None,
                &empty,
                &mut ExecutionBudget::default()
            )
            .is_err()
        );
    }
}

#[test]
fn resource_instance_contract_selects_current_fields_without_promising_preservation() {
    let ty = resource_index_type("Mark", vec![]);
    let before = field_instance(10, resource_index_variable(&ty, 1), 3);
    let after = field_instance(10, resource_index_variable(&ty, 2), 4);
    let requirement = CResourceSpec::instance(
        before.identity(),
        "cell".into(),
        before.schema().clone(),
        CResourceSpec::composite(
            CResourceAccessMode::Own,
            "marked_cell".into(),
            vec![CExpression::Value(int32(7))],
            vec![CType::Int32],
        ),
        CResourceTransferRole::Borrow,
        CResourceSnapshot::Current,
    )
    .unwrap();
    for instance in [before, after] {
        let fact = CResourceFact::own(CResource::Instance(instance));
        let state = CState::new()
            .with_resource_context(ResourceContext::new().unchecked_with_fact(fact.clone()));
        let selected = crate::kernel::functions::evaluate_function_resource_spec(
            &state,
            &requirement,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
        .unwrap();
        assert_eq!(selected, fact);
    }
    assert!(
        crate::kernel::functions::evaluate_function_resource_spec(
            &CState::new(),
            &requirement,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
        .is_err()
    );
}

#[test]
fn resource_instance_lookup_and_transfer_scale_by_identity() {
    let ty = resource_index_type("Mark", vec![]);
    let m = resource_index_variable(&ty, 1);
    let n = resource_index_variable(&ty, 2);
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Equal(
        Term::Algebraic(m.clone()),
        Term::Algebraic(n.clone()),
    ));
    let selected = CResourceFact::own(CResource::Instance(field_instance(1, n, 0)));
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let (context, build_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut context = ResourceContext::new();
            for identity in 1..=size {
                context = context
                    .try_compose_into_valid_context_delaying_normalization(
                        [CResourceFact::own(CResource::Instance(field_instance(
                            identity,
                            m.clone(),
                            0,
                        )))],
                        &assumptions,
                    )
                    .unwrap();
            }
            context
        });
        assert!(context.shares_storage_with(&context.clone()));
        let bindings = std::sync::Arc::new(
            (1..=size)
                .map(|id| (Variable(size + id), Variable(id)))
                .collect(),
        );
        let mut state = CState::new().with_resource_context(context.clone());
        state.resource_bindings = Some(bindings);
        let snapshot = state.clone();
        assert!(std::sync::Arc::ptr_eq(
            state.resource_bindings.as_ref().unwrap(),
            snapshot.resource_bindings.as_ref().unwrap()
        ));
        let (remaining, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                state
                    .owned_resource_instance(Variable(size + 1))
                    .unwrap()
                    .identity(),
                Variable(1)
            );
            // A formal absent from the map must not fall back to a caller ID.
            assert!(state.owned_resource_instance(Variable(1)).is_none());
            let mut missing = snapshot.clone();
            missing.resources = ResourceContext::new();
            assert!(
                missing
                    .owned_resource_instance(Variable(size + 1))
                    .is_none()
            );
            assert!(context.owned_instance(Variable(1)).is_some());
            assert!(context.owned_instance(Variable(size + 1)).is_none());
            assert!(context.satisfies_fact(&selected, &assumptions));
            context
                .without_fact_delaying_normalization(&selected, &assumptions)
                .unwrap()
        });
        assert_eq!(remaining.facts().len(), size as usize - 1);
        samples.push((build_work, query_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].0 <= pair[0].0 * 3 + 16,
            "instance build scaling: {samples:?}"
        );
        assert!(
            pair[1].1 <= pair[0].1 + 64,
            "fixed identity query scaling: {samples:?}"
        );
    }
}

#[test]
fn resource_instance_substitution_preserves_identity_without_memory_authority() {
    let pointer = Pointer::symbolic(Variable(10));
    let target = Pointer {
        block: "instance-target".into(),
        offset: PointerOffsetTerm::Constant(12),
    };
    let ty = resource_index_type(
        "Payload",
        vec![
            AlgebraicValueType::C(CValue::pointer(pointer.clone()).c_type()),
            AlgebraicValueType::C(CType::Int32),
        ],
    );
    let make = |p: Pointer, value: Bitvector32Term| {
        let model = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Set".into(),
                fields: vec![CValue::pointer(p.clone()).into(), int32(value).into()],
            },
        };
        let mut instance = field_instance(10, model, 0);
        instance.arguments = vec![CValue::pointer(p).into()].into();
        CResource::Instance(instance)
    };
    let source = make(pointer.clone(), Bitvector32Term::Variable(Variable(11)));
    let context = ResourceContext::new().unchecked_with_fact(CResourceFact::own(source.clone()));
    let assumptions = PureFactContext::new();
    for required in [
        CResourceFact::view_memory(memory_range(pointer.clone(), 0, 1)),
        CResourceFact::own_memory(memory_range(pointer, 0, 1)),
    ] {
        assert!(!context.satisfies_fact(&required, &assumptions));
    }
    let numeric = crate::kernel::reasoning::substitute_bitvector_variable_in_c_resource(
        &source,
        Variable(11),
        &Bitvector32Term::Constant(7),
    );
    let substituted = crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
        &Proposition::CResourceComposition(
            ResourceContext::new().unchecked_with_fact(CResourceFact::own(numeric)),
        ),
        Variable(10),
        &target,
    );
    let expected = Proposition::CResourceComposition(ResourceContext::new().unchecked_with_fact(
        CResourceFact::own(make(target, Bitvector32Term::Constant(7))),
    ));
    assert_eq!(
        substituted, expected,
        "C substitutions must not rename the resource identity"
    );
}

#[test]
fn resource_field_schemas_are_typed_shared_and_non_countable() {
    let fields = vec![
        (
            "model".into(),
            ResourceFieldType::Algebraic(resource_index_type("Mark", vec![])),
        ),
        ("revision".into(), ResourceFieldType::C(CType::Int32)),
    ];
    let schema = ResourceFieldSchema::new(fields.clone()).unwrap();
    assert_eq!(schema.fields(), fields);
    assert!(!schema.is_countable());
    let copy = schema.clone();
    assert!(std::ptr::eq(
        schema.fields().as_ptr(),
        copy.fields().as_ptr()
    ));
    assert!(ResourceFieldSchema::new(vec![]).unwrap().is_countable());
    assert!(ResourceFieldSchema::new(vec![fields[0].clone(), fields[0].clone()]).is_none());
    assert!(
        ResourceFieldSchema::new(vec![("".into(), ResourceFieldType::C(CType::Int32))]).is_none()
    );
    for ty in [
        CType::Void,
        CType::Int32Array(3),
        CType::FunctionPointer(CallbackSignature::from_encoded(1)),
    ] {
        assert!(ResourceFieldSchema::new(vec![("bad".into(), ResourceFieldType::C(ty))]).is_none());
    }
    let mut malformed = resource_index_type("Mark", vec![]);
    malformed.name = "Wrong".into();
    assert!(
        ResourceFieldSchema::new(vec![(
            "bad".into(),
            ResourceFieldType::Algebraic(malformed)
        )])
        .is_none()
    );
}

#[test]
fn resource_field_schema_clones_share_storage_at_multiple_sizes() {
    for size in [16, 32, 64, 128] {
        let schema = ResourceFieldSchema::new(
            (0..size)
                .map(|i| (format!("field_{i}"), ResourceFieldType::C(CType::Int32)))
                .collect(),
        )
        .unwrap();
        for _ in 0..size {
            let copy = schema.clone();
            assert_eq!(copy.fields().len(), size);
            assert!(
                std::ptr::eq(schema.fields().as_ptr(), copy.fields().as_ptr()),
                "cloning declaration metadata must not copy any field entries"
            );
        }
    }
}

fn resource_index_type(name: &str, fields: Vec<AlgebraicValueType>) -> AlgebraicType {
    let variants: std::sync::Arc<[AlgebraicVariantType]> = vec![
        AlgebraicVariantType {
            name: "Clear".into(),
            fields: vec![],
        },
        AlgebraicVariantType {
            name: "Set".into(),
            fields,
        },
    ]
    .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: name.into(),
        arguments: vec![],
    };
    AlgebraicType {
        rigid: false,
        name: name.into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

fn resource_index_variable(ty: &AlgebraicType, id: u64) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Variable(Variable(id)),
    }
}

fn indexed_resource(index: AlgebraicTerm, composite: bool) -> CResource {
    let arguments = vec![AlgebraicValue::Algebraic(index)].into();
    if composite {
        CResource::Composite {
            name: "indexed".into(),
            arguments,
        }
    } else {
        CResource::Token {
            name: "indexed".into(),
            arguments,
        }
    }
}

#[test]
fn symbolic_resource_indices_preserve_types_equality_and_linear_transfer() {
    let ty = resource_index_type("Mark", vec![]);
    let m = resource_index_variable(&ty, 990_001);
    let n = resource_index_variable(&ty, 990_002);
    let other = resource_index_variable(&resource_index_type("Other", vec![]), 990_001);
    for composite in [false, true] {
        let owned = CResourceFact::own(indexed_resource(m.clone(), composite));
        let renamed = CResourceFact::own(indexed_resource(n.clone(), composite));
        let wrong_type = CResourceFact::own(indexed_resource(other.clone(), composite));
        let facts = ResourceContext::new().unchecked_with_fact(owned.clone());
        let empty = PureFactContext::new();
        assert!(facts.satisfies_fact(&owned, &empty));
        assert!(!facts.satisfies_fact(&renamed, &empty));
        assert!(!facts.satisfies_fact(&wrong_type, &empty));
        assert!(!facts.satisfies_fact(
            &CResourceFact::own_quantity(owned.resource().clone(), Bitvector32Term::Constant(2)),
            &empty,
        ));
        assert!(
            !ResourceContext::new()
                .unchecked_with_fact(CResourceFact::View(owned.resource().clone()))
                .satisfies_fact(&owned, &empty)
        );

        for equality in [
            Proposition::Equal(Term::Algebraic(m.clone()), Term::Algebraic(n.clone())),
            Proposition::Equal(Term::Algebraic(n.clone()), Term::Algebraic(m.clone())),
            Proposition::ConditionIs(
                ConditionTerm::AlgebraicEqual(Box::new(m.clone()), Box::new(n.clone())),
                true,
            ),
        ] {
            let assumptions = empty.clone().assume_proposition(equality);
            assert!(facts.satisfies_fact(&renamed, &assumptions));
            assert!(c_resources_directly_match(
                owned.resource(),
                renamed.resource(),
                &assumptions
            ));
            let remaining = facts
                .clone()
                .without_fact_delaying_normalization(&renamed, &assumptions)
                .expect("an equal index should transfer the same unit");
            assert!(remaining.is_empty());
            assert!(!remaining.satisfies_fact(&owned, &assumptions));
            assert!(!remaining.satisfies_fact(&renamed, &assumptions));
        }
    }
}

#[test]
fn symbolic_resource_indices_distinguish_constructors_and_population_counts() {
    let ty = resource_index_type("Mark", vec![]);
    let constructor = |variant: &str| AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: variant.into(),
            fields: vec![],
        },
    };
    let clear = indexed_resource(constructor("Clear"), false);
    let set = indexed_resource(constructor("Set"), false);
    assert!(!c_resources_directly_match(
        &clear,
        &set,
        &PureFactContext::new()
    ));

    let m = resource_index_variable(&ty, 990_010);
    let n = resource_index_variable(&ty, 990_011);
    let arguments: ResourceArguments = vec![AlgebraicValue::Algebraic(m.clone())].into();
    let n_arguments = vec![AlgebraicValue::Algebraic(n.clone())];
    let state = CState::new().with_counted_population(
        "indexed",
        arguments.clone(),
        Bitvector32Term::Constant(3),
    );
    assert_eq!(
        state.counted_population("indexed", &arguments),
        Some(&Bitvector32Term::Constant(3))
    );
    assert!(state.counted_population("indexed", &n_arguments).is_none());
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::Equal(Term::Algebraic(m), Term::Algebraic(n)));
    let (_, recovered, count) = state
        .counted_population_proven_equal("indexed", &n_arguments, &assumptions)
        .unwrap();
    assert!(std::sync::Arc::ptr_eq(&arguments, &recovered));
    assert_eq!(count, Bitvector32Term::Constant(3));
    assert_eq!(
        state.counted_population_sum("indexed", &[None], &assumptions),
        count
    );
    assert_eq!(
        state.counted_population_sum("indexed", &[Some(n_arguments[0].clone())], &assumptions),
        count
    );
}

#[test]
fn symbolic_resource_indices_substitute_nested_payloads_without_memory_authority() {
    let pointer = Pointer::symbolic(Variable(990_020));
    let target = Pointer {
        block: "indexed-target".into(),
        offset: PointerOffsetTerm::Constant(12),
    };
    let ty = resource_index_type(
        "Payload",
        vec![
            AlgebraicValueType::C(CValue::pointer(pointer.clone()).c_type()),
            AlgebraicValueType::C(CType::Int32),
        ],
    );
    let model = |p: Pointer, value: Bitvector32Term| AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Set".into(),
            fields: vec![
                AlgebraicValue::C(CValue::pointer(p)),
                AlgebraicValue::C(int32(value)),
            ],
        },
    };
    let value = Bitvector32Term::Variable(Variable(990_021));
    let original = indexed_resource(model(pointer.clone(), value.clone()), false);
    let context = ResourceContext::new().unchecked_with_fact(CResourceFact::own(original.clone()));
    let empty = PureFactContext::new();
    let memory = memory_range(pointer, 0, 1);
    assert!(!context.satisfies_fact(&CResourceFact::view_memory(memory.clone()), &empty));
    assert!(!context.satisfies_fact(&CResourceFact::own_memory(memory), &empty));

    let numeric = crate::kernel::reasoning::substitute_bitvector_variable_in_c_resource(
        &original,
        Variable(990_021),
        &Bitvector32Term::Constant(7),
    );
    let source = Proposition::CResourceComposition(
        ResourceContext::new().unchecked_with_fact(CResourceFact::own(numeric)),
    );
    let substituted = crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
        &source,
        Variable(990_020),
        &target,
    );
    let expected = Proposition::CResourceComposition(ResourceContext::new().unchecked_with_fact(
        CResourceFact::own(indexed_resource(
            model(target, Bitvector32Term::Constant(7)),
            false,
        )),
    ));
    assert_eq!(substituted, expected);
}

#[test]
fn symbolic_resource_indices_share_snapshots_and_scale_with_indexed_context() {
    let ty = resource_index_type("Mark", vec![]);
    let selected = CResourceFact::own(indexed_resource(
        resource_index_variable(&ty, 991_000),
        false,
    ));
    let renamed = CResourceFact::own(indexed_resource(
        resource_index_variable(&ty, 991_001),
        false,
    ));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Equal(
        Term::Algebraic(resource_index_variable(&ty, 991_000)),
        Term::Algebraic(resource_index_variable(&ty, 991_001)),
    ));
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let (_, build_work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut context = ResourceContext::new();
            for i in 0..size {
                let fact = CResourceFact::own(CResource::Token {
                    name: format!("indexed_{i}"),
                    arguments: vec![AlgebraicValue::Algebraic(resource_index_variable(
                        &ty,
                        992_000 + i,
                    ))]
                    .into(),
                });
                let cloned = fact.clone();
                let (CResource::Token { arguments: a, .. }, CResource::Token { arguments: b, .. }) =
                    (fact.resource(), cloned.resource())
                else {
                    unreachable!()
                };
                assert!(std::sync::Arc::ptr_eq(a, b));
                context = context.unchecked_with_fact(fact);
            }
            context
        });
        let context = unrelated_token_context(size as usize).unchecked_with_fact(selected.clone());
        let (remaining, transfer_work) = crate::instrumentation::measure_deterministic_work(|| {
            context.without_fact_delaying_normalization(&renamed, &assumptions)
        });
        assert_eq!(remaining.unwrap().facts().len(), size as usize);
        samples.push((size, build_work, transfer_work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3).saturating_add(16),
            "building ADT-indexed resources: {samples:?}"
        );
        assert!(
            pair[1].2 <= pair[0].2.saturating_mul(2).saturating_add(16),
            "fixed indexed transfer: {samples:?}"
        );
    }
}

#[test]
fn symbolic_resource_indices_exact_transfer_scales_with_same_family_indices() {
    let ty = resource_index_type("Mark", vec![]);
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let selected = CResourceFact::own(indexed_resource(resource_index_variable(&ty, 1), false));
        let context = ResourceContext::new().unchecked_with_facts((1..=size).map(|id| {
            CResourceFact::own(indexed_resource(resource_index_variable(&ty, id), false))
        }));
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.without_fact_delaying_normalization(&selected, &PureFactContext::new())
        });
        assert_eq!(remaining.unwrap().facts().len(), size as usize - 1);
        samples.push((size, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(2).saturating_add(16),
            "exact ADT index lookup: {samples:?}"
        );
    }
}

#[test]
fn symbolic_resource_indices_clone_recursive_models_by_sharing() {
    let ty = resource_index_type(
        "Chain",
        vec![AlgebraicValueType::Algebraic {
            name: "Chain".into(),
            arguments: vec![],
        }],
    );
    for size in [8, 16, 32, 64] {
        let mut model = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Clear".into(),
                fields: vec![],
            },
        };
        for _ in 0..size {
            model = AlgebraicTerm {
                algebraic_type: ty.clone(),
                node: AlgebraicTermNode::Constructor {
                    variant: "Set".into(),
                    fields: vec![AlgebraicValue::Algebraic(model)],
                },
            };
        }
        assert!(model.is_well_formed());
        let resource = indexed_resource(model, false);
        let cloned = resource.clone();
        let (
            CResource::Token {
                arguments: left, ..
            },
            CResource::Token {
                arguments: right, ..
            },
        ) = (&resource, &cloned)
        else {
            unreachable!()
        };
        assert!(std::sync::Arc::ptr_eq(left, right));
    }
}

fn unrelated_token_context(size: usize) -> ResourceContext {
    ResourceContext::new().unchecked_with_facts(
        (0..size).map(|index| {
            CResourceFact::own_token(format!("token_{index}"), vec![int32(index as u32)])
        }),
    )
}

fn equality(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
        true,
    )
}

#[test]
fn zero_owned_resource_is_identity_after_symbolic_resolution() {
    let quantity = Bitvector32Term::Variable(Variable(910_000));
    let intermediate = Bitvector32Term::Variable(Variable(910_001));
    let assumptions = PureFactContext::new()
        .assume_proposition(equality(quantity.clone(), intermediate.clone()))
        .assume_proposition(equality(intermediate, Bitvector32Term::Constant(0)));
    let required = CResourceFact::own_quantity(
        CResource::Token {
            name: "empty".to_string(),
            arguments: vec![int32(7).into()].into(),
        },
        quantity,
    );
    let empty = ResourceContext::new();

    assert!(empty.satisfies_fact(&required, &assumptions));
    let remaining = empty
        .clone()
        .without_fact_delaying_normalization(&required, &assumptions)
        .expect("consuming a symbolically zero resource must be an identity");
    assert!(remaining.is_empty());

    let positive =
        CResourceFact::own_quantity(required.resource().clone(), Bitvector32Term::Constant(1));
    assert!(!empty.satisfies_fact(&positive, &assumptions));
    assert!(
        empty
            .without_fact_delaying_normalization(&positive, &assumptions)
            .is_none()
    );
}

#[test]
fn zero_resource_identity_ignores_unrelated_resources() {
    let quantity = Bitvector32Term::Variable(Variable(911_000));
    let intermediate = Bitvector32Term::Variable(Variable(911_001));
    let assumptions = PureFactContext::new()
        .assume_proposition(equality(quantity.clone(), intermediate.clone()))
        .assume_proposition(equality(intermediate, Bitvector32Term::Constant(0)));
    let required = CResourceFact::own_quantity(
        CResource::Token {
            name: "empty".to_string(),
            arguments: vec![int32(7).into()].into(),
        },
        quantity,
    );
    let samples = [16, 64, 256, 1024]
        .into_iter()
        .map(|size| {
            let context = unrelated_token_context(size);
            let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
                context
                    .clone()
                    .without_fact_delaying_normalization(&required, &assumptions)
            });
            assert_eq!(remaining.expect("zero consumption should succeed"), context);
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "zero-resource identity work changed with unrelated resources: {samples:?}"
    );
}

#[test]
fn zero_resource_count_witness_needs_no_population_bucket() {
    let resource = CResourceFact::own_quantity(
        CResource::Composite {
            name: "empty".to_string(),
            arguments: vec![int32(7).into()].into(),
        },
        Bitvector32Term::Constant(0),
    );
    let claim = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(claim.clone());
    assert!(
        prove_owned_resource_count_lower_bound(&CState::new(), &resource, &claim, &assumptions,)
            .is_some()
    );
}

#[test]
fn owned_resource_invariant_theorems_retain_context_premises() {
    let quantity = Bitvector32Term::Variable(Variable(912_000));
    let count = Bitvector32Term::Variable(Variable(912_001));
    let resource = CResourceFact::own_quantity(
        CResource::Token {
            name: "symbolic".to_string(),
            arguments: vec![int32(7).into()].into(),
        },
        quantity.clone(),
    );
    let state = CState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(resource.clone()))
        .with_counted_population("symbolic", vec![int32(7).into()].into(), count.clone());
    let count_claim = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(quantity.clone(), count),
        true,
    );
    let nonnegative_claim = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), quantity),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(count_claim.clone())
        .assume_proposition(nonnegative_claim.clone());

    let count_theorem =
        prove_owned_resource_count_lower_bound(&state, &resource, &count_claim, &assumptions)
            .expect("the count invariant should be certified");
    let nonnegative_theorem = prove_owned_resource_quantity_nonnegative(
        &state,
        &resource,
        &nonnegative_claim,
        &assumptions,
    )
    .expect("the quantity invariant should be certified");

    for (theorem, conclusion) in [
        (&count_theorem, &count_claim),
        (&nonnegative_theorem, &nonnegative_claim),
    ] {
        let Proposition::Implies(premise, body) = theorem.proposition() else {
            panic!("contextual resource theorem must retain its implication premise");
        };
        assert_eq!(premise.as_ref(), conclusion);
        assert_eq!(body.as_ref(), conclusion);
    }
}

#[test]
fn owned_resource_invariant_theorems_do_not_search_the_context() {
    let quantity = Bitvector32Term::Variable(Variable(912_010));
    let middle = Bitvector32Term::Variable(Variable(912_011));
    let count = Bitvector32Term::Variable(Variable(912_012));
    let resource = CResourceFact::own_quantity(
        CResource::Token {
            name: "symbolic_no_search".to_string(),
            arguments: vec![int32(7).into()].into(),
        },
        quantity.clone(),
    );
    let state = CState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(resource.clone()))
        .with_counted_population(
            "symbolic_no_search",
            vec![int32(7).into()].into(),
            count.clone(),
        );
    let claim = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(quantity.clone(), count.clone()),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(quantity, middle.clone()),
            true,
        ))
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(middle, count),
            true,
        ));

    assert!(assumptions.proves(&claim));
    assert!(
        prove_owned_resource_count_lower_bound(&state, &resource, &claim, &assumptions).is_none(),
        "a resource theorem constructor must not turn an unrecorded contextual search into authority"
    );
}

#[test]
fn resource_context_fork_updates_are_persistent_and_logarithmic() {
    for size in [16_usize, 64, 256, 1024, 4096] {
        let context = unrelated_token_context(size);
        let ancestor = context.clone();
        assert!(context.shares_storage_with(&ancestor));
        assert!(context.storage.materialized.get().is_none());

        let added = CResourceFact::own_token("target".to_string(), vec![int32(size as u32)]);
        let before_insert = crate::persistent::persistent_node_allocations();
        let successor = context.unchecked_with_fact(added.clone());
        let insert_allocations = crate::persistent::persistent_node_allocations() - before_insert;
        let logarithmic_height = usize::BITS as usize - size.leading_zeros() as usize;
        let update_bound = 64 * logarithmic_height + 64;
        assert!(
            insert_allocations <= update_bound,
            "size {size} resource insertion allocated {insert_allocations} persistent nodes (bound {update_bound})"
        );
        assert_eq!(ancestor.storage.facts.len(), size);
        assert!(!ancestor.satisfies_fact(&added, &PureFactContext::new()));

        let before_lookup = crate::persistent::persistent_node_allocations();
        assert!(successor.satisfies_fact(&added, &PureFactContext::new()));
        assert_eq!(
            crate::persistent::persistent_node_allocations() - before_lookup,
            0,
            "exact lookup must not rebuild a size-{size} resource index"
        );
        assert!(successor.storage.materialized.get().is_none());

        let before_remove = crate::persistent::persistent_node_allocations();
        let removed = successor
            .without_exact_representation(&added)
            .expect("the inserted resource should be removable");
        let remove_allocations = crate::persistent::persistent_node_allocations() - before_remove;
        assert!(
            remove_allocations <= update_bound,
            "size {size} resource removal allocated {remove_allocations} persistent nodes (bound {update_bound})"
        );
        assert_eq!(removed.facts(), ancestor.facts());
        assert!(ancestor.satisfies_fact(
            &CResourceFact::own_token("token_0".to_string(), vec![int32(0)]),
            &PureFactContext::new(),
        ));
    }
}

#[test]
fn consuming_support_removes_only_its_derived_views() {
    let authority = CResourceFact::own_composite("authority".to_string(), Vec::new());
    let view = CResourceFact::view_token("derived".to_string(), vec![int32(7)]);
    let context = ResourceContext::new()
        .unchecked_with_fact(view.clone())
        .unchecked_with_fact(authority.clone())
        .unchecked_with_supported_facts(&authority, [view.clone()]);
    assert_eq!(
        context
            .storage
            .index
            .exact
            .get(&view)
            .map_or(0, |entries| entries.len()),
        2,
        "an explicit view and a supported projection are distinct capabilities"
    );

    let remaining = context
        .without_exact_representation(&authority)
        .expect("the authority should be removable");
    assert_eq!(remaining.facts(), [view]);
    assert!(remaining.storage.supported_by.is_empty());
    assert!(remaining.storage.projections_by_support.is_empty());
}

#[test]
fn normalization_preserves_projection_support() {
    let authority = CResourceFact::own_composite("authority".to_string(), Vec::new());
    let view = CResourceFact::view_token("derived".to_string(), vec![int32(7)]);
    let expanded = CResourceFact::own_token("expanded".to_string(), vec![int32(9)]);
    let context = ResourceContext::new()
        .unchecked_with_fact(authority.clone())
        .unchecked_with_supported_facts(&authority, [view])
        .with_cached_supported_expansion(&authority, vec![expanded.clone()])
        .normalized(&PureFactContext::new());
    assert_eq!(
        context.cached_supported_expansion(&authority),
        Some([expanded].as_slice())
    );

    let remaining = context
        .without_exact_representation(&authority)
        .expect("normalization should retain the authority");
    assert!(remaining.is_empty());
    assert!(remaining.storage.expansions_by_support.is_empty());
}

#[test]
fn cached_projection_finds_the_owned_resource_that_packages_a_fact() {
    let authority = CResourceFact::own_composite("authority".to_string(), Vec::new());
    let allocation = CResourceFact::own_token(
        CResourceFact::ALLOCATION_RESOURCE_NAME.to_string(),
        vec![
            CValue::pointer(Pointer {
                block: "allocation".into(),
                offset: PointerOffsetTerm::Constant(0),
            }),
            int32(16),
        ],
    );
    let allocation_view = allocation.core().expect("owned allocation has a view core");
    let context = ResourceContext::new()
        .unchecked_with_fact(authority.clone())
        .unchecked_with_supported_facts(&authority, [allocation_view])
        .with_cached_supported_expansion(&authority, vec![allocation.clone()]);

    assert_eq!(
        context.cached_support_exposing_fact(&allocation, &PureFactContext::new()),
        Some(&authority),
        "the exact core projection should index its certified owned expansion",
    );
}

#[test]
fn support_removal_visits_only_the_supported_projections() {
    const PROJECTION_COUNT: usize = 8;
    for size in [16_usize, 64, 256, 1024, 4096] {
        let authority =
            CResourceFact::own_composite("authority".to_string(), vec![int32(size as u32)]);
        let projections = (0..PROJECTION_COUNT)
            .map(|index| {
                CResourceFact::view_token(format!("projection_{index}"), vec![int32(size as u32)])
            })
            .collect::<Vec<_>>();
        let context = unrelated_token_context(size)
            .unchecked_with_fact(authority.clone())
            .unchecked_with_supported_facts(&authority, projections.clone());
        let ancestor = context.clone();

        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .without_exact_representation(&authority)
                .expect("the authority should be removable")
        });
        assert_eq!(
            work, PROJECTION_COUNT,
            "retiring support in a size-{size} context must visit only its projections"
        );
        assert_eq!(remaining.facts().len(), size);
        assert_eq!(ancestor.facts().len(), size + PROJECTION_COUNT + 1);
        for projection in projections {
            assert!(!remaining.satisfies_fact(&projection, &PureFactContext::new()));
        }
    }
}

#[test]
fn resource_join_preserves_only_common_projection_support() {
    let authority = CResourceFact::own_composite("authority".to_string(), Vec::new());
    let view = CResourceFact::view_token("derived".to_string(), Vec::new());
    let expansion = vec![CResourceFact::own_token("expanded".to_string(), Vec::new())];
    let root = ResourceContext::new().unchecked_with_fact(authority.clone());
    let left = root
        .clone()
        .unchecked_with_supported_facts(&authority, [view.clone()])
        .with_cached_supported_expansion(&authority, expansion.clone());
    let right = root
        .clone()
        .unchecked_with_supported_facts(&authority, [view.clone()])
        .with_cached_supported_expansion(&authority, expansion);
    let common = ResourceContext::common_exact_descendant(&left, &right, &root)
        .expect("both contexts descend from the same root");
    assert_eq!(
        common.cached_supported_expansion(&authority).unwrap().len(),
        1
    );
    assert!(
        common
            .without_exact_representation(&authority)
            .expect("the common authority should be removable")
            .is_empty(),
        "a projection supported in both branches must remain supported"
    );

    let explicit_right = root.clone().unchecked_with_fact(view);
    let mixed = ResourceContext::common_exact_descendant(&left, &explicit_right, &root)
        .expect("both contexts descend from the same root");
    assert_eq!(mixed.facts(), [authority]);
    assert!(mixed.storage.expansions_by_support.is_empty());
}

#[test]
fn resource_common_descendant_visits_only_branch_local_changes() {
    let left_path = CResourceFact::own_token("left_path".to_string(), Vec::new());
    let right_path = CResourceFact::own_token("right_path".to_string(), Vec::new());
    let permit = CResourceFact::own_token("permit".to_string(), Vec::new());
    let ready = CResourceFact::own_composite("ready".to_string(), Vec::new());
    let mut samples = Vec::new();

    for size in [16_usize, 64, 256, 1024, 4096] {
        let root = unrelated_token_context(size)
            .unchecked_with_fact(left_path.clone())
            .unchecked_with_fact(right_path.clone())
            .unchecked_with_fact(permit.clone());
        let assumptions = PureFactContext::new();
        let normalized_root = root.clone().normalized(&assumptions);
        assert!(
            normalized_root.shares_storage_with(&root),
            "no-op normalization must preserve a size-{size} snapshot by identity"
        );
        let left = root
            .clone()
            .without_fact(&left_path, &assumptions)
            .expect("left path should be consumable")
            .without_fact(&permit, &assumptions)
            .expect("left permit should be consumable")
            .unchecked_with_fact(ready.clone());
        let right = root
            .clone()
            .without_fact(&right_path, &assumptions)
            .expect("right path should be consumable")
            .without_fact(&permit, &assumptions)
            .expect("right permit should be consumable")
            .unchecked_with_fact(ready.clone());
        assert!(left.descends_from(&root));
        assert!(right.descends_from(&root));
        assert!(left.storage.materialized.get().is_none());
        assert!(right.storage.materialized.get().is_none());

        let before = crate::persistent::persistent_node_allocations();
        let common = ResourceContext::common_exact_descendant(&left, &right, &root)
            .expect("both branch contexts should retain their shared root");
        samples.push((
            size,
            usize::BITS as usize - size.leading_zeros() as usize,
            crate::persistent::persistent_node_allocations() - before,
        ));
        assert!(common.contains_exact_representation(&ready));
        assert!(!common.contains_exact_representation(&left_path));
        assert!(!common.contains_exact_representation(&right_path));
        assert!(!common.contains_exact_representation(&permit));
        for index in [0, size / 2, size - 1] {
            assert!(
                common.contains_exact_representation(&CResourceFact::own_token(
                    format!("token_{index}"),
                    vec![int32(index as u32)],
                ))
            );
        }
    }

    let (_, base_height, base_allocations) = samples[0];
    for (size, height, allocations) in samples {
        let bound = base_allocations + 64 * (height - base_height);
        assert!(
            allocations <= bound,
            "size {size} common resource descendant allocated {allocations} persistent nodes (bound {bound})"
        );
    }

    let unrelated = ResourceContext::new().unchecked_with_fact(ready);
    let root = ResourceContext::new();
    assert!(ResourceContext::common_exact_descendant(&unrelated, &unrelated, &root).is_none());

    let unit = CResourceFact::own_token("mergeable".to_string(), Vec::new());
    let merged = CResourceFact::own_quantity(
        CResource::Token {
            name: "mergeable".to_string(),
            arguments: Vec::new().into(),
        },
        Bitvector32Term::Constant(2),
    );
    let left = root
        .clone()
        .unchecked_with_fact(unit.clone())
        .unchecked_with_fact(unit.clone())
        .normalized(&PureFactContext::new());
    let right = root
        .clone()
        .unchecked_with_fact(unit.clone())
        .unchecked_with_fact(unit)
        .normalized(&PureFactContext::new());
    assert!(left.descends_from(&root));
    assert!(right.descends_from(&root));
    let common = ResourceContext::common_exact_descendant(&left, &right, &root)
        .expect("normalization should preserve changed-fact ancestry");
    assert!(common.contains_exact_representation(&merged));

    let duplicate = CResourceFact::own_token("duplicate".to_string(), Vec::new());
    let duplicate_root = ResourceContext::new()
        .unchecked_with_fact(duplicate.clone())
        .unchecked_with_fact(duplicate.clone());
    let duplicate_left = duplicate_root.clone();
    let duplicate_right = duplicate_root
        .clone()
        .without_exact_representation(&duplicate)
        .expect("one duplicate should be removable");
    let duplicate_common = ResourceContext::common_exact_descendant(
        &duplicate_left,
        &duplicate_right,
        &duplicate_root,
    )
    .expect("a one-sided removal should retain common ancestry");
    assert_eq!(
        duplicate_common
            .storage
            .index
            .exact
            .get(&duplicate)
            .map_or(0, |entries| entries.len()),
        1,
        "the exact common descendant must retain the minimum multiplicity"
    );
}

#[test]
fn resource_memory_block_and_interval_indexes_update_logarithmically() {
    for size in [16_usize, 64, 256, 1024, 4096] {
        let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
            CResourceFact::own_memory(memory_range(
                Pointer {
                    block: format!("unrelated-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                0,
                1,
            ))
        }));
        let target = CResourceFact::own_memory(memory_range(
            Pointer {
                block: "target-block".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            7,
            11,
        ));
        let before = crate::persistent::persistent_node_allocations();
        let successor = context.clone().unchecked_with_fact(target.clone());
        let allocations = crate::persistent::persistent_node_allocations() - before;
        let logarithmic_height = usize::BITS as usize - size.leading_zeros() as usize;
        let update_bound = 128 * logarithmic_height + 128;
        assert!(
            allocations <= update_bound,
            "size {size} memory resource insertion allocated {allocations} persistent nodes (bound {update_bound})"
        );
        assert_eq!(successor.direct_match_candidates(&target).count(), 1);
        assert_eq!(context.direct_match_candidates(&target).count(), 0);

        let before_remove = crate::persistent::persistent_node_allocations();
        let removed = successor
            .without_exact_representation(&target)
            .expect("the inserted memory resource should be removable");
        let remove_allocations = crate::persistent::persistent_node_allocations() - before_remove;
        assert!(remove_allocations <= update_bound);
        assert_eq!(removed, context);
    }
}

#[test]
fn exact_resource_lookup_is_indexed_after_context_construction() {
    let required = CResourceFact::own_token("target".to_string(), vec![int32(0)]);
    for size in [16, 32, 64, 128] {
        let context = unrelated_token_context(size).unchecked_with_fact(required.clone());
        assert!(context.satisfies_fact(&required, &PureFactContext::new()));
        let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.satisfies_fact(&required, &PureFactContext::new())
        });
        assert!(satisfied);
        assert_eq!(
            work, 0,
            "indexed exact lookup scanned a size-{size} context"
        );
    }
}

#[test]
fn exact_owned_resource_satisfies_view_without_entailment_scan() {
    let range = memory_range(
        Pointer {
            block: "owned-view-target".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        8,
    );
    let owned = CResourceFact::own_memory(range.clone());
    let required = CResourceFact::view_memory(range);
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = unrelated_token_context(size).unchecked_with_fact(owned.clone());
            assert!(context.satisfies_fact(&required, &PureFactContext::new()));
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.satisfies_fact(&required, &PureFactContext::new())
            });
            assert!(satisfied);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "exact ownership-to-view lookup should ignore unrelated resources: {samples:?}"
    );
}

#[test]
fn direct_resource_match_candidates_ignore_unrelated_shapes_and_blocks() {
    let target = CResourceFact::own_token("target".to_string(), vec![int32(0)]);
    let target_memory = CResourceFact::view_memory(memory_range(
        Pointer {
            block: "target-block".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        1,
    ));
    let context = unrelated_token_context(128)
        .unchecked_with_facts((0..128).map(|index| {
            CResourceFact::view_memory(memory_range(
                Pointer {
                    block: format!("unrelated-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                0,
                1,
            ))
        }))
        .unchecked_with_fact(target.clone())
        .unchecked_with_fact(target_memory.clone());

    assert_eq!(context.direct_match_candidates(&target).count(), 1);
    assert_eq!(context.direct_match_candidates(&target_memory).count(), 1);
}

#[test]
fn nonexact_memory_entailment_ignores_unrelated_blocks() {
    let target_base = Pointer {
        block: "target-block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let required = CResourceFact::view_memory(memory_range(target_base.clone(), 2, 6));
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = ResourceContext::new()
                .unchecked_with_facts((0..size).map(|index| {
                    CResourceFact::view_memory(memory_range(
                        Pointer {
                            block: format!("unrelated-{index}").into(),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        0,
                        8,
                    ))
                }))
                .unchecked_with_fact(CResourceFact::own_memory(memory_range(
                    target_base.clone(),
                    0,
                    8,
                )));
            assert_eq!(context.direct_match_candidates(&required).count(), 1);
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.satisfies_fact(&required, &PureFactContext::new())
            });
            assert!(satisfied);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed memory entailment should not inspect unrelated blocks: {samples:?}"
    );
}

#[test]
fn unrelated_resource_normalization_has_linear_deterministic_work() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = unrelated_token_context(size);
            let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.normalized(&PureFactContext::new())
            });
            assert_eq!(normalized.facts().len(), size);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "resource normalization is superlinear: {samples:?}"
        );
    }
}

#[test]
fn adjacent_memory_normalization_has_linearithmic_deterministic_work() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let base = Pointer {
                block: "p".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_memory(memory_range(
                    base.clone(),
                    index as u32,
                    index as u32 + 1,
                ))
            }));
            let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.normalized(&PureFactContext::new())
            });
            assert_eq!(normalized.facts().len(), 1);
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "adjacent resource normalization is superlinear: {samples:?}"
        );
    }
}

#[test]
fn disjoint_concrete_range_validity_scales_near_linearly() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let base = Pointer {
                block: "p".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_memory(memory_range(
                    base.clone(),
                    (index * 2) as u32,
                    (index * 2 + 1) as u32,
                ))
            }));
            let (error, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.validity_error(&PureFactContext::new())
            });
            assert!(error.is_none());
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "concrete range validation is superlinear: {samples:?}"
        );
    }
}

#[test]
fn observable_structural_separation_does_not_materialize_owned_pairs() {
    for same_base in [false, true] {
        let samples = [16, 32, 64, 128]
            .into_iter()
            .map(|size| {
                let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                    CResourceFact::own_memory(memory_range(
                        Pointer {
                            block: if same_base {
                                "shared_block".into()
                            } else {
                                format!("block_{index}").into()
                            },
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        if same_base { (index * 2) as u32 } else { 0 },
                        if same_base { (index * 2 + 1) as u32 } else { 1 },
                    ))
                }));
                let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
                    context
                        .observable_facts(&PureFactContext::new())
                        .expect("structurally disjoint memory ranges should compose")
                });
                assert_eq!(facts.len(), 1, "size-{size} projection materialized pairs");
                assert!(matches!(facts[0], Proposition::CResourceComposition(_)));
                assert!(
                    PureFactContext::new().proves(&Proposition::CResourceSeparate {
                        left: context.facts()[0].resource().clone(),
                        right: context.facts()[size - 1].resource().clone(),
                    })
                );
                (size, work)
            })
            .collect::<Vec<_>>();
        for pair in samples.windows(2) {
            assert!(
                pair[1].1 <= pair[0].1.saturating_mul(3),
                "observable resource projection is superlinear: {samples:?}"
            );
        }
    }
}

#[test]
fn inserting_a_disjoint_concrete_range_uses_interval_neighbors() {
    for size in [16, 32, 64, 128] {
        let base = Pointer {
            block: "p".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
            CResourceFact::own_memory(memory_range(
                base.clone(),
                (index * 2) as u32,
                (index * 2 + 1) as u32,
            ))
        }));
        let next =
            CResourceFact::own_memory(memory_range(base, (size * 2) as u32, (size * 2 + 1) as u32));
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.try_compose_into_valid_context_delaying_normalization(
                std::iter::once(next),
                &PureFactContext::new(),
            )
        });
        assert!(result.is_ok());
        assert!(
            work <= size + 4,
            "indexed insertion did too much work for {size} existing ranges: {work}"
        );
    }
}

#[test]
fn installing_a_certified_resource_group_does_not_recheck_internal_pairs() {
    let base = Pointer {
        block: "certified_group".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    for size in [16, 64, 256, 1024] {
        let facts = (0..size)
            .map(|index| {
                CResourceFact::own_memory(memory_range(
                    base.clone(),
                    (index * 2) as u32,
                    (index * 2 + 1) as u32,
                ))
            })
            .collect::<Vec<_>>();
        ResourceContext::new()
            .try_compose_with_facts(facts.clone(), &PureFactContext::new())
            .expect("the resource group must be valid before it is certified");
        let (installed, work) = crate::instrumentation::measure_deterministic_work(|| {
            ResourceContext::new()
                .try_compose_certified_group_into_valid_context_delaying_normalization(
                    facts,
                    &PureFactContext::new(),
                )
        });
        assert!(installed.is_ok());
        assert_eq!(
            work, 0,
            "installing a certified size-{size} group rechecked its internal pairs"
        );
    }
}

#[test]
fn installing_a_certified_resource_group_still_checks_the_existing_frame() {
    let base = Pointer {
        block: "certified_group_cross_check".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let existing = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(base.clone(), 0, 2)));
    let overlapping = CResourceFact::own_memory(memory_range(base, 1, 3));
    let result = existing.try_compose_certified_group_into_valid_context_delaying_normalization(
        [overlapping],
        &PureFactContext::new(),
    );
    assert!(
        result.is_err(),
        "certification of a group's interior must not skip its boundary check"
    );
}

#[test]
fn resource_family_cores_are_view_facts() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };

    assert_eq!(
        view_memory_fact(base.clone(), 0, 1).core(),
        Some(view_memory_fact(base.clone(), 0, 1))
    );
    assert_eq!(
        own_memory_fact(base.clone(), 0, 1).core(),
        Some(view_memory_fact(base, 0, 1))
    );
    assert_eq!(
        CResourceFact::own_token("token".to_string(), vec![int32(0)]).core(),
        Some(CResourceFact::view_token(
            "token".to_string(),
            vec![int32(0)]
        ))
    );
    assert_eq!(
        CResourceFact::own_composite("box".to_string(), vec![int32(1)]).core(),
        Some(CResourceFact::view_composite(
            "box".to_string(),
            vec![int32(1)]
        ))
    );
}

#[test]
fn declared_resource_families_accumulate_equal_owned_units() {
    for fact in [
        CResourceFact::own_token("token".to_string(), vec![int32(0)]),
        CResourceFact::own_composite("box".to_string(), vec![int32(1)]),
    ] {
        let context = ResourceContext::new()
            .try_compose_with_facts([fact.clone(), fact.clone()], &PureFactContext::new())
            .expect("equal declared resources should form a quantity");
        assert_eq!(context.facts().len(), 1);
        assert_eq!(context.facts()[0].owned_quantity(), Some(2));
    }
}

#[test]
fn exact_resource_views_are_preserved_when_satisfied() {
    for (owned, viewed) in [
        (
            CResourceFact::own_token("token".to_string(), vec![int32(0)]),
            CResourceFact::view_token("token".to_string(), vec![int32(0)]),
        ),
        (
            CResourceFact::own_composite("box".to_string(), vec![int32(1)]),
            CResourceFact::view_composite("box".to_string(), vec![int32(1)]),
        ),
    ] {
        let context = ResourceContext::new().unchecked_with_fact(owned.clone());
        let after_view = context
            .without_fact(&viewed, &PureFactContext::new())
            .expect("owned exact resource should satisfy its view");
        assert_eq!(after_view.facts(), &[owned]);
    }
}

#[test]
fn declared_resources_normalize_and_consume_one_unit_at_a_time() {
    let unit = CResourceFact::own_token("object_ref".to_string(), vec![int32(7)]);
    let context = ResourceContext::new()
        .try_compose_with_facts([unit.clone(), unit.clone()], &PureFactContext::new())
        .expect("equal counted facts should compose");

    assert_eq!(context.facts().len(), 1);
    assert_eq!(context.facts()[0].owned_quantity(), Some(2));

    let remaining = context
        .without_fact(&unit, &PureFactContext::new())
        .expect("one unit should be consumable from a count of two");
    assert_eq!(remaining.facts(), &[unit]);
}

#[test]
fn symbolic_declared_resource_quantity_splits_without_materializing_units() {
    let quantity = Bitvector32Term::var(Variable(700));
    let resource = CResource::Token {
        name: "permit".to_string(),
        arguments: vec![int32(9).into()].into(),
    };
    let symbolic = CResourceFact::own_quantity(resource.clone(), quantity.clone());
    let unit = CResourceFact::own(resource.clone());
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::Bitvector32SignedGreaterEqual(
            Box::new(quantity.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        ),
        true,
    );

    let remaining = ResourceContext::new()
        .unchecked_with_fact(symbolic)
        .without_fact(&unit, &assumptions)
        .expect("one unit should split from a positive symbolic quantity");

    assert_eq!(
        remaining.facts(),
        &[CResourceFact::own_quantity(
            resource,
            Bitvector32Term::subtract(quantity, Bitvector32Term::Constant(1)),
        )]
    );
}

#[test]
fn declared_resource_quantity_work_ignores_the_numeric_coefficient() {
    let resource = CResource::Token {
        name: "permit".to_string(),
        arguments: vec![int32(9).into()].into(),
    };
    let symbolic_quantity = Bitvector32Term::var(Variable(701));

    let samples = [
        ("one", Bitvector32Term::Constant(1)),
        ("two", Bitvector32Term::Constant(2)),
        ("ten", Bitvector32Term::Constant(10)),
        ("one hundred", Bitvector32Term::Constant(100)),
        ("one thousand", Bitvector32Term::Constant(1_000)),
        ("symbolic", symbolic_quantity.clone()),
    ]
    .into_iter()
    .map(|(label, quantity)| {
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(quantity.clone()),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            true,
        );
        let context = ResourceContext::new().unchecked_with_facts([
            CResourceFact::own_quantity(resource.clone(), quantity.clone()),
            CResourceFact::own(resource.clone()),
        ]);
        let (normalized, normalization_work) =
            crate::instrumentation::measure_deterministic_work(|| context.normalized(&assumptions));
        assert_eq!(normalized.facts().len(), 1);

        let available = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_quantity(resource.clone(), quantity));
        let (remaining, consumption_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                available.without_fact(&CResourceFact::own(resource.clone()), &assumptions)
            });
        assert!(remaining.is_some(), "{label} units should contain one unit");

        (label, normalization_work, consumption_work)
    })
    .collect::<Vec<_>>();

    assert!(
        samples.iter().all(|sample| sample.1 == samples[0].1),
        "normalization work depended on the coefficient: {samples:?}"
    );
    assert!(
        samples[1..5].iter().all(|sample| sample.2 == samples[1].2),
        "one-unit splitting work depended on the concrete coefficient: {samples:?}"
    );
    assert!(
        samples[0].2 <= samples[1].2,
        "the exact one-unit fast path should not cost more than splitting: {samples:?}"
    );
    assert!(
        samples[5].2 <= samples[1].2 + 8,
        "a symbolic coefficient should add only bounded expression-reasoning work: {samples:?}"
    );
}

#[test]
fn zero_declared_resource_quantity_is_the_composition_identity() {
    let zero = CResourceFact::own_quantity(
        CResource::Token {
            name: "permit".to_string(),
            arguments: vec![int32(9).into()].into(),
        },
        Bitvector32Term::Constant(0),
    );
    assert!(zero.core().is_none());
    let context = ResourceContext::new()
        .try_compose_with_fact(zero, &PureFactContext::new())
        .expect("zero ownership should compose harmlessly");
    assert!(context.is_empty());
}

#[test]
fn declared_resource_quantities_are_part_of_context_equality() {
    let unit = CResourceFact::own_token("object_ref".to_string(), vec![int32(7)]);
    let one = ResourceContext::new()
        .try_compose_with_fact(unit.clone(), &PureFactContext::new())
        .unwrap();
    let two = ResourceContext::new()
        .try_compose_with_facts([unit.clone(), unit], &PureFactContext::new())
        .unwrap();
    let two_uncompacted = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_token(
            "object_ref".to_string(),
            vec![int32(7)],
        ))
        .unchecked_with_fact(CResourceFact::own_token(
            "object_ref".to_string(),
            vec![int32(7)],
        ));

    assert!(!resource_contexts_definitionally_equal_with_definitions(
        &[],
        &CMemory::new(),
        &one,
        &CMemory::new(),
        &two,
        &PureFactContext::new(),
    ));
    assert!(resource_contexts_definitionally_equal_with_definitions(
        &[],
        &CMemory::new(),
        &two_uncompacted,
        &CMemory::new(),
        &two,
        &PureFactContext::new(),
    ));
}

#[test]
fn resource_consumption_ignores_unrelated_exact_shapes() {
    let required = CResourceFact::view_token("target".to_string(), vec![int32(7)]);
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let context = ResourceContext::new()
                .unchecked_with_facts((0..size).map(|index| {
                    CResourceFact::own_token(format!("unrelated_{index}"), vec![int32(index)])
                }))
                .unchecked_with_fact(CResourceFact::own_token(
                    "target".to_string(),
                    vec![int32(7)],
                ));
            assert_eq!(context.direct_match_candidates(&required).count(), 1);
            let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.without_fact_delaying_normalization(&required, &PureFactContext::new())
            });
            assert!(remaining.is_some());
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed token consumption should not inspect unrelated resource shapes: {samples:?}"
    );
}

#[test]
fn incremental_quantity_consumption_normalizes_only_the_exact_resource_bucket() {
    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024, 4096] {
        let target_resource = CResource::Token {
            name: "shared_name".to_string(),
            arguments: vec![int32(size + 1).into()].into(),
        };
        let unit = CResourceFact::Own(
            target_resource.clone(),
            Box::new(Bitvector32Term::Constant(1)),
        );
        let required =
            CResourceFact::own_quantity(target_resource.clone(), Bitvector32Term::Constant(2));
        let context = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_token("shared_name".to_string(), vec![int32(index)])
            }))
            .unchecked_with_fact(unit.clone())
            .unchecked_with_fact(unit.clone());
        let ancestor = context.clone();
        assert!(context.storage.materialized.get().is_none());

        let before = crate::persistent::persistent_node_allocations();
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .clone()
                .without_fact_incrementally(&required, &PureFactContext::new())
        });
        let remaining = remaining.expect("two retained units should satisfy quantity two");
        samples.push((
            size,
            usize::BITS as usize - (size as usize).leading_zeros() as usize,
            crate::persistent::persistent_node_allocations() - before,
            work,
        ));
        assert!(!remaining.satisfies_fact(&unit, &PureFactContext::new()));
        assert!(
            remaining.contains_exact_representation(&CResourceFact::own_token(
                "shared_name".to_string(),
                vec![int32(size / 2)],
            ))
        );
        assert!(remaining.storage.materialized.get().is_none());
        assert_eq!(
            ancestor
                .storage
                .index
                .exact
                .get(&unit)
                .map_or(0, |entries| entries.len()),
            2,
            "incremental consumption must leave its ancestor unchanged"
        );
        assert!(ancestor.shares_storage_with(&context));
    }

    let (_, base_height, base_allocations, base_work) = samples[0];
    for (size, height, allocations, work) in samples {
        let allocation_bound = base_allocations + 96 * (height - base_height);
        assert!(
            allocations <= allocation_bound,
            "size {size} incremental quantity consumption allocated {allocations} persistent nodes (bound {allocation_bound})"
        );
        assert!(
            work <= base_work + 2,
            "size {size} incremental quantity consumption used {work} deterministic units (base {base_work})"
        );
    }

    let unit = CResourceFact::own_token("target".to_string(), Vec::new());
    let context = ResourceContext::new()
        .unchecked_with_fact(unit.clone())
        .unchecked_with_fact(unit);
    let unavailable = CResourceFact::own_quantity(
        CResource::Token {
            name: "target".to_string(),
            arguments: Vec::new().into(),
        },
        Bitvector32Term::Constant(3),
    );
    assert!(
        context
            .clone()
            .without_fact_incrementally(&unavailable, &PureFactContext::new())
            .is_none(),
        "failed incremental consumption must not manufacture a larger quantity"
    );
    assert_eq!(context.facts().len(), 2);
}

#[test]
fn missing_composite_query_ignores_ambient_memory_splits() {
    let base = Pointer {
        block: "backing".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let context = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(base.clone(), 0, 1)))
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(base, 1, 2)));
    let required = CResourceFact::own_composite("allocated".to_string(), vec![int32(0)]);

    assert!(!context.satisfies_fact(&required, &PureFactContext::new()));
}

#[test]
fn owned_memory_query_without_owned_memory_is_rejected_structurally() {
    let context = ResourceContext::new().unchecked_with_fact(CResourceFact::view_composite(
        "tree".to_string(),
        vec![int32(0)],
    ));
    let required = CResourceFact::own_memory(memory_range(
        Pointer {
            block: "p".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        1,
    ));

    assert!(!context.satisfies_fact(&required, &PureFactContext::new()));
}

#[test]
fn batch_resource_consumption_splits_without_repeated_normalization() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let context = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(base.clone(), 0, 3)));
    let required = [
        CResourceFact::own_memory(memory_range(base.clone(), 0, 1)),
        CResourceFact::own_memory(memory_range(base, 1, 3)),
    ];

    let remaining = context
        .without_facts(&required, &PureFactContext::new())
        .expect("both subranges should be consumable");

    assert!(remaining.is_empty());
}

#[test]
fn batch_resource_consumption_normalizes_when_a_requirement_needs_a_merge() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let context = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(base.clone(), 0, 1)))
        .unchecked_with_fact(CResourceFact::own_memory(memory_range(base.clone(), 1, 2)));
    let required = [CResourceFact::own_memory(memory_range(base, 0, 2))];

    let remaining = context
        .without_facts(&required, &PureFactContext::new())
        .expect("adjacent ranges should merge before consumption");

    assert!(remaining.is_empty());
}

#[test]
fn resource_context_observes_write_separation() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left = memory_range(base.clone(), 0, 1);
    let right = memory_range(base.clone(), 1, 2);
    let facts = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(left.clone()))
        .unchecked_with_fact(CResourceFact::own_memory(right.clone()))
        .observable_facts(&PureFactContext::new())
        .expect("adjacent writes should be a valid resource context");

    assert_eq!(facts.len(), 1);
    assert!(matches!(facts[0], Proposition::CResourceComposition(_)));
    assert!(
        PureFactContext::new().proves(&Proposition::CResourceSeparate {
            left: CResource::Memory(left),
            right: CResource::Memory(right),
        })
    );
}

#[test]
fn resource_context_observes_same_and_cross_family_separation() {
    let memory = CResource::Memory(memory_range(
        Pointer {
            block: "p".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        1,
    ));
    let token = CResource::Token {
        name: "left".to_string(),
        arguments: vec![].into(),
    };
    let other_token = CResource::Token {
        name: "right".to_string(),
        arguments: vec![].into(),
    };
    let facts = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own(memory.clone()))
        .unchecked_with_fact(CResourceFact::own(token.clone()))
        .unchecked_with_fact(CResourceFact::own(other_token.clone()))
        .observable_facts(&PureFactContext::new())
        .expect("distinct owned resources should compose validly");

    let assumptions = facts
        .into_iter()
        .fold(PureFactContext::new(), |assumptions, fact| {
            assumptions.assume_proposition(fact)
        });
    assert!(assumptions.proves(&Proposition::CResourceSeparate {
        left: token.clone(),
        right: other_token,
    }));
    assert!(assumptions.proves(&Proposition::CResourceSeparate {
        left: memory,
        right: token,
    }));
}

#[test]
fn observable_abstract_resources_use_one_indexed_composition() {
    for size in [16, 32, 64, 128] {
        let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
            CResourceFact::own(CResource::Token {
                name: format!("token_{index}"),
                arguments: vec![].into(),
            })
        }));
        let facts = context
            .observable_facts(&PureFactContext::new())
            .expect("distinct token resources should compose");
        assert_eq!(facts.len(), 1, "size-{size} projection materialized pairs");
        let assumptions = facts
            .into_iter()
            .fold(PureFactContext::new(), |assumptions, fact| {
                assumptions.assume_proposition(fact)
            });
        assert!(assumptions.proves(&Proposition::CResourceSeparate {
            left: context.facts()[0].resource().clone(),
            right: context.facts()[size - 1].resource().clone(),
        }));
    }
}

#[test]
fn composite_resource_arguments_respect_proven_pointer_equality() {
    let left_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(40_000)), 4),
    };
    let right_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(40_001)), 4),
    };
    let left = CResourceFact::own(CResource::Composite {
        name: "list".to_string(),
        arguments: vec![CValue::pointer(left_pointer.clone()).into()].into(),
    });
    let right = CResourceFact::own(CResource::Composite {
        name: "list".to_string(),
        arguments: vec![CValue::pointer(right_pointer.clone()).into()].into(),
    });
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(left_pointer, right_pointer),
        true,
    );

    let remaining = ResourceContext::new()
        .unchecked_with_fact(left.clone())
        .without_fact(&right, &assumptions)
        .expect("equal resource arguments should identify the same owned fact");
    assert!(remaining.is_empty());

    let combined = ResourceContext::new()
        .unchecked_with_fact(left)
        .try_compose_with_fact(right, &assumptions)
        .expect("proved-equal resource arguments should accumulate");
    assert_eq!(combined.facts().len(), 1);
    assert_eq!(combined.facts()[0].owned_quantity(), Some(2));
}

#[test]
fn resource_separation_proves_memory_disjointness() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left = memory_range(base.clone(), 0, 1);
    let right = memory_range(base.clone(), 1, 2);
    let assumptions = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
        left: CResource::Memory(left),
        right: CResource::Memory(right),
    });

    assert!(assumptions.proves(&Proposition::CMemoryDisjoint {
        left_base: base.clone(),
        left_start: Bitvector32Term::Constant(0),
        left_end: Bitvector32Term::Constant(1),
        right_base: base,
        right_start: Bitvector32Term::Constant(1),
        right_end: Bitvector32Term::Constant(2),
    }));
}

#[test]
fn resource_separation_covers_larger_memory_range() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left_first = CResource::Memory(memory_range(base.clone(), 0, 1));
    let left_second = CResource::Memory(memory_range(base.clone(), 1, 2));
    let left_combined = CResource::Memory(memory_range(base.clone(), 0, 2));
    let right = CResource::Memory(memory_range(base, 10, 11));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: left_first,
            right: right.clone(),
        })
        .assume_proposition(Proposition::CResourceSeparate {
            left: left_second,
            right: right.clone(),
        });

    assert!(assumptions.proves(&Proposition::CResourceSeparate {
        left: left_combined,
        right,
    }));
}

#[test]
fn resource_separation_transports_across_equal_memory_ranges() {
    let target = Pointer::symbolic(Variable(20_100));
    let original_data = Pointer::symbolic(Variable(20_101));
    let equal_data = Pointer::symbolic(Variable(20_102));
    let original_length = Bitvector32Term::Variable(Variable(20_103));
    let equal_length = Bitvector32Term::Variable(Variable(20_104));
    let target_resource = CResource::Memory(memory_range(target, 0, 4));
    let original_resource = CResource::Memory(memory_range(
        original_data.clone(),
        0,
        original_length.clone(),
    ));
    let equal_resource =
        CResource::Memory(memory_range(equal_data.clone(), 0, equal_length.clone()));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: target_resource.clone(),
            right: original_resource,
        })
        .assume_condition(
            ConditionTerm::pointer_equal(original_data, equal_data),
            true,
        )
        .assume_condition(ConditionTerm::equal(original_length, equal_length), true);

    assert!(assumptions.proves(&Proposition::CResourceSeparate {
        left: target_resource,
        right: equal_resource,
    }));
}

#[test]
fn resource_contains_projects_separation_to_children() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let parent = CResource::Token {
        name: "parent".to_string(),
        arguments: vec![].into(),
    };
    let child = CResource::Memory(memory_range(base.clone(), 0, 1));
    let other = CResource::Memory(memory_range(base.clone(), 1, 2));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: parent.clone(),
            right: other.clone(),
        })
        .assume_proposition(Proposition::CResourceContains {
            parent,
            child: child.clone(),
        });

    assert!(assumptions.proves(&Proposition::CResourceSeparate {
        left: child,
        right: other,
    }));
}

#[test]
fn checked_resource_composition_rejects_invalid_state_before_normalizing() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let error = ResourceContext::new()
        .try_compose_with_facts(
            [
                own_memory_fact(base.clone(), 0, 1),
                own_memory_fact(base.clone(), 0, 1),
            ],
            &PureFactContext::new(),
        )
        .expect_err("duplicate writes must be rejected before normalization");

    assert_eq!(
        error,
        ResourceContextValidityError::OverlappingOwnedMemoryResources {
            left: memory_range(base.clone(), 0, 1),
            right: memory_range(base, 0, 1),
        }
    );
}

#[test]
fn symbolic_same_block_ranges_emit_no_pairs_with_near_linear_work() {
    // The lazy-separation acceptance curve: N symbolic same-block owned
    // ranges expose one compact composition authority and zero pairwise
    // CResourceSeparate propositions, in work near-linear in N.
    let samples = [8, 16, 32, 64]
        .into_iter()
        .map(|size| {
            let base = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            };
            let endpoints = (0..=size)
                .map(|index| Bitvector32Term::Variable(Variable(94_000 + index as u64)))
                .collect::<Vec<_>>();
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_memory(CMemoryRange::new(
                    base.clone(),
                    endpoints[index].clone(),
                    endpoints[index + 1].clone(),
                ))
            }));
            let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.observable_facts_assuming_valid(&PureFactContext::new())
            });
            let pair_count = facts
                .iter()
                .filter(|fact| matches!(fact, Proposition::CResourceSeparate { .. }))
                .count();
            assert_eq!(
                pair_count, 0,
                "symbolic same-block ranges must not materialize pairwise separations"
            );
            assert!(
                facts
                    .iter()
                    .any(|fact| matches!(fact, Proposition::CResourceComposition(_))),
                "multi-owner contexts should expose one compact authority"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "observable fact projection is superlinear: {samples:?}"
        );
    }
}

/// Exposing a cell that an unfolded composite holds is a structural lookup
/// at each unfolding, not a proof: with a chain of order facts relating the
/// composites' pointers, reasoning about every candidate at every unfolding
/// grows superlinearly, while the structural answer stays near linear in the
/// number of composites. Regression for the binary-tree slowdown, where
/// certification exposed each derived load through the resource algebra's
/// reasoning and took minutes.
#[test]
fn composite_exposure_finds_held_cells_by_structure_near_linearly() {
    let definition = CCompositeResourceDefinition::new(
        "cell",
        vec![c_parameter("item", CType::Int32Pointer)],
        None,
        false,
        vec![CResourceSpec::owned_memory(CMemorySegment {
            base: c_variable("item"),
            start: c_int32_literal(0),
            end: c_int32_literal(1),
            element_width: 4,
            guard: None,
        })],
        Vec::new(),
    );
    let pointer = |index: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::Variable(Variable(900_000 + index)),
            4,
        ),
    };
    let samples = [4_u64, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
                CResourceFact::own_composite(
                    "cell".to_string(),
                    vec![CValue::pointer(pointer(index))],
                )
            }));
            let mut assumptions = PureFactContext::new();
            for index in 0..size - 1 {
                assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(900_000 + index)),
                        Bitvector32Term::Variable(Variable(900_000 + index + 1)),
                    ),
                    true,
                ));
            }
            let target = CResourceFact::view_memory(memory_range(pointer(size - 1), 0, 1));
            let (exposed, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::functions::expose_composite_resource_fact(
                    &context,
                    &target,
                    std::slice::from_ref(&definition),
                    &CMemory::new(),
                    &assumptions,
                )
            });
            assert!(
                exposed.is_some(),
                "size {size}: the unfolded cell should be exposed"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    eprintln!("composite exposure samples: {samples:?}");
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "composite exposure is superlinear: {samples:?}"
        );
    }
}

#[test]
fn integer_resource_fields_require_mathematical_values() {
    let schema =
        ResourceFieldSchema::new(vec![("total".into(), ResourceFieldType::Integer)]).unwrap();
    assert!(!schema.is_countable());
    let make = |value| {
        ResourceInstance::new(
            Variable(1),
            "account".into(),
            vec![].into(),
            schema.clone(),
            vec![value].into(),
        )
    };
    assert!(
        make(AlgebraicValue::Integer(IntegerTerm::Constant(
            "18446744073709551616".parse().unwrap()
        )))
        .is_some()
    );
    assert!(make(int32(1).into()).is_none());
}

#[test]
fn matched_resource_integer_binding_is_checked_and_substituted() {
    let ty = resource_index_type("IntegerModel", vec![AlgebraicValueType::Integer]);
    let model = resource_index_variable(&ty, 991_001);
    let constructor = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Set".into(),
            fields: vec![AlgebraicValue::Integer(IntegerTerm::constant_i64(7))],
        },
    };
    let schema = ResourceFieldSchema::new(vec![(
        "model".into(),
        ResourceFieldType::Algebraic(ty.clone()),
    )])
    .unwrap();
    let instance = ResourceInstance::new(
        Variable(991_000),
        "integer_box".into(),
        vec![].into(),
        schema.clone(),
        vec![AlgebraicValue::Algebraic(model.clone())].into(),
    )
    .unwrap();
    let binding = Variable(9_100_000_000);
    let mut definition =
        CCompositeResourceDefinition::new("integer_box", vec![], None, false, vec![], vec![])
            .with_instance_schema(Some(schema));
    definition.matched = Some(CResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            CResourceMatchArm {
                variant: "Clear".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            CResourceMatchArm {
                variant: "Set".into(),
                bindings: vec!["value".into()],
                binding_types: vec![AlgebraicValueType::Integer],
                binding_variables: vec![Some(binding)],
                contains: vec![],
                facts: vec![SpecProposition::IntegerComparison {
                    left: SpecIntegerExpression::Term(IntegerTerm::var(binding)),
                    operator: IntegerComparisonOperator::GreaterEqual,
                    right: SpecIntegerExpression::Term(IntegerTerm::constant_i64(0)),
                }],
                children: vec![],
            },
        ],
    });
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone()))),
    );
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Equal(
        Term::Algebraic(model),
        Term::Algebraic(constructor),
    ));
    assert!(
        rewrite_resource_instance(&state, &instance, &definition, &assumptions, true).is_ok(),
        "the selected Integer constructor field should discharge its arm fact"
    );

    let mut malformed = definition.clone();
    malformed.matched.as_mut().unwrap().arms[1].binding_variables = vec![None];
    assert!(
        rewrite_resource_instance(&state, &instance, &malformed, &assumptions, true).is_err(),
        "an Integer arm without a checked kernel identity must be rejected"
    );
}

#[test]
fn matched_resource_integer_binding_does_not_capture_free_integer_field() {
    let ty = resource_index_type("IntegerCaptureModel", vec![AlgebraicValueType::Integer]);
    let model = resource_index_variable(&ty, 991_101);
    let binding = Variable(9_100_000_001);
    let constructor = AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Set".into(),
            fields: vec![AlgebraicValue::Integer(IntegerTerm::constant_i64(7))],
        },
    };
    let schema = ResourceFieldSchema::new(vec![
        ("model".into(), ResourceFieldType::Algebraic(ty.clone())),
        ("other".into(), ResourceFieldType::Integer),
    ])
    .unwrap();
    // The second field deliberately contains a free term with the same
    // numeric identity used by the selected constructor binding. It must
    // remain free when the arm's `value` placeholder is instantiated.
    let instance = ResourceInstance::new(
        Variable(991_100),
        "integer_capture_box".into(),
        vec![].into(),
        schema.clone(),
        vec![
            AlgebraicValue::Algebraic(model.clone()),
            AlgebraicValue::Integer(IntegerTerm::var(binding)),
        ]
        .into(),
    )
    .unwrap();
    let field = SpecIntegerExpression::ResourceField(ResourceFieldProjection {
        // Resource body facts refer to the matched instance through the
        // placeholder binding installed by `instance_body_evaluation`, not
        // through the concrete instance identity.  Keep the field payload's
        // free Integer identity independent from that resource placeholder.
        identity: Variable(u64::MAX),
        children: vec![],
        field_index: 1,
        at_entry: false,
    });
    let mut definition = CCompositeResourceDefinition::new(
        "integer_capture_box",
        vec![],
        None,
        false,
        vec![],
        vec![],
    )
    .with_instance_schema(Some(schema));
    definition.matched = Some(CResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            CResourceMatchArm {
                variant: "Clear".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            CResourceMatchArm {
                variant: "Set".into(),
                bindings: vec!["value".into()],
                binding_types: vec![AlgebraicValueType::Integer],
                binding_variables: vec![Some(binding)],
                contains: vec![],
                facts: vec![SpecProposition::IntegerComparison {
                    left: field,
                    operator: IntegerComparisonOperator::Equal,
                    right: SpecIntegerExpression::Term(IntegerTerm::var(binding)),
                }],
                children: vec![],
            },
        ],
    });
    let state = CState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own(CResource::Instance(instance.clone()))),
    );
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Equal(
        Term::Algebraic(model),
        Term::Algebraic(constructor),
    ));
    let (_, unfolded_facts) =
        rewrite_resource_instance(&state, &instance, &definition, &assumptions, true).unwrap();
    let free_field_fact = unfolded_facts.iter().any(|fact| {
        let Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) = fact else {
            return false;
        };
        (left.as_ref() == &IntegerTerm::var(binding)
            && right.as_ref() == &IntegerTerm::constant_i64(7))
            || (right.as_ref() == &IntegerTerm::var(binding)
                && left.as_ref() == &IntegerTerm::constant_i64(7))
    });
    assert!(
        free_field_fact,
        "the free field term must survive arm binding substitution: {unfolded_facts:?}"
    );

    let fold_state = CState::new();
    assert!(
        rewrite_resource_instance(&fold_state, &instance, &definition, &assumptions, false)
            .is_err(),
        "folding must require the free field equality rather than reducing it to 7 == 7"
    );
    let valid_fold_assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
        ConditionTerm::IntegerEqual(
            IntegerTerm::var(binding).into(),
            IntegerTerm::constant_i64(7).into(),
        ),
        true,
    ));
    assert!(
        rewrite_resource_instance(
            &fold_state,
            &instance,
            &definition,
            &valid_fold_assumptions,
            false,
        )
        .is_ok(),
        "the explicit free field equality should discharge the fold prerequisite"
    );
}

/// Builds a fact context of `size` unrelated bounded variables, then adds the
/// facts a quantity or separation query actually names. Package 3's exact
/// routes must answer from the named facts alone.
fn unrelated_order_fact_context(size: usize) -> PureFactContext {
    let mut assumptions = PureFactContext::new();
    for index in 0..size {
        assumptions = assumptions
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Variable(Variable(960_100 + index as u64)),
                    Bitvector32Term::Constant(1_000),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_greater_equal(
                    Bitvector32Term::Variable(Variable(960_100 + index as u64)),
                    Bitvector32Term::Constant(0),
                ),
                true,
            );
    }
    assumptions
}

/// Package 3 regression. The quantity relations behind counted populations and
/// the resource algebra are decided by exact lookup and the retained atomic
/// condition checker, so an ambient context of unrelated bounded variables must
/// not change their work. The general prover this replaced scanned every
/// condition fact for an inconsistency and every proposition fact for a
/// singleton substitution, so its work grew with `size`.
#[test]
fn quantity_relations_ignore_unrelated_facts() {
    let count = Bitvector32Term::Variable(Variable(960_001));
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size).assume_condition(
                ConditionTerm::equal(count.clone(), Bitvector32Term::Constant(3)),
                true,
            );
            let (decided, work) = crate::instrumentation::measure_deterministic_work(|| {
                [
                    // `population_quantity_is_positive` / `resource_quantity_is_positive`
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::signed_greater_than(
                            count.clone(),
                            Bitvector32Term::Constant(0),
                        ),
                    ),
                    // `resource_quantity_at_least`
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::signed_greater_equal(
                            count.clone(),
                            Bitvector32Term::Constant(2),
                        ),
                    ),
                    // `population_quantities_are_equal`
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::equal(count.clone(), Bitvector32Term::Constant(3)),
                    ),
                    // A relation that does not follow: the miss must also be
                    // flat, and must not be repaired by a broader search.
                    quantity_condition_holds(
                        &assumptions,
                        ConditionTerm::equal(count.clone(), Bitvector32Term::Constant(4)),
                    ),
                ]
            });
            assert_eq!(
                decided,
                [true, true, true, false],
                "size {size}: exact quantity routes decided the wrong relations"
            );
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "quantity relations scanned unrelated facts: {samples:?}"
    );
}

/// The same curve through the resource-algebra entry points that consume those
/// relations: symbolic-quantity entailment (`resource_quantity_at_least` and
/// the residual test in `consume_exact_resource_fact`) and access-mode coring
/// (`resource_quantity_is_positive`).
#[test]
fn symbolic_quantity_consumption_ignores_unrelated_facts() {
    let available_quantity = Bitvector32Term::Variable(Variable(960_011));
    let required_quantity = Bitvector32Term::Variable(Variable(960_012));
    let resource = CResource::Token {
        name: "counted".to_string(),
        arguments: vec![int32(7).into()].into(),
    };
    let available = CResourceFact::own_quantity(resource.clone(), available_quantity.clone());
    let required = CResourceFact::own_quantity(resource.clone(), required_quantity.clone());
    let empty_quantity = Bitvector32Term::Variable(Variable(960_014));
    let empty_core = CResourceFact::own_quantity(resource, empty_quantity.clone());
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size)
                .assume_condition(
                    ConditionTerm::signed_greater_equal(
                        available_quantity.clone(),
                        required_quantity.clone(),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_greater_than(
                        available_quantity.clone(),
                        Bitvector32Term::Constant(0),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::equal(empty_quantity.clone(), Bitvector32Term::Constant(0)),
                    true,
                );
            let context = ResourceContext::new().unchecked_with_fact(available.clone());
            let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
                (
                    context.satisfies_fact(&required, &assumptions),
                    available.core_with_assumptions(&assumptions).is_some(),
                    // The miss matters too: an exactly-zero quantity has no
                    // access-mode core, and the general prover answered that
                    // only after scanning every ambient condition fact for an
                    // inconsistency and every proposition fact for a singleton
                    // substitution.
                    empty_core.core_with_assumptions(&assumptions).is_some(),
                )
            });
            assert_eq!(
                outcome,
                (true, true, false),
                "size {size}: symbolic quantity entailment lost its exact premise"
            );
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "symbolic quantity consumption scanned unrelated facts: {samples:?}"
    );
}

/// Allocation separation now asks the retained atomic resource checker rather
/// than the general prover, so the same flat curve applies to it.
#[test]
fn allocation_separation_ignores_unrelated_facts() {
    let allocation_base = Pointer {
        block: "package-3-allocation".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let held = own_memory_fact(
        Pointer {
            block: "package-3-held".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        8,
    );
    let overlapping = own_memory_fact(allocation_base.clone(), 0, 8);
    let bytes = Bitvector32Term::Constant(16);
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size);
            let (outcome, work) = crate::instrumentation::measure_deterministic_work(|| {
                (
                    held.is_proven_separate_from_allocation_with_element_width(
                        &allocation_base,
                        &bytes,
                        4,
                        &assumptions,
                    ),
                    overlapping.is_proven_separate_from_allocation_with_element_width(
                        &allocation_base,
                        &bytes,
                        4,
                        &assumptions,
                    ),
                )
            });
            assert_eq!(
                outcome,
                (true, false),
                "size {size}: allocation separation decided the wrong blocks"
            );
            (size, work)
        })
        .collect::<Vec<_>>();

    let base_work = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "allocation separation scanned unrelated facts: {samples:?}"
    );
}

/// Package 10(a) regression for `ResourceContext::satisfies_fact`'s miss
/// path.
///
/// A resource query that misses must be paid for by the fact it names and by
/// the resources the context indexes under that fact's block — never by the
/// ambient condition facts that happen to be in scope. Two axes are measured,
/// each with one fixed query.
///
/// The resource axis is flat. On the ambient-condition axis the residual
/// slope is the exact order-path walk in `condition_reasoning/order_paths.rs`,
/// a whole-context loop inside the frozen condition checker that
/// the kernel authority boundary in `docs/internals/proof-objects.md` treats as a separate indexing debt. This test
/// pins the slope that remains after the two `condition_facts` scans in
/// `exact_less_equal_for_memory_resolution` became indexed lookups at the two
/// endpoints the query names. Before that change the same query grew at twice
/// this rate (93, 157, 285, 541 over these sizes), so the assertion fails on
/// the old representation.
#[test]
fn satisfies_fact_miss_ignores_unrelated_facts() {
    let base = Pointer {
        block: "package-10a-held".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let held = own_memory_fact(base.clone(), 0, 8);
    let adjacent = own_memory_fact(base.clone(), 8, 16);
    let symbolic_end = Bitvector32Term::Variable(Variable(970_001));
    // A miss whose end is symbolic: the shape that reaches the proof-aware
    // containment layers instead of being refused by constant bounds.
    let missing = own_memory_fact(base.clone(), 0, symbolic_end);
    let context = ResourceContext::new()
        .unchecked_with_fact(held.clone())
        .unchecked_with_fact(adjacent.clone());

    let sizes = [16, 32, 64, 128];
    let ambient = sizes
        .into_iter()
        .map(|size| {
            let assumptions = unrelated_order_fact_context(size);
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.satisfies_fact(&missing, &assumptions)
            });
            assert!(
                !satisfied,
                "size {size}: the missing resource was satisfied"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    let base_work = ambient[0].1;
    assert!(
        ambient
            .iter()
            .all(|(size, work)| *work <= base_work + 2 * (size - sizes[0])),
        "satisfies_fact's miss path still scans ambient condition facts: {ambient:?}"
    );

    // The other axis: unrelated resources in the same context, with the
    // ambient fact context held empty. The block index must keep this flat.
    let resources = sizes
        .into_iter()
        .map(|size| {
            let mut wide = ResourceContext::new()
                .unchecked_with_fact(held.clone())
                .unchecked_with_fact(adjacent.clone());
            for index in 0..size {
                wide = wide.unchecked_with_fact(own_memory_fact(
                    Pointer {
                        block: format!("package-10a-unrelated-{index}").into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    0,
                    4,
                ));
            }
            let assumptions = PureFactContext::new();
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                wide.satisfies_fact(&missing, &assumptions)
            });
            assert!(
                !satisfied,
                "size {size}: the missing resource was satisfied"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    let base_work = resources[0].1;
    assert!(
        resources
            .iter()
            .all(|(_, work)| *work <= base_work.saturating_add(2)),
        "satisfies_fact's miss path scanned unrelated resources: {resources:?}"
    );
}

/// A contract section whose clauses cannot be put in any evaluable order is
/// refused by naming a pair, not the clause that happens to be written last.
/// Clause order does not decide a section, so one position is not the answer.
#[test]
fn resource_clauses_with_no_evaluable_order_name_two_positions() {
    let unowned = |variable| {
        CResourceSpec::owned_memory(CMemorySegment {
            base: CExpression::Load(Box::new(CExpression::Value(CValue::pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::Variable(Variable(variable)),
                    4,
                ),
            })))),
            start: c_int32_literal(0),
            end: c_int32_literal(1),
            element_width: 4,
            guard: None,
        })
    };
    let evaluate = |clauses: &[CResourceSpec]| {
        let CRuntimeError::FunctionContract(message) =
            crate::kernel::functions::evaluate_function_resource_context(
                &CState::new(),
                clauses,
                &[],
                &PureFactContext::new(),
                &mut ExecutionBudget::default(),
            )
            .expect("clause evaluation stays inside its budget")
            .expect_err("no clause has read authority for its base")
        else {
            panic!("an unevaluable segment is a contract error");
        };
        message
    };
    assert_eq!(
        evaluate(&[unowned(100), unowned(101)]),
        "could not evaluate an owned memory resource segment (resource clauses 1 and 2 cannot \
         be evaluated in any order: each needs a cell no clause evaluated before it supplies)"
    );
    // One stalled clause is still reported at its own position: there is no
    // second clause whose authority it could have been waiting for.
    assert_eq!(
        evaluate(&[unowned(100)]),
        "could not evaluate an owned memory resource segment (resource clause 1 of 1)"
    );
}

/// A datatype with field-free variants plus one that carries an `int32`, so a
/// test can vary how many arms exclusion has to rule out.
fn arm_selection_type(nullary: &[&str], payload: &str) -> AlgebraicType {
    let variants: std::sync::Arc<[AlgebraicVariantType]> = nullary
        .iter()
        .map(|name| AlgebraicVariantType {
            name: (*name).into(),
            fields: vec![],
        })
        .chain([AlgebraicVariantType {
            name: payload.into(),
            fields: vec![AlgebraicValueType::C(CType::Int32)],
        }])
        .collect::<Vec<_>>()
        .into();
    let value_type = AlgebraicValueType::Algebraic {
        name: "Slot".into(),
        arguments: vec![],
    };
    AlgebraicType {
        rigid: false,
        name: "Slot".into(),
        arguments: vec![],
        variants: variants.clone(),
        schemas: std::sync::Arc::new(AlgebraicSchemas::new(BTreeMap::from([(
            value_type, variants,
        )]))),
    }
}

fn arm_selection_constructor(
    ty: &AlgebraicType,
    variant: &str,
    fields: Vec<AlgebraicValue>,
) -> AlgebraicTerm {
    AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: variant.into(),
            fields,
        },
    }
}

#[test]
fn resource_model_arm_selection_decides_only_entailed_arms() {
    let ty = arm_selection_type(&["Empty"], "Filled");
    let model = resource_index_variable(&ty, 11);
    let empty = arm_selection_constructor(&ty, "Empty", vec![]);
    let filled = |value: u32| {
        arm_selection_constructor(
            &ty,
            "Filled",
            vec![AlgebraicValue::C(CValue::Int32(Bitvector32Term::Constant(
                value,
            )))],
        )
    };
    let equal = |left: &AlgebraicTerm, right: &AlgebraicTerm| {
        Proposition::Equal(
            Term::Algebraic(left.clone()),
            Term::Algebraic(right.clone()),
        )
    };

    // No evidence selects nothing: the resource stays folded.
    assert!(select_resource_model_arm(&model, &PureFactContext::new()).is_none());

    // A constructor premise answers with the fields the arm binds.
    let known = PureFactContext::new().assume_proposition(equal(&model, &filled(3)));
    assert_eq!(
        select_resource_model_arm(&model, &known),
        Some(ResourceModelArmSelection::Constructor(filled(3)))
    );

    // Ruling out the only other variant leaves one arm, with no field values.
    let excluded = PureFactContext::new()
        .assume_proposition(Proposition::Not(Box::new(equal(&model, &empty))));
    assert_eq!(
        select_resource_model_arm(&model, &excluded),
        Some(ResourceModelArmSelection::Variant("Filled".to_string()))
    );

    // A disequality against a constructor that carries fields rules out
    // nothing: `model != Filled(3)` still leaves `Filled` possible.
    let unexcluded = PureFactContext::new()
        .assume_proposition(Proposition::Not(Box::new(equal(&model, &filled(3)))));
    assert!(select_resource_model_arm(&model, &unexcluded).is_none());

    // An existential names the arm without naming its payload.
    let witness = arm_selection_constructor(
        &ty,
        "Filled",
        vec![AlgebraicValue::C(CValue::Int32(Bitvector32Term::Variable(
            Variable(77),
        )))],
    );
    let witnessed = PureFactContext::new().assume_proposition(Proposition::Exists {
        name: "v".to_string(),
        var: Variable(77),
        sort: Sort::CInt32,
        body: Box::new(equal(&model, &witness)),
    });
    assert_eq!(
        select_resource_model_arm(&model, &witnessed),
        Some(ResourceModelArmSelection::Variant("Filled".to_string()))
    );

    // Three constructors and one exclusion leave two arms, so nothing is
    // selected and no proof by cases happens.
    let wide = arm_selection_type(&["Empty", "Reserved"], "Filled");
    let wide_model = resource_index_variable(&wide, 11);
    let wide_empty = arm_selection_constructor(&wide, "Empty", vec![]);
    let wide_excluded = PureFactContext::new()
        .assume_proposition(Proposition::Not(Box::new(equal(&wide_model, &wide_empty))));
    assert!(select_resource_model_arm(&wide_model, &wide_excluded).is_none());
}

#[test]
fn resource_model_arm_selection_ignores_unrelated_premises() {
    let ty = arm_selection_type(&["Empty"], "Filled");
    let model = resource_index_variable(&ty, 11);
    let empty = arm_selection_constructor(&ty, "Empty", vec![]);
    let exclusion = |value: &AlgebraicTerm| {
        Proposition::Not(Box::new(Proposition::Equal(
            Term::Algebraic(value.clone()),
            Term::Algebraic(empty.clone()),
        )))
    };
    let mut samples = Vec::new();
    for size in [16, 32, 64, 128] {
        let mut assumptions = PureFactContext::new().assume_proposition(exclusion(&model));
        for index in 100..100 + size {
            assumptions.insert_proposition_fact(exclusion(&resource_index_variable(&ty, index)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                select_resource_model_arm(&model, &assumptions),
                Some(ResourceModelArmSelection::Variant("Filled".to_string()))
            );
        });
        assert!(work > 0, "arm selection must count the premises it visits");
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= pair[0] + 32, "{samples:?}");
    }
}

/// Expanded leaves retain the source clause position used by diagnostics.
/// The first source aggregate contributes two stalled leaves here; the
/// evaluator must skip the duplicate leaf and name the next source clause,
/// rather than reporting a misleading pair of positions for one clause.
#[test]
fn expanded_resource_clause_diagnostics_keep_source_positions() {
    let unowned = |variable| {
        CResourceSpec::owned_memory(CMemorySegment {
            base: CExpression::Load(Box::new(CExpression::Value(CValue::pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::Variable(Variable(variable)),
                    4,
                ),
            })))),
            start: c_int32_literal(0),
            end: c_int32_literal(1),
            element_width: 4,
            guard: None,
        })
    };
    let CRuntimeError::FunctionContract(message) =
        crate::kernel::functions::evaluate_function_resource_context(
            &CState::new(),
            &[
                unowned(100).with_clause_position(0, 2),
                unowned(101).with_clause_position(0, 2),
                unowned(102).with_clause_position(1, 2),
            ],
            &[],
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .expect("clause evaluation stays inside its budget")
        .expect_err("no clause has read authority for its base")
    else {
        panic!("an unevaluable segment is a contract error");
    };
    assert!(message.contains("resource clauses 1 and 2 cannot be evaluated in any order"));
}

/// An adversarially ordered dependency chain is retried through an indexed
/// event worklist.  Its deterministic work should grow with the explicit
/// dependency nodes and edges, not with repeated whole-section scans.
#[test]
fn dependent_resource_clause_work_scales_with_dependency_nodes() {
    let pointer = |index: usize| Pointer {
        // Keep each node in its own block so the curve measures the clause
        // dependency walk rather than the unrelated same-block range
        // normalization cost of the resource algebra.
        block: PointerBlock::Concrete(format!("dependency-{index}")),
        offset: PointerOffsetTerm::Constant((index as i64) * 4),
    };
    let load = |pointer: Pointer| CExpression::TypedLoad {
        pointer: Box::new(c_pointer_value(pointer)),
        value_type: CType::Int32Pointer,
        volatile: false,
    };
    let samples = [4_usize, 8, 16, 32]
        .into_iter()
        .map(|size| {
            let pointers = (0..=size).map(pointer).collect::<Vec<_>>();
            let memory = pointers.windows(2).fold(CMemory::new(), |memory, pair| {
                memory.store(pair[0].clone(), CValue::pointer(pair[1].clone()))
            });
            let state = CState::new().with_memory(memory);
            // Clause 0 is the only initially readable provider.  Put it last
            // and reverse the dependents so a fixed-point implementation must
            // rescan the whole pending suffix once per dependency depth.  An
            // event queue instead retries only the newly unblocked successor.
            let clauses = (1..size)
                .rev()
                .chain(std::iter::once(0))
                .map(|index| {
                    let base = if index == 0 {
                        c_pointer_value(pointers[index].clone())
                    } else {
                        load(pointers[index - 1].clone())
                    };
                    CResourceSpec::owned_memory(CMemorySegment {
                        base,
                        start: c_int32_literal(0),
                        end: c_int32_literal(1),
                        element_width: 4,
                        guard: None,
                    })
                })
                .collect::<Vec<_>>();
            let ((result, work), attempts) =
                crate::kernel::measure_resource_clause_attempts(|| {
                    crate::instrumentation::measure_deterministic_work(|| {
                        crate::kernel::functions::evaluate_function_resource_context(
                            &state,
                            &clauses,
                            &[],
                            &PureFactContext::new(),
                            &mut ExecutionBudget::default(),
                        )
                    })
                });
            let result = result.unwrap();
            assert!(
                result.is_ok(),
                "the dependency chain should evaluate: {result:?}"
            );
            assert_eq!(
                attempts,
                size * 2 - 1,
                "each blocked clause should be retried once after its provider: size={size}"
            );
            (size, work, attempts)
        })
        .collect::<Vec<_>>();
    assert!(
        samples
            .windows(2)
            .all(|pair| { pair[1].1 <= pair[0].1.saturating_mul(4) + 256 }),
        "dependent clause work should stay bounded by the dependency graph: {samples:?}"
    );
}

/// A concrete pending load can be woken by a later symbolic range only after
/// that range's own base has become readable.  This three-clause chain keeps
/// the symbolic provider out of the initial section supply, so the positive
/// result exercises the block-local fallback event rather than the initial
/// pending scan.
#[test]
fn symbolic_supplied_range_wakes_concrete_pending_dependency() {
    let seed = Pointer {
        block: PointerBlock::Concrete("resource-clause-symbolic-seed".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let intermediate = Pointer {
        block: PointerBlock::Concrete("resource-clause-symbolic-intermediate".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let target = Pointer {
        block: PointerBlock::Concrete("resource-clause-symbolic-target".to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    let length = Bitvector32Term::Variable(Variable(9_903));
    let load = |pointer: Pointer| CExpression::TypedLoad {
        pointer: Box::new(c_pointer_value(pointer)),
        value_type: CType::Int32Pointer,
        volatile: false,
    };
    let owned = |base: CExpression, end: CExpression| {
        CResourceSpec::owned_memory(CMemorySegment {
            base,
            start: c_int32_literal(0),
            end,
            element_width: 4,
            guard: None,
        })
    };
    let clauses = vec![
        // A waits on the concrete cell at `intermediate`, but is listed first.
        owned(load(intermediate.clone()), c_int32_literal(1)),
        // B is the symbolic provider for that cell.  Its base load waits on C.
        owned(
            load(seed.clone()),
            CExpression::Value(int32(length.clone())),
        ),
        // C is the only clause that can evaluate on the first pass.
        owned(c_pointer_value(seed.clone()), c_int32_literal(1)),
    ];
    let memory = CMemory::new()
        .store(seed, CValue::pointer(intermediate.clone()))
        .store(intermediate, CValue::pointer(target));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), length),
        true,
    );
    let result = crate::kernel::functions::evaluate_function_resource_context(
        &CState::new().with_memory(memory),
        &clauses,
        &[],
        &assumptions,
        &mut ExecutionBudget::default(),
    )
    .expect("clause evaluation stays inside its budget")
    .expect("the symbolic provider should wake the concrete pending clause");
    assert_eq!(result.facts().len(), 3);
}
