//! Scalar-input facts authorize object geometry, never bytes or initialization.
use super::*;

fn layout(nominal: bool) -> CAggregateLayout {
    let layout = CAggregateLayout::new(
        16,
        8,
        vec![
            CAggregateField::new("pointer", 0, CType::Int32Pointer),
            CAggregateField::new("saved", 8, CType::Int32),
        ],
    );
    layout.with_declaration_identity(nominal.then(|| {
        Arc::new(
            crate::kernel::primitives::CppRecordDeclarationIdentity::new(
                "scalar-object-test-import",
                "Restore",
            ),
        )
    }))
}

fn scalar(address: Pointer) -> CPointerValue {
    CPointerValue::new(address.clone(), CType::Int32Pointer).with_designation(
        PointerDesignation::Object {
            root: address.clone(),
            path: Arc::from([]),
            base: address,
            element_type: CType::Int32,
            stride: 4,
            count: IntegerTerm::constant_i64(1).into(),
        },
    )
}

fn separate(left: Pointer, width: u32, right: Pointer) -> Proposition {
    Proposition::CResourceSeparate {
        left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
            left,
            0u32.into(),
            1u32.into(),
            width,
        ))),
        right: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
            right,
            0u32.into(),
            1u32.into(),
            4,
        ))),
    }
}

fn setup() -> (Pointer, CPointerValue, PureFactContext) {
    let object = Pointer::symbolic(Variable(940_200));
    let input = scalar(Pointer::symbolic(Variable(940_201)));
    let facts = PureFactContext::new()
        .assume_proposition(separate(object.clone(), 8, input.pointer().clone()))
        .assume_proposition(separate(
            object.offset_by_bytes(8),
            4,
            input.pointer().clone(),
        ));
    (object, input, facts)
}

fn raw_object(object: &Pointer) -> CMemory {
    CMemory::new().with_uninitialized_object(object.clone(), 16)
}

#[test]
fn scalar_object_padding_requires_both_authenticated_nominal_inputs() {
    let _session = crate::kernel::VerificationSession::enter();
    let (object, input, facts) = setup();
    let raw = raw_object(&object);
    assert!(raw.may_read_uninitialized_object_under(input.pointer(), 4, &facts));
    let object_only = raw
        .clone()
        .with_object_input_domain(object.clone(), &layout(true))
        .unwrap();
    assert!(object_only.may_read_uninitialized_object_under(input.pointer(), 4, &facts));
    let scalar_only = raw
        .clone()
        .with_scalar_input_domain(input.clone(), CType::Int32)
        .unwrap();
    assert!(scalar_only.may_read_uninitialized_object_under(input.pointer(), 4, &facts));
    let structural = scalar_only
        .clone()
        .with_object_input_domain(object.clone(), &layout(false))
        .unwrap();
    assert!(structural.may_read_uninitialized_object_under(input.pointer(), 4, &facts));
    let witnessed = scalar_only
        .with_object_input_domain(object, &layout(true))
        .unwrap();
    assert!(!witnessed.may_read_uninitialized_object_under(input.pointer(), 4, &facts));
    assert!(witnessed.may_read_uninitialized_object_under(input.pointer(), 8, &facts));
    assert!(!witnessed.has_initialized_bytes_at(input.pointer(), 4));
    assert!(!witnessed.has_block(&input.pointer().block));
    assert!(
        witnessed
            .clone()
            .with_scalar_input_domain(
                CPointerValue::new(input.pointer().clone(), CType::Int32Pointer),
                CType::Int32,
            )
            .is_err(),
        "a raw carrier cannot issue an input witness"
    );
}

#[test]
fn scalar_object_padding_checks_full_field_widths_and_actual_aliases() {
    let _session = crate::kernel::VerificationSession::enter();
    let (object, input, facts) = setup();
    let memory = raw_object(&object)
        .with_object_input_domain(object.clone(), &layout(true))
        .unwrap()
        .with_scalar_input_domain(input.clone(), CType::Int32)
        .unwrap();
    let narrow = PureFactContext::new()
        .assume_proposition(separate(object.clone(), 4, input.pointer().clone()))
        .assume_proposition(separate(
            object.offset_by_bytes(8),
            4,
            input.pointer().clone(),
        ));
    assert!(
        crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
            &object,
            4,
            input.pointer(),
            4,
            &narrow,
        )
    );
    assert!(
        !crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
            &object,
            8,
            input.pointer(),
            4,
            &narrow,
        ),
        "separation of a four-byte prefix cannot frame the complete eight-byte field"
    );
    assert!(memory.may_read_uninitialized_object_under(input.pointer(), 4, &narrow));
    assert!(memory.may_read_uninitialized_object_under(
        input.pointer(),
        4,
        &PureFactContext::new()
    ));
    assert!(!memory.may_read_uninitialized_object_under(input.pointer(), 4, &facts));
    for offset in [0, 8, 12] {
        let aliased = scalar(object.offset_by_bytes(offset));
        let aliased_memory = memory
            .clone()
            .with_scalar_input_domain(aliased.clone(), CType::Int32)
            .unwrap();
        assert!(
            aliased_memory.may_read_uninitialized_object_under(aliased.pointer(), 4, &facts),
            "actual field or padding alias at {offset} must retain the raw footprint"
        );
    }
    let declared =
        CMemory::new().with_declared_aggregate_block(object.block.clone(), &layout(true));
    assert!(
        declared
            .with_scalar_input_domain(scalar(object.offset_by_bytes(12)), CType::Int32)
            .is_err(),
        "a forged complete scalar selection cannot override a declared record's padding"
    );
}

#[test]
fn scalar_object_padding_uses_complete_field_coverage_from_validated_composition() {
    let _session = crate::kernel::VerificationSession::enter();
    // Match symbolic source entry: both parameters share external coordinates,
    // and no assumption says the scalar is outside the record's padding.
    let address = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(variable)), 4),
    };
    let object = address(940_210);
    let input = scalar(address(940_211));
    let memory = raw_object(&object)
        .with_object_input_domain(object.clone(), &layout(true))
        .unwrap()
        .with_scalar_input_domain(input.clone(), CType::Int32)
        .unwrap();
    let owned = |base, end, width| {
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base,
            0u32.into(),
            end,
            width,
        ))
    };
    let composition = ResourceContext::new()
        .unchecked_with_fact(owned(object.clone(), 2u32.into(), 4))
        .unchecked_with_fact(owned(object.offset_by_bytes(8), 1u32.into(), 4))
        .unchecked_with_fact(owned(input.pointer().clone(), 1u32.into(), 4));
    let facts =
        PureFactContext::new().assume_proposition(Proposition::CResourceComposition(composition));
    assert!(!facts.proves_stated_byte_separation(input.pointer(), 4, &object, 16));
    assert!(!memory.may_read_uninitialized_object_under(input.pointer(), 4, &facts));
    // A composition owning only the pointer field's first four bytes does not
    // cover its full access and cannot exclude the record's raw footprint.
    let narrow_composition = ResourceContext::new()
        .unchecked_with_fact(owned(object.clone(), 1u32.into(), 4))
        .unchecked_with_fact(owned(object.offset_by_bytes(8), 1u32.into(), 4))
        .unchecked_with_fact(owned(input.pointer().clone(), 1u32.into(), 4));
    let narrow = PureFactContext::new()
        .assume_proposition(Proposition::CResourceComposition(narrow_composition));
    assert!(memory.may_read_uninitialized_object_under(input.pointer(), 4, &narrow));
}

#[test]
fn scalar_object_authentication_does_not_initialize_or_survive_ended_lifetimes() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Pointer {
        block: "local:scalar-object-noinit".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = scalar(address.clone());
    let memory = CMemory::new()
        .with_declared_scalar_block(address.block.clone(), 4, CType::Int32)
        .with_scalar_input_domain(value.clone(), CType::Int32)
        .unwrap();
    assert!(memory.has_scalar_object_domain(&value, CType::Int32));
    assert!(!memory.has_initialized_bytes_at(&address, 4));
    let ended = memory.without_local_block(&address.block);
    assert!(!ended.has_scalar_object_domain(&value, CType::Int32));
    assert!(!ended.has_initialized_bytes_at(&address, 4));
    assert!(!ended.has_scalar_object_domain(
        &scalar(Pointer {
            block: "null".into(),
            offset: PointerOffsetTerm::Constant(0)
        }),
        CType::Int32
    ));
}

#[test]
fn scalar_object_padding_query_ignores_unrelated_input_registry_growth() {
    let _session = crate::kernel::VerificationSession::enter();
    let (object, input, facts) = setup();
    let mut costs = Vec::new();
    for count in [16, 128, 1024] {
        let mut memory = raw_object(&object)
            .with_object_input_domain(object.clone(), &layout(true))
            .unwrap()
            .with_scalar_input_domain(input.clone(), CType::Int32)
            .unwrap();
        for index in 0..count {
            let unrelated = Pointer::symbolic(Variable(941_000 + index));
            memory = memory
                .with_scalar_input_domain(scalar(unrelated.clone()), CType::Int32)
                .unwrap()
                .with_object_input_domain(unrelated, &layout(true))
                .unwrap();
        }
        let (overlaps, cost) = crate::instrumentation::measure_deterministic_work(|| {
            memory.may_read_uninitialized_object_under(input.pointer(), 4, &facts)
        });
        assert!(!overlaps);
        costs.push(cost);
    }
    assert!(
        costs.windows(2).all(|pair| pair[0] == pair[1]),
        "selected padding query costs {costs:?}"
    );
}

fn lifetime_input(
    root: &Pointer,
    aggregate: bool,
    declared: bool,
) -> (CMemory, CPointerValue, CFunction) {
    let mut memory = CMemory::new();
    let pointer = if aggregate {
        let layout = Arc::new(layout(true));
        if declared {
            memory = memory.with_declared_aggregate_block(root.block.clone(), &layout);
        }
        memory = memory
            .with_object_input_domain(root.clone(), &layout)
            .unwrap();
        CMemory::aggregate_input_pointer(root.clone(), &layout, CType::Int32Pointer)
    } else {
        if declared {
            memory = memory.with_declared_scalar_block(root.block.clone(), 4, CType::Int32);
        }
        memory = memory
            .with_scalar_input_domain(scalar(root.clone()), CType::Int32)
            .unwrap();
        scalar(root.clone())
    };
    let function = c_function(
        CType::Void,
        "live_input",
        vec![c_parameter("pointer", CType::Int32Pointer)],
        c_return(CExpression::Value(CValue::Void)),
    );
    let function = if aggregate {
        function.with_aggregate_object_inputs(vec![CAggregateObjectInput {
            parameter_index: 0,
            layout: Arc::new(layout(true)),
        }])
    } else {
        function.with_scalar_object_inputs(vec![CScalarObjectInput {
            parameter_index: 0,
            element_type: CType::Int32,
        }])
    };
    (memory, pointer, function)
}

fn assert_input_binding(
    memory: CMemory,
    pointer: &CPointerValue,
    function: &CFunction,
    accepted: bool,
) {
    let caller = CState::new().with_memory(memory);
    let values = [CValue::Pointer(pointer.clone())];
    assert_eq!(
        bind_c_function_arguments(&caller, function, &values).is_some(),
        accepted
    );
    assert_eq!(
        bind_c_contract_arguments(&caller, function.contract_interface(), &values, None).is_some(),
        accepted,
    );
}

#[test]
fn scalar_object_inputs_do_not_survive_free_or_contract_retirement_through_equal_alias() {
    let _session = crate::kernel::VerificationSession::enter();
    let root = Pointer::symbolic(Variable(943_000));
    let freed = Pointer::symbolic(Variable(943_001));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(root.clone(), freed.clone()),
        true,
    ));
    assert!(!assumptions.is_inconsistent());
    for aggregate in [false, true] {
        for declared in [false, true] {
            let (memory, pointer, function) = lifetime_input(&root, aggregate, declared);
            let memory = memory
                .with_heap_allocation_claim(freed.clone(), 16)
                .unwrap();
            assert_input_binding(memory.clone(), &pointer, &function, true);
            let after_free = memory
                .clone()
                .free_heap_block(&freed, &assumptions)
                .unwrap();
            // The deallocation spelling alone does not reveal the alias to
            // the binder's empty-context query. Retirement must remove its
            // authenticated input fact, including a removed declaration's
            // fallback entry, before either binder can use it again.
            assert!(!after_free.is_deallocated_heap_address(&root, &PureFactContext::new()));
            assert_input_binding(after_free, &pointer, &function, false);
            let after_contract =
                memory.retire_contract_heap_allocation_claim(&freed, &16u32.into(), &assumptions);
            assert_input_binding(after_contract, &pointer, &function, false);
        }
    }
}

#[test]
fn scalar_object_input_retirement_requires_complete_separation_even_without_ownership() {
    let _session = crate::kernel::VerificationSession::enter();
    let freed = Pointer::symbolic(Variable(943_010));
    let root = Pointer::symbolic(Variable(943_011));
    for aggregate in [false, true] {
        let (memory, pointer, function) = lifetime_input(&root, aggregate, false);
        let memory = memory
            .with_heap_allocation_claim(freed.clone(), 16)
            .unwrap();
        let width = if aggregate { 16 } else { 4 };
        let full = Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                freed.clone(),
                0u32.into(),
                1u32.into(),
                16,
            ))),
            right: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                root.clone(),
                0u32.into(),
                1u32.into(),
                width,
            ))),
        };
        let separated = PureFactContext::new().assume_proposition(full);
        let narrow =
            PureFactContext::new().assume_proposition(separate(freed.clone(), 4, root.clone()));
        let unequal = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(root.clone(), freed.clone()),
            false,
        ));
        for (facts, accepted) in [
            (PureFactContext::new(), false),
            (unequal, false),
            (narrow, false),
            (separated, true),
        ] {
            let after_free = memory.clone().free_heap_block(&freed, &facts).unwrap();
            assert_input_binding(after_free, &pointer, &function, accepted);
            let after_contract =
                memory
                    .clone()
                    .retire_contract_heap_allocation_claim(&freed, &16u32.into(), &facts);
            assert_input_binding(after_contract, &pointer, &function, accepted);
        }
        // The registered geometry requires neither ownership nor initialized
        // bytes. Therefore absence of an owner cannot preserve its lifetime.
        assert!(!memory.has_initialized_bytes_at(&root, width));
    }
}

#[test]
fn scalar_object_input_retirement_preserves_symbolically_separated_extents() {
    let _session = crate::kernel::VerificationSession::enter();
    let freed = Pointer::symbolic(Variable(943_020));
    let root = Pointer::symbolic(Variable(943_021));
    let bytes = Bitvector32Term::Variable(Variable(943_022));
    for aggregate in [false, true] {
        let (memory, pointer, function) = lifetime_input(&root, aggregate, false);
        let memory = memory
            .with_heap_allocation_claim(freed.clone(), bytes.clone())
            .unwrap();
        let allocation_range =
            CMemoryRange::new_with_element_width(freed.clone(), 0u32.into(), bytes.clone(), 1);
        let object_range = CMemoryRange::new_with_element_width(
            root.clone(),
            0u32.into(),
            1u32.into(),
            if aggregate { 16 } else { 4 },
        );
        let stated = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(allocation_range.clone())),
            right: Box::new(CResource::Memory(object_range.clone())),
        });
        let composition = ResourceContext::new()
            .unchecked_with_fact(CResourceFact::own_memory(allocation_range))
            .unchecked_with_fact(CResourceFact::own_memory(object_range));
        let composed = PureFactContext::new()
            .assume_proposition(Proposition::CResourceComposition(composition));
        for facts in [stated, composed] {
            let after_free = memory.clone().free_heap_block(&freed, &facts).unwrap();
            assert_input_binding(after_free, &pointer, &function, true);
            let after_contract = memory
                .clone()
                .retire_contract_heap_allocation_claim(&freed, &bytes, &facts);
            assert_input_binding(after_contract, &pointer, &function, true);
        }
    }
}

#[test]
fn scalar_object_input_retirement_skips_unrelated_fresh_allocations() {
    let mut costs = Vec::new();
    for count in [16, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let freed = Pointer {
            block: PointerBlock::Heap(943_030),
            offset: PointerOffsetTerm::Constant(0),
        };
        let root = Pointer::symbolic(Variable(943_031));
        let (mut memory, pointer, function) = lifetime_input(&root, false, false);
        memory = memory
            .with_heap_allocation_claim(freed.clone(), 16)
            .unwrap();
        for index in 0..count {
            let unrelated = Pointer {
                block: PointerBlock::Heap(944_000 + index),
                offset: PointerOffsetTerm::Constant(0),
            };
            memory = if index % 2 == 0 {
                memory
                    .with_scalar_input_domain(scalar(unrelated), CType::Int32)
                    .unwrap()
            } else {
                memory
                    .with_object_input_domain(unrelated, &layout(true))
                    .unwrap()
            };
        }
        let assumptions = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(root, freed.clone()),
            true,
        ));
        let (retired, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory.free_heap_block(&freed, &assumptions).unwrap()
        });
        assert_input_binding(retired.clone(), &pointer, &function, false);
        assert_eq!(retired.heap.scalar_input_domains.len(), count as usize / 2);
        assert_eq!(retired.heap.object_input_domains.len(), count as usize / 2);
        costs.push(work);
    }
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn scalar_object_padding_uses_cross_block_native_input_composition() {
    let _session = crate::kernel::VerificationSession::enter();
    // The original constructor's receiver is symbolic, while its scalar
    // reference argument uses external parameter coordinates.
    let object = Pointer::symbolic(Variable(945_000));
    let input = scalar(Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(945_001)), 4),
    });
    let memory = raw_object(&object)
        .with_object_input_domain(object.clone(), &layout(true))
        .unwrap()
        .with_scalar_input_domain(input.clone(), CType::Int32)
        .unwrap();
    let owned = |base, end, width| {
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base,
            0u32.into(),
            end,
            width,
        ))
    };
    let facts = |pointer_end| {
        PureFactContext::new().assume_proposition(Proposition::CResourceComposition(
            ResourceContext::new()
                .unchecked_with_fact(owned(object.clone(), pointer_end, 4))
                // The source owns-field slot includes the final tail padding.
                .unchecked_with_fact(owned(object.offset_by_bytes(8), 2u32.into(), 4))
                .unchecked_with_fact(owned(input.pointer().clone(), 1u32.into(), 4)),
        ))
    };
    let full = facts(2u32.into());
    assert!(!full.proves_stated_byte_separation(input.pointer(), 4, &object, 16));
    assert!(
        crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
            &object,
            8,
            input.pointer(),
            4,
            &full,
        )
    );
    let proof = crate::kernel::memory_provenance::typed_store_separated_ranges_evidence(
        &object,
        8,
        input.pointer(),
        4,
        &full,
    )
    .expect("cross-block composition carries checked complete-width evidence");
    let step = CMemoryDerivation::Store {
        base: crate::kernel::intern_c_memory(CMemory::new()),
        pointer: object.clone(),
        value: CValue::typed_pointer(Pointer::null(), CType::Int32Pointer),
    };
    assert!(proof.checks(&step, input.pointer(), 4, &full));
    assert!(!proof.checks(&step, input.pointer(), 4, &PureFactContext::new()));
    assert!(!memory.may_read_uninitialized_object_under(input.pointer(), 4, &full));
    let narrow = facts(1u32.into());
    assert!(
        !crate::kernel::memory_provenance::write_access_is_disjoint_from_load(
            &object,
            8,
            input.pointer(),
            4,
            &narrow,
        )
    );
    assert!(memory.may_read_uninitialized_object_under(input.pointer(), 4, &narrow));
    assert!(!memory.has_initialized_bytes_at(input.pointer(), 4));
}

#[test]
fn cross_block_composition_requires_owned_members_and_refuses_literal_aliases() {
    let _session = crate::kernel::VerificationSession::enter();
    let left = Pointer::symbolic(Variable(945_010));
    let right = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(945_011)),
    };
    let range = |base| CMemoryRange::new_with_element_width(base, 0u32.into(), 1u32.into(), 4);
    let viewed = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(range(left.clone())))
        .unchecked_with_fact(CResourceFact::view_memory(range(right.clone())));
    assert!(
        viewed
            .separated_owned_members_across_blocks(
                &left.block,
                &right.block,
                |_| true,
                |_| true,
                |_, _| true,
            )
            .is_none()
    );
    let literals = |identity: &str| Pointer {
        block: PointerBlock::StringLiteral {
            identity: identity.into(),
            bytes: b"abc\0".to_vec(),
        },
        offset: PointerOffsetTerm::Constant(0),
    };
    let a = literals("left-literal");
    let b = literals("right-literal");
    let literal_owners = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(range(a.clone())))
        .unchecked_with_fact(CResourceFact::own_memory(range(b.clone())));
    assert!(
        literal_owners
            .separated_owned_members_across_blocks(
                &a.block,
                &b.block,
                |_| true,
                |_| true,
                |_, _| true,
            )
            .is_none()
    );
    // One owned member cannot separate two accesses it both contains. The
    // existing same-block selection keeps its entry-identity check.
    let same = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(range(left.clone())))
        .unchecked_with_fact(CResourceFact::own_memory(range(left.offset_by_bytes(8))));
    assert!(
        same.separated_owned_members_in_block(
            &left.block,
            |range| range.base() == &left,
            |range| range.base() == &left,
            |_, _| true,
        )
        .is_none()
    );
}

#[test]
fn cross_block_composition_queries_are_indexed_and_bound_rejected_pairs() {
    let mut costs = Vec::new();
    for count in [16u32, 128, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let left = Pointer::symbolic(Variable(945_020));
        let right = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(945_021)),
        };
        let range = |base| CMemoryRange::new_with_element_width(base, 0u32.into(), 1u32.into(), 4);
        let mut context = ResourceContext::new();
        for index in 0..count {
            context = context
                .unchecked_with_fact(CResourceFact::own_memory(range(
                    left.offset_by_bytes(index * 16),
                )))
                .unchecked_with_fact(CResourceFact::own_memory(range(
                    right.offset_by_bytes(index * 16),
                )))
                .unchecked_with_fact(CResourceFact::own_memory(range(Pointer::symbolic(
                    Variable(946_000 + index as u64),
                ))));
        }
        let admissions = std::cell::Cell::new(0usize);
        let (selected, rejected_work) = crate::instrumentation::measure_deterministic_work(|| {
            context.separated_owned_members_across_blocks(
                &left.block,
                &right.block,
                |_| true,
                |_| true,
                |_, _| {
                    admissions.set(admissions.get() + 1);
                    false
                },
            )
        });
        assert!(selected.is_none());
        assert_eq!(admissions.get(), 4);
        assert!(rejected_work <= 10, "{rejected_work}");
        let target_left = left.offset_by_bytes((count - 1) * 16);
        let target_right = right.offset_by_bytes((count - 1) * 16);
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.separated_owned_members_across_blocks(
                &left.block,
                &right.block,
                |range| range.base() == &target_left,
                |range| range.base() == &target_right,
                |_, _| true,
            )
        });
        assert!(selected.is_some());
        assert!(work <= 2 * count as usize + 4, "{count}: {work}");
        costs.push(rejected_work);
    }
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn symbolic_retirement_accepts_equivalent_element_and_byte_footprints() {
    let _session = crate::kernel::VerificationSession::enter();
    let freed = Pointer::symbolic(Variable(943_030));
    let root = Pointer::symbolic(Variable(943_031));
    let count = Bitvector32Term::Variable(Variable(943_032));
    let bytes = Bitvector32Term::Multiply(Box::new(count.clone()), Box::new(4u32.into()));
    for aggregate in [false, true] {
        let (memory, pointer, function) = lifetime_input(&root, aggregate, false);
        let memory = memory
            .with_heap_allocation_claim(freed.clone(), bytes.clone())
            .unwrap();
        let width: u32 = if aggregate { 16 } else { 4 };
        for (held_end, bounded, accepted) in [
            (count.clone(), true, true),
            (count.clone(), false, false),
            (
                Bitvector32Term::Subtract(Box::new(count.clone()), Box::new(1u32.into())),
                true,
                false,
            ),
        ] {
            let mut facts =
                PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
                    left: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                        freed.clone(),
                        0u32.into(),
                        held_end,
                        4,
                    ))),
                    right: Box::new(CResource::Memory(CMemoryRange::new_with_element_width(
                        root.clone(),
                        0u32.into(),
                        (width / 4).into(),
                        4,
                    ))),
                });
            if bounded {
                facts = facts
                    .assume_condition(
                        ConditionTerm::signed_less_equal(0u32.into(), count.clone()),
                        true,
                    )
                    .assume_condition(
                        ConditionTerm::signed_less_equal(count.clone(), 1000u32.into()),
                        true,
                    );
            }
            let after_free = memory.clone().free_heap_block(&freed, &facts).unwrap();
            assert_input_binding(after_free, &pointer, &function, accepted);
            let after_contract = memory
                .clone()
                .retire_contract_heap_allocation_claim(&freed, &bytes, &facts);
            assert_input_binding(after_contract, &pointer, &function, accepted);
        }
    }
}
