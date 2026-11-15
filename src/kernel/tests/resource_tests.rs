// These tests exercise discovery explicitly through kernel::search::ProofSearch.
use super::*;
use crate::kernel::LoanViewBinding;
use crate::kernel::binary_node;
use crate::kernel::int32_constant;
use crate::kernel::loans::{LoanLedger, LoanViewBindings};
use crate::kernel::{CompareRelation, MachineIntegerType};

/// A fold publishes read authority for the cells it consumed, attached to
/// the folded instance. Folding what an unfold opened returns the state the
/// unfold started from, apart from that observation.
fn folded_without_read_views(state: ExecutionState) -> ExecutionState {
    let resources = state
        .resources()
        .clone()
        .without_owned_instance_read_views();
    state.with_resource_context(resources)
}

#[test]
fn separation_candidates_preserve_derived_aliases_and_loaded_bases() {
    let _session = crate::kernel::VerificationSession::enter();
    let scalar = |id: u64| MachineTerm::Variable(Variable(989_700 + id));
    let base = |value| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(value, 4),
    };
    let owner = |pointer| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            pointer,
            0u32.into(),
            3u32.into(),
            4,
        ))
    };
    let query = |pointer| {
        Resource::Memory(MemoryRange::new_with_element_width(
            pointer,
            1u32.into(),
            2u32.into(),
            4,
        ))
    };
    let a = scalar(0);
    let b = scalar(1);
    let alias = scalar(2);
    let middle = scalar(3);
    let frame = ResourceContext::new()
        .unchecked_with_fact(owner(base(a.clone())))
        .unchecked_with_fact(owner(base(b.clone())));
    let holds = |context: PureFactContext| {
        context.assume_proposition(Proposition::ResourceComposition(frame.clone()))
    };
    let separated = |context: &PureFactContext| {
        context.proves_resource_separate(&query(base(alias.clone())), &query(base(b.clone())))
    };
    assert!(!separated(&holds(PureFactContext::new())));
    let one_order = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_equal(a.clone(), alias.clone()),
        true,
    );
    assert!(
        !separated(&holds(one_order.clone())),
        "one bound is not an alias"
    );
    let both_orders = one_order.assume_condition(
        ConditionTerm::signed_less_equal(alias.clone(), a.clone()),
        true,
    );
    assert!(separated(&holds(both_orders)));
    let pinned = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(a.clone(), 7u32.into()), true)
        .assume_condition(ConditionTerm::equal(alias.clone(), 7u32.into()), true);
    assert!(separated(&holds(pinned)));
    let transitive = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_equal(base(alias.clone()), base(middle.clone())),
            true,
        )
        .assume_condition(
            ConditionTerm::pointer_equal(base(middle), base(a.clone())),
            true,
        );
    assert!(separated(&holds(transitive)));

    // No condition names `a`: the owner's loaded base must remain a
    // candidate because the memory edge itself resolves it to `a`.
    let slot = Pointer::symbolic(Variable(989_799));
    let retained_state = Memory::new().store(slot.clone(), ProgramValue::Int32(a.clone()));
    let loaded = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(retained_state),
        Box::new(slot),
        LoadKind::Int32,
    );
    let loaded_frame = ResourceContext::new()
        .unchecked_with_fact(owner(base(loaded)))
        .unchecked_with_fact(owner(base(b.clone())));
    let facts =
        PureFactContext::new().assume_proposition(Proposition::ResourceComposition(loaded_frame));
    assert!(facts.proves_resource_separate(&query(base(a.clone())), &query(base(b.clone()))));
    assert!(!facts.proves_resource_separate(&query(base(a.clone())), &query(base(a))));
}

#[test]
fn separation_candidates_follow_a_block_alias_to_the_owner() {
    // `__rb_insert` in the sized double rotations: the queried range sits in
    // a fresh symbolic block that a pointer equality identifies with a
    // parameter's address, so its owner lives in another block.
    let _session = crate::kernel::VerificationSession::enter();
    let a = MachineTerm::Variable(Variable(989_800));
    let parameter = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(a, 4),
    };
    let loaded = Pointer::symbolic(Variable(989_801));
    let target = Pointer::symbolic(Variable(989_802));
    let range = |pointer: Pointer, start: u32, end: u32| {
        MemoryRange::new_with_element_width(pointer, start.into(), end.into(), 4)
    };
    let frame = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(range(parameter.clone(), 1, 2)))
        .unchecked_with_fact(ResourceFact::own_memory(range(target.clone(), 1, 2)));
    let query = |context: &PureFactContext| {
        context.proves_resource_separate(
            &Resource::Memory(range(target.clone(), 1, 2)),
            &Resource::Memory(range(loaded.clone(), 1, 2)),
        )
    };
    let unrelated =
        PureFactContext::new().assume_proposition(Proposition::ResourceComposition(frame.clone()));
    assert!(!query(&unrelated), "an unowned range proves nothing");
    let aliased = unrelated.assume_condition(
        ConditionTerm::pointer_equal(loaded.clone(), parameter.clone()),
        true,
    );
    assert!(query(&aliased));
}

#[test]
fn normalized_resource_specs_validate_families_and_preserve_transfer_metadata() {
    let segment = MemorySegment::new(
        crate::kernel::program_expression::variable("p"),
        crate::kernel::program_expression::int32_literal(0),
        crate::kernel::program_expression::int32_literal(2),
    );
    let memory_view = ResourceSpec::new(
        ResourceTerm::Memory(segment.clone()),
        ResourceAccessMode::View,
        ResourceQuantity::One,
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    assert_eq!(memory_view.family(), ResourceFamily::Memory);
    assert_eq!(memory_view.access(), ResourceAccessMode::View);
    assert_eq!(memory_view.role(), ResourceTransferRole::Borrow);
    assert_eq!(memory_view.state_source(), ResourceStateSource::Entry);
    assert_eq!(
        memory_view.clone().with_clause_position(0, 2),
        memory_view.clone().with_clause_position(1, 9)
    );

    let memory_owner = ResourceSpec::new(
        ResourceTerm::Memory(segment),
        ResourceAccessMode::Own,
        ResourceQuantity::One,
        ResourceTransferRole::Consume,
        ResourceStateSource::Current,
    )
    .unwrap();
    assert!(memory_owner.memory_segment().is_some());

    let composite_view = ResourceSpec::declared(
        ResourceFamily::Composite,
        ResourceAccessMode::View,
        "box".into(),
        vec![],
        vec![],
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let token_owner = ResourceSpec::declared(
        ResourceFamily::Token,
        ResourceAccessMode::Own,
        "permit".into(),
        vec![],
        vec![],
        ResourceTransferRole::Produce,
        ResourceStateSource::Post,
    )
    .unwrap();
    assert_eq!(composite_view.family(), ResourceFamily::Composite);
    assert_eq!(token_owner.family(), ResourceFamily::Token);
    assert_eq!(token_owner.role(), ResourceTransferRole::Produce);
    assert_eq!(token_owner.state_source(), ResourceStateSource::Post);

    let counted = ResourceSpec::quantified(
        crate::kernel::program_expression::int32_literal(3),
        token_owner.clone(),
        ResourceTransferRole::Consume,
        ResourceStateSource::Current,
    )
    .unwrap();
    assert!(matches!(counted.quantity(), ResourceQuantity::Count(_)));

    assert!(matches!(
        ResourceSpec::new(
            ResourceTerm::Memory(MemorySegment::new(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(0),
                crate::kernel::program_expression::int32_literal(1),
            )),
            ResourceAccessMode::Own,
            ResourceQuantity::Count(crate::kernel::program_expression::int32_literal(2)),
            ResourceTransferRole::Consume,
            ResourceStateSource::Entry,
        ),
        Err(ResourceSpecError::InvalidQuantity {
            family: ResourceFamily::Memory,
            ..
        })
    ));
    assert!(matches!(
        ResourceSpec::quantified(
            crate::kernel::program_expression::int32_literal(2),
            composite_view,
            ResourceTransferRole::Consume,
            ResourceStateSource::Current,
        ),
        Err(ResourceSpecError::InvalidAccess {
            family: ResourceFamily::Composite,
            access: ResourceAccessMode::View,
        })
    ));

    let schema = ResourceFieldSchema::new(vec![]).unwrap();
    let instance_term = ResourceTerm::Instance {
        identity: Variable(77),
        binder: "cell".into(),
        schema: schema.clone(),
        resource: Box::new(ResourceTerm::Composite {
            name: "cell".into(),
            arguments: vec![],
            argument_state_sources: vec![],
            parameter_types: vec![],
        }),
    };
    assert!(matches!(
        ResourceSpec::new(
            instance_term.clone(),
            ResourceAccessMode::View,
            ResourceQuantity::One,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        ),
        Err(ResourceSpecError::InvalidAccess {
            family: ResourceFamily::Instance,
            access: ResourceAccessMode::View,
        })
    ));
    assert!(
        ResourceSpec::new(
            instance_term,
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        )
        .is_ok()
    );
    assert!(matches!(
        ResourceSpec::new(
            ResourceTerm::Instance {
                identity: Variable(78),
                binder: "token".into(),
                schema,
                resource: Box::new(ResourceTerm::Token {
                    name: "token".into(),
                    arguments: vec![],
                    argument_state_sources: vec![],
                    parameter_types: vec![],
                }),
            },
            ResourceAccessMode::Own,
            ResourceQuantity::One,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        ),
        Err(ResourceSpecError::InvalidNestedTerm(_))
    ));
}

#[test]
fn validated_resource_rebuilds_preserve_metadata_and_instance_bodies() {
    let variable = Variable(77_700);
    let quantity = ProgramExpression::Value(int32(MachineTerm::Variable(variable)));
    let spec = ResourceSpec::new(
        ResourceTerm::Token {
            name: "permit".into(),
            arguments: vec![quantity.clone()],
            argument_state_sources: vec![ResourceStateSource::Current],
            parameter_types: vec![ProgramType::Int32],
        },
        ResourceAccessMode::Own,
        ResourceQuantity::Count(quantity),
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let substituted = crate::kernel::reasoning::substitute_bitvector_variable_in_resource_spec(
        &spec,
        variable,
        &MachineTerm::constant(3),
    );
    assert_eq!(substituted.access(), ResourceAccessMode::Own);
    assert_eq!(substituted.role(), ResourceTransferRole::Borrow);
    assert_eq!(substituted.state_source(), ResourceStateSource::Entry);
    assert!(matches!(
        substituted.quantity(),
        ResourceQuantity::Count(ProgramExpression::Value(ProgramValue::Int32(
            int32_constant!(3)
        )))
    ));
    assert!(matches!(
        substituted.term(),
        ResourceTerm::Token { arguments, .. }
            if matches!(arguments.as_slice(), [ProgramExpression::Value(ProgramValue::Int32(int32_constant!(3)))])
    ));

    let schema = ResourceFieldSchema::new(vec![]).unwrap();
    let instance = ResourceSpec::instance(
        variable,
        "cell".into(),
        schema,
        ResourceSpec::composite(ResourceAccessMode::Own, "cell".into(), vec![], vec![]),
        ResourceTransferRole::Borrow,
        ResourceStateSource::Entry,
    )
    .unwrap();
    let inner = instance
        .instance_resource_spec()
        .expect("validated instance has a reconstructible inner term");
    assert_eq!(inner.access(), ResourceAccessMode::Own);
    assert_eq!(inner.quantity(), &ResourceQuantity::One);
    assert_eq!(inner.role(), ResourceTransferRole::Borrow);
    assert_eq!(inner.state_source(), ResourceStateSource::Entry);

    assert!(matches!(
        ResourceSpec::new(
            ResourceTerm::Instance {
                identity: variable,
                binder: "cell".into(),
                schema: ResourceFieldSchema::new(vec![]).unwrap(),
                resource: Box::new(ResourceTerm::Composite {
                    name: "cell".into(),
                    arguments: vec![],
                    argument_state_sources: vec![],
                    parameter_types: vec![],
                }),
            },
            ResourceAccessMode::View,
            ResourceQuantity::One,
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        ),
        Err(ResourceSpecError::InvalidAccess {
            family: ResourceFamily::Instance,
            access: ResourceAccessMode::View,
        })
    ));
}

#[test]
fn owned_range_access_survives_learning_a_symbolic_pointer_alias() {
    let cell = Pointer::symbolic(Variable(100));
    let slot = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(101)), 4),
    };
    let unrelated = Pointer::symbolic(Variable(102));
    let range = MemoryRange::new(
        cell.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(range));
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

#[test]
fn owned_range_read_survives_learning_a_symbolic_pointer_alias() {
    // A frame's identity payload (symbolic) and the C value loaded for it
    // (external plus an offset) name the same cell once their equality is
    // proved. The owning fact sits under the symbolic spelling; a read
    // through either spelling must find it. The read lookup used to resolve
    // the symbolic pointer to its non-symbolic alias and look only there,
    // refusing a read of a cell the state plainly owned (the insert fixup's
    // `gparent->__rb_parent_color` after `gparent == cgp`).
    let cell = Pointer::symbolic(Variable(100));
    let slot = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(101)), 4),
    };
    let unrelated = Pointer::symbolic(Variable(102));
    let range = MemoryRange::new(
        cell.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(range));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(slot.clone(), cell.clone()),
        true,
    );
    for pointer in [&cell, &slot] {
        assert!(
            resources.permits_memory_read(pointer, 4, &assumptions),
            "read through {pointer:?} should be permitted"
        );
    }
    assert!(!resources.permits_memory_read(&unrelated, 4, &assumptions));
    assert!(!resources.permits_memory_read(&cell, 16, &assumptions));
}

#[test]
fn owned_memory_consumption_survives_a_late_transitive_displaced_alias() {
    // An unfold can publish a cell before a later proof arm establishes the
    // equality used by fold. Keep the resource state fixed while the pure
    // context forks and learns the two links in either order.
    let owner_root = Pointer::symbolic(Variable(210));
    let owner = Pointer {
        block: owner_root.block.clone(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let middle = Pointer::symbolic(Variable(211));
    let requested = Pointer {
        block: PointerBlock::Symbolic(Variable(212)),
        offset: PointerOffsetTerm::Constant(8),
    };
    let cell = |base| {
        ResourceFact::own_memory(MemoryRange::new(
            base,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        ))
    };
    let resources = ResourceContext::new().unchecked_with_fact(cell(owner.clone()));
    let required = cell(requested.clone());
    let empty = PureFactContext::new();
    assert!(
        resources
            .clone()
            .without_fact_incrementally(&required, &empty)
            .is_none()
    );
    for reverse in [false, true] {
        let links = [
            ConditionTerm::pointer_equal(owner_root.clone(), middle.clone()),
            ConditionTerm::pointer_equal(middle.clone(), Pointer::symbolic(Variable(212))),
        ];
        let mut assumptions = empty.clone();
        for link in if reverse {
            links.into_iter().rev().collect::<Vec<_>>()
        } else {
            links.to_vec()
        } {
            assumptions = assumptions.assume_condition(link, true);
        }
        assert!(assumptions.equality_graph.are_equal(&owner, &requested));
        assert!(
            resources
                .clone()
                .without_fact_incrementally(&required, &assumptions)
                .expect("fold must consume the owned cell through the late alias")
                .facts()
                .is_empty()
        );
        assert!(
            resources
                .clone()
                .without_fact_incrementally(
                    &cell(Pointer {
                        block: requested.block.clone(),
                        offset: PointerOffsetTerm::Constant(12)
                    }),
                    &assumptions,
                )
                .is_none()
        );
    }
    assert!(
        resources
            .without_fact_incrementally(&required, &empty)
            .is_none()
    );
}

#[test]
fn paired_memory_index_tracks_resource_deltas_and_displaced_merges() {
    let cell = |base| {
        ResourceFact::own_memory(MemoryRange::new(
            base,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        ))
    };
    let owner = Pointer::symbolic(Variable(810_000));
    let alias = Pointer::symbolic(Variable(810_001));
    let shifted = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let resources = ResourceContext::new().unchecked_with_fact(cell(shifted.clone()));
    let empty = PureFactContext::new();
    resources.synchronize_memory_equalities(&empty);
    // Force the graph to retain the alias representative, while the heavier
    // resource payload retains its own independent address coordinates.
    let mut assumptions = empty.clone();
    for i in 2..20 {
        assumptions = assumptions.assume_condition(
            ConditionTerm::pointer_equal(alias.clone(), Pointer::symbolic(Variable(810_000 + i))),
            true,
        );
        resources.synchronize_memory_equalities(&assumptions);
    }
    assumptions =
        assumptions.assume_condition(ConditionTerm::pointer_equal(alias.clone(), shifted), true);
    resources.synchronize_memory_equalities(&assumptions);
    let required = cell(alias.clone());
    let consumed = resources
        .clone()
        .without_fact_incrementally(&required, &assumptions)
        .unwrap();
    assert!(
        consumed
            .clone()
            .without_fact_incrementally(&required, &assumptions)
            .is_none()
    );
    // Reinsert after the merge, then normalize (which can renumber entries).
    let restored = consumed
        .unchecked_with_fact(cell(owner.clone()))
        .unchecked_with_fact(required.clone())
        .normalized(&assumptions);
    let remaining = restored
        .without_fact_incrementally(&required, &assumptions)
        .unwrap();
    assert!(
        remaining
            .clone()
            .without_fact_incrementally(&required, &assumptions)
            .is_none()
    );
    assert!(
        remaining
            .without_fact_incrementally(&cell(owner), &assumptions)
            .is_some()
    );
    // A sibling equality context must not inherit the warmed alias lookup.
    assert!(
        resources
            .clone()
            .without_fact_incrementally(&required, &empty)
            .is_none()
    );
    assert!(
        resources
            .without_fact_incrementally(&required, &assumptions)
            .is_some()
    );
}

#[test]
fn paired_memory_index_consumes_inside_a_displaced_aliased_range() {
    let owner = Pointer::symbolic(Variable(830_000));
    let alias = Pointer::symbolic(Variable(830_001));
    let resources =
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            owner.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(4),
        )));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(owner, alias.clone()), true);
    let required = ResourceFact::own_memory(MemoryRange::new(
        Pointer {
            block: alias.block.clone(),
            offset: PointerOffsetTerm::Constant(4),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    let residual = resources
        .without_fact_incrementally(&required, &assumptions)
        .expect("consume an interior cell through the equal block");
    assert!(
        residual
            .clone()
            .without_fact_incrementally(&required, &assumptions)
            .is_none()
    );
    let remaining_cell = ResourceFact::own_memory(MemoryRange::new(
        alias,
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    assert!(
        residual
            .without_fact_incrementally(&remaining_cell, &assumptions)
            .is_some()
    );
}

#[test]
fn owned_fragment_reservation_checks_aliases_gaps_and_linear_consumption() {
    let base = Pointer::symbolic(Variable(862_000));
    let returned = Pointer::symbolic(Variable(862_001));
    let bytes = |start: u32, end: u32| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base.clone(),
            start.into(),
            end.into(),
            1,
        ))
    };
    // A returned i32 field sits beside padding still spelled in bytes.
    let field = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        returned.clone(),
        0u32.into(),
        1u32.into(),
        4,
    ));
    let resources = ResourceContext::new()
        .unchecked_with_fact(field.clone())
        .unchecked_with_fact(bytes(12, 16));
    let empty = PureFactContext::new();
    resources.synchronize_memory_equalities(&empty);
    assert!(
        resources
            .clone()
            .reserve_owned_memory_fragments(&bytes(8, 16), &empty)
            .is_none()
    );
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_equal(
            Pointer {
                block: base.block.clone(),
                offset: PointerOffsetTerm::Constant(8),
            },
            returned,
        ),
        true,
    );
    let (remaining, supports) = resources
        .clone()
        .reserve_owned_memory_fragments(&bytes(8, 16), &facts)
        .unwrap();
    assert_eq!(supports.len(), 2);
    assert_ne!(supports[0], supports[1]);
    for support in &supports {
        assert!(resources.owned_fact_for_occurrence(*support).is_some());
        assert!(remaining.owned_fact_for_occurrence(*support).is_none());
    }
    assert!(
        remaining
            .reserve_owned_memory_fragments(&bytes(8, 16), &facts)
            .is_none()
    );
    assert!(
        resources
            .clone()
            .reserve_owned_memory_fragments(&bytes(8, 17), &facts)
            .is_none()
    );
    let viewed = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::view_memory(
            field.memory_own_range().unwrap().clone(),
        ))
        .unchecked_with_fact(bytes(12, 16));
    assert!(
        viewed
            .reserve_owned_memory_fragments(&bytes(8, 16), &facts)
            .is_none()
    );
    // A failed reservation of a larger range did not consume its input.
    assert!(
        resources
            .reserve_owned_memory_fragments(&bytes(8, 16), &facts)
            .is_some()
    );
}

#[test]
fn owned_fragment_reservation_preserves_native_supplier_bounds() {
    let base = Pointer::symbolic(Variable(862_019));
    let owner = ResourceFact::own_memory(MemoryRange::new_wide(
        base.clone(),
        MachineTerm::uint64_constant(0),
        MachineTerm::uint64_constant(16),
        1,
    ));
    let required = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base.clone(),
        0u32.into(),
        4u32.into(),
        1,
    ));
    let facts = PureFactContext::new();
    let resources = ResourceContext::new().unchecked_with_fact(owner.clone());
    resources.synchronize_memory_equalities(&facts);
    let (remaining, supports) = resources
        .clone()
        .reserve_owned_memory_fragments(&required, &facts)
        .expect("an aligned constant piece preserves native coordinates");
    assert_eq!(supports.len(), 1);
    assert_eq!(
        remaining.facts(),
        [ResourceFact::own_memory(MemoryRange::new_wide(
            base,
            MachineTerm::uint64_constant(4),
            MachineTerm::uint64_constant(16),
            1,
        ))]
    );
    assert!(resources.contains_exact_representation(&owner));
    assert!(
        resources
            .directly_supporting_owned_entry(&required, &facts)
            .is_some()
    );
}

#[test]
fn owned_fragment_reservation_joins_mixed_width_fields_at_symbolic_bases() {
    let facts = PureFactContext::new();
    for base in [
        Pointer::symbolic(Variable(862_020)),
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(862_021)),
        },
    ] {
        let memory = |start: u32, end: u32, width| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                base.clone(),
                start.into(),
                end.into(),
                width,
            ))
        };
        let fields = [
            memory(0, 1, 4),
            memory(4, 5, 1),
            memory(5, 6, 1),
            memory(6, 7, 1),
            memory(7, 8, 1),
        ];
        let whole = memory(0, 2, 4);
        let context = |fields: Vec<ResourceFact>| {
            let resources = ResourceContext::new().unchecked_with_facts(fields);
            resources.synchronize_memory_equalities(&facts);
            resources
        };
        let resources = context(fields.to_vec());
        let (remaining, supports) = resources
            .clone()
            .reserve_owned_memory_fragments(&whole, &facts)
            .unwrap();
        assert_eq!(supports.len(), fields.len());
        for support in supports {
            assert!(resources.owned_fact_for_occurrence(support).is_some());
            assert!(remaining.owned_fact_for_occurrence(support).is_none());
        }
        assert!(
            remaining
                .reserve_owned_memory_fragments(&whole, &facts)
                .is_none()
        );
        assert!(
            resources
                .reserve_owned_memory_fragments(&memory(0, 3, 4), &facts)
                .is_none()
        );
        for missing in 0..fields.len() {
            let mut incomplete = fields.to_vec();
            incomplete.remove(missing);
            assert!(
                context(incomplete)
                    .reserve_owned_memory_fragments(&whole, &facts)
                    .is_none()
            );
        }
        let mut viewed = fields.to_vec();
        viewed[4] = ResourceFact::view_memory(fields[4].memory_own_range().unwrap().clone());
        assert!(
            context(viewed)
                .reserve_owned_memory_fragments(&whole, &facts)
                .is_none()
        );
        // Five explicitly owned bytes omit the three padding bytes.
        assert!(
            context(fields[..2].to_vec())
                .reserve_owned_memory_fragments(&whole, &facts)
                .is_none()
        );
    }
}

fn instance_memory_fixture() -> (
    ResourceInstance,
    CompositeResourceDefinition,
    ExecutionState,
) {
    let schema = ResourceFieldSchema::new(vec![(
        "value".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(100)), 4),
    };
    let instance = ResourceInstance::new(
        Variable(1),
        "cell".into(),
        vec![ProgramValue::pointer(pointer).into()].into(),
        schema.clone(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    let definition = CompositeResourceDefinition::new(
        "cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment {
            base: crate::kernel::program_expression::variable("p"),
            start: crate::kernel::program_expression::int32_literal(0),
            end: crate::kernel::program_expression::int32_literal(1),
            element_width: 4,
            guard: None,
            uninitialized: false,
            value_runs: Default::default(),
        })],
        vec![],
    )
    .with_instance_schema(Some(schema));
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone()))),
    );
    (instance, definition, state)
}

#[test]
fn inactive_instance_quantity_does_not_imply_nonnegativity() {
    let (mut instance, mut definition, _) = instance_memory_fixture();
    instance.fields = vec![int32(u32::MAX).into()].into();
    let unit = ResourceSpec::declared(
        ResourceFamily::Token,
        ResourceAccessMode::Own,
        "credit".into(),
        vec![],
        vec![],
        ResourceTransferRole::Consume,
        ResourceStateSource::Current,
    )
    .unwrap();
    definition.contains = vec![
        ResourceSpec::quantified(
            crate::kernel::program_expression::variable("value"),
            unit,
            ResourceTransferRole::Consume,
            ResourceStateSource::Current,
        )
        .unwrap()
        .with_guard(SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(
                crate::kernel::program_expression::int32_literal(0),
            ),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::ProgramExpression(
                crate::kernel::program_expression::int32_literal(1),
            ),
        }),
    ];
    let assumptions = PureFactContext::new();
    let (folded, _) = rewrite_resource_instance(
        &ExecutionState::new(),
        &instance,
        &definition,
        &assumptions,
        false,
    )
    .unwrap();
    let (opened, facts) =
        rewrite_resource_instance(&folded, &instance, &definition, &assumptions, true).unwrap();
    assert!(opened.resources().is_empty());
    assert!(!facts.contains(&Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: Box::new(MachineTerm::constant(u32::MAX)),
            right: Box::new(MachineTerm::constant(0))
        },
        true,
    )));
}

fn recursive_child_fixture() -> (
    ResourceInstance,
    CompositeResourceDefinition,
    ExecutionState,
) {
    let (mut instance, mut definition, _) = instance_memory_fixture();
    let tree = AlgebraicValueType::Algebraic {
        name: "Tree".into(),
        arguments: vec![],
    };
    let ty = resource_index_type(
        "Tree",
        vec![
            AlgebraicValueType::Program(ProgramType::Int32Pointer),
            tree.clone(),
            AlgebraicValueType::Program(ProgramType::Int32Pointer),
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
                ProgramValue::pointer(Pointer::null()).into(),
                AlgebraicValue::Algebraic(empty.clone()),
                ProgramValue::pointer(Pointer::null()).into(),
                AlgebraicValue::Algebraic(empty),
            ],
        },
    })]
    .into();
    definition.instance_schema = Some(instance.schema.clone());
    definition.matched = Some(ResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            ResourceMatchArm {
                variant: "Clear".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            ResourceMatchArm {
                variant: "Set".into(),
                bindings: vec!["lp".into(), "lm".into(), "rp".into(), "rm".into()],
                binding_types: ty.variants[1].fields.clone(),
                binding_variables: vec![None, None, None, None],
                contains: std::mem::take(&mut definition.contains),
                facts: vec![],
                children: vec![
                    ResourceChildSpec {
                        name: "left".into(),
                        resource: "cell".into(),
                        binding: Variable(90),
                        arguments: vec![SpecExpression::ProgramExpression(
                            crate::kernel::program_expression::variable("lp"),
                        )],
                        field_bindings: vec![ResourceChildField::Constructor(1)],
                    },
                    ResourceChildSpec {
                        name: "right".into(),
                        resource: "cell".into(),
                        binding: Variable(91),
                        arguments: vec![SpecExpression::ProgramExpression(
                            crate::kernel::program_expression::variable("rp"),
                        )],
                        field_bindings: vec![ResourceChildField::Constructor(3)],
                    },
                ],
            },
        ],
    });
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone()))),
    );
    (instance, definition, state)
}

#[test]
fn independent_children_kernel_consumes_names_and_accepts_replacements() {
    let (instance, definition, state) = recursive_child_fixture();
    let assumptions = PureFactContext::new();
    let children = vec![
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let rewrite = |state: &ExecutionState,
                   instance: &ResourceInstance,
                   unfold,
                   children: &[(String, Variable)]| {
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
    let open = rewrite(&state, &instance, true, &children).unwrap().state;
    assert!(matches!(
        open.resources().instance_consumption(instance.identity()),
        Some(InstanceConsumption::Unfold)
    ));
    assert!(
        state
            .resources()
            .instance_consumption(instance.identity())
            .is_none()
    );
    assert!(open.instance_field_scope.is_empty());
    assert!(open.resource_instance_fields(instance.identity()).is_none());
    assert!(
        open.resource_instance_at_path(instance.identity(), &["left".into()])
            .is_none()
    );
    let left = open.owned_resource_instance(Variable(501)).unwrap().clone();
    let raw = rewrite(&open, &left, true, &[]).unwrap().state;
    assert!(raw.owned_resource_instance(left.identity()).is_none());
    assert!(rewrite(&raw, &instance, false, &children).is_err());
    let mut replacement = left.clone();
    replacement.identity = Variable(503);
    let replaced = rewrite(&raw, &replacement, false, &[]).unwrap().state;
    let selected = vec![
        ("left".into(), Variable(503)),
        ("right".into(), Variable(502)),
    ];
    let closed = rewrite(&replaced, &instance, false, &selected)
        .unwrap()
        .state;
    assert!(
        closed
            .resources()
            .instance_consumption(instance.identity())
            .is_none()
    );
    assert!(matches!(
        closed.resources().instance_consumption(Variable(503)),
        Some(InstanceConsumption::FoldChild { parent, slot })
            if *parent == instance.identity() && slot.as_ref() == "left"
    ));
    let reopened = rewrite(&closed, &instance, true, &selected).unwrap().state;
    assert!(
        reopened
            .resources()
            .instance_consumption(Variable(503))
            .is_none()
    );
    // Refolding and unfolding a sibling state do not change the original.
    assert!(matches!(
        raw.resources().instance_consumption(left.identity()),
        Some(InstanceConsumption::Unfold)
    ));
    assert_eq!(
        closed
            .resources()
            .clone()
            .without_owned_instance_read_views(),
        *state.resources()
    );
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
fn unfolding_a_child_retains_its_checked_pointer_read_in_the_callers_graph() {
    let (instance, mut definition, state) = recursive_child_fixture();
    let arm = &mut definition.matched.as_mut().unwrap().arms[1];
    arm.contains[0].memory_segment_mut().unwrap().end =
        crate::kernel::program_expression::int32_literal(2);
    arm.children[0].arguments = vec![SpecExpression::ProgramExpression(
        ProgramExpression::TypedLoad {
            pointer: Box::new(crate::kernel::program_expression::variable("p")),
            value_type: ProgramType::Int32Pointer,
            volatile: false,
            pointee_constant: false,
            access_class: None,
            source: Default::default(),
        },
    )];
    let AlgebraicValue::Program(ProgramValue::Pointer(parent)) = &instance.arguments()[0] else {
        unreachable!()
    };
    let stored = PointerValue::new(Pointer::symbolic(Variable(559)), ProgramType::Int32Pointer);
    let state = state.with_memory(Memory::new().store(
        parent.pointer().clone(),
        ProgramValue::Pointer(stored.clone()),
    ));
    let observed = Pointer::loaded_value(&intern_memory(state.memory().clone()), parent.pointer());
    let equation = ExecutionPureFact::logical_read_equation(stored, observed)
        .proposition()
        .clone();
    let children = [
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let Proposition::ConditionIs(condition, truth) = &equation else {
        unreachable!()
    };
    let context = PureFactContext::new();
    let sibling = context.clone();
    let before = context.equality_graph.knows_condition(condition, *truth);
    let sibling_before = sibling.equality_graph.knows_condition(condition, *truth);
    let mut invalid = definition.clone();
    invalid.matched.as_mut().unwrap().arms[1].children[0].field_bindings =
        vec![ResourceChildField::Parent(999)];
    assert!(
        crate::kernel::rewrite_resource_instance_selecting_children(
            &state,
            &instance,
            &invalid,
            std::slice::from_ref(&invalid),
            &context,
            true,
            Some(&children),
        )
        .is_err()
    );
    assert_eq!(
        context.equality_graph.knows_condition(condition, *truth),
        before,
        "a refused exchange must not publish its scratch read evidence"
    );
    let opened = crate::kernel::rewrite_resource_instance_selecting_children(
        &state,
        &instance,
        &definition,
        std::slice::from_ref(&definition),
        &context,
        true,
        Some(&children),
    )
    .unwrap();
    assert!(
        context.equality_graph.knows_condition(condition, *truth),
        "the checked read definition must leave the temporary opening context"
    );
    assert_eq!(
        sibling.equality_graph.knows_condition(condition, *truth),
        sibling_before,
        "checked read evidence stays in the selected proof context"
    );
    assert!(
        !opened.semantic_facts.contains(&equation),
        "raw read definitions are not new public proof-state facts"
    );
}

#[test]
fn recursive_child_kernel_rejects_implicit_parent_handles() {
    let (instance, definition, state) = recursive_child_fixture();
    let assumptions = PureFactContext::new();
    assert_eq!(
        rewrite_resource_instance(&state, &instance, &definition, &assumptions, true)
            .unwrap_err()
            .describe(),
        "recursive children require explicit independent child selections"
    );
    let children = [
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let opened = crate::kernel::rewrite_resource_instance_selecting_children(
        &state,
        &instance,
        &definition,
        std::slice::from_ref(&definition),
        &assumptions,
        true,
        Some(&children),
    )
    .unwrap()
    .state;
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
    invalid.matched.as_mut().unwrap().arms[1].children[0].field_bindings =
        vec![ResourceChildField::Constructor(0)];
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
    fields[0] = ProgramValue::pointer(Pointer::symbolic(Variable(556))).into();
    fields[1] = AlgebraicValue::Algebraic(unknown.clone());
    // Rebuild the outer argument list after updating only its immediate fields.
    let model = model.clone();
    instance.fields = vec![AlgebraicValue::Algebraic(model)].into();
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone()))),
    );
    let assumptions = PureFactContext::new();
    let children = [
        ("left".into(), Variable(501)),
        ("right".into(), Variable(502)),
    ];
    let open = crate::kernel::rewrite_resource_instance_selecting_children(
        &state,
        &instance,
        &definition,
        std::slice::from_ref(&definition),
        &assumptions,
        true,
        Some(&children),
    )
    .unwrap()
    .state;
    let child = open.owned_resource_instance(Variable(501)).unwrap();
    assert_eq!(child.fields(), &[AlgebraicValue::Algebraic(unknown)]);
    assert!(rewrite_resource_instance(&open, child, &definition, &assumptions, true).is_err());
    let closed = crate::kernel::rewrite_resource_instance_selecting_children(
        &open,
        &instance,
        &definition,
        std::slice::from_ref(&definition),
        &assumptions,
        false,
        Some(&children),
    )
    .unwrap()
    .state;
    assert_eq!(
        closed
            .resources()
            .clone()
            .without_owned_instance_read_views(),
        *state.resources()
    );
}

#[test]
fn instance_memory_guard_requires_a_proved_case_and_exposes_only_that_case() {
    let (instance, mut definition, state) = instance_memory_fixture();
    definition.condition = Some(SpecProposition::Comparison {
        left: SpecExpression::ProgramExpression(crate::kernel::program_expression::variable("p")),
        operator: ComparisonOperator::NotEqual,
        right: SpecExpression::ProgramExpression(crate::kernel::program_expression::int32_literal(
            0,
        )),
    });
    let ProgramValue::Pointer(pointer) = instance.arguments()[0].as_program_value().unwrap() else {
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
                .any(|fact| matches!(fact, Proposition::MemoryLoadable { .. })),
            !is_null
        );
        assert!(rewrite_resource_instance(&open, &instance, &definition, &unknown, false).is_err());
        let (closed, _) =
            rewrite_resource_instance(&open, &instance, &definition, &assumptions, false).unwrap();
        assert_eq!(folded_without_read_views(closed), state);
        let raw = ExecutionState::new().with_resource_context(open.resources().clone());
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
    definition.matched = Some(ResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            ResourceMatchArm {
                children: vec![],
                variant: "Clear".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
            },
            ResourceMatchArm {
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
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone()))),
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
            .any(|fact| matches!(fact, Proposition::MemoryLoadable { .. }))
    );
    assert!(rewrite_resource_instance(&empty, &instance, &definition, &set, false).is_err());
    let (open, _) = rewrite_resource_instance(&state, &instance, &definition, &set, true).unwrap();
    assert!(!open.resources().is_empty());
    assert!(open.instance_field_scope.is_empty());
    let mut fresh = instance.clone();
    fresh.identity = Variable(999);
    fresh.fields = vec![AlgebraicValue::Algebraic(constructor("Set"))].into();
    let raw = ExecutionState::new().with_resource_context(open.resources().clone());
    let (constructed, _) =
        rewrite_resource_instance(&raw, &fresh, &definition, &unknown, false).unwrap();
    assert_eq!(
        constructed.owned_resource_instance(fresh.identity()),
        Some(&fresh)
    );
    assert!(constructed.instance_field_scope.is_empty());
    assert!(
        rewrite_resource_instance(&ExecutionState::new(), &fresh, &definition, &unknown, false)
            .is_err()
    );
    assert_eq!(
        folded_without_read_views(
            rewrite_resource_instance(&open, &instance, &definition, &set, false)
                .unwrap()
                .0
        ),
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
                    .push(AlgebraicValueType::Program(ProgramType::Int32));
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
        folded_without_read_views(
            rewrite_resource_instance(&opened, &instance, &definition, &assumptions, false)
                .unwrap()
                .0
        ),
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
    let raw = ExecutionState::new().with_resource_context(opened.resources.clone());
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

fn field_instance(identity: u64, model: AlgebraicTerm, revision: u32) -> ResourceInstance {
    let schema = ResourceFieldSchema::new(vec![
        (
            "model".into(),
            ResourceFieldType::Algebraic(model.algebraic_type.clone()),
        ),
        (
            "revision".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        ),
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
    let owned = ResourceFact::own(Resource::Instance(instance.clone()));
    let context = ResourceContext::new()
        .try_compose_with_fact(owned.clone(), &assumptions)
        .unwrap();
    assert!(owned.core().is_none());
    assert!(owned.core_with_assumptions(&assumptions).is_none());
    let mut invalid = vec![ResourceFact::View(owned.resource().clone())];
    invalid.extend([0, 2].map(|q| ResourceFact::own_quantity(owned.resource().clone(), q.into())));
    invalid.push(ResourceFact::own_quantity(
        owned.resource().clone(),
        MachineTerm::Variable(Variable(8)),
    ));
    for fact in invalid {
        assert!(matches!(
            ResourceContext::new().try_compose_with_fact(fact.clone(), &assumptions),
            Err(ResourceContextValidityError::InvalidExclusiveAccess(_))
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
        let fact = ResourceFact::own(Resource::Instance(duplicate));
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
    let owned = ResourceFact::own(Resource::Instance(field_instance(10, m.clone(), 0)));
    let equal_state = ResourceFact::own(Resource::Instance(field_instance(10, n.clone(), 0)));
    let other_identity = ResourceFact::own(Resource::Instance(field_instance(11, m.clone(), 0)));
    let changed_scalar = ResourceFact::own(Resource::Instance(field_instance(10, m.clone(), 1)));
    let empty = PureFactContext::new();
    let context = ResourceContext::new().unchecked_with_fact(owned.clone());
    assert!(!context.satisfies_fact(&equal_state, &empty));
    let assumptions =
        empty.assume_proposition(Proposition::Equal(Term::Algebraic(m), Term::Algebraic(n)));
    assert!(context.satisfies_fact(&equal_state, &assumptions));
    assert!(resources_directly_match(
        owned.resource(),
        equal_state.resource(),
        &assumptions
    ));
    for wrong in [other_identity.clone(), changed_scalar] {
        assert!(!context.satisfies_fact(&wrong, &assumptions));
        assert!(!resources_directly_match(
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
        ExecutionState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
            ResourceFact::own(Resource::Instance(field_instance(10, model, revision))),
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
            program_type: ProgramType::Int32,
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
        assert_eq!(paths[0].value.clone().into_native(), int32(expected));
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
        !crate::kernel::search::ProofSearch::proves(&(empty), &paths[0].proposition),
        "ownership alone must not imply preservation"
    );
    let equal = empty
        .clone()
        .assume_proposition(Proposition::Equal(Term::Algebraic(n), Term::Algebraic(m)));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(equal),
        &paths[0].proposition
    ));
    let missing = ExecutionState::new();
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
        assert_eq!(
            crate::kernel::search::ProofSearch::proves(&(empty), &paths[0].proposition),
            should_hold
        );
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
    for (identity, field_index, program_type) in [
        (99, 1, ProgramType::Int32),
        (10, 2, ProgramType::Int32),
        (10, 0, ProgramType::Int32),
        (10, 1, ProgramType::UInt32),
    ] {
        let expression = SpecExpression::ResourceField {
            projection: ResourceFieldProjection {
                identity: Variable(identity),
                children: vec![],
                field_index,
                at_entry: false,
            },
            program_type,
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
    let requirement = ResourceSpec::instance(
        before.identity(),
        "cell".into(),
        before.schema().clone(),
        ResourceSpec::composite(
            ResourceAccessMode::Own,
            "marked_cell".into(),
            vec![ProgramExpression::Value(int32(7))],
            vec![ProgramType::Int32],
        ),
        ResourceTransferRole::Borrow,
        ResourceStateSource::Current,
    )
    .unwrap();
    for instance in [before, after] {
        let fact = ResourceFact::own(Resource::Instance(instance));
        let state = ExecutionState::new()
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
            &ExecutionState::new(),
            &requirement,
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .unwrap()
        .is_err()
    );
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
            AlgebraicValueType::Program(ProgramValue::pointer(pointer.clone()).program_type()),
            AlgebraicValueType::Program(ProgramType::Int32),
        ],
    );
    let make = |p: Pointer, value: MachineTerm| {
        let model = AlgebraicTerm {
            algebraic_type: ty.clone(),
            node: AlgebraicTermNode::Constructor {
                variant: "Set".into(),
                fields: vec![ProgramValue::pointer(p.clone()).into(), int32(value).into()],
            },
        };
        let mut instance = field_instance(10, model, 0);
        instance.arguments = vec![ProgramValue::pointer(p).into()].into();
        Resource::Instance(instance)
    };
    let source = make(pointer.clone(), MachineTerm::Variable(Variable(11)));
    let context = ResourceContext::new().unchecked_with_fact(ResourceFact::own(source.clone()));
    let assumptions = PureFactContext::new();
    for required in [
        ResourceFact::view_memory(memory_range(pointer.clone(), 0, 1)),
        ResourceFact::own_memory(memory_range(pointer, 0, 1)),
    ] {
        assert!(!context.satisfies_fact(&required, &assumptions));
    }
    let numeric = crate::kernel::reasoning::substitute_bitvector_variable_in_resource(
        &source,
        Variable(11),
        &MachineTerm::constant(7),
    );
    let substituted = crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
        &Proposition::ResourceComposition(
            ResourceContext::new().unchecked_with_fact(ResourceFact::own(numeric)),
        ),
        Variable(10),
        &target,
    );
    let expected = Proposition::ResourceComposition(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(make(target, MachineTerm::constant(7)))),
    );
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
        (
            "revision".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        ),
    ];
    let schema = ResourceFieldSchema::new(fields.clone()).unwrap();
    assert_eq!(schema.fields(), fields);
    assert!(!schema.is_fieldless());
    let copy = schema.clone();
    assert!(std::ptr::eq(
        schema.fields().as_ptr(),
        copy.fields().as_ptr()
    ));
    assert!(ResourceFieldSchema::new(vec![]).unwrap().is_fieldless());
    assert!(ResourceFieldSchema::new(vec![fields[0].clone(), fields[0].clone()]).is_none());
    assert!(
        ResourceFieldSchema::new(vec![(
            "".into(),
            ResourceFieldType::Program(ProgramType::Int32)
        )])
        .is_none()
    );
    for ty in [
        ProgramType::Void,
        ProgramType::Int32Array(3),
        ProgramType::FunctionPointer(CallbackSignature::from_encoded(1)),
    ] {
        assert!(
            ResourceFieldSchema::new(vec![("bad".into(), ResourceFieldType::Program(ty))])
                .is_none()
        );
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
                .map(|i| {
                    (
                        format!("field_{i}"),
                        ResourceFieldType::Program(ProgramType::Int32),
                    )
                })
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

fn indexed_resource(index: AlgebraicTerm, composite: bool) -> Resource {
    let arguments = vec![AlgebraicValue::Algebraic(index)].into();
    if composite {
        Resource::Composite {
            name: "indexed".into(),
            arguments,
        }
    } else {
        Resource::Token {
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
        let owned = ResourceFact::own(indexed_resource(m.clone(), composite));
        let renamed = ResourceFact::own(indexed_resource(n.clone(), composite));
        let wrong_type = ResourceFact::own(indexed_resource(other.clone(), composite));
        let facts = ResourceContext::new().unchecked_with_fact(owned.clone());
        let empty = PureFactContext::new();
        assert!(facts.satisfies_fact(&owned, &empty));
        assert!(!facts.satisfies_fact(&renamed, &empty));
        assert!(!facts.satisfies_fact(&wrong_type, &empty));
        assert!(!facts.satisfies_fact(
            &ResourceFact::own_quantity(owned.resource().clone(), MachineTerm::constant(2)),
            &empty,
        ));
        assert!(
            !ResourceContext::new()
                .unchecked_with_fact(ResourceFact::View(owned.resource().clone()))
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
            assert!(resources_directly_match(
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
fn symbolic_resource_indices_distinguish_constructors() {
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
    assert!(!resources_directly_match(
        &clear,
        &set,
        &PureFactContext::new()
    ));
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
            AlgebraicValueType::Program(ProgramValue::pointer(pointer.clone()).program_type()),
            AlgebraicValueType::Program(ProgramType::Int32),
        ],
    );
    let model = |p: Pointer, value: MachineTerm| AlgebraicTerm {
        algebraic_type: ty.clone(),
        node: AlgebraicTermNode::Constructor {
            variant: "Set".into(),
            fields: vec![
                AlgebraicValue::Program(ProgramValue::pointer(p)),
                AlgebraicValue::Program(int32(value)),
            ],
        },
    };
    let value = MachineTerm::Variable(Variable(990_021));
    let original = indexed_resource(model(pointer.clone(), value.clone()), false);
    let context = ResourceContext::new().unchecked_with_fact(ResourceFact::own(original.clone()));
    let empty = PureFactContext::new();
    let memory = memory_range(pointer, 0, 1);
    assert!(!context.satisfies_fact(&ResourceFact::view_memory(memory.clone()), &empty));
    assert!(!context.satisfies_fact(&ResourceFact::own_memory(memory), &empty));

    let numeric = crate::kernel::reasoning::substitute_bitvector_variable_in_resource(
        &original,
        Variable(990_021),
        &MachineTerm::constant(7),
    );
    let source = Proposition::ResourceComposition(
        ResourceContext::new().unchecked_with_fact(ResourceFact::own(numeric)),
    );
    let substituted = crate::kernel::reasoning::substitute_pointer_variable_in_proposition(
        &source,
        Variable(990_020),
        &target,
    );
    let expected = Proposition::ResourceComposition(ResourceContext::new().unchecked_with_fact(
        ResourceFact::own(indexed_resource(
            model(target, MachineTerm::constant(7)),
            false,
        )),
    ));
    assert_eq!(substituted, expected);
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
            Resource::Token {
                arguments: left, ..
            },
            Resource::Token {
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
            ResourceFact::own_token(format!("token_{index}"), vec![int32(index as u32)])
        }),
    )
}

fn equality(left: MachineTerm, right: MachineTerm) -> Proposition {
    Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left),
            right: Box::new(right),
        },
        true,
    )
}

#[test]
fn zero_owned_resource_is_identity_after_symbolic_resolution() {
    let quantity = MachineTerm::Variable(Variable(910_000));
    let intermediate = MachineTerm::Variable(Variable(910_001));
    let assumptions = PureFactContext::new()
        .assume_proposition(equality(quantity.clone(), intermediate.clone()))
        .assume_proposition(equality(intermediate, MachineTerm::constant(0)));
    let required = ResourceFact::own_quantity(
        Resource::Token {
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
        ResourceFact::own_quantity(required.resource().clone(), MachineTerm::constant(1));
    assert!(!empty.satisfies_fact(&positive, &assumptions));
    assert!(
        empty
            .without_fact_delaying_normalization(&positive, &assumptions)
            .is_none()
    );
}

#[test]
fn resource_context_fork_updates_are_persistent_and_logarithmic() {
    for size in [16_usize, 64, 256, 1024, 4096] {
        let context = unrelated_token_context(size);
        let ancestor = context.clone();
        assert!(context.shares_storage_with(&ancestor));
        assert!(context.storage.materialized.get().is_none());

        let added = ResourceFact::own_token("target".to_string(), vec![int32(size as u32)]);
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
            &ResourceFact::own_token("token_0".to_string(), vec![int32(0)]),
            &PureFactContext::new(),
        ));
    }
}

#[test]
fn consuming_support_removes_only_its_derived_views() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let view = ResourceFact::view_token("derived".to_string(), vec![int32(7)]);
    let other_authority = ResourceFact::own_composite("other".to_string(), Vec::new());
    let other_view = ResourceFact::view_token("other_derived".to_string(), vec![int32(8)]);
    let context = ResourceContext::new()
        .unchecked_with_fact(view.clone())
        .unchecked_with_fact(authority.clone())
        .unchecked_with_fact(other_authority.clone())
        .unchecked_with_supported_facts(&other_authority, [other_view.clone()])
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
    assert!(remaining.contains_exact_representation(&view));
    assert!(remaining.contains_exact_representation(&other_authority));
    assert!(remaining.contains_exact_representation(&other_view));
    assert!(remaining.satisfies_fact(&other_view, &PureFactContext::new()));
    assert!(!remaining.storage.supported_by.is_empty());
    assert_eq!(
        remaining
            .directly_supporting_owned_entry(&other_view, &PureFactContext::new())
            .map(|(_, support)| support),
        Some(&other_authority),
    );
    assert!(
        remaining
            .directly_supporting_owned_entry(&view, &PureFactContext::new())
            .is_none(),
        "consuming an authority must remove its indexed projection",
    );
}

#[test]
fn equal_support_occurrences_keep_their_own_projections() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let first_view = ResourceFact::view_token("first_derived".to_string(), vec![int32(7)]);
    let second_view = ResourceFact::view_token("second_derived".to_string(), vec![int32(8)]);
    let context = ResourceContext::new()
        .unchecked_with_fact(authority.clone())
        .unchecked_with_fact(authority.clone())
        .unchecked_with_supported_facts_from_entry(0, &authority, [first_view.clone()])
        .unchecked_with_supported_facts_from_entry(1, &authority, [second_view.clone()]);

    let remaining = context
        .without_exact_representation(&authority)
        .expect("one equal authority occurrence should be removable");
    assert!(!remaining.contains_exact_representation(&first_view));
    assert!(remaining.contains_exact_representation(&second_view));
    assert_eq!(
        remaining
            .directly_supporting_owned_entry(&second_view, &PureFactContext::new())
            .map(|(_, support)| support),
        Some(&authority),
    );
}

#[test]
fn resource_equality_and_exchange_preserve_support_occurrence_identity() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let view = ResourceFact::view_token("derived".to_string(), Vec::new());
    let root = ResourceContext::new()
        .unchecked_with_fact(authority.clone())
        .unchecked_with_fact(authority.clone());
    let left =
        root.clone()
            .unchecked_with_supported_facts_from_entry(0, &authority, [view.clone()]);
    let right = root
        .clone()
        .unchecked_with_supported_facts_from_entry(1, &authority, [view]);

    let independently_allocated_same_topology = ResourceContext::new()
        .unchecked_with_fact(authority.clone())
        .unchecked_with_fact(authority.clone())
        .unchecked_with_supported_facts_from_entry(
            0,
            &authority,
            [ResourceFact::view_token("derived".to_string(), Vec::new())],
        );
    assert_eq!(
        left, independently_allocated_same_topology,
        "context equality compares support topology, while provenance checks use opaque occurrences"
    );

    assert_ne!(
        left, right,
        "swapping equal support occurrences changes authority"
    );
    assert!(
        !left.same_exchange_from(&right, &root),
        "the exact exchange frontier must reject a forged support occurrence"
    );
}

#[test]
fn forked_siblings_allocate_distinct_occurrence_identity() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let root = ResourceContext::new();
    let left = root.clone().unchecked_with_fact(authority.clone());
    let right = root.unchecked_with_fact(authority.clone());
    let left_occurrence = left
        .directly_supporting_owned_entry(&authority, &PureFactContext::new())
        .map(|(occurrence, _)| occurrence);
    let right_occurrence = right
        .directly_supporting_owned_entry(&authority, &PureFactContext::new())
        .map(|(occurrence, _)| occurrence);
    assert_ne!(left_occurrence, right_occurrence);
}

#[test]
fn owned_support_lookup_follows_observation_projection() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let projected = ResourceFact::view_composite("nested".to_string(), vec![int32(7)]);
    let context = ResourceContext::new()
        .unchecked_with_fact(projected.clone())
        .unchecked_with_fact(authority.clone())
        .unchecked_with_supported_facts(&authority, [projected.clone()]);

    assert_eq!(
        context
            .directly_supporting_owned_entry(&projected, &PureFactContext::new())
            .map(|(_, support)| support),
        Some(&authority),
        "an observed view must retain the owned support that can invalidate it",
    );
}

#[test]
fn normalization_preserves_projection_support() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let view = ResourceFact::view_token("derived".to_string(), vec![int32(7)]);
    let expanded = ResourceFact::own_token("expanded".to_string(), vec![int32(9)]);
    let context = ResourceContext::new()
        .unchecked_with_fact(authority.clone())
        .unchecked_with_supported_facts(&authority, [view])
        .with_cached_supported_expansion(&authority, vec![expanded.clone()]);
    let authority_occurrence = context
        .directly_supporting_owned_entry(&authority, &PureFactContext::new())
        .map(|(occurrence, _)| occurrence);
    assert!(authority_occurrence.is_some());
    let context = context.normalized(&PureFactContext::new());
    assert_eq!(
        context
            .directly_supporting_owned_entry(&authority, &PureFactContext::new())
            .map(|(occurrence, _)| occurrence),
        authority_occurrence,
        "normalization must preserve the support occurrence",
    );
    assert_eq!(
        context.cached_supported_expansion(&authority),
        Some([expanded].as_slice())
    );

    let remaining = context
        .without_exact_representation(&authority)
        .expect("normalization should retain the authority");
    assert!(remaining.is_empty());
    assert!(
        remaining
            .storage
            .expansions_by_support_occurrence
            .is_empty()
    );
}

#[test]
fn normalization_preserves_support_through_unrelated_merge() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let view = ResourceFact::view_token("derived".to_string(), vec![int32(7)]);
    let unit = ResourceFact::own_token("mergeable".to_string(), Vec::new());
    let context = ResourceContext::new()
        .unchecked_with_fact(authority.clone())
        .unchecked_with_supported_facts(&authority, [view.clone()])
        .unchecked_with_fact(unit.clone())
        .unchecked_with_fact(unit)
        .normalized(&PureFactContext::new());

    assert_eq!(
        context
            .directly_supporting_owned_entry(&view, &PureFactContext::new())
            .map(|(_, support)| support),
        Some(&authority),
        "an unrelated normalization must not detach an observation",
    );
}

#[test]
fn duplicate_authority_occurrences_survive_normalization_in_order() {
    let authority = ResourceFact::own(Resource::Instance(field_instance(
        900,
        resource_index_variable(&resource_index_type("Marker", vec![]), 1),
        0,
    )));
    let first_view = ResourceFact::view_token("first_view".to_string(), Vec::new());
    let second_view = ResourceFact::view_token("second_view".to_string(), Vec::new());
    let base = Pointer {
        block: "unrelated".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let first_range = ResourceFact::own_memory(memory_range(base.clone(), 0, 1));
    let second_range = ResourceFact::own_memory(memory_range(base, 1, 2));
    let context = ResourceContext::new()
        .unchecked_with_fact(authority.clone())
        .unchecked_with_fact(authority.clone())
        .unchecked_with_supported_facts_from_entry(0, &authority, [first_view.clone()])
        .unchecked_with_supported_facts_from_entry(1, &authority, [second_view.clone()])
        .unchecked_with_fact(first_range.clone())
        .unchecked_with_fact(second_range)
        .normalized_around_facts(&[first_range], &PureFactContext::new());

    let occurrences = context.owned_occurrences_for_fact(&authority);
    assert_eq!(occurrences.len(), 2);
    assert_eq!(
        context
            .directly_supporting_owned_entry(&first_view, &PureFactContext::new())
            .map(|(occurrence, _)| occurrence),
        Some(occurrences[0])
    );
    assert_eq!(
        context
            .directly_supporting_owned_entry(&second_view, &PureFactContext::new())
            .map(|(occurrence, _)| occurrence),
        Some(occurrences[1])
    );

    let after_first = context
        .without_exact_representation_for_occurrence(occurrences[0])
        .expect("the first duplicate authority should be removable");
    assert!(!after_first.contains_exact_representation(&first_view));
    assert!(after_first.contains_exact_representation(&second_view));
    let remaining_occurrence = after_first.owned_occurrences_for_fact(&authority)[0];
    let after_second = after_first
        .without_exact_representation_for_occurrence(remaining_occurrence)
        .expect("the second duplicate authority should be removable");
    assert!(!after_second.contains_exact_representation(&second_view));
}

#[test]
fn duplicate_cached_authorities_rekey_after_remove_and_reinsert() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let first_expansion = vec![ResourceFact::own_token("first".to_string(), Vec::new())];
    let second_expansion = vec![ResourceFact::own_token("second".to_string(), Vec::new())];
    let context = ResourceContext::new()
        .unchecked_with_fact(authority.clone())
        .unchecked_with_fact(authority.clone());
    let occurrences = context.owned_occurrences_for_fact(&authority);
    let context = context
        .with_cached_supported_expansion_for_occurrence(occurrences[0], &authority, first_expansion)
        .with_cached_supported_expansion_for_occurrence(
            occurrences[1],
            &authority,
            second_expansion.clone(),
        );
    let context = context
        .without_exact_representation_for_occurrence(occurrences[0])
        .expect("the first cached authority should be removable");
    assert_eq!(
        context
            .storage
            .expansions_by_support_entry
            .get(&authority)
            .and_then(|bucket| bucket.get(&0))
            .map(|expansion| expansion.as_slice()),
        Some(second_expansion.as_slice())
    );

    let context = context.unchecked_with_fact(authority.clone());
    let reinserted = context.owned_occurrences_for_fact(&authority)[1];
    let context = context.with_cached_supported_expansion_for_occurrence(
        reinserted,
        &authority,
        vec![ResourceFact::own_token(
            "reinserted".to_string(),
            Vec::new(),
        )],
    );
    assert_eq!(context.cached_supported_expansions(&authority).len(), 2);
    assert_eq!(
        context
            .storage
            .expansions_by_support_entry
            .get(&authority)
            .and_then(|bucket| bucket.get(&0))
            .map(|expansion| expansion.as_slice()),
        Some(second_expansion.as_slice())
    );
}

#[test]
fn cached_projection_finds_the_owned_resource_that_packages_a_fact() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let allocation = ResourceFact::own_token(
        ResourceFact::ALLOCATION_RESOURCE_NAME.to_string(),
        vec![
            ProgramValue::pointer(Pointer {
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
fn resource_join_preserves_only_common_projection_support() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let view = ResourceFact::view_token("derived".to_string(), Vec::new());
    let expansion = vec![ResourceFact::own_token("expanded".to_string(), Vec::new())];
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
    assert!(mixed.storage.expansions_by_support_occurrence.is_empty());
}

#[test]
fn resource_join_drops_projection_when_memory_footprints_diverge() {
    let support = ResourceFact::own_composite("join_memory_support".into(), Vec::new());
    let view = |block: &str| {
        ResourceFact::view_memory(MemoryRange::new(
            Pointer {
                block: block.into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        ))
    };
    let root = ResourceContext::new().unchecked_with_fact(support.clone());
    let support_occurrence = root.owned_occurrences_for_fact(&support)[0];
    let left_memory = Memory::new().with_block("left-join", 8);
    let right_memory = Memory::new().with_block("right-join", 8);
    let left = root
        .clone()
        .unchecked_with_supported_facts_from_occurrence_with_memory(
            support_occurrence,
            &support,
            [view("left-join")],
            &left_memory,
        );
    let right = root
        .clone()
        .unchecked_with_supported_facts_from_occurrence_with_memory(
            support_occurrence,
            &support,
            [view("right-join")],
            &right_memory,
        );
    let common = ResourceContext::common_exact_descendant(&left, &right, &root)
        .expect("branches share the root resource authority");
    assert!(common.contains_exact_representation(&support));
    assert_eq!(
        common
            .facts()
            .iter()
            .filter(|fact| fact.is_view() && fact.memory_range().is_some())
            .count(),
        0,
        "a projection with divergent memory dependency metadata must not be reintroduced unindexed"
    );
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn resource_common_descendant_visits_only_branch_local_changes() {
    let left_path = ResourceFact::own_token("left_path".to_string(), Vec::new());
    let right_path = ResourceFact::own_token("right_path".to_string(), Vec::new());
    let permit = ResourceFact::own_token("permit".to_string(), Vec::new());
    let ready = ResourceFact::own_composite("ready".to_string(), Vec::new());
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
            "no-op normalization must preserve a size-{size} state by identity"
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
                common.contains_exact_representation(&ResourceFact::own_token(
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

    let unit = ResourceFact::own_token("mergeable".to_string(), Vec::new());
    let merged = ResourceFact::own_quantity(
        Resource::Token {
            name: "mergeable".to_string(),
            arguments: Vec::new().into(),
        },
        MachineTerm::constant(2),
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

    let duplicate = ResourceFact::own_token("duplicate".to_string(), Vec::new());
    let duplicate_root = ResourceContext::new()
        .unchecked_with_fact(duplicate.clone())
        .unchecked_with_fact(duplicate.clone());
    let duplicate_left = duplicate_root.clone();
    let duplicate_right = duplicate_root
        .clone()
        .without_exact_representation(&duplicate)
        .expect("one duplicate should be removable");
    let shared_occurrence = duplicate_right
        .storage
        .index
        .exact
        .get(&duplicate)
        .and_then(|entries| entries.iter().next())
        .map(|entry| duplicate_right.occurrence(*entry))
        .expect("the right branch should retain one authority occurrence");
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
    let common_occurrence = duplicate_common
        .storage
        .index
        .exact
        .get(&duplicate)
        .and_then(|entries| entries.iter().next())
        .map(|entry| duplicate_common.occurrence(*entry));
    assert_eq!(common_occurrence, Some(shared_occurrence));
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn resource_memory_block_and_interval_indexes_update_logarithmically() {
    for size in [16_usize, 64, 256, 1024, 4096] {
        let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
            ResourceFact::own_memory(memory_range(
                Pointer {
                    block: format!("unrelated-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                0,
                1,
            ))
        }));
        let target = ResourceFact::own_memory(memory_range(
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
fn direct_resource_match_candidates_ignore_unrelated_shapes_and_blocks() {
    let target = ResourceFact::own_token("target".to_string(), vec![int32(0)]);
    let target_memory = ResourceFact::view_memory(memory_range(
        Pointer {
            block: "target-block".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        1,
    ));
    let context = unrelated_token_context(128)
        .unchecked_with_facts((0..128).map(|index| {
            ResourceFact::view_memory(memory_range(
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
fn installing_a_certified_resource_group_still_checks_the_existing_frame() {
    let base = Pointer {
        block: "certified_group_cross_check".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let existing = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(memory_range(base.clone(), 0, 2)));
    let overlapping = ResourceFact::own_memory(memory_range(base, 1, 3));
    let result = existing.try_compose_certified_group_into_valid_context_delaying_normalization(
        [overlapping],
        &PureFactContext::new(),
    );
    assert!(
        result.is_err(),
        "certification of a group's interior must not skip its boundary check"
    );
}

/// the owner-observation rule and law 4 in docs/internals/stable-views.md, the owner-absorbs-view normalization kept at
/// step 8c. An unbound viewed description beside its owner is an observation
/// of that ownership: dropping it changes no live access share, so
/// normalization may merge the pair into the owner alone.
///
/// This is also why `evaluate_contract_return_resources` no longer filters
/// ensured views against caller ownership before composing them. The filter
/// asked `satisfies_fact`, which an owner answers, so an owner discharged a
/// returned view for free; composition plus this merge reaches the same
/// context without consulting ownership, and the provenance routes decide
/// whether the view was ever legitimate.
#[test]
fn an_unbound_view_beside_its_owner_normalizes_into_the_owner() {
    let base = Pointer {
        block: "owner_absorbs_view".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owner = own_memory_fact(base.clone(), 0, 1);
    let observation = view_memory_fact(base, 0, 1);
    let normalized = ResourceContext::new()
        .unchecked_with_facts([owner.clone(), observation.clone()])
        .normalized(&PureFactContext::new());
    assert_eq!(
        normalized.facts(),
        &[owner],
        "an unbound observation beside its owner is a description, not a second authority"
    );
}

/// The other half of the same rule: a view whose occurrence carries a live
/// loan dependency is never absorbed. The merged fact is a new authority with
/// no occurrence, so absorbing a bound view would drop the binding that
/// authorizes reading it and retire the loan by normalization — exactly what
/// the owner-observation rule in docs/internals/stable-views.md forbids ("Combining an owner and a live borrowed description
/// cannot absorb the loan"). `ResourceContext::normalized`'s `loan_bound`
/// guard, not the family algebra, is what draws the line: `normalize_pair`
/// sees two bare facts and cannot tell the two cases apart.
#[test]
fn a_loan_bound_view_beside_an_owner_is_not_absorbed_by_normalization() {
    let base = Pointer {
        block: "bound_view_survives".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owner = own_memory_fact(base.clone(), 0, 1);
    let borrowed = view_memory_fact(base, 0, 1);
    let context = ResourceContext::new().unchecked_with_facts([owner.clone(), borrowed.clone()]);
    let borrowed_occurrence = context.occurrences_for_fact(&borrowed)[0];
    let support_occurrence = context.owned_occurrences_for_fact(&owner)[0];
    let ledger = LoanLedger::new();
    let lender = ledger.fresh_participant().unwrap();
    let reader = ledger.fresh_participant().unwrap();
    let opening = ledger
        .lend(lender, reader, support_occurrence, owner.clone())
        .unwrap();
    let context = context.with_loan_dependency(
        borrowed_occurrence,
        LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support: support_occurrence,
            viewed: borrowed.clone(),
            hold: None,
        },
    );
    let normalized = context.normalized(&PureFactContext::new());
    assert!(
        normalized.facts().contains(&borrowed),
        "a bound view must survive normalization: {normalized:?}"
    );
    let surviving = normalized.occurrences_for_fact(&borrowed);
    assert_eq!(surviving, vec![borrowed_occurrence]);
    assert!(
        normalized.loan_dependency(borrowed_occurrence).is_some(),
        "the dependency that authorizes the borrowed description must survive with it"
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
        ResourceFact::own_token("token".to_string(), vec![int32(0)]).core(),
        Some(ResourceFact::view_token(
            "token".to_string(),
            vec![int32(0)]
        ))
    );
    assert_eq!(
        ResourceFact::own_composite("box".to_string(), vec![int32(1)]).core(),
        Some(ResourceFact::view_composite(
            "box".to_string(),
            vec![int32(1)]
        ))
    );
}

#[test]
fn declared_resource_families_accumulate_equal_owned_units() {
    for fact in [
        ResourceFact::own_token("token".to_string(), vec![int32(0)]),
        ResourceFact::own_composite("box".to_string(), vec![int32(1)]),
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
            ResourceFact::own_token("token".to_string(), vec![int32(0)]),
            ResourceFact::view_token("token".to_string(), vec![int32(0)]),
        ),
        (
            ResourceFact::own_composite("box".to_string(), vec![int32(1)]),
            ResourceFact::view_composite("box".to_string(), vec![int32(1)]),
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
    let unit = ResourceFact::own_token("object_ref".to_string(), vec![int32(7)]);
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
    let quantity = MachineTerm::var(Variable(700));
    let resource = Resource::Token {
        name: "permit".to_string(),
        arguments: vec![int32(9).into()].into(),
    };
    let symbolic = ResourceFact::own_quantity(resource.clone(), quantity.clone());
    let unit = ResourceFact::own(resource.clone());
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: Box::new(quantity.clone()),
            right: Box::new(MachineTerm::constant(1)),
        },
        true,
    );

    let remaining = ResourceContext::new()
        .unchecked_with_fact(symbolic)
        .without_fact(&unit, &assumptions)
        .expect("one unit should split from a positive symbolic quantity");

    assert_eq!(
        remaining.facts(),
        &[ResourceFact::own_quantity(
            resource,
            MachineTerm::subtract(quantity, MachineTerm::constant(1)),
        )]
    );
}

#[test]
fn declared_resource_quantity_work_ignores_the_numeric_coefficient() {
    let resource = Resource::Token {
        name: "permit".to_string(),
        arguments: vec![int32(9).into()].into(),
    };
    let symbolic_quantity = MachineTerm::var(Variable(701));

    let samples = [
        ("one", MachineTerm::constant(1)),
        ("two", MachineTerm::constant(2)),
        ("ten", MachineTerm::constant(10)),
        ("one hundred", MachineTerm::constant(100)),
        ("one thousand", MachineTerm::constant(1_000)),
        ("symbolic", symbolic_quantity.clone()),
    ]
    .into_iter()
    .map(|(label, quantity)| {
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: Box::new(quantity.clone()),
                right: Box::new(MachineTerm::constant(1)),
            },
            true,
        );
        let assumptions = assumptions.assume_condition(
            ConditionTerm::signed_add_overflows(quantity.clone(), MachineTerm::constant(1)),
            false,
        );
        let context = ResourceContext::new().unchecked_with_facts([
            ResourceFact::own_quantity(resource.clone(), quantity.clone()),
            ResourceFact::own(resource.clone()),
        ]);
        let (normalized, normalization_work) =
            crate::instrumentation::measure_deterministic_work(|| context.normalized(&assumptions));
        assert_eq!(normalized.facts().len(), 1);

        let available = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_quantity(resource.clone(), quantity));
        let (remaining, consumption_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                available.without_fact(&ResourceFact::own(resource.clone()), &assumptions)
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
    // The symbolic case has a different expression shape. Its semantic
    // containment is checked above; compare work only across concrete
    // coefficients rather than assigning an arbitrary symbolic surcharge.
}

#[test]
fn zero_declared_resource_quantity_is_the_composition_identity() {
    let zero = ResourceFact::own_quantity(
        Resource::Token {
            name: "permit".to_string(),
            arguments: vec![int32(9).into()].into(),
        },
        MachineTerm::constant(0),
    );
    assert!(zero.core().is_none());
    let context = ResourceContext::new()
        .try_compose_with_fact(zero, &PureFactContext::new())
        .expect("zero ownership should compose harmlessly");
    assert!(context.is_empty());
}

#[test]
fn declared_resource_quantities_are_part_of_context_equality() {
    let unit = ResourceFact::own_token("object_ref".to_string(), vec![int32(7)]);
    let one = ResourceContext::new()
        .try_compose_with_fact(unit.clone(), &PureFactContext::new())
        .unwrap();
    let two = ResourceContext::new()
        .try_compose_with_facts([unit.clone(), unit], &PureFactContext::new())
        .unwrap();
    let two_uncompacted = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_token(
            "object_ref".to_string(),
            vec![int32(7)],
        ))
        .unchecked_with_fact(ResourceFact::own_token(
            "object_ref".to_string(),
            vec![int32(7)],
        ));

    assert!(!resource_contexts_definitionally_equal_with_definitions(
        &[],
        &Memory::new(),
        &one,
        &Memory::new(),
        &two,
        &PureFactContext::new(),
    ));
    assert!(resource_contexts_definitionally_equal_with_definitions(
        &[],
        &Memory::new(),
        &two_uncompacted,
        &Memory::new(),
        &two,
        &PureFactContext::new(),
    ));
}

/// Definitional equality equates a folded composite with its opened pieces
/// only where the composite's body facts hold over those pieces. A loop back
/// edge used this comparison to return a folded `owns zero_cell(p)` from a
/// body that had stored 9 into the cell and never refolded it.
#[test]
fn definitional_equality_reassembles_a_composite_only_where_its_facts_hold() {
    let pointer = Pointer {
        block: "reassembled-cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let definition = CompositeResourceDefinition::new(
        "zero_cell",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment::new(
            crate::kernel::program_expression::variable("p"),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(1),
        ))],
        vec![SpecProposition::Comparison {
            left: SpecExpression::ProgramExpression(crate::kernel::program_expression::index(
                crate::kernel::program_expression::variable("p"),
                crate::kernel::program_expression::int32_literal(0),
            )),
            operator: ComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
    );
    let folded = ResourceContext::new().unchecked_with_fact(ResourceFact::own_composite(
        "zero_cell".into(),
        vec![ProgramValue::typed_pointer(
            pointer.clone(),
            ProgramType::Int32Pointer,
        )],
    ));
    let pieces = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
        MemoryRange::new(pointer.clone(), 0.into(), 1.into()),
    ));
    let memory = |value: u32| {
        Memory::new()
            .with_block(pointer.block.clone(), 4)
            .store(pointer.clone(), int32(value))
    };
    let equal = |stored: u32| {
        resource_contexts_definitionally_equal_with_definitions(
            std::slice::from_ref(&definition),
            &memory(0),
            &folded,
            &memory(stored),
            &pieces,
            &PureFactContext::new(),
        )
    };
    assert!(
        !equal(9),
        "a cell holding 9 is not a `zero_cell`, so it is not the folded head"
    );
    assert!(equal(0), "a cell holding 0 reassembles the folded head");
}

#[test]
fn missing_composite_query_ignores_ambient_memory_splits() {
    let base = Pointer {
        block: "backing".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let context = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(memory_range(base.clone(), 0, 1)))
        .unchecked_with_fact(ResourceFact::own_memory(memory_range(base, 1, 2)));
    let required = ResourceFact::own_composite("allocated".to_string(), vec![int32(0)]);

    assert!(!context.satisfies_fact(&required, &PureFactContext::new()));
}

#[test]
fn owned_memory_query_without_owned_memory_is_rejected_structurally() {
    let context = ResourceContext::new().unchecked_with_fact(ResourceFact::view_composite(
        "tree".to_string(),
        vec![int32(0)],
    ));
    let required = ResourceFact::own_memory(memory_range(
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
        .unchecked_with_fact(ResourceFact::own_memory(memory_range(base.clone(), 0, 3)));
    let required = [
        ResourceFact::own_memory(memory_range(base.clone(), 0, 1)),
        ResourceFact::own_memory(memory_range(base, 1, 3)),
    ];

    let remaining = context
        .without_facts(&required, &PureFactContext::new())
        .expect("both subranges should be consumable");

    assert!(remaining.is_empty());
}

#[test]
fn incremental_memory_merge_retires_dependent_entries_once() {
    let assumptions = PureFactContext::new();
    let base = Pointer {
        block: "supported-merge".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let first = ResourceFact::own_memory(memory_range(base.clone(), 0, 1));
    let second = ResourceFact::own_memory(memory_range(base.clone(), 1, 2));
    let unrelated = ResourceFact::own_token("unrelated".into(), Vec::new());
    let resources =
        ResourceContext::new().unchecked_with_facts([first.clone(), second, unrelated.clone()]);
    let occurrence = *resources
        .storage
        .index
        .exact
        .get(&first)
        .unwrap()
        .iter()
        .next()
        .and_then(|entry| resources.storage.occurrence_by_entry.get(entry))
        .unwrap();
    let memory = Memory::new().with_block("supported-merge", 8);
    let resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
        occurrence,
        &first,
        [ResourceFact::view_memory(memory_range(base.clone(), 0, 1))],
        &memory,
    );
    let required = ResourceFact::own_memory(memory_range(base, 0, 2));
    let remaining = resources
        .without_fact_incrementally(&required, &assumptions)
        .expect("merging the selected owner bucket retires each supported entry once");
    assert!(!remaining.satisfies_fact(&required, &assumptions));
    assert!(remaining.satisfies_fact(&unrelated, &assumptions));
    assert!(
        remaining
            .clone()
            .without_fact_incrementally(&required, &assumptions)
            .is_none()
    );
    assert!(
        remaining
            .without_fact_incrementally(&unrelated, &assumptions)
            .is_some()
    );
}

#[test]
fn batch_resource_consumption_normalizes_when_a_requirement_needs_a_merge() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let context = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(memory_range(base.clone(), 0, 1)))
        .unchecked_with_fact(ResourceFact::own_memory(memory_range(base.clone(), 1, 2)));
    let required = [ResourceFact::own_memory(memory_range(base, 0, 2))];

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
        .unchecked_with_fact(ResourceFact::own_memory(left.clone()))
        .unchecked_with_fact(ResourceFact::own_memory(right.clone()))
        .observable_facts(&PureFactContext::new())
        .expect("adjacent writes should be a valid resource context");

    assert_eq!(facts.len(), 1);
    assert!(matches!(facts[0], Proposition::ResourceComposition(_)));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(left)),
            right: Box::new(Resource::Memory(right)),
        }
    ));
}

#[test]
fn resource_context_observes_same_and_cross_family_separation() {
    let memory = Resource::Memory(memory_range(
        Pointer {
            block: "p".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        1,
    ));
    let token = Resource::Token {
        name: "left".to_string(),
        arguments: vec![].into(),
    };
    let other_token = Resource::Token {
        name: "right".to_string(),
        arguments: vec![].into(),
    };
    let facts = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own(memory.clone()))
        .unchecked_with_fact(ResourceFact::own(token.clone()))
        .unchecked_with_fact(ResourceFact::own(other_token.clone()))
        .observable_facts(&PureFactContext::new())
        .expect("distinct owned resources should compose validly");

    let assumptions = facts
        .into_iter()
        .fold(PureFactContext::new(), |assumptions, fact| {
            assumptions.assume_proposition(fact)
        });
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ResourceSeparate {
            left: Box::new(token.clone()),
            right: Box::new(other_token),
        }
    ));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ResourceSeparate {
            left: Box::new(memory),
            right: Box::new(token),
        }
    ));
}

#[test]
fn observable_abstract_resources_use_one_indexed_composition() {
    for size in [16, 32, 64, 128] {
        let context = ResourceContext::new().unchecked_with_facts((0..size).map(|index| {
            ResourceFact::own(Resource::Token {
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
        assert!(crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &Proposition::ResourceSeparate {
                left: Box::new(context.facts()[0].resource().clone()),
                right: Box::new(context.facts()[size - 1].resource().clone()),
            }
        ));
    }
}

#[test]
fn composite_resource_arguments_respect_proven_pointer_equality() {
    let left_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(40_000)), 4),
    };
    let right_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(40_001)), 4),
    };
    let left = ResourceFact::own(Resource::Composite {
        name: "list".to_string(),
        arguments: vec![ProgramValue::pointer(left_pointer.clone()).into()].into(),
    });
    let right = ResourceFact::own(Resource::Composite {
        name: "list".to_string(),
        arguments: vec![ProgramValue::pointer(right_pointer.clone()).into()].into(),
    });
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::PointerValueEqual(
            Box::new(PointerValue::new(left_pointer, ProgramType::Int32Pointer)),
            Box::new(PointerValue::new(right_pointer, ProgramType::Int32Pointer)),
        ),
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
fn resource_separation_covers_larger_memory_range() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left_first = Resource::Memory(memory_range(base.clone(), 0, 1));
    let left_second = Resource::Memory(memory_range(base.clone(), 1, 2));
    let left_combined = Resource::Memory(memory_range(base.clone(), 0, 2));
    let right = Resource::Memory(memory_range(base, 10, 11));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(left_first),
            right: Box::new(right.clone()),
        })
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(left_second),
            right: Box::new(right.clone()),
        });

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ResourceSeparate {
            left: Box::new(left_combined),
            right: Box::new(right),
        }
    ));
}

#[test]
fn resource_separation_transports_across_equal_memory_ranges() {
    let target = Pointer::symbolic(Variable(20_100));
    let original_data = Pointer::symbolic(Variable(20_101));
    let equal_data = Pointer::symbolic(Variable(20_102));
    let original_length = MachineTerm::Variable(Variable(20_103));
    let equal_length = MachineTerm::Variable(Variable(20_104));
    let target_resource = Resource::Memory(memory_range(target, 0, 4));
    let original_resource = Resource::Memory(memory_range(
        original_data.clone(),
        0,
        original_length.clone(),
    ));
    let equal_resource =
        Resource::Memory(memory_range(equal_data.clone(), 0, equal_length.clone()));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(target_resource.clone()),
            right: Box::new(original_resource),
        })
        .assume_condition(
            ConditionTerm::pointer_equal(original_data, equal_data),
            true,
        )
        .assume_condition(ConditionTerm::equal(original_length, equal_length), true);

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ResourceSeparate {
            left: Box::new(target_resource),
            right: Box::new(equal_resource),
        }
    ));
}

#[test]
fn resource_contains_projects_separation_to_children() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let parent = Resource::Token {
        name: "parent".to_string(),
        arguments: vec![].into(),
    };
    let child = Resource::Memory(memory_range(base.clone(), 0, 1));
    let other = Resource::Memory(memory_range(base.clone(), 1, 2));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(parent.clone()),
            right: Box::new(other.clone()),
        })
        .assume_proposition(Proposition::ResourceContains {
            parent: Box::new(parent),
            child: Box::new(child.clone()),
        });

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ResourceSeparate {
            left: Box::new(child),
            right: Box::new(other),
        }
    ));
}

#[test]
fn assumed_resource_composition_has_exact_membership() {
    let resources = ResourceContext::new()
        .try_compose_with_facts(
            [own_memory_fact(Pointer::symbolic(Variable(41_001)), 0, 1)],
            &PureFactContext::new(),
        )
        .unwrap();
    let proposition = Proposition::ResourceComposition(resources);
    let empty = PureFactContext::new();
    assert!(!empty.contains_assumed_exact(&proposition));
    let context = empty.assume_proposition(proposition.clone());
    assert!(context.contains_assumed_exact(&proposition));
    assert!(context.proves_exact(&proposition));
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
fn equal_cross_block_pointer_bases_cannot_be_owned_twice() {
    let symbolic = Pointer::symbolic(Variable(41_000));
    let argument = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let symbolic_range = MemoryRange::new(
        symbolic.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    let argument_range = MemoryRange::new(
        argument.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(symbolic.clone(), argument.clone()),
        true,
    );

    assert!(memory_ranges_proven_overlapping(
        &symbolic_range,
        &argument_range,
        &assumptions,
    ));

    let symbolic_owner = ResourceFact::own_memory(symbolic_range.clone());
    let argument_owner = ResourceFact::own_memory(argument_range.clone());
    let existing = ResourceContext::new().unchecked_with_fact(symbolic_owner.clone());
    assert!(matches!(
        existing
            .clone()
            .try_compose_with_fact(argument_owner.clone(), &assumptions),
        Err(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
    ));

    let unchecked = ResourceContext::new().unchecked_with_facts([symbolic_owner, argument_owner]);
    assert!(matches!(
        unchecked.validity_error(&assumptions),
        Some(ResourceContextValidityError::OverlappingOwnedMemoryResources { .. })
    ));

    let adjacent = ResourceFact::own_memory(MemoryRange::new(
        argument,
        MachineTerm::constant(1),
        MachineTerm::constant(2),
    ));
    assert!(
        existing
            .try_compose_with_fact(adjacent, &assumptions)
            .is_ok()
    );
}

#[test]
fn equal_content_string_literals_remain_readable_without_separation_evidence() {
    let literal = |identity: &str| Pointer {
        block: PointerBlock::StringLiteral {
            identity: identity.to_string(),
            bytes: b"ok\0".to_vec(),
        },
        offset: PointerOffsetTerm::Constant(0),
    };
    let first = literal("first");
    let second = literal("second");
    let range = |base| {
        MemoryRange::new_with_element_width(
            base,
            MachineTerm::constant(0),
            MachineTerm::constant(3),
            1,
        )
    };
    let first_range = range(first.clone());
    let second_range = range(second.clone());
    let assumptions =
        PureFactContext::new().assume_condition(ConditionTerm::pointer_equal(first, second), true);

    assert!(memory_ranges_proven_overlapping(
        &first_range,
        &second_range,
        &assumptions,
    ));
    let resources = ResourceContext::new()
        .try_compose_with_fact(ResourceFact::own_memory(first_range.clone()), &assumptions)
        .unwrap()
        .try_compose_with_fact(ResourceFact::own_memory(second_range.clone()), &assumptions)
        .expect("equal read-only literals may share their bytes");
    assert!(resources.is_valid(&assumptions));
    assert!(!resources.proves_owned_memory_ranges_separate_shallow(&first_range, &second_range,));
}

#[test]
fn integer_resource_fields_require_mathematical_values() {
    let schema =
        ResourceFieldSchema::new(vec![("total".into(), ResourceFieldType::Integer)]).unwrap();
    assert!(!schema.is_fieldless());
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
        CompositeResourceDefinition::new("integer_box", vec![], None, false, vec![], vec![])
            .with_instance_schema(Some(schema));
    definition.matched = Some(ResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            ResourceMatchArm {
                variant: "Clear".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            ResourceMatchArm {
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
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone()))),
    );
    let assumptions = PureFactContext::new().assume_proposition(Proposition::Equal(
        Term::Algebraic(model),
        Term::Algebraic(constructor),
    ));
    let selected = crate::kernel::rewrite_resource_instance_selecting_children(
        &state,
        &instance,
        &definition,
        std::slice::from_ref(&definition),
        &assumptions,
        true,
        None,
    )
    .expect("the selected Integer constructor field should discharge its arm fact");
    assert_eq!(selected.body_clauses.len(), 1);
    assert_eq!(selected.body_clauses[0].arm.as_deref(), Some("Set"));
    assert_eq!(selected.body_clauses[0].ordinal, 0);
    let already_known = assumptions
        .clone()
        .assume_proposition(selected.body_clauses[0].proposition.clone());
    let repeated = crate::kernel::rewrite_resource_instance_selecting_children(
        &state,
        &instance,
        &definition,
        std::slice::from_ref(&definition),
        &already_known,
        true,
        None,
    )
    .expect("an already-known body clause still has declaration correspondence");
    assert_eq!(repeated.body_clauses.len(), 1);
    assert_eq!(
        repeated.body_clauses[0].proposition,
        selected.body_clauses[0].proposition
    );
    assert!(
        repeated
            .semantic_facts
            .contains(&selected.body_clauses[0].proposition),
        "unfold returns its justified clause without querying caller membership"
    );
    let readmitted = already_known
        .clone()
        .assume_proposition(selected.body_clauses[0].proposition.clone());
    assert_eq!(already_known.fact_counts(), readmitted.fact_counts());
    assert!(readmitted.contains_assumed_exact(&selected.body_clauses[0].proposition));

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
    let mut definition = CompositeResourceDefinition::new(
        "integer_capture_box",
        vec![],
        None,
        false,
        vec![],
        vec![],
    )
    .with_instance_schema(Some(schema));
    definition.matched = Some(ResourceMatchBody {
        field_index: 0,
        algebraic_type: ty.clone(),
        arms: vec![
            ResourceMatchArm {
                variant: "Clear".into(),
                bindings: vec![],
                binding_types: vec![],
                binding_variables: vec![],
                contains: vec![],
                facts: vec![],
                children: vec![],
            },
            ResourceMatchArm {
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
    let state = ExecutionState::new().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(instance.clone()))),
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

    let fold_state = ExecutionState::new();
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
                    MachineTerm::Variable(Variable(960_100 + index as u64)),
                    MachineTerm::constant(1_000),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_greater_equal(
                    MachineTerm::Variable(Variable(960_100 + index as u64)),
                    MachineTerm::constant(0),
                ),
                true,
            );
    }
    assumptions
}

fn dependent_pair_entry_fixture() -> (
    ExecutionState,
    CompositeResourceDefinition,
    Vec<ResourceSpec>,
) {
    let next = |pointer: ProgramExpression| ProgramExpression::TypedLoad {
        pointer: Box::new(ProgramExpression::Subobject {
            pointer: Box::new(pointer),
            width: 8,
        }),
        value_type: ProgramType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        access_class: None,
        source: Default::default(),
    };
    let cell = |base| {
        ResourceSpec::owned_memory(MemorySegment::new(
            base,
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(2),
        ))
    };
    let definition = CompositeResourceDefinition::new(
        "dependent_pair",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![
            cell(crate::kernel::program_expression::variable("p")),
            cell(next(crate::kernel::program_expression::variable("p"))),
        ],
        vec![],
    );
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(910_000)), 4),
    };
    let state = ExecutionState::new().with_local("node", ProgramValue::pointer(pointer));
    let clause = |argument| {
        ResourceSpec::declared(
            ResourceFamily::Composite,
            ResourceAccessMode::Own,
            "dependent_pair".into(),
            vec![argument],
            vec![ProgramType::Int32Pointer],
            ResourceTransferRole::Borrow,
            ResourceStateSource::Entry,
        )
        .unwrap()
    };
    let second = next(next(crate::kernel::program_expression::variable("node")));
    let third = next(second.clone());
    (
        state,
        definition,
        vec![
            clause(crate::kernel::program_expression::variable("node")),
            clause(second),
            clause(third),
        ],
    )
}

#[test]
fn folded_composite_body_cells_supply_dependent_entry_arguments_without_opening() {
    let (state, definition, clauses) = dependent_pair_entry_fixture();
    let resources = crate::kernel::functions::evaluate_function_resource_context(
        &state,
        &clauses,
        &[definition],
        // Match the function-entry API: the caller establishes these extents.
        &PureFactContext::new().assume_entry_clause_extents(),
        &mut ExecutionBudget::default(),
    )
    .unwrap()
    .expect("typed body views address the second and third folded clauses");
    assert_eq!(resources.facts().iter().filter(|fact| matches!(fact.resource(), Resource::Composite { name, .. } if name == "dependent_pair")).count(), 3);
    assert!(
        resources
            .facts()
            .iter()
            .all(|fact| !matches!(fact.resource(), Resource::Memory(_)) || fact.is_view())
    );
}

#[test]
fn zero_folded_composite_quantity_supplies_no_body_read_authority() {
    let (state, definition, _) = dependent_pair_entry_fixture();
    let parent = ResourceFact::own_quantity(
        Resource::Composite {
            name: "dependent_pair".into(),
            arguments: vec![
                state
                    .locals()
                    .get_native("node")
                    .as_deref()
                    .unwrap()
                    .clone()
                    .into(),
            ]
            .into(),
        },
        MachineTerm::constant(0),
    );
    let supply = crate::kernel::functions::resource_clause_section_supply(
        &state,
        &[parent],
        &[definition],
        &PureFactContext::new(),
    );
    assert!(
        supply.facts().iter().all(|fact| {
            !matches!(fact.resource(), Resource::Memory(_))
                || state
                    .resources()
                    .satisfies_fact(fact, &PureFactContext::new())
        }),
        "a zero head must not add read authority beyond the existing frame: {supply:?}"
    );
}

/// A contract section whose clauses cannot be put in any evaluable order is
/// refused by naming a pair, not the clause that happens to be written last.
/// Clause order does not decide a section, so one position is not the answer.
#[test]
fn resource_clauses_with_no_evaluable_order_name_two_positions() {
    let unowned = |variable| {
        ResourceSpec::owned_memory(MemorySegment {
            value_runs: Default::default(),
            base: ProgramExpression::Load(Box::new(ProgramExpression::Value(
                ProgramValue::pointer(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(
                        MachineTerm::Variable(Variable(variable)),
                        4,
                    ),
                }),
            ))),
            start: crate::kernel::program_expression::int32_literal(0),
            end: crate::kernel::program_expression::int32_literal(1),
            element_width: 4,
            guard: None,
            uninitialized: false,
        })
    };
    let evaluate = |clauses: &[ResourceSpec]| {
        let error = crate::kernel::functions::evaluate_function_resource_context(
            &ExecutionState::new(),
            clauses,
            &[],
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
        )
        .expect("clause evaluation stays inside its budget")
        .expect_err("no clause has read authority for its base");
        error
            .function_contract_message()
            .expect("an unevaluable segment is a contract error")
            .to_string()
    };
    assert_eq!(
        evaluate(&[unowned(100), unowned(101)]),
        "could not evaluate an owned memory resource segment: segment base produced runtime \
         error: a required resource is not available (resource clauses 1 and 2 cannot \
         be evaluated in any order: each needs a cell no clause evaluated before it supplies)"
    );
    // One stalled clause is still reported at its own position: there is no
    // second clause whose authority it could have been waiting for.
    assert_eq!(
        evaluate(&[unowned(100)]),
        "could not evaluate an owned memory resource segment: segment base produced runtime \
         error: a required resource is not available (resource clause 1 of 1)"
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
            fields: vec![AlgebraicValueType::Program(ProgramType::Int32)],
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
            vec![AlgebraicValue::Program(ProgramValue::Int32(
                MachineTerm::constant(value),
            ))],
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
        vec![AlgebraicValue::Program(ProgramValue::Int32(
            MachineTerm::Variable(Variable(77)),
        ))],
    );
    let witnessed = PureFactContext::new().assume_proposition(Proposition::Exists {
        name: "v".to_string(),
        var: Variable(77),
        sort: Sort::ProgramInt32,
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
fn resource_model_possible_arms_are_the_unrefuted_ones() {
    let ty = arm_selection_type(&["Empty", "Reserved"], "Filled");
    let model = resource_index_variable(&ty, 11);
    let empty = arm_selection_constructor(&ty, "Empty", vec![]);
    let reserved = arm_selection_constructor(&ty, "Reserved", vec![]);
    let exclusion = |value: &AlgebraicTerm| {
        Proposition::Not(Box::new(Proposition::Equal(
            Term::Algebraic(model.clone()),
            Term::Algebraic(value.clone()),
        )))
    };

    // Nothing refuted is selection's business, not this decision's: an
    // unconstrained model publishes no common authority at all.
    assert_eq!(
        decide_resource_model_arm(&model, &PureFactContext::new()),
        ResourceModelArmDecision::Open,
        "an unrefuted model has no refuted arm to reason from"
    );

    // One exclusion of three leaves exactly the two arms that must agree.
    let excluded = PureFactContext::new().assume_proposition(exclusion(&empty));
    assert_eq!(
        decide_resource_model_arm(&model, &excluded),
        ResourceModelArmDecision::Possible(vec!["Filled".to_string(), "Reserved".to_string()])
    );

    // Two exclusions leave one arm, which selection answers for.
    let decided = excluded.assume_proposition(exclusion(&reserved));
    assert_eq!(
        decide_resource_model_arm(&model, &decided),
        ResourceModelArmDecision::Selected(ResourceModelArmSelection::Variant(
            "Filled".to_string()
        ))
    );
}

/// Expanded leaves retain the source clause position used by diagnostics.
/// The first source aggregate contributes two stalled leaves here; the
/// evaluator must skip the duplicate leaf and name the next source clause,
/// rather than reporting a misleading pair of positions for one clause.
#[test]
fn expanded_resource_clause_diagnostics_keep_source_positions() {
    let unowned = |variable| {
        ResourceSpec::owned_memory(MemorySegment {
            value_runs: Default::default(),
            base: ProgramExpression::Load(Box::new(ProgramExpression::Value(
                ProgramValue::pointer(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(
                        MachineTerm::Variable(Variable(variable)),
                        4,
                    ),
                }),
            ))),
            start: crate::kernel::program_expression::int32_literal(0),
            end: crate::kernel::program_expression::int32_literal(1),
            element_width: 4,
            guard: None,
            uninitialized: false,
        })
    };
    let error = crate::kernel::functions::evaluate_function_resource_context(
        &ExecutionState::new(),
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
    .expect_err("no clause has read authority for its base");
    let message = error
        .function_contract_message()
        .expect("an unevaluable segment is a contract error");
    assert!(message.contains("resource clauses 1 and 2 cannot be evaluated in any order"));
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
    let length = MachineTerm::Variable(Variable(9_903));
    let load = |pointer: Pointer| ProgramExpression::TypedLoad {
        pointer: Box::new(crate::kernel::program_expression::pointer_value(pointer)),
        value_type: ProgramType::Int32Pointer,
        volatile: false,
        pointee_constant: false,
        access_class: None,
        source: Default::default(),
    };
    let owned = |base: ProgramExpression, end: ProgramExpression| {
        ResourceSpec::owned_memory(MemorySegment {
            base,
            start: crate::kernel::program_expression::int32_literal(0),
            end,
            element_width: 4,
            guard: None,
            uninitialized: false,
            value_runs: Default::default(),
        })
    };
    let clauses = vec![
        // A waits on the concrete cell at `intermediate`, but is listed first.
        owned(
            load(intermediate.clone()),
            crate::kernel::program_expression::int32_literal(1),
        ),
        // B is the symbolic provider for that cell.  Its base load waits on C.
        owned(
            load(seed.clone()),
            ProgramExpression::Value(int32(length.clone())),
        ),
        // C is the only clause that can evaluate on the first pass.
        owned(
            crate::kernel::program_expression::pointer_value(seed.clone()),
            crate::kernel::program_expression::int32_literal(1),
        ),
    ];
    let memory = Memory::new()
        .store(seed, ProgramValue::pointer(intermediate.clone()))
        .store(intermediate, ProgramValue::pointer(target));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_equal(MachineTerm::constant(1), length),
        true,
    );
    let result = crate::kernel::functions::evaluate_function_resource_context(
        &ExecutionState::new().with_memory(memory),
        &clauses,
        &[],
        &assumptions,
        &mut ExecutionBudget::default(),
    )
    .expect("clause evaluation stays inside its budget")
    .expect("the symbolic provider should wake the concrete pending clause");
    assert_eq!(result.facts().len(), 3);
}

#[test]
fn observed_memory_projection_is_invalidated_by_overlap_but_not_disjoint_store() {
    let support = ResourceFact::own_composite("memory_support".to_string(), Vec::new());
    let observed_range = MemoryRange::new(
        Pointer {
            block: "observed-block".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    let base = Memory::new().with_block("observed-block", 32);
    let resources = ResourceContext::new().unchecked_with_fact(support.clone());
    let support_occurrence = *resources
        .storage
        .index
        .exact
        .get(&support)
        .expect("support entry")
        .iter()
        .next()
        .and_then(|entry| resources.storage.occurrence_by_entry.get(entry))
        .expect("support occurrence");
    let resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
        support_occurrence,
        &support,
        [ResourceFact::view_memory(observed_range.clone())],
        &base,
    );
    let state = ExecutionState::new()
        .with_memory(base.clone())
        .with_resource_context(resources);
    let disjoint = state.clone().with_memory(base.clone().store(
        Pointer {
            block: "observed-block".into(),
            offset: PointerOffsetTerm::Constant(16),
        },
        int32(1),
    ));
    assert!(
        disjoint
            .resources()
            .contains_exact_representation(&ResourceFact::view_memory(observed_range.clone()))
    );
    let overlapping = disjoint
        .clone()
        .with_memory(disjoint.memory().clone().store(
            Pointer {
                block: "observed-block".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            int32(2),
        ));
    assert!(
        !overlapping
            .resources()
            .contains_exact_representation(&ResourceFact::view_memory(observed_range))
    );
    assert!(
        overlapping
            .resources()
            .contains_exact_representation(&support)
    );
}

#[test]
fn observed_projection_tracks_loaded_address_prerequisite() {
    let support = ResourceFact::own_composite("loaded_address_support".to_string(), Vec::new());
    let selector = Pointer {
        block: "loaded-address-selector".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new()
        .with_block("loaded-address-selector", 4)
        .with_block("loaded-address-data", 32)
        .with_block("loaded-address-unrelated", 4)
        .store(selector.clone(), int32(0));
    let selector_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&memory),
        Box::new(selector.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let projected = ResourceFact::view_memory(MemoryRange::new(
        Pointer {
            block: "loaded-address-data".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(0),
        // Keep the load nested in the bound expression, as it is after
        // lowering an indexed composite member rather than a hand-written
        // standalone cell range.
        binary_node!(
            Int32,
            Add,
            Box::new(selector_load),
            Box::new(MachineTerm::constant(0)),
        ),
    ));
    let unrelated = ResourceFact::view_memory(MemoryRange::new(
        Pointer {
            block: "loaded-address-unrelated".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    let resources = ResourceContext::new().unchecked_with_fact(support.clone());
    let occurrence = resources.owned_occurrences_for_fact(&support)[0];
    let resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
        occurrence,
        &support,
        [projected.clone(), unrelated.clone()],
        &memory,
    );
    let state = ExecutionState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources);

    // The data projection is disjoint from this write, but its address was
    // derived from the selector cell, so changing that prerequisite retires
    // the projection instead of leaving a stale address alive.
    let after_selector_write = state
        .clone()
        .with_memory(memory.clone().store(selector.clone(), int32(1)));
    assert!(
        !after_selector_write
            .resources()
            .contains_exact_representation(&projected)
    );
    assert!(
        after_selector_write
            .resources()
            .contains_exact_representation(&support)
    );
    assert!(
        after_selector_write
            .resources()
            .contains_exact_representation(&unrelated)
    );
}

#[test]
fn observed_projection_tracks_loaded_base_and_start_prerequisites() {
    let support = ResourceFact::own_composite("loaded_base_start_support".to_string(), Vec::new());
    let selector = Pointer {
        block: "base-start-selector".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = Memory::new()
        .with_block("base-start-selector", 8)
        .with_block("base-start-data", 32)
        .with_block("base-start-unrelated", 4)
        .store(selector.clone(), int16(0));
    let selector_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory_ref(&memory),
        Box::new(selector.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let base_projected = ResourceFact::view_memory(MemoryRange::new(
        Pointer {
            block: "base-start-data".into(),
            offset: PointerOffsetTerm::scaled_int32_node(selector_load.clone(), 4),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    let start_projected = ResourceFact::view_memory(MemoryRange::new(
        Pointer {
            block: "base-start-data".into(),
            offset: PointerOffsetTerm::Constant(8),
        },
        selector_load.clone(),
        binary_node!(
            Int32,
            Add,
            Box::new(selector_load),
            Box::new(MachineTerm::constant(1)),
        ),
    ));
    let unrelated = ResourceFact::view_memory(MemoryRange::new(
        Pointer {
            block: "base-start-unrelated".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    let resources = ResourceContext::new().unchecked_with_fact(support.clone());
    let occurrence = resources.owned_occurrences_for_fact(&support)[0];
    let resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
        occurrence,
        &support,
        [
            base_projected.clone(),
            start_projected.clone(),
            unrelated.clone(),
        ],
        &memory,
    );
    let after_selector_write = ExecutionState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources)
        .with_memory(memory.store(selector, int16(1)));
    assert!(
        !after_selector_write
            .resources()
            .contains_exact_representation(&base_projected)
    );
    assert!(
        !after_selector_write
            .resources()
            .contains_exact_representation(&start_projected)
    );
    assert!(
        after_selector_write
            .resources()
            .contains_exact_representation(&unrelated)
    );
}

#[test]
fn observed_wide_footprint_and_unknown_loop_barrier_are_invalidated() {
    let support = ResourceFact::own_composite("wide_support".to_string(), Vec::new());
    let range = MemoryRange::new_with_element_width(
        Pointer {
            block: "wide-block".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(20_000),
        1,
    );
    let memory = Memory::new().with_block("wide-block", 20_000);
    let resources = ResourceContext::new().unchecked_with_fact(support.clone());
    let entry = *resources
        .storage
        .index
        .exact
        .get(&support)
        .unwrap()
        .iter()
        .next()
        .unwrap();
    let occurrence = resources.occurrence(entry);
    let resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
        occurrence,
        &support,
        [ResourceFact::view_memory(range.clone())],
        &memory,
    );
    let state = ExecutionState::new()
        .with_memory(memory)
        .with_resource_context(resources);
    let barrier = state
        .memory()
        .clone()
        .with_loop_memory_havoc_preserving_loans(Variable(81), &BTreeSet::new(), None, None);
    let after = state.with_memory(barrier);
    assert!(
        !after
            .resources()
            .contains_exact_representation(&ResourceFact::view_memory(range))
    );
    assert!(after.resources().contains_exact_representation(&support));
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn supported_projection_interval_updates_scale_with_index_height() {
    let mut samples = Vec::new();
    for unrelated_count in [4_usize, 16, 64, 256, 1024] {
        let memory = Memory::new().with_block("projection-curve", (8 * unrelated_count + 8) as u32);
        let mut resources = ResourceContext::new();
        for index in 0..unrelated_count {
            let support = ResourceFact::own_composite(
                format!("projection_curve_unrelated_{index}"),
                Vec::new(),
            );
            resources = resources.unchecked_with_fact(support.clone());
            let occurrence = resources.owned_occurrences_for_fact(&support)[0];
            let view = ResourceFact::view_memory(MemoryRange::new(
                Pointer {
                    block: "projection-curve".into(),
                    offset: PointerOffsetTerm::Constant((8 + index * 8) as i64),
                },
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            ));
            resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
                occurrence,
                &support,
                [view],
                &memory,
            );
        }
        let target_support =
            ResourceFact::own_composite("projection_curve_target".into(), Vec::new());
        resources = resources.unchecked_with_fact(target_support.clone());
        let target_occurrence = resources.owned_occurrences_for_fact(&target_support)[0];
        let target_view = ResourceFact::view_memory(MemoryRange::new(
            Pointer {
                block: "projection-curve".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        ));
        let before_insert = crate::persistent::persistent_node_allocations();
        let resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
            target_occurrence,
            &target_support,
            [target_view.clone()],
            &memory,
        );
        let insert_allocations = crate::persistent::persistent_node_allocations() - before_insert;
        let target_entry = *resources
            .storage
            .index
            .exact
            .get(&target_view)
            .expect("target projection entry")
            .iter()
            .next()
            .expect("target projection entry id");
        let target_occurrence = resources.occurrence(target_entry);
        let before_remove = crate::persistent::persistent_node_allocations();
        let remaining = resources
            .without_exact_representation_for_occurrence(target_occurrence)
            .expect("target projection should be removable");
        let remove_allocations = crate::persistent::persistent_node_allocations() - before_remove;
        assert!(!remaining.contains_exact_representation(&target_view));
        samples.push((unrelated_count, insert_allocations, remove_allocations));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3).saturating_add(256)
                && pair[1].2 <= pair[0].2.saturating_mul(3).saturating_add(256),
            "supported interval insertion/removal grew with ambient facts: {samples:?}"
        );
    }
    for (size, insert_allocations, remove_allocations) in samples {
        let height = usize::BITS as usize - size.leading_zeros() as usize;
        assert!(
            insert_allocations <= 512 * height && remove_allocations <= 512 * height,
            "supported interval update exceeded fixed-depth indexed bound at size {size}: insert={insert_allocations}, remove={remove_allocations}"
        );
    }
}

#[test]
fn removing_symbolic_memory_observations_does_not_leave_alias_bucket_entries() {
    let support = ResourceFact::own_composite("symbolic_alias_support".into(), Vec::new());
    let memory = Memory::new();
    let mut resources = ResourceContext::new().unchecked_with_fact(support.clone());
    let support_occurrence = resources.owned_occurrences_for_fact(&support)[0];
    for iteration in 0..4 {
        let view = ResourceFact::view_memory(MemoryRange::new(
            Pointer {
                block: PointerBlock::Symbolic(Variable(900 + iteration)),
                offset: PointerOffsetTerm::Constant(0),
            },
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        ));
        resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
            support_occurrence,
            &support,
            [view.clone()],
            &memory,
        );
        let entry = *resources
            .storage
            .index
            .exact
            .get(&view)
            .expect("symbolic observation entry")
            .iter()
            .next()
            .expect("symbolic observation entry id");
        let occurrence = resources.occurrence(entry);
        resources = resources
            .without_exact_representation_for_occurrence(occurrence)
            .expect("symbolic observation should be removable");
        assert!(resources.storage.symbolic_memory_support.is_empty());
        assert!(resources.storage.support_metadata_by_projection.is_empty());
    }
}

#[test]
fn v11_fresh_view_children_use_exact_occurrences_and_preserve_duplicates() {
    let support = ResourceFact::own_token("v11_support".into(), Vec::new());
    let child = ResourceFact::view_token("v11_child".into(), Vec::new());
    let before = ResourceContext::new().unchecked_with_facts([support.clone(), child.clone()]);
    let existing_child = before.occurrences_for_fact(&child)[0];
    let support_occurrence = before.owned_occurrences_for_fact(&support)[0];
    let (after, inserted) = before
        .clone()
        .unchecked_with_facts_and_occurrences([child.clone()]);
    assert_eq!(inserted.len(), 1);
    let inserted_child = inserted[0].1;
    assert_ne!(existing_child, inserted_child);

    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().unwrap();
    let reader = ledger.fresh_participant().unwrap();
    let opening = ledger
        .lend(owner, reader, support_occurrence, support.clone())
        .unwrap();
    let binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support: support_occurrence,
        viewed: child.clone(),
        hold: None,
    };
    let after = after.with_loan_dependency(inserted_child, binding.clone());
    assert!(after.loan_dependency(existing_child).is_none());
    assert_eq!(after.loan_dependency(inserted_child), Some(&binding));
    assert_eq!(after.occurrences_for_fact(&child).len(), 2);
    let recreated = after
        .without_exact_representation_for_occurrence(inserted_child)
        .unwrap();
    assert!(recreated.loan_dependency(inserted_child).is_none());
    let (recreated, inserted_again) = recreated.unchecked_with_facts_and_occurrences([child]);
    assert_ne!(inserted_again[0].1, inserted_child);
    assert!(recreated.loan_dependency(inserted_again[0].1).is_none());
}

#[test]
fn v11_duplicate_bound_and_unbound_views_are_not_authority_candidates() {
    let support = ResourceFact::own_token("v11_duplicate_support".into(), Vec::new());
    let child = ResourceFact::view_token("v11_duplicate_child".into(), Vec::new());
    let context = ResourceContext::new().unchecked_with_facts([
        support.clone(),
        child.clone(),
        child.clone(),
    ]);
    let occurrences = context.occurrences_for_fact(&child);
    assert_eq!(occurrences.len(), 2);
    let support_occurrence = context.owned_occurrences_for_fact(&support)[0];
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().unwrap();
    let reader = ledger.fresh_participant().unwrap();
    let opening = ledger
        .lend(owner, reader, support_occurrence, support)
        .unwrap();
    let binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support: support_occurrence,
        viewed: child.clone(),
        hold: None,
    };
    let context = context.with_loan_dependency(occurrences[0], binding.clone());
    assert!(context.loan_dependency(occurrences[1]).is_none());
    // A checked surface operation must reject this mixed candidate set rather
    // than silently selecting the one occurrence that happens to be bound.
    assert!(
        context
            .occurrences_for_fact(&child)
            .iter()
            .any(|occurrence| context.loan_dependency(*occurrence).is_none())
    );
}

/// Build the same one-dependency context every time, in a fresh ledger.
/// `view_the_support` changes only the binding's viewed fact, so two contexts
/// that disagree on it still hold the same facts and the same support graph.
fn context_with_one_loan_dependency(view_the_support: bool) -> ResourceContext {
    let support = ResourceFact::own_token("f7_dependency_support".into(), Vec::new());
    let child = ResourceFact::view_token("f7_dependency_child".into(), Vec::new());
    let context = ResourceContext::new().unchecked_with_facts([support.clone(), child.clone()]);
    let child_occurrence = context.occurrences_for_fact(&child)[0];
    let support_occurrence = context.owned_occurrences_for_fact(&support)[0];
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().unwrap();
    let reader = ledger.fresh_participant().unwrap();
    let opening = ledger
        .lend(owner, reader, support_occurrence, support.clone())
        .unwrap();
    context.with_loan_dependency(
        child_occurrence,
        LoanViewBinding {
            loan: opening.loan,
            scope: opening.scope,
            share: opening.root_share,
            support: support_occurrence,
            viewed: if view_the_support { support } else { child },
            hold: None,
        },
    )
}

fn resource_context_hash(context: &ResourceContext) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    context.hash(&mut hasher);
    hasher.finish()
}

/// F7. A binding names its loan, scope, share, and support with fresh arena
/// counters, so two contexts built identically in different ledgers carry
/// different raw identities. Comparing those counters reported such contexts
/// unequal, which costs loop fixpoints and interning; the comparison and the
/// hash both use structure-derived keys instead.
#[test]
fn loan_dependencies_from_different_ledgers_compare_equal_and_hash_alike() {
    let left = context_with_one_loan_dependency(false);
    let right = context_with_one_loan_dependency(false);
    let left_binding = left
        .live_loan_dependencies()
        .next()
        .expect("the left context should carry a live dependency")
        .1
        .clone();
    let right_binding = right
        .live_loan_dependencies()
        .next()
        .expect("the right context should carry a live dependency")
        .1
        .clone();
    // Without different raw identities the assertions below would be vacuous.
    assert_ne!(left_binding.loan, right_binding.loan);
    assert_ne!(left_binding.scope, right_binding.scope);
    assert_ne!(left_binding.share, right_binding.share);
    assert_ne!(left_binding.support, right_binding.support);
    assert_eq!(left_binding.viewed, right_binding.viewed);

    assert_eq!(left, right);
    assert_eq!(left.cmp(&right), std::cmp::Ordering::Equal);
    assert_eq!(resource_context_hash(&left), resource_context_hash(&right));
}

/// Two contexts whose dependencies differ only in the viewed fact must still
/// order, and order the same way each time they are rebuilt in a new arena.
#[test]
fn loan_dependencies_differing_in_the_viewed_fact_order_deterministically() {
    let viewing_child = context_with_one_loan_dependency(false);
    let viewing_support = context_with_one_loan_dependency(true);
    assert_eq!(viewing_child.facts(), viewing_support.facts());
    assert_ne!(viewing_child, viewing_support);

    let ordering = viewing_child.cmp(&viewing_support);
    assert_ne!(ordering, std::cmp::Ordering::Equal);
    assert_eq!(viewing_support.cmp(&viewing_child), ordering.reverse());
    assert_eq!(
        context_with_one_loan_dependency(false).cmp(&context_with_one_loan_dependency(true)),
        ordering
    );
}

#[test]
fn v11_unbound_owner_observation_composite_still_expands() {
    let definition = CompositeResourceDefinition::new(
        "v11_observation_box",
        Vec::new(),
        None,
        false,
        vec![
            ResourceSpec::declared(
                ResourceFamily::Token,
                ResourceAccessMode::Own,
                "v11_observation_child".into(),
                Vec::new(),
                Vec::new(),
                ResourceTransferRole::Consume,
                ResourceStateSource::Current,
            )
            .unwrap(),
        ],
        Vec::new(),
    );
    let parent = ResourceFact::view_composite("v11_observation_box".into(), Vec::new());
    let resources = ResourceContext::new().unchecked_with_fact(parent.clone());
    let expanded = crate::kernel::functions::expand_composite_resource_fact_with_children(
        &resources,
        &parent,
        &[definition],
        &Memory::new(),
        &PureFactContext::new(),
    )
    .expect("an unbound owner-supported observation remains expandable");
    assert!(
        expanded
            .0
            .contains_exact_representation(&ResourceFact::view_token(
                "v11_observation_child".into(),
                Vec::new()
            ))
    );
}

#[test]
fn v11_composite_expansion_refuses_equal_ambient_child_without_destination() {
    let definition = CompositeResourceDefinition::new(
        "v11_box",
        Vec::new(),
        None,
        false,
        vec![
            ResourceSpec::declared(
                ResourceFamily::Token,
                ResourceAccessMode::Own,
                "v11_child".into(),
                Vec::new(),
                Vec::new(),
                ResourceTransferRole::Consume,
                ResourceStateSource::Current,
            )
            .unwrap(),
        ],
        Vec::new(),
    );
    let support = ResourceFact::own_token("v11_expansion_support".into(), Vec::new());
    let parent = ResourceFact::view_composite("v11_box".into(), Vec::new());
    let child = ResourceFact::view_token("v11_child".into(), Vec::new());
    let resources =
        ResourceContext::new().unchecked_with_facts([support.clone(), parent.clone(), child]);
    let support_occurrence = resources.owned_occurrences_for_fact(&support)[0];
    let parent_occurrence = resources.occurrences_for_fact(&parent)[0];
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().unwrap();
    let reader = ledger.fresh_participant().unwrap();
    let opening = ledger
        .lend(owner, reader, support_occurrence, support)
        .unwrap();
    let binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support: support_occurrence,
        viewed: parent,
        hold: None,
    };
    let resources = resources.with_loan_dependency(parent_occurrence, binding);
    assert!(
        crate::kernel::functions::expand_composite_resource_fact_with_children(
            &resources,
            &ResourceFact::view_composite("v11_box".into(), Vec::new()),
            &[definition],
            &Memory::new(),
            &PureFactContext::new(),
        )
        .is_none()
    );
}

#[test]
fn v11_tampered_cstate_mirror_is_rejected_and_stale_sidecar_is_dropped() {
    let support = ResourceFact::own_token("v11_tamper_support".into(), Vec::new());
    let child = ResourceFact::view_token("v11_tamper_child".into(), Vec::new());
    let resources = ResourceContext::new().unchecked_with_facts([support.clone(), child.clone()]);
    let support_occurrence = resources.owned_occurrences_for_fact(&support)[0];
    let child_occurrence = resources.occurrences_for_fact(&child)[0];
    let ledger = LoanLedger::new();
    let owner = ledger.fresh_participant().unwrap();
    let reader = ledger.fresh_participant().unwrap();
    let opening = ledger
        .lend(owner, reader, support_occurrence, support)
        .unwrap();
    let binding = LoanViewBinding {
        loan: opening.loan,
        scope: opening.scope,
        share: opening.root_share,
        support: support_occurrence,
        viewed: child,
        hold: None,
    };
    let state = ExecutionState::new().with_resource_context_and_loan_dependencies(
        resources,
        [(child_occurrence, binding.clone())],
    );
    assert!(state.loan_bindings_are_consistent());
    let mut tampered = binding.clone();
    tampered.viewed = ResourceFact::view_token("v11_other_child".into(), Vec::new());
    let mut tampered_state = state;
    tampered_state.loan_view_bindings =
        LoanViewBindings::default().with_inserted(child_occurrence, tampered);
    assert!(!tampered_state.loan_bindings_are_consistent());

    let retained = tampered_state.with_resource_context(ResourceContext::new());
    assert!(
        retained
            .resources()
            .live_loan_dependencies()
            .next()
            .is_none()
    );
    assert!(retained.loan_bindings_are_consistent());

    let first = LoanViewBindings::default().with_inserted(child_occurrence, binding.clone());
    let mut other_binding = binding;
    other_binding.viewed = ResourceFact::view_token("v11_identity_other".into(), Vec::new());
    let second = LoanViewBindings::default().with_inserted(child_occurrence, other_binding);
    assert_ne!(first, second);
}

/// A memory footprint is bytes; the element width only spells them (D6).
/// `p[2..3]` at width 4 and `p[8..12]` at width 1 name the same four bytes,
/// so each entails the other for ownership and for a view, and a mismatched
/// width by itself decides nothing either way.
#[test]
fn memory_entailment_relates_two_spellings_of_one_byte_footprint() {
    let assumptions = PureFactContext::new();
    let base = Pointer {
        block: "mixed-width-footprint".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let int32_cell = MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(2),
        MachineTerm::constant(3),
        4,
    );
    let same_bytes = MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(8),
        MachineTerm::constant(12),
        1,
    );
    let int32_context =
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(int32_cell.clone()));
    let byte_context =
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(same_bytes.clone()));
    assert!(
        int32_context.satisfies_fact(&ResourceFact::own_memory(same_bytes.clone()), &assumptions)
    );
    assert!(
        byte_context.satisfies_fact(&ResourceFact::own_memory(int32_cell.clone()), &assumptions)
    );
    assert!(int32_context.satisfies_fact(&ResourceFact::view_memory(same_bytes), &assumptions));
    assert!(byte_context.satisfies_fact(&ResourceFact::view_memory(int32_cell), &assumptions));

    // One byte past the end is still one byte too many.
    let one_byte_over = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(8),
        MachineTerm::constant(13),
        1,
    ));
    assert!(!int32_context.satisfies_fact(&one_byte_over, &assumptions));
    // A different four bytes of the same block is not the same footprint.
    let neighbour = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base,
        MachineTerm::constant(12),
        MachineTerm::constant(16),
        1,
    ));
    assert!(!int32_context.satisfies_fact(&neighbour, &assumptions));
}

/// Subtraction is bytewise too: taking a width-1 field out of a width-4 owner
/// leaves exactly the bytes the requirement did not name, spelled in the
/// owner's own coordinate system, and putting the piece back restores the
/// original owner.
#[test]
fn subtracting_a_byte_field_from_an_int32_owner_leaves_the_bytewise_remainder() {
    let assumptions = PureFactContext::new();
    let base = Pointer {
        block: "mixed-width-split".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let owner = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(2),
        MachineTerm::constant(4),
        4,
    ));
    let byte_field = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(8),
        MachineTerm::constant(12),
        1,
    ));
    let context = ResourceContext::new()
        .try_compose_with_fact(owner.clone(), &assumptions)
        .unwrap();
    let residual = context
        .clone()
        .without_fact_incrementally(&byte_field, &assumptions)
        .expect("a width-1 field is consumable from a width-4 owner");
    let remainder = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base,
        MachineTerm::constant(3),
        MachineTerm::constant(4),
        4,
    ));
    assert!(residual.satisfies_fact(&remainder, &assumptions));
    assert!(!residual.satisfies_fact(&byte_field, &assumptions));
    assert!(!residual.satisfies_fact(&owner, &assumptions));
    assert_eq!(
        residual.clone().normalized(&assumptions).facts(),
        [remainder]
    );

    // The bytes are conserved: returning the lent piece rebuilds the owner.
    let restored = residual
        .try_compose_with_fact(byte_field, &assumptions)
        .unwrap()
        .normalized(&assumptions);
    assert!(restored.satisfies_fact(&owner, &assumptions));
    assert!(restored.is_valid(&assumptions));
}

/// Two owners whose bytes do not meet stay two owners whatever their widths,
/// and the context composes and stays valid; where they abut, normalization
/// puts them back together instead of leaving the context fragmented across
/// two spellings of one block.
#[test]
fn bytewise_disjoint_mismatched_width_owners_compose_and_adjacent_ones_merge() {
    let assumptions = PureFactContext::new();
    let base = Pointer {
        block: "mixed-width-composition".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let int32_head = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(2),
        4,
    ));
    let distant_bytes = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(12),
        MachineTerm::constant(16),
        1,
    ));
    let disjoint = ResourceContext::new()
        .try_compose_with_fact(int32_head.clone(), &assumptions)
        .unwrap()
        .try_compose_with_fact(distant_bytes.clone(), &assumptions)
        .expect("bytewise-disjoint owners compose whatever their widths");
    assert!(disjoint.is_valid(&assumptions));
    assert!(disjoint.satisfies_fact(&int32_head, &assumptions));
    assert!(disjoint.satisfies_fact(&distant_bytes, &assumptions));
    assert!(!disjoint.satisfies_fact(
        &ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base.clone(),
            MachineTerm::constant(8),
            MachineTerm::constant(12),
            1,
        )),
        &assumptions
    ));

    let adjacent_bytes = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(8),
        MachineTerm::constant(12),
        1,
    ));
    let merged = ResourceContext::new()
        .try_compose_with_fact(int32_head, &assumptions)
        .unwrap()
        .try_compose_with_fact(adjacent_bytes, &assumptions)
        .unwrap()
        .normalized(&assumptions);
    assert_eq!(
        merged.facts(),
        [ResourceFact::own_memory(
            MemoryRange::new_with_element_width(
                base,
                MachineTerm::constant(0),
                MachineTerm::constant(3),
                4,
            )
        )]
    );
}

/// Owned pieces over displaced spellings of one symbolic base, the shape a
/// call on `x + 1` or `x + i` returns, rejoin their neighbours over `x` when
/// restated over `x` they abut exactly.
#[test]
fn owned_pieces_over_displaced_bases_rejoin_where_they_abut() {
    let x = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(88_100)), 4),
    };
    let i = MachineTerm::Variable(Variable(88_101));
    let own = |base: &Pointer, start: MachineTerm, end: MachineTerm| {
        ResourceFact::own_memory(MemoryRange::new(base.clone(), start, end))
    };
    let constant = MachineTerm::constant;
    let assumptions = PureFactContext::new();

    let constant_pieces = ResourceContext::new()
        .unchecked_with_facts([
            own(&x, constant(0), constant(1)),
            own(&x, constant(2), constant(4)),
            own(&x.offset_by_bytes(4), constant(0), constant(1)),
        ])
        .normalized(&assumptions);
    assert_eq!(constant_pieces.facts(), [own(&x, constant(0), constant(4))]);

    let symbolic_pieces = ResourceContext::new()
        .unchecked_with_facts([
            own(&x, constant(0), i.clone()),
            own(
                &x.offset_by_int32_elements(i.clone()),
                constant(0),
                constant(1),
            ),
        ])
        .normalized(&assumptions);
    assert_eq!(
        symbolic_pieces.facts(),
        [own(
            &x,
            constant(0),
            MachineTerm::add(i.clone(), constant(1))
        )]
    );
}

#[test]
fn mixed_width_symbolic_ranges_do_not_join_across_gaps_or_overlaps() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(88_900)), 4),
    };
    for start in [11, 13] {
        let pieces = [
            ResourceFact::own_memory(MemoryRange::new(
                base.offset_by_bytes(8),
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            )),
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                base.clone(),
                MachineTerm::constant(start),
                MachineTerm::constant(16),
                1,
            )),
        ];
        let context = ResourceContext::new()
            .unchecked_with_facts(pieces)
            .normalized(&PureFactContext::new());
        assert_eq!(context.facts().len(), 2);
        assert!(!context.satisfies_fact(
            &ResourceFact::own_memory(MemoryRange::new(
                base.clone(),
                MachineTerm::constant(2),
                MachineTerm::constant(4)
            )),
            &PureFactContext::new()
        ));
    }
}

/// A displaced piece stays apart from a neighbour it may not abut: a gap, an
/// overlap, or a restated start that is exact only while `i + 1` does not
/// wrap all leave the pieces as they were.
#[test]
fn owned_pieces_over_displaced_bases_that_may_not_abut_stay_apart() {
    let x = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(88_200)), 4),
    };
    let i = MachineTerm::Variable(Variable(88_201));
    let own = |base: &Pointer, start: MachineTerm, end: MachineTerm| {
        ResourceFact::own_memory(MemoryRange::new(base.clone(), start, end))
    };
    let constant = MachineTerm::constant;
    let assumptions = PureFactContext::new();
    for pieces in [
        // A gap: `x[1..2]` is held by no one.
        [
            own(&x, constant(0), constant(1)),
            own(&x.offset_by_bytes(8), constant(0), constant(1)),
        ],
        // An overlap at `x[1..2]`.
        [
            own(&x, constant(0), constant(2)),
            own(&x.offset_by_bytes(4), constant(0), constant(1)),
        ],
        // `(x + i)[1..2]` is `x[i + 1..i + 2]` only while `i + 1` does not wrap.
        [
            own(&x, constant(0), MachineTerm::add(i.clone(), constant(1))),
            own(
                &x.offset_by_int32_elements(i.clone()),
                constant(1),
                constant(2),
            ),
        ],
    ] {
        let normalized = ResourceContext::new()
            .unchecked_with_facts(pieces.clone())
            .normalized(&assumptions);
        let mut facts = normalized.facts().to_vec();
        let mut expected = pieces.to_vec();
        facts.sort();
        expected.sort();
        assert_eq!(facts, expected);
    }
}

#[test]
fn distinct_heap_allocations_never_merge_under_contradictory_assumptions() {
    let block = |id: u64| Pointer {
        block: PointerBlock::Heap(id),
        offset: PointerOffsetTerm::Constant(0),
    };
    let (b, c) = (block(1000001), block(1000002));
    let alloc_b = ResourceFact::own_allocation(b.clone(), 16u32);
    let alloc_c = ResourceFact::own_allocation(c.clone(), 16u32);
    // A contradictory `false`-is-true fact must not let normalization merge
    // distinct heap authorities. Heap identities are unique by construction.
    let poisoned = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::Constant(false),
        true,
    ));
    let normalized = ResourceContext::new()
        .unchecked_with_fact(alloc_b.clone())
        .unchecked_with_fact(alloc_c.clone())
        .normalized(&poisoned);
    let mut quantities = std::collections::BTreeMap::new();
    for fact in normalized.facts() {
        if let Some((base, _)) = fact.allocation() {
            *quantities.entry(format!("{base:?}")).or_insert(0u32) +=
                fact.owned_quantity().unwrap_or(0);
        }
    }
    assert_eq!(
        quantities.values().copied().max(),
        Some(1),
        "distinct allocations must stay unique: {quantities:?}"
    );
    assert!(
        normalized.satisfies_fact(&alloc_b, &poisoned)
            && normalized.satisfies_fact(&alloc_c, &poisoned),
        "both authorities must remain usable"
    );
}

/// An element index is signed, and both of `memory_range_covers`'s
/// constant-arithmetic arms used to read one as an unsigned residue: the
/// fact-pinned arm read every endpoint through `as_const`, which answers
/// `u32`, and the structural arm folded the base delta into each endpoint with
/// the modular `MachineTerm::add`. Both drew a *positive containment*
/// conclusion from it, which is the direction a residue cannot support.
mod constant_range_containment {
    use super::*;

    fn external(elements: i64) -> Pointer {
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(elements * 4),
        }
    }

    fn range(base: Pointer, start: i32, end: i32) -> MemoryRange {
        MemoryRange::new(
            base,
            MachineTerm::constant(start as u32),
            MachineTerm::constant(end as u32),
        )
    }

    fn covers(available: &MemoryRange, required: &MemoryRange) -> bool {
        crate::kernel::memory_range_covers(available, required, &PureFactContext::new())
    }

    #[test]
    fn a_range_below_the_owner_is_not_covered_by_it() {
        let owned = range(external(0), 0, 1);
        // `p[-1..0]` is the element *before* `p`. Read as `u32` its start is
        // `4294967295`, which clears `available_start <= required_start`
        // against every owner, and its end is `0`, which clears the other
        // side against every owner whose own end is nonnegative.
        assert!(!covers(&owned, &range(external(0), -1, 0)));
        assert!(!covers(&owned, &range(external(0), -1, 1)));
        assert!(!covers(&owned, &range(external(0), -3, 0)));
        // The same ranges from an owner that does hold them.
        let wide = range(external(-3), 0, 4);
        assert!(covers(&wide, &range(external(0), -1, 0)));
        assert!(covers(&wide, &range(external(0), -1, 1)));
        assert!(covers(&wide, &range(external(0), -3, 0)));
    }

    #[test]
    fn a_base_far_below_the_owner_does_not_wrap_into_it() {
        let owned = range(external(0), 0, 1);
        // `q = &p[i32::MIN]`. The relative start `i32::MIN + (-1)` wraps to
        // `i32::MAX` and the relative end to `i32::MIN`, which bracket every
        // constant range there is; the true position is `2^31 + 1` elements
        // below `p`.
        let far = external(i64::from(i32::MIN));
        assert!(!covers(&owned, &range(far.clone(), -1, 0)));
        assert!(!covers(&owned, &range(far, 0, 1)));
        // A base a constant distance inside the owner still answers.
        assert!(covers(&range(external(0), 0, 4), &range(external(1), 0, 2)));
        assert!(!covers(
            &range(external(0), 0, 4),
            &range(external(1), 0, 4)
        ));
    }

    #[test]
    fn a_range_is_its_start_and_its_count_not_its_endpoints() {
        // `p[i32::MAX..i32::MIN]` is a forward range of exactly one element,
        // at `i32::MAX`. Reading its endpoints as an interval would place it
        // inside anything at all.
        let one_at_the_top = range(external(0), i32::MAX, i32::MIN);
        assert!(!covers(&range(external(0), 0, 1), &one_at_the_top));
        assert!(covers(&one_at_the_top, &one_at_the_top));
        assert!(covers(
            &range(external(0), i32::MAX - 1, i32::MIN),
            &one_at_the_top
        ));
    }

    #[test]
    fn a_base_delta_the_facts_pin_is_still_taken() {
        let index = MachineTerm::Variable(Variable(93_960));
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let child = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
        };
        let owned = range(base, 0, 4);
        let required = MemoryRange::new(child, MachineTerm::constant(0), MachineTerm::constant(1));
        let pinned = |value: i32| {
            PureFactContext::new().assume_condition(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(index.clone()),
                    right: Box::new(MachineTerm::constant(value as u32)),
                },
                true,
            )
        };
        assert!(crate::kernel::memory_range_covers(
            &owned,
            &required,
            &pinned(2)
        ));
        assert!(!crate::kernel::memory_range_covers(
            &owned,
            &required,
            &pinned(-1)
        ));
        assert!(!crate::kernel::memory_range_covers(
            &owned,
            &required,
            &pinned(4)
        ));
    }
}

/// An owned population's quantity is an `int32`. Every rule that *orders* one
/// asks the `int32` `>=` comparison, except the two constant arms that
/// decide whether an owner may observe itself, which read the bits.
mod owned_quantity_sign {
    use super::*;

    fn token(quantity: i32) -> ResourceFact {
        ResourceFact::own_quantity(
            Resource::Token {
                name: "tok".to_string(),
                arguments: Vec::new().into(),
            },
            MachineTerm::constant(quantity as u32),
        )
    }

    fn viewed() -> ResourceFact {
        ResourceFact::View(Resource::Token {
            name: "tok".to_string(),
            arguments: Vec::new().into(),
        })
    }

    /// A population of `-1` owns nothing, so it exposes no viewed description
    /// of itself and entails no view. `-294967296` is the quantity two
    /// declared-nonnegative `produces 2000000000 of` clauses compose to.
    #[test]
    fn a_negative_population_observes_nothing() {
        let assumptions = PureFactContext::new();
        for quantity in [-1, i32::MIN, -294_967_296, 0] {
            let owned = token(quantity);
            assert_eq!(owned.core(), None);
            assert_eq!(owned.core_with_assumptions(&assumptions), None);
            assert!(!owned.has_proven_positive_quantity(&assumptions));
            assert!(
                !ResourceContext::new()
                    .unchecked_with_fact(owned)
                    .satisfies_fact(&viewed(), &assumptions)
            );
        }
    }

    /// The other polarity: a positive population still observes itself, at
    /// one unit and at the largest quantity there is.
    #[test]
    fn a_positive_population_still_observes_itself() {
        let assumptions = PureFactContext::new();
        for quantity in [1, 2, i32::MAX] {
            let owned = token(quantity);
            assert_eq!(owned.core(), Some(viewed()));
            assert_eq!(owned.core_with_assumptions(&assumptions), Some(viewed()));
            assert!(owned.has_proven_positive_quantity(&assumptions));
            assert!(
                ResourceContext::new()
                    .unchecked_with_fact(owned)
                    .satisfies_fact(&viewed(), &assumptions)
            );
        }
    }
}

/// A population count is a mathematical natural number, so the merge that
/// composes two owned quantities into one must state the total exactly or
/// decline. Composing them with the modular `MachineTerm::add` made two
/// `produces 2000000000 of tok(o)` clauses a population of `-294967296`, and
/// `ensures count(tok(o)) < 0` verified over four billion produced units.
mod population_quantity_totals {
    use super::*;

    fn token(quantity: MachineTerm) -> ResourceFact {
        ResourceFact::own_quantity(
            Resource::Token {
                name: "tok".to_string(),
                arguments: Vec::new().into(),
            },
            quantity,
        )
    }

    fn constant(quantity: i32) -> MachineTerm {
        MachineTerm::constant(quantity as u32)
    }

    /// The quantity the merge of these two facts carries, or `None` where the
    /// two were left where they are.
    fn merged_quantity(
        left: MachineTerm,
        right: MachineTerm,
        assumptions: &PureFactContext,
    ) -> Option<MachineTerm> {
        let merged = ResourceContext::new()
            .unchecked_with_fact(token(left))
            .unchecked_with_fact(token(right))
            .normalized(assumptions);
        let facts = merged.facts().to_vec();
        match facts.as_slice() {
            [fact] => Some(fact.owned_quantity_term().cloned().expect("owned quantity")),
            _ => None,
        }
    }

    /// Neither the wrapped total nor any other number: the pair is left
    /// alone, and each fact still says what its clause said.
    #[test]
    fn an_overflowing_total_is_not_composed() {
        let assumptions = PureFactContext::new();
        for (left, right) in [
            (2_000_000_000, 2_000_000_000),
            (i32::MAX, 1),
            (1, i32::MAX),
            (i32::MAX, i32::MAX),
            // A total that wraps all the way back to a plausible-looking
            // positive number is the same defect wearing a friendlier value.
            (1_500_000_000, 1_500_000_000),
        ] {
            assert_eq!(
                merged_quantity(constant(left), constant(right), &assumptions),
                None,
                "{left} + {right} was composed"
            );
        }
        // A total that leaves the range downwards is not a count either.
        assert_eq!(
            merged_quantity(constant(-1), constant(-1), &assumptions),
            None
        );
    }

    /// The other polarity: a total that is a count is still composed, at the
    /// ordinary quantities and at the largest one that fits.
    #[test]
    fn a_total_that_is_a_count_is_still_composed() {
        let assumptions = PureFactContext::new();
        for (left, right) in [(1, 1), (2, 5), (2_000_000_000, 147_483_647), (i32::MAX, 0)] {
            assert_eq!(
                merged_quantity(constant(left), constant(right), &assumptions),
                Some(constant(left + right)),
                "{left} + {right} was not composed"
            );
        }
    }

    /// A symbolic merge requires its addition bound, for both a pair of
    /// variables and an increment by one.
    #[test]
    fn symbolic_totals_require_checked_addition_bounds() {
        let quantity = MachineTerm::Variable(Variable(7));
        let other = MachineTerm::Variable(Variable(8));
        for right in [quantity.clone(), other, MachineTerm::constant(1)] {
            assert_eq!(
                merged_quantity(quantity.clone(), right.clone(), &PureFactContext::new()),
                None
            );
            let assumptions = PureFactContext::new().assume_condition(
                ConditionTerm::signed_add_overflows(quantity.clone(), right.clone()),
                false,
            );
            assert_eq!(
                merged_quantity(quantity.clone(), right.clone(), &assumptions),
                Some(MachineTerm::add(quantity.clone(), right))
            );
        }
    }

    /// The one symbolic exception: recombining a framed remainder lands on
    /// the term the split was taken from, which is exact whatever the pieces
    /// are, and is what a contract refinement does.
    #[test]
    fn recombining_a_framed_remainder_restores_its_term() {
        let assumptions = PureFactContext::new();
        let available = MachineTerm::Variable(Variable(11));
        let used = MachineTerm::Variable(Variable(12));
        let remainder = binary_node!(
            Int32,
            Subtract,
            Box::new(available.clone()),
            Box::new(used.clone())
        );
        assert_eq!(
            merged_quantity(used.clone(), remainder.clone(), &assumptions),
            Some(available.clone())
        );
        assert_eq!(
            merged_quantity(remainder, used, &assumptions),
            Some(available)
        );
    }
}

/// The partition gate over one block of constant, same-base owned ranges is a
/// linear sweep instead of a pairwise scan, and the incremental path beside it
/// probes only the neighbours of a new range in the `concrete_memory` key
/// order. Both stand in for the scan *only on the order they assume*. Read as
/// `u32`, a range starting below its base sorts past every range there is, so
/// its overlapping neighbour is never the one it is compared against.
mod concrete_partition_sweep {
    use super::*;

    fn external() -> Pointer {
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn owns(start: i32, end: i32) -> ResourceFact {
        ResourceFact::own_memory(MemoryRange::new(
            external(),
            MachineTerm::constant(start as u32),
            MachineTerm::constant(end as u32),
        ))
    }

    /// Both routes into the gate: the whole-context check, and the
    /// incremental one that adds the last fact to an already-valid context.
    fn admits(facts: &[ResourceFact]) -> bool {
        let assumptions = PureFactContext::new();
        let mut whole = ResourceContext::new();
        for fact in facts {
            whole = whole.unchecked_with_fact(fact.clone());
        }
        if whole.validity_error(&assumptions).is_some() {
            return false;
        }
        let (last, earlier) = facts.split_last().expect("at least one fact");
        let mut incremental = ResourceContext::new();
        for fact in earlier {
            incremental = incremental.unchecked_with_fact(fact.clone());
        }
        incremental
            .try_compose_into_valid_context_delaying_normalization(
                std::iter::once(last.clone()),
                &assumptions,
            )
            .is_ok()
    }

    #[test]
    fn neighbour_order_uses_exact_bytes_for_native_and_mixed_width_ranges() {
        let native = |start, end, width| {
            ResourceFact::own_memory(MemoryRange::new_wide(
                external(),
                MachineTerm::uint64_constant(start),
                MachineTerm::uint64_constant(end),
                width,
            ))
        };
        let bytes = |start: u32, end: u32| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                external(),
                start.into(),
                end.into(),
                1,
            ))
        };
        // Element-coordinate ordering would place the disjoint byte decoy
        // between the overlapping four-byte ranges.
        let cases = [
            [owns(10, 20), bytes(21u32, 22u32), owns(19, 23)],
            [native(10, 20, 4), bytes(21, 22), native(19, 23, 4)],
            [native(10, 20, 4), bytes(21, 22), bytes(76, 92)],
            [
                native(1 << 33, (1 << 33) + 8, 4),
                owns(0, 1),
                native((1 << 33) + 7, (1 << 33) + 9, 4),
            ],
            // Unrepresentable byte coordinates must not wrap into the index.
            [
                native(u64::MAX - 8, u64::MAX - 2, 1),
                owns(0, 1),
                native(u64::MAX - 4, u64::MAX - 1, 1),
            ],
        ];
        let assumptions = PureFactContext::new();
        for [first, decoy, overlapping] in cases {
            let context = ResourceContext::new().unchecked_with_facts([first, decoy]);
            assert!(
                context
                    .clone()
                    .unchecked_with_fact(overlapping.clone())
                    .validity_error(&assumptions)
                    .is_some()
            );
            assert!(
                context
                    .try_compose_into_valid_context_delaying_normalization(
                        [overlapping],
                        &assumptions,
                    )
                    .is_err()
            );
        }
    }

    /// `p[-1..1]` and `p[0..2]` are two owners of element `p[0]`. With a
    /// decoy between them in unsigned order the sweep compared the negative
    /// range only against the decoy, and the neighbour probe found only the
    /// decoy either side of it.
    #[test]
    fn a_range_below_its_base_is_compared_against_the_range_it_overlaps() {
        assert!(!admits(&[owns(0, 2), owns(5, 6), owns(-1, 1)]));
        // Order of arrival does not decide it.
        assert!(!admits(&[owns(-1, 1), owns(5, 6), owns(0, 2)]));
        assert!(!admits(&[owns(5, 6), owns(0, 2), owns(-1, 1)]));
        // Two decoys either side, and an overlap that is wholly below the
        // base rather than straddling it.
        assert!(!admits(&[
            owns(-9, -6),
            owns(0, 2),
            owns(5, 6),
            owns(-8, -7)
        ]));
        // The running maximum end is read signed too: a range whose *end* is
        // below the base must not be taken as the furthest one.
        assert!(!admits(&[owns(-4, -1), owns(0, 2), owns(1, 3)]));
    }

    /// The other polarity: a partition of ranges below, across and above the
    /// base is still a partition, and the sweep still refuses an ordinary
    /// nonnegative overlap.
    #[test]
    fn ranges_that_partition_the_block_are_still_admitted() {
        assert!(admits(&[owns(-4, -1), owns(-1, 0), owns(0, 2), owns(5, 6)]));
        assert!(admits(&[owns(5, 6), owns(0, 2), owns(-4, -1)]));
        assert!(admits(&[owns(i32::MIN, i32::MIN + 2), owns(0, 1)]));
        assert!(!admits(&[owns(0, 2), owns(5, 6), owns(1, 3)]));
        assert!(!admits(&[owns(-4, -1), owns(5, 6), owns(-2, 0)]));
    }
}

/// `split_memory_range` states the residues in the owner's coordinates, so the
/// requirement's endpoints cross a base delta to get there. That join used the
/// modular `MachineTerm::add` and installed the result as the residues'
/// own bounds, so a carry left the holder an owned fact over cells the
/// requirement had taken — and `consumed_range_is_well_formed` cannot see it,
/// because it compares the same two wrapped terms with each other.
mod residue_bounds {
    use super::*;

    fn external(elements: i64) -> Pointer {
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(elements * 4),
        }
    }

    fn range(base: Pointer, start: MachineTerm, end: MachineTerm) -> MemoryRange {
        MemoryRange::new(base, start, end)
    }

    fn constant(value: i32) -> MachineTerm {
        MachineTerm::constant(value as u32)
    }

    fn split(
        available: &MemoryRange,
        required: &MemoryRange,
        assumptions: &PureFactContext,
    ) -> Option<Vec<MemoryRange>> {
        crate::kernel::split_memory_range(available, required, assumptions)
    }

    #[test]
    fn an_ordinary_split_keeps_both_sides() {
        let assumptions = PureFactContext::new();
        let available = range(external(0), constant(0), constant(4));
        let residues = split(
            &available,
            &range(external(1), constant(0), constant(2)),
            &assumptions,
        )
        .expect("a constant split inside the owner");
        assert_eq!(
            residues,
            vec![
                range(external(0), constant(0), constant(1)),
                range(external(0), constant(3), constant(4)),
            ]
        );
        // The same requirement stated in the owner's own coordinates.
        assert_eq!(
            split(
                &available,
                &range(external(0), constant(1), constant(3)),
                &assumptions
            )
            .expect("a split with a zero base delta"),
            vec![
                range(external(0), constant(0), constant(1)),
                range(external(0), constant(3), constant(4)),
            ]
        );
    }

    #[test]
    fn a_carrying_base_delta_states_no_residue() {
        let assumptions = PureFactContext::new();
        let available = range(external(0), constant(0), constant(10));
        // `&p[i32::MAX]` is the delta, and `i32::MAX + 2` carries: the sum is
        // `2^31 + 1` elements above the owner's base, while the residue reads
        // as `i32::MIN + 1`, which the owner's endpoints bracket.
        let required = range(external(i64::from(i32::MAX)), constant(2), constant(3));
        assert_eq!(split(&available, &required, &assumptions), None);
        // The same shape at a base whose join stays put still splits.
        assert_eq!(
            split(
                &available,
                &range(external(3), constant(2), constant(3)),
                &assumptions
            )
            .expect("a join that does not carry"),
            vec![
                range(external(0), constant(0), constant(5)),
                range(external(0), constant(6), constant(10)),
            ]
        );
    }

    #[test]
    fn a_symbolic_join_asks_whether_it_carries() {
        let index = MachineTerm::Variable(Variable(93_970));
        let count = MachineTerm::Variable(Variable(93_971));
        let available = range(external(0), constant(0), count);
        let required = MemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
            },
            constant(1),
            constant(2),
        );
        // `i + 1` is one element above `i` only while the add does not carry.
        assert_eq!(split(&available, &required, &PureFactContext::new()), None);
        let no_carry = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_add_overflows(index.clone(), constant(1)),
                false,
            )
            .assume_condition(
                ConditionTerm::signed_add_overflows(index.clone(), constant(2)),
                false,
            );
        assert!(split(&available, &required, &no_carry).is_some());
        // The requirement stated in the owner's own coordinates has no add to
        // carry, and is the shape a split ordinarily arrives in.
        assert!(
            split(
                &available,
                &range(
                    external(0),
                    index.clone(),
                    MachineTerm::add(index, constant(1))
                ),
                &PureFactContext::new()
            )
            .is_some()
        );
    }
}

#[test]
fn named_population_members_keep_identity_and_fields_independent_of_count() {
    let schema = ResourceFieldSchema::new(vec![(
        "serial".into(),
        ResourceFieldType::Program(ProgramType::Int32),
    )])
    .unwrap();
    let block = PointerBlock::Heap(940_501);
    let pointer = Pointer {
        block: block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let arguments: ResourceArguments = vec![ProgramValue::pointer(pointer.clone()).into()].into();
    let description =
        crate::kernel::ResourceDescription::new("ticket".into(), arguments.clone(), schema.clone());
    let authority = ResourceFact::own(Resource::PopulationAuthority(description.clone()));
    let mut created = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(
            Memory::new()
                .with_heap_allocation_claim(pointer, HeapExtent::int32(4))
                .unwrap(),
        );
    created.record_population_storage_creation(block.clone());
    let assumptions = PureFactContext::new();
    let (empty, _) = created
        .checked_population_authority_exchange(&authority, true, &assumptions)
        .unwrap();
    let definition = CompositeResourceDefinition::new(
        "ticket",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![],
        vec![],
    )
    .with_instance_schema(Some(schema.clone()));
    let member = |serial| {
        ResourceInstance::new(
            Variable::allocate_fresh().unwrap(),
            "ticket".into(),
            arguments.clone(),
            schema.clone(),
            vec![int32(serial).into()].into(),
        )
        .unwrap()
    };
    let first = member(1);
    let second = member(2);
    let rewrite = |state: &ExecutionState, instance: &ResourceInstance, unfold| {
        rewrite_resource_instance(state, instance, &definition, &assumptions, unfold)
            .map(|(next, _)| next)
    };
    let count = |state: &ExecutionState| {
        state
            .population_effects
            .creation
            .as_ref()
            .unwrap()
            .observe(&block, "ticket")
            .unwrap()
    };
    for quantity in [
        MachineTerm::constant(1),
        MachineTerm::constant(2),
        MachineTerm::Variable(Variable::allocate_fresh().unwrap()),
    ] {
        assert!(
            empty
                .population_effects
                .creation
                .as_ref()
                .unwrap()
                .checked_member_exchange_quantity(
                    &block,
                    &description,
                    true,
                    &quantity,
                    &assumptions
                )
                .is_err(),
            "an anonymous quantity cannot replace named occurrences and their fields"
        );
    }
    let one = rewrite(&empty, &first, false).unwrap();
    assert_eq!(count(&one), 1);
    assert_eq!(
        rewrite(&empty, &first, false)
            .unwrap()
            .population_effects
            .creation,
        one.population_effects.creation,
        "rechecking preserves the ledger successor"
    );
    let two = rewrite(&one, &second, false).unwrap();
    assert_eq!(count(&two), 2);
    assert_eq!(
        two.resources().owned_instance(first.identity()),
        Some(&first)
    );
    assert_eq!(
        two.resources().owned_instance(second.identity()),
        Some(&second)
    );
    assert!(
        rewrite(&two, &second, false).is_err(),
        "identity cannot be duplicated"
    );
    let mut forged = second.clone();
    forged.fields = vec![int32(99).into()].into();
    assert!(
        rewrite(&two, &forged, true).is_err(),
        "count does not authorize different fields"
    );
    assert!(
        two.checked_population_authority_exchange(&authority, false, &assumptions)
            .is_err(),
        "live members block retirement"
    );
    let without_authority = two.clone().with_resource_context(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own(Resource::Instance(first.clone()))),
    );
    assert!(
        rewrite(&without_authority, &first, true).is_err(),
        "member ownership does not grant authority"
    );
    let remaining = rewrite(&two, &first, true).unwrap();
    assert_eq!(count(&remaining), 1);
    assert_eq!(
        remaining.resources().owned_instance(second.identity()),
        Some(&second)
    );
    assert!(
        rewrite(&remaining, &first, true).is_err(),
        "consumption is single spend"
    );
    let zero = rewrite(&remaining, &second, true).unwrap();
    assert_eq!(count(&zero), 0);
    zero.checked_population_authority_exchange(&authority, false, &assumptions)
        .unwrap();
    let before_authority = rewrite(&created, &first, false).unwrap();
    assert!(
        before_authority
            .checked_population_authority_exchange(&authority, true, &assumptions)
            .is_err(),
        "prior members prohibit a fresh empty authority"
    );
}

#[test]
fn predicate_population_state_reads_saved_count_without_transfer_rights() {
    let pointer = Pointer {
        block: PointerBlock::Heap(940_601),
        offset: PointerOffsetTerm::Constant(0),
    };
    let arguments: ResourceArguments = vec![ProgramValue::pointer(pointer.clone()).into()].into();
    let description = crate::kernel::ResourceDescription::new(
        "member".into(),
        arguments.clone(),
        ResourceFieldSchema::new(vec![]).unwrap(),
    );
    let authority = ResourceFact::own(Resource::PopulationAuthority(description));
    let selected = ResourceFact::own(Resource::Composite {
        name: "member".into(),
        arguments: arguments.clone(),
    });
    let definition = CompositeResourceDefinition::new(
        "member",
        vec![program_parameter("p", ProgramType::Int32Pointer)],
        None,
        false,
        vec![],
        vec![],
    );
    let assumptions = PureFactContext::new();
    let mut created = ExecutionState::new()
        .with_population_creation_tracking()
        .with_memory(
            Memory::new()
                .with_heap_allocation_claim(pointer.clone(), HeapExtent::int32(4))
                .unwrap(),
        );
    created.record_population_storage_creation(pointer.block.clone());
    let (empty, _) = created
        .checked_population_authority_exchange(&authority, true, &assumptions)
        .unwrap();
    let (one, _) = empty
        .checked_population_member_exchange(&selected, true, &definition, &assumptions)
        .unwrap();
    let retained_state = one.resource_state_source();
    let (two, _) = one
        .checked_population_member_exchange(&selected, true, &definition, &assumptions)
        .unwrap();
    let expression = SpecExpression::CountedResourceCount {
        name: "member".into(),
        arguments: vec![Some(SpecExpression::Value(ProgramValue::pointer(pointer)))],
    };
    let read = |state: &ExecutionState| {
        program_evaluate_speprogram_expression_at_state(state, &expression, None, &assumptions)
            .unwrap()
            .0
    };
    assert_eq!(read(&retained_state), int32(1));
    assert_eq!(read(&retained_state.resource_state_source()), int32(1));
    assert_eq!(read(&two), int32(2));
    assert!(
        !retained_state
            .resources()
            .satisfies_fact(&authority, &assumptions)
    );
    assert!(
        !retained_state
            .resources()
            .satisfies_fact(&selected, &assumptions)
    );
    // Even explicitly supplying custody cannot turn a logical state into
    // a second branch of the linear population ledger.
    let forged = retained_state.with_resource_context(one.resources().clone());
    let instance = ResourceInstance::new(
        Variable::allocate_fresh().unwrap(),
        "member".into(),
        arguments,
        ResourceFieldSchema::new(vec![(
            "serial".into(),
            ResourceFieldType::Program(ProgramType::Int32),
        )])
        .unwrap(),
        vec![int32(7).into()].into(),
    )
    .unwrap();
    for establish in [false, true] {
        assert!(
            forged
                .checked_population_authority_exchange(&authority, establish, &assumptions)
                .is_err()
        );
        assert!(
            forged
                .checked_population_member_exchange(&selected, establish, &definition, &assumptions)
                .is_err()
        );
        assert!(
            forged
                .clone()
                .record_instance_population_exchange(&forged, &instance, establish, &assumptions)
                .is_err()
        );
    }
}

// A suffix uses a non-wrapping, full-width subtraction and the same backing
// identity. Neither a low-word bound nor an invented endpoint supplies it.
#[test]
fn wide_shifted_suffix_coverage_checks_extent_and_identity() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(983_100));
    let whole = MachineTerm::Variable(Variable(983_101));
    let taken = MachineTerm::Variable(Variable(983_102));
    let available = MemoryRange::new_wide(
        base.clone(),
        MachineTerm::uint64_constant(0),
        whole.clone(),
        4,
    );
    let required = MemoryRange::new_wide(
        base.offset_by_typed_elements(
            MachineTerm::uint64_subtract(whole.clone(), taken.clone()),
            4,
            true,
            true,
        ),
        MachineTerm::uint64_constant(0),
        taken.clone(),
        4,
    );
    let bounded = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_less_equal(
            whole.clone(),
            MachineTerm::uint64_constant(i64::MAX as u64 / 4),
        ),
        true,
    );
    let facts = bounded.clone().assume_condition(
        ConditionTerm::uint64_less_equal(taken.clone(), whole.clone()),
        true,
    );
    let covers = |a, b, f| crate::kernel::primitives::wide_memory_range_covers(a, b, f);
    assert!(covers(&available, &required, &facts));
    assert!(!covers(&available, &required, &bounded));
    let only_count = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_less_equal(taken.clone(), whole.clone()),
        true,
    );
    assert!(!covers(&available, &required, &only_count));
    let offset_suffix = MemoryRange::new_wide(
        base.offset_by_typed_elements(taken.clone(), 4, true, true),
        MachineTerm::uint64_constant(0),
        MachineTerm::uint64_subtract(whole.clone(), taken.clone()),
        4,
    );
    assert!(covers(&available, &offset_suffix, &facts));
    assert!(!covers(&available, &offset_suffix, &bounded));
    assert!(!covers(&available, &offset_suffix, &only_count));
    let low_words = bounded.clone().assume_condition(
        ConditionTerm::signed_less_equal(
            MachineTerm::uint32_from_64(taken.clone()),
            MachineTerm::uint32_from_64(whole),
        ),
        true,
    );
    assert!(!covers(&available, &required, &low_words));
    let unrelated = MemoryRange::new_wide(
        Pointer::symbolic(Variable(983_103)),
        MachineTerm::uint64_constant(0),
        taken.clone(),
        4,
    );
    assert!(!covers(&available, &unrelated, &facts));
    let wrong_count = MemoryRange::new_wide(
        required.base().clone(),
        MachineTerm::uint64_constant(0),
        MachineTerm::Variable(Variable(983_104)),
        4,
    );
    assert!(!covers(&available, &wrong_count, &facts));
    let wrapped = MemoryRange::new_wide(
        base.offset_by_typed_elements(MachineTerm::uint64_constant(u64::MAX), 4, true, true),
        MachineTerm::uint64_constant(0),
        MachineTerm::uint64_constant(2),
        4,
    );
    assert!(!covers(&available, &wrapped, &facts));
    let concrete = MemoryRange::new_wide(
        base.clone(),
        MachineTerm::uint64_constant(0),
        MachineTerm::uint64_constant(3),
        4,
    );
    let part = MemoryRange::new_wide(
        base.offset_by_typed_elements(MachineTerm::uint64_constant(1), 4, true, true),
        MachineTerm::uint64_constant(0),
        MachineTerm::uint64_constant(2),
        4,
    );
    let empty_facts = PureFactContext::new();
    assert!(covers(&concrete, &part, &empty_facts));
    let past = MemoryRange::new_wide(
        part.base().clone(),
        MachineTerm::uint64_constant(0),
        MachineTerm::uint64_constant(3),
        4,
    );
    assert!(!covers(&concrete, &past, &empty_facts));
}

#[test]
fn wide_range_observer_transport_rejects_changed_cells_and_low_word_equalities() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(983_200));
    let before = Memory::new().store(
        pointer.clone(),
        ProgramValue::UInt64(MachineTerm::uint64_constant(3)),
    );
    let old = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before.clone()),
        Box::new(pointer.clone()),
        LoadKind::Bits64,
    );
    let observer = MachineTerm::Variable(Variable(983_201));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_equal(observer.clone(), old.clone()),
        true,
    );
    assert!(facts.uint64_values_equal_for_range_resolution(&observer, &old));
    let after = before.store(
        pointer.clone(),
        ProgramValue::UInt64(MachineTerm::uint64_constant((1u64 << 32) + 3)),
    );
    let changed = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(after),
        Box::new(pointer),
        LoadKind::Bits64,
    );
    assert!(!facts.uint64_values_equal_for_range_resolution(&observer, &changed));
    let other = MachineTerm::Variable(Variable(983_202));
    let narrow = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(observer.clone(), other.clone()), true);
    assert!(!narrow.uint64_values_equal_for_range_resolution(&observer, &other));
}

/// Two readers that took a range's bounds as signed 32-bit indices met a
/// range with unsigned 64-bit bounds and stopped the verifier: resource
/// equality at a loop's back edge, and the byte renormalization a coverage
/// question falls back to when the element widths differ. Both now answer.
#[test]
fn wide_ranges_are_compared_and_refused_without_a_32_bit_reading() {
    let base = Pointer::symbolic(Variable(97_400));
    let end = MachineTerm::Variable(Variable(97_401));
    let other_end = MachineTerm::Variable(Variable(97_402));
    let wide = |end: &MachineTerm, width| {
        MemoryRange::new_wide(
            base.clone(),
            MachineTerm::uint64_constant(0),
            end.clone(),
            width,
        )
    };
    let narrow = MemoryRange::new_with_element_width(base.clone(), 0u32.into(), 4u32.into(), 1);
    let equal = |left: &MemoryRange, right: &MemoryRange| {
        crate::kernel::assumptions::resources_equal_ignoring_memories(
            &Resource::Memory(left.clone()),
            &Resource::Memory(right.clone()),
        )
    };
    assert!(equal(&wide(&end, 1), &wide(&end, 1)));
    assert!(!equal(&wide(&end, 1), &wide(&other_end, 1)));
    assert!(!equal(&wide(&end, 1), &narrow));
    assert!(!equal(&narrow, &wide(&end, 1)));

    let facts = PureFactContext::new();
    let covers = crate::kernel::primitives::memory_range_covers;
    assert!(!covers(&wide(&end, 1), &wide(&end, 4), &facts));
    assert!(!covers(&wide(&end, 4), &wide(&end, 1), &facts));
    let words = MemoryRange::new_with_element_width(base.clone(), 0u32.into(), 4u32.into(), 4);
    assert!(!covers(&wide(&end, 1), &words, &facts));
    assert!(!covers(&words, &wide(&end, 1), &facts));
}

#[test]
fn a_field_access_in_a_wide_struct_array_byte_range_is_placed_over_elements() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(983_410));
    let count = MachineTerm::Variable(Variable(983_411));
    let index = MachineTerm::Variable(Variable(983_412));
    // `m * 8u64` bytes of eight-byte structs, as a 64-bit heap block holds them.
    let bytes = MachineTerm::uint64_multiply(count.clone(), MachineTerm::uint64_constant(8));
    let range = MemoryRange::new_wide(base.clone(), MachineTerm::uint64_constant(0), bytes, 1);
    let at = |offset: PointerOffsetTerm| Pointer {
        block: base.block.clone(),
        offset,
    };
    let field = |scaled: PointerOffsetTerm, bytes: i64| {
        at(PointerOffsetTerm::Add(
            Box::new(scaled),
            Box::new(PointerOffsetTerm::Constant(bytes)),
        ))
    };
    let unsigned = PointerOffsetTerm::scaled_int64_node(index.clone(), 8, true);
    // The front end's `(int64)i * 8` byte displacement of `&p[i]`.
    let signed = PointerOffsetTerm::scaled_int64_node(
        MachineTerm::int64_multiply(index.clone(), MachineTerm::int64_constant(8)),
        1,
        false,
    );
    let assume = |facts: PureFactContext, condition| facts.assume_condition(condition, true);
    let bounded = assume(
        PureFactContext::new(),
        ConditionTerm::uint64_less_equal(count.clone(), MachineTerm::uint64_constant(100)),
    );
    let below = assume(
        bounded.clone(),
        ConditionTerm::uint64_less_than(index.clone(), count.clone()),
    );
    for scaled in [&unsigned, &signed] {
        assert!(below.pointer_access_in_wide_range(&field(scaled.clone(), 4), 4, &range));
        assert!(below.pointer_access_in_wide_range(&field(scaled.clone(), 0), 4, &range));
        // An access crossing into the next element is not one field.
        assert!(!below.pointer_access_in_wide_range(&field(scaled.clone(), 4), 8, &range));
    }
    // `i <= m` admits `&p[m]`, whose fields lie past the block.
    let at_most = assume(
        bounded.clone(),
        ConditionTerm::uint64_less_equal(index.clone(), count.clone()),
    );
    assert!(!at_most.pointer_access_in_wide_range(&field(unsigned.clone(), 4), 4, &range));
    // Without `m <= PTRDIFF_MAX / 8` the product may wrap: `i < m` places
    // nothing in `m * 8u64` bytes.
    let unbounded = assume(
        PureFactContext::new(),
        ConditionTerm::uint64_less_than(index.clone(), count.clone()),
    );
    assert!(!unbounded.pointer_access_in_wide_range(&field(unsigned.clone(), 4), 4, &range));
    // A constant field of the first element needs one element.
    let first = at(PointerOffsetTerm::Constant(4));
    assert!(!bounded.pointer_access_in_wide_range(&first, 4, &range));
    let nonempty = assume(
        bounded,
        ConditionTerm::uint64_less_equal(MachineTerm::uint64_constant(1), count.clone()),
    );
    assert!(nonempty.pointer_access_in_wide_range(&first, 4, &range));
}

/// A wide range of `k`-byte structs and the byte range of the same bytes
/// stand for each other, in coverage and subtraction, once the product
/// relating them is decided not to wrap; never before.
#[test]
fn a_wide_struct_range_and_its_byte_range_are_respelled_under_no_wrap() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(983_420));
    let count = MachineTerm::Variable(Variable(983_421));
    let zero = MachineTerm::uint64_constant(0);
    let bytes = MachineTerm::uint64_multiply(count.clone(), MachineTerm::uint64_constant(8));
    let block = MemoryRange::new_wide(base.clone(), zero.clone(), bytes, 1);
    let structs = MemoryRange::new_wide(base.clone(), zero.clone(), count.clone(), 8);
    let bounded = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_less_equal(count.clone(), MachineTerm::uint64_constant(100)),
        true,
    );
    let unbounded = PureFactContext::new();
    for (available, required) in [(&block, &structs), (&structs, &block)] {
        assert!(crate::kernel::memory_range_covers(
            available, required, &bounded
        ));
        assert_eq!(
            crate::kernel::primitives::split_memory_range(available, required, &bounded),
            Some(Vec::new())
        );
        // `n * 8` may wrap: the byte range may hold fewer than `n` structs.
        assert!(!crate::kernel::memory_range_covers(
            available, required, &unbounded
        ));
        assert!(
            crate::kernel::primitives::split_memory_range(available, required, &unbounded)
                .is_none()
        );
    }
    // Taking the first struct of `n` leaves the other `n - 1`, in the owner's
    // width: the requirement's bytes `0..8` are not decided inside
    // `n * 8u64`, so the owner is re-spelled as structs instead.
    let nonempty = bounded.clone().assume_condition(
        ConditionTerm::uint64_less_equal(MachineTerm::uint64_constant(1), count.clone()),
        true,
    );
    let first = MemoryRange::new_wide(
        base.clone(),
        zero.clone(),
        MachineTerm::uint64_constant(1),
        8,
    );
    assert!(crate::kernel::memory_range_covers(
        &block, &first, &nonempty
    ));
    let residues =
        crate::kernel::primitives::split_memory_range(&block, &first, &nonempty).unwrap();
    assert_eq!(residues.len(), 1);
    assert_eq!(residues[0].element_width(), 8);
    // A struct width that does not divide the other has no re-spelling.
    let pairs = MemoryRange::new_wide(base, zero, count, 12);
    assert!(!crate::kernel::memory_range_covers(
        &block, &pairs, &bounded
    ));
}

/// A struct range required from a byte range whose struct count is not
/// bounded names the product that must not wrap; a bounded one is covered
/// and names nothing.
#[test]
fn a_wide_respelling_refusal_names_the_undecided_product() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(983_440));
    let count = MachineTerm::Variable(Variable(983_441));
    let zero = MachineTerm::uint64_constant(0);
    let bytes = MachineTerm::uint64_multiply(count.clone(), MachineTerm::uint64_constant(8));
    let held = MemoryRange::new_wide(base.clone(), zero.clone(), bytes, 1);
    let required = MemoryRange::new_wide(base, zero, count.clone(), 8);
    let bounded = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_less_equal(count.clone(), MachineTerm::uint64_constant(100)),
        true,
    );
    let refusal = |facts: &PureFactContext| {
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(held.clone()))
            .normalized(facts)
            .wide_range_respelling_refusal(&required, facts)
    };
    let no_wrap = refusal(&PureFactContext::new()).expect("the product is not decided");
    assert_eq!(no_wrap.range, ResourceFact::own_memory(required.clone()));
    assert_eq!(no_wrap.count, count);
    assert_eq!(no_wrap.factor, 8);
    assert!(refusal(&bounded).is_none());
}

/// A field of a struct in a held range of `k`-byte structs, and its element
/// address, are placed over the range's count, as they are in a byte block.
#[test]
fn a_field_access_in_a_wide_struct_range_is_placed_over_its_count() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(983_430));
    let count = MachineTerm::Variable(Variable(983_431));
    let index = MachineTerm::Variable(Variable(983_432));
    let range = MemoryRange::new_wide(
        base.clone(),
        MachineTerm::uint64_constant(0),
        count.clone(),
        8,
    );
    let at = |offset: PointerOffsetTerm| Pointer {
        block: base.block.clone(),
        offset,
    };
    let signed = PointerOffsetTerm::scaled_int64_node(
        MachineTerm::int64_multiply(index.clone(), MachineTerm::int64_constant(8)),
        1,
        false,
    );
    let field = |bytes: i64| {
        at(PointerOffsetTerm::Add(
            Box::new(signed.clone()),
            Box::new(PointerOffsetTerm::Constant(bytes)),
        ))
    };
    let assume = |facts: PureFactContext, condition| facts.assume_condition(condition, true);
    let bounded = assume(
        PureFactContext::new(),
        ConditionTerm::uint64_less_equal(count.clone(), MachineTerm::uint64_constant(100)),
    );
    let below = assume(
        bounded.clone(),
        ConditionTerm::uint64_less_than(index.clone(), count.clone()),
    );
    assert!(below.pointer_access_in_wide_range(&field(4), 4, &range));
    assert!(below.position_in_wide_struct_array(&field(4), &range));
    assert!(!below.pointer_access_in_wide_range(&field(4), 8, &range));
    // `i <= m` forms `&p[m]` but no field of it.
    let at_most = assume(
        bounded,
        ConditionTerm::uint64_less_equal(index.clone(), count.clone()),
    );
    assert!(at_most.position_in_wide_struct_array(&field(0), &range));
    assert!(!at_most.position_in_wide_struct_array(&field(4), &range));
    assert!(!at_most.pointer_access_in_wide_range(&field(4), 4, &range));
    // Without `m <= PTRDIFF_MAX / 8` nothing is placed.
    let unbounded = assume(
        PureFactContext::new(),
        ConditionTerm::uint64_less_than(index, count),
    );
    assert!(!unbounded.pointer_access_in_wide_range(&field(4), 4, &range));
    assert!(!unbounded.position_in_wide_struct_array(&field(4), &range));
    // A constant offset before the range is outside it.
    assert!(!below.pointer_access_in_wide_range(&at(PointerOffsetTerm::Constant(-2)), 4, &range));
}

#[test]
fn native_range_coverage_checks_complete_signed_observations() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(983_400));
    let index = MachineTerm::Variable(Variable(983_401));
    let next = MachineTerm::uint64_add(index.clone(), MachineTerm::uint64_constant(1));
    let available = MemoryRange::new_wide(base.clone(), index.clone(), next.clone(), 4);
    let narrow = MachineTerm::uint32_from_64(index.clone());
    let required = MemoryRange::new(
        base.clone(),
        narrow.clone(),
        MachineTerm::add(narrow.clone(), MachineTerm::constant(1)),
    );
    let bounded = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_less_than(index.clone(), MachineTerm::uint64_constant(3)),
        true,
    );
    let covers = crate::kernel::primitives::wide_memory_range_covers;
    let access_facts = bounded.clone().assume_condition(
        ConditionTerm::uint64_less_equal(
            next.clone(),
            MachineTerm::uint64_constant(i64::MAX as u64 / 4),
        ),
        true,
    );
    assert_eq!(
        crate::kernel::split_memory_range(&available, &required, &bounded),
        Some(Vec::new())
    );
    for (observation, wide) in [
        (narrow.clone(), false),
        (index.clone(), false),
        (index.clone(), true),
    ] {
        let selected = base.offset_by_typed_elements(observation, 4, wide, wide);
        assert!(access_facts.pointer_access_in_wide_range(&selected, 4, &available));
        assert!(!PureFactContext::new().pointer_access_in_wide_range(&selected, 4, &available));
    }
    assert!(covers(&available, &required, &bounded));
    assert!(!covers(&available, &required, &PureFactContext::new()));
    let low_only = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(narrow.clone(), MachineTerm::constant(3)),
        true,
    );
    assert!(!covers(&available, &required, &low_only));
    let signed_edge = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_equal(index.clone(), MachineTerm::uint64_constant(i32::MAX as u64)),
        true,
    );
    assert!(!covers(&available, &required, &signed_edge));
    let native_wrap = PureFactContext::new().assume_condition(
        ConditionTerm::uint64_equal(index.clone(), MachineTerm::uint64_constant(u64::MAX)),
        true,
    );
    assert!(!covers(&available, &required, &native_wrap));
    let too_long = MemoryRange::new(
        base.clone(),
        narrow.clone(),
        MachineTerm::add(narrow.clone(), MachineTerm::constant(2)),
    );
    assert!(!covers(&available, &too_long, &bounded));
    let wrong_base = MemoryRange::new(
        Pointer::symbolic(Variable(983_402)),
        narrow.clone(),
        MachineTerm::add(narrow, MachineTerm::constant(1)),
    );
    assert!(!covers(&available, &wrong_base, &bounded));
}

#[test]
fn native_owned_fragments_supply_indexed_writes() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer::symbolic(Variable(983_410));
    let range = |start, end| {
        MemoryRange::new_wide(
            base.clone(),
            MachineTerm::uint64_constant(start),
            MachineTerm::uint64_constant(end),
            4,
        )
    };
    let mut resources = ResourceContext::new();
    for (start, end) in [(0, 1), (2, 3), (1, 2)] {
        resources = resources.unchecked_with_fact(ResourceFact::own_memory(range(start, end)));
    }
    let facts = PureFactContext::new();
    for index in 0..3 {
        let pointer = base.offset_by_elements(MachineTerm::constant(index), 4);
        assert_eq!(
            resources.memory_write_range(&pointer, 4, &facts).cloned(),
            Some(range(index as u64, index as u64 + 1))
        );
    }
    for required in [
        range(0, 3),
        MemoryRange::new(base.clone(), 0u32.into(), 3u32.into()),
    ] {
        let remaining = resources
            .clone()
            .without_fact_incrementally(&ResourceFact::own_memory(required), &facts)
            .expect("all three owned fragments cover the complete request");
        assert!(remaining.facts().is_empty());
    }
    let outside = base.offset_by_elements(MachineTerm::constant(3), 4);
    assert!(resources.memory_write_range(&outside, 4, &facts).is_none());
    let viewed = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::View(Resource::Memory(range(0, 3))));
    assert!(viewed.memory_write_range(&base, 4, &facts).is_none());
}

#[test]
fn observable_projection_uses_current_loan_bindings_and_composite_eligibility() {
    let _session = crate::kernel::VerificationSession::enter();
    let context = context_with_one_loan_dependency(false);
    assert_eq!(
        context
            .observable_facts_assuming_valid(&PureFactContext::new())
            .len(),
        1,
        "a separately held owner and live borrow expose their composition"
    );
    let original = context.observable_composition();
    let (occurrence, binding) = context.live_loan_dependencies().next().unwrap();
    assert_eq!(original.loan_dependency(occurrence), Some(binding));
    let current = context
        .clone()
        .with_loan_dependency_state(ResourceContext::new().loan_dependency_state());
    let updated = current.observable_composition();
    assert!(std::sync::Arc::ptr_eq(&original.storage, &updated.storage));
    assert!(updated.loan_dependency(occurrence).is_none());
    assert_eq!(updated, current.observable_composition_uncached());
    assert_ne!(original, updated);
    assert!(
        current
            .observable_facts_assuming_valid(&PureFactContext::new())
            .is_empty(),
        "one owner alone does not expose a separation composition"
    );
    let composite = ResourceFact::own_composite("observable_box".into(), Vec::new());
    let context = ResourceContext::new().unchecked_with_fact(composite.clone());
    assert_eq!(
        context
            .observable_facts_assuming_valid(&PureFactContext::new())
            .len(),
        1
    );
    let context = context.without_exact_representation(&composite).unwrap();
    assert!(
        context
            .observable_facts_assuming_valid(&PureFactContext::new())
            .is_empty()
    );
}

#[test]
fn first_state_difference_names_the_resource_held_on_one_side() {
    let authority = ResourceFact::own_composite("authority".to_string(), Vec::new());
    let holding = ExecutionState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(authority.clone()));
    let empty = ExecutionState::new();
    assert_eq!(holding.first_difference(&holding.clone()), None);
    let before = holding.first_difference(&empty).unwrap();
    assert!(
        before.contains("owns authority(") && before.contains("only before"),
        "{before}"
    );
    let published = empty.first_difference(&holding).unwrap();
    assert!(
        published.contains("owns authority(") && published.contains("published state"),
        "{published}"
    );
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/resource_tests.rs");
}

fn canonical_cell(index: i64) -> ResourceFact {
    ResourceFact::own_memory(MemoryRange::new(
        Pointer {
            block: PointerBlock::Concrete(format!("object{index}")),
            offset: PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ))
}

#[test]
fn equal_resource_contexts_share_one_canonical_fact_set() {
    let facts = (0..16).map(canonical_cell).collect::<Vec<_>>();
    let forward = ResourceContext::new().unchecked_with_facts(facts.iter().cloned());
    let backward = ResourceContext::new().unchecked_with_facts(facts.iter().rev().cloned());
    assert!(
        forward
            .storage
            .index
            .canonical
            .shares_root_with(&backward.storage.index.canonical)
    );
    assert_eq!(forward, backward);
    // Taking a fact and giving it back restores the set, not a copy of it.
    let empty = PureFactContext::new();
    let taken = forward
        .clone()
        .without_fact_incrementally(&facts[3], &empty)
        .expect("the fact is held");
    assert!(
        !taken
            .storage
            .index
            .canonical
            .shares_root_with(&forward.storage.index.canonical)
    );
    let returned = taken.unchecked_with_fact(facts[3].clone());
    assert!(
        returned
            .storage
            .index
            .canonical
            .shares_root_with(&forward.storage.index.canonical)
    );
}

#[test]
fn comparing_equal_resource_contexts_walks_no_facts() {
    // Contexts holding the same facts are told equal by their canonical
    // fact sets' roots, whatever their size: no fact is visited.
    for size in [64, 1024] {
        let facts = (0..size).map(canonical_cell).collect::<Vec<_>>();
        let first = ResourceContext::new().unchecked_with_facts(facts.iter().cloned());
        let second = ResourceContext::new().unchecked_with_facts(facts.iter().rev().cloned());
        let before = crate::kernel::primitives::canonical_fact_set::canonical_fact_set_walks();
        assert_eq!(first.cmp(&second), std::cmp::Ordering::Equal);
        assert!(first == second);
        assert_eq!(
            crate::kernel::primitives::canonical_fact_set::canonical_fact_set_walks(),
            before,
            "size {size}"
        );
    }
}

#[test]
fn constant_owner_neighbors_ignore_empty_ranges_and_preserve_branches() {
    for origin in [None, Some(0), Some(1u64 << 63)] {
        let _session = crate::kernel::VerificationSession::enter();
        let assumptions = PureFactContext::new();
        let base = Pointer::symbolic(Variable(995_200));
        let range = |start: u64, end: u64| match origin {
            Some(origin) => MemoryRange::new_wide(
                base.clone(),
                MachineTerm::uint64_constant(origin + start),
                MachineTerm::uint64_constant(origin + end),
                4,
            ),
            None => MemoryRange::new(base.clone(), (start as u32).into(), (end as u32).into()),
        };
        let owner = ResourceFact::own_memory(range(0, 10));
        let empty = ResourceFact::own_memory(range(5, 5));
        let reversed = ResourceFact::own_memory(range(8, 7));
        let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_facts([
            owner.clone(),
            empty.clone(),
            reversed,
        ]);
        assert!(context.is_valid(&assumptions));
        let overlap = ResourceFact::own_memory(range(6, 9));
        assert!(
            !context
                .clone()
                .unchecked_with_fact(overlap.clone())
                .is_valid(&assumptions)
        );
        assert!(
            context
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [overlap.clone()],
                    &assumptions
                )
                .is_err()
        );
        let child = context
            .clone()
            .without_exact_representation(&owner)
            .unwrap()
            .without_exact_representation(&empty)
            .unwrap();
        assert!(
            child
                .try_compose_into_valid_context_delaying_normalization(
                    [overlap.clone()],
                    &assumptions
                )
                .is_ok()
        );
        assert!(
            context
                .clone()
                .try_compose_into_valid_context_delaying_normalization([overlap], &assumptions)
                .is_err()
        );
        assert!(
            context
                .try_compose_into_valid_context_delaying_normalization(
                    [ResourceFact::own_memory(range(6, 6))],
                    &assumptions
                )
                .is_ok()
        );
    }
}

#[test]
fn native_owner_neighbors_compare_exact_mixed_width_bytes() {
    let _session = crate::kernel::VerificationSession::enter();
    let assumptions = PureFactContext::new();
    let base = Pointer::symbolic(Variable(995_201));
    let owned = |start, end, width| {
        ResourceFact::own_memory(MemoryRange::new_wide(
            base.clone(),
            MachineTerm::uint64_constant(start),
            MachineTerm::uint64_constant(end),
            width,
        ))
    };
    // These byte coordinates exceed u64::MAX, but the range terms themselves
    // retain their unsigned element indices and must not be narrowed or wrapped.
    let start = 1u64 << 62;
    let owner = owned(start, start + 4, 4);
    let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(owner);
    let overlap = owned(start * 2 + 2, start * 2 + 3, 2);
    assert!(
        context
            .clone()
            .unchecked_with_fact(overlap.clone())
            .validity_error(&assumptions)
            .is_some()
    );
    assert!(
        context
            .clone()
            .try_compose_into_valid_context_delaying_normalization([overlap], &assumptions)
            .is_err()
    );
    assert!(
        context
            .try_compose_into_valid_context_delaying_normalization(
                [owned(start * 2 + 8, start * 2 + 9, 2)],
                &assumptions
            )
            .is_ok()
    );
    let limit = ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(owned(
        u64::MAX - 4,
        u64::MAX - 2,
        u32::MAX,
    ));
    assert!(
        limit
            .try_compose_into_valid_context_delaying_normalization(
                [owned(u64::MAX - 3, u64::MAX, u32::MAX)],
                &assumptions
            )
            .is_err()
    );
}

#[test]
fn translated_owner_coordinates_preserve_overlap_and_branch_isolation() {
    for native in [false, true] {
        let _session = crate::kernel::VerificationSession::enter();
        let assumptions = PureFactContext::new();
        let prefix = PointerOffsetTerm::Variable(Variable(995_400));
        let owned = |delta: i64, start: u32, end: u32, width: u32| {
            let base = Pointer {
                block: PointerBlock::Symbolic(Variable(995_401)),
                offset: PointerOffsetTerm::add(prefix.clone(), PointerOffsetTerm::Constant(delta)),
            };
            ResourceFact::own_memory(if native {
                MemoryRange::new_wide(
                    base,
                    MachineTerm::uint64_constant(start.into()),
                    MachineTerm::uint64_constant(end.into()),
                    width,
                )
            } else {
                MemoryRange::new_with_element_width(base, start.into(), end.into(), width)
            })
        };
        let first = owned(0, 0, 1, 4);
        let second = owned(8, 0, 1, 4);
        let empty = owned(2, 0, 0, 1);
        let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_facts([
            first.clone(),
            second,
            empty.clone(),
        ]);
        assert!(context.is_valid(&assumptions));
        // Different base/range spellings of the same bytes and a partial overlap
        // of different widths must fail both complete and incremental checks.
        for overlap in [owned(-4, 1, 2, 4), owned(2, 0, 1, 2), owned(4, 1, 2, 4)] {
            assert!(
                !context
                    .clone()
                    .unchecked_with_fact(overlap.clone())
                    .is_valid(&assumptions)
            );
            assert!(
                context
                    .clone()
                    .try_compose_into_valid_context_delaying_normalization([overlap], &assumptions)
                    .is_err()
            );
        }
        assert!(
            context
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [owned(4, 0, 1, 4)],
                    &assumptions
                )
                .is_ok()
        );
        let child = context
            .clone()
            .without_exact_representation(&first)
            .unwrap()
            .without_exact_representation(&empty)
            .unwrap();
        assert!(
            child
                .try_compose_into_valid_context_delaying_normalization(
                    [owned(-4, 1, 2, 4)],
                    &assumptions
                )
                .is_ok()
        );
        assert!(
            context
                .try_compose_into_valid_context_delaying_normalization(
                    [owned(-4, 1, 2, 4)],
                    &assumptions
                )
                .is_err()
        );
    }
}

#[test]
fn translated_owner_coordinates_keep_native_extent_and_symbolic_origin() {
    let _session = crate::kernel::VerificationSession::enter();
    let assumptions = PureFactContext::new();
    let owned = |variable, delta, start, end| {
        ResourceFact::own_memory(MemoryRange::new_wide(
            Pointer {
                block: PointerBlock::Symbolic(Variable(995_402)),
                offset: PointerOffsetTerm::add(
                    PointerOffsetTerm::Constant(delta),
                    PointerOffsetTerm::Variable(Variable(variable)),
                ),
            },
            MachineTerm::uint64_constant(start),
            MachineTerm::uint64_constant(end),
            4,
        ))
    };
    let start = 1u64 << 63;
    let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(owned(
        995_403,
        0,
        start,
        start + 1,
    ));
    let same_bytes = owned(995_403, -4, start + 1, start + 2);
    assert!(
        !context
            .clone()
            .unchecked_with_fact(same_bytes.clone())
            .is_valid(&assumptions)
    );
    assert!(
        context
            .clone()
            .try_compose_into_valid_context_delaying_normalization([same_bytes], &assumptions)
            .is_err()
    );
    // An unrelated symbolic origin is not the same address merely because
    // its block and constant displacement match.
    assert!(
        context
            .clone()
            .try_compose_into_valid_context_delaying_normalization(
                [owned(995_404, 0, start, start + 1)],
                &assumptions
            )
            .is_ok()
    );
    assert!(
        context
            .try_compose_into_valid_context_delaying_normalization(
                [owned(995_403, 4, start, start + 1)],
                &assumptions
            )
            .is_ok()
    );
}

#[test]
fn owned_root_neighbors_keep_alias_and_duplicate_refusals() {
    let _session = crate::kernel::VerificationSession::enter();
    let assumptions = PureFactContext::new();
    let pointer = |id| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::var(Variable(id)), 1),
    };
    let p = pointer(995_600);
    let q = pointer(995_601);
    let owned = |base, start: u32, end: u32| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base,
            start.into(),
            end.into(),
            4,
        ))
    };
    let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_facts([
        owned(p.clone(), 0, 1),
        owned(p.clone(), 2, 3),
        owned(q.clone(), 5, 6),
    ]);
    let required = owned(p.clone(), 5, 6);
    assert!(
        context
            .clone()
            .try_compose_into_valid_context_delaying_normalization([required.clone()], &assumptions)
            .is_ok()
    );
    assert!(
        context
            .clone()
            .try_compose_into_valid_context_delaying_normalization(
                [required.clone(), required.clone()],
                &assumptions
            )
            .is_err()
    );
    let aliases = assumptions
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(p, q), true);
    assert!(context.is_valid(&aliases));
    assert!(
        !context
            .clone()
            .unchecked_with_fact(required.clone())
            .is_valid(&aliases)
    );
    assert!(
        context
            .try_compose_into_valid_context_delaying_normalization([required], &aliases)
            .is_err()
    );
}

#[test]
fn owned_root_neighbors_require_complete_coordinate_coverage() {
    let _session = crate::kernel::VerificationSession::enter();
    let index = MachineTerm::var(Variable(995_620));
    let assumptions =
        PureFactContext::new().assume_proposition(equality(index.clone(), 5u32.into()));
    let pointer = |id| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::var(Variable(id)), 4),
    };
    let p = pointer(995_621);
    let q = pointer(995_622);
    let range = |base, start, end| MemoryRange::new_with_element_width(base, start, end, 4);
    let shifted = Pointer {
        block: p.block.clone(),
        offset: PointerOffsetTerm::add(
            p.offset.clone(),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        ),
    };
    for held in [
        ResourceFact::own_memory(range(
            p.clone(),
            index.clone(),
            MachineTerm::add(index.clone(), 1u32.into()),
        )),
        ResourceFact::own_memory(range(shifted, 0u32.into(), 1u32.into())),
    ] {
        let required = ResourceFact::own_memory(range(p.clone(), 5u32.into(), 6u32.into()));
        // Supply the two overlap inequalities explicitly: this regression
        // tests candidate retention, independently of arithmetic search.
        let available = held.memory_own_range().unwrap();
        let requested = required.memory_own_range().unwrap();
        let delta = requested
            .base()
            .element_index_from_base_with_width(available.base(), available.element_width())
            .expect("explicit relative index");
        let assumptions = assumptions
            .clone()
            .assume_condition(
                ConditionTerm::signed_less_than(
                    available.start().clone(),
                    MachineTerm::add(delta.clone(), requested.end().clone()),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(
                    MachineTerm::add(delta, requested.start().clone()),
                    available.end().clone(),
                ),
                true,
            );
        let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_facts([
            held.clone(),
            ResourceFact::own_memory(range(q.clone(), 0u32.into(), 1u32.into())),
        ]);
        assert!(context.is_valid(&assumptions));
        assert!(
            !context
                .clone()
                .unchecked_with_fact(required.clone())
                .is_valid(&assumptions)
        );
        assert!(
            context
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [required.clone()],
                    &assumptions
                )
                .is_err()
        );
        let child = context.clone().without_exact_representation(&held).unwrap();
        assert!(
            child
                .try_compose_into_valid_context_delaying_normalization(
                    [required.clone()],
                    &assumptions
                )
                .is_ok()
        );
        assert!(
            context
                .try_compose_into_valid_context_delaying_normalization([required], &assumptions)
                .is_err()
        );
    }
}

#[test]
fn exact_alias_owned_neighbors_preserve_translations_and_branch_isolation() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer::symbolic(Variable(995_650));
    let q = Pointer::symbolic(Variable(995_651));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true);
    let owned = |base, start: u32, end: u32| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base,
            start.into(),
            end.into(),
            4,
        ))
    };
    let translated = Pointer {
        block: q.block.clone(),
        offset: PointerOffsetTerm::add(q.offset.clone(), PointerOffsetTerm::Constant(8)),
    };
    let held = owned(translated, 0, 1);
    let context = ResourceContext::new_with_equalities(&assumptions)
        .unchecked_with_facts([held.clone(), owned(q.clone(), 5, 6)]);
    assert!(context.is_valid(&assumptions));
    for (start, end, accepted) in [(0, 2, true), (2, 3, false), (3, 5, true), (5, 6, false)] {
        assert_eq!(
            context
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [owned(p.clone(), start, end)],
                    &assumptions,
                )
                .is_ok(),
            accepted
        );
    }
    let child = context.clone().without_exact_representation(&held).unwrap();
    assert!(
        child
            .try_compose_into_valid_context_delaying_normalization(
                [owned(p.clone(), 2, 3)],
                &assumptions,
            )
            .is_ok()
    );
    assert!(
        context
            .try_compose_into_valid_context_delaying_normalization([owned(p, 2, 3)], &assumptions,)
            .is_err()
    );
}

#[test]
fn exact_alias_owned_neighbors_retain_symbolic_ranges() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer::symbolic(Variable(995_660));
    let q = Pointer::symbolic(Variable(995_661));
    let index = MachineTerm::var(Variable(995_662));
    let end = MachineTerm::add(index.clone(), 1u32.into());
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true)
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), 6u32.into()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(5u32.into(), end.clone()),
            true,
        );
    let owned = |base, start, end| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(base, start, end, 4))
    };
    let context = ResourceContext::new_with_equalities(&assumptions).unchecked_with_facts([
        owned(q.clone(), 0u32.into(), 1u32.into()),
        owned(q, index, end),
    ]);
    assert!(context.is_valid(&assumptions));
    assert!(
        context
            .try_compose_into_valid_context_delaying_normalization(
                [owned(p, 5u32.into(), 6u32.into())],
                &assumptions,
            )
            .is_err()
    );
}

#[test]
fn exact_alias_owned_neighbors_keep_nonzero_displacements() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = |id| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::var(Variable(id)), 4),
    };
    let p = pointer(995_670);
    let q = pointer(995_671);
    let displaced = Pointer {
        block: q.block.clone(),
        offset: PointerOffsetTerm::add(q.offset.clone(), PointerOffsetTerm::Constant(8)),
    };
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), displaced), true);
    let owned = |base, start: u32| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base,
            start.into(),
            (start + 1).into(),
            4,
        ))
    };
    let context = ResourceContext::new_with_equalities(&assumptions)
        .unchecked_with_facts((0..3).map(|i| owned(q.clone(), i)));
    assert!(context.is_valid(&assumptions));
    // p[0] is q[2], not q[0]. The owner at q[1] makes neighbours of
    // a query rebased to q instead of the exact alias q + 8 miss q[2].
    assert!(
        context
            .try_compose_into_valid_context_delaying_normalization([owned(p, 0)], &assumptions,)
            .is_err()
    );
}

#[test]
fn owner_only_base_buckets_follow_persistent_consumption_and_reinsertion() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer::symbolic(Variable(995_710));
    let q = Pointer::symbolic(Variable(995_711));
    let index = MachineTerm::var(Variable(995_712));
    let end = MachineTerm::add(index.clone(), 1u32.into());
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true)
        .assume_condition(
            ConditionTerm::signed_less_than(4u32.into(), end.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), 5u32.into()),
            true,
        );
    let held_range = MemoryRange::new_with_element_width(q, 4u32.into(), 5u32.into(), 4);
    let owner = ResourceFact::own_memory(held_range.clone());
    let view = ResourceFact::view_memory(held_range);
    let required = ResourceFact::own_memory(MemoryRange::new_with_element_width(p, index, end, 4));
    let parent = ResourceContext::new_with_equalities(&assumptions)
        .unchecked_with_facts([view.clone(), owner.clone()]);
    let refuses = |context: ResourceContext| {
        context
            .try_compose_into_valid_context_delaying_normalization([required.clone()], &assumptions)
            .is_err()
    };
    assert!(refuses(parent.clone()));
    let child = parent.clone().without_exact_representation(&owner).unwrap();
    assert!(child.contains_exact_representation(&view));
    assert!(!refuses(child.clone()));
    assert!(refuses(parent.clone()));
    let reinserted = child
        .clone()
        .try_compose_into_valid_context_delaying_normalization([owner], &assumptions)
        .unwrap();
    assert!(refuses(reinserted));
    assert!(!refuses(child));
    let without_view = parent.without_exact_representation(&view).unwrap();
    assert!(refuses(without_view));
}

#[test]
fn skipping_unowned_alias_blocks_keeps_local_and_cross_block_refusals() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer::symbolic(Variable(995_800));
    let q = Pointer::symbolic(Variable(995_801));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true);
    for native in [false, true] {
        let range = |base, start: u32| {
            if native {
                MemoryRange::new_wide(
                    base,
                    MachineTerm::uint64_constant(u64::from(start)),
                    MachineTerm::uint64_constant(u64::from(start + 1)),
                    4,
                )
            } else {
                MemoryRange::new_with_element_width(base, start.into(), (start + 1).into(), 4)
            }
        };
        let p_owner = ResourceFact::own_memory(range(p.clone(), 0));
        let q_owner = ResourceFact::own_memory(range(q.clone(), 0));
        let views = ResourceContext::new_with_equalities(&assumptions).unchecked_with_facts([
            ResourceFact::view_memory(range(p.clone(), 0)),
            ResourceFact::view_memory(range(q.clone(), 0)),
        ]);
        assert!(
            views
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [p_owner.clone()],
                    &assumptions,
                )
                .is_ok()
        );
        // Two owners introduced in the same batch still conflict across aliases.
        assert!(
            views
                .clone()
                .try_compose_into_valid_context_delaying_normalization(
                    [p_owner.clone(), q_owner.clone()],
                    &assumptions,
                )
                .is_err()
        );
        for held in [p_owner.clone(), q_owner.clone()] {
            let parent = views.clone().unchecked_with_fact(held.clone());
            assert!(
                parent
                    .clone()
                    .try_compose_into_valid_context_delaying_normalization(
                        [p_owner.clone()],
                        &assumptions,
                    )
                    .is_err()
            );
            // Adjacent cells remain admissible, whether the held owner is
            // local or in the explicitly aliased block.
            assert!(
                parent
                    .clone()
                    .try_compose_into_valid_context_delaying_normalization(
                        [ResourceFact::own_memory(range(p.clone(), 1))],
                        &assumptions,
                    )
                    .is_ok()
            );
            let child = parent.clone().without_exact_representation(&held).unwrap();
            assert!(
                child
                    .try_compose_into_valid_context_delaying_normalization(
                        [p_owner.clone()],
                        &assumptions,
                    )
                    .is_ok()
            );
            assert!(
                parent
                    .try_compose_into_valid_context_delaying_normalization(
                        [p_owner.clone()],
                        &assumptions,
                    )
                    .is_err()
            );
        }
    }
}

#[test]
fn direct_constant_overlap_keeps_byte_widths_translations_and_alias_refusals() {
    let _session = crate::kernel::VerificationSession::enter();
    let p = Pointer::symbolic(Variable(995_950));
    let q = Pointer::symbolic(Variable(995_951));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true);
    for native in [false, true] {
        let range = |base, start: u32, end: u32, width| {
            if native {
                MemoryRange::new_wide(
                    base,
                    MachineTerm::uint64_constant(u64::from(start)),
                    MachineTerm::uint64_constant(u64::from(end)),
                    width,
                )
            } else {
                MemoryRange::new_with_element_width(base, start.into(), end.into(), width)
            }
        };
        let held = range(p.clone(), 0, 1, 4);
        for (query, overlaps) in [
            (range(p.offset_by_bytes(2), 0, 1, 1), true),
            (range(p.offset_by_bytes(4), 0, 1, 1), false),
            (range(p.clone(), 0, 0, 4), false),
            (range(q.clone(), 0, 1, 4), true),
            (range(q.clone(), 1, 2, 4), false),
        ] {
            assert_eq!(
                memory_ranges_proven_overlapping(&held, &query, &assumptions),
                overlaps
            );
            assert_eq!(
                memory_ranges_proven_overlapping(&query, &held, &assumptions),
                overlaps
            );
            if overlaps {
                let stated_separate =
                    assumptions
                        .clone()
                        .assume_proposition(Proposition::ResourceSeparate {
                            left: Box::new(Resource::Memory(held.clone())),
                            right: Box::new(Resource::Memory(query.clone())),
                        });
                assert!(memory_ranges_proven_overlapping(
                    &held,
                    &query,
                    &stated_separate
                ));
            }
        }
    }
    // These byte coordinates exceed i64; they must not be narrowed before
    // comparing a partial overlap and an adjacent translated interval.
    let high = 1u64 << 63;
    let wide = |base| {
        MemoryRange::new_wide(
            base,
            MachineTerm::uint64_constant(high),
            MachineTerm::uint64_constant(high + 1),
            8,
        )
    };
    let held = wide(p.clone());
    for (displacement, overlaps) in [(4, true), (8, false)] {
        let query = wide(p.offset_by_bytes(displacement));
        assert_eq!(
            memory_ranges_proven_overlapping(&held, &query, &assumptions),
            overlaps
        );
        assert_eq!(
            memory_ranges_proven_overlapping(&query, &held, &assumptions),
            overlaps
        );
    }
}
