use super::prelude::*;

fn memory_range(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CMemoryRange {
    CMemoryRange::new(base, start.into(), end.into())
}

fn read_element(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CResourceFact {
    CResourceFact::view_memory(memory_range(base, start, end))
}

fn write_element(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> CResourceFact {
    CResourceFact::own_memory(memory_range(base, start, end))
}

fn read_context(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_fact(read_element(base, start, end))
}

fn write_context(
    base: Pointer,
    start: impl Into<Bitvector32Term>,
    end: impl Into<Bitvector32Term>,
) -> ResourceContext {
    ResourceContext::new().unchecked_with_fact(write_element(base, start, end))
}

fn assert_replayable_derivation(assumptions: &Assumptions, proposition: &Proposition) {
    let derivation = assumptions
        .derive_proposition(proposition)
        .expect("expected an explicit proposition derivation");
    assert_eq!(derivation.conclusion(), proposition);
    assert!(
        derivation.replay(assumptions),
        "explicit proposition derivation must replay"
    );
}

#[test]
fn proposition_derivation_honors_active_deadline() {
    let assumptions = Assumptions::new();
    let proposition = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    assert!(assumptions.derive_proposition(&proposition).is_some());
    assert!(
        assumptions
            .derive_atomic_proposition(&proposition)
            .is_some()
    );

    crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        assert!(assumptions.derive_proposition(&proposition).is_none());
        assert!(
            assumptions
                .derive_atomic_proposition(&proposition)
                .is_none()
        );
        assert!(!super::reasoning::with_memory_resolution_fuel(|| {
            super::reasoning::consume_memory_resolution_fuel()
        }));
        assert!(!super::reasoning::with_resource_prover_fuel(|| {
            super::reasoning::consume_resource_prover_fuel()
        }));
    });
}

#[test]
fn strict_reverse_order_derives_a_false_comparison() {
    let left = Bitvector32Term::Variable(Variable(200));
    let right = Bitvector32Term::Variable(Variable(201));
    let reverse = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(right.clone(), left.clone()),
        true,
    );
    let target = Proposition::ConditionIs(ConditionTerm::signed_less_than(left, right), false);
    let assumptions = Assumptions::new().assume_proposition(reverse.clone());
    let derivation = assumptions
        .derive_proposition(&target)
        .expect("a strict reverse order should prove the comparison false");
    assert_eq!(derivation.context_premises(), vec![reverse]);
    assert!(derivation.replay(&assumptions));
    assert!(
        assumptions
            .clone()
            .defer_non_exact_loadability_obligations()
            .derive_proposition(&target)
            .is_some(),
        "proof construction remains available when symbolic execution defers search"
    );
}

#[test]
fn signed_less_equal_and_inequality_derive_strict_order() {
    let left = Bitvector32Term::Variable(Variable(9_004));
    let right = Bitvector32Term::Variable(Variable(9_005));
    let less_equal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(left.clone(), right.clone()),
        true,
    );
    let unequal =
        Proposition::ConditionIs(ConditionTerm::equal(left.clone(), right.clone()), false);
    let strict = Proposition::ConditionIs(ConditionTerm::signed_less_than(left, right), true);
    let assumptions = Assumptions::new()
        .assume_proposition(less_equal)
        .assume_proposition(unequal);

    assert_replayable_derivation(&assumptions, &strict);
}

#[test]
fn condition_search_skips_irrelevant_implication_antecedents() {
    let target_condition = ConditionTerm::signed_less_than(
        Bitvector32Term::Variable(Variable(9_001)),
        Bitvector32Term::Variable(Variable(9_002)),
    );
    let unrelated_condition = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(9_003)),
        Bitvector32Term::Variable(Variable(9_004)),
    );
    let true_fact = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::Implies(
            Box::new(true_fact.clone()),
            Box::new(Proposition::ConditionIs(unrelated_condition, true)),
        ))
        .assume_proposition(Proposition::Implies(
            Box::new(true_fact),
            Box::new(Proposition::ConditionIs(target_condition.clone(), true)),
        ));

    Assumptions::reset_condition_implication_antecedent_checks();
    assert!(assumptions.proves(&Proposition::ConditionIs(target_condition, true)));
    assert_eq!(
        Assumptions::condition_implication_antecedent_checks(),
        1,
        "only an implication whose conclusion can establish the target should inspect its antecedent"
    );
}

#[test]
fn merging_required_obligations_preserves_the_certification_frontier() {
    let value = Bitvector32Term::Variable(Variable(9_010));
    let assumptions = Assumptions::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::equal(value.clone(), Bitvector32Term::Constant(1)),
        true,
    ));
    let derived = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), value),
        true,
    );
    assert!(assumptions.proves(&derived));

    let required = ProofObligation::verification_condition(derived.clone());
    let merged = merge_obligations(&[], &[required], &assumptions)
        .expect("required verification conditions should compose");
    assert_eq!(merged.len(), 1);
    assert_eq!(merged[0].proposition(), &derived);
}

#[test]
fn condition_fact_matching_ignores_unrelated_local_memory() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(100_000)), 4),
    };
    let owner_field = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::add(owner.offset.clone(), PointerOffsetTerm::Constant(4)),
    };
    let ignored_local = Pointer {
        block: "local:ignored".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let empty_memory = CMemory::new();
    let old_memory = empty_memory.clone().store(
        owner.clone(),
        int32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(empty_memory),
            Box::new(owner),
        )),
    );
    let before_local = CMemory::new()
        .with_block("call-havoc:8000000", 0)
        .with_block("local:ignored", 4);
    let after_local = before_local
        .clone()
        .with_block("local:ignored", 4)
        .store(ignored_local, int32(Bitvector32Term::Variable(Variable(1))));
    let old_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(old_memory),
        Box::new(owner_field.clone()),
    );
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before_local),
                Box::new(owner_field.clone()),
            ),
            old_load.clone(),
        ),
        true,
    );
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after_local),
                Box::new(owner_field),
            ),
            old_load,
        ),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(fact);

    assert_replayable_derivation(&assumptions, &target);
}

#[test]
fn bounded_order_replay_ignores_unrelated_local_memory() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(100_001)), 4),
    };
    let position = owner.clone();
    let length = owner.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let local = CMemory::local_pointer("temporary");
    let fact_memory = CMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block(local.block.clone(), 4)
        .store(local, int32(7));
    let target_memory = CMemory::new().with_block("call-havoc:0", 0);
    let symbolic_length = Bitvector32Term::Variable(Variable(100_002));
    let load = |memory: &CMemory, pointer: &Pointer| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory.clone()),
            Box::new(pointer.clone()),
        )
    };
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::equal(load(&fact_memory, &position), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(load(&fact_memory, &length), symbolic_length.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), symbolic_length),
            true,
        );
    let target = ConditionTerm::signed_less_than(
        load(&target_memory, &position),
        load(&target_memory, &length),
    );

    assert!(assumptions.proves_order_condition_for_memory_resolution(&target, true));
}

#[test]
fn equality_chains_across_observationally_equivalent_memory_loads() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(100_000)), 4),
    };
    let observed = CMemory::local_pointer("observed");
    let before_materialized = CMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block("call-havoc:1", 0)
        .with_block(observed.block.clone(), 4)
        .store(observed, int32(Bitvector32Term::Variable(Variable(10))));
    let before_sparse = CMemory::new()
        .with_block("call-havoc:0", 0)
        .with_block("call-havoc:1", 0);
    let after = before_sparse.clone().with_block("call-havoc:3", 0);
    let before_materialized_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before_materialized),
        Box::new(owner.clone()),
    );
    let before_sparse_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before_sparse),
        Box::new(owner.clone()),
    );
    let after_load =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(owner));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::equal(before_materialized_load, Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(after_load.clone(), before_sparse_load),
            true,
        );
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(after_load, Bitvector32Term::Constant(1)),
        true,
    );

    assert_replayable_derivation(&assumptions, &target);
}

#[test]
fn proposition_derivation_proves_implication_from_false_antecedent() {
    let condition = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(1)),
        Bitvector32Term::Constant(0),
    );
    let antecedent = Proposition::ConditionIs(condition.clone(), false);
    let conclusion = Proposition::Implies(
        Box::new(antecedent),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(2)),
                Bitvector32Term::Variable(Variable(3)),
            ),
            true,
        )),
    );
    let assumptions = Assumptions::new().assume_condition(condition, true);

    let derivation = assumptions
        .derive_simp_proposition(&conclusion)
        .expect("a false antecedent should prove an implication");
    assert!(derivation.replay(&assumptions));
}

#[test]
fn bitwise_xor_normalizes_swap_identities() {
    let x = Bitvector32Term::Variable(Variable(1));
    let y = Bitvector32Term::Variable(Variable(2));
    let x_xor_y = Bitvector32Term::bitwise_xor(x.clone(), y.clone());
    let recovered_x = Bitvector32Term::bitwise_xor(y.clone(), x_xor_y.clone());
    let recovered_y = Bitvector32Term::bitwise_xor(x_xor_y, x.clone());

    assert_eq!(recovered_x, x);
    assert_eq!(recovered_y, y);
}

#[test]
fn join_state_forgets_changed_scalars_and_memory() {
    let stable_x = int32(Bitvector32Term::Variable(Variable(7)));
    let pointer = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state_zero = CState::new()
        .with_local("x", stable_x.clone())
        .with_local("y", int32(0))
        .with_memory(
            CMemory::new()
                .with_block("heap", 4)
                .store(pointer.clone(), int32(0)),
        )
        .with_resource_context(write_context(pointer.clone(), 0, 1));
    let state_one = CState::new()
        .with_local("x", stable_x.clone())
        .with_local("y", int32(1))
        .with_memory(
            CMemory::new()
                .with_block("heap", 4)
                .store(pointer, int32(1)),
        );
    let stable = BTreeMap::from([("x".to_string(), stable_x.clone())]);

    let abstract_zero = abstract_c_state_for_join(&state_zero, &stable).expect("join abstraction");
    let abstract_one = abstract_c_state_for_join(&state_one, &stable).expect("join abstraction");

    assert_eq!(abstract_zero, abstract_one);
    assert_eq!(abstract_zero.locals().get("x"), Some(&stable_x));
    assert_ne!(abstract_zero.locals().get("y"), Some(&int32(0)));
    assert!(abstract_zero.resources().is_empty());
}

#[test]
fn join_state_abstracts_changed_pointer_locals() {
    let left = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let abstract_left = abstract_c_state_for_join(
        &CState::new().with_local("selected", CValue::Pointer(left)),
        &BTreeMap::new(),
    )
    .expect("pointer join abstraction");
    let abstract_right = abstract_c_state_for_join(
        &CState::new().with_local("selected", CValue::Pointer(right)),
        &BTreeMap::new(),
    )
    .expect("pointer join abstraction");

    assert_eq!(abstract_left, abstract_right);
    let Some(CValue::Pointer(selected)) = abstract_left.locals().get("selected") else {
        panic!("selected should remain a pointer local");
    };
    assert!(selected.has_symbolic_block());
}

#[test]
fn join_state_fresh_variables_do_not_collide_with_symbolic_pointer_blocks() {
    let state = CState::new().with_local(
        "selected",
        CValue::Pointer(Pointer::symbolic(Variable(1_000_000))),
    );
    let abstract_state =
        abstract_c_state_for_join(&state, &BTreeMap::new()).expect("pointer join abstraction");
    let Some(CValue::Pointer(selected)) = abstract_state.locals().get("selected") else {
        panic!("selected should remain a pointer local");
    };

    assert_eq!(selected.block, PointerBlock::Symbolic(Variable(1_000_001)));
}

#[test]
fn symbolic_pointer_blocks_do_not_imply_non_aliasing() {
    let symbolic = Pointer::symbolic(Variable(21_000));
    let concrete = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };

    assert!(!pointers_proven_distinct(
        &symbolic,
        &concrete,
        &Assumptions::new()
    ));
    assert_eq!(
        Assumptions::new().decide(&ConditionTerm::pointer_equal(symbolic, concrete)),
        None
    );
}

#[test]
fn concrete_pointer_block_names_cannot_create_symbolic_identity() {
    let misleading_name = Pointer {
        block: "symbolic-pointer:21000".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let heap = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };

    assert!(!misleading_name.has_symbolic_block());
    assert!(misleading_name.blocks_proven_distinct(&heap));
}

#[test]
fn resource_family_cores_are_view_facts() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };

    assert_eq!(
        read_element(base.clone(), 0, 1).core(),
        Some(read_element(base.clone(), 0, 1))
    );
    assert_eq!(
        write_element(base.clone(), 0, 1).core(),
        Some(read_element(base, 0, 1))
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
fn exact_resource_families_reject_duplicate_owned_facts() {
    for fact in [
        CResourceFact::own_token("token".to_string(), vec![int32(0)]),
        CResourceFact::own_composite("box".to_string(), vec![int32(1)]),
    ] {
        let error = ResourceContext::new()
            .try_compose_with_facts([fact.clone(), fact.clone()], &Assumptions::new())
            .expect_err("duplicate exact owned resources must be invalid");
        assert_eq!(
            error,
            ResourceContextValidityError::DuplicateOwnedResourceFact(fact)
        );
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
            .without_fact(&viewed, &Assumptions::new())
            .expect("owned exact resource should satisfy its view");
        assert_eq!(after_view.facts(), &[owned]);
    }
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

    assert!(!context.satisfies_fact(&required, &Assumptions::new()));
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
        .without_facts(&required, &Assumptions::new())
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
        .without_facts(&required, &Assumptions::new())
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
        .observable_facts(&Assumptions::new())
        .expect("adjacent writes should be a valid resource context");

    assert_eq!(
        facts,
        vec![Proposition::CResourceSeparate {
            left: CResource::Memory(left),
            right: CResource::Memory(right),
        }]
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
        arguments: vec![],
    };
    let other_token = CResource::Token {
        name: "right".to_string(),
        arguments: vec![],
    };
    let facts = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::Own(memory.clone()))
        .unchecked_with_fact(CResourceFact::Own(token.clone()))
        .unchecked_with_fact(CResourceFact::Own(other_token.clone()))
        .observable_facts(&Assumptions::new())
        .expect("distinct owned resources should compose validly");

    assert!(facts.contains(&Proposition::CResourceSeparate {
        left: token.clone(),
        right: other_token,
    }));
    assert!(facts.contains(&Proposition::CResourceSeparate {
        left: memory,
        right: token,
    }));
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
    let left = CResourceFact::Own(CResource::Composite {
        name: "list".to_string(),
        arguments: vec![CValue::Pointer(left_pointer.clone())],
    });
    let right = CResourceFact::Own(CResource::Composite {
        name: "list".to_string(),
        arguments: vec![CValue::Pointer(right_pointer.clone())],
    });
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::pointer_equal(left_pointer, right_pointer),
        true,
    );

    let remaining = ResourceContext::new()
        .unchecked_with_fact(left.clone())
        .without_fact(&right, &assumptions)
        .expect("equal resource arguments should identify the same owned fact");
    assert!(remaining.is_empty());

    assert!(matches!(
        ResourceContext::new()
            .unchecked_with_fact(left)
            .try_compose_with_fact(right, &assumptions),
        Err(ResourceContextValidityError::DuplicateOwnedResourceFact(_))
    ));
}

#[test]
fn resource_separation_proves_memory_disjointness() {
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left = memory_range(base.clone(), 0, 1);
    let right = memory_range(base.clone(), 1, 2);
    let assumptions = Assumptions::new().assume_proposition(Proposition::CResourceSeparate {
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
    let assumptions = Assumptions::new()
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
    let assumptions = Assumptions::new()
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
        arguments: vec![],
    };
    let child = CResource::Memory(memory_range(base.clone(), 0, 1));
    let other = CResource::Memory(memory_range(base.clone(), 1, 2));
    let assumptions = Assumptions::new()
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
                write_element(base.clone(), 0, 1),
                write_element(base.clone(), 0, 1),
            ],
            &Assumptions::new(),
        )
        .expect_err("duplicate writes must be rejected before normalization");

    assert_eq!(
        error,
        ResourceContextValidityError::OverlappingWriteResources {
            left: memory_range(base.clone(), 0, 1),
            right: memory_range(base, 0, 1),
        }
    );
}

#[test]
fn concrete_max_executes_without_list_encoding() {
    let state = c_max_state(int32(0), int32(1));
    let theorem =
        prove_c_statement_execution(state.clone(), c_max_body()).expect("max should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement: c_max_body(),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state,
            },
        }
    );
}

#[test]
fn concrete_max_function_call_preserves_caller_locals() {
    let state = CState::new().with_local("caller", int32(99));
    let function = c_max_function();
    let arguments = vec![c_int32_literal(0), c_int32_literal(1)];
    let theorem = prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Assumptions::new(),
    )
    .expect("max function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state: state.clone(),
            function,
            arguments,
            outcome: CFunctionOutcome::Return {
                value: int32(1),
                state,
            },
        }
    );
}

#[test]
fn symbolic_max_function_call_reports_branch_facts() {
    let a = Variable(14);
    let b = Variable(15);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = CState::new();
    let function = c_max_function();
    let arguments = vec![
        CExpression::Value(int32(a_bits.clone())),
        CExpression::Value(int32(b_bits.clone())),
    ];
    let execution = prove_symbolic_c_function_execution_paths(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Assumptions::new(),
    );

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(condition.clone(), true)]
    );
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition.clone(), true)),
            Box::new(Proposition::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                arguments: arguments.clone(),
                outcome: CFunctionOutcome::Return {
                    value: int32(b_bits),
                    state: state.clone(),
                },
            }),
        )
    );

    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(condition.clone(), false)]
    );
    assert_eq!(
        execution.paths()[1].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[1].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition, false)),
            Box::new(Proposition::CFunctionExecutes {
                state: state.clone(),
                function,
                arguments,
                outcome: CFunctionOutcome::Return {
                    value: int32(a_bits),
                    state,
                },
            }),
        )
    );
}

#[test]
fn function_call_threads_memory_but_discards_callee_locals() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new()
        .with_local("caller", int32(42))
        .with_resource_context(resources.clone());
    let function = c_function(
        CType::Int32,
        "store_and_load",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_seq(
            c_store(c_variable("p"), c_int32_literal(9)),
            c_return(c_load(c_variable("p"))),
        ),
    );
    let arguments = vec![c_pointer_value(pointer.clone())];
    let final_state = CState::new()
        .with_local("caller", int32(42))
        .with_memory(CMemory::new().store(pointer.clone(), int32(9)))
        .with_resource_context(resources);
    let theorem = prove_symbolic_c_function_execution(
        state.clone(),
        function.clone(),
        arguments.clone(),
        Assumptions::new(),
    )
    .expect("store/load function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state,
            function,
            arguments,
            outcome: CFunctionOutcome::Return {
                value: int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn function_call_does_not_inherit_undeclared_resources() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new().with_resource_context(resources);
    let helper = c_function(
        CType::Int32,
        "store_and_load",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_seq(
            c_store(c_variable("p"), c_int32_literal(9)),
            c_return(c_load(c_variable("p"))),
        ),
    );
    let caller = c_function(
        CType::Int32,
        "caller",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_call_assign("result", "store_and_load", vec![c_variable("p")]),
    );
    let arguments = vec![c_pointer_value(pointer.clone())];
    let theorem = prove_symbolic_c_function_execution_with_environment(
        state.clone(),
        caller.clone(),
        arguments.clone(),
        Assumptions::new(),
        CExecutionEnvironment::new().with_function(helper),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("call should report missing callee permission");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionExecutes {
            state,
            function: caller,
            arguments,
            outcome: CFunctionOutcome::RuntimeError(CRuntimeError::MissingResource {
                resource: write_element(pointer, 0, 1),
            }),
        }
    );
}

#[test]
fn concrete_function_specification_is_native_theorem() {
    let function = c_max_function();
    let specification = c_function_specification(
        CState::new(),
        vec![c_int32_literal(0), c_int32_literal(1)],
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(1),
            state: CState::new(),
        },
    );
    let theorem = prove_c_function_satisfies_specification(
        function.clone(),
        specification.clone(),
        Assumptions::new(),
    )
    .expect("concrete max specification should prove");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CFunctionSatisfiesSpecification {
            function,
            specification
        }
    );
}

#[test]
fn symbolic_function_specification_uses_requirements_as_execution_pure_facts() {
    let a = Variable(16);
    let b = Variable(17);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let function = c_max_function();
    let specification = c_function_specification(
        CState::new(),
        vec![
            CExpression::Value(int32(a_bits)),
            CExpression::Value(int32(b_bits)),
        ],
        vec![Proposition::ConditionIs(condition.clone(), true)],
        CFunctionOutcome::Return {
            value: int32(Bitvector32Term::Variable(b)),
            state: CState::new(),
        },
    );
    let theorem = prove_c_function_satisfies_specification(
        function.clone(),
        specification.clone(),
        Assumptions::new(),
    )
    .expect("symbolic branch specification should prove under condition");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition, true)),
            Box::new(Proposition::CFunctionSatisfiesSpecification {
                function,
                specification
            }),
        )
    );
}

#[test]
fn symbolic_max_branch_specifications_include_bounds() {
    let a = Variable(60);
    let b = Variable(61);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let function = c_max_function();
    let arguments = vec![
        CExpression::Value(int32(a_bits.clone())),
        CExpression::Value(int32(b_bits.clone())),
    ];
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());

    let right_specification = c_function_specification(
        CState::new(),
        arguments.clone(),
        vec![Proposition::ConditionIs(condition.clone(), true)],
        CFunctionOutcome::Return {
            value: int32(b_bits.clone()),
            state: CState::new(),
        },
    );
    prove_c_function_satisfies_specification_and_propositions(
        function.clone(),
        right_specification,
        Assumptions::new(),
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(b_bits.clone(), a_bits.clone()),
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(b_bits.clone(), b_bits.clone()),
                true,
            ),
        ],
    )
    .expect("under a < b, max returns b and b is >= both inputs");

    let left_specification = c_function_specification(
        CState::new(),
        arguments,
        vec![Proposition::ConditionIs(condition, false)],
        CFunctionOutcome::Return {
            value: int32(a_bits.clone()),
            state: CState::new(),
        },
    );
    prove_c_function_satisfies_specification_and_propositions(
        function,
        left_specification,
        Assumptions::new(),
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(a_bits.clone(), a_bits.clone()),
                true,
            ),
            Proposition::ConditionIs(ConditionTerm::signed_greater_equal(a_bits, b_bits), true),
        ],
    )
    .expect("under not (a < b), max returns a and a is >= both inputs");
}

#[test]
fn symbolic_clamp_branch_specifications_include_bounds_under_ordered_limits() {
    let x = Variable(62);
    let lo = Variable(63);
    let hi = Variable(64);
    let x_bits = Bitvector32Term::Variable(x);
    let lo_bits = Bitvector32Term::Variable(lo);
    let hi_bits = Bitvector32Term::Variable(hi);
    let ordered_limits = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(lo_bits.clone(), hi_bits.clone()),
        true,
    );
    let below_lo = ConditionTerm::signed_less_than(x_bits.clone(), lo_bits.clone());
    let above_hi = ConditionTerm::signed_greater_than(x_bits.clone(), hi_bits.clone());
    let function = c_function(
        CType::Int32,
        "clamp",
        vec![
            c_parameter("x", CType::Int32),
            c_parameter("lo", CType::Int32),
            c_parameter("hi", CType::Int32),
        ],
        c_if(
            c_less_than(c_variable("x"), c_variable("lo")),
            c_return(c_variable("lo")),
            c_if(
                c_greater_than(c_variable("x"), c_variable("hi")),
                c_return(c_variable("hi")),
                c_return(c_variable("x")),
            ),
        ),
    );
    let arguments = vec![
        CExpression::Value(int32(x_bits.clone())),
        CExpression::Value(int32(lo_bits.clone())),
        CExpression::Value(int32(hi_bits.clone())),
    ];

    for (requires, result, message) in [
        (
            vec![
                ordered_limits.clone(),
                Proposition::ConditionIs(below_lo.clone(), true),
            ],
            lo_bits.clone(),
            "x below lo returns lo within bounds",
        ),
        (
            vec![
                ordered_limits.clone(),
                Proposition::ConditionIs(below_lo.clone(), false),
                Proposition::ConditionIs(above_hi.clone(), true),
            ],
            hi_bits.clone(),
            "x above hi returns hi within bounds",
        ),
        (
            vec![
                ordered_limits.clone(),
                Proposition::ConditionIs(below_lo.clone(), false),
                Proposition::ConditionIs(above_hi.clone(), false),
            ],
            x_bits.clone(),
            "x already in range returns x within bounds",
        ),
    ] {
        let specification = c_function_specification(
            CState::new(),
            arguments.clone(),
            requires,
            CFunctionOutcome::Return {
                value: int32(result.clone()),
                state: CState::new(),
            },
        );
        prove_c_function_satisfies_specification_and_propositions(
            function.clone(),
            specification,
            Assumptions::new(),
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(result.clone(), lo_bits.clone()),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(result, hi_bits.clone()),
                    true,
                ),
            ],
        )
        .expect(message);
    }
}

#[test]
fn incomplete_symbolic_function_specification_does_not_prove() {
    let a = Variable(18);
    let b = Variable(19);
    let function = c_max_function();
    let specification = c_function_specification(
        CState::new(),
        vec![
            CExpression::Value(int32(Bitvector32Term::Variable(a))),
            CExpression::Value(int32(Bitvector32Term::Variable(b))),
        ],
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(Bitvector32Term::Variable(b)),
            state: CState::new(),
        },
    );

    assert!(
        prove_c_function_satisfies_specification(function, specification, Assumptions::new())
            .is_none()
    );
}

#[test]
fn call_assign_uses_function_environment() {
    let increment = c_function(
        CType::Int32,
        "increment",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_add(c_variable("x"), c_int32_literal(1))),
    );
    let environment = CExecutionEnvironment::new().with_function(increment);
    let state = CState::new();
    let statement = c_seq(
        c_call_assign("result", "increment", vec![c_int32_literal(41)]),
        c_return(c_variable("result")),
    );
    let final_state = CState::new().with_local("result", int32(42));
    let theorem = prove_symbolic_c_execution_with_environment(
        state.clone(),
        statement.clone(),
        Assumptions::new(),
        environment,
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("known function call should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(42),
                state: final_state,
            },
        }
    );
}

#[test]
fn loop_semantics_explicitly_select_verification_or_verified_rules() {
    let state = CState::new().with_local("i", int32(0));
    let statement = c_while_with_invariant_checks(
        c_less_than(c_variable("i"), c_int32_literal(1)),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("i")),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        c_assign("i", c_add(c_variable("i"), c_int32_literal(1))),
    );
    let assumptions = Assumptions::new();
    let (certified, loop_rule) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
            state.clone(),
            statement.clone(),
            assumptions.clone(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::EXECUTE_BODIES,
        );
    let loop_rule = loop_rule.expect("loop verification should produce a rule");
    assert!(certified.paths().iter().all(|path| {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        matches!(proposition, Proposition::CStatementVerifies { .. })
    }));

    let missing = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(missing.paths().is_empty());

    let mut ignored_rule = loop_rule.clone();
    ignored_rule.paths.clear();
    let verified_directly = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        CExecutionEnvironment::new().with_verified_loop_rules([ignored_rule]),
        CExecutionSemantics::EXECUTE_BODIES,
    );
    assert!(!verified_directly.paths().is_empty());

    let reused = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions
            .clone()
            .assume_condition(ConditionTerm::Constant(true), true),
        CExecutionEnvironment::new().with_verified_loop_rules([loop_rule.clone()]),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert_eq!(reused.paths().len(), certified.paths().len());
    assert!(reused.paths().iter().all(|path| {
        let mut proposition = path.theorem().proposition();
        while let Proposition::Implies(_, body) = proposition {
            proposition = body;
        }
        matches!(proposition, Proposition::CStatementVerifies { .. })
    }));

    let mismatched = prove_symbolic_c_statement_verification_paths_with_environment(
        state.with_local("unrelated", int32(0)),
        statement,
        assumptions,
        CExecutionEnvironment::new().with_verified_loop_rules([loop_rule]),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    assert!(mismatched.paths().is_empty());
}

#[test]
fn perpetual_loop_verifies_safety_without_minting_a_concrete_exit() {
    let state = CState::new();
    let statement = c_while_with_invariant_checks(
        c_int32_literal(1),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(0)),
            },
            Some("perpetual loop entry".to_string()),
            Some("perpetual loop preservation".to_string()),
        )],
        c_skip(),
    );
    let (verification, rule) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
            state.clone(),
            statement.clone(),
            Assumptions::new(),
            CExecutionEnvironment::new(),
            CExecutionSemantics::EXECUTE_BODIES,
        );
    assert!(rule.is_some());
    assert_eq!(verification.paths().len(), 1);
    let mut proposition = verification.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        Proposition::CStatementVerifies {
            outcome: CStatementOutcome::VerificationDiverges,
            ..
        }
    ));

    let concrete = prove_symbolic_c_execution_paths(state, statement, Assumptions::new());
    assert!(concrete.paths().is_empty());
    assert!(concrete.limit().is_some());
}

#[test]
fn loop_exit_rule_with_proven_preservation_does_not_reverify_the_body() {
    let state = CState::new().with_local("i", int32(0));
    let statement = c_while_with_invariant_checks(
        c_less_than(c_variable("i"), c_int32_literal(1)),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("i")),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        c_assign("i", c_int32_literal(u32::MAX)),
    );
    let assumptions = Assumptions::new();
    let automatic = prove_symbolic_c_statement_verification_paths_with_environment(
        state.clone(),
        statement.clone(),
        assumptions.clone(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    );
    assert!(
        automatic
            .paths()
            .iter()
            .flat_map(SymbolicCExecutionPath::obligations)
            .any(|obligation| obligation.context() == Some("loop preservation"))
    );

    let (after_proof, loop_rule) = prove_symbolic_c_loop_exit_with_proven_phases(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        false,
        true,
    );
    assert!(loop_rule.is_some());
    assert!(after_proof.paths().iter().all(|path| {
        path.obligations()
            .iter()
            .all(|obligation| obligation.context() != Some("loop preservation"))
    }));
}

#[test]
fn loop_exit_with_unproven_preservation_does_not_produce_rule() {
    let state = CState::new().with_local("i", int32(u32::MAX));
    let statement = c_while_with_invariant_checks(
        c_int32_literal(1),
        Vec::new(),
        vec![CLoopInvariantCheck::new(
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::LessEqual,
                right: SpecExpression::CExpression(c_variable("i")),
            },
            Some("loop entry".to_string()),
            Some("loop preservation".to_string()),
        )],
        c_assign("i", c_int32_literal(u32::MAX)),
    );
    let (execution, loop_rule) = prove_symbolic_c_loop_exit_with_proven_phases(
        state,
        statement,
        Assumptions::new(),
        CExecutionEnvironment::new(),
        true,
        false,
    );

    assert!(loop_rule.is_none());
    let obligations = execution
        .paths()
        .iter()
        .flat_map(SymbolicCExecutionPath::obligations)
        .collect::<Vec<_>>();
    assert!(
        obligations
            .iter()
            .all(|obligation| obligation.context() != Some("loop entry"))
    );
    assert!(
        obligations
            .iter()
            .any(|obligation| obligation.context() == Some("loop preservation"))
    );
}

#[test]
fn unknown_call_assign_is_runtime_error() {
    let state = CState::new();
    let statement = c_call_assign("result", "missing", Vec::new());
    let theorem = prove_symbolic_c_execution_with_environment(
        state.clone(),
        statement.clone(),
        Assumptions::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
    .expect("unknown function should produce a single runtime-error path");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnknownFunction(
                "missing".to_string(),
            )),
        }
    );
}

#[test]
fn while_loop_executes_concrete_countdown() {
    let state = CState::new().with_local("x", int32(3));
    let loop_statement = c_while(
        c_greater_than(c_variable("x"), c_int32_literal(0)),
        Vec::new(),
        c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
    );
    let statement = c_seq(loop_statement, c_return(c_variable("x")));
    let final_state = CState::new().with_local("x", int32(0));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("concrete countdown loop should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state: final_state,
            },
        }
    );
}

#[test]
fn loop_budget_exhaustion_is_executor_failure_not_c_runtime_error() {
    let state = CState::new().with_local("x", int32(0));
    let statement = c_while(
        c_int32_literal(1),
        Vec::new(),
        c_assign("x", c_variable("x")),
    );
    let budget = ExecutionBudget::new().with_loop_unrolls(2);
    let execution = prove_symbolic_c_execution_paths_with_budget(
        state.clone(),
        statement.clone(),
        Assumptions::new(),
        budget.clone(),
    );

    assert_eq!(execution.limit(), Some(ExecutionLimit::LoopUnrolls));
    assert_eq!(execution.paths(), &[] as &[SymbolicCExecutionPath]);
    assert!(
        prove_symbolic_c_execution_with_budget(state, statement, Assumptions::new(), budget,)
            .is_none()
    );
}

#[test]
fn executor_budgets_cap_steps_calls_and_paths() {
    let state = CState::new();
    let statement = c_return(c_int32_literal(1));

    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
            state.clone(),
            statement.clone(),
            Assumptions::new(),
            ExecutionBudget::new().with_statement_steps(0),
        )
        .limit(),
        Some(ExecutionLimit::StatementSteps)
    );
    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
            state.clone(),
            statement,
            Assumptions::new(),
            ExecutionBudget::new().with_expression_steps(0),
        )
        .limit(),
        Some(ExecutionLimit::ExpressionSteps)
    );

    let function = c_function(
        CType::Int32,
        "id",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_variable("x")),
    );
    assert_eq!(
        prove_symbolic_c_function_execution_paths_with_budget(
            CState::new(),
            function,
            vec![c_int32_literal(1)],
            Assumptions::new(),
            ExecutionBudget::new().with_function_calls(0),
        )
        .limit(),
        Some(ExecutionLimit::FunctionCalls)
    );

    let a = Variable(75);
    let b = Variable(76);
    let branchy_statement = c_return(c_less_than(
        CExpression::Value(int32(Bitvector32Term::Variable(a))),
        CExpression::Value(int32(Bitvector32Term::Variable(b))),
    ));
    assert_eq!(
        prove_symbolic_c_execution_paths_with_budget(
            state,
            branchy_statement,
            Assumptions::new(),
            ExecutionBudget::new().with_paths(3),
        )
        .limit(),
        Some(ExecutionLimit::Paths)
    );
}

#[test]
fn while_invariant_is_proof_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let invariant = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: pointer,
        bytes: Bitvector32Term::Constant(4),
    };
    let state = CState::new().with_local("x", int32(0));
    let statement = c_while(
        c_greater_than(c_variable("x"), c_int32_literal(0)),
        vec![invariant.clone()],
        c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("false loop should execute under invariant obligation");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(invariant),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Normal(state),
            }),
        )
    );
}

#[test]
fn builtin_obligation_solver_proves_trivial_props() {
    let assumptions = Assumptions::new();
    let memory = CMemory::new().with_block("block", 8);
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };

    assert!(assumptions.proves(&Proposition::Equal(
        Term::Bitvector32(Bitvector32Term::Constant(7)),
        Term::Bitvector32(Bitvector32Term::Constant(7)),
    )));
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::Constant(true),
        true
    )));
    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer.clone(),
        bytes: Bitvector32Term::Constant(4),
    }));
    assert!(assumptions.proves(&Proposition::CMemoryCanStore {
        memory,
        pointer,
        byte_width: 4,
    }));
}

#[test]
fn empty_memory_range_is_vacuously_loadable() {
    let proposition = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: "not-live".into(),
            offset: PointerOffsetTerm::Variable(Variable(1)),
        },
        bytes: Bitvector32Term::Constant(0),
    };

    assert!(Assumptions::new().proves(&proposition));
}

#[test]
fn deferred_obligations_keep_contextual_memory_proofs_explicit() {
    let memory = CMemory::new();
    let base = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes: Bitvector32Term::Constant(8),
    };
    let element = Proposition::CMemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = Assumptions::new().assume_proposition(range);

    let mut ordinary = Vec::new();
    assert!(add_proof_obligation(&mut ordinary, &assumptions, element.clone()).is_some());
    assert!(
        ordinary.is_empty(),
        "ordinary execution may solve the range"
    );

    let mut deferred = Vec::new();
    let deferred_assumptions = assumptions.defer_non_exact_loadability_obligations();
    assert!(add_proof_obligation(&mut deferred, &deferred_assumptions, element.clone()).is_some());
    assert_eq!(deferred.len(), 1);
    assert_eq!(deferred[0].proposition(), &element);
}

#[test]
fn memory_derivation_records_the_selected_range_candidate() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let unrelated = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: Pointer {
            block: "unrelated".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        bytes: Bitvector32Term::Constant(64),
    };
    let selected = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::Constant(8),
    };
    let target = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(unrelated)
        .assume_proposition(selected.clone());
    let derivation = assumptions
        .derive_atomic_proposition(&target)
        .expect("the selected range should establish the element access");

    assert!(derivation.replay(&assumptions));
    assert_eq!(derivation.context_premises(), vec![selected]);
}

#[test]
fn loadable_symbolic_subrange_proves_an_indexed_cell() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let split = Bitvector32Term::Variable(Variable(87));
    let index = Bitvector32Term::Variable(Variable(88));
    let len = Bitvector32Term::Variable(Variable(89));
    let range = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.offset_by_int32_elements(split.clone()),
        bytes: Bitvector32Term::multiply(
            Bitvector32Term::subtract(len.clone(), split.clone()),
            Bitvector32Term::Constant(4),
        ),
    };
    let target = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(index.clone()),
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(range)
        .assume_condition(ConditionTerm::signed_less_equal(split, index.clone()), true)
        .assume_condition(ConditionTerm::signed_less_than(index, len), true);

    assert!(
        assumptions.derive_atomic_proposition(&target).is_some(),
        "split <= index < len should select a cell from [split..len]"
    );
}

#[test]
fn adjacent_loadable_regions_certify_their_concatenation() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let prefix = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::Constant(8),
    };
    let next_cell = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        bytes: Bitvector32Term::Constant(4),
    };
    let goal = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::Constant(12),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(prefix.clone())
        .assume_proposition(next_cell.clone());
    let derivation = assumptions
        .derive_atomic_proposition(&goal)
        .expect("an initialized next cell should extend the loadable prefix");
    assert!(derivation.replay(&assumptions));
    let premises = derivation.context_premises();
    assert_eq!(premises.len(), 2);
    assert!(premises.contains(&prefix));
    assert!(premises.contains(&next_cell));

    let stored_memory = CMemory::new().store(
        data.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        CValue::Int32(Bitvector32Term::Constant(9)),
    );
    let stored_goal = Proposition::CMemoryLoadable {
        memory: stored_memory,
        base: data.clone(),
        bytes: Bitvector32Term::Constant(12),
    };
    let stored_assumptions = Assumptions::new().assume_proposition(prefix.clone());
    let stored_derivation = stored_assumptions
        .derive_atomic_proposition(&stored_goal)
        .expect("a materialized next cell should extend the loadable prefix");
    assert!(stored_derivation.replay(&stored_assumptions));
    assert_eq!(stored_derivation.context_premises(), vec![prefix]);

    let gap = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Constant(4)),
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(goal.clone())
        .assume_proposition(gap);
    let too_wide = Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: data,
        bytes: Bitvector32Term::Constant(16),
    };
    assert!(!assumptions.proves(&too_wide));
}

#[test]
fn field_derived_capacity_range_covers_a_shorter_live_prefix() {
    if skip_without_memory_dag() {
        return;
    }
    let entry_memory = CMemory::new();
    let owner = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
            byte_width: 4,
        },
    };
    let field = |byte_offset| Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::Add(
            Box::new(owner.offset.clone()),
            Box::new(PointerOffsetTerm::Constant(byte_offset)),
        ),
    };
    let len = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&entry_memory),
        Box::new(owner.clone()),
    );
    let after_len = entry_memory
        .clone()
        .store(owner.clone(), CValue::Int32(len.clone()));
    let cap = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after_len),
        Box::new(field(4)),
    );
    let after_cap = after_len
        .clone()
        .store(field(4), CValue::Int32(cap.clone()));
    let range_data_offset = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&after_cap),
        Box::new(field(8)),
    );
    let range_data = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(range_data_offset),
            byte_width: 4,
        },
    };
    let entry_data_offset = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&entry_memory),
        Box::new(field(8)),
    );
    let entry_data = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(entry_data_offset),
            byte_width: 4,
        },
    };
    let index = Bitvector32Term::Variable(Variable(2_000_000));
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: after_cap,
            base: range_data,
            bytes: Bitvector32Term::multiply(cap.clone(), Bitvector32Term::Constant(4)),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), len.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_equal(len, cap), true);
    let target = Proposition::CMemoryLoadable {
        memory: entry_memory,
        base: entry_data.offset_by_int32_elements(index),
        bytes: Bitvector32Term::Constant(4),
    };

    assert!(
        assumptions.derive_atomic_proposition(&target).is_some(),
        "a field-derived capacity range must cover an entry-spelled live-prefix cell"
    );
}

#[test]
fn quantified_int32_fact_certifies_an_instantiated_load() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact_index = Variable(2_100_000);
    let target_index = Variable(2_100_001);
    let length = Bitvector32Term::Variable(Variable(2_100_002));
    let indexed_fact_pointer = data.offset_by_int32_elements(Bitvector32Term::Variable(fact_index));
    let loaded_value = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&memory),
        Box::new(indexed_fact_pointer),
    );
    let guarded_fact = forall_int32(
        fact_index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Variable(fact_index),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(fact_index),
                        length.clone(),
                    ),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(loaded_value, Bitvector32Term::Constant(7)),
                true,
            )),
        ),
    );
    let assumptions = Assumptions::new()
        .assume_proposition(guarded_fact)
        .assume_condition(
            ConditionTerm::signed_less_equal(
                Bitvector32Term::Constant(0),
                Bitvector32Term::Variable(target_index),
            ),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(Bitvector32Term::Variable(target_index), length),
            true,
        );
    let target = Proposition::CMemoryLoadable {
        memory,
        base: data.offset_by_int32_elements(Bitvector32Term::Variable(target_index)),
        bytes: Bitvector32Term::Constant(4),
    };

    assert!(assumptions.proves(&target));
    crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
        assert!(!assumptions.proves(&target));
    });
    assert!(
        !Assumptions::new()
            .assume_proposition(forall_int32(
                fact_index,
                Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            ))
            .proves(&target)
    );
}

#[test]
fn quantified_int32_fact_certifies_its_complete_guarded_range() {
    let memory = CMemory::new();
    let data = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let index = Variable(2_100_010);
    let length = Bitvector32Term::Variable(Variable(2_100_011));
    let index_bits = Bitvector32Term::Variable(index);
    let loaded_value = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&memory),
        Box::new(data.offset_by_int32_elements(index_bits.clone())),
    );
    let guarded_fact = forall_int32(
        index,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        index_bits.clone(),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(index_bits, length.clone()),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(loaded_value, Bitvector32Term::Constant(7)),
                true,
            )),
        ),
    );
    let assumptions = Assumptions::new().assume_proposition(guarded_fact);
    let target = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: data.clone(),
        bytes: Bitvector32Term::multiply(length.clone(), Bitvector32Term::Constant(4)),
    };

    assert!(assumptions.proves(&target));
    assert!(!assumptions.proves(&Proposition::CMemoryLoadable {
        memory: memory.with_block("other-state", 4),
        base: data.clone(),
        bytes: Bitvector32Term::multiply(length.clone(), Bitvector32Term::Constant(4)),
    }));
    assert!(!assumptions.proves(&Proposition::CMemoryLoadable {
        memory: CMemory::new(),
        base: Pointer {
            block: "other-data".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        bytes: Bitvector32Term::multiply(length, Bitvector32Term::Constant(4)),
    }));
}

#[test]
fn proposition_derivation_replay_requires_its_context() {
    let x = Bitvector32Term::Variable(Variable(86));
    let proposition = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(x, Bitvector32Term::Constant(0)),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(proposition.clone());
    let derivation = assumptions
        .derive_simp_proposition(&proposition)
        .expect("exact fact should produce a derivation");

    assert!(derivation.replay(&assumptions));
    assert!(!derivation.replay(&Assumptions::new()));
    assert_eq!(derivation.context_premises(), vec![proposition]);
}

#[test]
fn implication_derivation_context_excludes_its_local_antecedent() {
    let antecedent = Proposition::Predicate {
        name: "local_hypothesis".to_string(),
        arguments: Vec::new(),
    };
    let goal = Proposition::Implies(Box::new(antecedent.clone()), Box::new(antecedent));
    let assumptions = Assumptions::new();
    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("an implication may use its own antecedent");

    assert!(derivation.replay(&assumptions));
    assert!(
        derivation.context_premises().is_empty(),
        "binder-local assumptions are not ambient certificate premises"
    );
}

#[test]
fn forall_introduction_rejects_a_variable_free_in_ambient_assumptions() {
    let variable = Variable(186);
    let body = Proposition::Predicate {
        name: "holds".to_string(),
        arguments: vec![Term::Bitvector32(Bitvector32Term::Variable(variable))],
    };
    let goal = forall_int32(variable, body.clone());
    let assumptions = Assumptions::new().assume_proposition(body);

    assert!(!assumptions.proves(&goal));
    assert!(assumptions.derive_proposition(&goal).is_none());
}

#[test]
fn forall_derivation_replay_shadows_ambient_uses_of_the_binder_id() {
    let variable = Variable(187);
    let value = Bitvector32Term::Variable(variable);
    let goal = forall_int32(
        variable,
        Proposition::ConditionIs(ConditionTerm::equal(value.clone(), value), true),
    );
    let derivation = Assumptions::new()
        .derive_proposition(&goal)
        .expect("reflexivity should prove a universal in an empty context");
    let contaminated = Assumptions::new().assume_proposition(Proposition::Predicate {
        name: "ambient".to_string(),
        arguments: vec![Term::Bitvector32(Bitvector32Term::Variable(variable))],
    });

    assert!(derivation.replay(&Assumptions::new()));
    assert!(derivation.replay(&contaminated));
}

#[test]
fn finite_context_split_derivation_records_its_range_premises() {
    let variable = Variable(87);
    let value = Bitvector32Term::Variable(variable);
    let lower = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(Bitvector32Term::Constant(3), value.clone()),
        true,
    );
    let upper = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(value.clone(), Bitvector32Term::Constant(3)),
        true,
    );
    let goal = Proposition::ConditionIs(
        ConditionTerm::equal(value, Bitvector32Term::Constant(3)),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_proposition(lower.clone())
        .assume_proposition(upper.clone());
    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("the singleton finite range should establish equality");

    assert!(derivation.replay(&assumptions));
    assert!(!derivation.replay(&Assumptions::new()));
    let context = derivation.context_premises();
    assert!(context.contains(&lower));
    assert!(context.contains(&upper));
}

#[test]
fn successor_order_derivation_needs_only_an_upper_bound() {
    let index = Bitvector32Term::Variable(Variable(88));
    let upper = Bitvector32Term::Variable(Variable(89));
    let upper_bound =
        Proposition::ConditionIs(ConditionTerm::signed_less_than(index.clone(), upper), true);
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            index.clone(),
            Bitvector32Term::add(index.clone(), Bitvector32Term::Constant(1)),
        ),
        true,
    );
    let unrelated_order = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::Variable(Variable(90)),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_proposition(unrelated_order)
        .assume_proposition(upper_bound.clone())
        .assume_proposition(Proposition::Predicate {
            name: "unrelated".to_string(),
            arguments: Vec::new(),
        });
    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("an int32 value below another int32 value cannot overflow when incremented");

    assert!(derivation.replay(&assumptions));
    assert_eq!(derivation.context_premises(), vec![upper_bound]);
}

#[test]
fn upper_bound_extends_to_a_nonoverflowing_successor() {
    let length = Bitvector32Term::Variable(Variable(89_100));
    let capacity = Bitvector32Term::Variable(Variable(89_101));
    let successor = Bitvector32Term::add(capacity.clone(), Bitvector32Term::Constant(1));
    let goal = ConditionTerm::signed_less_equal(length.clone(), successor.clone());
    let bounded = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(length, capacity.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(capacity.clone(), Bitvector32Term::Constant(100)),
            true,
        );

    assert_eq!(
        bounded.decide(&ConditionTerm::signed_less_equal(
            Bitvector32Term::Variable(Variable(89_100)),
            capacity.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        bounded.decide(&ConditionTerm::signed_add_overflows(
            capacity.clone(),
            Bitvector32Term::Constant(1),
        )),
        Some(false)
    );
    assert_eq!(bounded.decide(&goal), Some(true));
    assert_eq!(
        Assumptions::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(
                    Bitvector32Term::Variable(Variable(89_100)),
                    capacity,
                ),
                true,
            )
            .decide(&ConditionTerm::signed_less_equal(
                Bitvector32Term::Variable(Variable(89_100)),
                successor,
            )),
        None,
        "the successor relation must still require overflow evidence"
    );
}

#[test]
fn assumptions_split_small_finite_context_variable() {
    let j = Bitvector32Term::Variable(Variable(87));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(2)),
            true,
        );
    let proposition = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j, Bitvector32Term::Constant(1)),
            true,
        )),
    );

    assert!(assumptions.proves(&proposition));
    assert_replayable_derivation(&assumptions, &proposition);
}

#[test]
fn finite_context_derivation_replays_under_a_narrower_range() {
    let j = Bitvector32Term::Variable(Variable(88));
    let broad = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(2)),
            true,
        );
    let proposition = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(1)),
            true,
        )),
    );
    let derivation = broad
        .derive_proposition(&proposition)
        .expect("the broad two-value range should produce a finite proof");
    let narrow = broad.assume_condition(
        ConditionTerm::signed_less_than(j, Bitvector32Term::Constant(1)),
        true,
    );

    assert!(
        derivation.replay(&narrow),
        "a proof covering a finite range remains valid when later facts narrow that range"
    );
}

#[test]
fn proposition_derivation_composes_case_split_conjuncts() {
    let j = Bitvector32Term::Variable(Variable(187));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(2)),
            true,
        );
    let finite_choice = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(j, Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(187)),
                Bitvector32Term::Constant(1),
            ),
            true,
        )),
    );
    let proposition = Proposition::And(Box::new(finite_choice.clone()), Box::new(finite_choice));

    assert_replayable_derivation(&assumptions, &proposition);
}

#[test]
fn finite_forall_order_fact_participates_in_transitive_order_path() {
    let memory = CMemory::new();
    let indexed_load = |index| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(memory.clone()),
            Box::new(Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::scale_int32(index, 4),
            }),
        )
    };
    let k = Variable(88);
    let k_bits = Bitvector32Term::Variable(k);
    let load_k = indexed_load(k_bits.clone());
    let load_0 = indexed_load(Bitvector32Term::Constant(0));
    let load_1 = indexed_load(Bitvector32Term::Constant(1));
    let load_2 = indexed_load(Bitvector32Term::Constant(2));
    let finite_order_fact = Proposition::ForAll {
        var: k,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(k_bits, Bitvector32Term::Constant(1)),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(load_k, load_1.clone()),
                true,
            )),
        )),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(finite_order_fact)
        .assume_condition(
            ConditionTerm::signed_less_equal(load_1, load_2.clone()),
            true,
        );

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(load_0, load_2),
        true,
    )));
}

#[test]
fn conditional_forall_instantiates_at_same_named_variable_in_order_path() {
    let k = Variable(188);
    let k_bits = Bitvector32Term::Variable(k);
    let j = Bitvector32Term::Variable(Variable(189));
    let value_at_k = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(CMemory::new()),
        Box::new(Pointer {
            block: "arg-memory".into(),
            offset: PointerOffsetTerm::scale_int32(k_bits.clone(), 4),
        }),
    );
    let pivot = Bitvector32Term::Variable(Variable(191));
    let successor = Bitvector32Term::Variable(Variable(192));
    let induction_hypothesis = Proposition::ForAll {
        var: k,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(k_bits.clone(), j.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(value_at_k.clone(), pivot.clone()),
                true,
            )),
        )),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(induction_hypothesis)
        .assume_condition(
            ConditionTerm::signed_less_than(
                k_bits.clone(),
                Bitvector32Term::add(j.clone(), Bitvector32Term::Constant(1)),
            ),
            true,
        )
        .assume_condition(ConditionTerm::equal(k_bits, j.clone()), false)
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j, Bitvector32Term::Constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(pivot, successor.clone()),
            true,
        );
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(value_at_k, successor),
        true,
    );

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("quantified order instance should produce a simplifier derivation");
    assert_eq!(derivation.conclusion(), &goal);
    assert!(derivation.replay(&assumptions));
}

#[test]
fn forall_int32_application_preserves_exact_premises_and_conclusion() {
    let binder = Variable(500);
    let bound = Bitvector32Term::Variable(binder);
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(bound.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let conclusion = Proposition::ConditionIs(ConditionTerm::equal(bound.clone(), bound), true);
    let quantified = Proposition::ForAll {
        var: binder,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(premise),
            Box::new(conclusion),
        )),
    };
    let value = Bitvector32Term::Variable(Variable(501));
    let instantiated_premise = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let instantiated_conclusion =
        Proposition::ConditionIs(ConditionTerm::equal(value.clone(), value), true);

    let theorem = prove_forall_int32_application(
        &quantified,
        Bitvector32Term::Variable(Variable(501)),
        std::slice::from_ref(&instantiated_premise),
    )
    .expect("exact int32 application should be certified");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(quantified),
            Box::new(Proposition::Implies(
                Box::new(instantiated_premise),
                Box::new(instantiated_conclusion),
            )),
        )
    );
}

#[test]
fn forall_int32_application_rejects_a_mismatched_premise() {
    let binder = Variable(510);
    let bound = Bitvector32Term::Variable(binder);
    let quantified = Proposition::ForAll {
        var: binder,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(bound.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(bound.clone(), bound),
                true,
            )),
        )),
    };
    let wrong = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::Variable(Variable(511)),
            Bitvector32Term::Constant(1),
        ),
        true,
    );

    assert!(
        prove_forall_int32_application(
            &quantified,
            Bitvector32Term::Variable(Variable(511)),
            &[wrong],
        )
        .is_none()
    );
}

#[test]
fn forall_int32_application_avoids_capturing_the_argument_variable() {
    let outer = Variable(520);
    let inner = Variable(521);
    let quantified = Proposition::ForAll {
        var: outer,
        sort: Sort::CInt32,
        body: Box::new(Proposition::ForAll {
            var: inner,
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(outer),
                    Bitvector32Term::Variable(inner),
                ),
                true,
            )),
        }),
    };
    let theorem =
        prove_forall_int32_application(&quantified, Bitvector32Term::Variable(inner), &[])
            .expect("capture-avoiding instantiation should be certified");
    let Proposition::Implies(_, conclusion) = theorem.proposition() else {
        panic!("application theorem should retain its quantified premise");
    };
    let Proposition::ForAll {
        var: renamed, body, ..
    } = conclusion.as_ref()
    else {
        panic!("nested quantifier should remain in the conclusion");
    };
    assert_ne!(*renamed, inner, "the inner binder must be renamed");
    assert!(matches!(
        body.as_ref(),
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(left, right),
            true
        ) if left.as_ref() == &Bitvector32Term::Variable(inner)
            && right.as_ref() == &Bitvector32Term::Variable(*renamed)
    ));
}

#[test]
fn assumptions_prove_by_bounded_disjunction_cases() {
    let x = Bitvector32Term::Variable(Variable(89));
    let x_is_zero = Proposition::ConditionIs(
        ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let x_is_one = Proposition::ConditionIs(
        ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(1)),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(Proposition::Or(
        Box::new(x_is_zero.clone()),
        Box::new(x_is_one.clone()),
    ));

    let proposition = Proposition::Or(Box::new(x_is_one), Box::new(x_is_zero));
    assert!(assumptions.proves(&proposition));
    assert_replayable_derivation(&assumptions, &proposition);
}

#[test]
fn known_memory_block_bounds_prove_symbolic_element_access() {
    let index = Variable(91);
    let index_bits = Bitvector32Term::Variable(index);
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index_bits.clone(), Bitvector32Term::Constant(3)),
            true,
        );
    let memory = CMemory::new().with_block("local:a", 12);
    let pointer = CMemory::local_pointer("a").offset_by_int32_elements(index_bits);

    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer.clone(),
        bytes: Bitvector32Term::Constant(4),
    }));
    assert!(assumptions.proves(&Proposition::CMemoryCanStore {
        memory,
        pointer,
        byte_width: 4,
    }));
}

#[test]
fn symbolic_int32_range_directly_proves_constant_element_loadable() {
    let memory = CMemory::new();
    let base = Pointer {
        block: "data".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let length = Bitvector32Term::Variable(Variable(89));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: Bitvector32Term::multiply(length, Bitvector32Term::Constant(4)),
        });

    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        bytes: Bitvector32Term::Constant(4),
    }));
}

#[test]
fn assumptions_prove_forall_int32_array_range_body() {
    let index = Variable(90);
    let index_bits = Bitvector32Term::Variable(index);
    let memory = CMemory::new().with_block("block", 12);
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let indexed_pointer = base.offset_by_int32_elements(index_bits.clone());
    let in_segment = Proposition::And(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(index_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(index_bits, Bitvector32Term::Constant(3)),
            true,
        )),
    );
    let loadable_index = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: indexed_pointer,
        bytes: Bitvector32Term::Constant(4),
    };
    let assumptions = Assumptions::new().assume_proposition(Proposition::CMemoryLoadable {
        memory,
        base,
        bytes: Bitvector32Term::Constant(12),
    });

    assert!(assumptions.proves(&forall_int32(
        index,
        Proposition::Implies(Box::new(in_segment), Box::new(loadable_index)),
    )));
}

#[test]
fn loadability_transports_to_snapshot_with_symbolic_index_bounds() {
    let index = Bitvector32Term::Variable(Variable(190));
    let cursor = Bitvector32Term::Variable(Variable(191));
    let range_memory = CMemory::new();
    let snapshot_memory = CMemory::new().with_block("local:j", 4);
    let base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: range_memory,
            base: base.clone(),
            bytes: Bitvector32Term::Constant(12),
        })
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), cursor.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(cursor.clone(), Bitvector32Term::Constant(2)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(cursor, Bitvector32Term::Constant(2)),
            false,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            index.clone(),
            Bitvector32Term::Constant(3),
        )),
        Some(true)
    );
    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: snapshot_memory,
        base: base.offset_by_int32_elements(index),
        bytes: Bitvector32Term::Constant(4),
    }));
}

#[test]
fn assumptions_prove_finite_forall_int32_by_instantiation() {
    let i = Variable(92);
    let j = Variable(93);
    let i_bits = Bitvector32Term::Variable(i);
    let j_bits = Bitvector32Term::Variable(j);
    let antecedent = Proposition::And(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(j_bits.clone(), Bitvector32Term::Constant(0)),
                true,
            )),
        )),
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(i_bits.clone(), j_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(j_bits, Bitvector32Term::Constant(3)),
                true,
            )),
        )),
    );
    let consequent = Proposition::Or(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(i_bits, Bitvector32Term::Constant(1)),
            true,
        )),
    );

    assert!(Assumptions::new().proves(&forall_int32(
        i,
        forall_int32(
            j,
            Proposition::Implies(Box::new(antecedent), Box::new(consequent)),
        ),
    )));
}

#[test]
fn assumptions_use_finite_forall_fact_to_prove_condition() {
    let k = Variable(94);
    let base_left = Bitvector32Term::Variable(Variable(95));
    let base_right = Bitvector32Term::Variable(Variable(96));
    let k_bits = Bitvector32Term::Variable(k);
    let antecedent = Proposition::And(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(k_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(k_bits.clone(), Bitvector32Term::Constant(3)),
            true,
        )),
    );
    let consequent = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Add(Box::new(base_left.clone()), Box::new(k_bits.clone())),
            Bitvector32Term::Add(Box::new(base_right.clone()), Box::new(k_bits)),
        ),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(forall_int32(
        k,
        Proposition::Implies(Box::new(antecedent), Box::new(consequent)),
    ));

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Add(Box::new(base_left), Box::new(Bitvector32Term::Constant(1))),
            Bitvector32Term::Add(Box::new(base_right), Box::new(Bitvector32Term::Constant(1))),
        ),
        true,
    )));
}

#[test]
fn order_solver_uses_negated_less_than_transitively() {
    let a = Bitvector32Term::Variable(Variable(94));
    let b = Bitvector32Term::Variable(Variable(95));
    let c = Bitvector32Term::Variable(Variable(96));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::signed_less_than(b.clone(), a.clone()), false)
        .assume_condition(ConditionTerm::signed_less_than(c.clone(), b), false);

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(a, c),
        true,
    )));
}

#[test]
fn assumptions_do_not_prove_implication_by_treating_unknown_antecedent_as_false() {
    let x = Bitvector32Term::Variable(Variable(91));
    let antecedent = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );
    let consequent =
        Proposition::ConditionIs(ConditionTerm::equal(x, Bitvector32Term::Constant(0)), true);

    assert!(!Assumptions::new().proves(&Proposition::Implies(
        Box::new(antecedent),
        Box::new(consequent),
    )));
}

#[test]
fn assumptions_prove_implication_with_refuted_antecedent() {
    let x = Bitvector32Term::Variable(Variable(91));
    let condition = ConditionTerm::equal(x, Bitvector32Term::Constant(0));
    let assumptions = Assumptions::new().assume_condition(condition.clone(), true);
    let antecedent = Proposition::ConditionIs(condition, false);
    let consequent = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(92)),
            Bitvector32Term::Constant(7),
        ),
        true,
    );

    assert!(assumptions.proves(&Proposition::Implies(
        Box::new(antecedent),
        Box::new(consequent),
    )));
}

#[test]
fn simp_derives_vacuous_implication_before_searching_large_consequent() {
    fn unknown_tree(depth: usize, index: usize) -> Proposition {
        if depth == 0 {
            return Proposition::Predicate {
                name: format!("unknown_{index}"),
                arguments: Vec::new(),
            };
        }
        Proposition::And(
            Box::new(unknown_tree(depth - 1, index * 2)),
            Box::new(unknown_tree(depth - 1, index * 2 + 1)),
        )
    }

    let condition = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(93)),
        Bitvector32Term::Constant(0),
    );
    let antecedent = Proposition::ConditionIs(condition.clone(), true);
    let consequent = unknown_tree(9, 0);
    let goal = Proposition::Implies(Box::new(antecedent), Box::new(consequent));
    let assumptions = Assumptions::new().assume_condition(condition, false);

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("a refuted antecedent should close before inspecting the consequent");
    assert!(derivation.replay(&assumptions));
}

#[test]
fn simp_derives_implication_body_before_refuting_known_antecedent() {
    let antecedent_condition = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(94)),
        Bitvector32Term::Constant(0),
    );
    let consequent_condition = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(95)),
        Bitvector32Term::Constant(7),
    );
    let goal = Proposition::Implies(
        Box::new(Proposition::ConditionIs(antecedent_condition.clone(), true)),
        Box::new(Proposition::ConditionIs(consequent_condition.clone(), true)),
    );
    let assumptions = Assumptions::new()
        .assume_condition(antecedent_condition, true)
        .assume_condition(consequent_condition, true);

    let derivation = assumptions
        .derive_simp_proposition(&goal)
        .expect("a known antecedent should use the available consequent directly");
    assert!(derivation.replay(&assumptions));
}

#[test]
fn assumptions_simplify_overflow_through_equality_chain() {
    let index = Bitvector32Term::Variable(Variable(91));
    let length = Bitvector32Term::Variable(Variable(92));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::equal(index.clone(), length.clone()), true)
        .assume_condition(
            ConditionTerm::equal(length, Bitvector32Term::Constant(0)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            index,
            Bitvector32Term::Constant(1),
        )),
        Some(false),
    );
}

#[test]
fn same_block_pointer_equality_transports_through_equal_offsets() {
    let left = Pointer {
        block: "shared".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(91)), 4),
    };
    let right = Pointer {
        block: "shared".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::pointer_equal(left.clone(), right.clone()),
        true,
    );

    assert!(pointers_proven_equal_for_memory_resolution(
        &left.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &right.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &assumptions,
    ));
}

#[test]
fn builtin_obligation_solver_discharges_concrete_invariant() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("block", 4);
    let invariant = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer,
        bytes: Bitvector32Term::Constant(4),
    };
    let state = CState::new().with_local("x", int32(0)).with_memory(memory);
    let statement = c_while(
        c_greater_than(c_variable("x"), c_int32_literal(0)),
        vec![invariant],
        c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1))),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("concrete invariant should be solved");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Normal(state),
        }
    );
}

#[test]
fn countdown_loop_body_preserves_nonnegative_invariant_symbolically() {
    let x = Variable(66);
    let x_bits = Bitvector32Term::Variable(x);
    let state = CState::new().with_local("x", int32(x_bits.clone()));
    let statement = c_assign("x", c_subtract(c_variable("x"), c_int32_literal(1)));
    let invariant =
        ConditionTerm::signed_greater_equal(x_bits.clone(), Bitvector32Term::Constant(0));
    let condition =
        ConditionTerm::signed_greater_than(x_bits.clone(), Bitvector32Term::Constant(0));
    let post_invariant = Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(
            Bitvector32Term::Subtract(
                Box::new(x_bits.clone()),
                Box::new(Bitvector32Term::Constant(1)),
            ),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_condition(invariant.clone(), true)
        .assume_condition(condition.clone(), true);
    let theorem = prove_c_statement_executes_and_propositions(
        state.clone(),
        statement.clone(),
        assumptions,
        vec![post_invariant.clone()],
    )
    .expect("x > 0 should prove x - 1 executes and remains nonnegative");

    assert_eq!(
        theorem.proposition().peel_implications(),
        &proposition_and(
            Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Normal(CState::new().with_local(
                    "x",
                    int32(Bitvector32Term::Subtract(
                        Box::new(x_bits),
                        Box::new(Bitvector32Term::Constant(1)),
                    )),
                ),),
            },
            post_invariant,
        )
    );
}

#[test]
fn symbolic_max_lt_branch_is_native_theorem() {
    let a = Variable(10);
    let b = Variable(11);
    let theorem = prove_c_max_lt_returns_right(a, b).expect("lt branch should prove");
    let condition = ConditionTerm::Bitvector32SignedLessThan(
        Box::new(Bitvector32Term::Variable(a)),
        Box::new(Bitvector32Term::Variable(b)),
    );
    let state = c_max_state(
        int32(Bitvector32Term::Variable(a)),
        int32(Bitvector32Term::Variable(b)),
    );

    assert_eq!(
        theorem.proposition(),
        &forall_int32(
            a,
            forall_int32(
                b,
                Proposition::Implies(
                    Box::new(Proposition::ConditionIs(condition, true)),
                    Box::new(Proposition::CStatementExecutes {
                        state: state.clone(),
                        statement: c_max_body(),
                        outcome: CStatementOutcome::Return {
                            value: int32(Bitvector32Term::Variable(b)),
                            state,
                        },
                    }),
                ),
            ),
        )
    );
}

#[test]
fn symbolic_max_not_lt_branch_is_native_theorem() {
    let a = Variable(12);
    let b = Variable(13);
    let theorem = prove_c_max_not_lt_returns_left(a, b).expect("false branch should prove");
    let condition = ConditionTerm::Bitvector32SignedLessThan(
        Box::new(Bitvector32Term::Variable(a)),
        Box::new(Bitvector32Term::Variable(b)),
    );
    let state = c_max_state(
        int32(Bitvector32Term::Variable(a)),
        int32(Bitvector32Term::Variable(b)),
    );

    assert_eq!(
        theorem.proposition(),
        &forall_int32(
            a,
            forall_int32(
                b,
                Proposition::Implies(
                    Box::new(Proposition::ConditionIs(condition, false)),
                    Box::new(Proposition::CStatementExecutes {
                        state: state.clone(),
                        statement: c_max_body(),
                        outcome: CStatementOutcome::Return {
                            value: int32(Bitvector32Term::Variable(a)),
                            state,
                        },
                    }),
                ),
            ),
        )
    );
}

#[test]
fn signed_add_overflow_is_native_undefined_behavior() {
    let state = CState::new();
    let theorem = prove_c_expression_evaluation(
        state.clone(),
        c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
    )
    .expect("concrete add should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state,
            expression: c_add(c_int32_literal(2_147_483_647), c_int32_literal(1)),
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn condition_evaluation_certifies_c_truthiness_directly() {
    let state = CState::new();
    let condition = c_less_than(c_int32_literal(1), c_int32_literal(2));
    let evaluation =
        prove_symbolic_c_condition_evaluation(state.clone(), condition.clone(), Assumptions::new());

    assert_eq!(evaluation.paths().len(), 1);
    assert_eq!(
        evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CConditionEvaluates {
            state,
            condition,
            outcome: CConditionOutcome::Value(true),
        }
    );
}

#[test]
fn void_truthiness_is_an_explicit_type_error() {
    let state = CState::new();
    let condition = c_void_value();
    let evaluation =
        prove_symbolic_c_condition_evaluation(state.clone(), condition.clone(), Assumptions::new());

    assert_eq!(evaluation.paths().len(), 1);
    assert_eq!(
        evaluation.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CConditionEvaluates {
            state: state.clone(),
            condition,
            outcome: CConditionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
        }
    );

    for expression in [
        c_not(c_void_value()),
        c_and(c_void_value(), c_int32_literal(1)),
        c_or(c_void_value(), c_int32_literal(1)),
    ] {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("invalid void truthiness should retain its runtime-error frontier");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            }
        );
    }
}

#[test]
fn void_local_declaration_is_an_explicit_type_error() {
    let paths = execute_c_statement_paths(
        &CState::new(),
        &c_declare("invalid", CType::Void),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("invalid void declarations should execute to a type error");

    assert_eq!(paths.len(), 1);
    assert_eq!(
        &paths[0].outcome,
        &CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
    );

    let paths = execute_c_statement_paths(
        &CState::new(),
        &c_if(c_void_value(), CStatement::Skip, CStatement::Skip),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("a void condition should execute to a type error");
    assert_eq!(paths.len(), 1);
    assert_eq!(
        &paths[0].outcome,
        &CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
    );
}

#[test]
fn symbolic_condition_evaluation_exposes_both_truthiness_paths() {
    let x = Variable(90);
    let state = CState::new().with_local("x", int32(Bitvector32Term::Variable(x)));
    let condition = c_greater_equal(c_variable("x"), c_int32_literal(0));
    let evaluation = prove_symbolic_c_condition_evaluation(state, condition, Assumptions::new());

    let outcomes = evaluation
        .paths()
        .iter()
        .map(
            |path| match path.theorem().proposition().peel_implications() {
                Proposition::CConditionEvaluates { outcome, .. } => outcome.clone(),
                proposition => panic!("unexpected condition theorem {proposition:?}"),
            },
        )
        .collect::<BTreeSet<_>>();
    assert_eq!(
        outcomes,
        BTreeSet::from([
            CConditionOutcome::Value(false),
            CConditionOutcome::Value(true),
        ])
    );
}

#[test]
fn int32_subtraction_is_native() {
    let state = CState::new();
    let statement = c_return(c_subtract(c_int32_literal(7), c_int32_literal(2)));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("concrete subtraction should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(5),
                state,
            },
        }
    );
}

#[test]
fn nonnegative_ordered_subtraction_does_not_overflow() {
    let position = Bitvector32Term::Variable(Variable(24));
    let length = Bitvector32Term::Variable(Variable(25));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(position.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(length.clone(), position.clone()),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_subtract_overflows(length, position)),
        Some(false)
    );
}

#[test]
fn signed_subtract_overflow_is_native_undefined_behavior() {
    let state = CState::new();
    let theorem = prove_c_expression_evaluation(
        state.clone(),
        c_subtract(c_int32_literal(2_147_483_648), c_int32_literal(1)),
    )
    .expect("concrete subtraction should evaluate");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state,
            expression: c_subtract(c_int32_literal(2_147_483_648), c_int32_literal(1)),
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
        }
    );
}

#[test]
fn int32_comparisons_return_c_int32_zero_or_one() {
    let state = CState::new();
    let examples = [
        (
            c_less_equal(c_int32_literal(2), c_int32_literal(2)),
            int32(1),
        ),
        (
            c_greater_than(c_int32_literal(3), c_int32_literal(2)),
            int32(1),
        ),
        (
            c_greater_equal(c_int32_literal(2), c_int32_literal(3)),
            int32(0),
        ),
        (c_equal(c_int32_literal(4), c_int32_literal(4)), int32(1)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("comparison should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn pointer_equality_returns_c_int32_zero_or_one() {
    let p = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let same = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let next = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let other = Pointer {
        block: "other".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(p))
        .with_local("same", CValue::Pointer(same))
        .with_local("next", CValue::Pointer(next))
        .with_local("other", CValue::Pointer(other));
    let examples = [
        (c_equal(c_variable("p"), c_variable("same")), int32(1)),
        (c_equal(c_variable("p"), c_variable("next")), int32(0)),
        (c_equal(c_variable("p"), c_variable("other")), int32(0)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("pointer equality should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn spec_pointer_equality_lowers_to_a_pure_fact() {
    let left = Pointer::symbolic(Variable(22_100));
    let right = Pointer::symbolic(Variable(22_101));
    let equality = ConditionTerm::pointer_equal(left.clone(), right.clone());

    assert_eq!(
        c_value_comparison_proposition(
            &CValue::Pointer(left.clone()),
            CComparisonOperator::Equal,
            &CValue::Pointer(right.clone()),
        ),
        Some(Proposition::ConditionIs(equality.clone(), true)),
    );
    assert_eq!(
        c_value_comparison_proposition(
            &CValue::Pointer(left.clone()),
            CComparisonOperator::NotEqual,
            &CValue::Pointer(right),
        ),
        Some(Proposition::ConditionIs(equality, false)),
    );
    assert_eq!(
        c_value_comparison_proposition(
            &CValue::Pointer(left),
            CComparisonOperator::LessThan,
            &CValue::Int32(Bitvector32Term::Constant(0)),
        ),
        None,
    );
}

#[test]
fn symbolic_pointer_truthiness_keeps_null_and_nonnull_paths() {
    let paths = c_truthiness_paths(
        CValue::Pointer(Pointer::symbolic(Variable(22_000))),
        Vec::new(),
        Vec::new(),
        &Assumptions::new(),
    );

    assert_eq!(paths.len(), 2);
    assert!(paths.iter().any(|path| path.is_true));
    assert!(paths.iter().any(|path| !path.is_true));
}

#[test]
fn pointer_equality_accepts_int32_zero_as_null_pointer_constant() {
    let null = Pointer {
        block: "null".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let nonnull = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("nullp", CValue::Pointer(null))
        .with_local("p", CValue::Pointer(nonnull));
    let examples = [
        (c_equal(c_variable("nullp"), c_int32_literal(0)), int32(1)),
        (c_equal(c_int32_literal(0), c_variable("nullp")), int32(1)),
        (c_equal(c_variable("p"), c_int32_literal(0)), int32(0)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("null equality should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }

    let invalid = c_equal(c_variable("p"), c_int32_literal(1));
    let theorem = prove_c_expression_evaluation(state.clone(), invalid.clone())
        .expect("invalid pointer equality should evaluate");
    assert_eq!(
        theorem.proposition(),
        &Proposition::CExpressionEvaluates {
            state,
            expression: invalid,
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
        }
    );
}

#[test]
fn not_equal_and_not_return_c_int32_zero_or_one() {
    let null = Pointer {
        block: "null".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let same = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let next = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let state = CState::new()
        .with_local("nullp", CValue::Pointer(null))
        .with_local("p", CValue::Pointer(p))
        .with_local("same", CValue::Pointer(same))
        .with_local("next", CValue::Pointer(next));
    let examples = [
        (
            c_not_equal(c_int32_literal(4), c_int32_literal(5)),
            int32(1),
        ),
        (c_not_equal(c_variable("p"), c_variable("same")), int32(0)),
        (c_not_equal(c_variable("p"), c_variable("next")), int32(1)),
        (
            c_not_equal(c_variable("nullp"), c_int32_literal(0)),
            int32(0),
        ),
        (c_not(c_int32_literal(0)), int32(1)),
        (c_not(c_int32_literal(7)), int32(0)),
        (c_not(c_variable("nullp")), int32(1)),
        (c_not(c_variable("p")), int32(0)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("logical expression should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }
}

#[test]
fn logical_and_or_short_circuit_right_operand() {
    let invalid_pointer = Pointer {
        block: "missing".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let invalid_load = c_typed_load(c_pointer_value(invalid_pointer), CType::Int32);
    let state = CState::new().with_resource_context(read_context(
        Pointer {
            block: "missing".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        0,
        1,
    ));
    let examples = [
        (c_and(c_int32_literal(0), invalid_load.clone()), int32(0)),
        (c_or(c_int32_literal(1), invalid_load.clone()), int32(1)),
    ];

    for (expression, expected) in examples {
        let theorem = prove_c_expression_evaluation(state.clone(), expression.clone())
            .expect("short-circuit expression should evaluate");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: state.clone(),
                expression,
                outcome: CExpressionOutcome::Value(expected),
            }
        );
    }

    assert!(
        prove_c_expression_evaluation(
            state.clone(),
            c_and(c_int32_literal(1), invalid_load.clone()),
        )
        .is_none()
    );
    assert!(prove_c_expression_evaluation(state, c_or(c_int32_literal(0), invalid_load)).is_none());
}

#[test]
fn untyped_pointer_operations_report_indeterminate_pointee_type() {
    let pointer = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer_value = || c_pointer_value(pointer.clone());
    let expressions = [
        c_load(pointer_value()),
        c_index(pointer_value(), c_int32_literal(1)),
        c_add(pointer_value(), c_int32_literal(1)),
        c_add(c_int32_literal(1), pointer_value()),
    ];

    for expression in expressions {
        let theorem = prove_c_expression_evaluation(CState::new(), expression.clone())
            .expect("an untyped pointer operation should produce an explicit model error");
        assert_eq!(
            theorem.proposition(),
            &Proposition::CExpressionEvaluates {
                state: CState::new(),
                expression,
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::IndeterminatePointeeType,),
            }
        );
    }
}

#[test]
fn symbolic_pointer_equality_reports_branch_facts() {
    let offset = Variable(80);
    let left = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Variable(offset),
    };
    let condition = ConditionTerm::pointer_offset_equal(left.offset.clone(), right.offset.clone());
    let state = CState::new()
        .with_local("p", CValue::Pointer(left))
        .with_local("q", CValue::Pointer(right));
    let statement = c_if(
        c_equal(c_variable("p"), c_variable("q")),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(condition.clone(), true)]
    );
    assert_eq!(
        execution.paths()[0]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement: statement.clone(),
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state: state.clone(),
            },
        }
    );
    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(condition, false)]
    );
    assert_eq!(
        execution.paths()[1]
            .theorem()
            .proposition()
            .peel_implications(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state,
            },
        }
    );
}

#[test]
fn if_uses_c_int32_truthiness() {
    let state = CState::new();
    let statement = c_if(
        c_int32_literal(7),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("nonzero int32 condition should take then branch");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(1),
                state,
            },
        }
    );

    let state = CState::new();
    let statement = c_if(
        c_int32_literal(0),
        c_return(c_int32_literal(1)),
        c_return(c_int32_literal(0)),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("zero int32 condition should take else branch");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(0),
                state,
            },
        }
    );
}

#[test]
fn assignment_and_sequence_update_native_state() {
    let state = CState::new().with_local("x", int32(0));
    let statement = c_seq(c_assign("x", c_int32_literal(2)), c_return(c_variable("x")));
    let final_state = CState::new().with_local("x", int32(2));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("assignment sequence should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(2),
                state: final_state,
            },
        }
    );
}

#[test]
fn store_then_load_threads_native_memory() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new().with_resource_context(resources.clone());
    let statement = c_seq(
        c_typed_store(
            c_pointer_value(pointer.clone()),
            c_int32_literal(9),
            CType::Int32,
        ),
        c_return(c_typed_load(c_pointer_value(pointer.clone()), CType::Int32)),
    );
    let final_state = CState::new()
        .with_memory(CMemory::new().store(pointer.clone(), int32(9)))
        .with_resource_context(resources);
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("store then load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn read_element_permits_symbolic_external_load_from_incomplete_memory() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(pointer.clone()))
        .with_resource_context(read_context(pointer.clone(), 0, 1));
    let statement = c_return(c_load(c_variable("p")));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(execution.paths()[0].obligations(), &[]);
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(CMemory::new()),
                    Box::new(pointer),
                )),
                state,
            },
        }
    );
}

#[test]
fn block_backed_store_then_load_needs_no_memory_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("block", 16);
    let resources = write_context(pointer.clone(), 0, 1);
    let state = CState::new()
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    let statement = c_seq(
        c_typed_store(
            c_pointer_value(pointer.clone()),
            c_int32_literal(9),
            CType::Int32,
        ),
        c_return(c_typed_load(c_pointer_value(pointer.clone()), CType::Int32)),
    );
    let final_state = CState::new()
        .with_memory(memory.store(pointer, int32(9)))
        .with_resource_context(resources);
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("in-range block store/load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(9),
                state: final_state,
            },
        }
    );
}

#[test]
fn block_backed_missing_load_returns_symbolic_value_without_obligation() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = CMemory::new().with_block("block", 16);
    let state = CState::new()
        .with_local("p", CValue::Pointer(pointer.clone()))
        .with_memory(memory.clone())
        .with_resource_context(read_context(pointer.clone(), 0, 1));
    let statement = c_return(c_load(c_variable("p")));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("in-range missing load should produce symbolic value");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory),
                    Box::new(pointer)
                )),
                state,
            },
        }
    );
}

#[test]
fn pointer_addition_scales_int32_offsets_for_loads() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let second = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = CMemory::new()
        .with_block("block", 16)
        .store(second.clone(), int32(23));
    let resources = read_context(base.clone(), 1, 2);
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_memory(memory)
        .with_resource_context(resources.clone());
    let statement = c_return(c_load(c_add(c_variable("p"), c_int32_literal(1))));
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("pointer arithmetic load should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(23),
                state: CState::new()
                    .with_local(
                        "p",
                        CValue::Pointer(Pointer {
                            block: "block".into(),
                            offset: PointerOffsetTerm::Constant(0),
                        }),
                    )
                    .with_memory(
                        CMemory::new()
                            .with_block("block", 16)
                            .store(second, int32(23),),
                    )
                    .with_resource_context(resources),
            },
        }
    );
}

#[test]
fn read_element_permits_pointer_addition_load_beyond_memory_block() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let derived = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory = CMemory::new().with_block("block", 4);
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_memory(memory.clone())
        .with_resource_context(read_context(base, 1, 2));
    let statement = c_return(c_load(c_add(c_variable("p"), c_int32_literal(1))));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(execution.paths()[0].obligations(), &[]);
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state: state.clone(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory),
                    Box::new(derived),
                )),
                state,
            },
        }
    );
}

#[test]
fn fixed_bound_store_loop_touches_only_valid_pointer_range() {
    let base = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("block", 12);
    let resources = write_context(base.clone(), 0, 3);
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_local("i", int32(0))
        .with_memory(memory.clone())
        .with_resource_context(resources.clone());
    let loop_statement = c_while(
        c_less_than(c_variable("i"), c_int32_literal(3)),
        Vec::new(),
        c_seq(
            c_store(c_add(c_variable("p"), c_variable("i")), c_variable("i")),
            c_assign("i", c_add(c_variable("i"), c_int32_literal(1))),
        ),
    );
    let statement = c_seq(loop_statement, c_return(c_variable("i")));
    let final_memory = memory
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            int32(0),
        )
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(4),
            },
            int32(1),
        )
        .store(
            Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(8),
            },
            int32(2),
        );
    let final_state = CState::new()
        .with_local(
            "p",
            CValue::Pointer(Pointer {
                block: "block".into(),
                offset: PointerOffsetTerm::Constant(0),
            }),
        )
        .with_local("i", int32(3))
        .with_memory(final_memory)
        .with_resource_context(resources);
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(3),
                state: final_state,
            },
        }
    );
}

#[test]
fn symbolic_loadable_discharges_pointer_access_obligation() {
    let i = Variable(67);
    let n = Variable(68);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let memory = CMemory::new();
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(base.clone()))
        .with_local("i", int32(i_bits.clone()))
        .with_memory(memory.clone())
        .with_resource_context(write_context(base.clone(), 0, n_bits.clone()));
    let statement = c_store(c_add(c_variable("p"), c_variable("i")), c_int32_literal(7));
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: Bitvector32Term::Multiply(
                Box::new(n_bits.clone()),
                Box::new(Bitvector32Term::Constant(4)),
            ),
        })
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(i_bits.clone(), n_bits),
            true,
        );
    let execution = prove_symbolic_c_execution_paths(state, statement, assumptions);

    assert_eq!(execution.paths().len(), 1);
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
}

#[test]
fn interval_arithmetic_proves_increment_bounds_and_no_overflow() {
    let i = Variable(69);
    let n = Variable(70);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let state = CState::new().with_local("i", int32(i_bits.clone()));
    let statement = c_assign("i", c_add(c_variable("i"), c_int32_literal(1)));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(i_bits.clone(), n_bits.clone()),
            true,
        );
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_than(i_bits.clone(), incremented.clone()),
        true,
    )));
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(i_bits.clone(), incremented.clone()),
        true,
    )));
    let theorem = prove_c_statement_executes_and_propositions(
        state,
        statement,
        assumptions,
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(
                    incremented.clone(),
                    Bitvector32Term::Constant(0),
                ),
                true,
            ),
            Proposition::ConditionIs(ConditionTerm::signed_less_equal(incremented, n_bits), true),
        ],
    )
    .expect("interval facts should prove i + 1 bounds and no signed overflow");

    assert!(matches!(theorem.proposition(), Proposition::Implies(_, _)));
}

#[test]
fn signed_order_solver_knows_int32_universal_bounds() {
    let x = Bitvector32Term::Variable(Variable(71));
    let int_min = Bitvector32Term::Constant(i32::MIN as u32);
    let int_max = Bitvector32Term::Constant(i32::MAX as u32);
    let assumptions = Assumptions::new();

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            x.clone(),
            int_max.clone()
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_than(x.clone(), int_max)),
        Some(false)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            x.clone(),
            int_min.clone()
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(x, int_min)),
        Some(false)
    );
}

#[test]
fn interval_arithmetic_uses_lower_bound_for_incremented_values() {
    let i = Variable(73);
    let i_bits = Bitvector32Term::Variable(i);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    // A lower bound alone is not enough: `i + 1` wraps at INT_MAX, so
    // `i >= 1` does not entail `i + 1 >= 1` (false at i = INT_MAX).
    let lower_only = Assumptions::new().assume_condition(
        ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(1)),
        true,
    );
    assert!(!lower_only.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(incremented.clone(), Bitvector32Term::Constant(1),),
        true,
    )));

    // Knowing `i < INT_MAX` rules out signed overflow of `i + 1`, so the
    // lower bound carries to the incremented value.
    let assumptions = lower_only.assume_condition(
        ConditionTerm::signed_less_than(i_bits, Bitvector32Term::Constant(i32::MAX as u32)),
        true,
    );
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_greater_equal(incremented.clone(), Bitvector32Term::Constant(1),),
        true,
    )));
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::signed_greater_than(incremented, Bitvector32Term::Constant(0)),
        true,
    )));
}

#[test]
fn nonnegative_successor_requires_no_overflow_evidence() {
    let x = Bitvector32Term::Variable(Variable(74_001));
    let successor = Bitvector32Term::add(x.clone(), Bitvector32Term::Constant(1));
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(0)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            successor.clone(),
            Bitvector32Term::Constant(0),
        )),
        None,
    );
    assert!(
        assumptions
            .derive_simp_proposition(&Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(successor, Bitvector32Term::Constant(0),),
                true,
            ))
            .is_none()
    );
}

#[test]
fn additive_upper_bound_covers_incremented_pointer_access() {
    let j = Variable(74);
    let j_bits = Bitvector32Term::Variable(j);
    let incremented = Bitvector32Term::add(j_bits.clone(), Bitvector32Term::Constant(1));
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer = base.offset_by_int32_elements(incremented.clone());
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(j_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j_bits, Bitvector32Term::Constant(2)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            incremented,
            Bitvector32Term::Constant(3),
        )),
        Some(true)
    );
    assert!(assumptions.pointer_access_in_range(
        &pointer,
        4,
        &base,
        &Bitvector32Term::Constant(0),
        &Bitvector32Term::Constant(3),
    ));
}

#[test]
fn relative_dependent_range_is_covered_by_owned_range() {
    let owner = Bitvector32Term::Variable(Variable(75));
    let backing = Bitvector32Term::Variable(Variable(76));
    let index = Bitvector32Term::Variable(Variable(77));
    let length = Bitvector32Term::Variable(Variable(78));
    let capacity = Bitvector32Term::Variable(Variable(79));
    let base = Pointer {
        block: "owner".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let backing_start = Bitvector32Term::subtract(backing.clone(), owner.clone());
    let indexed_start =
        Bitvector32Term::subtract(Bitvector32Term::add(backing, index.clone()), owner);
    let available = CResourceFact::own_memory(CMemoryRange::new(
        base.clone(),
        backing_start.clone(),
        Bitvector32Term::add(backing_start, capacity.clone()),
    ));
    let required = CResourceFact::own_memory(CMemoryRange::new(
        base,
        indexed_start.clone(),
        Bitvector32Term::add(indexed_start, Bitvector32Term::Constant(1)),
    ));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(index, length.clone()), true)
        .assume_condition(ConditionTerm::signed_less_equal(length, capacity), true);
    let resources = ResourceContext::new().unchecked_with_fact(available);

    assert!(resources.satisfies_fact(&required, &assumptions));
    assert!(resources.without_fact(&required, &assumptions).is_some());
}

#[test]
fn addition_cancels_a_negated_pointer_base() {
    let base = Bitvector32Term::Variable(Variable(90));
    let index = Bitvector32Term::Variable(Variable(91));
    let negative_base = Bitvector32Term::subtract(Bitvector32Term::Constant(0), base.clone());

    assert_eq!(
        Bitvector32Term::add(negative_base, Bitvector32Term::add(base, index.clone()),),
        index
    );
}

#[test]
fn negative_equality_fact_decides_equality_false() {
    let x = Bitvector32Term::Variable(Variable(79));
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::equal(x.clone(), Bitvector32Term::Constant(0)),
        false,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(Bitvector32Term::Constant(0), x,)),
        Some(false)
    );
}

#[test]
fn equality_facts_are_transitive() {
    let i = Bitvector32Term::Variable(Variable(84));
    let k = Bitvector32Term::Variable(Variable(85));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::equal(k.clone(), i.clone()), true)
        .assume_condition(ConditionTerm::equal(i, Bitvector32Term::Constant(1)), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(k, Bitvector32Term::Constant(1))),
        Some(true)
    );
}

#[test]
fn equality_transports_signed_order_facts_in_both_directions() {
    let selected = Bitvector32Term::Variable(Variable(86));
    let key = Bitvector32Term::Variable(Variable(87));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::equal(selected.clone(), key.clone()), true)
        .assume_condition(
            ConditionTerm::signed_greater_equal(key.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(10), selected.clone()),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            selected,
            Bitvector32Term::Constant(0),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(10),
            key,
        )),
        Some(true)
    );
}

#[test]
fn simp_combines_equality_with_discrete_integer_bounds() {
    let length = Bitvector32Term::Variable(Variable(87_100));
    let owner_length = Bitvector32Term::Variable(Variable(87_101));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::equal(owner_length.clone(), length), true);

    assert_eq!(
        assumptions.decide_condition_for_simp(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(1),
            owner_length,
        )),
        Some(true)
    );
}

#[test]
fn simp_evaluates_equality_arithmetic_chains() {
    let old_split = Bitvector32Term::Variable(Variable(87_102));
    let split = Bitvector32Term::Variable(Variable(87_103));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::equal(old_split.clone(), Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(
                split.clone(),
                Bitvector32Term::add(old_split, Bitvector32Term::Constant(1)),
            ),
            true,
        );

    assert_eq!(
        assumptions.decide_condition_for_simp(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(1),
            split,
        )),
        Some(true)
    );
}

#[test]
fn equality_transport_reaches_chains_and_arithmetic_terms() {
    let x = Bitvector32Term::Variable(Variable(88));
    let y = Bitvector32Term::Variable(Variable(89));
    let z = Bitvector32Term::Variable(Variable(90));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::equal(x.clone(), y), true)
        .assume_condition(ConditionTerm::equal(z.clone(), x), true)
        .assume_condition(
            ConditionTerm::signed_less_than(
                Bitvector32Term::add(z, Bitvector32Term::Constant(1)),
                Bitvector32Term::Constant(8),
            ),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::add(
                Bitvector32Term::Variable(Variable(89)),
                Bitvector32Term::Constant(1),
            ),
            Bitvector32Term::Constant(8),
        )),
        Some(true)
    );
}

#[test]
fn excluded_small_integer_range_is_inconsistent() {
    let k = Bitvector32Term::Variable(Variable(80));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::Constant(3)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(0)),
            false,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(1)),
            false,
        )
        .assume_condition(ConditionTerm::equal(k, Bitvector32Term::Constant(2)), false);

    assert!(assumptions.proves(&false_equals_true_proposition()));
}

#[test]
fn singleton_integer_range_forces_equality() {
    let k = Bitvector32Term::Variable(Variable(86));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k.clone(), Bitvector32Term::Constant(1)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::equal(k, Bitvector32Term::Constant(0))),
        Some(true)
    );
}

#[test]
fn safe_positive_subtraction_is_below_its_base() {
    let x = Bitvector32Term::Variable(Variable(87));
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(1)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::subtract(x.clone(), Bitvector32Term::Constant(1)),
            x,
        )),
        Some(true)
    );
}

#[test]
fn mutable_frame_proves_unwritten_load_equal_across_stack_locals() {
    let i = Variable(74);
    let i_bits = Bitvector32Term::Variable(i);
    let old_memory = CMemory::new();
    let loop_entry_memory = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(1));
    let loop_exit_memory = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(i_bits.clone()));
    let first_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(i_bits.clone()),
            byte_width: 4,
        },
    };
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits, Bitvector32Term::Constant(1)),
            true,
        )
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: loop_entry_memory,
            after: loop_exit_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(loop_exit_memory),
                Box::new(first_cell.clone()),
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(old_memory),
                Box::new(first_cell)
            ),
        ),
        true,
    )));
}

#[test]
fn mutable_frame_transports_load_across_certified_effect_chain() {
    let preserved = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let first_write = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let second_write = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let before = CMemory::new();
    let middle = before.clone().store(first_write.clone(), int32(1));
    let after = middle.clone().store(second_write.clone(), int32(2));
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: before.clone(),
            after: middle.clone(),
            pointers: vec![first_write],
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: middle,
            after: after.clone(),
            pointers: vec![second_write],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after),
                Box::new(preserved.clone())
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before),
                Box::new(preserved)
            ),
        ),
        true,
    )));
}

#[test]
fn unrelated_external_cell_store_preserves_memory_load_with_stack_temporary() {
    let old_memory = CMemory::new();
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p1 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let stack_memory = CMemory::new()
        .with_block("local:tmp", 4)
        .store(CMemory::local_pointer("tmp"), int32(0));
    let current_memory = stack_memory.clone().store(
        p0.clone(),
        int32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(stack_memory),
            Box::new(p0),
        )),
    );

    assert!(Assumptions::new().proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(current_memory),
                Box::new(p1.clone())
            ),
            Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(old_memory), Box::new(p1)),
        ),
        true,
    )));
}

#[test]
fn exact_changed_cell_frame_precedes_abstract_effect_search() {
    let queried = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(40_000)), 4),
    };
    let materialized = Pointer {
        block: queried.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(40_001)), 4),
    };
    let before = CMemory::new().with_block("call-havoc:0", 0);
    let after = before.clone().store(materialized.clone(), int32(7));
    let assumptions = Assumptions::new().assume_proposition(Proposition::CResourceSeparate {
        left: CResource::Memory(memory_range(queried.clone(), 0, 1)),
        right: CResource::Memory(memory_range(materialized, 0, 1)),
    });

    assert!(c_memory_load_is_unchanged(
        &before,
        &after,
        &queried,
        &assumptions,
    ));
}

#[test]
fn exact_separation_resolves_contained_symbolic_ranges_without_general_search() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(41_000)), 4),
    };
    let data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(41_001)), 4),
    };
    let length = Bitvector32Term::Variable(Variable(41_002));
    let owner_range = memory_range(owner.clone(), 0, 4);
    let data_range = memory_range(data.clone(), 0, length.clone());
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(owner_range.clone()),
            right: CResource::Memory(data_range.clone()),
        })
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        ));
    let owner_field = memory_range(owner.offset_by_int32_elements(2.into()), 0, 1);
    let data_cell = memory_range(data.clone(), 0, 1);

    assert!(
        assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &owner_field,
            &data_cell,
        )
    );

    let memory = CMemory::new().with_block("call-havoc:0", 0);
    let data_field = owner.offset_by_int32_elements(2.into());
    let loaded_data_offset = PointerOffsetTerm::scale_int32(
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(memory), Box::new(data_field)),
        4,
    );
    let loaded_data = Pointer {
        block: data.block.clone(),
        offset: loaded_data_offset.clone(),
    };
    let assumptions = assumptions
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(loaded_data_offset, data.offset.clone()),
            true,
        ))
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), length),
            true,
        ));
    let owner_len_field = memory_range(owner.offset_by_int32_elements(1.into()), 0, 1);
    let second_data_cell = memory_range(loaded_data, 1, 2);
    assert!(
        assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &owner_len_field,
            &second_data_cell,
        )
    );
}

#[test]
fn direct_resource_match_uses_exact_field_load_equalities() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("call-havoc:0", 0);
    let loaded_data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(owner.offset_by_int32_elements(2.into())),
            ),
            4,
        ),
    };
    let loaded_length = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory),
        Box::new(owner.offset_by_int32_elements(1.into())),
    );
    let named_data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(41_100)), 4),
    };
    let named_length = Bitvector32Term::Variable(Variable(41_101));
    let loaded = CResource::Memory(memory_range(loaded_data.clone(), 0, loaded_length.clone()));
    let named = CResource::Memory(memory_range(named_data.clone(), 0, named_length.clone()));

    assert!(!c_resources_directly_match(
        &loaded,
        &named,
        &Assumptions::new()
    ));

    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::pointer_offset_equal(loaded_data.offset, named_data.offset),
            true,
        )
        .assume_condition(ConditionTerm::equal(loaded_length, named_length), true);
    assert!(c_resources_directly_match(&loaded, &named, &assumptions));
}

#[test]
fn equivalent_memory_load_order_facts_can_be_inconsistent() {
    let old_memory = CMemory::new();
    let stack_memory = CMemory::new()
        .with_block("local:tmp", 4)
        .store(CMemory::local_pointer("tmp"), int32(0));
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let old_p0 = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(old_memory),
        Box::new(p0.clone()),
    );
    let stack_p0 =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(stack_memory), Box::new(p0));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_than(old_p0.clone(), stack_p0.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(stack_p0, old_p0), true);

    assert!(assumptions.proves(&false_equals_true_proposition()));
}

#[test]
fn equivalent_condition_facts_with_different_truth_values_are_inconsistent() {
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p1 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory_a = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(0));
    let memory_b = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(1));
    let left_a = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory_a.clone()),
        Box::new(p0.clone()),
    );
    let right_a = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory_a),
        Box::new(p1.clone()),
    );
    let left_b = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory_b.clone()),
        Box::new(p0),
    );
    let right_b =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(memory_b), Box::new(p1));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::signed_less_than(left_a, right_a), true)
        .assume_condition(ConditionTerm::signed_less_than(left_b, right_b), false);

    assert!(assumptions.proves(&false_equals_true_proposition()));
}

#[test]
fn disjoint_range_proves_mutable_frame_cell_distinct() {
    let i = Variable(81);
    let j = Variable(82);
    let i_bits = Bitvector32Term::Variable(i);
    let j_bits = Bitvector32Term::Variable(j);
    let before_memory = CMemory::new();
    let after_memory = CMemory::new();
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(i_bits.clone()),
            byte_width: 4,
        },
    };
    let read_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(j_bits.clone()),
            byte_width: 4,
        },
    };
    let i_plus_one = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let j_plus_one = Bitvector32Term::Add(
        Box::new(j_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_than(i_bits.clone(), i_plus_one.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j_bits.clone(), j_plus_one.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: base.clone(),
            left_start: i_bits.clone(),
            left_end: i_plus_one,
            right_base: base,
            right_start: j_bits.clone(),
            right_end: j_plus_one,
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: before_memory.clone(),
            after: after_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after_memory),
                Box::new(read_cell.clone())
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before_memory),
                Box::new(read_cell)
            ),
        ),
        true,
    )));
}

#[test]
fn disjoint_ranges_frame_metadata_across_symbolic_index_store() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(83)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(84)), 4),
    };
    let index = Bitvector32Term::Variable(Variable(85));
    let capacity = Bitvector32Term::Variable(Variable(86));
    let metadata_cell = owner.clone();
    let written_cell = data.offset_by_int32_elements(index.clone());
    let before_memory = CMemory::new();
    let after_memory = before_memory.clone().store(written_cell.clone(), int32(7));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index, capacity.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: owner,
            left_start: Bitvector32Term::Constant(0),
            left_end: Bitvector32Term::Constant(4),
            right_base: data,
            right_start: Bitvector32Term::Constant(0),
            right_end: capacity,
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: before_memory.clone(),
            after: after_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after_memory),
                Box::new(metadata_cell.clone()),
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before_memory),
                Box::new(metadata_cell)
            ),
        ),
        true,
    )));
}

#[test]
fn equivalent_field_derived_bases_frame_symbolic_index_store() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(87)), 4),
    };
    let owner_data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let base_memory = CMemory::new();
    let execution_memory = base_memory
        .clone()
        .with_block("local:data", 8)
        .store(CMemory::local_pointer("data"), int32(0));
    let resource_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(base_memory.clone()),
                Box::new(owner_data_cell.clone()),
            ),
            4,
        ),
    };
    let execution_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(execution_memory.clone()),
                Box::new(owner_data_cell),
            ),
            4,
        ),
    };
    let index = Bitvector32Term::Variable(Variable(88));
    let capacity = Bitvector32Term::Variable(Variable(89));
    let metadata_cell = owner.clone();
    let written_cell = execution_data.offset_by_int32_elements(index.clone());
    let after_memory = execution_memory
        .clone()
        .store(written_cell.clone(), int32(7));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index, capacity.clone()),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                resource_data,
                Bitvector32Term::Constant(0),
                capacity,
            )),
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: execution_memory.clone(),
            after: after_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after_memory),
                Box::new(metadata_cell.clone()),
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(execution_memory),
                Box::new(metadata_cell)
            ),
        ),
        true,
    )));
}

#[test]
fn direct_transport_composes_framed_loads_inside_an_indexed_address() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(95)), 4),
    };
    let owner_len_cell = owner.clone();
    let owner_data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let before = CMemory::new();
    let data_value = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(owner_data_cell),
    );
    let length = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(owner_len_cell),
    );
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data_value, 4),
    };
    let index = Bitvector32Term::Variable(Variable(96));
    let capacity = Bitvector32Term::Variable(Variable(97));
    let written_cell = data.offset_by_int32_elements(index.clone());
    let terminator_cell = data.offset_by_int32_elements(length.clone());
    let after = before.clone().store(written_cell.clone(), int32(7));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(terminator_cell),
            ),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::signed_less_than(index, length), true)
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                data,
                Bitvector32Term::Constant(0),
                capacity,
            )),
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before,
            after: after.clone(),
            pointers: vec![written_cell],
        });

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("the address loads and then the indexed cell should transport");
    let Proposition::Implies(source, target) = theorem.proposition() else {
        panic!("transport theorem must be an implication");
    };
    assert_eq!(source.as_ref(), &fact);
    assert_ne!(target.as_ref(), &fact);
    assert_eq!(c_condition_fact_memories(target), vec![after]);
}

#[test]
fn direct_transport_rewrites_loads_inside_pointer_equality() {
    let before = CMemory::new();
    let field_cell = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(8),
    };
    let field_value = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(field_cell.clone()),
            ),
            4,
        ),
    };
    let local_value = Pointer {
        block: PointerBlock::Symbolic(Variable(110)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(field_value, local_value.clone()),
        true,
    );
    let after = before.clone().with_block("local:result", 8);

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &Assumptions::new())
        .expect("an unrelated local-memory change should transport a pointer-valued field load");
    let Proposition::Implies(source, target) = theorem.proposition() else {
        panic!("transport theorem must be an implication");
    };
    assert_eq!(source.as_ref(), &fact);
    let transported_field_value = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after),
                Box::new(field_cell),
            ),
            4,
        ),
    };
    assert_eq!(
        target.as_ref(),
        &Proposition::ConditionIs(
            ConditionTerm::pointer_equal(transported_field_value, local_value),
            true,
        )
    );
}

#[test]
fn pointer_equality_composes_across_same_block_offset_equalities() {
    let final_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(120)),
    };
    let snapshot_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(121)),
    };
    let local_pointer = Pointer {
        block: PointerBlock::Symbolic(Variable(122)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::pointer_offset_equal(
                final_pointer.offset.clone(),
                snapshot_pointer.offset.clone(),
            ),
            true,
        )
        .assume_condition(
            ConditionTerm::pointer_equal(snapshot_pointer, local_pointer.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::pointer_equal(local_pointer, Pointer::null()),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::pointer_equal(
            final_pointer,
            Pointer::null()
        )),
        Some(true)
    );
}

#[test]
fn explicit_separation_contains_one_element_under_a_positive_length() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(98)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(99)), 4),
    };
    let length = Bitvector32Term::Variable(Variable(100));
    let owner_range = CMemoryRange::new(
        owner,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(6),
    );
    let data_range = CMemoryRange::new(data, Bitvector32Term::Constant(0), length.clone());
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), length),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(owner_range.clone()),
            right: CResource::Memory(data_range.clone()),
        });

    assert!(
        assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &CMemoryRange::new(
                data_range.base().clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            ),
            &CMemoryRange::new(
                owner_range.base().clone(),
                Bitvector32Term::Constant(1),
                Bitvector32Term::Constant(2),
            ),
        )
    );
}

#[test]
fn direct_separation_contains_zero_under_a_constant_lower_bound() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(104)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(105)), 4),
    };
    let length = Bitvector32Term::Variable(Variable(106));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                data.clone(),
                Bitvector32Term::Constant(0),
                length,
            )),
        });

    assert!(assumptions.ranges_directly_disjoint_from_pointer(
        &[CMemoryRange::new(
            owner,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
        &data,
    ));
}

#[test]
fn constant_field_offset_is_disjoint_from_earlier_constant_range() {
    let base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(101)), 4),
    };
    let first_field = CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    );
    let third_field = base.offset_by_int32_elements(Bitvector32Term::Constant(2));

    assert!(Assumptions::new().ranges_proven_disjoint_from_pointer(&[first_field], &third_field));
}

#[test]
fn bounded_separation_uses_order_fact_across_equivalent_snapshots() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(102)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(103)), 4),
    };
    let len_cell = owner.clone();
    let cap_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let plain = CMemory::new();
    let cached = CMemory::new().store(
        Pointer {
            block: "local:cache".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        int32(0),
    );
    let query_len = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(plain.clone()),
        Box::new(len_cell.clone()),
    );
    let query_cap = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(plain),
        Box::new(cap_cell.clone()),
    );
    let fact_len = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(cached.clone()),
        Box::new(len_cell),
    );
    let fact_cap =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(cached), Box::new(cap_cell));
    let owner_range = CMemoryRange::new(
        owner.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
    );
    let owned_data_range = CMemoryRange::new(data.clone(), Bitvector32Term::Constant(0), query_cap);
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::signed_less_equal(fact_len, fact_cap), true)
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(owner_range),
            right: CResource::Memory(owned_data_range),
        });

    assert!(assumptions.ranges_proven_disjoint_from_pointer(
        &[CMemoryRange::new(
            data,
            Bitvector32Term::Constant(0),
            query_len,
        )],
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
    ));
}

#[test]
fn covering_disjoint_fact_handles_shifted_mutable_range() {
    let n = Variable(83);
    let k = Variable(84);
    let n_bits = Bitvector32Term::Variable(n);
    let k_bits = Bitvector32Term::Variable(k);
    let before_memory = CMemory::new();
    let after_memory = CMemory::new();
    let dst_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(85)), 4),
    };
    let src_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(86)), 4),
    };
    let src_cell = src_base.offset_by_int32_elements(k_bits.clone());
    let shifted_dst = dst_base.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(k_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k_bits, n_bits.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: dst_base,
            left_start: Bitvector32Term::Constant(0),
            left_end: n_bits.clone(),
            right_base: src_base,
            right_start: Bitvector32Term::Constant(0),
            right_end: n_bits.clone(),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before: before_memory.clone(),
            after: after_memory.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                shifted_dst,
                Bitvector32Term::Constant(0),
                Bitvector32Term::subtract(n_bits, Bitvector32Term::Constant(1)),
            )],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after_memory),
                Box::new(src_cell.clone())
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before_memory),
                Box::new(src_cell)
            ),
        ),
        true,
    )));
}

#[test]
fn atomic_condition_fact_transport_uses_certified_effect_summary() {
    let before = CMemory::new()
        .with_block("stable", 4)
        .with_block("mutated", 4);
    let after = before.clone().with_block("call-havoc:0", 0);
    let stable = Pointer {
        block: "stable".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mutated = Pointer {
        block: "mutated".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(stable.clone()),
            ),
            Bitvector32Term::Constant(7),
        ),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(Proposition::CMemoryEffectSummary {
        before: before.clone(),
        after: after.clone(),
        mutable_ranges: vec![CMemoryRange::new(
            mutated,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    });

    let theorem = prove_c_condition_fact_transport(&fact, &after, &assumptions)
        .expect("the framed load should transport");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(after),
                        Box::new(stable)
                    ),
                    Bitvector32Term::Constant(7),
                ),
                true,
            )),
        )
    );
}

#[test]
fn memory_load_equality_does_not_ignore_loop_havoc_identity() {
    let before = CMemory::new();
    let after = before.clone().with_block("havoc:0", 0);
    let pointer = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let equality = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after),
                Box::new(pointer.clone()),
            ),
            Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(before), Box::new(pointer)),
        ),
        true,
    );

    assert!(
        !Assumptions::new().proves(&equality),
        "a havoced snapshot requires explicit frame evidence"
    );
}

#[test]
fn atomic_condition_fact_transport_ignores_distinct_materialized_cell() {
    let before = CMemory::new()
        .with_block("arg-memory", 8)
        .with_block("call-havoc:0", 0);
    let preserved = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let materialized = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let after = before
        .clone()
        .store(materialized, CValue::Int32(Bitvector32Term::Constant(9)));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(preserved.clone()),
            ),
            Bitvector32Term::Constant(7),
        ),
        true,
    );

    let theorem = prove_c_condition_fact_transport(&fact, &after, &Assumptions::new())
        .expect("a distinct materialized cell must not change the framed load");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(after),
                        Box::new(preserved)
                    ),
                    Bitvector32Term::Constant(7),
                ),
                true,
            )),
        )
    );
}

#[test]
fn atomic_condition_fact_transport_preserves_pointer_offset_equality() {
    let before = CMemory::new()
        .with_block("stable", 4)
        .with_block("mutated", 4);
    let after = before.clone().with_block("call-havoc:0", 0);
    let stable = Pointer {
        block: "stable".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mutated = Pointer {
        block: "mutated".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let expected = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(345)), 4);
    let fact = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::scale_int32(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(before.clone()),
                    Box::new(stable.clone()),
                ),
                4,
            ),
            expected.clone(),
        ),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(Proposition::CMemoryEffectSummary {
        before,
        after: after.clone(),
        mutable_ranges: vec![CMemoryRange::new(
            mutated,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    });

    let theorem = prove_c_condition_fact_transport(&fact, &after, &assumptions)
        .expect("the framed pointer-valued field should transport");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(
                    PointerOffsetTerm::scale_int32(
                        Bitvector32Term::MemoryLoad(
                            crate::kernel::intern_c_memory(after),
                            Box::new(stable)
                        ),
                        4,
                    ),
                    expected,
                ),
                true,
            )),
        )
    );
}

#[test]
fn equality_fact_matching_transports_both_pointer_offset_endpoints() {
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let local = Pointer {
        block: "local:value".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new()
        .with_block("arg-memory", 8)
        .with_block("local:value", 4);
    let after = before
        .clone()
        .store(local, CValue::Int32(Bitvector32Term::Constant(7)));
    let load_offset = |memory: &CMemory, pointer: &Pointer| {
        PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(pointer.clone()),
            ),
            4,
        )
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            load_offset(&before, &left),
            load_offset(&before, &right),
        ),
        true,
    );
    let target = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            load_offset(&after, &left),
            load_offset(&after, &right),
        ),
        true,
    );
    let assumptions = Assumptions::new().assume_proposition(fact);

    assert!(assumptions.proves(&target));
}

#[test]
fn memory_load_equality_combines_equal_pointer_base_and_zero_index() {
    let memory = CMemory::new().with_block("arg-memory", 64);
    let owner = Bitvector32Term::Variable(Variable(90));
    let data = Bitvector32Term::Variable(Variable(91));
    let owner_offset = PointerOffsetTerm::scale_int32(owner, 4);
    let data_field = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(owner_offset.clone(), PointerOffsetTerm::Constant(8)),
    };
    let pos_field = Pointer {
        block: "arg-memory".into(),
        offset: owner_offset,
    };
    let data_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(data_field),
    );
    let pos_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(pos_field),
    );
    let indexed = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_load.clone(), 4),
            PointerOffsetTerm::scale_int32(pos_load.clone(), 4),
        ),
    };
    let direct = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data.clone(), 4),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(
                PointerOffsetTerm::scale_int32(data_load, 4),
                PointerOffsetTerm::scale_int32(data, 4),
            ),
            true,
        ))
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(pos_load, Bitvector32Term::Constant(0)),
            true,
        ));
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(indexed),
            ),
            Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(memory), Box::new(direct)),
        ),
        true,
    );

    assert!(assumptions.proves(&target));
}

#[test]
fn pointer_offset_equality_combines_equal_base_and_zero_index() {
    let base = Bitvector32Term::Variable(Variable(90));
    let target = Bitvector32Term::Variable(Variable(91));
    let index = Bitvector32Term::Variable(Variable(92));
    let base_offset = PointerOffsetTerm::scale_int32(base, 4);
    let target_offset = PointerOffsetTerm::scale_int32(target, 4);
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::pointer_offset_equal(base_offset.clone(), target_offset.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::add(base_offset, PointerOffsetTerm::scale_int32(index, 4),),
            target_offset,
        )),
        Some(true),
    );
}

#[test]
fn atomic_condition_fact_transport_uses_exact_separate_range() {
    let before = CMemory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(91)), 4),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(left.clone()),
            ),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                left.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                right.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                right,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_transport(&fact, &after, &assumptions)
        .expect("the exact separate range should frame the left load");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(after),
                        Box::new(left)
                    ),
                    Bitvector32Term::Constant(0),
                ),
                true,
            )),
        )
    );
}

#[test]
fn direct_condition_transport_uses_relative_separate_range() {
    let before = CMemory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let data_index_from_owner = Bitvector32Term::subtract(
        Bitvector32Term::Variable(Variable(93)),
        Bitvector32Term::Variable(Variable(92)),
    );
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(data.clone()),
            ),
            Bitvector32Term::Variable(Variable(94)),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_than(
                data_index_from_owner.clone(),
                Bitvector32Term::add(data_index_from_owner.clone(), Bitvector32Term::Constant(2)),
            ),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                data_index_from_owner.clone(),
                Bitvector32Term::add(data_index_from_owner, Bitvector32Term::Constant(2)),
            )),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                owner,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("relative exact separation should directly frame the data load");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(after),
                        Box::new(data)
                    ),
                    Bitvector32Term::Variable(Variable(94)),
                ),
                true,
            )),
        )
    );
}

#[test]
fn direct_condition_transport_uses_indexed_relative_separate_range() {
    let before = CMemory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let data_one = data.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let data_index_from_owner = Bitvector32Term::subtract(
        Bitvector32Term::Variable(Variable(93)),
        Bitvector32Term::Variable(Variable(92)),
    );
    let length = Bitvector32Term::Variable(Variable(95));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(data_one.clone()),
            ),
            Bitvector32Term::Variable(Variable(94)),
        ),
        true,
    );
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                data_index_from_owner.clone(),
                Bitvector32Term::add(data_index_from_owner, length),
            )),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                owner,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("an indexed pointer in a relative separate range should be directly framed");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(after),
                        Box::new(data_one)
                    ),
                    Bitvector32Term::Variable(Variable(94)),
                ),
                true,
            )),
        )
    );
}

#[test]
fn condition_fact_transport_preserves_arithmetic_structure() {
    let before = CMemory::new().with_block("stable", 4);
    let after = before.clone().with_block("local:value", 4);
    let stable = Pointer {
        block: "stable".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::add(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(before),
                    Box::new(stable.clone()),
                ),
                Bitvector32Term::Constant(1),
            ),
            Bitvector32Term::Constant(8),
        ),
        true,
    );

    let theorem = prove_c_condition_fact_transport(&fact, &after, &Assumptions::new())
        .expect("arithmetic around a framed load should transport structurally");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::add(
                        Bitvector32Term::MemoryLoad(
                            crate::kernel::intern_c_memory(after),
                            Box::new(stable)
                        ),
                        Bitvector32Term::Constant(1),
                    ),
                    Bitvector32Term::Constant(8),
                ),
                true,
            )),
        )
    );
}

#[test]
fn adjacent_disjoint_fact_ranges_cover_larger_disjoint_goal() {
    let n_bits = Bitvector32Term::Variable(Variable(87));
    let p_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p_plus_one = p_base.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let q_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(88)), 4),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: p_base.clone(),
            left_start: Bitvector32Term::Constant(0),
            left_end: Bitvector32Term::Constant(1),
            right_base: q_base.clone(),
            right_start: Bitvector32Term::Constant(0),
            right_end: n_bits.clone(),
        })
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: p_plus_one,
            left_start: Bitvector32Term::Constant(0),
            left_end: Bitvector32Term::Constant(2),
            right_base: q_base.clone(),
            right_start: Bitvector32Term::Constant(0),
            right_end: n_bits.clone(),
        });

    assert!(assumptions.proves(&Proposition::CMemoryDisjoint {
        left_base: p_base,
        left_start: Bitvector32Term::Constant(0),
        left_end: Bitvector32Term::Constant(2),
        right_base: q_base,
        right_start: Bitvector32Term::Constant(0),
        right_end: n_bits,
    }));
}

#[test]
fn constant_non_overlapping_ranges_on_one_base_are_separate() {
    let base = Pointer {
        block: "object".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left = CResource::Memory(CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    let right = CResource::Memory(CMemoryRange::new(
        base,
        Bitvector32Term::Constant(2),
        Bitvector32Term::Constant(4),
    ));

    assert!(Assumptions::new().proves(&Proposition::CResourceSeparate {
        left: left.clone(),
        right: right.clone(),
    }));
    assert!(Assumptions::new().proves(&Proposition::CResourceSeparate {
        left: right,
        right: left,
    }));
}

#[test]
fn symbolic_disjoint_fact_proves_itself() {
    let n_bits = Bitvector32Term::Variable(Variable(89));
    let p_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let q_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4),
    };
    let fact = Proposition::CMemoryDisjoint {
        left_base: p_base,
        left_start: Bitvector32Term::Constant(0),
        left_end: n_bits.clone(),
        right_base: q_base,
        right_start: Bitvector32Term::Constant(0),
        right_end: n_bits,
    };
    let assumptions = Assumptions::new().assume_proposition(fact.clone());

    assert!(assumptions.proves(&fact));
}

#[test]
fn while_invariant_rule_proves_symbolic_loop_exit_fact() {
    let i = Variable(71);
    let n = Variable(72);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let state = CState::new()
        .with_local("i", int32(i_bits.clone()))
        .with_local("n", int32(n_bits.clone()));
    let condition = c_less_than(c_variable("i"), c_variable("n"));
    let body = c_assign("i", c_add(c_variable("i"), c_int32_literal(1)));
    let invariant = vec![
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(i_bits.clone(), n_bits.clone()),
            true,
        ),
    ];
    let assumptions = invariant
        .iter()
        .cloned()
        .fold(Assumptions::new(), Assumptions::assume_proposition)
        .assume_condition(
            ConditionTerm::signed_less_equal(
                n_bits.clone(),
                Bitvector32Term::Constant(i32::MAX as u32),
            ),
            true,
        );
    let theorem = prove_c_while_invariant_rule(
        state,
        condition,
        invariant,
        body,
        assumptions,
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(
                    incremented.clone(),
                    Bitvector32Term::Constant(0),
                ),
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(incremented, n_bits.clone()),
                true,
            ),
        ],
        Proposition::ConditionIs(ConditionTerm::equal(i_bits, n_bits), true),
    )
    .expect("invariant rule should prove preservation and i == n on loop exit");

    assert!(matches!(theorem.proposition(), Proposition::Implies(_, _)));
}

/// Pins the unsoundness that `prove_c_while_invariant_rule` is fenced for.
///
/// The rule's acceptance does not depend on the body at all: it matches the
/// body's post-state as `CStatementOutcome::Normal(_)`, throws it away, and
/// discharges `preserved` against the *pre-body* assumption context. So one
/// and the same `preserved` list -- which describes the step `i := i + 1` --
/// is accepted both for a body that increments `i` and for a body that zeroes
/// it.
///
/// If someone teaches the rule to check the invariant at the body's
/// post-state, the second case below must start failing; replace this test
/// with a positive preservation test at that point.
#[test]
fn while_invariant_rule_ignores_what_the_body_does_to_the_invariant() {
    let i = Variable(171);
    let n = Variable(172);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let state = CState::new()
        .with_local("i", int32(i_bits.clone()))
        .with_local("n", int32(n_bits.clone()));
    let condition = c_less_than(c_variable("i"), c_variable("n"));
    let invariant = vec![
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(i_bits.clone(), n_bits.clone()),
            true,
        ),
    ];
    let assumptions = invariant
        .iter()
        .cloned()
        .fold(Assumptions::new(), Assumptions::assume_proposition)
        .assume_condition(
            ConditionTerm::signed_less_equal(
                n_bits.clone(),
                Bitvector32Term::Constant(i32::MAX as u32),
            ),
            true,
        );
    // `preserved` describes the state after the step `i := i + 1`.
    let preserved = vec![
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(incremented.clone(), Bitvector32Term::Constant(0)),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(incremented, n_bits.clone()),
            true,
        ),
    ];
    let postcondition = Proposition::ConditionIs(ConditionTerm::equal(i_bits, n_bits), true);

    let prove_with_body = |body: CStatement| {
        prove_c_while_invariant_rule(
            state.clone(),
            condition.clone(),
            invariant.clone(),
            body,
            assumptions.clone(),
            preserved.clone(),
            postcondition.clone(),
        )
    };

    // The body that `preserved` actually describes.
    assert!(
        prove_with_body(c_assign("i", c_add(c_variable("i"), c_int32_literal(1)))).is_some(),
        "the incrementing body should be accepted"
    );
    // A body that sets `i` to 0, so after the step `i` is 0 rather than
    // `i + 1`. The rule accepts the unchanged `preserved` anyway, which is
    // exactly the gap the fence exists to contain.
    assert!(
        prove_with_body(c_assign("i", c_int32_literal(0))).is_some(),
        "the fenced rule is expected to accept a `preserved` list the body does \
         not establish; if it now rejects it, the rule learned to look at the \
         body's post-state and the fence should be revisited"
    );
}

/// The while-invariant rule must stay unreachable from outside the kernel.
///
/// The real guarantee is the `#[cfg(test)]` + `pub(super)` declaration in
/// `api.rs`, which `kernel/mod.rs`'s `pub use api::*` cannot widen. This test
/// pins that declaration so re-exporting the rule fails the gate rather than
/// silently adding an unsound axiom to the trusted base.
#[test]
fn while_invariant_rule_is_not_exported_from_the_kernel() {
    let api_source = include_str!("api.rs");

    assert!(
        !api_source.contains("pub fn prove_c_while_invariant_rule"),
        "prove_c_while_invariant_rule must not be publicly exported: it is an \
         unsound partial while rule (see its doc comment in api.rs)"
    );
    assert!(
        api_source.contains("#[cfg(test)]\npub(super) fn prove_c_while_invariant_rule("),
        "prove_c_while_invariant_rule must stay declared as \
         `#[cfg(test)] pub(super) fn` so it does not exist in a release build"
    );
}

#[test]
fn same_block_frame_uses_symbolic_offset_inequality() {
    let i = Variable(73);
    let j = Variable(74);
    let i_bits = Bitvector32Term::Variable(i);
    let j_bits = Bitvector32Term::Variable(j);
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let stored_pointer = base.offset_by_int32_elements(i_bits);
    let loaded_pointer = base.offset_by_int32_elements(j_bits);
    let memory = CMemory::new().store(loaded_pointer.clone(), int32(42));
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::pointer_offset_equal(
            stored_pointer.offset.clone(),
            loaded_pointer.offset.clone(),
        ),
        false,
    );
    let theorem = prove_memory_load_after_store_distinct_under_assumptions(
        memory.clone(),
        stored_pointer.clone(),
        int32(9),
        loaded_pointer.clone(),
        assumptions,
    )
    .expect("i != j should prove store p[i] preserves load p[j]");

    assert_eq!(
        theorem.proposition().peel_implications(),
        &Proposition::CMemoryLoads {
            memory: memory.store(stored_pointer, int32(9)),
            pointer: loaded_pointer,
            outcome: CExpressionOutcome::Value(int32(42)),
        }
    );
}

#[test]
fn same_symbolic_base_constant_offsets_are_distinct() {
    let base = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4);
    let first = Pointer {
        block: "arg-memory".into(),
        offset: base.clone(),
    };
    let second = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(base, PointerOffsetTerm::Constant(4)),
    };

    assert!(pointers_proven_distinct(
        &first,
        &second,
        &Assumptions::new()
    ));
}

#[test]
fn additive_equality_cancellation_feeds_range_contradictions() {
    let base = Bitvector32Term::Variable(Variable(91));
    let index = Bitvector32Term::Variable(Variable(92));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::equal(Bitvector32Term::add(base.clone(), index.clone()), base),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(index, Bitvector32Term::Constant(1)),
            true,
        );

    assert!(assumptions.is_inconsistent());
}

#[test]
fn equality_facts_close_signed_order_contradiction_cycles() {
    let left = Bitvector32Term::Variable(Variable(193));
    let right = Bitvector32Term::Variable(Variable(194));
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::equal(left.clone(), right.clone()), true)
        .assume_condition(
            ConditionTerm::signed_less_than(left, Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(right, Bitvector32Term::Constant(1)),
            true,
        );

    assert!(assumptions.is_inconsistent());
}

/// Memory-load lowering splits on every cell it cannot resolve, so a
/// quantified invariant over an owned array produces one path per owner field
/// guarded by "this element aliases that field". Those paths are vacuous, but
/// only the index bound assumed *inside* the quantifier rules them out, and
/// the splitter never sees it. The invariant closer does, so the contradiction
/// has to be visible there — and only there: with the bound dropped the guard
/// is genuinely satisfiable and must stay consistent.
#[test]
fn separation_refutes_an_alias_guard_exactly_when_the_index_is_in_range() {
    let block: PointerBlock = "arg-memory".into();
    let owner_offset = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(801)), 4);
    let data = Bitvector32Term::Variable(Variable(802));
    let capacity = Bitvector32Term::Variable(Variable(803));
    let index = Bitvector32Term::Variable(Variable(804));
    let owner = Pointer {
        block: block.clone(),
        offset: owner_offset.clone(),
    };
    let data_base = Pointer {
        block,
        offset: PointerOffsetTerm::scale_int32(data.clone(), 4),
    };
    // The element address the alias guard claims equals the `cap` field's.
    let element = PointerOffsetTerm::add(
        PointerOffsetTerm::scale_int32(data, 4),
        PointerOffsetTerm::scale_int32(index.clone(), 4),
    );
    let capacity_field = PointerOffsetTerm::add(owner_offset, PointerOffsetTerm::Constant(4));
    let unbounded = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(owner, 1, 2)),
            right: CResource::Memory(memory_range(data_base, 0, capacity.clone())),
        })
        .assume_condition(
            ConditionTerm::pointer_offset_equal(element, capacity_field),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        );

    assert!(!unbounded.is_inconsistent());
    assert!(
        unbounded
            .assume_condition(ConditionTerm::signed_less_than(index, capacity), true)
            .is_inconsistent()
    );
}

/// A loop back edge re-proves `forall k < b + 1, P(k)` from an invariant that
/// only covers `k < b`. The missing step is one case split, not a theory: `k`
/// is below `b` or equal to it, and the two halves are discharged by facts
/// that are already present. Replay must accept the same split and must reject
/// it when the bound that licensed it is gone.
#[test]
fn an_assumed_upper_bound_splits_a_goal_at_its_final_index() {
    let bound = Bitvector32Term::Variable(Variable(811));
    let index = Bitvector32Term::Variable(Variable(812));
    // Holds strictly below the bound (by the quantified fact) and at it (by
    // reflexivity); neither half's justification covers the other.
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(index.clone(), bound.clone()),
        true,
    );
    let context = Assumptions::new().assume_condition(
        ConditionTerm::signed_less_than(
            index.clone(),
            Bitvector32Term::add(bound.clone(), Bitvector32Term::Constant(1)),
        ),
        true,
    );

    let derivation = context
        .derive_proposition(&goal)
        .expect("the split closes the goal");
    assert!(matches!(
        derivation.rule,
        PropositionDerivationRule::UpperBoundSplit { .. }
    ));
    assert!(derivation.replay(&context));
    // Without the bound there is no split to license and nothing to prove.
    let unbounded = Assumptions::new();
    assert!(!derivation.replay(&unbounded));
    assert!(unbounded.derive_proposition(&goal).is_none());
}

#[test]
fn equality_to_constant_feeds_signed_order_decisions() {
    let value = Bitvector32Term::Variable(Variable(93));
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::equal(value.clone(), Bitvector32Term::Constant(1)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(0),
            value.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            value,
            Bitvector32Term::Constant(1),
        )),
        Some(true)
    );
}

#[test]
fn range_fold_simplifies_empty_and_one_step_ranges() {
    let accumulator = Variable(93);
    let item = Variable(94);
    let x = Bitvector32Term::Variable(Variable(95));
    let body = Bitvector32Term::add(Bitvector32Term::Variable(accumulator), x.clone());

    assert_eq!(
        Bitvector32Term::range_fold(
            Bitvector32Term::Constant(4),
            Bitvector32Term::Constant(4),
            Bitvector32Term::Constant(7),
            accumulator,
            item,
            body.clone(),
        ),
        Bitvector32Term::Constant(7)
    );

    assert_eq!(
        Bitvector32Term::range_fold(
            Bitvector32Term::Variable(Variable(96)),
            Bitvector32Term::add(
                Bitvector32Term::Variable(Variable(96)),
                Bitvector32Term::Constant(1)
            ),
            Bitvector32Term::Constant(7),
            accumulator,
            item,
            body,
        ),
        Bitvector32Term::add(Bitvector32Term::Constant(7), x)
    );
}

#[test]
fn count_shaped_range_fold_split_is_proven_equal() {
    let lo = Bitvector32Term::Variable(Variable(97));
    let mid = Bitvector32Term::Variable(Variable(98));
    let hi = Bitvector32Term::Variable(Variable(99));
    let x = Bitvector32Term::Variable(Variable(100));
    let accumulator = Variable(101);
    let item = Variable(102);
    let contribution = Bitvector32Term::if_then_else(
        ConditionTerm::equal(Bitvector32Term::Variable(item), x),
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(0),
    );
    let body = Bitvector32Term::add(Bitvector32Term::Variable(accumulator), contribution);
    let count = |start: Bitvector32Term, end: Bitvector32Term| {
        Bitvector32Term::range_fold(
            start,
            end,
            Bitvector32Term::Constant(0),
            accumulator,
            item,
            body.clone(),
        )
    };
    let whole = count(lo.clone(), hi.clone());
    let split = Bitvector32Term::add(
        count(lo.clone(), mid.clone()),
        count(mid.clone(), hi.clone()),
    );

    // The split identity fold(lo,hi) = fold(lo,mid) + fold(mid,hi) only
    // holds for lo <= mid <= hi. Without that ordering it is unsound
    // (half-open ranges make an out-of-order mid over- or under-count),
    // so the rule must not fire on unconstrained bounds.
    assert!(!Assumptions::new().proves(&Proposition::ConditionIs(
        ConditionTerm::equal(whole.clone(), split.clone()),
        true,
    )));

    let ordered = Assumptions::new()
        .assume_condition(ConditionTerm::signed_less_equal(lo, mid.clone()), true)
        .assume_condition(ConditionTerm::signed_less_equal(mid, hi), true);
    assert!(ordered.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(whole, split),
        true,
    )));
}

#[test]
fn symbolic_store_invalidates_only_possible_aliasing_cells() {
    let i = Variable(81);
    let i_bits = Bitvector32Term::Variable(i);
    let concrete_cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let symbolic_cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(i_bits.clone()),
            byte_width: 4,
        },
    };
    let memory = CMemory::new()
        .with_block("array", 12)
        .store(concrete_cell.clone(), int32(42));

    let aliased = memory
        .without_possible_aliasing_cells(&symbolic_cell, &Assumptions::new())
        .store(symbolic_cell.clone(), int32(7));
    assert_eq!(aliased.known_value(&concrete_cell), None);

    let distinct_assumptions = Assumptions::new().assume_condition(
        ConditionTerm::equal(i_bits, Bitvector32Term::Constant(1)),
        false,
    );
    let distinct = memory
        .without_possible_aliasing_cells(&symbolic_cell, &distinct_assumptions)
        .store(symbolic_cell, int32(7));
    assert_eq!(distinct.known_value(&concrete_cell), Some(int32(42)));
}

#[test]
fn memory_resolution_alias_check_uses_explicit_separation() {
    let left_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4),
    };
    let right_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(91)), 4),
    };
    let assumptions = Assumptions::new().assume_proposition(Proposition::CResourceSeparate {
        left: CResource::Memory(memory_range(left_base.clone(), 0, 4)),
        right: CResource::Memory(memory_range(right_base.clone(), 0, 4)),
    });

    assert!(pointers_proven_distinct_for_memory_resolution(
        &left_base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &right_base.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));
    assert!(!pointers_proven_equal_for_memory_resolution(
        &left_base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &right_base.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));

    let right_start = Bitvector32Term::subtract(
        Bitvector32Term::Variable(Variable(91)),
        Bitvector32Term::Variable(Variable(90)),
    );
    let normalized_assumptions =
        Assumptions::new().assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(left_base.clone(), 0, 4)),
            right: CResource::Memory(memory_range(
                left_base.clone(),
                right_start.clone(),
                Bitvector32Term::add(right_start, Bitvector32Term::Constant(4)),
            )),
        });
    assert!(pointers_proven_distinct_for_memory_resolution(
        &left_base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &right_base.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &normalized_assumptions,
    ));
}

#[test]
fn memory_resolution_alias_check_uses_exact_transitive_range_bounds() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let index = Bitvector32Term::Variable(Variable(94));
    let length = Bitvector32Term::Variable(Variable(95));
    let capacity = Bitvector32Term::Variable(Variable(96));
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(owner.clone(), 0, 4)),
            right: CResource::Memory(memory_range(data.clone(), 0, capacity.clone())),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(length, capacity), true);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &data.offset_by_int32_elements(index),
        &assumptions,
    ));

    let incremented = Bitvector32Term::add(
        Bitvector32Term::Variable(Variable(94)),
        Bitvector32Term::Constant(1),
    );
    let incremented_assumptions = assumptions
        .assume_condition(
            ConditionTerm::signed_add_overflows(
                Bitvector32Term::Variable(Variable(94)),
                Bitvector32Term::Constant(1),
            ),
            false,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(
                incremented.clone(),
                Bitvector32Term::Variable(Variable(96)),
            ),
            true,
        );
    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &data.offset_by_int32_elements(incremented),
        &incremented_assumptions,
    ));
}

#[test]
fn memory_resolution_alias_check_uses_strict_indices_across_equal_loaded_bases() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(97)), 4),
    };
    let data_cell = owner.offset_by_bytes(8);
    let before = CMemory::new();
    let after = before.clone().with_block("local:temporary", 4);
    let data_before = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(data_cell.clone()),
    );
    let data_after =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(data_cell));
    let length =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(before), Box::new(owner));
    let index = Bitvector32Term::subtract(length.clone(), Bitvector32Term::Constant(1));
    let indexed = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_after.clone(), 4),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        ),
    };
    let terminator = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_before.clone(), 4),
            PointerOffsetTerm::scale_int32(length.clone(), 4),
        ),
    };
    let assumptions = Assumptions::new()
        .assume_condition(ConditionTerm::equal(data_after, data_before), true)
        .assume_condition(ConditionTerm::signed_less_than(index, length), true);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &indexed,
        &terminator,
        &assumptions,
    ));
}

#[test]
fn memory_resolution_alias_check_transports_unchanged_field_loads() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let len_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let before = CMemory::new();
    let after = before.clone().store(len_cell, int32(7));
    let data_before = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(data_cell.clone()),
    );
    let data_after =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(data_cell));
    let zero_index = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before),
        Box::new(owner.clone()),
    );
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_before, 4),
            PointerOffsetTerm::scale_int32(zero_index.clone(), 4),
        ),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data_after, 4),
    };
    let assumptions = Assumptions::new().assume_condition(
        ConditionTerm::equal(zero_index, Bitvector32Term::Constant(0)),
        true,
    );

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));
    assert!(pointers_proven_equal_for_memory_resolution(
        &left,
        &right,
        &assumptions,
    ));
}

#[test]
fn memory_resolution_separation_transports_unchanged_range_base_loads() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let len_cell = owner.clone();
    let data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let before = CMemory::new();
    let after = before.clone().store(len_cell, int32(7));
    let data_before = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(data_cell.clone()),
    );
    let data_after =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(data_cell));
    let length = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(owner.clone()),
    );
    let capacity = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(owner.offset_by_int32_elements(Bitvector32Term::Constant(1))),
    );
    let index = Bitvector32Term::subtract(length.clone(), Bitvector32Term::Constant(1));
    let data_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data_before, 4),
    };
    let indexed_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_after.clone(), 4),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        ),
    };
    let assumptions = Assumptions::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(owner.clone(), 0, 4)),
            right: CResource::Memory(CMemoryRange::new(
                data_base.clone(),
                Bitvector32Term::Constant(0),
                capacity.clone(),
            )),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(length, capacity), true);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner,
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));
    assert!(pointers_proven_equal_for_memory_resolution(
        &data_base,
        &Pointer {
            block: "arg-memory".into(),
            offset: PointerOffsetTerm::scale_int32(data_after, 4),
        },
        &assumptions,
    ));
    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &indexed_data,
        &assumptions,
    ));
}

#[test]
fn incremented_materialized_index_transports_its_nonnegative_bound() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(931)), 4),
    };
    let local_index = Pointer {
        block: "local:index".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new();
    let old_len = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(owner.clone()),
    );
    let materialized = before
        .with_block("local:index", 4)
        .store(local_index.clone(), int32(old_len.clone()));
    let materialized_index = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(materialized),
        Box::new(local_index),
    );
    let incremented = Bitvector32Term::add(materialized_index, Bitvector32Term::Constant(1));
    let upper = Bitvector32Term::Variable(Variable(932));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), old_len.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(old_len, upper), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            incremented.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(0),
            incremented,
        )),
        Some(true)
    );
}

#[test]
fn assumptions_resolve_materialized_symbolic_memory_load_aliases() {
    let k = Variable(75);
    let k_bits = Bitvector32Term::Variable(k);
    let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(k_bits),
            byte_width: 4,
        },
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(base_memory.clone()),
                        Box::new(pointer),
                    )),
                )
            });

    for (index, pointer) in src_pointers.into_iter().enumerate() {
        let assumptions = Assumptions::new()
            .assume_condition(
                ConditionTerm::pointer_offset_equal(
                    symbolic_src.offset.clone(),
                    pointer.offset.clone(),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(k),
                    Bitvector32Term::Constant(index as u32),
                ),
                true,
            );

        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(base_memory.clone()),
                    Box::new(pointer)
                ),
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(materialized_memory.clone()),
                    Box::new(symbolic_src.clone()),
                ),
            ),
            true,
        )));
    }
}

#[test]
fn assumptions_reject_forall_based_on_a_shadowed_materialized_load_index() {
    let k = Variable(76);
    let k_bits = Bitvector32Term::Variable(k);
    let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(k_bits.clone()),
            byte_width: 4,
        },
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(base_memory.clone()),
                        Box::new(pointer),
                    )),
                )
            });
    let body = Proposition::Implies(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(k_bits.clone(), Bitvector32Term::Constant(3)),
                true,
            )),
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(base_memory),
                    Box::new(src_pointers[1].clone()),
                ),
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(materialized_memory),
                    Box::new(symbolic_src.clone()),
                ),
            ),
            true,
        )),
    );
    let proposition = Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(
                symbolic_src.offset.clone(),
                src_pointers[0].offset.clone(),
            ),
            false,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(k_bits.clone(), Bitvector32Term::Constant(0)),
                false,
            )),
            Box::new(Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::pointer_offset_equal(
                        symbolic_src.offset,
                        src_pointers[1].offset.clone(),
                    ),
                    true,
                )),
                Box::new(Proposition::Implies(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::equal(k_bits, Bitvector32Term::Constant(1)),
                        true,
                    )),
                    Box::new(Proposition::ForAll {
                        var: k,
                        sort: Sort::CInt32,
                        body: Box::new(body),
                    }),
                )),
            )),
        )),
    );

    assert!(!Assumptions::new().proves(&proposition));
}

#[test]
fn assumptions_reject_forall_based_on_a_shadowed_prefix_index() {
    let i = Variable(82);
    let k = Variable(83);
    let i_bits = Bitvector32Term::Variable(i);
    let k_bits = Bitvector32Term::Variable(k);
    let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(k_bits.clone()),
            byte_width: 4,
        },
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(base_memory.clone()),
                        Box::new(pointer),
                    )),
                )
            });
    let body = Proposition::Implies(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(
                    k_bits.clone(),
                    Bitvector32Term::Add(
                        Box::new(i_bits.clone()),
                        Box::new(Bitvector32Term::Constant(1)),
                    ),
                ),
                true,
            )),
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(base_memory),
                    Box::new(src_pointers[1].clone()),
                ),
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(materialized_memory),
                    Box::new(symbolic_src.clone()),
                ),
            ),
            true,
        )),
    );
    let proposition = Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(i_bits.clone(), Bitvector32Term::Constant(1)),
            true,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(
                    symbolic_src.offset,
                    PointerOffsetTerm::Int32Scaled {
                        value: Box::new(i_bits.clone()),
                        byte_width: 4,
                    },
                ),
                true,
            )),
            Box::new(Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(k_bits, i_bits),
                    true,
                )),
                Box::new(Proposition::ForAll {
                    var: k,
                    sort: Sort::CInt32,
                    body: Box::new(body),
                }),
            )),
        )),
    );

    assert!(!Assumptions::new().proves(&proposition));
}

#[test]
fn local_declaration_allocates_stack_object_for_address_of() {
    let local_pointer = Pointer {
        block: "local:x".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new();
    let statement = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_assign("x", c_int32_literal(5)),
            c_return(c_load(c_addr_of("x"))),
        ),
    );
    let final_state = CState::new().with_local("x", int32(5)).with_memory(
        CMemory::new()
            .with_block("local:x", 4)
            .store(local_pointer, int32(5)),
    );
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), Assumptions::new())
        .expect("local declaration/address-of should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state,
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn symbolic_execution_stops_without_needed_overflow_fact() {
    let left = Variable(20);
    let right = Variable(21);
    let state = CState::new()
        .with_local("left", int32(Bitvector32Term::Variable(left)))
        .with_local("right", int32(Bitvector32Term::Variable(right)));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));

    assert!(prove_symbolic_c_execution(state, statement, Assumptions::new()).is_none());
}

#[test]
fn symbolic_execution_reports_branch_facts() {
    let a = Variable(24);
    let b = Variable(25);
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = c_max_state(int32(a_bits), int32(b_bits));
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), c_max_body(), Assumptions::new());

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(condition.clone(), true)]
    );
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition.clone(), true)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement: c_max_body(),
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Variable(b)),
                    state: state.clone(),
                },
            }),
        )
    );

    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(condition.clone(), false)]
    );
    assert_eq!(
        execution.paths()[1].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[1].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(condition, false)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement: c_max_body(),
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Variable(a)),
                    state,
                },
            }),
        )
    );
}

#[test]
fn symbolic_execution_reports_overflow_facts() {
    let left = Variable(26);
    let right = Variable(27);
    let left_bits = Bitvector32Term::Variable(left);
    let right_bits = Bitvector32Term::Variable(right);
    let state = CState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));
    let overflow = ConditionTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
    let execution =
        prove_symbolic_c_execution_paths(state.clone(), statement.clone(), Assumptions::new());

    assert_eq!(execution.paths().len(), 2);
    assert_eq!(
        execution.paths()[0].facts(),
        &[ExecutionPureFact::condition(overflow.clone(), false)]
    );
    assert_eq!(
        execution.paths()[0].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[0].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(overflow.clone(), false)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement: statement.clone(),
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Add(
                        Box::new(left_bits),
                        Box::new(right_bits)
                    )),
                    state: state.clone(),
                },
            }),
        )
    );

    assert_eq!(
        execution.paths()[1].facts(),
        &[ExecutionPureFact::condition(overflow.clone(), true)]
    );
    assert_eq!(
        execution.paths()[1].obligations(),
        &[] as &[ProofObligation]
    );
    assert_eq!(
        execution.paths()[1].theorem().proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(overflow, true)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            }),
        )
    );
}

#[test]
fn symbolic_execution_uses_no_overflow_fact() {
    let left = Variable(22);
    let right = Variable(23);
    let left_bits = Bitvector32Term::Variable(left);
    let right_bits = Bitvector32Term::Variable(right);
    let state = CState::new()
        .with_local("left", int32(left_bits.clone()))
        .with_local("right", int32(right_bits.clone()));
    let statement = c_return(c_add(c_variable("left"), c_variable("right")));
    let no_overflow = ConditionTerm::signed_add_overflows(left_bits.clone(), right_bits.clone());
    let assumptions = Assumptions::new().assume_condition(no_overflow.clone(), false);
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), assumptions)
        .expect("no-overflow fact should let symbolic add execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(no_overflow, false)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Add(
                        Box::new(left_bits),
                        Box::new(right_bits)
                    )),
                    state,
                },
            }),
        )
    );
}

#[test]
fn symbolic_increment_uses_int_max_bound_to_rule_out_overflow() {
    let x = Variable(65);
    let x_bits = Bitvector32Term::Variable(x);
    let state = CState::new().with_local("x", int32(x_bits.clone()));
    let statement = c_return(c_add(c_variable("x"), c_int32_literal(1)));
    let x_lt_int_max =
        ConditionTerm::signed_less_than(x_bits.clone(), Bitvector32Term::Constant(i32::MAX as u32));
    let assumptions = Assumptions::new().assume_condition(x_lt_int_max.clone(), true);
    let theorem = prove_symbolic_c_execution(state.clone(), statement.clone(), assumptions)
        .expect("x < INT_MAX should prove x + 1 does not overflow");

    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(Proposition::ConditionIs(x_lt_int_max, true)),
            Box::new(Proposition::CStatementExecutes {
                state: state.clone(),
                statement,
                outcome: CStatementOutcome::Return {
                    value: int32(Bitvector32Term::Add(
                        Box::new(x_bits),
                        Box::new(Bitvector32Term::Constant(1)),
                    )),
                    state,
                },
            }),
        )
    );
}

#[test]
fn symbolic_increment_uses_any_strict_upper_bound_to_rule_out_overflow() {
    let x_bits = Bitvector32Term::Variable(Variable(651));
    let upper_bits = Bitvector32Term::Variable(Variable(652));
    let assumption = ConditionTerm::signed_less_than(x_bits.clone(), upper_bits);
    let assumptions = Assumptions::new().assume_condition(assumption, true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            x_bits,
            Bitvector32Term::Constant(1),
        )),
        Some(false)
    );
}

#[test]
fn signed_addition_uses_both_operand_intervals_to_rule_out_overflow() {
    let left = Bitvector32Term::Variable(Variable(653));
    let right = Bitvector32Term::Variable(Variable(654));
    let million = Bitvector32Term::Constant(1_000_000);
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), left.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(left.clone(), million.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), right.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(right.clone(), million),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(left, right)),
        Some(false)
    );
}

#[test]
fn signed_addition_uses_negative_operand_intervals_to_rule_out_overflow() {
    let left = Bitvector32Term::Variable(Variable(655));
    let right = Bitvector32Term::Variable(Variable(656));
    let negative_million = Bitvector32Term::Constant((-1_000_000i32) as u32);
    let zero = Bitvector32Term::Constant(0);
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(negative_million.clone(), left.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(left.clone(), zero.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(negative_million, right.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_equal(right.clone(), zero), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(left, right)),
        Some(false)
    );
}

#[test]
fn signed_addition_ranges_nested_additions_only_when_each_level_is_safe() {
    let left = Bitvector32Term::Variable(Variable(657));
    let middle = Bitvector32Term::Variable(Variable(658));
    let right = Bitvector32Term::Variable(Variable(659));
    let upper = Bitvector32Term::Constant(700_000_000);
    let mut assumptions = Assumptions::new();
    for term in [&left, &middle, &right] {
        assumptions = assumptions
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), term.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(term.clone(), upper.clone()),
                true,
            );
    }
    let partial = Bitvector32Term::add(left, middle);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(partial.clone(), right)),
        Some(false)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            partial,
            Bitvector32Term::Constant(800_000_000),
        )),
        None
    );
}

#[test]
fn signed_addition_matches_interval_facts_across_unchanged_snapshots() {
    let cell = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(660)), 4),
    };
    let before = CMemory::new();
    let after = before.clone().with_block("local:temporary", 4);
    let before_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before),
        Box::new(cell.clone()),
    );
    let after_load =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(cell));
    let assumptions = Assumptions::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), before_load.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(before_load, Bitvector32Term::Constant(1_000_000)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_add_overflows(
            after_load.clone(),
            after_load,
        )),
        Some(false)
    );
}

#[test]
fn pointer_store_through_local_address_updates_named_lvalue() {
    let local_pointer = Pointer {
        block: "local:x".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let statement = c_seq(
        c_declare("x", CType::Int32),
        c_seq(
            c_store(c_addr_of("x"), c_int32_literal(5)),
            c_return(c_variable("x")),
        ),
    );
    let final_state = CState::new().with_local("x", int32(5)).with_memory(
        CMemory::new()
            .with_block("local:x", 4)
            .store(local_pointer, int32(5)),
    );
    let theorem = prove_symbolic_c_execution(CState::new(), statement.clone(), Assumptions::new())
        .expect("pointer store through local address should execute");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CStatementExecutes {
            state: CState::new(),
            statement,
            outcome: CStatementOutcome::Return {
                value: int32(5),
                state: final_state,
            },
        }
    );
}

#[test]
fn memory_load_store_are_native_theorems() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value = int32(7);
    let theorem =
        prove_memory_load_after_store_same(CMemory::new(), pointer.clone(), value.clone());

    assert_eq!(
        theorem.proposition(),
        &Proposition::CMemoryLoads {
            memory: CMemory::new().store(pointer.clone(), value.clone()),
            pointer,
            outcome: CExpressionOutcome::Value(value),
        }
    );
}

#[test]
fn store_preserves_distinct_memory_cell_frame() {
    let stored_pointer = Pointer {
        block: "left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let loaded_pointer = Pointer {
        block: "right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().store(loaded_pointer.clone(), int32(42));
    let theorem = prove_memory_load_after_store_other(
        memory.clone(),
        stored_pointer.clone(),
        int32(9),
        loaded_pointer.clone(),
    )
    .expect("store to distinct pointer should preserve loaded cell");

    assert_eq!(
        theorem.proposition(),
        &Proposition::CMemoryLoads {
            memory: memory.store(stored_pointer, int32(9)),
            pointer: loaded_pointer,
            outcome: CExpressionOutcome::Value(int32(42)),
        }
    );
}

#[test]
fn missing_memory_load_is_native_undefined_behavior() {
    let pointer = Pointer {
        block: "block".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let theorem = prove_memory_load(CMemory::new(), pointer.clone());

    assert_eq!(
        theorem.proposition(),
        &Proposition::CMemoryLoads {
            memory: CMemory::new(),
            pointer,
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
        }
    );
}

#[test]
fn contract_certification_checks_every_spec_lowering_path() {
    let base = Pointer {
        block: "local:contract-path-probe".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let queried = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::Variable(Variable(900_001)),
    };
    let memory = CMemory::new()
        .with_block(base.block.clone(), 8)
        .store(base, int32(0));
    let state = CState::new().with_memory(memory);
    let q = SpecExpression::CExpression(c_variable("q"));
    let function = c_function(
        CType::Int32,
        "contract_path_probe",
        vec![c_parameter("q", CType::Int32Pointer)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        vec![SpecProposition::MemoryLoadable {
            memory: SpecMemory::Current,
            base: q.clone(),
            start: SpecExpression::Value(int32(0)),
            end: SpecExpression::Value(int32(1)),
            element_width: 4,
        }],
        vec![SpecProposition::Comparison {
            left: SpecExpression::MemoryLoad {
                memory: SpecMemory::Current,
                pointer: Box::new(q),
                value_type: CType::Int32,
            },
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(0)),
        }],
        vec![],
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_proposition(0, 0),
        ],
        true,
    );
    let execution = prove_c_function_contract_execution_paths_with_environment(
        state,
        function.clone(),
        vec![c_pointer_value(queried)],
        vec![],
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let unverified = c_unverified_function_contract_claims(&function, &execution)
        .expect("the complete frontier should remain checkable");

    assert_eq!(unverified, vec![CFunctionContractClaimKey::Ensure(0)]);
}

#[test]
fn function_execution_theorem_retains_non_assumable_verification_conditions() {
    let verification_condition = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
    let conclusion = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let theorem = Theorem::new(wrap_proof_facts(
        conclusion,
        &Assumptions::new(),
        &[],
        &[ProofObligation::verification_condition(
            verification_condition.clone(),
        )],
    ));

    assert!(matches!(
        theorem.proposition(),
        Proposition::Implies(condition, _)
            if condition.as_ref() == &verification_condition
    ));
}

#[test]
fn symbolic_path_can_only_certify_its_exact_function_specification() {
    let function = c_function(
        CType::Int32,
        "exact_path",
        Vec::new(),
        c_return(c_int32_literal(0)),
    );
    let execution = prove_symbolic_c_function_execution_paths(
        CState::new(),
        function.clone(),
        Vec::new(),
        Assumptions::new(),
    );
    let false_specification = c_function_specification(
        CState::new(),
        Vec::new(),
        Vec::new(),
        CFunctionOutcome::Return {
            value: int32(1),
            state: CState::new(),
        },
    );

    assert!(
        prove_c_function_satisfies_specification_from_symbolic_path(
            function,
            false_specification,
            &execution.paths()[0],
        )
        .is_none()
    );
}

#[test]
fn verified_function_rule_applies_contract_without_executing_body() {
    let helper = c_function(
        CType::Int32,
        "opaque_helper",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_int32_literal(99)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("x")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let statement = c_seq(
        c_call_assign("result", "opaque_helper", vec![c_int32_literal(5)]),
        c_return(c_variable("result")),
    );
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement.clone(),
        Assumptions::new(),
        environment.clone(),
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution
        .paths()
        .first()
        .expect("opaque call should produce one path");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::CStatementVerifies {
        outcome: CStatementOutcome::Return { value, .. },
        ..
    } = proposition
    else {
        panic!("opaque call should produce an abstract return branch")
    };
    assert!(*value != int32(99));
    let propositions = path
        .facts()
        .iter()
        .map(|fact| fact.proposition().clone())
        .collect::<Vec<_>>();
    assert!(
        path.facts().iter().any(ExecutionPureFact::is_certified),
        "verified-call ensures should be marked as kernel-certified facts"
    );
    let assumptions = assumptions_with_propositions(&Assumptions::new(), &propositions);
    let CValue::Int32(result) = value else {
        panic!("opaque helper should return int32")
    };
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::Bitvector32Equal(
            Box::new(result.clone()),
            Box::new(Bitvector32Term::Constant(5)),
        ),
        true,
    )));

    let body_execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement,
        Assumptions::new(),
        environment,
        CExecutionSemantics::EXECUTE_BODIES,
    );
    let mut proposition = body_execution.paths()[0].theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    assert!(matches!(
        proposition,
        Proposition::CStatementExecutes {
            outcome: CStatementOutcome::Return { value, .. },
            ..
        } if *value == int32(99)
    ));
}

#[test]
fn verified_function_rule_coerces_null_constants_in_contract_views() {
    let p_is_null = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("p")),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::CExpression(c_int32_literal(0)),
    };
    let returns_one = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("result")),
        operator: CComparisonOperator::Equal,
        right: SpecExpression::CExpression(c_int32_literal(1)),
    };
    let helper = c_function(
        CType::Int32,
        "pointer_is_null",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_int32_literal(1)),
    )
    .with_contract(
        vec![p_is_null],
        vec![returns_one],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        c_call_assign("result", "pointer_is_null", vec![c_int32_literal(0)]),
        Assumptions::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("opaque null call path");

    assert!(
        path.obligations().is_empty(),
        "typed null precondition should be discharged: {:#?}",
        path.obligations()
    );
    assert!(path.facts().iter().any(|fact| {
        matches!(
            fact.proposition(),
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(_, right),
                true
            ) if right.as_const() == Some(1)
        )
    }));
}

#[test]
fn verified_function_rule_does_not_publish_one_spec_alias_path() {
    let stored = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let queried = Pointer {
        block: stored.block.clone(),
        offset: PointerOffsetTerm::Variable(Variable(900_002)),
    };
    let q = SpecExpression::CExpression(c_variable("q"));
    let reflexive_load = SpecProposition::Comparison {
        left: SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(q.clone()),
            value_type: CType::Int32,
        },
        operator: CComparisonOperator::Equal,
        right: SpecExpression::MemoryLoad {
            memory: SpecMemory::Current,
            pointer: Box::new(q),
            value_type: CType::Int32,
        },
    };
    let helper = c_function(
        CType::Int32,
        "opaque_alias_probe",
        vec![c_parameter("q", CType::Int32Pointer)],
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![reflexive_load],
        Vec::new(),
        vec![
            CFunctionContractClaim::body_safety(),
            CFunctionContractClaim::ensure_proposition(0, 0),
        ],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new().with_memory(CMemory::new().with_block("heap", 8).store(stored, int32(0))),
        c_call_assign(
            "result",
            "opaque_alias_probe",
            vec![c_pointer_value(queried)],
        ),
        Assumptions::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("opaque call path");

    assert!(
        path.obligations().is_empty(),
        "unexpected obligations: {:#?}",
        path.obligations()
    );
    assert!(!path.facts().iter().any(|fact| {
        matches!(
            fact.proposition(),
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), _)
        )
    }));
}

#[test]
fn opaque_pointer_result_can_alias_its_argument() {
    let argument = Pointer {
        block: "heap".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let helper = c_function(
        CType::Int32Pointer,
        "opaque_identity_pointer",
        vec![c_parameter("p", CType::Int32Pointer)],
        c_return(c_variable("p")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("p")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        c_call_assign(
            "result",
            "opaque_identity_pointer",
            vec![c_pointer_value(argument.clone())],
        ),
        Assumptions::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("opaque call path");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::CStatementVerifies {
        outcome: CStatementOutcome::Normal(state),
        ..
    } = proposition
    else {
        panic!("opaque pointer call should return normally")
    };
    let Some(CValue::Pointer(result)) = state.locals().get("result") else {
        panic!("call result should be a pointer")
    };

    assert!(result.has_symbolic_block());
    assert!(!result.blocks_proven_distinct(&argument));
    let assumptions = assumptions_with_propositions(
        &Assumptions::new(),
        &path
            .facts()
            .iter()
            .map(|fact| fact.proposition().clone())
            .collect::<Vec<_>>(),
    );
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::pointer_equal(result.clone(), argument),
        true,
    )));
}

#[test]
fn verified_immutable_calls_allocate_distinct_results() {
    let helper = c_function(
        CType::Int32,
        "opaque_identity",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_variable("x")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("x")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let statement = c_seq(
        c_call_assign("first", "opaque_identity", vec![c_int32_literal(5)]),
        c_seq(
            c_call_assign("second", "opaque_identity", vec![c_int32_literal(7)]),
            c_return(c_variable("second")),
        ),
    );
    let execution = prove_symbolic_c_execution_paths_with_environment(
        CState::new(),
        statement,
        Assumptions::new(),
        environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
    );
    let path = execution.paths().first().expect("calls should execute");
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::CStatementVerifies {
        outcome: CStatementOutcome::Return { value, state },
        ..
    } = proposition
    else {
        panic!("calls should return normally")
    };

    let first = state.locals().get("first").expect("first result");
    let second = state.locals().get("second").expect("second result");
    assert_ne!(first, second);
    assert_eq!(value, second);
}

#[test]
fn separate_statement_verification_calls_preserve_fresh_identity_progress() {
    let helper = c_function(
        CType::Int32,
        "opaque_identity",
        vec![c_parameter("x", CType::Int32)],
        c_return(c_variable("x")),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::CExpression(c_variable("x")),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let mut budget = ExecutionBudget::default();

    let (first_execution, _) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            CState::new(),
            c_call_assign("first", "opaque_identity", vec![c_int32_literal(5)]),
            Assumptions::new(),
            environment.clone(),
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut budget,
        );
    let first_next = budget.next_verification_variable();
    let first_path = first_execution.paths().first().expect("first call path");
    let mut first_proposition = first_path.theorem().proposition();
    while let Proposition::Implies(_, body) = first_proposition {
        first_proposition = body;
    }
    let Proposition::CStatementVerifies {
        outcome: CStatementOutcome::Normal(first_state),
        ..
    } = first_proposition
    else {
        panic!("first call should return normally")
    };
    let first_value = first_state.locals().get("first").expect("first result");

    let (second_execution, _) =
        prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
            first_state.clone(),
            c_call_assign("second", "opaque_identity", vec![c_int32_literal(7)]),
            Assumptions::new(),
            environment,
            CExecutionSemantics::APPLY_VERIFIED_RULES,
            &mut budget,
        );
    let second_path = second_execution.paths().first().expect("second call path");
    let mut second_proposition = second_path.theorem().proposition();
    while let Proposition::Implies(_, body) = second_proposition {
        second_proposition = body;
    }
    let Proposition::CStatementVerifies {
        outcome: CStatementOutcome::Normal(second_state),
        ..
    } = second_proposition
    else {
        panic!("second call should return normally")
    };
    let second_value = second_state.locals().get("second").expect("second result");

    assert!(first_next > 0);
    assert!(budget.next_verification_variable() > first_next);
    assert_ne!(first_value, second_value);
}

#[test]
fn verified_function_rule_requires_every_contract_claim_certificate() {
    let function = c_function(
        CType::Int32,
        "two_claims",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(0)),
            },
            SpecProposition::Comparison {
                left: SpecExpression::Value(int32(0)),
                operator: CComparisonOperator::Equal,
                right: SpecExpression::Value(int32(0)),
            },
        ],
        Vec::new(),
        vec![
            CFunctionContractClaim::ensure_proposition(0, 0),
            CFunctionContractClaim::ensure_proposition(1, 1),
        ],
        true,
    );
    let execution = prove_c_function_contract_execution_paths_with_environment(
        CState::new(),
        function.clone(),
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    let impostor = c_function(
        CType::Int32,
        "two_claims",
        Vec::new(),
        c_return(c_int32_literal(1)),
    );
    let impostor_execution = prove_c_function_contract_execution_paths_with_environment(
        CState::new(),
        impostor,
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::Ensure(0),
            &impostor_execution,
        )
        .is_none()
    );

    let first = c_verified_function_contract_claim(
        &function,
        CFunctionContractClaimKey::Ensure(0),
        &execution,
    )
    .expect("first claim should certify");

    assert!(c_verified_function_rule(function.clone(), std::slice::from_ref(&first)).is_none());

    let second = c_verified_function_contract_claim(
        &function,
        CFunctionContractClaimKey::Ensure(1),
        &execution,
    )
    .expect("second claim should certify");
    assert!(c_verified_function_rule(function, &[first, second]).is_some());
}

#[test]
fn contract_claim_rejects_same_source_function_with_a_different_contract() {
    let body = c_return(c_int32_literal(0));
    let uncontracted = c_function(CType::Int32, "contract_identity", Vec::new(), body.clone());
    let execution = prove_c_function_contract_execution_paths_with_environment(
        CState::new(),
        uncontracted,
        Vec::new(),
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );
    let stronger = c_function(CType::Int32, "contract_identity", Vec::new(), body).with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(1)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );

    assert!(
        c_verified_function_contract_claim(
            &stronger,
            CFunctionContractClaimKey::Ensure(0),
            &execution,
        )
        .is_none()
    );
}

#[test]
fn body_safety_claim_rejects_an_unproved_execution_condition() {
    let function = c_function(
        CType::Int32,
        "unsafe_body",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let state = CState::new();
    let obligation = ProofObligation::verification_condition(Proposition::ConditionIs(
        ConditionTerm::Constant(false),
        true,
    ));
    let proposition = Proposition::CFunctionExecutes {
        state: state.clone(),
        function: function.clone(),
        arguments: Vec::new(),
        outcome: CFunctionOutcome::Return {
            value: int32(0),
            state,
        },
    };
    let path = SymbolicCExecutionPath {
        assumptions: Assumptions::new(),
        facts: Vec::new(),
        effect_facts: Vec::new(),
        obligations: vec![obligation.clone()],
        theorem: Theorem::new(wrap_proof_facts(
            proposition,
            &Assumptions::new(),
            &[],
            &[obligation],
        )),
    };
    let execution = CFunctionContractExecution {
        execution: SymbolicCExecution {
            paths: vec![path],
            limit: None,
        },
    };

    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::BodySafety,
            &execution,
        )
        .is_none()
    );
}

#[test]
fn body_safety_claim_uses_path_facts_for_verification_conditions() {
    let function = c_function(
        CType::Int32,
        "guarded_body",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    );
    let state = CState::new();
    let guard = Proposition::ConditionIs(
        ConditionTerm::signed_less_than(
            Bitvector32Term::Variable(Variable(91_000)),
            Bitvector32Term::Constant(8),
        ),
        true,
    );
    let fact = ExecutionPureFact::new(guard.clone());
    let obligation = ProofObligation::verification_condition(guard);
    let proposition = Proposition::CFunctionExecutes {
        state: state.clone(),
        function: function.clone(),
        arguments: Vec::new(),
        outcome: CFunctionOutcome::Return {
            value: int32(0),
            state,
        },
    };
    let path = SymbolicCExecutionPath {
        assumptions: Assumptions::new(),
        facts: vec![fact.clone()],
        effect_facts: Vec::new(),
        obligations: vec![obligation.clone()],
        theorem: Theorem::new(wrap_proof_facts(
            proposition,
            &Assumptions::new(),
            &[fact],
            &[obligation],
        )),
    };
    let execution = CFunctionContractExecution {
        execution: SymbolicCExecution {
            paths: vec![path],
            limit: None,
        },
    };

    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::BodySafety,
            &execution,
        )
        .is_some(),
        "a path guard established by symbolic execution must discharge a guarded safety condition"
    );
}

#[test]
fn effect_endpoint_comparison_ignores_function_local_cells() {
    let local = Pointer {
        block: "local:temporary".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new().with_block("local:temporary", 4);
    let after = before.clone().store(local, int32(7));

    assert!(super::api::c_effect_memories_definitionally_equal(
        &before,
        &after,
        &Assumptions::new(),
    ));

    let external = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let changed_external = after.store(external, int32(9));
    assert!(!super::api::c_effect_memories_definitionally_equal(
        &before,
        &changed_external,
        &Assumptions::new(),
    ));
}

#[test]
fn effect_endpoint_allows_resource_allocation_bookkeeping() {
    let allocation = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(64),
    };
    let before = CMemory::new();
    let after = before
        .clone()
        .with_heap_allocation_claim(allocation, Bitvector32Term::Constant(16))
        .expect("a fresh symbolic allocation claim should be registerable");

    assert!(
        super::api::c_effect_memory_advances_over_internal_heap_state(
            &before,
            &after,
            &before,
            &Assumptions::new(),
        )
    );
}

#[test]
fn contract_claim_rejects_caller_supplied_false_entry_fact() {
    let function = c_function(
        CType::Int32,
        "false_postcondition",
        Vec::new(),
        c_return(c_int32_literal(0)),
    )
    .with_contract(
        Vec::new(),
        vec![SpecProposition::Comparison {
            left: SpecExpression::CExpression(c_variable("result")),
            operator: CComparisonOperator::Equal,
            right: SpecExpression::Value(int32(1)),
        }],
        Vec::new(),
        vec![CFunctionContractClaim::ensure_proposition(0, 0)],
        true,
    );
    let execution = prove_c_function_contract_execution_paths_with_environment(
        CState::new(),
        function.clone(),
        Vec::new(),
        vec![Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        )],
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert!(
        c_verified_function_contract_claim(
            &function,
            CFunctionContractClaimKey::Ensure(0),
            &execution,
        )
        .is_none()
    );
}

#[test]
fn decision_memo_distinguishes_equal_shaped_fact_sets_by_content() {
    // The decide memo is keyed by fact-set content identity. Two fact sets
    // that answer the same condition differently must never share a memo
    // entry, no matter how the objects are allocated or reused, and asking
    // one right after the other (in both orders) must not leak either
    // answer to the other.
    let x = Bitvector32Term::Variable(Variable(1));
    let below = ConditionTerm::signed_less_than(x.clone(), Bitvector32Term::Constant(10));
    let assumes_true = Assumptions::new().assume_condition(below.clone(), true);
    let assumes_false = Assumptions::new().assume_condition(below.clone(), false);

    for _ in 0..2 {
        assert_eq!(assumes_true.decide(&below), Some(true));
        assert_eq!(assumes_false.decide(&below), Some(false));
        assert_eq!(assumes_true.decide(&below), Some(true));
    }
}

// --- named-memory-states arc: the derivation DAG -------------------------
// See docs/advanced/memory-dag.md. These pin the two invariants
// the arc's safety argument rests on (advisory-only, and parent id < child
// id) plus the havoc-identity property that must hold by construction.

/// These tests assert what the DAG *adds*, so under
/// `CLICK_DISABLE_MEMORY_DAG` there is nothing for them to say. Skipping
/// them there is what makes the flag a real A/B handle: the whole suite
/// stays green with the arc switched off.
fn skip_without_memory_dag() -> bool {
    memory_dag_disabled()
}

fn arc_pointer(offset: i64) -> Pointer {
    Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(offset),
    }
}

#[test]
fn a_store_records_the_edge_from_the_snapshot_it_wrote() {
    if skip_without_memory_dag() {
        return;
    }
    let base = CMemory::new().with_block("arg-memory", 16);
    let after = base
        .clone()
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(7)));

    let derivation = crate::kernel::intern_c_memory_ref(&after)
        .derivation()
        .expect("a store records how the snapshot was produced");
    match derivation.as_ref() {
        CMemoryDerivation::Store {
            base: recorded_base,
            pointer,
            value,
        } => {
            assert_eq!(recorded_base.as_ref(), &base);
            assert_eq!(pointer, &arc_pointer(4));
            assert_eq!(value, &CValue::Int32(Bitvector32Term::Constant(7)));
        }
        other => panic!("expected a store edge, got {other:?}"),
    }
}

#[test]
fn derivation_bases_are_strictly_older_so_the_dag_cannot_cycle() {
    if skip_without_memory_dag() {
        return;
    }
    // Storing a value and then storing it back re-interns the original
    // snapshot, which is the shortest cycle the DAG could otherwise grow.
    // First-wins recording keeps the older edge, so following `base` still
    // strictly decreases and terminates.
    let base = CMemory::new().with_block("arg-memory", 16);
    let written = base
        .clone()
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(1)));
    let restored = written
        .clone()
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(0)))
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(1)));
    assert_eq!(restored, written, "the round trip returns the same value");

    let mut node = crate::kernel::intern_c_memory_ref(&restored);
    let mut hops = 0;
    while let Some(derivation) = node.derivation() {
        let next = derivation.base().clone();
        assert!(
            next.arena_id() < node.arena_id(),
            "a derivation base must be strictly older than what it derives"
        );
        node = next;
        hops += 1;
        assert!(hops < 64, "walking derivation bases must terminate");
    }
}

#[test]
fn a_store_that_changes_nothing_records_no_edge_to_itself() {
    if skip_without_memory_dag() {
        return;
    }
    let base = CMemory::new()
        .with_block("arg-memory", 16)
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(3)));
    let again = base
        .clone()
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(3)));
    assert_eq!(again, base);

    let node = crate::kernel::intern_c_memory_ref(&again);
    if let Some(derivation) = node.derivation() {
        assert_ne!(
            derivation.base().arena_id(),
            node.arena_id(),
            "a snapshot must never be recorded as derived from itself"
        );
    }
}

#[test]
fn loop_havoc_is_its_own_edge_kind_and_keeps_its_marker_block() {
    if skip_without_memory_dag() {
        return;
    }
    let base = CMemory::new()
        .with_block("arg-memory", 16)
        .store(arc_pointer(0), CValue::Int32(Bitvector32Term::Constant(5)));
    let after = base
        .clone()
        .with_loop_memory_havoc(Variable(0), &BTreeSet::new());

    assert!(
        after.has_block(&"havoc:0".into()),
        "the freshness marker block must survive the arc untouched"
    );
    let derivation = crate::kernel::intern_c_memory_ref(&after)
        .derivation()
        .expect("loop havoc records how the snapshot was produced");
    match derivation.as_ref() {
        CMemoryDerivation::LoopHavoc {
            base: recorded_base,
            variable,
        } => {
            assert_eq!(recorded_base.as_ref(), &base);
            assert_eq!(*variable, Variable(0));
        }
        other => panic!("expected a loop-havoc edge, got {other:?}"),
    }
}

#[test]
fn derivations_carry_a_load_across_a_distinct_store_but_not_across_havoc() {
    // The first consumer of the DAG: load preservation answered from the
    // recorded history rather than from effect facts. A store to a provably
    // distinct cell is crossable; a loop havoc between the same endpoints is
    // not, because it has no write set to be disjoint from.
    //
    // Only the positive direction is the DAG's to add. The havoc refusals
    // are soundness properties that must hold with the arc switched off too,
    // so they run under both settings.
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);

    if !skip_without_memory_dag() {
        // A call havoc changes the block set (it adds its marker block), so
        // the snapshot-diff matcher refuses to look at the cells at all. The
        // recorded edge carries the call's mutable ranges, so the walk can
        // still cross it for a pointer provably outside them. This is the
        // case the DAG answers and value bridging cannot.
        let called = base.clone().with_call_memory_havoc(
            Variable(3),
            &[memory_range(arc_pointer(8), 0, 8)],
            &Assumptions::new(),
        );
        assert!(
            !memories_match_for_pointer_load_under_assumptions(
                &base,
                &called,
                &read,
                &Assumptions::new()
            ),
            "the snapshot-diff matcher is expected not to cross the marker block"
        );
        assert!(
            c_memory_load_is_unchanged(&base, &called, &read, &Assumptions::new()),
            "a call that may only write a disjoint range preserves the load"
        );
    }

    let havoced = base
        .clone()
        .with_loop_memory_havoc(Variable(7), &BTreeSet::new());
    assert!(
        !c_memory_load_is_unchanged(&base, &havoced, &read, &Assumptions::new()),
        "loop havoc must never be crossed without explicit frame evidence"
    );

    let havoced_then_stored = havoced
        .clone()
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(9)));
    assert!(
        !c_memory_load_is_unchanged(&base, &havoced_then_stored, &read, &Assumptions::new()),
        "a crossable store must not smuggle a walk past an intervening havoc"
    );
}

/// Stage 4: the DAG-guided cell lookup answers load equality for snapshots
/// that are *siblings*, which the stage-2 walk cannot do because it only ever
/// asks whether one snapshot is reachable from the other.
///
/// Two calls, each havocking a range disjoint from the loaded cell, produce
/// two snapshots neither of which derives from the other. Value bridging
/// refuses them outright — each carries its own `call-havoc:N` marker block,
/// so the block sets differ and the snapshot matcher stops before looking at
/// any cell. Resolving both against the write history lands them on one
/// common ancestor, and the loads are equal with no snapshot comparison.
#[test]
fn sibling_snapshots_resolve_one_cell_to_a_common_ancestor() {
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let load_in = |memory: &CMemory| {
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory_ref(memory),
            Box::new(read.clone()),
        )
    };
    let call_havoc = |variable| {
        base.clone().with_call_memory_havoc(
            Variable(variable),
            &[memory_range(arc_pointer(8), 0, 8)],
            &Assumptions::new(),
        )
    };
    let (left, right) = (call_havoc(3), call_havoc(4));

    assert!(
        !memories_match_for_pointer_load_under_assumptions(
            &left,
            &right,
            &read,
            &Assumptions::new()
        ),
        "the two marker blocks are expected to stop the snapshot matcher"
    );
    assert_eq!(
        Assumptions::new().memory_loads_proven_equal(&load_in(&left), &load_in(&right)),
        !skip_without_memory_dag(),
        "the common-ancestor lookup is exactly what the DAG adds here"
    );

    // Soundness, and so asserted in both modes: an intervening loop havoc has
    // no write set, so no walk may resolve through one.
    let havoced = left
        .clone()
        .with_loop_memory_havoc(Variable(9), &BTreeSet::new());
    assert!(
        !Assumptions::new().memory_loads_proven_equal(&load_in(&left), &load_in(&havoced)),
        "loop havoc must stop the cell lookup"
    );
}

/// The owned-string loadable shape: the permission fact and its bound facts
/// spell `len` as a load at contract
/// entry, while the index the goal extracts spells it at a later snapshot
/// separated by a block declaration, stores, and a cell-forgetting prune —
/// exactly the edges (`BlockDeclared`, `CellsForgotten`) that used to leave
/// the two spellings in disjoint DAG components. The loadable prover's
/// extended bridging connects them; everywhere outside that prover the new
/// edges must stay invisible (pinned by the frame-evidence test above and
/// the byte-identical replay of the certified corpus).
#[test]
fn loadable_bound_check_bridges_len_spellings_across_block_and_prune_edges() {
    if skip_without_memory_dag() {
        return;
    }
    let entry = CMemory::new().with_block("arg-memory", 64);
    let len_pointer = arc_pointer(0);
    let len_at_entry = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&entry),
        Box::new(len_pointer.clone()),
    );

    // The recorded facts: the buffer permission and both `len` bounds, all
    // spelled at entry.
    let assumptions = Assumptions::new()
        // Same-block permissions that cannot cover `buffer[len]`. These used
        // to trigger costly general equality searches before the matching
        // symbolic range was considered.
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(0),
            bytes: Bitvector32Term::Constant(4),
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(8),
            bytes: Bitvector32Term::Constant(4),
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(12),
            bytes: Bitvector32Term::Constant(4),
        })
        .assume_proposition(Proposition::CMemoryLoadable {
            memory: entry.clone(),
            base: arc_pointer(16),
            bytes: Bitvector32Term::Constant(32),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), len_at_entry.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(len_at_entry, Bitvector32Term::Constant(8)),
            true,
        );

    // The later snapshot: a local declared, a distinct cell written, and the
    // write-path prune that forgets it again. Its `len` load is a different
    // spelling of the same cell.
    let later = entry
        .clone()
        .with_block("local:i", 4)
        .store(arc_pointer(4), CValue::Int32(Bitvector32Term::Constant(9)))
        .store(arc_pointer(8), CValue::Int32(Bitvector32Term::Constant(2)))
        .without_possible_aliasing_cells(&arc_pointer(4), &assumptions);
    let len_at_later = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory_ref(&later),
        Box::new(len_pointer),
    );

    // loadable(buffer[len]) with `len` spelled at the later snapshot.
    let goal_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Constant(16)),
            Box::new(PointerOffsetTerm::Int32Scaled {
                value: Box::new(len_at_later),
                byte_width: 4,
            }),
        ),
    };
    assert!(
        assumptions.proves_memory_loadable(&later, &goal_base, &Bitvector32Term::Constant(4)),
        "the loadable bound check must connect the two len spellings along \
         the recorded block-declaration and cell-forgetting edges"
    );
}

#[test]
fn a_store_to_the_loaded_cell_is_not_crossable() {
    // A soundness property, so it must hold with the arc switched off too.
    let base = CMemory::new().with_block("arg-memory", 16);
    let read = arc_pointer(0);
    let stored = base
        .clone()
        .store(read.clone(), CValue::Int32(Bitvector32Term::Constant(9)));

    assert!(
        !c_memory_load_is_unchanged(&base, &stored, &read, &Assumptions::new()),
        "the walk must refuse the very cell that was written"
    );
}

/// The premise-availability path matches two spellings of one fact whose load
/// atoms carry different memory snapshots. The match is decided by proof, not
/// by ignoring the snapshots: an unframed call havoc between the two snapshots
/// blocks it, and an effect summary that frames the loaded pointer restores it.
#[test]
fn conditions_equal_modulo_proven_snapshots_needs_frame_evidence() {
    let before = CMemory::new()
        .with_block("arg-memory", 8)
        .with_block("call-havoc:0", 0);
    let after = before.clone().with_block("call-havoc:1", 0);
    let loaded = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let elsewhere = Pointer {
        block: "other-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let condition = |memory: &CMemory| {
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(77)),
            Bitvector32Term::add(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory.clone()),
                    Box::new(loaded.clone()),
                ),
                Bitvector32Term::Constant(1),
            ),
        )
    };

    // Same snapshot: the two spellings are literally one condition.
    assert!(
        Assumptions::new()
            .conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&before))
    );

    // A call havoc stands between the snapshots and nothing frames the load,
    // so the later spelling is a different fact, not another spelling.
    assert!(
        !Assumptions::new()
            .conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&after)),
        "an unframed call havoc must not be matched away"
    );

    // With an effect summary whose mutable range misses the loaded pointer,
    // the two snapshots provably agree there and the spellings match.
    let framed = Assumptions::new().assume_proposition(Proposition::CMemoryEffectSummary {
        before: before.clone(),
        after: after.clone(),
        mutable_ranges: vec![CMemoryRange::new(
            elsewhere,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    });
    assert!(
        framed.conditions_equal_modulo_proven_snapshots(&condition(&before), &condition(&after)),
        "a framed load should match across the effect"
    );

    // Framing never relaxes the structure: a different condition stays
    // different however well the snapshots are framed.
    let other = ConditionTerm::equal(
        Bitvector32Term::Variable(Variable(78)),
        Bitvector32Term::add(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after.clone()),
                Box::new(loaded.clone()),
            ),
            Bitvector32Term::Constant(1),
        ),
    );
    assert!(!framed.conditions_equal_modulo_proven_snapshots(&condition(&before), &other));
}

fn heap_allocation_paths() -> Vec<CStatementExecutionPath> {
    let state = CState::new().with_local("p", CValue::Pointer(Pointer::null()));
    execute_c_statement_paths(
        &state,
        &c_heap_allocate("p", 16),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("fixed-size allocation should execute")
}

fn successful_heap_allocation_state() -> CState {
    let paths = heap_allocation_paths();
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("allocation statement should produce one pending outcome");
    };
    let Some(CValue::Pointer(pointer)) = pending.locals().get("p") else {
        panic!("allocation should assign a pointer");
    };
    let assumptions = Assumptions::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(pointer.clone(), Pointer::null()),
        false,
    ));
    resolve_pending_heap_allocations(pending, &assumptions)
}

#[test]
fn heap_allocate_has_null_or_fresh_uninitialized_outcomes() {
    let paths = heap_allocation_paths();
    assert_eq!(paths.len(), 1);
    let success = successful_heap_allocation_state();
    let Some(CValue::Pointer(pointer)) = success.locals().get("p") else {
        panic!("allocation should assign a pointer");
    };
    assert_eq!(
        success.memory().live_heap_block_size(pointer),
        Some(&Bitvector32Term::Constant(16))
    );
    if !skip_without_memory_dag() {
        let derivation = intern_c_memory_ref(success.memory())
            .derivation()
            .expect("successful allocation should record a memory edge");
        assert!(matches!(
            derivation.as_ref(),
            CMemoryDerivation::HeapAllocated { block, bytes, .. }
                if block == &pointer.block && *bytes == Bitvector32Term::Constant(16)
        ));
    }
    assert!(
        success
            .resources()
            .facts()
            .contains(&CResourceFact::own_allocation(pointer.clone(), 16))
    );
    let read = evaluate_c_expression_paths(
        &success,
        &c_load(c_variable("p")),
        &Assumptions::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("heap read should execute");
    assert!(matches!(
        read.as_slice(),
        [CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead),
            ..
        }]
    ));

    let CStatementOutcome::Normal(pending) = &paths[0].outcome else {
        unreachable!();
    };
    let Some(CValue::Pointer(pointer)) = pending.locals().get("p") else {
        unreachable!();
    };
    let null = resolve_pending_heap_allocations(
        pending,
        &Assumptions::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pointer.clone(), Pointer::null()),
            true,
        )),
    );
    assert!(null.resources().facts().is_empty());
    assert!(null.memory().live_heap_block_size(pointer).is_none());
}

#[test]
fn pending_and_failed_heap_allocation_preserve_existing_memory() {
    if skip_without_memory_dag() {
        return;
    }

    let existing = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let state = CState::new()
        .with_local("p", CValue::Pointer(Pointer::null()))
        .with_memory(
            CMemory::new()
                .with_block("arg-memory", 4)
                .store(existing.clone(), int32(37)),
        );
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_allocate("p", 16),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("allocation statement should produce a pending result");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("allocation statement should produce one pending outcome");
    };
    let Some(CValue::Pointer(pending_pointer)) = pending.locals().get("p") else {
        panic!("allocation should assign a symbolic pending pointer");
    };
    let pending_pointer = pending_pointer.clone();
    let pending_memory = pending.memory().clone();

    let pending_derivation = intern_c_memory_ref(&pending_memory)
        .derivation()
        .expect("pending allocation should record a memory edge");
    let CMemoryDerivation::HeapAllocationPending {
        base,
        allocation_base,
        bytes,
    } = pending_derivation.as_ref()
    else {
        panic!("unexpected pending-allocation derivation: {pending_derivation:?}");
    };
    assert_eq!(base.as_ref(), state.memory());
    assert_eq!(allocation_base, &pending_pointer);
    assert_eq!(*bytes, Bitvector32Term::Constant(16));
    assert!(with_extended_dag_bridging(|| c_memory_load_is_unchanged(
        state.memory(),
        &pending_memory,
        &existing,
        &Assumptions::new(),
    )));

    let failed = resolve_pending_heap_allocations(
        pending,
        &Assumptions::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.clone(), Pointer::null()),
            true,
        )),
    );
    assert!(failed.resources().facts().is_empty());
    assert!(
        failed
            .memory()
            .live_heap_block_size(&pending_pointer)
            .is_none()
    );
    assert!(with_extended_dag_bridging(|| c_memory_load_is_unchanged(
        state.memory(),
        failed.memory(),
        &existing,
        &Assumptions::new(),
    )));
    assert_eq!(failed.memory(), state.memory());

    let succeeded = resolve_pending_heap_allocations(
        pending,
        &Assumptions::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.clone(), Pointer::null()),
            false,
        )),
    );
    let derivation = intern_c_memory_ref(succeeded.memory())
        .derivation()
        .expect("successful allocation should record a memory edge");
    let CMemoryDerivation::HeapAllocated { base, block, bytes } = derivation.as_ref() else {
        panic!("unexpected successful-allocation derivation: {derivation:?}");
    };
    assert_eq!(base.as_ref(), &pending_memory);
    assert!(matches!(block, PointerBlock::Heap(_)));
    assert_eq!(*bytes, Bitvector32Term::Constant(16));
    assert!(with_extended_dag_bridging(|| c_memory_load_is_unchanged(
        &pending_memory,
        succeeded.memory(),
        &existing,
        &Assumptions::new(),
    )));
}

#[test]
fn successful_heap_allocation_is_fresh_from_every_existing_block() {
    let first = successful_heap_allocation_state();
    let Some(CValue::Pointer(first_pointer)) = first.locals().get("p") else {
        panic!("first allocation should assign a pointer");
    };
    let first_pointer = first_pointer.clone();
    assert!(pointers_proven_distinct(
        &first_pointer,
        &Pointer::null(),
        &Assumptions::new(),
    ));
    assert!(pointers_proven_distinct(
        &first_pointer,
        &CMemory::local_pointer("local"),
        &Assumptions::new(),
    ));
    assert!(pointers_proven_distinct(
        &first_pointer,
        &Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        },
        &Assumptions::new(),
    ));

    let state = first.with_local("q", CValue::Pointer(Pointer::null()));
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_allocate("q", 16),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        // Deliberately reset the generator: existing heap identities still
        // have to prevent reuse.
        &mut ExecutionBudget::default(),
    )
    .expect("second allocation should execute");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(pending),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("second allocation should have one pending outcome");
    };
    let Some(CValue::Pointer(pending_pointer)) = pending.locals().get("q") else {
        panic!("second allocation should assign a pending pointer");
    };
    let second = resolve_pending_heap_allocations(
        pending,
        &Assumptions::new().assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pending_pointer.clone(), Pointer::null()),
            false,
        )),
    );
    let Some(CValue::Pointer(second_pointer)) = second.locals().get("q") else {
        panic!("second allocation should resolve to a pointer");
    };
    assert!(pointers_proven_distinct(
        &first_pointer,
        second_pointer,
        &Assumptions::new(),
    ));
}

#[test]
fn heap_free_retires_the_complete_block_and_rejects_double_free() {
    let success = successful_heap_allocation_state();
    let freed = execute_c_statement_paths(
        &success,
        &c_heap_free(c_variable("p")),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("free should execute");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(freed),
            facts: free_facts,
            ..
        },
    ] = freed.as_slice()
    else {
        panic!("valid free should have one normal path: {freed:?}");
    };
    let Some(CValue::Pointer(pointer)) = freed.locals().get("p") else {
        panic!("freed local should still contain its stale pointer value");
    };
    assert!(freed.memory().is_retired_heap_address(pointer));
    assert!(freed.resources().facts().is_empty());
    assert!(matches!(
        free_facts.as_slice(),
        [ExecutionPureFact {
            proposition: Proposition::CHeapLifetimeRetired {
                after,
                allocation_base,
                bytes,
                ..
            },
            ..
        }] if after == freed.memory()
            && allocation_base == pointer
            && *bytes == Bitvector32Term::Constant(16)
    ));
    if !skip_without_memory_dag() {
        let derivation = intern_c_memory_ref(freed.memory())
            .derivation()
            .expect("free should record a memory edge");
        assert!(matches!(
            derivation.as_ref(),
            CMemoryDerivation::HeapFreed { allocation_base, bytes, .. }
                if allocation_base == pointer && *bytes == Bitvector32Term::Constant(16)
        ));
    }

    let double = execute_c_statement_paths(
        freed,
        &c_heap_free(c_variable("p")),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("double free should execute to a diagnostic");
    assert!(matches!(
        double.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(
                CInvalidFree::DoubleFree
            )),
            ..
        }]
    ));
}

#[test]
fn scoped_call_borrows_end_before_free() {
    let state = successful_heap_allocation_state();
    let helper = c_function(
        CType::Int32,
        "read_borrow",
        vec![c_parameter("data", CType::Int32Pointer)],
        c_return(c_int32_literal(0)),
    )
    .with_resource_summary(
        vec![CResourceSpec::Read(CMemorySegment::new(
            c_variable("data"),
            c_int32_literal(0),
            c_int32_literal(1),
        ))],
        Vec::new(),
    );
    let environment = CExecutionEnvironment::new()
        .with_function(helper.clone())
        .with_verified_function_rule(CVerifiedFunctionRule { function: helper });
    let statement = c_seq(
        c_call_assign("observed", "read_borrow", vec![c_variable("p")]),
        c_heap_free(c_variable("p")),
    );
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &Assumptions::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::default(),
    )
    .expect("a read-only call borrow followed by free should execute");

    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after),
            ..
        }] if after.resources().facts().is_empty()
    ));
}

#[test]
fn standalone_view_cannot_authorize_free() {
    let state = successful_heap_allocation_state();
    let Some(CValue::Pointer(pointer)) = state.locals().get("p") else {
        panic!("successful allocation should expose its pointer")
    };
    let pointer = pointer.clone();
    let complete_access = CMemoryRange::new(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
    );
    let resources = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_allocation(pointer, 16))
        .unchecked_with_fact(CResourceFact::view_memory(complete_access.clone()));
    let state = state.with_resource_context(resources);
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("a standalone view should fail locally at free");
    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                resource: CResourceFact::Own(CResource::Memory(missing)),
            }),
            ..
        }] if missing == &complete_access
    ));
}

#[test]
fn persistent_composite_view_blocks_free_locally() {
    let state = successful_heap_allocation_state();
    let Some(CValue::Pointer(pointer)) = state.locals().get("p") else {
        panic!("successful allocation should expose its pointer")
    };
    let persistent = CResourceFact::view_composite(
        "borrowed_allocation".to_string(),
        vec![CValue::Pointer(pointer.clone())],
    );
    let state = state.clone().with_resource_context(
        state
            .resources()
            .clone()
            .unchecked_with_fact(persistent.clone()),
    );
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("a persistent stale view should produce a local diagnostic");
    assert!(
        matches!(
            paths.as_slice(),
            [CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(
                    CRuntimeError::StaleResourceAfterFree { resource }
                ),
                ..
            }] if resource == &persistent
        ),
        "unexpected free result for {persistent:#?}: {paths:#?}"
    );
}

#[test]
fn separated_persistent_view_survives_free() {
    let state = successful_heap_allocation_state();
    let other = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let view = CResourceFact::view_memory(CMemoryRange::new(
        other,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    let state = state
        .clone()
        .with_resource_context(state.resources().clone().unchecked_with_fact(view.clone()));
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("a view of a distinct allocation should survive free");

    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after),
            ..
        }] if after.resources().facts() == [view]
    ));
}

#[test]
fn free_of_external_allocation_preserves_unrelated_external_cells() {
    let allocation_base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(908_000)), 4),
    };
    let unrelated = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(908_001)), 4),
    };
    let memory = CMemory::new()
        .store(unrelated.clone(), int32(37))
        .with_heap_allocation_claim(allocation_base.clone(), 16)
        .expect("external allocation claim should be fresh");
    let resources = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_allocation(allocation_base.clone(), 16))
        .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            allocation_base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
        )));
    let state = CState::new()
        .with_memory(memory)
        .with_resource_context(resources)
        .with_local("p", CValue::Pointer(allocation_base.clone()));

    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("freeing an imported allocation should execute");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after),
            ..
        },
    ] = paths.as_slice()
    else {
        panic!("free should have one normal path: {paths:?}");
    };

    assert_eq!(
        after.memory().load(&unrelated),
        CExpressionOutcome::Value(int32(37))
    );
    assert!(!after.memory().is_retired_heap_address(&unrelated));
    assert!(after.memory().is_retired_heap_address(&allocation_base));
    assert!(
        after
            .memory()
            .is_retired_heap_address(&allocation_base.offset_by_int32_elements(1.into()))
    );
}

#[test]
fn free_requires_allocation_authority_not_just_write_access() {
    let mut success = successful_heap_allocation_state();
    success
        .resources
        .facts
        .retain(|fact| fact.allocation().is_none());
    let paths = execute_c_statement_paths(
        &success,
        &c_heap_free(c_variable("p")),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("missing-authority free should execute to a diagnostic");
    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                resource
            }),
            ..
        }] if resource.allocation().is_some()
    ));
}

#[test]
fn heap_storage_becomes_readable_only_after_a_store() {
    let success = successful_heap_allocation_state();
    let stored = execute_c_statement_paths(
        &success,
        &c_store(c_variable("p"), c_int32_literal(37)),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("an owned fresh heap cell should be writable");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(stored),
            ..
        },
    ] = stored.as_slice()
    else {
        panic!("heap store should succeed: {stored:?}");
    };
    let read = evaluate_c_expression_paths(
        stored,
        &c_load(c_variable("p")),
        &Assumptions::new(),
        &mut ExecutionBudget::default(),
    )
    .expect("initialized heap read should execute");
    assert!(matches!(
        read.as_slice(),
        [CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            ..
        }] if value == &int32(37)
    ));
}

#[test]
fn free_null_needs_no_allocation_resources() {
    let state = CState::new().with_local("p", CValue::Pointer(Pointer::null()));
    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("free(NULL) should execute");
    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after),
            ..
        }] if after == &state
    ));
}

#[test]
fn free_preserves_a_separate_recursive_tail_with_the_same_symbolic_block() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(909_000)), 4),
    };
    let tail = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(909_001)), 4),
    };
    let tail_resource =
        CResourceFact::own_composite("allocated_list".to_string(), vec![CValue::Pointer(tail)]);
    let resources = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_allocation(base.clone(), 16))
        .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
        )))
        .unchecked_with_fact(tail_resource.clone());
    let memory = CMemory::new()
        .with_heap_allocation_claim(base.clone(), 16)
        .expect("symbolic allocation claim should be fresh");
    let state = CState::new()
        .with_memory(memory)
        .with_resource_context(resources)
        .with_local("p", CValue::Pointer(base));

    let paths = execute_c_statement_paths(
        &state,
        &c_heap_free(c_variable("p")),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("freeing a separated parent should execute");
    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(after),
            ..
        }] if after.resources().facts() == [tail_resource]
    ));
}

fn nullable_owner_contract(body: CStatement) -> (CState, CFunction, Vec<CExpression>) {
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(910_000)), 4),
    };
    let pointer_value = CValue::Pointer(pointer.clone());
    let pointer_expression = SpecExpression::CExpression(c_variable("item"));
    let definition = CCompositeResourceDefinition::new(
        "owned_item",
        vec![c_parameter("item", CType::Int32Pointer)],
        Some(SpecProposition::Comparison {
            left: pointer_expression.clone(),
            operator: CComparisonOperator::NotEqual,
            right: SpecExpression::Value(CValue::Pointer(Pointer::null())),
        }),
        false,
        vec![
            CResourceSpec::Token {
                access: CResourceAccessMode::Own,
                name: "allocation".to_string(),
                arguments: vec![
                    c_variable("item"),
                    CExpression::Value(CValue::Int32(Bitvector32Term::Constant(4))),
                ],
                parameter_types: vec![CType::Int32Pointer, CType::Int32],
            },
            CResourceSpec::Write(CMemorySegment {
                base: c_variable("item"),
                start: c_int32_literal(0),
                end: c_int32_literal(1),
                guard: None,
            }),
        ],
        Vec::new(),
    );
    let requirement = CResourceSpec::Composite {
        access: CResourceAccessMode::Own,
        name: "owned_item".to_string(),
        arguments: vec![c_variable("item")],
        parameter_types: vec![CType::Int32Pointer],
    };
    let function = c_function(
        CType::Int32,
        "item_destroy",
        vec![c_parameter("item", CType::Int32Pointer)],
        body,
    )
    .with_resource_summary(vec![requirement], Vec::new())
    .with_contract(
        Vec::new(),
        Vec::new(),
        Vec::new(),
        vec![CFunctionContractClaim::body_safety()],
        true,
    )
    .with_composite_resource_definitions(vec![definition]);
    let state = CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
        CResourceFact::own_composite("owned_item".to_string(), vec![pointer_value]),
    ));
    (state, function, vec![c_pointer_value(pointer)])
}

#[test]
fn guarded_opaque_call_footprints_skip_only_inactive_segments() {
    let (_, mut function, _) = nullable_owner_contract(c_return(c_int32_literal(0)));
    let active = SpecProposition::Comparison {
        left: SpecExpression::CExpression(c_variable("item")),
        operator: CComparisonOperator::NotEqual,
        right: SpecExpression::Value(CValue::Pointer(Pointer::null())),
    };
    function.contract_mutable = vec![
        CMemorySegment::new(c_int32_literal(7), c_int32_literal(0), c_int32_literal(1))
            .with_guard(active),
    ];
    let environment = CExecutionEnvironment::new()
        .with_function(function.clone())
        .with_verified_function_rule(CVerifiedFunctionRule {
            function: function.clone(),
        });

    let null = CValue::Pointer(Pointer::null());
    let null_state =
        CState::new().with_resource_context(ResourceContext::new().unchecked_with_fact(
            CResourceFact::own_composite("owned_item".to_string(), vec![null]),
        ));
    let null_paths = execute_c_statement_paths(
        &null_state,
        &c_call_assign("result", "item_destroy", vec![c_int32_literal(0)]),
        &Assumptions::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::default(),
    )
    .expect("an inactive malformed footprint should not be evaluated");
    assert!(matches!(
        null_paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(_),
            ..
        }]
    ));

    let nonnull = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let nonnull_state = CState::new().with_resource_context(
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_composite(
            "owned_item".to_string(),
            vec![CValue::Pointer(nonnull.clone())],
        )),
    );
    let nonnull_paths = execute_c_statement_paths(
        &nonnull_state,
        &c_call_assign("result", "item_destroy", vec![c_pointer_value(nonnull)]),
        &Assumptions::new(),
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        &mut ExecutionBudget::default(),
    )
    .expect("an active malformed footprint should produce a local diagnostic");
    assert!(matches!(
        nonnull_paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(message)),
            ..
        }] if message.contains("could not evaluate mutable footprint")
    ));
}

#[test]
fn contract_certification_splits_undecided_conditional_resource_guards() {
    let (state, function, arguments) = nullable_owner_contract(c_seq(
        c_heap_free(c_variable("item")),
        c_return(c_int32_literal(0)),
    ));
    let execution = prove_c_function_contract_execution_paths_with_environment(
        state,
        function.clone(),
        arguments,
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(execution.path_count(), 2);
    assert!(c_verified_function_contract_claims(&function, &execution).is_some());
}

#[test]
fn conditional_resource_certification_checks_the_unsafe_case_too() {
    let (state, function, arguments) = nullable_owner_contract(c_seq(
        c_heap_free(c_variable("item")),
        c_seq(
            c_heap_free(c_variable("item")),
            c_return(c_int32_literal(0)),
        ),
    ));
    let execution = prove_c_function_contract_execution_paths_with_environment(
        state,
        function.clone(),
        arguments,
        Vec::new(),
        CExecutionEnvironment::new(),
        CExecutionSemantics::APPLY_CALL_RULES_AND_VERIFY_LOOPS,
        CFunctionContractExecutionMode::VerifyLoops,
    );

    assert_eq!(execution.path_count(), 2);
    let error = c_unverified_function_contract_claims(&function, &execution)
        .expect_err("the nonnull double-free case must invalidate certification");
    assert!(error.contains("DoubleFree"), "unexpected failure: {error}");
}

#[test]
fn interior_free_and_store_after_free_are_rejected() {
    let success = successful_heap_allocation_state();
    let interior = execute_c_statement_paths(
        &success,
        &c_heap_free(c_add(c_variable("p"), c_int32_literal(1))),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("interior free should produce a diagnostic");
    assert!(matches!(
        interior.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(
                CInvalidFree::InteriorPointer
            )),
            ..
        }]
    ));

    let freed = execute_c_statement_paths(
        &success,
        &c_heap_free(c_variable("p")),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("valid free should execute");
    let [
        CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(freed),
            ..
        },
    ] = freed.as_slice()
    else {
        panic!("valid free should succeed: {freed:?}");
    };
    let store = execute_c_statement_paths(
        freed,
        &c_store(c_variable("p"), c_int32_literal(1)),
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("store-after-free should produce undefined behavior");
    assert!(matches!(
        store.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
            ..
        }]
    ));
}

#[test]
fn returning_malloc_result_resolves_null_and_success_outcomes() {
    let state = CState::new().with_local("p", CValue::Pointer(Pointer::null()));
    let statement = c_seq(c_heap_allocate("p", 16), c_return(c_variable("p")));
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("returning a malloc result should split its outcomes");
    assert_eq!(paths.len(), 2);
    assert!(
        paths
            .iter()
            .all(|path| path.facts.iter().all(|fact| !fact.is_public())),
        "the malloc outcome split is internal, not a source-level premise"
    );

    let mut saw_success = false;
    let mut saw_failure = false;
    for path in paths {
        let CStatementOutcome::Return { value, state } = path.outcome else {
            panic!("malloc return should not produce a diagnostic");
        };
        let CValue::Pointer(pointer) = value else {
            panic!("malloc should return a pointer");
        };
        assert!(!state.memory().has_pending_heap_allocation());
        if pointer == Pointer::null() {
            saw_failure = true;
            assert!(state.resources().facts().is_empty());
        } else {
            saw_success = true;
            assert!(matches!(pointer.block, PointerBlock::Heap(_)));
            assert_eq!(
                state.memory().live_heap_block_size(&pointer),
                Some(&Bitvector32Term::Constant(16))
            );
            assert!(
                state
                    .resources()
                    .facts()
                    .contains(&CResourceFact::own_allocation(pointer.clone(), 16))
            );
        }
    }
    assert!(saw_success && saw_failure);
}

#[test]
fn unreturned_unresolved_malloc_result_cannot_cross_a_return() {
    let state = CState::new().with_local("p", CValue::Pointer(Pointer::null()));
    let statement = c_seq(c_heap_allocate("p", 16), c_return(c_int32_literal(0)));
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &Assumptions::new(),
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .expect("unresolved allocation should execute to a diagnostic");
    assert!(matches!(
        paths.as_slice(),
        [CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome),
            ..
        }]
    ));
}
