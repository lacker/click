use super::*;

fn unrelated_token_context(size: usize) -> ResourceContext {
    ResourceContext::new().unchecked_with_facts(
        (0..size).map(|index| {
            CResourceFact::own_token(format!("token_{index}"), vec![int32(index as u32)])
        }),
    )
}

#[test]
fn exact_resource_lookup_is_indexed_after_context_construction() {
    let required = CResourceFact::own_token("target".to_string(), vec![int32(0)]);
    for size in [16, 32, 64, 128] {
        let context = unrelated_token_context(size).unchecked_with_fact(required.clone());
        assert!(context.satisfies_fact(&required, &Assumptions::new()));
        let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.satisfies_fact(&required, &Assumptions::new())
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
            assert!(context.satisfies_fact(&required, &Assumptions::new()));
            let (satisfied, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.satisfies_fact(&required, &Assumptions::new())
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
                context.satisfies_fact(&required, &Assumptions::new())
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
                context.normalized(&Assumptions::new())
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
                context.normalized(&Assumptions::new())
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
                context.validity_error(&Assumptions::new())
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
                        .observable_facts(&Assumptions::new())
                        .expect("structurally disjoint memory ranges should compose")
                });
                assert_eq!(facts.len(), 1, "size-{size} projection materialized pairs");
                assert!(matches!(facts[0], Proposition::CResourceComposition(_)));
                assert!(Assumptions::new().proves(&Proposition::CResourceSeparate {
                    left: context.facts()[0].resource().clone(),
                    right: context.facts()[size - 1].resource().clone(),
                }));
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
                &Assumptions::new(),
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
fn declared_resource_families_accumulate_equal_owned_units() {
    for fact in [
        CResourceFact::own_token("token".to_string(), vec![int32(0)]),
        CResourceFact::own_composite("box".to_string(), vec![int32(1)]),
    ] {
        let context = ResourceContext::new()
            .try_compose_with_facts([fact.clone(), fact.clone()], &Assumptions::new())
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
            .without_fact(&viewed, &Assumptions::new())
            .expect("owned exact resource should satisfy its view");
        assert_eq!(after_view.facts(), &[owned]);
    }
}

#[test]
fn declared_resources_normalize_and_consume_one_unit_at_a_time() {
    let unit = CResourceFact::own_token("object_ref".to_string(), vec![int32(7)]);
    let context = ResourceContext::new()
        .try_compose_with_facts([unit.clone(), unit.clone()], &Assumptions::new())
        .expect("equal counted facts should compose");

    assert_eq!(context.facts().len(), 1);
    assert_eq!(context.facts()[0].owned_quantity(), Some(2));

    let remaining = context
        .without_fact(&unit, &Assumptions::new())
        .expect("one unit should be consumable from a count of two");
    assert_eq!(remaining.facts(), &[unit]);
}

#[test]
fn declared_resource_quantities_are_part_of_context_equality() {
    let unit = CResourceFact::own_token("object_ref".to_string(), vec![int32(7)]);
    let one = ResourceContext::new()
        .try_compose_with_fact(unit.clone(), &Assumptions::new())
        .unwrap();
    let two = ResourceContext::new()
        .try_compose_with_facts([unit.clone(), unit], &Assumptions::new())
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
        &Assumptions::new(),
    ));
    assert!(resource_contexts_definitionally_equal_with_definitions(
        &[],
        &CMemory::new(),
        &two_uncompacted,
        &CMemory::new(),
        &two,
        &Assumptions::new(),
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
                context.without_fact_delaying_normalization(&required, &Assumptions::new())
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

    assert_eq!(facts.len(), 1);
    assert!(matches!(facts[0], Proposition::CResourceComposition(_)));
    assert!(Assumptions::new().proves(&Proposition::CResourceSeparate {
        left: CResource::Memory(left),
        right: CResource::Memory(right),
    }));
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
        .unchecked_with_fact(CResourceFact::own(memory.clone()))
        .unchecked_with_fact(CResourceFact::own(token.clone()))
        .unchecked_with_fact(CResourceFact::own(other_token.clone()))
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
    let left = CResourceFact::own(CResource::Composite {
        name: "list".to_string(),
        arguments: vec![CValue::Pointer(left_pointer.clone())],
    });
    let right = CResourceFact::own(CResource::Composite {
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
