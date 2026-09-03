use super::*;

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
            arguments: vec![int32(7)],
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
            arguments: vec![int32(7)],
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
            arguments: vec![int32(7)],
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
            arguments: vec![int32(7)],
        },
        quantity.clone(),
    );
    let state = CState::new()
        .with_resource_context(ResourceContext::new().unchecked_with_fact(resource.clone()))
        .with_counted_population("symbolic", vec![int32(7)], count.clone());
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
            CValue::Pointer(Pointer {
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
            arguments: Vec::new(),
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
        arguments: vec![int32(9)],
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
        arguments: vec![int32(9)],
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
            arguments: vec![int32(9)],
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
            arguments: vec![int32(size + 1)],
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
            arguments: Vec::new(),
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
                arguments: vec![],
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
        arguments: vec![CValue::Pointer(left_pointer.clone())],
    });
    let right = CResourceFact::own(CResource::Composite {
        name: "list".to_string(),
        arguments: vec![CValue::Pointer(right_pointer.clone())],
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
        arguments: vec![],
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
        vec![CResourceSpec::OwnMemory(CMemorySegment {
            base: c_variable("item"),
            start: c_int32_literal(0),
            end: c_int32_literal(1),
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
                    vec![CValue::Pointer(pointer(index))],
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
