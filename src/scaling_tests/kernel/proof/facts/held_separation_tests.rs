// Scaling tests of `src/kernel/proof/facts.rs` (module `held_separation_tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// Same-block unrelated members must not turn one selected observation
/// into a frame scan or an enumeration of ownership pairs.
#[test]
fn held_separation_uses_only_the_selected_members() {
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let resources = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|index| ResourceFact::own(cell(index))));
        let state = ExecutionState::new().with_resource_context(resources);
        let facts = ProofFacts::default();
        let goal = separation(cell(size - 2), cell(size - 1));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let observed = facts.with_selected_held_resource_separation(&goal, &state);
            assert!(observed.contains(&goal));
            assert_eq!(observed.fact_count(), 1);
        });
        samples.push(work);
    }
    assert!(samples.iter().all(|work| *work > 0));
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 32),
        "selected separation inspected unrelated ownership: {samples:?}"
    );
}

#[test]
fn held_field_separation_does_not_visit_unrelated_owners() {
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        // Keep term-bridge imports cold at every sample size.
        crate::kernel::clear_integer_bridge_memo();
        let state = ExecutionState::new().with_resource_context(
            ResourceContext::new().unchecked_with_facts(
                (0..size).map(|index| ResourceFact::own(range(index, 0, 6, 4))),
            ),
        );
        let goal = separation(range(size - 2, 1, 2, 8), range(size - 1, 0, 1, 8));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                ProofFacts::default()
                    .with_selected_held_resource_separation(&goal, &state)
                    .contains(&goal)
            );
        });
        samples.push(work);
    }
    assert!(samples.iter().all(|work| *work > 0));
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "selected fields visited unrelated owners: {samples:?}"
    );
}

#[test]
fn held_separation_transitive_alias_uses_the_shared_resource_index() {
    let _session = crate::kernel::VerificationSession::enter();
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        // Keep term-bridge imports cold at every sample size.
        crate::kernel::clear_integer_bridge_memo();
        let pointer = |index| {
            let Resource::Memory(range) = cell(index) else {
                unreachable!()
            };
            range.base().clone()
        };
        let link = |a, b| {
            Proposition::ConditionIs(ConditionTerm::pointer_equal(pointer(a), pointer(b)), true)
        };
        let mut facts = ProofFacts::from_ordered(&[link(0, size + 1), link(size + 1, size + 2)]);
        for index in 0..size {
            facts = facts.with_fact(link(size + 10 + 2 * index, size + 11 + 2 * index));
        }
        let resources = ResourceContext::new_with_equalities(facts.assumptions())
            .unchecked_with_facts((0..size).map(|index| ResourceFact::own(range(index, 0, 6, 4))));
        let state = ExecutionState::new().with_resource_context(resources);
        let goal = separation(range(size + 2, 1, 2, 8), range(1, 0, 1, 8));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                facts
                    .with_selected_held_resource_separation(&goal, &state)
                    .contains(&goal)
            );
        });
        samples.push(work);
    }
    assert!(samples.iter().all(|work| *work > 0));
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "transitive selected ownership visited unrelated inputs: {samples:?}"
    );
}

#[test]
fn exact_partition_known_ignores_unselected_members_and_refuses_two_views() {
    let mut work = Vec::new();
    for count in [4, 16, 64, 256] {
        let owned = cell(0);
        let viewed = cell(1);
        let resources = ResourceContext::new().unchecked_with_facts(
            std::iter::once(ResourceFact::own(owned.clone()))
                .chain(std::iter::once(ResourceFact::View(viewed.clone())))
                .chain((2..count).map(|i| ResourceFact::View(cell(i)))),
        );
        let goal = separation(owned.clone(), viewed.clone());
        let (_, cost) = crate::instrumentation::measure_deterministic_work(|| {
            let _guard = crate::kernel::search::FastOperationScope::enter("exact partition known");
            let facts = ProofFacts::default().with_exact_partition_separation(&goal, &resources);
            assert!(facts.contains(&goal));
            assert!(resources.proves_exact_partition_separation(&viewed, &owned));
            assert!(!resources.proves_exact_partition_separation(&viewed, &cell(2)));
            assert!(!resources.proves_exact_partition_separation(&owned, &owned));
            assert!(!resources.proves_exact_partition_separation(&owned, &cell(count + 1)));
        });
        work.push(cost);
    }
    assert!(
        work.windows(2).all(|pair| pair[1] <= pair[0] + 32),
        "{work:?}"
    );
}

#[test]
fn exact_partition_known_does_not_treat_supported_views_as_independent() {
    let owner = ResourceFact::own(range(0, 0, 2, 4));
    let projected = range(0, 0, 1, 4);
    let resources = ResourceContext::new()
        .unchecked_with_facts([owner.clone()])
        .unchecked_with_supported_facts(&owner, [ResourceFact::View(projected.clone())]);
    assert!(!resources.proves_exact_partition_separation(owner.resource(), &projected));
}

#[test]
fn separation_carrier_key_ignores_unrelated_facts() {
    let mut samples = Vec::new();
    for size in [4, 16, 64, 256] {
        let mut facts = ProofFacts::default();
        for index in 0..size {
            facts = facts.with_fact(separation(cell(index + 10), cell(index + 1000)));
        }
        let held = separation(cell(0), cell(1));
        let goal = separation(alternate_carrier(cell(0)), cell(1));
        let (_, cost) = crate::instrumentation::measure_deterministic_work(|| {
            let _guard =
                crate::kernel::search::FastOperationScope::enter("spatial separation lookup");
            let facts = facts.with_fact(held);
            assert!(facts.contains(&goal));
        });
        samples.push(cost);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn partition_spatial_lookup_ignores_unrelated_owners() {
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let resources = ResourceContext::new()
            .unchecked_with_facts((0..size).map(|i| ResourceFact::own(cell(i))));
        let (_, cost) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(
                resources.proves_exact_partition_separation(&alternate_carrier(cell(0)), &cell(1))
            );
        });
        samples.push(cost);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn byte_partition_keys_ignore_related_views_and_unrelated_members() {
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let left = cell(0);
        let right = cell(1);
        let mut input = vec![ResourceFact::own(left.clone())];
        for index in 0..size {
            let Resource::Memory(mut viewed) = right.clone() else {
                unreachable!()
            };
            let Resource::Memory(origin) = cell(10_000 + index) else {
                unreachable!()
            };
            viewed = viewed
                .with_designation(Arc::new(origin.base().clone()))
                .with_opaque_extent(Some(Arc::new(origin.base().clone())), false)
                .with_typed_carrier();
            input.push(ResourceFact::View(Resource::Memory(viewed)));
            input.push(ResourceFact::own(cell(100_000 + index)));
        }
        let resources = ResourceContext::new().unchecked_with_facts(input);
        let byte_spelling = |resource: &Resource| {
            let Resource::Memory(range) = resource else {
                unreachable!()
            };
            Resource::Memory(MemoryRange::new_with_element_width(
                range.base().clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(4),
                1,
            ))
        };
        let a = byte_spelling(&left);
        let b = byte_spelling(&right);
        let ((hit, same, missing), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                (
                    resources.proves_exact_partition_separation(&a, &b),
                    resources.proves_exact_partition_separation(&a, &left),
                    resources.proves_exact_partition_separation(&a, &cell(999_999)),
                )
            });
        assert!(hit && !same && !missing);
        let withdrawn = resources
            .clone()
            .without_exact_representation(&ResourceFact::own(left))
            .unwrap();
        assert!(!withdrawn.proves_exact_partition_separation(&a, &b));
        assert!(resources.proves_exact_partition_separation(&a, &b));
        samples.push(work);
    }
    assert!(
        samples[0] > 0 && samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}
