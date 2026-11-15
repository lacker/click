// Scaling tests of `src/kernel/tests/memory_reasoning_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::binary_node;
use crate::kernel::{CompareRelation, MachineIntegerType};

/// Unaddressable scalar declarations keep their permissions without growing
/// the observable pointer frame. Addressable locals must remain observable.
#[test]
fn unaddressable_scalar_owners_do_not_restate_observable_memory_frames() {
    let saved = crate::kernel::capture_block_registries();
    let base = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(93_600)),
            },
            0u32.into(),
            1u32.into(),
        )))
        .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(93_601)),
            },
            0u32.into(),
            1u32.into(),
        )));
    let assumptions = PureFactContext::new();
    let expected = base.observable_facts_assuming_valid(&assumptions);
    let mut measured_work = Vec::new();
    for count in [0, 16, 64, 256] {
        crate::kernel::set_never_address_taken_locals(
            (0..count).map(|i| format!("hidden_{i}")).collect(),
        );
        let mut resources = base.clone();
        for i in 0..count {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(
                    Memory::local_pointer(&format!("hidden_{i}")),
                    0u32.into(),
                    4u32.into(),
                    1,
                ),
            ));
        }
        let (observed, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.observable_facts_assuming_valid(&assumptions)
        });
        assert_eq!(observed, expected);
        measured_work.push((count, work));
        assert_eq!(resources.facts().len(), count + 2);
        let addressed = ResourceFact::own_memory(MemoryRange::new(
            Memory::local_pointer("addressed"),
            0u32.into(),
            1u32.into(),
        ));
        let observable = resources
            .unchecked_with_fact(addressed.clone())
            .observable_facts_assuming_valid(&assumptions);
        assert!(observable.iter().any(|fact| matches!(fact, Proposition::ResourceComposition(context) if context.facts().contains(&addressed))));
    }
    crate::kernel::restore_block_registries(&saved);
    assert!(
        measured_work
            .iter()
            .all(|(count, work)| *work <= measured_work[0].1 * 4 + *count * 128 + 32),
        "observable frame projection exceeded bounded work: {measured_work:?}"
    );
}

#[test]
fn memory_range_endpoint_graph_matching_scales_without_fact_index() {
    for size in [16u64, 64, 256, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let variable = |id| MachineTerm::Variable(Variable(42_000 + id));
        let mut assumptions = PureFactContext::new();
        for index in 0..size {
            assumptions = assumptions.assume_condition(
                ConditionTerm::equal(variable(index), variable(index + 1)),
                true,
            );
        }
        let resource = |index| {
            Resource::Memory(MemoryRange::new(
                Pointer::symbolic(Variable(43_000)),
                MachineTerm::constant(0),
                MachineTerm::add(variable(index), MachineTerm::constant(1)),
            ))
        };
        let left = resource(0);
        let _scope = assumptions.enter_id_scope();
        PureFactContext::reset_bitvector_equality_index_fact_visits();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 1..=size {
                assert!(resources_directly_match(
                    &left,
                    &resource(index),
                    &assumptions,
                ));
            }
        });
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn loadability_transports_checked_aliases_without_scanning_unrelated_facts() {
    let memory = Memory::new();
    let storage = Pointer {
        block: "viewed-storage".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let result = Pointer {
        block: PointerBlock::Symbolic(Variable(9_300_100)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let equality = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(result.clone(), storage.clone()),
        true,
    );
    let view = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: storage.clone(),
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    let goal = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: result.clone(),
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new().assume_proposition(equality.clone())),
        &goal
    ));
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new().assume_proposition(view.clone())),
        &goal
    ));
    let samples = [8, 32, 128].map(|size| {
        let mut context = PureFactContext::new()
            .assume_proposition(equality.clone())
            .assume_proposition(view.clone());
        for index in 0..size {
            context = context.assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: Pointer {
                    block: format!("unrelated-view-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                bytes: MachineTerm::constant(4),
                wide: false,
            });
        }
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::search::ProofSearch::proves(&(context), &goal)
        });
        assert!(proved);
        assert!(!crate::kernel::search::ProofSearch::proves(
            &(context),
            &Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: result.offset_by_bytes(4),
                bytes: MachineTerm::constant(4),
                wide: false,
            }
        ));
        work
    });
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "alias transport work: {samples:?}"
    );

    let local = Memory::local_pointer("expired-view");
    let before = Memory::new().with_block("local:expired-view", 4);
    let after = before.without_local_block(&local.block);
    let context = PureFactContext::new()
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(result.clone(), local.clone()),
            true,
        ))
        .assume_proposition(Proposition::MemoryLoadable {
            memory: before,
            base: local,
            bytes: MachineTerm::constant(4),
            wide: false,
        });
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(context),
        &Proposition::MemoryLoadable {
            memory: after,
            base: result,
            bytes: MachineTerm::constant(4),
            wide: false,
        }
    ));
}

#[test]
fn memory_loadable_query_ignores_same_block_unrelated_pointer_shapes() {
    let memory = Memory::new();
    let target = Pointer {
        block: "indexed-viewable-shapes".into(),
        offset: PointerOffsetTerm::Constant(10_000),
    };
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions =
                PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
                    memory: memory.clone(),
                    base: target.clone(),
                    bytes: MachineTerm::constant(8),
                    wide: false,
                });
            for index in 0..size {
                assumptions = assumptions.assume_proposition(Proposition::MemoryLoadable {
                    memory: memory.clone(),
                    base: Pointer {
                        block: target.block.clone(),
                        offset: PointerOffsetTerm::Constant(index as i64),
                    },
                    bytes: MachineTerm::constant(4),
                    wide: false,
                });
            }
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::search::ProofSearch::proves(
                    &(assumptions),
                    &Proposition::MemoryLoadable {
                        memory: memory.clone(),
                        base: target.clone(),
                        bytes: MachineTerm::constant(4),
                        wide: false,
                    },
                )
            });
            assert!(proved);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed viewability query should not inspect unrelated pointer shapes: {samples:?}"
    );
}

#[test]
fn composition_store_separation_uses_checked_aliases_without_scanning_other_owners() {
    use crate::kernel::memory_provenance::owned_composition_store_separated_evidence;

    let parameter = |id| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(id)), 4),
    };
    let write_base = parameter(95_001);
    let read = parameter(95_002);
    let owner = Pointer::symbolic(Variable(95_003));
    let alias = ConditionTerm::pointer_equal(write_base.clone(), owner.clone());
    for offset in [0, 8] {
        let write = write_base.offset_by_bytes(offset);
        let mut samples = Vec::new();
        for size in [8, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let resources = (0..size)
                .map(|index| own_memory_fact(parameter(96_000 + index), 0, 1))
                .chain([
                    own_memory_fact(owner.clone(), offset / 4, offset / 4 + 1),
                    own_memory_fact(read.clone(), 0, 1),
                ])
                .fold(ResourceContext::new(), ResourceContext::unchecked_with_fact);
            let without_alias = PureFactContext::new()
                .assume_proposition(Proposition::ResourceComposition(resources));
            let assumptions = without_alias.clone().assume_condition(alias.clone(), true);
            let (hop, work) = crate::instrumentation::measure_deterministic_work(|| {
                owned_composition_store_separated_evidence(&write, 4, &read, 4, &assumptions)
            });
            let hop = hop.expect("the store's exact alias names its owned member");
            let store = MemoryDerivation::Store {
                base: crate::kernel::intern_memory(Memory::new()),
                pointer: write.clone(),
                value: int32(7).into(),
            };
            assert!(hop.checks(&store, &read, 4, &assumptions));
            assert!(!hop.checks(&store, &read, 4, &without_alias));
            assert!(!hop.checks(&store, &read, 8, &assumptions));
            assert!(
                owned_composition_store_separated_evidence(&write, 4, &read, 4, &without_alias)
                    .is_none()
            );
            assert!(
                owned_composition_store_separated_evidence(&write, 8, &read, 4, &assumptions)
                    .is_none()
            );
            assert!(
                owned_composition_store_separated_evidence(&write, 4, &read, 8, &assumptions)
                    .is_none()
            );
            let wider_store = MemoryDerivation::Store {
                base: crate::kernel::intern_memory(Memory::new()),
                pointer: write.clone(),
                value: int64(7).into(),
            };
            assert!(!hop.checks(&wider_store, &read, 4, &assumptions));
            let equal = assumptions.assume_condition(
                ConditionTerm::pointer_equal(write.clone(), read.clone()),
                true,
            );
            assert!(
                owned_composition_store_separated_evidence(&write, 4, &read, 4, &equal).is_none()
            );
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[0] == pair[1]),
            "{samples:?}"
        );
    }
}

/// Load equality resolves through a chain of stored cells of any length:
/// each memory's cell holds the load of the next memory's cell, and the
/// chain ends at a constant. Each hop is one memoized query, so the work
/// follows the chain; the alias depth of 64 that used to cut the recursion
/// refused every chain past it.
#[test]
fn load_equality_resolves_through_stored_cell_chains_of_any_length() {
    let base = Pointer {
        block: "chain".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let cell = |index: usize| base.offset_by_elements(MachineTerm::constant(index as u32), 4);
    let mut samples = Vec::new();
    for length in [32usize, 64, 96, 128] {
        let mut memory =
            Memory::new().store(cell(length), ProgramValue::Int32(MachineTerm::constant(42)));
        for index in (0..length).rev() {
            let next = MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory),
                Box::new(cell(index + 1)),
                crate::kernel::LoadKind::Int32,
            );
            memory = Memory::new().store(cell(index), ProgramValue::Int32(next));
        }
        let load = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(memory),
            Box::new(cell(0)),
            crate::kernel::LoadKind::Int32,
        );
        let (proven, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                &load,
                &MachineTerm::constant(42),
                &PureFactContext::new(),
            )
        });
        assert!(
            proven,
            "a chain of {length} stored cells resolves to its constant"
        );
        samples.push((length, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "load resolution through a cell chain is superlinear: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 1.4s in the parallel gate"]
fn shifted_constant_view_extents_match_without_ambient_search() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = Memory::new();
    let base = Pointer::symbolic(Variable(9_319_000));
    let index = MachineTerm::Variable(Variable(9_319_001));
    let count = |length| {
        binary_node!(
            Int32,
            Subtract,
            Box::new(binary_node!(
                Int32,
                Add,
                Box::new(index.clone()),
                Box::new(MachineTerm::constant(length)),
            )),
            Box::new(index.clone()),
        )
    };
    let source = |bytes| Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes,
        wide: false,
    };
    for width in [1, 2, 4, 8, 16] {
        let bytes = if width == 1 {
            count(4)
        } else {
            binary_node!(
                Int32,
                Multiply,
                Box::new(count(4)),
                Box::new(MachineTerm::constant(width)),
            )
        };
        let mut costs = Vec::new();
        for size in [0, 16, 64, 256, 1024] {
            let mut context = PureFactContext::new().assume_proposition(source(bytes.clone()));
            for offset in 0..size {
                context = context.assume_condition(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(9_319_100 + offset)),
                        MachineTerm::constant(offset as u32),
                    ),
                    true,
                );
            }
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                context.proves_memory_loadable(&memory, &base, &MachineTerm::constant(4 * width))
            });
            assert!(proved);
            costs.push(work);
        }
        assert!(costs.iter().all(|cost| *cost == costs[0]), "{costs:?}");
        let context = PureFactContext::new().assume_proposition(source(bytes));
        assert!(!context.proves_memory_loadable(
            &memory,
            &base,
            &MachineTerm::constant(4 * width + 1),
        ));
        assert!(!context.proves_memory_loadable(
            &memory,
            &Pointer::symbolic(Variable(9_319_002)),
            &MachineTerm::constant(4 * width),
        ));
    }
    assert!(!PureFactContext::new().proves_memory_loadable(
        &memory,
        &base,
        &MachineTerm::constant(4),
    ));
    let wrapped = binary_node!(
        Int32,
        Multiply,
        Box::new(count(0x4000_0000)),
        Box::new(MachineTerm::constant(4)),
    );
    assert!(
        !PureFactContext::new()
            .assume_proposition(source(wrapped))
            .proves_memory_loadable(&memory, &base, &MachineTerm::constant(4))
    );
}

#[test]
fn bounded_unsigned_native_indices_project_only_with_full_width_evidence() {
    let native = MachineTerm::Variable(Variable(983_110));
    let alias = MachineTerm::Variable(Variable(983_111));
    let last = |n| MachineTerm::uint64_subtract(n, MachineTerm::uint64_constant(1));
    let wide = |n| PointerOffsetTerm::scaled_int64_node(n, 4, true);
    let projected = MachineTerm::uint32_from_64(last(native.clone()));
    let query = wide(last(alias.clone()));
    let bound = ConditionTerm::uint64_less_equal(
        last(native.clone()),
        MachineTerm::uint64_constant(1_073_741_822),
    );
    let equality = ConditionTerm::uint64_equal(alias.clone(), native.clone());
    let project = |facts: &PureFactContext| {
        crate::kernel::reasoning::element_index_from_offset_with_facts(&query, 4, facts)
    };
    assert_eq!(project(&PureFactContext::new()), None);
    let bounded = PureFactContext::new().assume_condition(bound.clone(), true);
    assert_eq!(project(&bounded), None);
    let equal_only = PureFactContext::new().assume_condition(equality.clone(), true);
    assert_eq!(project(&equal_only), None);
    let low_bound =
        ConditionTerm::signed_less_equal(projected.clone(), MachineTerm::constant(1_073_741_822));
    assert_eq!(
        project(&equal_only.clone().assume_condition(low_bound, true)),
        None
    );
    let signed_bound = ConditionTerm::int64_signed_less_equal(
        last(native.clone()),
        MachineTerm::int64_constant(1_073_741_822),
    );
    assert_eq!(
        project(&equal_only.clone().assume_condition(signed_bound, true)),
        None
    );
    let mut measured = Vec::new();
    for count in [0, 2, 16, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut facts = bounded.clone().assume_condition(equality.clone(), true);
        for i in 0..count {
            facts = facts.assume_condition(
                ConditionTerm::uint64_less_equal(
                    MachineTerm::Variable(Variable(984_000 + i)),
                    MachineTerm::uint64_constant(7),
                ),
                true,
            );
        }
        // Measure the retained checking service. Native output export has a
        // process-wide memo, independent of the per-session syntax caches.
        let (answer, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::shared_element_index_from_offset_with_facts(&query, 4, &facts)
        });
        assert_eq!(
            answer.map(|index| index.structural_value().clone()),
            Some(projected.clone())
        );
        measured.push(work);
        assert!(facts.element_index_rebuild_is_exact_for_width(&query, 4));
        // Element projection is exact even though scaling the largest index
        // exceeds the signed byte word. It grants no unbounded byte projection.
        assert!(!facts.element_index_rebuild_is_exact_for_width(&query, 1));
    }
    assert!(
        measured.windows(2).all(|pair| pair[0] == pair[1]),
        "{measured:?}"
    );
    for value in [0, 1_073_741_823, 1u64 << 32, u64::MAX] {
        let actual = value.wrapping_sub(1);
        let offset = wide(last(MachineTerm::uint64_constant(value)));
        let answer = crate::kernel::reasoning::element_index_from_offset_with_facts(
            &offset,
            4,
            &PureFactContext::new(),
        );
        assert_eq!(
            answer,
            i32::try_from(actual)
                .ok()
                .map(|x| MachineTerm::constant(x as u32))
        );
    }
}

/// Ordering two states of one path, which share all but one of `size`
/// entries, reads their cached content hashes and never walks the shared
/// entries, for memories and for resource contexts alike: sets of facts and
/// of stated compositions compare such states at every lookup.
#[test]
fn ordering_states_of_one_path_does_not_walk_their_shared_entries() {
    let object = |index: u32| Pointer::symbolic(Variable(99_400 + u64::from(index)));
    for size in [16u32, 64, 256] {
        let mut memory = Memory::new();
        let mut resources = ResourceContext::new();
        for index in 0..size {
            memory = memory.store(object(index), int32(index));
            resources = resources.unchecked_with_fact(own_memory_fact(object(index), 0, 1));
        }
        let later_memory = memory.clone().store(object(0), int32(size));
        let later_resources =
            resources
                .clone()
                .unchecked_with_fact(own_memory_fact(object(size), 0, 1));
        let (orders, walked) = crate::kernel::primitives::count_structural_comparisons(|| {
            (
                memory.cmp(&later_memory),
                resources.cmp(&later_resources),
                memory.cmp(&memory.clone()),
                resources.cmp(&resources.clone()),
            )
        });
        assert_ne!(orders.0, std::cmp::Ordering::Equal, "size={size}");
        assert_ne!(orders.1, std::cmp::Ordering::Equal, "size={size}");
        assert_eq!(orders.2, std::cmp::Ordering::Equal, "size={size}");
        assert_eq!(orders.3, std::cmp::Ordering::Equal, "size={size}");
        assert_eq!(walked, 0, "size={size}: ordering walked a state");
    }
}

/// Without a store owner, separation by ownership reads only the stated
/// compositions listed under the two objects' members
/// (`CompositionMemberIndex`). A path states, per object, a state of the
/// one context that holds them all and a separately built composition of
/// that object alone, as a call and an unfolding do. Admitting the last
/// composition, separating the newest object from the oldest, and failing to
/// separate an object from memory no composition owns each cost the same at
/// every size.
#[test]
fn store_separation_without_an_owner_reads_only_listed_compositions() {
    let object = |index: u32| Pointer::symbolic(Variable(98_900 + u64::from(index)));
    let unowned = Pointer::symbolic(Variable(98_899));
    let mut admitted = Vec::new();
    let mut proved = Vec::new();
    let mut refused = Vec::new();
    for size in [8u32, 16, 32, 128] {
        let mut resources = ResourceContext::new();
        let mut context = PureFactContext::new();
        let mut last = 0;
        for index in 0..size {
            resources = resources.unchecked_with_fact(own_memory_fact(object(index), 0, 1));
            let alone =
                ResourceContext::new().unchecked_with_fact(own_memory_fact(object(index), 0, 1));
            let (next, used) = crate::instrumentation::measure_deterministic_work(|| {
                context
                    .clone()
                    .assume_proposition(Proposition::ResourceComposition(resources.clone()))
                    .assume_proposition(Proposition::ResourceComposition(alone))
            });
            context = next;
            last = used;
        }
        admitted.push(last);
        let (newest, oldest) = (object(size - 1), object(0));
        let (separated, used) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_provenance::owned_composition_store_separated_evidence(
                &newest, 4, &oldest, 4, &context,
            )
            .is_some()
        });
        assert!(separated, "size={size}");
        proved.push(used);
        let (separated, used) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_provenance::owned_composition_store_separated_evidence(
                &newest, 4, &unowned, 4, &context,
            )
            .is_some()
        });
        assert!(!separated, "size={size}");
        refused.push(used);
    }
    for (what, work) in [
        ("admitting a composition", &admitted),
        ("separating two owned objects", &proved),
        ("refusing an unowned load", &refused),
    ] {
        assert!(
            work.windows(2).all(|pair| pair[1] <= pair[0] + 4),
            "{what} grows with the compositions stated earlier: {work:?}"
        );
    }
}

/// A store is separated by what its writer owns now. A path that stated a
/// composition at each of `size` earlier steps leaves them all among the
/// context's facts, and store separation does not read them: with the
/// writer's current composition as the store owner, separating the newest
/// object from the oldest costs the same at every size, and still succeeds.
#[test]
fn store_separation_work_is_independent_of_earlier_compositions() {
    let object = |index: u32| Pointer::symbolic(Variable(98_300 + u64::from(index)));
    let mut work = Vec::new();
    for size in [8u32, 32, 128] {
        let mut resources = ResourceContext::new();
        let mut context = PureFactContext::new();
        for index in 0..size {
            resources = resources.unchecked_with_fact(own_memory_fact(object(index), 0, 1));
            context =
                context.assume_proposition(Proposition::ResourceComposition(resources.clone()));
        }
        let context = context.with_store_owner(Some(resources));
        let (first, last) = (object(0), object(size - 1));
        let (separated, used) = crate::instrumentation::measure_deterministic_work(|| {
            let footprint = context.owned_store_footprint(&last, 4);
            (
                context.access_owned_apart_from_store(&footprint, &last, &first, 4),
                crate::kernel::memory_provenance::owned_composition_store_separated_evidence(
                    &last, 4, &first, 4, &context,
                )
                .is_some(),
            )
        });
        assert_eq!(separated, (true, true), "size={size}");
        work.push(used);
    }
    assert!(
        work.windows(2).all(|pair| pair[1] <= pair[0] + 8),
        "store separation work grows with the compositions stated earlier: {work:?}"
    );
}

/// Ownership lookup declines an aliased access and accepts the written owned
/// address. Neither query visits aliases of unrelated owned objects. The
/// corresponding C proof supplies separation and transports the read explicitly.
#[test]
fn written_store_separation_and_alias_refusal_ignore_unrelated_objects() {
    let pointer = |index: u64| Pointer::symbolic(Variable(97_100 + index));
    let equal = |left: &Pointer, right: &Pointer| {
        Proposition::ConditionIs(
            ConditionTerm::pointer_equal(left.clone(), right.clone()),
            true,
        )
    };
    let (q, identity, marker) = (pointer(0), pointer(1), pointer(2));
    let write = q.offset_by_bytes(8);
    for explicit_owners in [false, true] {
        let mut work = Vec::new();
        for size in [8u64, 32, 128] {
            let mut resources = ResourceContext::new()
                .unchecked_with_fact(own_memory_fact(identity.clone(), 2, 4))
                .unchecked_with_fact(own_memory_fact(marker.clone(), 0, 1));
            let mut context = PureFactContext::new().assume_proposition(equal(&q, &identity));
            for index in 0..size {
                let (object, alias) = (pointer(10 + 2 * index), pointer(11 + 2 * index));
                resources = resources.unchecked_with_fact(own_memory_fact(object.clone(), 0, 4));
                context = context.assume_proposition(equal(&alias, &object));
            }
            let context =
                context.assume_proposition(Proposition::ResourceComposition(resources.clone()));
            let context = if explicit_owners {
                context.with_store_owner(Some(resources))
            } else {
                context
            };
            let (separated, used) = crate::instrumentation::measure_deterministic_work(|| {
                let footprint = context.owned_store_footprint(&write, 8);
                let aliased = context.access_owned_apart_from_store(&footprint, &write, &marker, 4);
                let written = identity.offset_by_bytes(8);
                let footprint = context.owned_store_footprint(&written, 8);
                (
                    aliased,
                    context.access_owned_apart_from_store(&footprint, &written, &marker, 4),
                )
            });
            assert_eq!(separated, (false, true), "size={size}");
            work.push(used);
        }
        assert!(
            work.windows(2).all(|pair| pair[1] <= pair[0] + 8),
            "aliased store separation work grows with unrelated objects (explicit owners={explicit_owners}): {work:?}"
        );
    }
}

#[test]
fn stated_pointer_separation_lookup_visits_only_its_anchor_index() {
    for cross_block in [false, true] {
        let pointer = |id, right| Pointer {
            block: if right && cross_block {
                PointerBlock::Symbolic(Variable(941_000))
            } else {
                PointerBlock::ExternalArgument
            },
            offset: PointerOffsetTerm::Variable(Variable(id)),
        };
        let fact = |id| Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(memory_range(pointer(id, false), 0, 1))),
            right: Box::new(Resource::Memory(memory_range(pointer(id + 1, true), 0, 1))),
        };
        let left = pointer(1, false);
        let right = pointer(2, true);
        let comparison = ConditionTerm::pointer_equal(left.clone(), right.clone());
        let mut overhead = Vec::new();
        let mut proof_overhead = Vec::new();
        for size in [16u64, 64, 256, 1024] {
            let mut context = PureFactContext::new().assume_proposition(fact(1));
            for index in 0..size {
                context = context.assume_proposition(fact(100 + index * 2));
            }
            let comparisons = if cross_block {
                context.separated_anchor_pointers.lookup_comparisons(
                    &PureFactContext::separated_pointer_key(left.clone(), right.clone()),
                )
            } else {
                context.separated_anchor_offsets.lookup_comparisons(
                    &PureFactContext::separated_anchor_key(
                        left.offset.clone(),
                        right.offset.clone(),
                    ),
                )
            };
            let ((result, _work), work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    context.decide_pointer_disequality(&comparison)
                })
            });
            assert_eq!(result, Some(false));
            assert!(work >= comparisons);
            overhead.push(work - comparisons);
            let goal = Proposition::ConditionIs(comparison.clone(), false);
            let (known, proof_work) =
                crate::persistent::measure_persistent_work(|| context.contains_known(&goal));
            assert!(known);
            assert!(proof_work >= comparisons);
            proof_overhead.push(proof_work - comparisons);
            let height_bound = 2 * (size + 2).ilog2() as usize + 2;
            assert!(
                comparisons <= height_bound,
                "persistent anchor lookup follows tree height"
            );
        }
        assert!(
            proof_overhead.iter().all(|work| *work == proof_overhead[0]),
            "proof lookup only grows with the selected tree path: {proof_overhead:?}"
        );
        assert!(
            overhead.iter().all(|work| *work == overhead[0]),
            "only the selected tree path may grow: {overhead:?}"
        );
    }
}

#[test]
fn kept_frame_class_lookup_adds_only_selected_physical_coverage() {
    let pointer = |id| Pointer {
        block: PointerBlock::Symbolic(Variable(id)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let queried = pointer(951_001);
    let middle = pointer(951_002);
    let owner = pointer(951_003);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_equal(queried.clone(), middle.clone()),
            true,
        )
        .assume_condition(ConditionTerm::pointer_equal(middle, owner.clone()), true);
    let fact = |base| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base,
            0u32.into(),
            1u32.into(),
            8,
        ))
    };
    for size in [4u64, 16, 64, 256] {
        let mut ranges = ResourceContext::new_with_equalities(&assumptions)
            .unchecked_with_fact(fact(owner.clone()));
        for index in 0..size {
            ranges = ranges.unchecked_with_fact(fact(pointer(952_000 + index)));
        }
        let ((ordinary, ordinary_work), ordinary_maps) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    ranges
                        .memory_write_range(&queried, 8, &assumptions)
                        .is_some_and(|range| assumptions.kept_range_holds_access(range, &owner, 8))
                })
            });
        assert!(ordinary);
        let kept = crate::kernel::primitives::CallKeptRanges::new(ranges, Vec::new(), None);
        let ((found, frame_work), frame_maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                kept.holds_access(&queried, 8, &assumptions)
            })
        });
        assert!(found);
        assert!(
            frame_work <= ordinary_work,
            "frame adds no owner scan at size {size}"
        );
        assert!(
            frame_maps <= ordinary_maps,
            "frame adds no map traversal at size {size}"
        );
    }
}

#[test]
fn rechecked_kept_frame_checks_selected_equality_without_rebuilding_foreign_inputs() {
    let pointer = |id| Pointer::symbolic(Variable(id));
    let queried = pointer(954_001);
    let middle = pointer(954_002);
    let owner = pointer(954_003);
    for size in [4u64, 16, 64, 256] {
        let inputs = || {
            let mut facts = PureFactContext::new()
                .assume_condition(
                    ConditionTerm::pointer_equal(queried.clone(), middle.clone()),
                    true,
                )
                .assume_condition(
                    ConditionTerm::pointer_equal(middle.clone(), owner.clone()),
                    true,
                );
            for index in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::pointer_equal(
                        pointer(955_000 + index),
                        pointer(957_000 + index),
                    ),
                    true,
                );
            }
            facts
        };
        let first = inputs();
        let recheck = inputs();
        let control = inputs();
        let mut ranges = ResourceContext::new_with_equalities(&first).unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(owner.clone(), 2u32.into(), 4u32.into())),
        );
        for index in 0..size {
            ranges = ranges.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                pointer(955_000 + index),
                0u32.into(),
                1u32.into(),
            )));
        }
        let kept = crate::kernel::primitives::CallKeptRanges::new(ranges, Vec::new(), None);
        let access = queried.offset_by_bytes(8);
        let ((expected, expected_work), expected_maps) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    kept.holds_access(&access, 8, &first)
                        && control.pointers_known_equal(&access, &owner.offset_by_bytes(8))
                })
            });
        assert!(expected);
        let ((found, work), maps) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                kept.holds_access(&access, 8, &recheck)
            })
        });
        assert!(found);
        assert!(
            work <= expected_work,
            "recheck rebuilds unrelated inputs at size {size}: {work} > {expected_work}"
        );
        assert!(
            maps <= expected_maps,
            "recheck traverses unrelated inputs at size {size}: {maps} > {expected_maps}"
        );
    }
}

#[test]
fn one_owned_member_does_not_trigger_store_alias_reasoning() {
    use crate::kernel::memory_provenance::{
        count_composition_store_alias_queries, owned_composition_store_separated_evidence,
    };

    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(99_700)), 4),
    };
    let index = MachineTerm::Variable(Variable(99_701));
    let write = base.offset_by_bytes(12);
    let read = base.offset_by_int32_elements(index.clone());
    let mut samples = Vec::new();
    for size in [4, 16, 64] {
        let resources =
            ResourceContext::new().unchecked_with_fact(own_memory_fact(base.clone(), 0, 64));
        let mut context = PureFactContext::new()
            .assume_proposition(Proposition::ResourceComposition(resources))
            .assume_condition(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: Box::new(0.into()),
                    right: Box::new(index.clone()),
                },
                true,
            )
            .assume_condition(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(index.clone()),
                    right: Box::new(64.into()),
                },
                true,
            );
        for unrelated in 0..size {
            context = context.assume_condition(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(MachineTerm::Variable(Variable(100_000 + unrelated))),
                    right: Box::new(1000.into()),
                },
                true,
            );
        }
        let ((result, alias_queries), work) =
            crate::instrumentation::measure_deterministic_work(|| {
                count_composition_store_alias_queries(|| {
                    owned_composition_store_separated_evidence(&write, 4, &read, 4, &context)
                })
            });
        assert!(
            result.is_none(),
            "one owned member cannot separate its own cells"
        );
        assert_eq!(
            alias_queries, 0,
            "no distinct owned members can justify separation"
        );
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
    eprintln!("single-member store separation work: {samples:?}");
}

#[test]
fn fixed_overlapping_ranges_ignore_unrelated_separation_facts() {
    let samples = [4u64, 8, 16, 32].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(9_893_000)), 4),
        };
        let outer = MemoryRange::new(base.clone(), 0u32.into(), 6u32.into());
        let inner = MemoryRange::new(base, 2u32.into(), 4u32.into());
        let mut facts = PureFactContext::new();
        for index in 0..size {
            let a = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    MachineTerm::Variable(Variable(9_894_000 + index * 2)),
                    4,
                ),
            };
            let b = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    MachineTerm::Variable(Variable(9_894_001 + index * 2)),
                    4,
                ),
            };
            facts = facts.assume_proposition(Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(MemoryRange::new(
                    a,
                    0u32.into(),
                    1u32.into(),
                ))),
                right: Box::new(Resource::Memory(MemoryRange::new(
                    b,
                    0u32.into(),
                    1u32.into(),
                ))),
            });
        }
        let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                &outer, &inner,
            )
        });
        assert!(
            !separate,
            "one fixed byte interval overlaps its own subrange"
        );
        work
    });
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "fixed overlap must not scan unrelated separation authority: {samples:?}"
    );
}

/// Without explicit store owners, history still supplies separation, but a
/// store must select compositions by both accesses rather than scan history.
#[test]
fn ownerless_store_separation_ignores_unrelated_composition_history() {
    let object = |index| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(950_000 + index)),
    };
    for growing_partition in [false, true] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut resources =
                ResourceContext::new().unchecked_with_fact(own_memory_fact(object(0), 0, 1));
            let mut context = PureFactContext::new()
                .assume_proposition(Proposition::ResourceComposition(resources.clone()));
            for index in 1..=size {
                if !growing_partition {
                    resources = ResourceContext::new();
                }
                resources = resources.unchecked_with_fact(own_memory_fact(object(index), 0, 1));
                context =
                    context.assume_proposition(Proposition::ResourceComposition(resources.clone()));
            }
            // Only this last composition holds the pair. In the growing
            // partition it adds the read, not the write: querying only the
            // write's index bucket would miss it.
            let write = object(if growing_partition { 0 } else { size });
            let read = object(size + 1);
            resources = resources.unchecked_with_fact(own_memory_fact(read.clone(), 0, 1));
            context = context.assume_proposition(Proposition::ResourceComposition(resources));
            let (answers, work) = crate::instrumentation::measure_deterministic_work(|| {
                let footprint = context.owned_store_footprint(&write, 4);
                (
                    context.access_owned_apart_from_store(&footprint, &write, &read, 4),
                    context.access_owned_apart_from_store(&footprint, &write, &object(size + 2), 4),
                )
            });
            assert_eq!(answers, (true, false));
            samples.push(work);
        }
        assert!(
            samples.windows(2).all(|pair| pair[1] <= pair[0] + 8),
            "ownerless store separation scans history (growing partition={growing_partition}): {samples:?}"
        );
    }
}
