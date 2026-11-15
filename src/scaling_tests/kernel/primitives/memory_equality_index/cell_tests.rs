// Scaling tests of `src/kernel/primitives/memory_equality_index/cell_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType};

#[test]
fn checked_attachment_is_flat_beside_unrelated_equality_history() {
    for raw_input in [false, true] {
        let mut samples = Vec::new();
        let (base, alias) = (
            Pointer::symbolic(Variable(867_000)),
            Pointer::symbolic(Variable(867_001)),
        );
        for size in [8u64, 32, 128, 512] {
            let initial = PureFactContext::new();
            let mut facts = initial.clone();
            for i in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(868_000 + i)),
                        MachineTerm::Variable(Variable(868_001 + i)),
                    ),
                    true,
                );
            }
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(base.clone(), alias.clone()),
                true,
            );
            let owner = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                base.clone(),
                0u32.into(),
                4u32.into(),
                1,
            ));
            let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let (input, additions) = if raw_input {
                        (
                            ResourceContext::new().unchecked_with_fact(owner),
                            Vec::new(),
                        )
                    } else {
                        (ResourceContext::new(), vec![owner])
                    };
                    if raw_input {
                        // A cold query in an earlier input state must not make
                        // full-input construction walk the later history.
                        let _ = input.concrete_read_entries(&alias, 4, &initial);
                    }
                    let resources = if raw_input {
                        input.normalized(&facts)
                    } else {
                        input
                            .try_compose_into_valid_context_delaying_normalization(
                                additions, &facts,
                            )
                            .unwrap()
                    };
                    assert!(
                        resources
                            .concrete_read_entries(&alias, 4, &facts)
                            .is_some_and(|entries| entries.exact())
                    );
                    assert!(
                        resources
                            .concrete_write_entries(&alias, 4, &facts)
                            .is_some_and(|entries| entries.exact())
                    );
                })
            });
            samples.push((size, work, map_work));
        }
        eprintln!("selected attachment work: {samples:?}");
        assert!(
            samples
                .iter()
                .all(|(_, work, _)| *work <= samples[0].1 + 64),
            "attachment walked equality history: {samples:?}"
        );
        assert!(
            samples.windows(2).all(|pair| pair[1].2 <= pair[0].2 + 256),
            "attachment rebuilt graph state: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 0.7s in the parallel gate"]
fn checked_composition_attaches_only_new_resource_occurrences() {
    let mut samples = Vec::new();
    let base = Pointer::symbolic(Variable(870_000));
    for size in [16u32, 64, 256, 1024] {
        let facts = PureFactContext::new();
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut resources = ResourceContext::new();
                for i in 0..size {
                    resources = resources
                        .try_compose_into_valid_context_delaying_normalization(
                            [view(&base, i * 8, i * 8 + 4)],
                            &facts,
                        )
                        .unwrap();
                    assert!(
                        resources
                            .concrete_read_entries(&base.offset_by_bytes(i * 8), 4, &facts)
                            .is_some_and(|entries| entries.exact())
                    );
                }
            })
        });
        samples.push((size, work, map_work));
    }
    let ratio = usize::try_from(samples[3].0 / samples[0].0).unwrap();
    assert!(
        samples[3].1 <= samples[0].1 * ratio * 3,
        "composition rescanned old resources: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * ratio * 4,
        "composition rebuilt old indexes: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn forks_before_publication_keep_indexed_candidates_without_input_rescans() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(859_000 + id)),
        };
        let empty = PureFactContext::new();
        // Both forks precede resource publication. Their term registrations
        // cannot be assumed to extend the published graph's local node IDs.
        let branch = empty.clone().assume_condition(
            ConditionTerm::pointer_offset_equal(at(0).offset, at(size).offset),
            true,
        );
        let sibling = empty.clone();
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(at(i), 0u32.into(), 4u32.into(), 1),
            ));
        }
        // This cold view must be superseded by the completed publication.
        assert!(
            resources
                .concrete_read_entries(&at(size), 4, &branch)
                .is_none()
        );
        resources.synchronize_memory_equalities(&empty);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert!(
                        resources
                            .concrete_read_entries(&at(size), 4, &branch)
                            .is_some_and(|entries| entries.exact())
                    );
                    assert!(
                        resources
                            .concrete_write_entries(&at(size), 4, &branch)
                            .is_some_and(|entries| entries.exact())
                    );
                    // Unsupported containment stays with its existing
                    // authority checker. This measurement covers pairing and
                    // supported graph candidates, not that separate search.
                    assert!(
                        resources
                            .concrete_read_entries(&at(size), 4, &sibling)
                            .is_none()
                    );
                    assert!(
                        resources
                            .concrete_read_entries(&at(0), 4, &empty)
                            .is_some_and(|entries| entries.exact())
                    );
                }
            })
        });
        assert!(!resources.permits_memory_read(&at(size), 4, &sibling));
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "fork query scanned the input: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "fork query rebuilt the input: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn normalization_keeps_fork_pairing_without_deferred_input_scans() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id: u64| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(859_200 + id)),
        };
        let parent = PureFactContext::new();
        let first = parent.clone().assume_condition(
            ConditionTerm::pointer_offset_equal(at(0).offset, at(size).offset),
            true,
        );
        let sibling = parent.clone().assume_condition(
            ConditionTerm::pointer_offset_equal(at(0).offset, at(size + 1).offset),
            true,
        );
        // Removing a zero owner forces a real normalization replacement and
        // renumbers the remaining entries; a no-op normalize is insufficient.
        let mut resources = ResourceContext::new().unchecked_with_fact(ResourceFact::Own(
            Resource::Memory(MemoryRange::new_with_element_width(
                at(size + 2),
                0u32.into(),
                4u32.into(),
                1,
            )),
            Box::new(MachineTerm::constant(0)),
        ));
        for i in (0..size).rev() {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(at(i), 0u32.into(), 4u32.into(), 1),
            ));
        }
        resources.synchronize_memory_equalities(&first);
        assert!(
            resources
                .concrete_read_entries(&at(size + 1), 4, &sibling)
                .is_some_and(|entries| entries.exact())
        );
        let resources = resources.normalized(&parent);
        assert_eq!(resources.storage.facts.len(), size as usize);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    for (facts, alias) in [
                        (&sibling, at(size + 1)),
                        (&first, at(size)),
                        (&parent, at(0)),
                    ] {
                        assert!(
                            resources
                                .concrete_read_entries(&alias, 4, facts)
                                .is_some_and(|entries| entries.exact())
                        );
                        assert!(
                            resources
                                .concrete_write_entries(&alias, 4, facts)
                                .is_some_and(|entries| entries.exact())
                        );
                        let cell =
                            MemoryRange::new_with_element_width(alias, 0u32.into(), 4u32.into(), 1);
                        assert_eq!(
                            resources
                                .memory_fact_candidates(&cell, true, facts)
                                .entries
                                .len(),
                            1
                        );
                    }
                }
            })
        });
        assert!(!resources.permits_memory_read(&at(size), 4, &sibling));
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "normalization deferred an input scan: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "normalization lost registered roots: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn first_memory_occurrence_on_a_sibling_uses_closed_equality_state() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id: u64| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(864_000 + id)),
        };
        let initial = PureFactContext::new();
        let mut parent = initial.clone();
        let mut sibling = initial;
        for i in 0..size {
            for (context, prefix) in [(&mut parent, 865_000), (&mut sibling, 866_000)] {
                *context = context.clone().assume_condition(
                    ConditionTerm::equal(
                        MachineTerm::Variable(Variable(prefix + i)),
                        MachineTerm::Variable(Variable(prefix + i + 1)),
                    ),
                    true,
                );
            }
        }
        sibling = sibling.assume_condition(
            ConditionTerm::pointer_offset_equal(at(0).offset, at(1).offset),
            true,
        );
        let resources = ResourceContext::new();
        resources.synchronize_memory_equalities(&parent);
        let resources = resources.unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(at(0), 0u32.into(), 4u32.into(), 1),
        ));
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    resources
                        .concrete_read_entries(&at(1), 4, &sibling)
                        .is_some_and(|entries| entries.exact())
                );
                assert!(resources.memory_write_range(&at(1), 4, &sibling).is_some());
                assert!(resources.permits_memory_read(&at(1), 4, &sibling));
            })
        });
        assert!(!resources.permits_memory_read(&at(1), 4, &parent));
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "first occurrence scanned unrelated equality inputs: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "first occurrence rebuilt equality state: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 1.1s in the parallel gate"]
fn whole_cell_write_merges_and_queries_do_not_scan_other_payloads() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(862_000 + id)),
        };
        let owner = ResourceFact::own_memory(MemoryRange::new(at(0), 0u32.into(), 1u32.into()));
        let mut resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        for i in 0..size {
            // Large footprint payload at the alias, plus unrelated owners.
            resources = resources
                .unchecked_with_fact(view(&at(1), 0, 8 + i as u32 * 4))
                .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                    at(i + 2),
                    0u32.into(),
                    1u32.into(),
                )));
        }
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let ((facts, merge_work), merge_map_work) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let facts = empty.assume_condition(
                        ConditionTerm::pointer_offset_equal(at(0).offset, at(1).offset),
                        true,
                    );
                    resources.synchronize_memory_equalities(&facts);
                    facts
                })
            });
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for bytes in [4, C_POINTER_BYTE_WIDTH] {
                    let entries = resources
                        .concrete_write_entries(&at(1), bytes, &facts)
                        .unwrap();
                    assert!(entries.exact());
                    assert_eq!(entries.count(), 1);
                    assert_eq!(
                        resources.memory_write_range(&at(1), bytes, &facts),
                        owner.memory_own_range()
                    );
                }
            })
        });
        samples.push((size, merge_work, merge_map_work, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32 && samples[3].3 <= samples[0].3 * 2 + 32,
        "write merge/query scanned other payloads: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128 && samples[3].4 <= samples[0].4 * 3 + 128,
        "write merge/query rebuilt other payloads: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn late_offset_cell_hits_scale_with_affected_entries() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(853_000 + id)),
        };
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(view(&at(i), 0, 4));
        }
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let ((facts, update_work), update_map_work) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    let facts = empty.assume_condition(
                        ConditionTerm::pointer_offset_equal(at(0).offset, at(size).offset),
                        true,
                    );
                    resources.synchronize_memory_equalities(&facts);
                    facts
                })
            });
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    resources
                        .concrete_read_entries(&at(size), 4, &facts)
                        .unwrap()
                        .exact()
                );
                assert!(resources.permits_memory_read(&at(size), 4, &facts));
            })
        });
        samples.push((size, update_work, update_map_work, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "merge scanned unrelated cells: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "merge scanned unrelated map: {samples:?}"
    );
    assert!(
        samples[3].3 <= samples[0].3 * 2 + 32,
        "query scanned unrelated cells: {samples:?}"
    );
    assert!(
        samples[3].4 <= samples[0].4 * 3 + 128,
        "query scanned unrelated map: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 2s in the parallel gate"]
fn cell_publication_and_forks_do_not_repeat_input_registration() {
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(854_000 + id)),
        };
        let mut resources = ResourceContext::new();
        let mut facts = PureFactContext::new();
        resources.synchronize_memory_equalities(&facts);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..size {
                    resources = resources.unchecked_with_fact(view(&at(i), 0, 4));
                    resources.synchronize_memory_equalities(&facts);
                    facts = facts.assume_condition(
                        ConditionTerm::pointer_offset_equal(at(i).offset, at(size + i).offset),
                        true,
                    );
                    resources.synchronize_memory_equalities(&facts);
                    assert!(resources.permits_memory_read(&at(size + i), 4, &facts));
                }
                for i in 0..size {
                    let branch_resources = resources.clone();
                    let branch_facts = facts.clone().assume_condition(
                        ConditionTerm::pointer_offset_equal(at(0).offset, at(3 * size + i).offset),
                        true,
                    );
                    branch_resources.synchronize_memory_equalities(&branch_facts);
                    assert!(
                        branch_resources
                            .concrete_read_entries(&at(3 * size + i), 4, &branch_facts)
                            .unwrap()
                            .exact()
                    );
                    assert!(branch_resources.permits_memory_read(
                        &at(3 * size + i),
                        4,
                        &branch_facts
                    ));
                }
            })
        });
        let logarithm = size.ilog2() as usize + 1;
        assert!(work <= 800 * size as usize, "size={size}, work={work}");
        assert!(
            map_work <= 4096 * size as usize * logarithm,
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn scratch_queries_do_not_force_input_registration_at_the_next_boundary() {
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let at = |id| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(856_000 + id)),
        };
        let facts = PureFactContext::new();
        let mut resources = ResourceContext::new();
        for i in 0..size {
            resources = resources.unchecked_with_fact(view(&at(i), 0, 4));
        }
        resources.synchronize_memory_equalities(&facts);
        let scratch = facts.clone();
        assert!(
            resources
                .concrete_read_entries(&at(size), 4, &scratch)
                .is_none()
        );
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                resources.synchronize_memory_equalities(&facts)
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "scratch query discarded the input checkpoint: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "scratch query reattached unrelated input: {samples:?}"
    );
}

#[test]
fn cell_footprint_merges_and_queries_do_not_scan_other_sizes() {
    let mut samples = Vec::new();
    for size in [8u32, 32, 128, 512] {
        let at = |id: u64| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(859_000 + id)),
        };
        let (owner, alias) = (at(0), at(1));
        let mut resources = ResourceContext::new().unchecked_with_fact(view(&owner, 0, 4));
        for i in 0..size {
            resources = resources.unchecked_with_fact(view(&alias, 0, 8 + i * 4));
        }
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let facts = empty.assume_condition(
                    ConditionTerm::pointer_offset_equal(owner.offset, alias.offset.clone()),
                    true,
                );
                resources.synchronize_memory_equalities(&facts);
                let candidates = resources.concrete_read_entries(&alias, 4, &facts).unwrap();
                assert!(candidates.exact());
                assert_eq!(candidates.count(), 1);
                assert!(resources.permits_memory_read(&alias, 4, &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    eprintln!("selected footprint work: {samples:?}");
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "merge/query scanned other footprints: {samples:?}"
    );
    assert!(
        samples.windows(2).all(|pair| pair[1].2 <= pair[0].2 + 64),
        "merge/query rebuilt the larger footprint payload: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn interval_selection_is_indexed_beside_same_class_non_suppliers() {
    let base = Pointer::symbolic(Variable(895_030));
    let alias = Pointer::symbolic(Variable(895_031));
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(895_032)),
                MachineTerm::Variable(Variable(895_033)),
            ),
            true,
        )
        .assume_condition(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        );
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let mut resources =
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(view(&base, 0, 32));
        for i in 0..size {
            resources = resources.unchecked_with_fact(view(&base, 1024 + i * 32, 1040 + i * 32));
        }
        let query = alias.offset_by_bytes(8);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let mut entries = resources.concrete_read_entries(&query, 4, &facts).unwrap();
                let entry = entries.next().expect("one supplier");
                assert_eq!(entries.address(entry), Some(base.offset_by_bytes(8)));
                assert!(entries.next().is_none());
                assert!(resources.permits_memory_read(&query, 4, &facts));
                assert!(!resources.permits_memory_read(&alias.offset_by_bytes(64), 4, &facts));
            })
        });
        samples.push((work, map_work));
    }
    assert!(
        samples[3].0 <= samples[0].0 * 2 + 64,
        "same-class supplier scan: {samples:?}"
    );
    assert!(
        samples[3].1 <= samples[0].1 * 4 + 512,
        "same-class payload scan: {samples:?}"
    );
}

#[test]
fn write_permission_does_not_enumerate_covering_views() {
    let base = Pointer::symbolic(Variable(960_200));
    let facts = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [4u32, 16, 64, 256] {
        let mut resources = ResourceContext::new_with_equalities(&facts);
        for i in 0..size {
            resources = resources.unchecked_with_fact(view(&base, 0, 8 + i));
        }
        resources = resources.unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(base.clone(), 0u32.into(), 4u32.into(), 1),
        ));
        resources.synchronize_memory_equalities(&facts);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    resources
                        .memory_write_range(&base.offset_by_bytes(1), 1, &facts)
                        .is_some()
                );
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples
            .iter()
            .all(|(_, work, _)| *work <= samples[0].1 * 2 + 32),
        "write candidate selection enumerated read authority: {samples:?}"
    );
    assert!(
        samples
            .iter()
            .all(|(_, _, work)| *work <= samples[0].2 * 3 + 128),
        "write candidate selection visited covering views: {samples:?}"
    );
    {
        let costs = samples.iter().map(|x| x.1).collect::<Vec<_>>();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 64);
        assert!(indexed(&costs), "indexed work: {costs:?}");
        let scanned = costs
            .iter()
            .zip([4u32, 16, 64, 256])
            .map(|(work, size)| work + usize::try_from(size).unwrap())
            .collect::<Vec<_>>();
        assert!(
            !indexed(&scanned),
            "the smaller fixture must detect a visit per unrelated item: {costs:?}"
        );
    }
    {
        // The first query also registers the selected pointer. Keep its
        // original bound, and calibrate indexed lookup on the three warm sizes.
        let costs = samples[1..].iter().map(|x| x.2).collect::<Vec<_>>();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 128);
        assert!(indexed(&costs), "indexed work: {costs:?}");
        let scanned = costs
            .iter()
            .zip([16u32, 64, 256])
            .map(|(work, size)| work + usize::try_from(size).unwrap())
            .collect::<Vec<_>>();
        assert!(
            !indexed(&scanned),
            "the smaller fixture must detect a visit per unrelated item: {costs:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn symbolic_write_permission_does_not_search_views() {
    let base = Pointer::symbolic(Variable(961_000));
    let alias = Pointer::symbolic(Variable(961_001));
    let i = MachineTerm::Variable(Variable(961_002));
    let n = MachineTerm::Variable(Variable(961_003));
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(1u32.into(), i.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i.clone(), n.clone()), true);
    let query = base.offset_by_elements(i, 1);
    let owned = MemoryRange::new_with_element_width(base.clone(), 1u32.into(), n.clone(), 1);
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let mut resources = ResourceContext::new_with_equalities(&facts);
        for k in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::view_memory(
                MemoryRange::new_with_element_width(base.clone(), k.into(), n.clone(), 1),
            ));
        }
        resources = resources.unchecked_with_fact(ResourceFact::own_memory(owned.clone()));
        resources.synchronize_memory_equalities(&facts);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(
                    resources.memory_write_range(&query, 1, &facts),
                    Some(&owned)
                );
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples
            .iter()
            .all(|(_, work, _)| *work <= samples[0].1 * 2 + 64),
        "symbolic write searched view suppliers: {samples:?}"
    );
    assert!(
        samples
            .iter()
            .all(|(_, _, work)| *work <= samples[0].2 * 4 + 512),
        "symbolic write visited an ambient index: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn symbolic_partition_read_start_is_indexed_without_searching_other_ranges() {
    let base = Pointer::symbolic(Variable(899_000));
    let i = MachineTerm::Variable(Variable(899_001));
    let split = MachineTerm::Variable(Variable(899_002));
    let end = MachineTerm::Variable(Variable(899_003));
    let empty = PureFactContext::new();
    let facts = empty
        .clone()
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), i.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(i.clone(), split.clone()),
            true,
        );
    let query = base.offset_by_elements(i, 1);
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let mut resources = ResourceContext::new_with_equalities(&empty)
            .unchecked_with_fact(ResourceFact::view_memory(
                MemoryRange::new_with_element_width(base.clone(), 0u32.into(), split.clone(), 1),
            ))
            .unchecked_with_fact(ResourceFact::view_memory(
                MemoryRange::new_with_element_width(base.clone(), split.clone(), end.clone(), 1),
            ));
        for k in 1..=size {
            resources = resources.unchecked_with_fact(ResourceFact::view_memory(
                MemoryRange::new_with_element_width(base.clone(), k.into(), end.clone(), 1),
            ));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(resources.permits_memory_read(&query, 1, &facts));
            })
        });
        assert!(!resources.permits_memory_read(&query, 1, &empty));
        assert!(resources.memory_write_range(&query, 1, &facts).is_none());
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 64,
        "read searched partitions: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "read traversed unrelated payloads: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn indexed_memory_support_and_fragment_consumption_ignore_unrelated_spans() {
    let p = Pointer::symbolic(Variable(975_000));
    let q = Pointer::symbolic(Variable(975_001));
    let empty = PureFactContext::new();
    let facts = empty
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true);
    let own = |base: &Pointer, start: u32, end: u32| {
        ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base.clone(),
            start.into(),
            end.into(),
            1,
        ))
    };
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let left = own(&p, 4u32, 10u32);
        let right = own(&p, 10u32, 16u32);
        let mut resources = ResourceContext::new_with_equalities(&empty)
            .unchecked_with_fact(left.clone())
            .unchecked_with_fact(right);
        for i in 0..size {
            resources = resources.unchecked_with_fact(own(&p, 32 + i * 4, 34 + i * 4));
        }
        resources.synchronize_memory_equalities(&facts);
        let whole = own(&q, 6u32, 14u32);
        let piece = view(&q, 6, 8);
        let occurrence = resources.occurrences_for_fact(&left)[0];
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(
                    resources.directly_supporting_fact(&piece, &facts),
                    Some(&left)
                );
                assert_eq!(
                    resources.directly_supporting_owned_entry(&piece, &facts),
                    Some((occurrence, &left))
                );
                assert!(resources.satisfies_fact(&whole, &facts));
                assert!(
                    resources
                        .directly_supporting_owned_entry(&whole, &facts)
                        .is_none()
                );
                let consumed = resources
                    .clone()
                    .without_fact_incrementally(&whole, &facts)
                    .unwrap();
                assert!(consumed.satisfies_fact(&own(&q, 4u32, 6u32), &facts));
                assert!(consumed.satisfies_fact(&own(&q, 14u32, 16u32), &facts));
                assert!(!consumed.satisfies_fact(&whole, &facts));
                assert!(resources.satisfies_fact(&whole, &facts));
                assert!(!resources.satisfies_fact(&own(&q, 16u32, 20u32), &facts));
            })
        });
        samples.push((size, work, map_work));
        assert!(!resources.satisfies_fact(&whole, &empty));
        let gapped = resources
            .clone()
            .without_exact_representation(&left)
            .unwrap()
            .unchecked_with_fact(own(&p, 4u32, 7u32));
        assert!(!gapped.satisfies_fact(&whole, &facts));
        assert!(gapped.without_fact_incrementally(&whole, &facts).is_none());
        let views =
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(view(&p, 4, 16));
        assert!(!views.satisfies_fact(&whole, &facts));
        assert!(views.without_fact_incrementally(&whole, &facts).is_none());
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 128,
        "memory support searched unrelated spans: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 4 + 512,
        "memory support rebuilt unrelated input: {samples:?}"
    );
}

#[test]
fn explicit_memory_fragment_composition_scales_with_selected_input() {
    let base = Pointer::symbolic(Variable(977_000));
    let facts = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [4u32, 16, 64, 256] {
        let mut resources = ResourceContext::new_with_equalities(&facts);
        for i in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(base.clone(), i.into(), (i + 1).into(), 1),
            ));
        }
        let required = ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base.clone(),
            0u32.into(),
            size.into(),
            1,
        ));
        let ((consumed, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                resources
                    .without_fact_incrementally(&required, &facts)
                    .unwrap()
            })
        });
        assert!(consumed.is_empty());
        samples.push((size as usize, work, map_work));
    }
    let (base_size, base_work, base_map) = samples[0];
    for (size, work, map_work) in &samples {
        let scale = (size * (size.ilog2() as usize + 1))
            .div_ceil(base_size * (base_size.ilog2() as usize + 1));
        assert!(
            *work <= base_work * scale * 2 + 128,
            "fragment composition exceeded selected input: {samples:?}"
        );
        assert!(
            *map_work <= base_map * scale * 2 + 512,
            "fragment composition rebuilt ambient input: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 2.1s in the parallel gate"]
fn direct_memory_support_does_not_enumerate_overlapping_views() {
    let p = Pointer::symbolic(Variable(976_000));
    let q = Pointer::symbolic(Variable(976_001));
    let facts = PureFactContext::new()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true);
    for late_owner in [false, true] {
        for bytes in [4u32, 4096] {
            let owner = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                p.clone(),
                0u32.into(),
                bytes.into(),
                1,
            ));
            let mut samples = Vec::new();
            for size in [16u32, 64, 256, 1024] {
                let mut resources = ResourceContext::new_with_equalities(&facts);
                if !late_owner {
                    resources = resources.unchecked_with_fact(owner.clone());
                }
                for i in 0..size {
                    resources = resources.unchecked_with_fact(view(&p, 0, 8 + i));
                }
                if late_owner {
                    resources = resources.unchecked_with_fact(owner.clone());
                }
                let required = view(&q, 0, bytes);
                let ((), work) = crate::persistent::measure_persistent_work(|| {
                    let support = resources
                        .directly_supporting_fact(&required, &facts)
                        .unwrap();
                    assert!(!resources.occurrences_for_fact(support).is_empty());
                    assert!(resources.satisfies_fact(&required, &facts));
                });
                samples.push(work);
            }
            assert!(
                samples.iter().all(|work| *work <= samples[0] * 3 + 128),
                "direct {bytes}-byte support (late owner: {late_owner}) enumerated overlapping views: {samples:?}"
            );
        }
    }
}

#[test]
#[ignore = "nightly: 1.5s in the parallel gate"]
fn symbolic_fragment_support_follows_indexed_endpoint_successors() {
    let p = Pointer::symbolic(Variable(977_000));
    let i = MachineTerm::Variable(Variable(977_001));
    let n = MachineTerm::Variable(Variable(977_002));
    let middle = MachineTerm::Variable(Variable(977_003));
    let next = MachineTerm::add(i.clone(), 1u32.into());
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(n.clone()),
                right: Box::new(4u32.into()),
            },
            true,
        )
        .assume_condition(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::Equal,
                left: Box::new(i.clone()),
                right: Box::new(middle.clone()),
            },
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(i.clone(), 0u32.into()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i.clone(), n.clone()), true);
    let own = |start, end| ResourceFact::own_memory(MemoryRange::new(p.clone(), start, end));
    let required = own(0u32.into(), n.clone());
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let mut resources = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_fact(own(0u32.into(), i.clone()))
            .unchecked_with_fact(own(next.clone(), n.clone()))
            .unchecked_with_fact(own(middle.clone(), next.clone()))
            .unchecked_with_fact(ResourceFact::view_memory(MemoryRange::new(
                p.clone(),
                middle.clone(),
                next.clone(),
            )));
        for k in 0..size {
            resources =
                resources.unchecked_with_fact(own((100 + 4 * k).into(), (102 + 4 * k).into()));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(resources.satisfies_fact(&required, &facts));
                assert!(resources.satisfies_fact(&own(0u32.into(), 4u32.into()), &facts));
                assert!(
                    resources
                        .clone()
                        .without_fact_incrementally(&required, &facts)
                        .is_some()
                );
            })
        });
        samples.push((work, map_work));
        // A missing middle fragment cannot be bridged by unrelated same-base holdings.
        let gap = resources
            .clone()
            .without_fact_incrementally(&own(i.clone(), next.clone()), &facts)
            .unwrap();
        assert!(!gap.satisfies_fact(&required, &facts));
    }
    for (work, map_work) in &samples {
        assert!(
            *work <= samples[0].0 * 2 + 128,
            "symbolic fragment checker scanned ambient spans: {samples:?}"
        );
        assert!(
            *map_work <= samples[0].1 * 4 + 512,
            "symbolic endpoint traversal scanned ambient spans: {samples:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn ordered_symbolic_subrange_selects_its_retained_residual_without_scanning() {
    let p = Pointer::symbolic(Variable(978_000));
    let i = MachineTerm::Variable(Variable(978_001));
    let j = MachineTerm::Variable(Variable(978_002));
    let n = MachineTerm::Variable(Variable(978_003));
    let next_i = MachineTerm::add(i.clone(), 1u32.into());
    let next_j = MachineTerm::add(j.clone(), 1u32.into());
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(i.clone(), 0u32.into()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), 0u32.into()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i.clone(), j.clone()), true)
        .assume_condition(ConditionTerm::signed_less_than(j.clone(), n.clone()), true);
    let own = |start, end| ResourceFact::own_memory(MemoryRange::new(p.clone(), start, end));
    let tail = own(next_i, n);
    let required = own(j.clone(), next_j);
    let shifted = ResourceFact::own_memory(MemoryRange::new(
        p.offset_by_int32_elements(j),
        0u32.into(),
        1u32.into(),
    ));
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let mut resources = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_fact(own(0u32.into(), i.clone()))
            .unchecked_with_fact(tail.clone());
        for k in 0..size {
            resources =
                resources.unchecked_with_fact(own((100 + 4 * k).into(), (102 + 4 * k).into()));
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for required in [&required, &shifted] {
                    assert_eq!(
                        resources.directly_supporting_fact(required, &facts),
                        Some(&tail)
                    );
                    assert_eq!(
                        resources
                            .directly_supporting_owned_entry(required, &facts)
                            .unwrap()
                            .1,
                        &tail
                    );
                    assert!(resources.satisfies_fact(required, &facts));
                    assert!(
                        resources
                            .clone()
                            .without_fact_incrementally(required, &facts)
                            .is_some()
                    );
                }
            })
        });
        samples.push((work, map_work));
    }
    for (work, map_work) in &samples {
        assert!(
            *work <= samples[0].0 * 2 + 128,
            "ordered residual selection scanned ambient spans: {samples:?}"
        );
        assert!(
            *map_work <= samples[0].1 * 4 + 512,
            "ordered residual index scanned ambient spans: {samples:?}"
        );
    }
}

#[test]
fn constant_memory_miss_ignores_unrelated_zero_bound_neighbors() {
    let p = Pointer::symbolic(Variable(980_000));
    let required = view(&p, 0, 1);
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let mut facts = PureFactContext::new();
        for k in 0..size {
            facts = facts.assume_condition(
                ConditionTerm::signed_greater_equal(
                    MachineTerm::Variable(Variable(980_001 + u64::from(k))),
                    0u32.into(),
                ),
                true,
            );
        }
        let resources =
            ResourceContext::new_with_equalities(&facts).unchecked_with_fact(view(&p, 10, 20));
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(
                    resources
                        .directly_supporting_fact(&required, &facts)
                        .is_none()
                );
                assert!(!resources.satisfies_fact(&required, &facts));
            })
        });
        samples.push((work, map_work));
    }
    for (work, map_work) in &samples {
        assert!(
            *work <= samples[0].0 * 2 + 128,
            "constant miss searched unrelated bounds: {samples:?}"
        );
        assert!(
            *map_work <= samples[0].1 * 3 + 128,
            "constant miss visited unrelated bounds: {samples:?}"
        );
    }
}

#[test]
fn composition_object_evidence_ignores_unrelated_admitted_sources() {
    let external = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(899_000 + id)),
    };
    let target = external(0);
    let target_fact = view(&target, 0, 4);
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut facts = PureFactContext::new();
        for id in 1..=size {
            facts = facts.assume_proposition(Proposition::ResourceComposition(
                ResourceContext::new().unchecked_with_fact(view(&external(id), 0, 4)),
            ));
        }
        let sibling = facts.clone();
        facts = facts.assume_proposition(Proposition::ResourceComposition(
            ResourceContext::new().unchecked_with_fact(target_fact.clone()),
        ));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                facts
                    .composition_object_resources
                    .memory_object_evidence(&target, &facts),
                Some(&target_fact)
            );
            assert!(
                sibling
                    .composition_object_resources
                    .memory_object_evidence(&target, &sibling)
                    .is_none()
            );
        });
        samples.push(work);
    }
    assert!(
        samples[3] <= samples[0] + 40,
        "composition lookup searched unrelated sources: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.5s in the parallel gate"]
fn composition_provenance_admission_follows_sibling_deltas_not_the_shared_frame() {
    let pointer = |id: u64| Pointer::symbolic(Variable(901_000 + id));
    let dormant = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        pointer(0),
        0u32.into(),
        4u32.into(),
        1,
    ));
    let left_fact = view(&pointer(1), 0, 4);
    let right_fact = view(&pointer(2), 0, 4);
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let empty = PureFactContext::new();
        let mut common =
            ResourceContext::new_with_equalities(&empty).unchecked_with_fact(dormant.clone());
        for id in 3..size + 3 {
            common = common.unchecked_with_fact(view(&pointer(id), 0, 4));
        }
        // Independently consumed histories have a common prefix that still
        // contains dormant. Neither admitted source actually contains it.
        let left = common
            .clone()
            .without_fact_incrementally(&dormant, &empty)
            .unwrap()
            .unchecked_with_fact(left_fact.clone());
        let right = common
            .clone()
            .without_fact_incrementally(&dormant, &empty)
            .unwrap()
            .unchecked_with_fact(right_fact.clone());
        let parent = empty
            .clone()
            .assume_proposition(Proposition::ResourceComposition(left));
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            parent
                .clone()
                .assume_proposition(Proposition::ResourceComposition(right))
        });
        assert_eq!(
            facts
                .composition_object_resources
                .memory_object_evidence(&pointer(2), &facts),
            Some(&right_fact)
        );
        assert!(
            facts
                .composition_object_resources
                .memory_object_evidence(&pointer(0), &facts)
                .is_none()
        );
        assert!(
            parent
                .composition_object_resources
                .memory_object_evidence(&pointer(2), &parent)
                .is_none()
        );
        let (returned, returning_work) = crate::instrumentation::measure_deterministic_work(|| {
            facts.assume_proposition(Proposition::ResourceComposition(common))
        });
        assert_eq!(
            returned
                .composition_object_resources
                .memory_object_evidence(&pointer(0), &returned),
            Some(&dormant)
        );
        samples.push(work + returning_work);
    }
    assert!(
        samples[3] <= samples[0] + 40,
        "source admission visited the shared frame: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn captured_interior_pointer_reads_keep_owned_bounds_and_opaque_base_identity() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = Memory::new();
    let empty = PureFactContext::new();
    let read = |id| {
        let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
            &memory,
            Pointer::symbolic(Variable(id)),
            ProgramType::Int32Pointer,
            Vec::new().into(),
            Vec::new(),
            &empty,
        );
        let ExpressionOutcome::Value(ProgramValue::Pointer(value)) = &paths[0].outcome else {
            panic!("pointer read")
        };
        value.pointer().clone()
    };
    let base = read(972_100);
    let unrelated = read(972_101);
    let captured = Pointer::symbolic(Variable(972_102));
    let i = MachineTerm::Variable(Variable(972_103));
    let n = MachineTerm::Variable(Variable(972_104));
    let bounds = empty
        .clone()
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), i.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i.clone(), n.clone()), true);
    let relation =
        ConditionTerm::pointer_equal(captured.clone(), base.offset_by_elements(i.clone(), 4));
    let facts = bounds.clone().assume_condition(relation.clone(), true);
    let range = MemoryRange::new(base.clone(), 0u32.into(), n.clone());
    let owner = ResourceFact::own_memory(range.clone());
    let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(owner.clone());
    resources.synchronize_memory_equalities(&empty);
    assert_eq!(
        resources.memory_write_range(&captured, 4, &facts),
        Some(&range)
    );
    assert!(
        resources
            .memory_write_range(&captured, 4, &bounds)
            .is_none()
    );
    assert!(
        resources
            .memory_write_range(
                &captured,
                4,
                &empty.clone().assume_condition(relation.clone(), true)
            )
            .is_none()
    );
    assert!(
        resources
            .memory_write_range(&unrelated, 4, &facts)
            .is_none()
    );
    // A separate, noncontradictory context says only that the capture is at n.
    let end_only = bounds.clone().assume_condition(
        ConditionTerm::pointer_equal(captured.clone(), base.offset_by_elements(n, 4)),
        true,
    );
    assert!(
        resources
            .memory_write_range(&captured, 4, &end_only)
            .is_none()
    );
    let views = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_fact(ResourceFact::view_memory(range));
    views.synchronize_memory_equalities(&facts);
    assert!(views.memory_write_range(&captured, 4, &facts).is_none());
    let mut samples = Vec::new();
    for size in [0u64, 32, 128, 512] {
        let mut context = facts.clone();
        let mut frame = resources.clone();
        for k in 0..size {
            let p = Pointer::symbolic(Variable(980_000 + k * 2));
            let q = Pointer::symbolic(Variable(980_001 + k * 2));
            context = context.assume_condition(ConditionTerm::pointer_equal(p.clone(), q), true);
            frame = frame.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                p,
                0u32.into(),
                1u32.into(),
            )));
        }
        frame.synchronize_memory_equalities(&context);
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                assert!(frame.memory_write_range(&captured, 4, &context).is_some());
            }
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 4 + 512),
        "captured address queried unrelated state: {samples:?}"
    );
}

// A modular reference result must retain its checked base even beside other
// owners in the same external address space. Equality selects that occurrence;
// the existing owner, width and signed bounds still authorize the access.
#[test]
#[ignore = "nightly: 0.9s in the parallel gate"]
fn captured_interior_address_selects_its_base_beside_same_block_owners() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(973_100)),
    };
    let captured = Pointer::symbolic(Variable(973_101));
    let i = MachineTerm::Variable(Variable(973_102));
    let n = MachineTerm::Variable(Variable(973_103));
    let empty = PureFactContext::new();
    let facts = empty
        .clone()
        .assume_condition(
            ConditionTerm::pointer_equal(captured.clone(), base.offset_by_elements(i.clone(), 4)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), i.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i, n.clone()), true);
    let range = MemoryRange::new(base, 0u32.into(), n);
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut frame = ResourceContext::new_with_equalities(&empty)
            .unchecked_with_fact(ResourceFact::own_memory(range.clone()));
        for k in 0..size {
            let field = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(974_000 + k)),
            };
            frame = frame.unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(field, 0u32.into(), 1u32.into(), 8),
            ));
        }
        frame.synchronize_memory_equalities(&facts);
        let sibling = frame.clone();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..16 {
                assert_eq!(frame.memory_write_range(&captured, 4, &facts), Some(&range));
                assert!(frame.permits_memory_read(&captured, 4, &facts));
            }
        });
        assert!(sibling.memory_write_range(&captured, 4, &empty).is_none());
        samples.push(work);
    }
    assert!(
        samples[3] <= samples[0] * 4 + 512,
        "captured base lookup scanned unrelated owners: {samples:?}"
    );
}

#[test]
fn a_cold_small_memory_index_skips_unrelated_pointer_merge_history() {
    let mut samples = Vec::new();
    for size in [4u64, 32, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut graph = EqualityGraph::default();
        let unrelated = Pointer::symbolic(Variable(870_000));
        for id in 1..=size {
            graph.add_equality(&unrelated, &Pointer::symbolic(Variable(870_000 + id)));
        }
        let kept = Pointer {
            block: "local:cold-contract".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let resources = ResourceContext::new().unchecked_with_fact(view(&kept, 0, 4));
        let (index, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.pair_memory_equalities_in_graph(
                graph,
                false,
                Some(MemoryQuery::Address(&kept)),
            )
        });
        assert!(
            !index.points_initialized,
            "a raw lookup must not publish read authority"
        );
        assert!(index.addresses.classes.contains_key(&kept.block));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn framed_pointer_fragments_rejoin_through_their_checked_read_endpoint() {
    let mut work_samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let read = |context: &PureFactContext, memory: &Memory| {
            let retained_state = crate::kernel::intern_memory_ref(memory);
            let variable = crate::kernel::load_variable_for_cell_with_origin(
                &retained_state,
                &field,
                LoadKind::of_type(ProgramType::Int32Pointer).unwrap(),
                C_POINTER_BYTE_WIDTH,
                &retained_state,
            );
            let pointer = Pointer::loaded(&MachineTerm::Variable(variable)).unwrap();
            context.register_pointer_read(&pointer, &retained_state, &field);
            PointerValue::from_read(pointer, ProgramType::Int32Pointer, &retained_state, &field)
        };
        let source = read(&PureFactContext::new(), &Memory::new());
        let before = Memory::new().store(field.clone(), ProgramValue::Pointer(source.clone()));
        let range = |base: PointerValue, start: u32, end: u32| {
            MemoryRange::from_pointer_value(&base, start.into(), end.into(), 4)
        };
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(range(
                PointerValue::new(field.clone(), ProgramType::Int32Pointer),
                0,
                2,
            ))),
            right: Box::new(Resource::Memory(range(source.clone(), 0, 8))),
        };
        let context = PureFactContext::new().assume_proposition(separation.clone());
        let after = before.clone().with_call_memory_havoc(
            Variable(9_910_001),
            &[range(source.clone(), 0, 1)],
            &context,
            None,
        );
        let current = read(&context, &after);
        assert_eq!(
            crate::kernel::memory_provenance::checked_pointer_read_endpoint(
                current.pointer(),
                &context
            ),
            Some(source.pointer().clone())
        );
        let tail = ResourceFact::own_memory(range(source.clone(), 1, 8));
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(tail.clone())
            .unchecked_with_fact(ResourceFact::own_memory(range(current.clone(), 0, 1)));
        for index in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(range(
                PointerValue::new(
                    Pointer::symbolic(Variable(9_911_000 + index)),
                    ProgramType::Int32Pointer,
                ),
                0,
                8,
            )));
        }
        resources.synchronize_memory_equalities(&context);
        let required = ResourceFact::own_memory(range(current.clone(), 0, 8));
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources
                .clone()
                .without_fact_incrementally(&required, &context)
        });
        let remaining = remaining.expect("selected framed prefix and tail must rejoin");
        assert_eq!(remaining.iter().count(), size as usize);
        work_samples.push(work);
        assert!(
            !context
                .equality_graph
                .are_equal(source.pointer(), current.pointer())
        );
        let unseparated = PureFactContext::new();
        assert!(
            resources
                .clone()
                .without_fact_incrementally(&required, &unseparated)
                .is_none()
        );
        let withdrawn = resources
            .clone()
            .without_exact_representation(&tail)
            .unwrap();
        assert!(
            withdrawn
                .without_fact_incrementally(&required, &context)
                .is_none()
        );
        let partial = after.store(field.offset_by_bytes(4), ProgramValue::Int32(9u32.into()));
        let changed = ResourceFact::own_memory(range(read(&context, &partial), 0, 8));
        assert!(
            resources
                .without_fact_incrementally(&changed, &context)
                .is_none()
        );
    }
    assert!(
        work_samples
            .iter()
            .all(|work| *work <= work_samples[0] + 128),
        "unrelated owners changed selected two-fragment work: {work_samples:?}"
    );
    {
        let costs = work_samples.clone();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 128);
        assert!(indexed(&costs), "indexed work: {costs:?}");
        let scanned = costs
            .iter()
            .zip([4u64, 16, 64, 256])
            .map(|(work, size)| work + usize::try_from(size).unwrap())
            .collect::<Vec<_>>();
        assert!(
            !indexed(&scanned),
            "the smaller fixture must detect a visit per unrelated item: {costs:?}"
        );
    }
}

#[test]
fn framed_pointer_read_selects_interior_writes_under_live_authority() {
    let mut work_samples = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let read = |context: &PureFactContext, memory: &Memory| {
            let retained_state = crate::kernel::intern_memory_ref(memory);
            let variable = crate::kernel::load_variable_for_cell_with_origin(
                &retained_state,
                &field,
                LoadKind::of_type(ProgramType::Int32Pointer).unwrap(),
                C_POINTER_BYTE_WIDTH,
                &retained_state,
            );
            let pointer = Pointer::loaded(&MachineTerm::Variable(variable)).unwrap();
            context.register_pointer_read(&pointer, &retained_state, &field);
            pointer
        };
        let source = read(&PureFactContext::new(), &Memory::new());
        let before = Memory::new().store(
            field.clone(),
            ProgramValue::Pointer(PointerValue::new(source.clone(), ProgramType::Int32Pointer)),
        );
        let range = |base: Pointer, start: u32, end: u32| {
            MemoryRange::new_with_element_width(base, start.into(), end.into(), 4)
        };
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(range(field.clone(), 0, 2))),
            right: Box::new(Resource::Memory(range(source.clone(), 0, 8))),
        };
        let context = PureFactContext::new().assume_proposition(separation.clone());
        let after = before.clone().with_call_memory_havoc(
            Variable(9_910_001),
            &[range(source.clone(), 0, 1)],
            &context,
            None,
        );
        let current = read(&context, &after);
        assert_eq!(
            crate::kernel::memory_provenance::checked_pointer_read_endpoint(&current, &context),
            Some(source.clone())
        );
        let owner = ResourceFact::own_memory(range(source.clone(), 0, 8));
        let mut resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        for index in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(range(
                Pointer::symbolic(Variable(9_911_000 + index)),
                0,
                8,
            )));
        }
        resources.synchronize_memory_equalities(&context);
        let target = current.offset_by_bytes(4);
        let (selected, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.memory_write_range(&target, 4, &context).is_some()
        });
        assert!(
            selected,
            "a checked framed pointer must select its interior owner"
        );
        work_samples.push(work);
        assert!(!context.equality_graph.are_equal(&source, &current));
        let unseparated = PureFactContext::new();
        assert!(
            resources
                .memory_write_range(&target, 4, &unseparated)
                .is_none()
        );
        let withdrawn = resources
            .clone()
            .without_exact_representation(&owner)
            .unwrap();
        assert!(withdrawn.memory_write_range(&target, 4, &context).is_none());
        assert!(
            resources
                .memory_write_range(&current.offset_by_bytes(32), 4, &context)
                .is_none()
        );
        let partial = after.store(field.offset_by_bytes(4), ProgramValue::Int32(9u32.into()));
        let changed = read(&context, &partial).offset_by_bytes(4);
        assert!(
            resources
                .memory_write_range(&changed, 4, &context)
                .is_none()
        );
    }
    assert!(
        work_samples
            .iter()
            .all(|work| *work <= work_samples[0] + 128),
        "unrelated owners changed selected interior-write work: {work_samples:?}"
    );
}

#[test]
fn cold_read_queries_ignore_unrelated_classes_and_resource_ranges() {
    let pointer = |id| Pointer::symbolic(Variable(id));
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut context = PureFactContext::new();
        let mut resources = ResourceContext::new();
        for index in 0..size {
            let a = pointer(990_000 + index * 2);
            let b = pointer(990_001 + index * 2);
            context = context.assume_condition(ConditionTerm::pointer_equal(a, b.clone()), true);
            resources = resources.unchecked_with_fact(ResourceFact::view_memory(MemoryRange::new(
                b,
                0u32.into(),
                1u32.into(),
            )));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(resources.permits_memory_read(&pointer(990_000), 4, &context));
            // The first query's disposable class view cannot hide another
            // class's alias when the next query shares its graph input key.
            assert!(resources.permits_memory_read(&pointer(990_002), 4, &context));
        });
        samples.push(work);
    }
    assert!(
        samples.iter().max().unwrap() - samples.iter().min().unwrap() < 64,
        "{samples:?}"
    );
}

#[test]
fn an_indexed_read_supplier_does_not_resolve_its_pointer_history() {
    let mut samples = Vec::new();
    for size in [4u64, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let stored = Pointer::symbolic(Variable(9_930_000));
        let mut memory = Memory::new().store(
            field.clone(),
            ProgramValue::typed_pointer(stored, ProgramType::Int32Pointer),
        );
        for i in 0..size {
            memory = memory.store(
                Pointer {
                    block: PointerBlock::Heap(i),
                    offset: PointerOffsetTerm::Constant(0),
                },
                ProgramValue::Int32(1u32.into()),
            );
        }
        let retained_state = crate::kernel::intern_memory_ref(&memory);
        let variable = crate::kernel::load_variable_for_cell_with_origin(
            &retained_state,
            &field,
            LoadKind::of_type(ProgramType::Int32Pointer).unwrap(),
            C_POINTER_BYTE_WIDTH,
            &retained_state,
        );
        let pointer = Pointer::loaded(&MachineTerm::Variable(variable)).unwrap();
        let context = PureFactContext::new();
        context.register_pointer_read(&pointer, &retained_state, &field);
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(pointer.clone(), 0u32.into(), 8u32.into(), 1),
        ));
        resources.synchronize_memory_equalities(&context);
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.read_access(&pointer, 4, &context).is_some()
        });
        assert!(found);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "an existing supplier walked pointer history: {samples:?}"
    );
}

fn opening_checkpoint_work(steps: u64, unrelated: u64) -> usize {
    let at = |id| Pointer::symbolic(Variable(987_000 + id));
    let mut base = PureFactContext::new();
    for i in 0..unrelated {
        base = base.assume_condition(
            ConditionTerm::pointer_equal(at(1000 + 2 * i), at(1001 + 2 * i)),
            true,
        );
    }
    let owner = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        at(0),
        0u32.into(),
        4u32.into(),
        1,
    ));
    let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
        for step in 0..steps {
            let caller = base.clone();
            let opening = caller.clone();
            opening
                .equality_graph
                .add_checked_read_equality(&at(2 + 2 * step), &at(3 + 2 * step));
            let resources = ResourceContext::new();
            resources.capture_empty_memory_input(&caller);
            // Body evaluation uses a temporary stronger context before it
            // publishes the constructed read equation back to the caller.
            resources.synchronize_memory_equalities(&opening);
            let resources = resources
                .try_compose_into_valid_context_delaying_normalization(
                    [
                        owner.clone(),
                        ResourceFact::own_memory(MemoryRange::new_with_element_width(
                            at(0).offset_by_bytes(8),
                            0u32.into(),
                            4u32.into(),
                            1,
                        )),
                    ],
                    &opening,
                )
                .unwrap();
            caller
                .equality_graph
                .add_checked_read_equality(&at(2 + 2 * step), &at(3 + 2 * step));
            assert!(
                resources
                    .without_fact_incrementally(&owner, &caller)
                    .is_some()
            );
        }
    });
    work
}

#[test]
fn opening_checkpoints_ignore_unrelated_caller_equalities() {
    let samples = [0, 16, 64, 256].map(|unrelated| opening_checkpoint_work(4, unrelated));
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn opening_checkpoints_scale_with_selected_exchanges() {
    let samples = [8, 16, 32, 64].map(|steps| opening_checkpoint_work(steps, 64));
    assert!(samples[0] > 0);
    assert!(
        samples.windows(2).all(|pair| pair[1] <= 2 * pair[0] + 64),
        "{samples:?}"
    );
}

#[test]
fn query_read_definition_merges_scale_with_changed_suppliers() {
    fn work(count: u32, unrelated_count: u32, register_query: bool) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let name = |memory: &SharedMemory, address: &Pointer| {
            crate::kernel::memory_provenance::canonical_value_load_memory(memory, address, 8);
            Pointer::canonical_loaded_value(memory, address)
        };
        let unrelated = Pointer {
            block: PointerBlock::Heap(989_810),
            offset: PointerOffsetTerm::Constant(0),
        };
        let first = crate::kernel::intern_memory(
            Memory::new().store(unrelated.clone(), ProgramValue::UInt32(1u32.into())),
        );
        let later = crate::kernel::intern_memory(
            first
                .memory()
                .clone()
                .store(unrelated, ProgramValue::UInt32(2u32.into())),
        );
        let mut resources = ResourceContext::new();
        let mut pairs = Vec::new();
        for n in 0..count {
            let cell = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(i64::from(n) * 16),
            };
            let named = name(&first, &cell);
            let read = Pointer::loaded_value(&later, &cell);
            let own = |base, start, end| {
                ResourceFact::own_memory(MemoryRange::new_with_element_width(base, start, end, 8))
            };
            let left = own(read.clone(), 0u32.into(), 1u32.into());
            let right = own(named.clone(), 1u32.into(), 2u32.into());
            let extra = own(read.clone(), 2u32.into(), 3u32.into());
            resources = resources
                .unchecked_with_fact(left.clone())
                .unchecked_with_fact(right.clone())
                .unchecked_with_fact(extra.clone());
            pairs.push((cell, named, read, left, right, extra));
        }
        for n in 0..unrelated_count {
            resources = resources.unchecked_with_fact(view(
                &Pointer {
                    block: PointerBlock::Heap(990_000 + u64::from(n)),
                    offset: PointerOffsetTerm::Constant(0),
                },
                0,
                8,
            ));
        }
        let facts = PureFactContext::new();
        resources.synchronize_memory_equalities(&facts);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for (cell, named, read, left, right, extra) in pairs {
                let paired = resources.pair_memory_equalities(&facts, false, None);
                assert_eq!(named, name(&later, &cell));
                if register_query {
                    assert!(paired.graph.are_equal(&named, &read));
                }
                resources = resources
                    .clone()
                    .without_exact_representation(&left)
                    .unwrap();
                resources = resources
                    .clone()
                    .without_exact_representation(&right)
                    .unwrap();
                resources = resources.without_exact_representation(&extra).unwrap();
                assert!(!resources.permits_memory_read(&read, 8, &facts));
            }
        });
        work
    }
    for register_query in [false, true] {
        let chain = [4, 8, 16, 32].map(|count| work(count, 16, register_query));
        assert!(chain[0] > 0);
        assert!(
            chain.windows(2).all(|pair| pair[1] <= pair[0] * 3),
            "{chain:?}"
        );
        let ambient = [0, 16, 64, 256].map(|count| work(4, count, register_query));
        assert!(
            ambient.iter().all(|work| *work <= ambient[0] + 64),
            "{ambient:?}"
        );
    }
}
