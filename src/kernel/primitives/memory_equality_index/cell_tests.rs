use super::*;

fn view(base: &Pointer, start: u32, end: u32) -> CResourceFact {
    CResourceFact::view_memory(CMemoryRange::new_with_element_width(
        base.clone(),
        start.into(),
        end.into(),
        1,
    ))
}

#[test]
fn checked_context_construction_attaches_address_candidates() {
    let at = |id: u64| Pointer::symbolic(Variable(860_000 + id));
    let empty = PureFactContext::new();
    let facts = empty
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(at(0), at(1)), true)
        .assume_condition(ConditionTerm::pointer_equal(at(1), at(2)), true);
    let owner = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        at(0),
        0u32.into(),
        4u32.into(),
        1,
    ));
    for mode in 0..5 {
        let resources = match mode {
            0 => ResourceContext::new().try_compose_with_fact(owner.clone(), &facts),
            1 => ResourceContext::new()
                .try_compose_with_facts_delaying_normalization([owner.clone()], &facts),
            2 => ResourceContext::new()
                .try_compose_into_valid_context_delaying_normalization([owner.clone()], &facts),
            3 => ResourceContext::new()
                .try_compose_certified_group_into_valid_context_delaying_normalization(
                    [owner.clone()],
                    &facts,
                ),
            _ => Ok(ResourceContext::new()
                .unchecked_with_fact(owner.clone())
                .normalized(&facts)),
        }
        .unwrap();
        assert!(
            resources
                .concrete_read_entries(&at(2), 4, &facts)
                .is_some_and(|entries| entries.exact()),
            "unattached checked context: mode={mode}"
        );
        assert!(
            resources
                .concrete_write_entries(&at(2), 4, &facts)
                .is_some_and(|entries| entries.exact())
        );
        assert!(resources.permits_memory_read(&at(2), 4, &facts));
        assert!(resources.memory_write_range(&at(2), 4, &facts).is_some());
        assert!(!resources.permits_memory_read(&at(2), 4, &empty));
        assert!(!resources.permits_memory_read(&at(2), 8, &facts));
    }
}

#[test]
fn checked_attachment_is_flat_beside_unrelated_equality_history() {
    for raw_input in [false, true] {
        let mut samples = Vec::new();
        let (base, alias) = (
            Pointer::symbolic(Variable(867_000)),
            Pointer::symbolic(Variable(867_001)),
        );
        for size in [16u64, 64, 256, 1024] {
            let initial = PureFactContext::new();
            let mut facts = initial.clone();
            for i in 0..size {
                facts = facts.assume_condition(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(868_000 + i)),
                        Bitvector32Term::Variable(Variable(868_001 + i)),
                    ),
                    true,
                );
            }
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(base.clone(), alias.clone()),
                true,
            );
            let owner = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
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
        assert!(
            samples[3].1 <= samples[0].1 * 2 + 64,
            "attachment walked equality history: {samples:?}"
        );
        assert!(
            samples[3].2 <= samples[0].2 * 4 + 512,
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
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(at(i), 0u32.into(), 4u32.into(), 1),
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
        let mut resources = ResourceContext::new().unchecked_with_fact(CResourceFact::Own(
            CResource::Memory(CMemoryRange::new_with_element_width(
                at(size + 2),
                0u32.into(),
                4u32.into(),
                1,
            )),
            Box::new(Bitvector32Term::Constant(0)),
        ));
        for i in (0..size).rev() {
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(at(i), 0u32.into(), 4u32.into(), 1),
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
                        let cell = CMemoryRange::new_with_element_width(
                            alias,
                            0u32.into(),
                            4u32.into(),
                            1,
                        );
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
                        Bitvector32Term::Variable(Variable(prefix + i)),
                        Bitvector32Term::Variable(Variable(prefix + i + 1)),
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
        let resources = resources.unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new_with_element_width(at(0), 0u32.into(), 4u32.into(), 1),
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
fn publication_in_one_branch_keeps_sibling_input_pairing() {
    for scaled in [false, true] {
        let scalar = |id: u64| Bitvector32Term::Variable(Variable(859_100 + id));
        let at = |id: u64| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: if scaled {
                PointerOffsetTerm::scale_int32(scalar(id), 4)
            } else {
                PointerOffsetTerm::Variable(Variable(859_100 + id))
            },
        };
        let equality = |left: u64, right: u64| {
            if scaled {
                ConditionTerm::equal(scalar(left), scalar(right))
            } else {
                ConditionTerm::pointer_offset_equal(at(left).offset, at(right).offset)
            }
        };
        let parent = PureFactContext::new();
        let first = parent.clone().assume_condition(equality(0, 1), true);
        let sibling = parent.clone().assume_condition(equality(0, 2), true);
        let resources = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new_with_element_width(at(0), 0u32.into(), 4u32.into(), 1),
        ));
        resources.synchronize_memory_equalities(&first);
        for (facts, alias) in [
            (&sibling, at(2)),
            (&first, at(1)),
            (&parent, at(0)),
            (&sibling, at(2)),
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
            let cell = CMemoryRange::new_with_element_width(alias, 0u32.into(), 4u32.into(), 1);
            assert_eq!(
                resources
                    .memory_fact_candidates(&cell, true, facts)
                    .entries
                    .len(),
                1
            );
        }
        assert!(!resources.permits_memory_read(&at(1), 4, &sibling));
        assert!(!resources.permits_memory_read(&at(2), 4, &first));
        assert!(!resources.permits_memory_read(&at(1), 4, &parent));
    }
}

#[test]
fn cell_index_follows_completed_pointer_reads_and_preserves_snapshots() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = CMemory::new();
    let snapshot = crate::kernel::intern_c_memory(memory.clone());
    let (a, b) = (
        Pointer::symbolic(Variable(852_010)),
        Pointer::symbolic(Variable(852_011)),
    );
    let read = |address: &Pointer| {
        let paths = crate::kernel::eval::evaluate_c_memory_load_paths(
            &memory,
            address.clone(),
            CType::Int64Pointer,
            Vec::new().into(),
            Vec::new(),
            &PureFactContext::new(),
            true,
            false,
            None,
            None,
        );
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &paths[0].outcome else {
            panic!("pointer read")
        };
        (value.pointer().clone(), paths[0].facts.clone())
    };
    let (x, xf) = read(&a);
    let (y, yf) = read(&b);
    let facts = xf
        .iter()
        .chain(&yf)
        .fold(PureFactContext::new(), |context, fact| {
            context.assume_execution_pure_fact(fact)
        });
    let cell = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        x.clone(),
        0u32.into(),
        4u32.into(),
        1,
    ));
    let resources = ResourceContext::new().unchecked_with_fact(cell.clone());
    // The pure branch and resource sibling both fork before publication.
    let sibling = resources.clone();
    let connected = facts
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
    resources.synchronize_memory_equalities(&facts);
    // Resource lookup must register retained read definitions itself. A prior
    // pointer-equality query must not be needed to warm the graph.
    assert!(
        resources
            .concrete_read_entries(&y, 4, &connected)
            .unwrap()
            .exact()
    );
    assert!(resources.permits_memory_read(&y, 4, &connected));
    assert!(
        resources
            .concrete_write_entries(&y, 4, &connected)
            .unwrap()
            .exact()
    );
    assert_eq!(
        resources.memory_write_range(&y, 4, &connected),
        cell.memory_own_range()
    );
    assert!(!sibling.permits_memory_read(&y, 4, &facts));
    assert!(sibling.memory_write_range(&y, 4, &facts).is_none());
    assert!(!resources.permits_memory_read(&y.offset_by_bytes(4), 4, &connected));
    let old = Pointer::loaded_value(&snapshot, &a);
    assert!(
        resources
            .concrete_read_entries(&old, 4, &connected)
            .unwrap()
            .exact()
    );
    assert!(resources.permits_memory_read(&old, 4, &connected));
    assert!(
        resources
            .concrete_write_entries(&old, 4, &connected)
            .unwrap()
            .exact()
    );
    assert_eq!(
        resources.memory_write_range(&old, 4, &connected),
        cell.memory_own_range()
    );
    // Shifted whole cells register only their retained read-atom dependency.
    // Storage-relative names with symbolic coordinates are still outside the
    // concrete interval fragment, but exact address evidence does apply.
    let shifted = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            x.offset_by_bytes(8),
            0u32.into(),
            4u32.into(),
            1,
        )),
    );
    for value in [&y, &old] {
        let query = value.offset_by_bytes(8);
        let mut candidates = shifted
            .concrete_read_entries(&query, 4, &connected)
            .unwrap();
        assert!(candidates.exact());
        let entry = candidates.next().unwrap();
        assert_eq!(candidates.address(entry), Some(x.offset_by_bytes(8)));
        assert!(candidates.next().is_none());
        assert!(shifted.permits_memory_read(&query, 4, &connected));
        assert!(shifted.memory_write_range(&query, 4, &connected).is_some());
    }
    assert!(!shifted.permits_memory_read(&y.offset_by_bytes(8), 4, &facts));
    assert!(shifted.permits_memory_read(&old.offset_by_bytes(8), 4, &facts));
    let later = crate::kernel::intern_c_memory(memory.with_block("later", 8));
    assert!(!resources.permits_memory_read(&Pointer::loaded_value(&later, &a), 4, &connected));
    assert!(
        resources
            .memory_write_range(&Pointer::loaded_value(&later, &a), 4, &connected)
            .is_none()
    );
    assert!(resources.memory_write_range(&y, 5, &connected).is_none());
    let removed = resources
        .clone()
        .without_exact_representation(&cell)
        .unwrap();
    assert!(!removed.permits_memory_read(&y, 4, &connected));
    assert!(removed.memory_write_range(&y, 4, &connected).is_none());
    let restored = removed.unchecked_with_fact(cell).normalized(&connected);
    assert!(restored.permits_memory_read(&y, 4, &connected));
    assert!(restored.memory_write_range(&y, 4, &connected).is_some());
}

#[test]
fn typed_cell_candidates_follow_raw_offset_syntax_and_check_ownership() {
    let var = |id| PointerOffsetTerm::Variable(Variable(id));
    let raw = PointerOffsetTerm::Add(Box::new(var(852_022)), Box::new(var(852_021)));
    let (owner, alias) = (
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: raw.clone(),
        },
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: var(852_023),
        },
    );
    let cell = |base| {
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base,
            0u32.into(),
            1u32.into(),
            4,
        ))
    };
    let resources = ResourceContext::new().unchecked_with_fact(cell(owner.clone()));
    let empty = PureFactContext::new();
    resources.synchronize_memory_equalities(&empty);
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_offset_equal(raw, alias.offset.clone()),
        true,
    );
    assert!(
        resources
            .concrete_read_entries(&alias, 4, &facts)
            .unwrap()
            .exact()
    );
    assert!(resources.permits_memory_read(&alias, 4, &facts));
    assert!(
        resources
            .concrete_write_entries(&alias, 4, &facts)
            .unwrap()
            .exact()
    );
    assert_eq!(
        resources.memory_write_range(&alias, 4, &facts),
        cell(owner.clone()).memory_own_range()
    );
    let entries = resources
        .memory_fact_candidates(cell(alias.clone()).memory_range().unwrap(), true, &facts)
        .entries;
    assert_eq!(entries.len(), 1);
    assert!(
        resources
            .clone()
            .without_fact_incrementally(&cell(alias.clone()), &facts)
            .is_some()
    );
    assert!(
        resources
            .clone()
            .without_fact_incrementally(&cell(alias.clone()), &empty)
            .is_none()
    );
    let view_only =
        ResourceContext::new_with_equalities(&empty).unchecked_with_fact(view(&owner, 0, 4));
    assert!(view_only.permits_memory_read(&alias, 4, &facts));
    assert!(view_only.memory_write_range(&alias, 4, &facts).is_none());
    assert!(
        view_only
            .without_fact_incrementally(&cell(alias), &facts)
            .is_none()
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
        let owner = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            at(0),
            0u32.into(),
            1u32.into(),
            C_POINTER_BYTE_WIDTH,
        ));
        let mut resources = ResourceContext::new().unchecked_with_fact(owner.clone());
        for i in 0..size {
            // Large footprint payload at the alias, plus unrelated owners.
            resources = resources
                .unchecked_with_fact(view(&at(1), 0, 8 + i as u32 * 4))
                .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
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
                let bytes = C_POINTER_BYTE_WIDTH;
                let entries = resources
                    .concrete_write_entries(&at(1), bytes, &facts)
                    .unwrap();
                assert!(entries.exact());
                assert_eq!(entries.count(), 1);
                assert_eq!(
                    resources.memory_write_range(&at(1), bytes, &facts),
                    owner.memory_own_range()
                );
                assert!(
                    resources
                        .concrete_write_entries(&at(1), bytes + 1, &facts)
                        .is_none()
                );
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
fn exact_address_classes_survive_unspellable_affine_shifts() {
    let owner = Pointer::symbolic(Variable(855_000));
    let alias = Pointer::symbolic(Variable(855_001));
    let x = PointerOffsetTerm::Variable(Variable(855_002));
    let displaced = Pointer {
        block: alias.block.clone(),
        offset: PointerOffsetTerm::Add(Box::new(x.clone()), Box::new(x)),
    };
    let resources = ResourceContext::new().unchecked_with_fact(view(&owner, 0, 4));
    let empty = PureFactContext::new();
    resources.synchronize_memory_equalities(&empty);
    // Keep the alias block representative so the indexed owner must move
    // by 2*x, which AffineOffset::to_offset_term does not spell.
    let mut facts = empty;
    for i in 3..8 {
        facts = facts.assume_condition(
            ConditionTerm::pointer_equal(alias.clone(), Pointer::symbolic(Variable(855_000 + i))),
            true,
        );
    }
    facts = facts.assume_condition(
        ConditionTerm::pointer_equal(owner.clone(), displaced.clone()),
        true,
    );
    assert!(facts.equality_graph.are_equal(&owner, &displaced));
    let mut candidates = resources
        .concrete_read_entries(&displaced, 4, &facts)
        .expect("exact address equality does not require spelling an affine displacement");
    let entry = candidates.next().expect("retained supplier");
    assert_eq!(candidates.address(entry), Some(owner.clone()));
    assert!(resources.permits_memory_read(&displaced, 4, &facts));
    // A nearby address has no exact class witness; an unspellable coordinate
    // cannot turn the interval classifier's unknown into a decisive miss.
    assert!(
        resources
            .concrete_read_entries(&displaced.offset_by_bytes(8), 4, &facts)
            .is_none()
    );
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
fn offset_equalities_update_already_indexed_cells() {
    let at = |variable| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(variable)),
    };
    let (owner, alias) = (at(852_000), at(852_001));
    let empty = PureFactContext::new();
    let resources = ResourceContext::new().unchecked_with_fact(view(&owner, 0, 4));
    resources.synchronize_memory_equalities(&empty);
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_offset_equal(owner.offset.clone(), alias.offset.clone()),
        true,
    );
    assert!(facts.equality_graph.are_equal(&owner, &alias));
    assert!(
        resources.concrete_read_entries(&alias, 4, &facts).is_some(),
        "a graph equality must reach the cell index"
    );
    assert!(resources.permits_memory_read(&alias, 4, &facts));
    assert!(!resources.permits_memory_read(&alias, 4, &empty));
}

#[test]
fn whole_cell_hits_remain_indexed_beside_other_read_shapes() {
    let at = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(857_000 + id)),
    };
    let owner = at(0);
    let alias = at(1);
    let resources = ResourceContext::new()
        .unchecked_with_fact(view(&owner, 0, 4))
        .unchecked_with_fact(view(&at(2), 0, 8))
        .unchecked_with_fact(CResourceFact::view_memory(
            CMemoryRange::new_with_element_width(
                at(3),
                0u32.into(),
                Bitvector32Term::Variable(Variable(857_100)),
                1,
            ),
        ));
    let empty = PureFactContext::new();
    resources.synchronize_memory_equalities(&empty);
    let facts = empty.assume_condition(
        ConditionTerm::pointer_offset_equal(owner.offset, alias.offset.clone()),
        true,
    );
    let candidates = resources
        .concrete_read_entries(&alias, 4, &facts)
        .expect("unrelated read shapes must not disable a known cell match");
    assert!(candidates.exact());
    assert_eq!(candidates.count(), 1);
    assert!(resources.permits_memory_read(&alias, 4, &facts));
    assert!(!resources.permits_memory_read(&alias, 8, &facts));
}

#[test]
fn cell_footprints_follow_merges_removals_and_normalization() {
    let at = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(858_000 + id)),
    };
    let (owner, alias) = (at(0), at(1));
    let (short, long) = (view(&owner, 0, 4), view(&alias, 0, 8));
    let zero = CResourceFact::Own(
        CResource::Memory(CMemoryRange::new_with_element_width(
            owner.clone(),
            0u32.into(),
            12u32.into(),
            1,
        )),
        Box::new(Bitvector32Term::Constant(0)),
    );
    let resources = ResourceContext::new()
        .unchecked_with_fact(short.clone())
        .unchecked_with_fact(long.clone())
        .unchecked_with_fact(zero);
    let empty = PureFactContext::new();
    resources.synchronize_memory_equalities(&empty);
    let sibling = resources.clone();
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_offset_equal(owner.offset.clone(), alias.offset.clone()),
        true,
    );
    resources.synchronize_memory_equalities(&facts);
    for bytes in [4, 8] {
        let candidates = resources
            .concrete_read_entries(&alias, bytes, &facts)
            .unwrap();
        assert!(candidates.exact());
        assert_eq!(candidates.count(), 1);
        assert!(resources.permits_memory_read(&owner, bytes, &facts));
    }
    assert!(!sibling.permits_memory_read(&owner, 8, &empty));
    assert!(!resources.permits_memory_read(&owner, 12, &facts));
    let removed = resources
        .clone()
        .without_exact_representation(&short)
        .unwrap();
    // Removing the whole-cell counterpart prunes its size-4 payload. The
    // remaining longer view supplies an indexed partial-read candidate.
    let partial = removed.concrete_read_entries(&alias, 4, &facts).unwrap();
    assert!(!partial.exact());
    assert_eq!(partial.count(), 1);
    assert!(removed.permits_memory_read(&alias, 4, &facts));
    assert!(
        removed
            .concrete_read_entries(&alias, 8, &facts)
            .unwrap()
            .exact()
    );
    let empty_cells = removed.without_exact_representation(&long).unwrap();
    assert!(!empty_cells.permits_memory_read(&alias, 4, &facts));
    let restored = empty_cells.unchecked_with_fact(short).normalized(&facts);
    assert!(
        restored
            .concrete_read_entries(&alias, 4, &facts)
            .unwrap()
            .exact()
    );
    assert!(restored.permits_memory_read(&alias, 4, &facts));
    assert!(!restored.permits_memory_read(&alias, 8, &facts));
}

#[test]
fn cell_footprint_merges_and_queries_do_not_scan_other_sizes() {
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
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
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "merge/query scanned other footprints: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "merge/query rebuilt the larger footprint payload: {samples:?}"
    );
}

#[test]
fn logical_pointer_reads_reach_resource_index_without_equality_warmup() {
    let _session = crate::kernel::VerificationSession::enter();
    let logical_pointer_read = |memory: &CMemory, address: &Pointer, context: &PureFactContext| {
        let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
            memory,
            address.clone(),
            CType::Int64Pointer,
            Vec::new().into(),
            Vec::new(),
            context,
        );
        let [path] = paths.as_slice() else {
            panic!("one logical read")
        };
        assert!(path.facts.is_empty());
        assert!(path.obligations.is_empty());
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &path.outcome else {
            panic!("pointer read")
        };
        value.pointer().clone()
    };
    let memory = CMemory::new();
    let a = Pointer::symbolic(Variable(92_250));
    let b = Pointer::symbolic(Variable(92_251));
    let before = PureFactContext::new();
    let x = logical_pointer_read(&memory, &a, &before);
    let y = logical_pointer_read(&memory, &b, &before);
    let owner = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
        CMemoryRange::new_with_element_width(x, 0u32.into(), 4u32.into(), 1),
    ));
    owner.synchronize_memory_equalities(&before);
    let sibling = before.clone();
    let branch = before
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(a.clone(), b.clone()), true);
    // Ask the resource index first, without warming pointer equality or
    // invoking a spelling fallback. Producer definitions are term metadata.
    assert!(
        owner
            .concrete_read_entries(&y, 4, &branch)
            .is_some_and(|entries| entries.exact())
    );
    assert!(
        owner
            .concrete_write_entries(&y, 4, &branch)
            .is_some_and(|entries| entries.exact())
    );
    assert!(owner.permits_memory_read(&y, 4, &branch));
    assert!(owner.memory_write_range(&y, 4, &branch).is_some());
    assert!(!owner.permits_memory_read(&y, 4, &sibling));
    assert!(!owner.permits_memory_read(&y.offset_by_bytes(4), 4, &branch));
    assert!(owner.memory_write_range(&y, 5, &branch).is_none());
    let later = memory.store(a, CValue::typed_pointer(b, CType::Int64Pointer));
    let z = logical_pointer_read(&later, &Pointer::symbolic(Variable(92_251)), &branch);
    assert!(!owner.permits_memory_read(&z, 4, &branch));
}

#[test]
fn interval_candidates_ignore_unrelated_scalar_equalities() {
    let base = Pointer::symbolic(Variable(895_000));
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(895_001)),
            Bitvector32Term::Variable(Variable(895_002)),
        ),
        true,
    );
    let resources =
        ResourceContext::new_with_equalities(&facts).unchecked_with_fact(view(&base, 0, 32));
    let query = base.offset_by_bytes(8);
    let mut candidates = resources
        .concrete_read_entries(&query, 4, &facts)
        .expect("unrelated scalar aliases must not disable a complete interval fragment");
    assert!(!candidates.exact());
    assert!(candidates.next().is_some());
    assert!(candidates.next().is_none());
    assert!(resources.permits_memory_read(&query, 4, &facts));
}

#[test]
fn interval_candidates_follow_loaded_pointer_origins_without_spelling_retry() {
    let a = Pointer::symbolic(Variable(895_010));
    let b = Pointer::symbolic(Variable(895_011));
    let snapshot = crate::kernel::intern_c_memory(CMemory::new());
    let x = Pointer::loaded_value(&snapshot, &a);
    let y = Pointer::loaded_value(&snapshot, &b);
    let initial = PureFactContext::new();
    let connected = initial
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(a, b), true);
    let resources = ResourceContext::new_with_equalities(&initial).unchecked_with_fact(
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            x.clone(),
            0u32.into(),
            32u32.into(),
            1,
        )),
    );
    let query = y.offset_by_bytes(8);
    let mut candidates = resources
        .concrete_read_entries(&query, 4, &connected)
        .expect("retained loaded-pointer origins must use the complete interval fragment");
    assert!(!candidates.exact());
    assert!(candidates.next().is_some());
    assert!(candidates.next().is_none());
    assert!(resources.permits_memory_read(&query, 4, &connected));
    assert!(!resources.permits_memory_read(&query, 4, &initial));
    assert!(
        resources
            .memory_write_range(&query, 4, &connected)
            .is_some()
    );
    assert!(resources.memory_write_range(&query, 4, &initial).is_none());
    for start in [0u32, 8] {
        let required = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            if start == 0 { query.clone() } else { y.clone() },
            start.into(),
            (start + 4).into(),
            1,
        ));
        assert!(
            resources
                .directly_supporting_owned_entry(&required, &connected)
                .is_some(),
            "ownership support must use the candidate's retained graph alignment"
        );
        assert!(
            resources
                .directly_supporting_owned_entry(&required, &initial)
                .is_none()
        );
    }
    assert!(!resources.permits_memory_read(&y.offset_by_bytes(30), 4, &connected));
    assert!(
        resources
            .memory_write_range(&y.offset_by_bytes(30), 4, &connected)
            .is_none()
    );
    let later = crate::kernel::intern_c_memory(CMemory::new().with_block("later", 8));
    let other_snapshot = Pointer::loaded_value(&later, &Pointer::symbolic(Variable(895_010)));
    assert!(!resources.permits_memory_read(&other_snapshot.offset_by_bytes(8), 4, &connected));
}

#[test]
fn interval_completeness_is_local_and_follows_late_offset_dependencies() {
    let base = Pointer::symbolic(Variable(895_020));
    let other = Pointer::symbolic(Variable(895_021));
    let offset = PointerOffsetTerm::Variable(Variable(895_022));
    let initial = PureFactContext::new();
    let resources = ResourceContext::new_with_equalities(&initial)
        .unchecked_with_fact(view(&base, 0, 32))
        .unchecked_with_fact(view(&other, 0, 32));
    // Register an offset dependency before its later merge. It must taint
    // only this block, including existing interval payloads in the fork.
    let _ = resources.concrete_read_entries(
        &Pointer {
            block: base.block.clone(),
            offset: offset.clone(),
        },
        4,
        &initial,
    );
    let connected = initial.clone().assume_condition(
        ConditionTerm::pointer_equal(
            Pointer {
                block: base.block.clone(),
                offset,
            },
            base.offset_by_bytes(8),
        ),
        true,
    );
    assert_eq!(
        resources
            .concrete_read_entries(&base.offset_by_bytes(12), 4, &connected)
            .expect("retained interval hit survives incomplete coverage")
            .count(),
        1
    );
    assert!(
        resources
            .concrete_read_entries(&base.offset_by_bytes(48), 4, &connected)
            .is_none()
    );
    assert_eq!(
        resources
            .concrete_read_entries(&base.offset_by_bytes(48), 4, &initial)
            .expect("complete concrete miss")
            .count(),
        0
    );
    assert!(
        resources
            .concrete_read_entries(&other.offset_by_bytes(12), 4, &connected)
            .is_some()
    );
    assert!(
        resources
            .concrete_read_entries(&base.offset_by_bytes(12), 4, &initial)
            .is_some()
    );
    // Unknown interval completeness does not erase checked exact evidence.
    let exact = resources.clone().unchecked_with_fact(view(&base, 40, 44));
    assert!(
        exact
            .concrete_read_entries(&base.offset_by_bytes(40), 4, &connected)
            .is_some_and(|entries| entries.exact())
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
                Bitvector32Term::Variable(Variable(895_032)),
                Bitvector32Term::Variable(Variable(895_033)),
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
fn interval_alignment_retains_query_and_occurrence_checkpoint() {
    let base = Pointer::symbolic(Variable(895_040));
    let alias = Pointer::symbolic(Variable(895_041));
    let empty = PureFactContext::new();
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_equal(base.clone(), alias.clone()),
        true,
    );
    let cell = view(&base, 0, 4);
    let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(cell.clone());
    let mut candidates = resources.concrete_read_entries(&alias, 4, &facts).unwrap();
    let entry = candidates.next().unwrap();
    // Removal changes the live fork, not retained evidence or occurrence IDs.
    let removed = resources
        .clone()
        .without_exact_representation(&cell)
        .unwrap();
    assert_eq!(candidates.address(entry), Some(base.clone()));
    assert!(!removed.permits_memory_read(&alias, 4, &facts));
    assert!(!resources.permits_memory_read(&alias, 4, &empty));
    assert!(!resources.permits_memory_read(&alias, 5, &facts));
    assert!(resources.memory_write_range(&alias, 4, &facts).is_none());
}

#[test]
fn unpublished_loaded_intervals_do_not_claim_complete_supplier_coverage() {
    let a = Pointer::symbolic(Variable(895_060));
    let b = Pointer::symbolic(Variable(895_061));
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let x = Pointer::loaded_value(&memory, &a);
    let y = Pointer::loaded_value(&memory, &b);
    let facts = PureFactContext::new().assume_condition(ConditionTerm::pointer_equal(a, b), true);
    // The raw structural root has not registered x's defining load. A short
    // unrelated entry under y must not turn a missing supplier into a denial.
    let resources = ResourceContext::new()
        .unchecked_with_fact(view(&x, 0, 32))
        .unchecked_with_fact(view(&y, 0, 4));
    let query = y.offset_by_bytes(8);
    assert!(resources.concrete_read_entries(&query, 4, &facts).is_none());
    resources.synchronize_memory_equalities(&facts);
    assert!(resources.concrete_read_entries(&query, 4, &facts).is_some());
    assert!(resources.permits_memory_read(&query, 4, &facts));
}
#[test]
fn write_permission_does_not_enumerate_covering_views() {
    let base = Pointer::symbolic(Variable(960_200));
    let facts = PureFactContext::new();
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let mut resources = ResourceContext::new_with_equalities(&facts);
        for i in 0..size {
            resources = resources.unchecked_with_fact(view(&base, 0, 8 + i));
        }
        resources = resources.unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new_with_element_width(base.clone(), 0u32.into(), 4u32.into(), 1),
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
}

#[test]
#[ignore = "nightly: 2.0s in the parallel gate"]
fn symbolic_write_permission_does_not_search_views() {
    let base = Pointer::symbolic(Variable(961_000));
    let alias = Pointer::symbolic(Variable(961_001));
    let i = Bitvector32Term::Variable(Variable(961_002));
    let n = Bitvector32Term::Variable(Variable(961_003));
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
    let owned = CMemoryRange::new_with_element_width(base.clone(), 1u32.into(), n.clone(), 1);
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let mut resources = ResourceContext::new_with_equalities(&facts);
        for k in 0..size {
            resources = resources.unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(base.clone(), k.into(), n.clone(), 1),
            ));
        }
        resources = resources.unchecked_with_fact(CResourceFact::own_memory(owned.clone()));
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
fn sole_symbolic_write_owner_preserves_bounds_authority_and_forks() {
    let base = Pointer::symbolic(Variable(961_100));
    let alias = Pointer::symbolic(Variable(961_101));
    let i = Bitvector32Term::Variable(Variable(961_102));
    let n = Bitvector32Term::Variable(Variable(961_103));
    let empty = PureFactContext::new();
    let bounds = empty
        .clone()
        .assume_condition(
            ConditionTerm::signed_less_equal(1u32.into(), i.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i.clone(), n.clone()), true);
    let facts = bounds.clone().assume_condition(
        ConditionTerm::pointer_equal(base.clone(), alias.clone()),
        true,
    );
    let range = CMemoryRange::new_with_element_width(base.clone(), 1u32.into(), n.clone(), 1);
    let owner = CResourceFact::own_memory(range.clone());
    let resources = ResourceContext::new_with_equalities(&empty)
        .unchecked_with_fact(CResourceFact::view_memory(range.clone()))
        .unchecked_with_fact(owner.clone());
    resources.synchronize_memory_equalities(&empty);
    let query = alias.offset_by_elements(i.clone(), 1);
    assert_eq!(
        resources.memory_write_range(&query, 1, &facts),
        Some(&range)
    );
    assert!(resources.memory_write_range(&query, 1, &bounds).is_none());
    assert!(resources.memory_write_range(&base, 1, &facts).is_none());
    assert!(
        resources
            .memory_write_range(&alias.offset_by_elements(n, 1), 1, &facts)
            .is_none()
    );
    assert!(resources.memory_write_range(&query, 2, &facts).is_none());
    let no_bounds = empty.clone().assume_condition(
        ConditionTerm::pointer_equal(base.clone(), alias.clone()),
        true,
    );
    assert!(
        resources
            .memory_write_range(&query, 1, &no_bounds)
            .is_none()
    );
    let views = resources
        .clone()
        .without_exact_representation(&owner)
        .unwrap();
    assert!(views.memory_write_range(&query, 1, &facts).is_none());
    for quantity in [0u32, u32::MAX] {
        let invalid = views.clone().unchecked_with_fact(CResourceFact::Own(
            CResource::Memory(range.clone()),
            Box::new(quantity.into()),
        ));
        assert!(invalid.memory_write_range(&query, 1, &facts).is_none());
    }
    // Both occurrences must follow the late class merge. Selection reports
    // unknown rather than trying owners until one happens to cover the query.
    let second = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        alias,
        0u32.into(),
        range.end().clone(),
        1,
    ));
    let ambiguous = resources.clone().unchecked_with_fact(second.clone());
    assert!(ambiguous.write_access_entries(&query, 1, &facts).is_none());
    let restored = ambiguous.without_exact_representation(&second).unwrap();
    assert_eq!(restored.memory_write_range(&query, 1, &facts), Some(&range));
    assert_eq!(
        resources.memory_write_range(&query, 1, &facts),
        Some(&range)
    );
}

#[test]
#[ignore = "nightly: 0.8s in the parallel gate"]
fn symbolic_partition_read_start_is_indexed_without_searching_other_ranges() {
    let base = Pointer::symbolic(Variable(899_000));
    let i = Bitvector32Term::Variable(Variable(899_001));
    let split = Bitvector32Term::Variable(Variable(899_002));
    let end = Bitvector32Term::Variable(Variable(899_003));
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
            .unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(base.clone(), 0u32.into(), split.clone(), 1),
            ))
            .unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(base.clone(), split.clone(), end.clone(), 1),
            ));
        for k in 1..=size {
            resources = resources.unchecked_with_fact(CResourceFact::view_memory(
                CMemoryRange::new_with_element_width(base.clone(), k.into(), end.clone(), 1),
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
fn memory_support_returns_retained_occurrences_through_transitive_aliases() {
    let p = Pointer::symbolic(Variable(974_000));
    let q = Pointer::symbolic(Variable(974_001));
    let r = Pointer::symbolic(Variable(974_002));
    let empty = PureFactContext::new();
    let facts = empty
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true)
        .assume_condition(ConditionTerm::pointer_equal(q, r.clone()), true);
    let owner = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        p,
        0u32.into(),
        8u32.into(),
        1,
    ));
    let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(owner.clone());
    let required = view(&r, 2, 4);
    assert_eq!(
        resources.directly_supporting_fact(&required, &facts),
        Some(&owner)
    );
    let support = resources
        .directly_supporting_owned_entry(&required, &facts)
        .unwrap();
    assert_eq!(support.0, resources.occurrences_for_fact(&owner)[0]);
    assert_eq!(support.1, &owner);
    assert!(
        resources
            .directly_supporting_fact(&required, &empty)
            .is_none()
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
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
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
                assert!(
                    !resources
                        .has_other_directly_supporting_owned_entry(&piece, occurrence, &facts)
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
fn indexed_memory_support_never_promotes_zero_quantity() {
    let p = Pointer::symbolic(Variable(976_000));
    let facts = PureFactContext::new();
    let range = CMemoryRange::new_with_element_width(p, 0u32.into(), 4u32.into(), 1);
    let owner = CResourceFact::own_memory(range.clone());
    let zero = CResourceFact::Own(CResource::Memory(range), Box::new(0u32.into()));
    let resources = ResourceContext::new_with_equalities(&facts).unchecked_with_fact(zero);
    assert!(!resources.satisfies_fact(&owner, &facts));
    assert!(resources.directly_supporting_fact(&owner, &facts).is_none());
    assert!(
        resources
            .directly_supporting_owned_entry(&owner, &facts)
            .is_none()
    );
    assert!(
        resources
            .without_fact_incrementally(&owner, &facts)
            .is_none()
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
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(base.clone(), i.into(), (i + 1).into(), 1),
            ));
        }
        let required = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
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
            let owner = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
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
    let i = Bitvector32Term::Variable(Variable(977_001));
    let n = Bitvector32Term::Variable(Variable(977_002));
    let middle = Bitvector32Term::Variable(Variable(977_003));
    let next = Bitvector32Term::add(i.clone(), 1u32.into());
    let facts = PureFactContext::new()
        .assume_condition(
            ConditionTerm::Bitvector32Equal(Box::new(n.clone()), Box::new(4u32.into())),
            true,
        )
        .assume_condition(
            ConditionTerm::Bitvector32Equal(Box::new(i.clone()), Box::new(middle.clone())),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(i.clone(), 0u32.into()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i.clone(), n.clone()), true);
    let own = |start, end| CResourceFact::own_memory(CMemoryRange::new(p.clone(), start, end));
    let required = own(0u32.into(), n.clone());
    let mut samples = Vec::new();
    for size in [16u32, 64, 256, 1024] {
        let mut resources = ResourceContext::new_with_equalities(&facts)
            .unchecked_with_fact(own(0u32.into(), i.clone()))
            .unchecked_with_fact(own(next.clone(), n.clone()))
            .unchecked_with_fact(own(middle.clone(), next.clone()))
            .unchecked_with_fact(CResourceFact::view_memory(CMemoryRange::new(
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
    let i = Bitvector32Term::Variable(Variable(978_001));
    let j = Bitvector32Term::Variable(Variable(978_002));
    let n = Bitvector32Term::Variable(Variable(978_003));
    let next_i = Bitvector32Term::add(i.clone(), 1u32.into());
    let next_j = Bitvector32Term::add(j.clone(), 1u32.into());
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
    let own = |start, end| CResourceFact::own_memory(CMemoryRange::new(p.clone(), start, end));
    let tail = own(next_i, n);
    let required = own(j.clone(), next_j);
    let shifted = CResourceFact::own_memory(CMemoryRange::new(
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
fn fragment_coordinate_residues_do_not_establish_wide_pointer_adjacency() {
    let p = Pointer::symbolic(Variable(979_000));
    let positive = Pointer {
        block: p.block.clone(),
        offset: PointerOffsetTerm::Constant(i64::from(i32::MAX)),
    };
    let negative = Pointer {
        block: p.block,
        offset: PointerOffsetTerm::Constant(i64::from(i32::MIN)),
    };
    let own = |base, end| {
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base,
            0u32.into(),
            end,
            1,
        ))
    };
    let facts = PureFactContext::new();
    let resources = ResourceContext::new_with_equalities(&facts)
        .unchecked_with_fact(own(positive.clone(), 1u32.into()))
        .unchecked_with_fact(own(negative, 1u32.into()));
    let required = own(positive, 2u32.into());
    // The first piece's end has INT32_MIN's residue, but its true byte
    // address is 2^31. The negative piece cannot fill the adjacent byte.
    assert!(!resources.satisfies_fact(&required, &facts));
    assert!(
        resources
            .without_fact_incrementally(&required, &facts)
            .is_none()
    );
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
                    Bitvector32Term::Variable(Variable(980_001 + u64::from(k))),
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
fn storage_ownership_follows_transitive_address_equality() {
    let base = Pointer::symbolic(Variable(894_000));
    let alias = Pointer::symbolic(Variable(894_001));
    let last = Pointer::symbolic(Variable(894_002));
    let empty = PureFactContext::new();
    let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(
        CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base.clone(),
            0u32.into(),
            48u32.into(),
            1,
        )),
    );
    let facts = empty
        .clone()
        .assume_condition(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        )
        .assume_condition(ConditionTerm::pointer_equal(alias, last.clone()), true);
    assert!(resources.owns_storage_access(&last.offset_by_bytes(8), 40, &facts));
    assert!(!resources.owns_storage_access(&last.offset_by_bytes(9), 40, &facts));
    assert!(!resources.owns_storage_access(&last, 40, &empty));
    assert!(
        !ResourceContext::new_with_equalities(&facts)
            .unchecked_with_fact(view(&base, 0, 48))
            .owns_storage_access(&last, 40, &facts)
    );
}

#[test]
fn object_evidence_uses_provenance_classes_and_live_nonempty_occurrences() {
    let external = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(898_000 + id)),
    };
    let source = external(0);
    let target = external(1);
    let empty = PureFactContext::new();
    let fact = view(&source, 0, 4);
    let resources = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(fact.clone());
    let address_only = empty.clone().assume_condition(
        ConditionTerm::pointer_equal(source.clone(), target.clone()),
        true,
    );
    assert!(
        resources
            .memory_object_evidence(&target, &address_only)
            .is_none()
    );
    let shared_object = address_only.assume_condition(
        ConditionTerm::pointer_equal(source.object_identity(), target.object_identity()),
        true,
    );
    assert_eq!(
        resources.memory_object_evidence(&target, &shared_object),
        Some(&fact)
    );
    assert!(resources.memory_object_evidence(&target, &empty).is_none());
    assert_eq!(
        resources.memory_object_evidence(&source.offset_by_bytes(100), &empty),
        Some(&fact)
    );
    assert!(!resources.owns_storage_access(&source, 4, &empty));
    let owner = CResourceFact::own_memory(fact.memory_range().unwrap().clone());
    let owned = ResourceContext::new_with_equalities(&empty).unchecked_with_fact(owner.clone());
    let gone = owned
        .clone()
        .without_fact_incrementally(&owner, &empty)
        .unwrap();
    assert!(gone.memory_object_evidence(&source, &empty).is_none());
    assert_eq!(owned.memory_object_evidence(&source, &empty), Some(&owner));
    for fact in [
        view(&source, 0, 0),
        CResourceFact::own_quantity(
            CResource::Memory(CMemoryRange::new_with_element_width(
                source.clone(),
                0u32.into(),
                4u32.into(),
                1,
            )),
            0u32.into(),
        ),
    ] {
        assert!(
            ResourceContext::new_with_equalities(&empty)
                .unchecked_with_fact(fact)
                .memory_object_evidence(&source, &empty)
                .is_none()
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
            facts = facts.assume_proposition(Proposition::CResourceComposition(
                ResourceContext::new().unchecked_with_fact(view(&external(id), 0, 4)),
            ));
        }
        let sibling = facts.clone();
        facts = facts.assume_proposition(Proposition::CResourceComposition(
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
    let dormant = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
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
            .assume_proposition(Proposition::CResourceComposition(left));
        let (facts, work) = crate::instrumentation::measure_deterministic_work(|| {
            parent
                .clone()
                .assume_proposition(Proposition::CResourceComposition(right))
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
            facts.assume_proposition(Proposition::CResourceComposition(common))
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
    let memory = CMemory::new();
    let empty = PureFactContext::new();
    let read = |id| {
        let paths = crate::kernel::eval::evaluate_logical_memory_load_paths(
            &memory,
            Pointer::symbolic(Variable(id)),
            CType::Int32Pointer,
            Vec::new().into(),
            Vec::new(),
            &empty,
        );
        let CExpressionOutcome::Value(CValue::Pointer(value)) = &paths[0].outcome else {
            panic!("pointer read")
        };
        value.pointer().clone()
    };
    let base = read(972_100);
    let unrelated = read(972_101);
    let captured = Pointer::symbolic(Variable(972_102));
    let i = Bitvector32Term::Variable(Variable(972_103));
    let n = Bitvector32Term::Variable(Variable(972_104));
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
    let range = CMemoryRange::new(base.clone(), 0u32.into(), n.clone());
    let owner = CResourceFact::own_memory(range.clone());
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
        .unchecked_with_fact(CResourceFact::view_memory(range));
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
            frame = frame.unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
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
    let i = Bitvector32Term::Variable(Variable(973_102));
    let n = Bitvector32Term::Variable(Variable(973_103));
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
    let range = CMemoryRange::new(base, 0u32.into(), n);
    let mut samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut frame = ResourceContext::new_with_equalities(&empty)
            .unchecked_with_fact(CResourceFact::own_memory(range.clone()));
        for k in 0..size {
            let field = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(974_000 + k)),
            };
            frame = frame.unchecked_with_fact(CResourceFact::own_memory(
                CMemoryRange::new_with_element_width(field, 0u32.into(), 1u32.into(), 8),
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

// A read congruence learned through whole offsets must reach ownership's
// incremental class index, not just return true from an equality query.
#[test]
fn typed_read_congruence_publishes_late_ownership_class_updates() {
    let memory = crate::kernel::intern_c_memory(CMemory::new());
    let p = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(998_001)),
    };
    let q = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(998_002)),
    };
    let x = Pointer::loaded_value(&memory, &p);
    let y = Pointer::loaded_value(&memory, &q);
    let empty = PureFactContext::new();
    let resources =
        ResourceContext::new_with_equalities(&empty).unchecked_with_fact(view(&x, 0, 32));
    assert!(!resources.permits_memory_read(&y.offset_by_bytes(8), 4, &empty));
    let joined = empty.clone().assume_condition(
        ConditionTerm::pointer_offset_equal(p.offset, q.offset),
        true,
    );
    assert!(resources.permits_memory_read(&y.offset_by_bytes(8), 4, &joined));
    assert!(!resources.permits_memory_read(&y.offset_by_bytes(30), 4, &joined));
    assert!(!resources.permits_memory_read(&y.offset_by_bytes(8), 4, &empty));
}

#[test]
fn symbolic_owned_suffix_start_checks_bounds_and_retained_authority() {
    let base = Pointer::symbolic(Variable(989_000));
    let split = Bitvector32Term::Variable(Variable(989_001));
    let empty = PureFactContext::new();
    let facts = empty.clone().assume_condition(
        ConditionTerm::uint64_less_than(split.clone(), Bitvector32Term::UInt64Constant(32)),
        true,
    );
    let prefix = CMemoryRange::new_wide(
        base.clone(),
        Bitvector32Term::UInt64Constant(0),
        split.clone(),
        1,
    );
    let suffix = CMemoryRange::new_wide(
        base.clone(),
        split.clone(),
        Bitvector32Term::UInt64Constant(32),
        1,
    );
    let owner = CResourceFact::own_memory(suffix.clone());
    let resources = ResourceContext::new_with_equalities(&empty)
        .unchecked_with_fact(CResourceFact::own_memory(prefix))
        .unchecked_with_fact(CResourceFact::view_memory(suffix.clone()))
        .unchecked_with_fact(owner.clone());
    resources.synchronize_memory_equalities(&empty);
    let query = suffix.start_pointer();
    assert_eq!(
        resources.memory_write_range(&query, 1, &facts),
        Some(&suffix)
    );
    assert!(resources.memory_write_range(&query, 1, &empty).is_none());
    assert!(resources.memory_write_range(&query, 2, &facts).is_none());
    assert!(
        resources
            .memory_write_range(
                &CMemoryRange::new_wide(
                    base,
                    Bitvector32Term::UInt64Constant(32),
                    Bitvector32Term::UInt64Constant(33),
                    1
                )
                .start_pointer(),
                1,
                &facts
            )
            .is_none()
    );
    let removed = resources
        .clone()
        .without_exact_representation(&owner)
        .unwrap();
    assert!(removed.memory_write_range(&query, 1, &facts).is_none());
    assert_eq!(
        resources.memory_write_range(&query, 1, &facts),
        Some(&suffix)
    );
}

#[test]
fn framed_pointer_fragments_rejoin_through_their_checked_read_endpoint() {
    let mut work_samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let read = |context: &PureFactContext, memory: &CMemory| {
            let snapshot = crate::kernel::intern_c_memory_ref(memory);
            let variable = crate::kernel::load_variable_for_cell_with_origin(
                &snapshot,
                &field,
                LoadKind::Pointer,
                C_POINTER_BYTE_WIDTH,
                &snapshot,
            );
            let pointer =
                Pointer::loaded(field.block.clone(), Bitvector32Term::Variable(variable), 4);
            context.register_pointer_read(&pointer, &snapshot, &field);
            pointer
        };
        let source = read(&PureFactContext::new(), &CMemory::new());
        let before = CMemory::new().store(
            field.clone(),
            CValue::Pointer(CPointerValue::new(source.clone(), CType::Int32Pointer)),
        );
        let range = |base: Pointer, start: u32, end: u32| {
            CMemoryRange::new_with_element_width(base, start.into(), end.into(), 4)
        };
        let separation = Proposition::CResourceSeparate {
            left: Box::new(CResource::Memory(range(field.clone(), 0, 2))),
            right: Box::new(CResource::Memory(range(source.clone(), 0, 8))),
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
        let tail = CResourceFact::own_memory(range(source.clone(), 1, 8));
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(tail.clone())
            .unchecked_with_fact(CResourceFact::own_memory(range(current.clone(), 0, 1)));
        for index in 0..size {
            resources = resources.unchecked_with_fact(CResourceFact::own_memory(range(
                Pointer::symbolic(Variable(9_911_000 + index)),
                0,
                8,
            )));
        }
        resources.synchronize_memory_equalities(&context);
        let required = CResourceFact::own_memory(range(current.clone(), 0, 8));
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources
                .clone()
                .without_fact_incrementally(&required, &context)
        });
        let remaining = remaining.expect("selected framed prefix and tail must rejoin");
        assert_eq!(remaining.iter().count(), size as usize);
        work_samples.push(work);
        assert!(!context.equality_graph.are_equal(&source, &current));
        let weakened = context.without_exact_fact(&separation);
        assert!(
            resources
                .clone()
                .without_fact_incrementally(&required, &weakened)
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
        let partial = after.store(field.offset_by_bytes(4), CValue::Int32(9u32.into()));
        let changed = CResourceFact::own_memory(range(read(&context, &partial), 0, 8));
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
}
