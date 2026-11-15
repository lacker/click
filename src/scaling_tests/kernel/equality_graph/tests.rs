// Scaling tests of `src/kernel/equality_graph.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_borrow_alignment_retains_both_index_widths_without_alias_scans() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256, 1024] {
        let mut graph = EqualityGraph::default();
        let bytes = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(index(999_200), 1),
        };
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(index(999_201), 1),
        };
        let computed = base.offset_by_elements(index(999_202), 1);
        let wide = bytes.offset_by_typed_elements(index(999_203), 1, true, true);
        assert!(graph.add_offset_equality(&computed.offset, &wide.offset));
        assert_eq!(graph.additive_address(&computed), Some(computed.clone()));
        assert_eq!(graph.wide_additive_address(&computed), Some(wide.clone()));
        for item in 0..size {
            let alias = Pointer::symbolic(Variable(1_100_000 + item));
            assert!(graph.add_equality(&alias, &computed));
        }
        let cursor = Pointer::symbolic(Variable(1_100_000 + size - 1));
        let (((aligned, lane), work), map_work) =
            crate::persistent::measure_persistent_work(|| {
                crate::instrumentation::measure_deterministic_work(|| {
                    (
                        graph.pointer_at_base_with_wide_index(&cursor, &bytes),
                        graph.pointer_at_base_with_wide_index(&cursor.offset_by_bytes(1), &bytes),
                    )
                })
            });
        assert_eq!(lane, Some(wide.offset_by_bytes(1)));
        assert_eq!(aligned, Some(wide));
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "wide alignment scanned the address class: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "wide alignment map work scanned the address class: {samples:?}"
    );
}

// Every pointer equality query registers both addresses. Repeating a
// query reuses the registered address nodes: it neither grows the graph
// nor renormalizes and recloses the offsets, so its work is a fraction of
// the first query's and linear in the offsets it reinterns.
#[test]
fn repeated_address_queries_reuse_registered_addresses() {
    let mut costs = Vec::new();
    for size in [8u64, 32, 128] {
        let mut graph = EqualityGraph::default();
        assert!(graph.add_equality(&at(symbolic(1), 0), &at(symbolic(2), 16)));
        // An unrelated offset equality enables registered comparisons.
        graph.add_int32_equality(&index(1), &index(2));
        // Distinct indices give the sides different affine forms, so the
        // query reaches address registration, whose normal form of each
        // offset is a fresh flattened term.
        let offset = |first: u64| {
            (0..size).fold(PointerOffsetTerm::Constant(0), |sum, item| {
                PointerOffsetTerm::Add(
                    Box::new(sum),
                    Box::new(PointerOffsetTerm::scaled_int32_node(index(first + item), 4)),
                )
            })
        };
        let left = Pointer {
            block: symbolic(1),
            offset: offset(1_000),
        };
        let right = Pointer {
            block: symbolic(2),
            offset: offset(5_000),
        };
        let (first, first_work) =
            crate::instrumentation::measure_deterministic_work(|| graph.are_equal(&left, &right));
        let nodes = graph
            .state
            .lock()
            .expect("equality graph")
            .terms
            .node_count();
        let (repeated, repeated_work) =
            crate::instrumentation::measure_deterministic_work(|| graph.are_equal(&left, &right));
        assert_eq!(first, repeated);
        assert_eq!(
            graph
                .state
                .lock()
                .expect("equality graph")
                .terms
                .node_count(),
            nodes,
            "a repeated query must not register new nodes"
        );
        // Reinterning the raw offsets is about half the first query;
        // renormalizing and reinterning both normal forms would be more.
        assert!(
            repeated_work * 5 <= first_work * 3,
            "repeated {repeated_work}, first {first_work}"
        );
        costs.push((size, repeated_work));
    }
    for pair in costs.windows(2) {
        let ((small, small_work), (large, large_work)) = (pair[0], pair[1]);
        assert!(
            large_work <= small_work * (large / small) as usize * 2,
            "{costs:?}"
        );
    }
}

#[test]
fn reading_one_class_merge_does_not_walk_the_shared_history() {
    let samples = [16_u64, 64, 256]
        .into_iter()
        .map(|size| {
            let mut graph = EqualityGraph::default();
            for block in 1..size {
                assert!(
                    graph.add_equality(&at(symbolic(50_000), 0), &at(symbolic(50_000 + block), 0),)
                );
            }
            let parent = graph.clone();
            assert!(graph.add_equality(&at(symbolic(50_000), 0), &at(symbolic(50_000 + size), 0),));
            let mut sibling = parent.clone();
            sibling.add_equality(&at(symbolic(60_000), 0), &at(symbolic(60_001), 0));
            let (mismatch, mismatch_work) =
                crate::instrumentation::measure_deterministic_work(|| {
                    graph.pointer_merges_since(&sibling)
                });
            assert!(mismatch.is_none());
            assert_eq!(mismatch_work, 0, "sibling check walked the shared prefix");
            let (merges, work) = crate::instrumentation::measure_deterministic_work(|| {
                graph.pointer_merges_since(&parent).unwrap()
            });
            assert_eq!(merges.len(), 1);
            (size, work)
        })
        .collect::<Vec<_>>();
    assert!(
        samples.iter().all(|(_, work)| *work == samples[0].1),
        "one merge delta grew with the shared prefix: {samples:?}"
    );
}

#[test]
fn same_block_pointer_premise_chains_have_indexed_work() {
    for size in [16u64, 64, 256, 1024] {
        let block = symbolic(11_030);
        let offset = |i| PointerOffsetTerm::Variable(Variable(20_000 + i));
        let mut graph = EqualityGraph::default();
        let (_, insertion_work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                assert!(graph.add_equality(
                    &at_offset(block.clone(), offset(i)),
                    &at_offset(block.clone(), offset(i + 1)),
                ));
            }
        });
        assert!(
            insertion_work <= 128 * size as usize,
            "size={size}, insertion work={insertion_work}"
        );
        let (equal, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.are_offsets_equal(&offset(0), &offset(size))
        });
        assert!(equal);
        assert!(query_work < 64, "size={size}, query work={query_work}");
    }
}

#[test]
fn equal_base_offset_queries_ignore_unrelated_class_members() {
    for size in [16u64, 64, 256, 1024] {
        let x = PointerOffsetTerm::Variable(Variable(11_050));
        let y = PointerOffsetTerm::Variable(Variable(11_051));
        let mut graph = EqualityGraph::default();
        for i in 0..size {
            graph.add_equality(&at(symbolic(30_000 + i), 0), &at(symbolic(30_001 + i), 0));
        }
        graph.add_offset_equality(&x, &y);
        let left = at_offset(symbolic(30_000), x.clone());
        let right = at_offset(symbolic(30_000 + size), y.clone());
        let (equal, work) =
            crate::instrumentation::measure_deterministic_work(|| graph.are_equal(&left, &right));
        assert!(equal);
        assert!(work < 64, "size={size}, work={work}");
        let (equal, map_work) =
            crate::persistent::measure_persistent_work(|| graph.are_equal(&left, &right));
        assert!(equal);
        assert!(
            map_work < 64 * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn pointer_transitivity_recovers_same_block_offsets() {
    let offset = |id| PointerOffsetTerm::scaled_int32_node(index(id), 4);
    for reverse in [false, true] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128, 512] {
            let x = at_offset(PointerBlock::ExternalArgument, offset(960_000));
            let y = at_offset(PointerBlock::ExternalArgument, offset(960_001));
            let z = at(symbolic(960_002), 0);
            let mut graph = EqualityGraph::default();
            for id in 0..size {
                graph.add_equality(
                    &at_offset(
                        symbolic(961_000 + id),
                        PointerOffsetTerm::Variable(Variable(963_000 + id)),
                    ),
                    &z,
                );
            }
            if reverse {
                graph.add_equality(&z, &y);
            } else {
                graph.add_equality(&x, &z);
            }
            let sibling = graph.clone();
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                if reverse {
                    graph.add_equality(&x, &z);
                } else {
                    graph.add_equality(&z, &y);
                }
            });
            // A new non-affine offset relation can invalidate affine
            // completeness for the registered dependent addresses once.
            assert!(work <= 16 * size as usize + 512, "size={size}, work={work}");
            let (_, query_work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(graph.are_offsets_equal(&x.offset, &y.offset));
                assert!(graph.are_equal(&x, &y));
                assert!(!graph.are_equal(&x, &y.offset_by_bytes(1)));
            });
            samples.push(query_work);
            assert!(!sibling.are_offsets_equal(&x.offset, &y.offset));
            assert!(!sibling.are_equal(&x, &y));
        }
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 40),
            "reverse={reverse}, query work={samples:?}"
        );
    }
    // Equal addresses from different blocks do not equate their offsets.
    let mut graph = EqualityGraph::default();
    graph.add_equality(&at(symbolic(962_000), 4), &at(symbolic(962_001), 8));
    assert!(!graph.are_offsets_equal(
        &PointerOffsetTerm::Constant(4),
        &PointerOffsetTerm::Constant(8)
    ));
}

#[test]
fn mixed_pointer_queries_do_not_walk_growing_offset_classes() {
    for size in [8u64, 32, 128, 512] {
        let offset = |i| PointerOffsetTerm::Variable(Variable(940_000 + i));
        let x = at_offset(PointerBlock::ExternalArgument, offset(0));
        let y = at_offset(PointerBlock::ExternalArgument, offset(size));
        let z = at(symbolic(950_000), 0);
        let mut graph = EqualityGraph::default();
        let (_, construction) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 1..size {
                graph.add_offset_equality(&offset(i), &offset(i + 1));
            }
            graph.add_equality(&y, &z);
            graph.add_equality(&z, &Pointer::null());
        });
        assert!(
            construction < 128 * size as usize,
            "size={size}, work={construction}"
        );
        assert!(!graph.are_equal(&x, &Pointer::null()));
        let sibling = graph.clone();
        let mut branch = graph.clone();
        let (_, query) = crate::instrumentation::measure_deterministic_work(|| {
            branch.add_offset_equality(&offset(0), &offset(1));
            assert!(branch.are_equal(&x, &Pointer::null()));
            assert!(branch.are_equal(&Pointer::null(), &x));
        });
        assert!(query < 128, "size={size}, work={query}");
        assert!(!graph.are_equal(&x, &Pointer::null()));
        assert!(!sibling.are_equal(&x, &Pointer::null()));
    }
}

#[test]
fn constant_displacement_queries_ignore_unrelated_class_members() {
    for size in [16u64, 64, 256, 1024] {
        let a = symbolic(40_000);
        let b = symbolic(40_001);
        let x = PointerOffsetTerm::Variable(Variable(11_070));
        let y = PointerOffsetTerm::Variable(Variable(11_071));
        let mut graph = EqualityGraph::default();
        graph.add_equality(&at(a.clone(), 0), &at(b.clone(), 8));
        for i in 1..size {
            graph.add_equality(&at(symbolic(40_000 + i), 0), &at(symbolic(40_001 + i), 0));
        }
        graph.add_offset_equality(
            &PointerOffsetTerm::add(x.clone(), PointerOffsetTerm::Constant(8)),
            &y,
        );
        let left = at_offset(a, x);
        let right = at_offset(symbolic(40_000 + size), y);
        let (equal, work) =
            crate::instrumentation::measure_deterministic_work(|| graph.are_equal(&left, &right));
        assert!(equal);
        assert!(work < 96, "size={size}, work={work}");
        let (equal, map_work) =
            crate::persistent::measure_persistent_work(|| graph.are_equal(&left, &right));
        assert!(equal);
        assert!(
            map_work < 96 * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn same_block_pointer_queries_scale_with_registered_offset_classes() {
    for size in [16u64, 64, 256, 1024] {
        let base = symbolic(11_020);
        let mut graph = EqualityGraph::default();
        for id in 0..size {
            graph.add_int32_equality(&index(id), &index(id + 1));
        }
        let first = at_offset(base.clone(), PointerOffsetTerm::scale_int32(index(0), 4));
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            for id in 1..=size {
                let other = at_offset(base.clone(), PointerOffsetTerm::scale_int32(index(id), 4));
                assert!(graph.are_equal(&first, &other));
            }
        });
        assert!(work < 200 * size as usize, "size={size}, work={work}");
    }
}

#[test]
fn local_slot_alias_lookup_skips_unrelated_opaque_class_members() {
    let mut work = Vec::new();
    for size in [4u64, 16, 64] {
        let mut graph = EqualityGraph::default();
        let base = at(PointerBlock::ExternalArgument, 0);
        for id in 0..size {
            graph.add_equality(&base, &at(symbolic(10_000 + id), 0));
        }
        for name in ["local:first", "local:second", "global:other"] {
            graph.add_equality(&base, &at(name.into(), 8));
        }
        for query in [base.clone(), at("local:first".into(), 12)] {
            let mut expected = graph
                .pointer_spellings(&query)
                .into_iter()
                .map(|pointer| pointer.block)
                .filter(|block| block.starts_with("local:"))
                .collect::<Vec<_>>();
            let (mut actual, units) = crate::instrumentation::measure_deterministic_work(|| {
                graph.local_slot_alias_blocks(&query)
            });
            expected.sort();
            actual.sort();
            assert_eq!(actual, expected);
            if query == base {
                work.push(units);
            }
        }
    }
    assert!(work.iter().all(|units| *units <= work[0] + 64), "{work:?}");
}

// A displaced-pointer goal must discover its typed read dependencies without
// needing an earlier full-pointer query. A late address equality invalidates
// earlier misses.
#[test]
fn offset_queries_retain_typed_read_definitions_and_keep_blocks_distinct() {
    let memory = crate::kernel::intern_memory(Memory::new());
    let p = at(symbolic(919_001), 0);
    let q = at(symbolic(919_002), 0);
    let variable = |address: &Pointer| {
        crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            address,
            crate::kernel::LoadKind::Int32,
            8,
            &memory,
        )
    };
    let xv = variable(&p);
    let yv = variable(&q);
    let x = Pointer::loaded(&MachineTerm::Variable(xv)).unwrap();
    let y = Pointer::loaded(&MachineTerm::Variable(yv)).unwrap();
    // A typed read is named by its defining state and address, not by
    // its storage block or a scaled offset.
    for (value, address) in [(&x, &p), (&y, &q)] {
        let read = value.as_loaded_value().expect("a typed pointer read");
        assert_eq!(&read.defining_address, address);
        assert_eq!(read.defining_memory.arena_id(), memory.arena_id());
        assert_eq!(read.displacement, PointerOffsetTerm::Constant(0));
    }
    let mut graph = EqualityGraph::default();
    let sibling = graph.clone();
    // Warm displaced-query misses before the address equality arrives. The
    // late equality must invalidate them.
    for _ in 0..2 {
        assert!(!graph.are_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8)));
    }
    graph.add_equality(&p, &q);
    // Ask about a displaced pointer before any undisplaced query.
    assert!(graph.are_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8)));
    assert!(graph.are_equal(&x, &y));
    assert!(!graph.are_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(16)));
    assert!(!sibling.are_equal(&x, &y));
    assert!(!sibling.are_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8)));
    // A scalar-indexed address beside the same load is not the read.
    assert!(!graph.are_equal(
        &x,
        &Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(yv), 4),
        }
    ));
    // New unrelated definitions must not make rediscovery visit more than
    // these two selected operands.
    for size in [16u64, 64, 256, 1024] {
        for i in 0..size {
            let address = at(symbolic(920_000 + i), 0);
            let value = Pointer::loaded_value(&memory, &address);
            graph.register_pointer_read_definition(&value, &memory, &address);
        }
        let ((equal, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                graph.are_equal(&x.offset_by_bytes(16), &y.offset_by_bytes(16))
            })
        });
        assert!(equal);
        assert!(work < 200, "size={size}, work={work}");
        assert!(
            map_work < 512 * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
    // The read's displacement does not transfer to unrelated blocks.
    assert!(!graph.are_equal(
        &at_offset(symbolic(919_003), x.offset_by_bytes(8).offset),
        &at_offset(symbolic(919_004), y.offset_by_bytes(8).offset)
    ));
}

/// Load congruence for one query visits only the classed loads of the
/// queried load's own state: the work is the same beside 16 or 256
/// classed loads read from other states.
#[test]
fn load_congruence_work_ignores_classed_loads_of_other_states() {
    let name = |memory: &crate::kernel::SharedMemory, address: Pointer| {
        PointerBlock::Symbolic(crate::kernel::load_variable_for_cell_with_origin(
            memory,
            &address,
            crate::kernel::LoadKind::Int32,
            8,
            memory,
        ))
    };
    let mut costs = Vec::new();
    for unrelated in [16u64, 64, 256] {
        let mut classes = EqualityGraph::default();
        for index in 0..unrelated {
            let memory = crate::kernel::intern_memory(
                crate::kernel::Memory::new()
                    .with_block(symbolic(70_000 + index), 16)
                    .store(
                        at(symbolic(70_000 + index), 0),
                        ProgramValue::Int32(MachineTerm::constant(index as u32)),
                    ),
            );
            let loaded = name(&memory, at(symbolic(70_000 + index), 0));
            classes.add_equality(&at(loaded, 0), &at(symbolic(80_000 + index), 0));
        }
        let memory = crate::kernel::intern_memory(
            crate::kernel::Memory::new().with_block(symbolic(90_000), 16),
        );
        classes.add_equality(&at(symbolic(90_001), 0), &at(symbolic(90_002), 0));
        let left = name(&memory, at(symbolic(90_001), 0));
        let right = name(&memory, at(symbolic(90_002), 0));
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            classes.are_equal(&at(left.clone(), 8), &at(right.clone(), 8))
        });
        assert!(equal);
        costs.push(work);
    }
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn same_state_load_queries_ignore_unrelated_applications() {
    let memory = crate::kernel::intern_memory(Memory::new().with_block(symbolic(501), 16));
    let p = at(symbolic(502), 0);
    let q = at(symbolic(503), 0);
    let left = named_load(&memory, &p);
    let right = named_load(&memory, &q);
    let mut costs = Vec::new();
    for size in [16, 64, 256, 1024] {
        let mut classes = EqualityGraph::default();
        for i in 0..size {
            let load = named_load(&memory, &at(symbolic(100_000 + i), 0));
            classes.add_equality(&load, &at(symbolic(200_000 + i), 0));
        }
        classes.add_equality(&p, &q);
        let (equal, work) =
            crate::instrumentation::measure_deterministic_work(|| classes.are_equal(&left, &right));
        assert!(equal);
        costs.push(work);
        let (equal, map_work) =
            crate::persistent::measure_persistent_work(|| classes.are_equal(&left, &right));
        assert!(equal);
        assert!(
            map_work < 32 * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn late_merges_and_repeated_queries_have_near_linear_total_work() {
    let memory = crate::kernel::intern_memory(Memory::new().with_block(symbolic(601), 16));
    for size in [16u64, 64, 256, 1024] {
        let left = at(symbolic(602), 0);
        let right = at(symbolic(603), 0);
        let mut classes = EqualityGraph::default();
        let mut pairs = Vec::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                let a = named_load(&memory, &at(left.block.clone(), i as i64 * 8));
                let b = named_load(&memory, &at(right.block.clone(), i as i64 * 8));
                assert!(!classes.are_equal(&a, &b));
                pairs.push((a, b));
            }
            classes.add_equality(&left, &right);
            for (a, b) in &pairs {
                assert!(classes.are_equal(a, b));
            }
        });
        assert!(
            work <= 128 * size as usize,
            "size={size}, total work={work}"
        );
    }
}

#[test]
#[ignore = "nightly: 1.0s in the parallel gate"]
fn late_typed_load_merges_scale_with_existing_storage_relative_bridges() {
    let memory = crate::kernel::intern_memory(Memory::new());
    let mut costs = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut graph = EqualityGraph::default();
        let mut pairs = Vec::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                let p = at(symbolic(810_000 + i), 0);
                let q = at(symbolic(820_000 + i), 0);
                let old_value = |address: &Pointer| {
                    Pointer::loaded(&MachineTerm::Variable(
                        crate::kernel::load_variable_for_cell_with_origin(
                            &memory,
                            address,
                            crate::kernel::LoadKind::Int32,
                            8,
                            &memory,
                        ),
                    ))
                    .unwrap()
                };
                let left = old_value(&p);
                let right = old_value(&q);
                graph.add_equality(&left, &Pointer::loaded_value(&memory, &p));
                graph.add_equality(&right, &Pointer::loaded_value(&memory, &q));
                graph.add_equality(&p, &q);
                pairs.push((left, right));
            }
            for (left, right) in &pairs {
                assert!(graph.are_equal(left, right));
            }
        });
        costs.push(work);
    }
    // Read applications now include complete address terms. Check growth
    // across sizes rather than the old affine-only operation constant.
    assert!(
        costs.windows(2).all(|pair| pair[1] <= 5 * pair[0]),
        "{costs:?}"
    );
}

#[test]
fn branch_merges_do_not_reindex_the_large_shared_prefix() {
    let memory = crate::kernel::intern_memory(Memory::new().with_block(symbolic(701), 16));
    let root = at(symbolic(702), 0);
    let mut costs = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut trunk = EqualityGraph::default();
        for i in 0..size {
            let load = named_load(&memory, &at(root.block.clone(), i as i64 * 8));
            trunk.add_equality(&load, &at(symbolic(300_000 + i), 0));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..16 {
                let mut branch = trunk.clone();
                let alias = at(symbolic(400_000 + i), 0);
                branch.add_equality(&root, &alias);
                assert!(branch.are_equal(&root, &alias));
            }
        });
        costs.push(work);
    }
    assert!(costs.windows(2).all(|pair| pair[0] == pair[1]), "{costs:?}");
}

#[test]
fn separation_equality_query_uses_offset_classes_without_walking_aliases() {
    for size in [16u64, 64, 256, 1024] {
        let offset = |i| PointerOffsetTerm::Variable(Variable(500_000 + i));
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::pointer_offset_equal(offset(i), offset(i + 1)),
                true,
            );
        }
        let left = at_offset(symbolic(499_999), offset(0));
        let right = at_offset(symbolic(499_999), offset(size));
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.pointers_proven_equal_ignoring_memory_separation(&left, &right)
        });
        assert!(equal);
        assert!(work < 64, "size={size}, work={work}");
    }
}

#[test]
fn affine_input_normalization_is_linear_in_its_explicit_syntax() {
    for size in [16u64, 64, 256, 1024] {
        let mut input = PointerOffsetTerm::Constant(0);
        for i in 0..size {
            input = PointerOffsetTerm::Add(
                Box::new(input),
                Box::new(PointerOffsetTerm::Variable(Variable(900_000 + i))),
            );
        }
        let (form, work) = crate::instrumentation::measure_deterministic_work(|| {
            AffineOffset::of(&input).unwrap()
        });
        assert_eq!(form.terms.len(), size as usize);
        assert_eq!(work, 2 * size as usize + 1);
    }
}

/// Relabelling work along a chain of `n` equalities is `O(n log n)`:
/// union by size moves each block at most `log2 n` times. Joining two
/// balanced halves repeatedly is the worst case for relabelling.
#[test]
fn relabelling_work_is_n_log_n_across_sizes() {
    for exponent in [6u32, 8, 10, 12] {
        let n = 1u64 << exponent;
        let (classes, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut classes = EqualityGraph::default();
            let mut width = 1;
            while width < n {
                let mut start = 0;
                while start + width < n {
                    classes.add_equality(&at(symbolic(start), 0), &at(symbolic(start + width), 0));
                    start += 2 * width;
                }
                width *= 2;
            }
            classes
        });
        assert!(classes.are_equal(&at(symbolic(0), 0), &at(symbolic(n - 1), 0)));
        let bound = 16 * n * u64::from(exponent);
        assert!(
            work as u64 <= bound,
            "n = {n}: relabelled {work} blocks, above 16 n log2 n = {bound}"
        );
        // Balanced joins move a whole class each time, so the charge for
        // the moved members beyond the first is visible, not constant.
        assert!(work as u64 >= n / 2, "n = {n}: only {work} units charged");
    }
}

#[test]
fn shifted_raw_read_dependency_lookup_ignores_unrelated_definitions() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(Memory::new());
        let mut graph = EqualityGraph::default();
        for item in 0..size {
            let address = Pointer::symbolic(Variable(1_200_000 + item));
            let _ = memory
                .memory()
                .symbolic_pointer_load(&address, ProgramType::Int32Pointer);
            graph.add_equality(
                &Pointer::symbolic(Variable(1_300_000 + item)),
                &Pointer::symbolic(Variable(1_400_000 + item)),
            );
        }
        let address = Pointer::symbolic(Variable(1_500_000));
        let model = Pointer::symbolic(Variable(1_500_001));
        let ProgramValue::Pointer(raw) = memory
            .memory()
            .symbolic_pointer_load(&address, ProgramType::Int32Pointer)
        else {
            panic!("typed pointer read");
        };
        graph.add_equality(&Pointer::loaded_value(&memory, &address), &model);
        let read = |pointer: &Pointer| {
            MachineTerm::Variable(crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                pointer,
                crate::kernel::LoadKind::Int32,
                4,
            ))
        };
        let source = read(&raw.pointer().offset_by_bytes(24));
        let target = read(&model.offset_by_bytes(24));
        let expected = MachineTerm::constant(7);
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            graph.add_int32_equality(&source, &expected);
            graph.are_int32_equal(&target, &expected)
        });
        assert!(equal);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn pointer_fact_source_order_queries_ignore_unrelated_admissions() {
    let mut observed = Vec::new();
    for size in [16, 64, 256, 1024] {
        let graph = EqualityGraph::default();
        let mut target = None;
        for id in 0..size {
            let domain = crate::kernel::PointerValue::new(
                Pointer::symbolic(Variable(9_000_000 + id)),
                crate::kernel::ProgramType::Int32Pointer,
            );
            let fact = std::sync::Arc::new(crate::kernel::ExecutionPureFact::certified(
                domain
                    .opaque_coverage_fact(&crate::kernel::MemoryRange::new(
                        at(symbolic(987_100 + id), 0),
                        MachineTerm::constant(0),
                        MachineTerm::constant(1),
                    ))
                    .expect("coverage names the opaque domain"),
            ));
            graph.adjust_pointer_fact(&fact, true);
            if id == 0 {
                target = Some((domain.opaque_extent().unwrap().clone(), fact));
            }
        }
        let (origin, fact) = target.unwrap();
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            let fork = graph.clone();
            assert_eq!(
                fork.subobject_coverage_facts(&origin),
                vec![fact.proposition().clone()]
            );
            fork.adjust_pointer_fact(&fact, false);
            assert!(fork.subobject_coverage_facts(&origin).is_empty());
            assert_eq!(
                graph.subobject_coverage_facts(&origin),
                vec![fact.proposition().clone()]
            );
        });
        observed.push(work);
    }
    assert!(observed[0] > 0);
    assert!(
        observed.iter().all(|work| *work == observed[0]),
        "{observed:?}"
    );
}

#[test]
fn self_named_wide_read_observations_register_once_across_metadata() {
    use crate::kernel::{LoadKind, Memory, ProgramValue, intern_memory};
    for size in [8_u64, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let graph = EqualityGraph::default();
        let mut reads = Vec::new();
        let ((), production) = crate::instrumentation::measure_deterministic_work(|| {
            for item in 0..size {
                let address = Pointer::symbolic(Variable(9_800_000 + item));
                let named = intern_memory(Memory::new().with_block(format!("word-{item}"), 8));
                let variable = crate::kernel::load_variable_for_cell_with_origin(
                    &named,
                    &address,
                    LoadKind::Bits64,
                    8,
                    &named,
                );
                let value = MachineTerm::Variable(variable);
                let observed = intern_memory(
                    named
                        .memory()
                        .clone()
                        .with_block(format!("temporary-{item}"), 4)
                        .materialize_named_cell(
                            address.clone(),
                            ProgramValue::UInt64(value.clone()),
                        ),
                );
                assert_eq!(named.read_identity(), observed.read_identity());
                crate::kernel::eval::begin_load_origin_epoch();
                assert_eq!(
                    variable,
                    crate::kernel::load_variable_for_cell_with_origin(
                        &named,
                        &address,
                        LoadKind::Bits64,
                        8,
                        &observed,
                    )
                );
                assert!(!graph.are_uint64_equal(&value, &MachineTerm::uint64_constant(0)));
                // A genuinely different observation of the same read must
                // still be processed by an already populated graph.
                let resolved = intern_memory(named.memory().clone().materialize_named_cell(
                    address.clone(),
                    ProgramValue::UInt64(MachineTerm::uint64_constant(17)),
                ));
                crate::kernel::eval::begin_load_origin_epoch();
                assert_eq!(
                    variable,
                    crate::kernel::load_variable_for_cell_with_origin(
                        &named,
                        &address,
                        LoadKind::Bits64,
                        8,
                        &resolved,
                    )
                );
                assert!(graph.are_uint64_equal(&value, &MachineTerm::uint64_constant(17)));
                assert!(!graph.are_uint64_equal(&value, &MachineTerm::uint64_constant(0)));
                reads.push(value);
            }
        });
        let ((), queries) = crate::instrumentation::measure_deterministic_work(|| {
            for read in reads {
                assert!(!graph.are_uint64_equal(&read, &MachineTerm::uint64_constant(0)));
            }
        });
        assert!(production < 500 * size as usize, "{size}: {production}");
        assert!(queries < 50 * size as usize, "{size}: {queries}");
    }
}
