// Scaling tests of `src/kernel/tests/memory_dag_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

/// The justification the step rule gives for crossing `edge`'s own derivation
/// with a `bytes`-wide read at `pointer`, which the edge must not write.
fn seeded_edge_justification(
    edge: &SharedMemory,
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) -> MemoryDagHopJustification {
    let derivation = edge.derivation().expect("a seeded edge");
    let crate::kernel::resource_tracker::step_effect::StepEffect::Separate(
        crate::kernel::resource_tracker::step_effect::Separation::Cell(justification),
    ) = crate::kernel::resource_tracker::step_effect::affects(
        &derivation,
        edge,
        crate::kernel::resource_tracker::TrackedResource::Cell {
            pointer,
            bytes: crate::kernel::AccessExtent::from(bytes),
        },
        &crate::kernel::resource_tracker::step_effect::Evidence {
            assumptions,
            cross_loop_havoc: false,
        },
    )
    else {
        panic!("the seeded edge is separate from the read");
    };
    assert!(justification.checks(&derivation, pointer, bytes, assumptions));
    justification
}

#[test]
fn rewritten_store_witness_work_scales_with_explicit_adjacent_equalities() {
    crate::kernel::eval::declare_load_access_width(&arc_pointer(4), 4);
    let mut samples = Vec::new();
    for size in [1, 2, 4, 8] {
        let value = MachineTerm::constant(17);
        let mut memory = SymbolicMemory::new()
            .with_block("arg-memory", 128)
            .store(arc_pointer(4), ProgramValue::Int32(value.clone()));
        let load = |memory: &SymbolicMemory| {
            MachineTerm::read_named(
                ProgramPoint::at(&(crate::kernel::intern_memory_ref(memory))),
                Box::new(arc_pointer(4)),
                crate::kernel::LoadKind::Int32,
            )
        };
        let assumptions = PureFactContext::new();
        let capture = CheckedLoadEqualityCapture::start();
        assert!(checked_stored_origin_equality(
            &value,
            &load(&memory),
            &assumptions
        ));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                let previous = load(&memory);
                memory = memory.with_block(format!("unrelated-{size}-{index}"), 4);
                assert!(checked_atomic_load_equality(
                    &load(&memory),
                    &previous,
                    &assumptions
                ));
            }
        });
        samples.push((size, work));
        let witnesses = capture.finish();
        assert_eq!(witnesses.len(), size + 1);
        assert!(witnesses.iter().all(|witness| witness.checks(&assumptions)));
    }
    assert!(
        samples
            .iter()
            .all(|(size, work)| *work <= samples[0].1 * size),
        "explicit selected edges: {samples:?}"
    );
}

#[test]
fn reinterning_retained_memory_uses_shallow_component_identity() {
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut memory = SymbolicMemory::new();
            for index in 0..size {
                memory = memory.with_block(format!("shallow-memory-{size}-{index}"), 4);
            }
            let first = crate::kernel::intern_memory_ref(&memory);
            let (second, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::intern_memory_ref(&memory)
            });
            assert_eq!(first.arena_id(), second.arena_id());
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.iter().all(|(_, work)| *work == 0),
        "reinterning retained memory should not hash its contents: {samples:?}"
    );
}

#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 1.6s in the parallel gate"]
fn checked_order_store_crossing_ignores_unrelated_order_facts() {
    let samples = [4_u64, 16, 64, 256, 1024]
        .into_iter()
        .map(|size| {
            let index = MachineTerm::Variable(Variable(92_000_000 + size * 10 + 1));
            let length = MachineTerm::Variable(Variable(92_000_000 + size * 10 + 2));
            let written = symbolic_element_pointer(&index);
            let kept = symbolic_element_pointer(&length);
            let mut context = PureFactContext::new();
            for unrelated in 0..size {
                context = context.assume_condition(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(Variable(93_000_000 + unrelated * 2)),
                        MachineTerm::Variable(Variable(93_000_000 + unrelated * 2 + 1)),
                    ),
                    true,
                );
            }
            let context =
                context.assume_condition(ConditionTerm::signed_less_than(index, length), true);
            let base = SymbolicMemory::new().with_block(format!("arg-memory-{size}"), 64);
            let separated = base.clone().store_with_context(written, int32(7), &context);
            let load = |memory: &SymbolicMemory| {
                MachineTerm::read_named(
                    ProgramPoint::at(&(crate::kernel::intern_memory_ref(memory))),
                    Box::new(kept.clone()),
                    crate::kernel::LoadKind::Int32,
                )
            };
            let (resolved, work) = crate::instrumentation::measure_deterministic_work(|| {
                with_extended_dag_bridging(|| {
                    atomic_memory_load_equality_evidence(&load(&separated), &load(&base), &context)
                })
            });
            assert!(
                resolved.is_some(),
                "the store must be crossed at size {size}"
            );
            (size, work)
        })
        .collect::<Vec<_>>();
    let first = samples[0].1;
    assert!(
        samples
            .iter()
            .all(|(_, work)| *work <= first.saturating_mul(4).max(first + 64)),
        "crossing a store by its frozen order must not scale with unrelated facts: {samples:?}"
    );
}

/// The derivation walk has no hop cap: a load of an untouched cell is
/// framed across any number of stores to other cells, and the walk's work
/// grows with the chain's length.
#[test]
fn memory_dag_walks_follow_chains_of_any_length() {
    let samples = [32, 64, 128, 256]
        .into_iter()
        .map(|size| {
            let entry = SymbolicMemory::new().with_block("arg-memory", 4096);
            let mut memory = entry.clone();
            for index in 0..size {
                memory = memory.store(
                    arc_pointer(8 + 4 * index),
                    ProgramValue::Int32(MachineTerm::constant(index as u32)),
                );
            }
            let read = arc_pointer(0);
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                checked_memory_load_equality(&entry, &memory, &read, &PureFactContext::new())
            });
            assert!(equal, "the cell is untouched across {size} stores");
            (size, work)
        })
        .collect::<Vec<_>>();
    let (small, large) = (samples[0].1.max(1), samples[3].1);
    assert!(
        large <= small * 16,
        "the walk's work should grow linearly with the chain: {samples:?}"
    );
}

#[test]
fn seeded_pointer_read_evidence_does_not_enumerate_large_runs_or_alias_classes() {
    for size in [16u32, 64, 256, 1024] {
        let base = Address::symbolic(Variable(98_320));
        let address = base.offset_by_bytes((size - 2) * 4);
        let alias = Address::symbolic(Variable(98_321));
        let old = intern_memory(SymbolicMemory::new());
        let current = intern_memory(
            old.memory()
                .clone()
                .store(base.offset_by_bytes(size * 4 + 16), int32(1))
                .with_seeded_cells(base, 4, ProgramType::Int32, 0, size, old.clone()),
        );
        let (mut context, left, right) =
            seeded_pointer_read_context(&old, &current, &address, &alias);
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::address_equal(
                    address.clone(),
                    Address::symbolic(Variable(99_000 + u64::from(i))),
                ),
                true,
            );
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.register_pointer_read(&right, &current, &address);
        });
        assert!(context.pointers_known_equal(&left, &right));
        assert!(work < 500, "size={size}, work={work}");
    }
}

#[test]
fn pointer_read_source_registration_does_not_walk_growing_store_histories() {
    for size in [8u32, 32, 128, 512] {
        let address = Address::symbolic(Variable(98_340));
        let old = intern_memory(SymbolicMemory::new());
        let mut memory = old.memory().clone().with_seeded_cells(
            address.clone(),
            4,
            ProgramType::Int32,
            0,
            2,
            old.clone(),
        );
        let context = PureFactContext::new();
        for i in 0..size {
            memory = memory.store(address.offset_by_bytes(16), int32(i));
        }
        let current = intern_memory(memory);
        let left = Address::loaded_value(&old, &address);
        let right = Address::loaded_value(&current, &address);
        context.register_pointer_read(&left, &old, &address);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.register_pointer_read(&right, &current, &address);
        });
        assert!(!context.pointers_known_equal(&left, &right));
        assert!(work < 100, "size={size}, work={work}");
    }
}

#[test]
fn pointer_read_single_store_edges_compose_with_near_linear_work() {
    let mut previous_work = None;
    for size in [2u32, 8, 32, 128] {
        let address = Address::symbolic(Variable(98_390));
        let mut memory = intern_memory(SymbolicMemory::new());
        let context = PureFactContext::new();
        let original = Address::loaded_value(&memory, &address);
        context.register_pointer_read(&original, &memory, &address);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..size {
                memory = intern_memory(
                    memory
                        .memory()
                        .clone()
                        .store(address.offset_by_bytes(16), int32(i)),
                );
                let value = Address::loaded_value(&memory, &address);
                context.register_pointer_read(&value, &memory, &address);
                assert!(context.pointers_known_equal(&original, &value));
            }
        });
        assert!(work < 200 * size as usize, "size={size}, work={work}");
        if let Some(previous) = previous_work {
            assert!(
                work <= 5 * previous,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous_work = Some(work);
    }
}

#[test]
fn pointer_read_cache_forgetting_registration_does_not_search_older_history() {
    for size in [8u32, 32, 128, 512] {
        let address = arc_pointer(0);
        let mut memory = SymbolicMemory::new().with_block("arg-memory", 32);
        let original = intern_memory(memory.clone());
        for i in 0..size {
            memory = memory.store(
                address.clone(),
                ProgramValue::Int64(MachineTerm::int64_constant(i as i64)),
            );
        }
        let before = intern_memory(memory.clone());
        let context = PureFactContext::new();
        let forgotten = intern_memory(memory.without_possible_aliasing_cells(
            &address.offset_by_bytes(4),
            1,
            &context,
        ));
        let old_read = Address::loaded_value(&original, &address);
        let before_read = Address::loaded_value(&before, &address);
        let after_read = Address::loaded_value(&forgotten, &address);
        context.register_pointer_read(&old_read, &original, &address);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.register_pointer_read(&after_read, &forgotten, &address);
        });
        assert!(context.pointers_known_equal(&before_read, &after_read));
        assert!(!context.pointers_known_equal(&old_read, &after_read));
        assert!(work < 100, "size={size}, work={work}");
    }
}

#[test]
fn read_identity_production_is_linear_and_endpoint_queries_do_not_walk_history() {
    let mut previous_work = None;
    for size in [8u32, 32, 128, 512] {
        let address = Address::symbolic(Variable(98_440));
        let unknown = Address::symbolic(Variable(98_441));
        let original = intern_memory(SymbolicMemory::new());
        let mut memory = original.memory().clone();
        let context = PureFactContext::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for index in 0..size {
                memory = memory
                    .clone()
                    .with_seeded_cells(
                        address.clone(),
                        4,
                        ProgramType::Int32,
                        0,
                        2,
                        original.clone(),
                    )
                    .without_possible_aliasing_cells(&unknown, 4, &context)
                    .with_block(format!("local:read-metadata-{index}"), 4)
                    .with_initialized_object(&address.offset_by_bytes(index * 8), 8);
            }
        });
        let current = intern_memory(memory);
        assert_eq!(current.read_identity(), original.read_identity());
        let (_, query_work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(context.pointers_known_equal(
                &Address::loaded_value(&original, &address),
                &Address::loaded_value(&current, &address),
            ));
        });
        assert!(query_work < 100, "size={size}, query_work={query_work}");
        assert!(work < 500 * size as usize, "size={size}, work={work}");
        if let Some(previous) = previous_work {
            assert!(
                work <= 5 * previous,
                "size={size}, work={work}, previous={previous}"
            );
        }
        previous_work = Some(work);
    }
}

#[test]
fn named_state_alias_equality_does_not_depend_on_sibling_observation_origins() {
    let mut samples = Vec::new();
    for unrelated in [16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let left = Address::symbolic(Variable(977_110));
        let middle = Address::symbolic(Variable(977_111));
        let right = Address::symbolic(Variable(977_112));
        let first = ConditionTerm::address_equal(left.clone(), middle.clone());
        let second = ConditionTerm::address_equal(middle, right.clone());
        let mut assumptions = PureFactContext::new()
            .assume_condition(first.clone(), true)
            .assume_condition(second.clone(), true);
        for index in 0..unrelated {
            assumptions = assumptions.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(978_100 + index)),
                    MachineTerm::constant(index as u32),
                ),
                true,
            );
        }
        let named = crate::kernel::intern_memory(SymbolicMemory::new());
        let origins = ["local:first-arm", "local:second-arm"]
            .map(|block| crate::kernel::intern_memory(SymbolicMemory::new().with_block(block, 4)));
        let variables = [(&left, &origins[0]), (&right, &origins[1])].map(|(pointer, origin)| {
            crate::kernel::eval::load_variable_for_cell_with_origin(
                &named,
                pointer,
                LoadKind::Int32,
                4,
                origin,
            )
        });
        let [left_load, right_load] = variables.map(MachineTerm::Variable);
        let (witness, work) = crate::instrumentation::measure_deterministic_work(|| {
            let capture = CheckedLoadEqualityCapture::start();
            assert!(checked_origin_load_equality(
                &left_load,
                &right_load,
                &assumptions
            ));
            let witnesses = capture.finish();
            let [witness] = witnesses.as_slice() else {
                panic!("expected one named-state alias witness");
            };
            assert!(witness.checks(&assumptions));
            witness.clone()
        });
        // Each link alone is outside the measurement of the selected check.
        for remaining in [first.clone(), second.clone()] {
            let partial = PureFactContext::new().assume_condition(remaining, true);
            assert!(!witness.checks(&partial));
        }
        // The witness names the exact state, address, and read kind.
        let changed = crate::kernel::intern_memory(
            SymbolicMemory::new().with_block("local:different-retained_state", 4),
        );
        for retargeted in [
            MachineTerm::read_named(
                ProgramPoint::at(&changed),
                Box::new(right.clone()),
                LoadKind::Int32,
            ),
            MachineTerm::read_named(
                ProgramPoint::at(&named),
                Box::new(right.offset_by_bytes(4)),
                LoadKind::Int32,
            ),
            MachineTerm::read_named(
                ProgramPoint::at(&named),
                Box::new(right.clone()),
                LoadKind::UInt8,
            ),
        ] {
            assert!(!witness.checks_retargeted_for_test(
                left_load.clone(),
                retargeted,
                &assumptions,
                &crate::kernel::proof::CheckedCallEvents::default(),
            ));
        }
        // Widening a registered read must invalidate the retained 4-byte rule.
        crate::kernel::eval::load_variable_for_cell_with_origin(
            &named,
            &right,
            LoadKind::Int32,
            8,
            &origins[1],
        );
        assert!(!witness.checks(&assumptions));
        assert!(!checked_origin_load_equality(
            &left_load,
            &right_load,
            &assumptions
        ));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 16),
        "{samples:?}"
    );
}

#[test]
fn kept_range_lookup_follows_exact_aliases_without_scanning_unrelated_members() {
    let input = |name| Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(name)), 4),
    };
    let base = input(979_000);
    let model_base = Address {
        base: AddressBase::Symbolic(Variable(979_001)),
        offset: AddressOffset::Constant(0),
    };
    let alias = ConditionTerm::address_equal(base.clone(), model_base.clone());
    let assumptions = PureFactContext::new().assume_condition(alias.clone(), true);
    let field = memory_range(model_base, 2, 4);
    let pointer = base.offset_by_bytes(8);
    let mut previous = None;
    for count in [16, 64, 256, 1024] {
        let mut ranges =
            ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(field.clone()));
        for index in 0..count {
            ranges = ranges.unchecked_with_fact(ResourceFact::own_memory(memory_range(
                input(980_000 + index),
                0,
                2,
            )));
        }
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            assumptions.kept_range_holding_access(&ranges, || None, &pointer, 8)
        });
        assert_eq!(found, Some(&field));
        if let Some(previous) = previous {
            assert!(
                work <= previous + 32,
                "{count} unrelated members: {work} after {previous}"
            );
        }
        previous = Some(work);
    }
    let ranges = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(field));
    for (pointer, bytes) in [
        (pointer.clone(), 12),
        (base.offset_by_bytes(12), 8),
        (base.offset_by_bytes(4), 8),
    ] {
        assert!(
            assumptions
                .kept_range_holding_access(&ranges, || None, &pointer, bytes)
                .is_none()
        );
    }
    assert!(
        PureFactContext::new()
            .kept_range_holding_access(&ranges, || None, &pointer, 8)
            .is_none()
    );
}

/// A materialized run writes back its own source loads. Framing an unknown
/// address across it must not enumerate the run or require a disjointness fact.
#[test]
fn seeded_scalar_loads_frame_unknown_cells_with_constant_work() {
    let anchor = Address::symbolic(Variable(98_470));
    let other = Address::symbolic(Variable(98_471));
    let assumptions = PureFactContext::new();
    for (element_type, width) in [
        (ProgramType::Int32, 4),
        (ProgramType::Int32Pointer, 8),
        (ProgramType::Int32Pointer, 16),
    ] {
        let mut previous_work = None;
        for size in [16, 256, 4096, 65536] {
            let original = intern_memory(SymbolicMemory::new());
            let first = intern_memory(original.memory().clone().with_seeded_cells(
                anchor.clone(),
                width,
                element_type,
                0,
                size,
                original.clone(),
            ));
            let current = intern_memory(first.memory().clone().with_seeded_cells(
                anchor.offset_by_bytes(size * width),
                width,
                element_type,
                0,
                size,
                original.clone(),
            ));
            let (cell, work) = crate::instrumentation::measure_deterministic_work(|| {
                memory_dag_cell_source(&current, &other, 4, &assumptions, false).unwrap()
            });
            let MemoryDagCell::Unwritten { node, path } = cell else {
                panic!("naming must not invent a stored value for the other address");
            };
            assert_eq!(node, first);
            // Each explicit query crosses one cache-only edge.
            assert!(matches!(
                path.as_slice(),
                [hop] if hop.justification == MemoryDagHopJustification::SeededLoadsOfBase
            ));
            let earlier = memory_dag_cell_source(&first, &other, 4, &assumptions, false).unwrap();
            assert_eq!(earlier.node(), &original);
            for edge in [&current, &first] {
                assert_eq!(
                    seeded_edge_justification(edge, &other, 4, &assumptions),
                    MemoryDagHopJustification::SeededLoadsOfBase
                );
            }
            assert!(work < 100, "size={size}, work={work}");
            // Run length does not change the cost of one selected edge.
            if let Some(previous) = previous_work {
                assert!(
                    work <= previous,
                    "framing work must not grow with the run: size={size}: {work} > {previous}"
                );
            }
            previous_work.get_or_insert(work);
        }
    }
}

/// Narrow scalar observations can overlap a complete pointer read. A
/// full-width read must cross those no-write edges without reading the last
/// partial slot as a write. The witness stays constant-size as the run grows.
#[test]
fn seeded_scalar_slots_preserve_overlapping_wide_reads() {
    let pointer = Address::symbolic(Variable(98_490));
    let assumptions = PureFactContext::new();
    let mut previous_work = None;
    for (count, stride) in [2, 16, 256, 4096]
        .into_iter()
        .flat_map(|count| [4, 8].map(|stride| (count, stride)))
    {
        let original = intern_memory(SymbolicMemory::new());
        let current = intern_memory(original.memory().clone().with_seeded_cells(
            pointer.clone(),
            stride,
            ProgramType::Int32,
            0,
            count,
            original.clone(),
        ));
        let (cell, work) = crate::instrumentation::measure_deterministic_work(|| {
            memory_dag_cell_source(&current, &pointer, 8, &assumptions, false).unwrap()
        });
        let MemoryDagCell::Unwritten { node, path } = cell else {
            panic!("partial scalar cache slots cannot supply a whole pointer");
        };
        assert_eq!(node, original);
        assert!(matches!(
            path.as_slice(),
            [hop] if hop.justification == MemoryDagHopJustification::SeededLoadsOfBase
        ));
        assert_eq!(
            seeded_edge_justification(&current, &pointer, 8, &assumptions),
            MemoryDagHopJustification::SeededLoadsOfBase
        );
        assert!(work < 100, "count={count}, work={work}");
        // Run length does not change the cost of one selected edge.
        if let Some(previous) = previous_work {
            assert!(work <= previous, "count={count}: {work} > {previous}");
        }
        previous_work.get_or_insert(work);

        // A real four-byte overwrite of the pointer's upper half must still
        // stop the wide read, even after the resulting bytes are cached.
        let changed = intern_memory(
            original
                .memory()
                .clone()
                .store(pointer.offset_by_bytes(4), int32(7)),
        );
        let cached = intern_memory(changed.memory().clone().with_seeded_cells(
            pointer.clone(),
            stride,
            ProgramType::Int32,
            0,
            count,
            changed.clone(),
        ));
        let (cell, stop) =
            memory_dag_cell_source_with_stop(&cached, &pointer, 8, &assumptions, false).unwrap();
        assert_eq!(cell.node(), &changed);
        assert_eq!(stop, CellWalkStop::NotShownSeparate);
        let (cell, stop) =
            memory_dag_cell_source_with_stop(&changed, &pointer, 8, &assumptions, false).unwrap();
        assert_eq!(cell.node(), &changed);
        assert_eq!(stop, CellWalkStop::Affected);
    }
}

/// A base-pointer alias applies to the same field offset. The exact-store
/// predicate must use that indexed equality without scanning unrelated facts
/// or accepting a different field, partial store, or an unproved alias.
#[test]
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn stored_field_value_uses_indexed_base_aliases() {
    use crate::kernel::resource_tracker::cell_source::write_supplies_read;
    use crate::kernel::resource_tracker::step_effect::write_is_at_read_address;
    let _session = crate::kernel::VerificationSession::enter();
    let left = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(105_001)), 4),
    };
    let right = Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(105_002)), 4),
    };
    let write = left.offset_by_bytes(16);
    let read = right.offset_by_bytes(16);
    let stored = ProgramValue::typed_pointer(
        Address::symbolic(Variable(105_003)),
        ProgramType::Int32Pointer,
    );
    let bare = PureFactContext::new();
    assert!(!write_is_at_read_address(&write, &read, &bare));
    let mut samples = Vec::new();
    for count in [16u64, 64, 256] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_condition(
                ConditionTerm::address_equal(
                    Address::symbolic(Variable(110_000 + index * 2)),
                    Address::symbolic(Variable(110_001 + index * 2)),
                ),
                true,
            );
        }
        context = context.assume_condition(
            ConditionTerm::address_equal(left.clone(), right.clone()),
            true,
        );
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            write_is_at_read_address(&write, &read, &context)
        });
        assert!(equal);
        samples.push(work);
        assert!(write_supplies_read(&write, &stored, &read, 8, &context));
        assert!(!write_is_at_read_address(
            &write,
            &read.offset_by_bytes(4),
            &context
        ));
        assert!(!write_supplies_read(&write, &stored, &read, 4, &context));
        assert!(!write_supplies_read(
            &write,
            &ProgramValue::Int32(MachineTerm::constant(0)),
            &read,
            8,
            &context
        ));
    }
    assert!(samples[2] <= samples[0] * 4 + 32, "{samples:?}");
}

/// A transitive base alias must frame a different pointer field without an
/// alias scan. The retained hop must refuse missing aliases and every partial
/// overlap, including a later check made with a wider read.
#[test]
fn aliased_store_byte_frame_checks_width_context_and_scales() {
    use crate::kernel::resource_tracker::TrackedResource;
    use crate::kernel::resource_tracker::cell_source::MemoryDagHopJustification;
    use crate::kernel::resource_tracker::step_effect::{Evidence, Separation, StepEffect, affects};
    let _session = crate::kernel::VerificationSession::enter();
    let base = |id| Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(id)), 4),
    };
    let left = base(106_001);
    let right = base(106_002);
    let bridge = Address::symbolic(Variable(106_003));
    let read = right.offset_by_bytes(16);
    let value = ProgramValue::typed_pointer(
        Address::symbolic(Variable(106_004)),
        ProgramType::Int32Pointer,
    );
    let memory = intern_memory(SymbolicMemory::new());
    let classify = |write: Address, bytes, context: &PureFactContext| {
        let step = MemoryDerivation::Store {
            base: memory.clone(),
            pointer: write,
            value: value.clone().into(),
        };
        let result = affects(
            &step,
            &memory,
            TrackedResource::Cell {
                pointer: &read,
                bytes,
            },
            &Evidence {
                assumptions: context,
                cross_loop_havoc: false,
            },
        );
        (step, result)
    };
    let mut samples = Vec::new();
    for count in [4u64, 16, 64, 256] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_condition(
                ConditionTerm::address_equal(
                    Address::symbolic(Variable(120_000 + index * 2)),
                    Address::symbolic(Variable(120_001 + index * 2)),
                ),
                true,
            );
        }
        context = context
            .assume_condition(
                ConditionTerm::address_equal(left.clone(), bridge.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::address_equal(bridge.clone(), right.clone()),
                true,
            );
        let ((step, result), work) = crate::instrumentation::measure_deterministic_work(|| {
            classify(
                left.offset_by_bytes(8),
                crate::kernel::AccessExtent::from(8),
                &context,
            )
        });
        samples.push(work);
        let StepEffect::Separate(Separation::Cell(
            hop @ MemoryDagHopJustification::StoreAliasedByteSeparation { .. },
        )) = result
        else {
            panic!("expected checked aliased byte separation: {result:?}");
        };
        assert!(hop.checks(&step, &read, 8, &context));
        assert!(!hop.checks(&step, &read, 8, &PureFactContext::new()));
        // The same certificate cannot be moved onto a different store or a
        // read wide enough to reach a store on its other side.
        for offset in [12, 16, 20] {
            let (changed, effect) = classify(
                left.offset_by_bytes(offset),
                crate::kernel::AccessExtent::from(8),
                &context,
            );
            assert!(
                !matches!(effect, StepEffect::Separate(_)),
                "overlap at {offset}"
            );
            assert!(!hop.checks(&changed, &read, 8, &context));
        }
        let (after, effect) = classify(
            left.offset_by_bytes(24),
            crate::kernel::AccessExtent::from(8),
            &context,
        );
        let StepEffect::Separate(Separation::Cell(after_hop)) = effect else {
            panic!("the adjacent field is separate");
        };
        assert!(after_hop.checks(&after, &read, 8, &context));
        assert!(!after_hop.checks(&after, &read, 12, &context));
        let (_, bare_effect) = classify(
            left.offset_by_bytes(8),
            crate::kernel::AccessExtent::from(8),
            &PureFactContext::new(),
        );
        assert!(!matches!(bare_effect, StepEffect::Separate(_)));
    }
    assert!(samples[3] <= samples[0] * 4 + 32, "{samples:?}");
    {
        let costs = samples.clone();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 64);
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
#[cfg(not(feature = "fast-gate"))]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn graph_aliased_range_membership_checks_complete_access_and_scales() {
    // A named call can leave a store's pointer connected to the selected
    // range by two equalities. Check that local graph evidence frames the
    // complete access without enumerating unrelated aliases.
    use crate::kernel::memory_history::typed_store_separated_ranges_evidence;
    let _session = crate::kernel::VerificationSession::enter();
    let base = |id| Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::scale_int32(MachineTerm::Variable(Variable(id)), 4),
    };
    let write_base = base(160_001);
    let write_model = base(160_002);
    let read_base = base(160_003);
    let read_model = base(160_004);
    let write_bridge = Address::symbolic(Variable(160_005));
    let read_bridge = Address::symbolic(Variable(160_006));
    let write = write_base.offset_by_bytes(8);
    let read = read_base.offset_by_bytes(8);
    let range = |base: &Address, end| {
        MemoryRange::new_with_element_width(
            base.clone(),
            MachineTerm::constant(8),
            MachineTerm::constant(end),
            1,
        )
    };
    let separation = |end| Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(range(&write_model, end))),
        right: Box::new(Resource::Memory(range(&read_model, end))),
    };
    let aliases = [
        ConditionTerm::address_equal(write_base.clone(), write_bridge.clone()),
        ConditionTerm::address_equal(write_bridge, write_model.clone()),
        ConditionTerm::address_equal(read_base.clone(), read_bridge.clone()),
        ConditionTerm::address_equal(read_bridge, read_model.clone()),
    ];
    let step = MemoryDerivation::Store {
        base: intern_memory(SymbolicMemory::new()),
        pointer: write.clone(),
        value: ProgramValue::typed_pointer(
            Address::symbolic(Variable(160_007)),
            ProgramType::Int32Pointer,
        )
        .into(),
    };
    let mut samples = Vec::new();
    for count in [16u64, 64, 256, 1024] {
        let mut context = PureFactContext::new();
        for index in 0..count {
            context = context.assume_condition(
                ConditionTerm::address_equal(base(170_000 + index * 2), base(170_001 + index * 2)),
                true,
            );
        }
        for alias in &aliases {
            context = context.assume_condition(alias.clone(), true);
        }
        let no_separation = context.clone();
        context = context.assume_proposition(separation(16));
        let (witness, work) = crate::instrumentation::measure_deterministic_work(|| {
            let witness = typed_store_separated_ranges_evidence(&write, 8, &read, 8, &context)
                .expect("the graph aligns both accesses to the selected ranges");
            assert!(witness.checks(&step, &read, 8, &context));
            witness
        });
        samples.push(work);
        // Scale the producer and checker at every size. The invalid
        // certificates are independent of unrelated context size.
        if count != 16 {
            continue;
        }
        assert!(!witness.checks(&step, &read, 8, &no_separation));
        for absent in &aliases {
            let missing = aliases
                .iter()
                .filter(|alias| *alias != absent)
                .fold(PureFactContext::new(), |missing, alias| {
                    missing.assume_condition(alias.clone(), true)
                })
                .assume_proposition(separation(16));
            assert!(!witness.checks(&step, &read, 8, &missing));
            assert!(typed_store_separated_ranges_evidence(&write, 8, &read, 8, &missing).is_none());
        }
        assert!(!witness.checks(&step, &read, 9, &context));
        assert!(typed_store_separated_ranges_evidence(&write, 9, &read, 8, &context).is_none());
        assert!(typed_store_separated_ranges_evidence(&write, 8, &read, 9, &context).is_none());
        let partial = no_separation.assume_proposition(separation(12));
        assert!(typed_store_separated_ranges_evidence(&write, 8, &read, 8, &partial).is_none());
        let overlapping = context.assume_condition(
            ConditionTerm::address_equal(write_model.clone(), read_model.clone()),
            true,
        );
        assert!(!witness.checks(&step, &read, 8, &overlapping));
        assert!(typed_store_separated_ranges_evidence(&write, 8, &read, 8, &overlapping).is_none());
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] * 2 + 64),
        "{samples:?}"
    );
}

#[test]
fn local_lifetime_end_retains_complete_separated_range_evidence_and_scales() {
    let mut costs = Vec::new();
    for count in [16u32, 64, 256] {
        crate::kernel::eval::clear_load_variable_registry();
        let retired = SymbolicMemory::frame_local_pointer(u64::from(count), "span");
        let read = Address::symbolic(Variable(140_000 + u64::from(count)));
        let bytes = |base, end| MemoryRange::new_with_element_width(base, 0u32.into(), end, 1);
        let retired_range = bytes(retired.clone(), 16u32.into());
        let read_range = bytes(read.clone(), 8u32.into());
        let mut memory = SymbolicMemory::new()
            .with_block(retired.base.clone(), 16)
            .with_block(read.base.clone(), 16);
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(retired_range.clone()))
            .unchecked_with_fact(ResourceFact::own_memory(read_range.clone()));
        for index in 0..count {
            let other =
                SymbolicMemory::frame_local_pointer(u64::from(count + index + 1), "unrelated");
            memory = memory.with_block(other.base.clone(), 16);
            resources =
                resources.unchecked_with_fact(ResourceFact::own_memory(bytes(other, 16u32.into())));
        }
        let assumptions =
            PureFactContext::new().assume_proposition(Proposition::ResourceComposition(resources));
        crate::kernel::eval::declare_load_access_width(&read, 8);
        let before = crate::kernel::intern_memory_ref(&memory);
        let after = crate::kernel::intern_memory_ref(&memory.without_local_block(&retired.base));
        let load = |memory| {
            MachineTerm::read_named(
                memory,
                Box::new(read.clone()),
                crate::kernel::LoadKind::Int32,
            )
        };
        // Measure this selected cleanup edge's decision and certificate check,
        // excluding the pre-existing walks through the fixture's declarations.
        let (effect, cost) = crate::instrumentation::measure_deterministic_work(|| {
            with_extended_dag_bridging(|| {
                use crate::kernel::resource_tracker::step_effect;
                let effect = step_effect::affects(
                    after.derivation().unwrap().as_ref(),
                    &after,
                    crate::kernel::resource_tracker::TrackedResource::Cell {
                        pointer: &read,
                        bytes: crate::kernel::AccessExtent::from(8),
                    },
                    &step_effect::Evidence {
                        assumptions: &assumptions,
                        cross_loop_havoc: true,
                    },
                );
                if let step_effect::StepEffect::Separate(step_effect::Separation::Cell(hop)) =
                    &effect
                {
                    assert!(hop.checks(
                        after.derivation().unwrap().as_ref(),
                        &read,
                        8,
                        &assumptions
                    ));
                } else {
                    panic!("expected a checked cell separation: {effect:?}");
                }
                effect
            })
        });
        assert!(matches!(
            effect,
            crate::kernel::resource_tracker::step_effect::StepEffect::Separate(_)
        ));
        let capture = CheckedLoadEqualityCapture::start();
        let equal = checked_atomic_load_equality(
            &load(ProgramPoint::at(&after)),
            &load(ProgramPoint::at(&before)),
            &assumptions,
        );
        assert!(
            equal,
            "a separated caller pointer survives private-object cleanup"
        );
        costs.push(cost);
        let equalities = capture.finish();
        let [equality] = equalities.as_slice() else {
            panic!("expected one equality: {equalities:?}");
        };
        assert!(equality.checks(&assumptions));
        assert!(!equality.checks(&PureFactContext::new()));
        let Some(AtomicMemoryLoadEqualityEvidence::SameCell(evidence)) =
            equality.memory_dag_evidence_for_test()
        else {
            panic!("expected typed DAG evidence");
        };
        let hop = &retained_memory_dag_path(&evidence.left)[0];
        assert!(matches!(
            hop.justification,
            MemoryDagHopJustification::LocalLifetimeEndedSeparatedRanges { .. }
        ));
        assert!(
            hop.justification
                .checks(hop.derivation.as_ref(), &read, 8, &assumptions)
        );
        assert!(
            !hop.justification
                .checks(hop.derivation.as_ref(), &read, 16, &assumptions)
        );
        assert!(
            !hop.justification
                .checks(hop.derivation.as_ref(), &retired, 8, &assumptions)
        );
        let larger = SymbolicMemory::new().with_block(retired.base.clone(), 32);
        let larger_end =
            crate::kernel::intern_memory_ref(&larger.without_local_block(&retired.base));
        assert!(!hop.justification.checks(
            larger_end.derivation().unwrap().as_ref(),
            &read,
            8,
            &assumptions
        ));
        for (retired_bytes, read_bytes) in [(8u32, 8u32), (16, 4)] {
            let partial = ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own_memory(bytes(
                    retired.clone(),
                    retired_bytes.into(),
                )))
                .unchecked_with_fact(ResourceFact::own_memory(bytes(
                    read.clone(),
                    read_bytes.into(),
                )));
            let partial = PureFactContext::new()
                .assume_proposition(Proposition::ResourceComposition(partial));
            assert!(!checked_atomic_load_equality(
                &load(ProgramPoint::at(&after)),
                &load(ProgramPoint::at(&before)),
                &partial
            ));
        }
        assert!(!checked_atomic_load_equality(
            &load(ProgramPoint::at(&after)),
            &load(ProgramPoint::at(&before)),
            &PureFactContext::new()
        ));
    }
    assert!(
        costs.iter().all(|cost| *cost <= 250),
        "indexed lifetime separation grew with unrelated members: {costs:?}"
    );
}

#[test]
fn preliminary_byte_gap_uses_only_stated_endpoint_order() {
    use crate::kernel::reasoning::memory_resolution::{AccessByteOverlap, access_byte_overlap};
    let _session = crate::kernel::VerificationSession::enter();
    let memory = crate::kernel::intern_memory_ref(&SymbolicMemory::new());
    let index = |slot: i64| {
        MachineTerm::read_named(
            ProgramPoint::at(&memory),
            Box::new(Address {
                base: "byte-gap-index".into(),
                offset: AddressOffset::Constant(slot * 4),
            }),
            crate::kernel::LoadKind::Int32,
        )
    };
    let middle = index(2);
    let left_index = index(0);
    let right_index = index(1);
    let at = |index: &MachineTerm| Address {
        base: "byte-gap-data".into(),
        offset: AddressOffset::scale_int32(index.clone(), 4),
    };
    let left = at(&left_index);
    let right = at(&right_index);
    let order = ConditionTerm::signed_less_than(left_index.clone(), right_index.clone());
    let mut baseline_work = None;
    for size in [0u64, 16, 64, 256] {
        let mut context = PureFactContext::new();
        for extra in 0..size {
            context = context.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(97_400 + extra)),
                    (extra as u32).into(),
                ),
                true,
            );
        }
        let ordered = context.clone().assume_condition(order.clone(), true);
        let reversed = context.clone().assume_condition(order.clone(), false);
        let first_edge = Proposition::condition_is(
            ConditionTerm::signed_less_than(left_index.clone(), middle.clone()),
            true,
        );
        let second_edge = Proposition::condition_is(
            ConditionTerm::signed_less_equal(middle.clone(), right_index.clone()),
            true,
        );
        let chained = context
            .clone()
            .assume_proposition(first_edge)
            .assume_proposition(second_edge.clone());
        let broken = context.clone().assume_proposition(second_edge);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                access_byte_overlap(&left, 4, &right, 8, &context),
                AccessByteOverlap::Unknown
            );
            assert_eq!(
                access_byte_overlap(&left, 4, &right, 8, &ordered),
                AccessByteOverlap::Separate
            );
            // The eight-byte access is now below the four-byte one: a single
            // element gap cannot guarantee that its upper half is disjoint.
            assert_eq!(
                access_byte_overlap(&left, 8, &right, 4, &ordered),
                AccessByteOverlap::Unknown
            );
            assert_eq!(
                access_byte_overlap(&right, 8, &left, 4, &ordered),
                AccessByteOverlap::Separate
            );
            assert_eq!(
                access_byte_overlap(&left, 4, &right, 8, &reversed),
                AccessByteOverlap::Unknown
            );
            assert_eq!(
                access_byte_overlap(&left, 4, &right, 8, &chained),
                AccessByteOverlap::Unknown
            );
            assert_eq!(
                access_byte_overlap(&left, 4, &right, 8, &broken),
                AccessByteOverlap::Unknown
            );
        });
        let baseline = *baseline_work.get_or_insert(work);
        assert!(
            work <= baseline + 8 && work <= 256,
            "unrelated order context caused {work} work at size {size} (baseline {baseline})"
        );
    }
}

#[test]
fn indexed_byte_separation_ignores_unrelated_external_ranges() {
    let pointer = |id| Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Variable(Variable(id)),
    };
    let separate = |p, q| Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(memory_range(p, 0, 2))),
        right: Box::new(Resource::Memory(memory_range(q, 0, 2))),
    };
    let p = pointer(970_121);
    let q = pointer(970_122);
    let mut previous = None;
    for size in [16, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context
                .assume_proposition(separate(pointer(980_000 + 2 * i), pointer(980_001 + 2 * i)));
        }
        context = context.assume_proposition(separate(p.clone(), q.clone()));
        let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_history::indexed_store_byte_separation_evidence(
                &q, 8, &p, 8, &context,
            )
        });
        assert!(proof.is_some());
        if let Some(previous) = previous {
            assert_eq!(work, previous, "unrelated ranges at {size}");
        }
        previous = Some(work);
    }
}

#[test]
fn numeric_byte_geometry_ignores_unrelated_address_classes() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = |id| Address {
        base: AddressBase::ExternalArgument,
        offset: AddressOffset::Variable(Variable(id)),
    };
    let numeric_alias = |p: Address, q: Address| {
        Proposition::condition_is(
            ConditionTerm::uint64_equal(
                MachineTerm::integer_address(p),
                MachineTerm::integer_address(q),
            ),
            true,
        )
    };
    let p = pointer(970_131);
    let q = pointer(970_132);
    let mut previous = None;
    for size in [16, 64, 256] {
        let mut context = PureFactContext::new();
        for i in 0..size {
            context = context.assume_proposition(numeric_alias(
                pointer(990_000 + 2 * i),
                pointer(990_001 + 2 * i).offset_by_bytes(8),
            ));
        }
        context = context.assume_proposition(numeric_alias(q.clone(), p.offset_by_bytes(8)));
        let (proof, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_history::indexed_store_byte_separation_evidence(
                &q, 8, &p, 8, &context,
            )
        });
        assert!(proof.is_some());
        if let Some(previous) = previous {
            assert_eq!(work, previous, "unrelated address classes at {size}");
        }
        previous = Some(work);
    }
}

/// A frame containing views or folded resources but no flat owner cannot
/// retain a cell through this flat-range lookup. Do not first resolve the
/// queried pointer's read history to discover the empty owner index.
#[test]
fn an_unrelated_view_does_not_walk_pointer_read_history() {
    let mut samples = Vec::new();
    for size in [4u32, 8, 16, 32] {
        let _session = crate::kernel::VerificationSession::enter();
        let context = PureFactContext::new();
        let field = Address {
            base: AddressBase::ExternalArgument,
            offset: AddressOffset::Constant(0),
        };
        let target = Address::symbolic(Variable(995_600));
        let mut memory = SymbolicMemory::new().store(
            field.clone(),
            ProgramValue::typed_pointer(target, ProgramType::Int32Pointer),
        );
        for index in 0..size {
            memory = memory.store(
                SymbolicMemory::local_pointer("empty-frame-counter").offset_by_bytes(index * 4),
                ProgramValue::Int32(index.into()),
            );
        }
        let retained_state = crate::kernel::intern_memory_ref(&memory);
        let variable = crate::kernel::load_variable_for_cell_with_origin(
            &retained_state,
            &field,
            LoadKind::Int32,
            C_POINTER_BYTE_WIDTH,
            &retained_state,
        );
        let pointer = Address::loaded(&MachineTerm::Variable(variable)).unwrap();
        context.register_pointer_read(&pointer, &retained_state, &field);
        let ranges = ResourceContext::new_with_equalities(&context)
            .unchecked_with_fact(ResourceFact::view_memory(memory_range(field, 0, 2)));
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.kept_read_range_holding_access(&ranges, || None, &pointer, 4)
        });
        assert!(found.is_none());
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= 16),
        "an unrelated view walks the read history: {samples:?}"
    );
}

#[test]
fn mixed_width_seeded_runs_ignore_other_address_stems() {
    for bytes_first in [false, true] {
        let mut baseline = None;
        for length in [32, 1_024, 65_536, 2_147_483_647] {
            let _session = crate::kernel::VerificationSession::enter();
            let address = |variable| Address {
                base: AddressBase::ExternalArgument,
                offset: AddressOffset::Variable(Variable(variable)),
            };
            let word = address(98_750);
            let bytes = address(98_751);
            assert_eq!(word.base, bytes.base);
            let source = intern_memory(SymbolicMemory::new());
            let (memory, work) = crate::instrumentation::measure_deterministic_work(|| {
                let seed_word = |memory: SymbolicMemory| {
                    memory.with_seeded_cells(
                        word.clone(),
                        8,
                        ProgramType::UInt64,
                        0,
                        1,
                        source.clone(),
                    )
                };
                let seed_bytes = |memory: SymbolicMemory| {
                    memory.with_seeded_cells(
                        bytes.clone(),
                        1,
                        ProgramType::UInt8,
                        0,
                        length,
                        source.clone(),
                    )
                };
                let memory = if bytes_first {
                    seed_word(seed_bytes(SymbolicMemory::new()))
                } else {
                    seed_bytes(seed_word(SymbolicMemory::new()))
                };
                // A repeated entry projection must not enumerate the other run either.
                seed_word(memory)
            });
            assert_eq!(
                work,
                *baseline.get_or_insert(work),
                "length {length}, bytes first {bytes_first}: entry work must not depend on numeric length"
            );
            assert_eq!(memory.cells.representation_len(), 2);
        }
    }
}
#[test]
fn direct_pointer_projection_dependencies_scale_with_the_selected_chain() {
    let mut samples = Vec::new();
    for size in [8, 16, 32, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = intern_memory(
            SymbolicMemory::new().with_block_without_derivation("local:projection-chain", 4),
        );
        let mut left = Address::symbolic(Variable(98_370));
        let mut right = Address::symbolic(Variable(98_371));
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::address_equal(left.clone(), right.clone()),
            true,
        );
        for _ in 0..size {
            let projected = crate::kernel::memory_history::canonical_value_load_memory(
                &source,
                &left,
                crate::kernel::C_POINTER_BYTE_WIDTH,
            );
            left = Address::loaded_value(&projected, &left);
            right = Address::loaded_value(&source, &right);
        }
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.pointers_known_equal(&left, &right)
        });
        assert!(equal);
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 3 + 64,
            "projection dependencies repeated selected work: {samples:?}"
        );
    }
    let mut unrelated_samples = Vec::new();
    for size in [0, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = intern_memory(
            SymbolicMemory::new().with_block_without_derivation("local:projection-frame", 4),
        );
        for i in 0..size {
            let address = Address::symbolic(Variable(99_000 + i));
            let projected = crate::kernel::memory_history::canonical_value_load_memory(
                &source,
                &address,
                crate::kernel::C_POINTER_BYTE_WIDTH,
            );
            Address::loaded_value(&projected, &address);
        }
        let address = Address::symbolic(Variable(98_380));
        let projected = crate::kernel::memory_history::canonical_value_load_memory(
            &source,
            &address,
            crate::kernel::C_POINTER_BYTE_WIDTH,
        );
        let left = Address::loaded_value(&projected, &address);
        let right = Address::loaded_value(&source, &address);
        let context = PureFactContext::new();
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.pointers_known_equal(&left, &right)
        });
        assert!(equal);
        unrelated_samples.push(work);
    }
    assert!(
        unrelated_samples
            .iter()
            .all(|work| *work <= unrelated_samples[0] + 64),
        "projection lookup visited unrelated definitions: {unrelated_samples:?}"
    );
}

#[test]
fn abstract_read_congruence_scales_with_selected_reads() {
    let parameter = TypeParameterName::intern("ScaledReadT");
    let memory = intern_memory(SymbolicMemory::new());
    let read = |pointer: Address| AlgebraicTerm {
        algebraic_type: parameter.algebraic_type(),
        node: AlgebraicTermNode::MemoryLoad {
            point: crate::kernel::ProgramPoint::at(&memory.clone()),
            pointer: Box::new(pointer),
        },
    };
    let measure = |size: u64, ambient: u64| {
        let mut context = PureFactContext::new();
        for i in 0..ambient {
            context = context.assume_condition(
                ConditionTerm::address_equal(
                    Address::symbolic(Variable(995_000 + 2 * i)),
                    Address::symbolic(Variable(995_001 + 2 * i)),
                ),
                true,
            );
        }
        let anchor = Address::symbolic(Variable(994_000));
        let first = read(anchor.clone());
        crate::instrumentation::measure_deterministic_work(|| {
            for i in 1..=size {
                let alias = Address::symbolic(Variable(994_000 + i));
                let next = read(alias.clone());
                assert!(!context.equality_graph.are_algebraic_equal(&first, &next));
                context = context
                    .assume_condition(ConditionTerm::address_equal(anchor.clone(), alias), true);
                assert!(context.equality_graph.are_algebraic_equal(&first, &next));
            }
        })
        .1
    };
    let samples: Vec<_> = [8, 16, 32, 64]
        .into_iter()
        .map(|size| measure(size, 0))
        .collect();
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= 2 * pair[0] + 128,
            "abstract read congruence revisited prior aliases: {samples:?}"
        );
    }
    let unrelated: Vec<_> = [0, 16, 64, 256]
        .into_iter()
        .map(|size| measure(8, size))
        .collect();
    assert!(
        unrelated.iter().all(|work| *work <= unrelated[0] + 128),
        "abstract read congruence scanned unrelated facts: {unrelated:?}"
    );
}

#[test]
fn abstract_read_origin_lookup_ignores_unrelated_definitions() {
    let mut samples = Vec::new();
    for size in [0, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = intern_memory(
            SymbolicMemory::new().with_block_without_derivation("local:abstract-origin-scaling", 4),
        );
        let parameter = TypeParameterName::intern("ScaledOriginT");
        for i in 0..size {
            AlgebraicTermNode::parameter_load(
                source.clone(),
                Address::symbolic(Variable(993_000 + i)),
                parameter,
            );
        }
        let address = Address::symbolic(Variable(992_000));
        let ProgramValue::Parameter(named) =
            AlgebraicTermNode::parameter_load(source.clone(), address.clone(), parameter)
        else {
            unreachable!()
        };
        let observed = AlgebraicTerm {
            algebraic_type: parameter.algebraic_type(),
            node: AlgebraicTermNode::MemoryLoad {
                point: crate::kernel::ProgramPoint::at(&source),
                pointer: Box::new(address),
            },
        };
        let context = PureFactContext::new();
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            context
                .equality_graph
                .are_algebraic_equal(&named, &observed)
        });
        assert!(equal);
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "origin lookup visited unrelated producer definitions: {samples:?}"
    );
}
