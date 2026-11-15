// Scaling tests of `src/kernel/primitives/memory_equality_index.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;
use crate::kernel::{MachineCastSpelling, MachineTerm};

/// The selection charges the same work beside 2, 4, 8 and 16 unrelated
/// framed ranges as beside 1,024 (1,118 units at 16 to 1,024 on
/// 2026-10-15), so an ambient scan shows as growth at these sizes; the
/// larger sizes cost seconds of setup in a debug build, nearly all of it in
/// `synchronize_memory_equalities` over the unrelated ranges.
#[test]
fn checked_read_endpoint_selects_framed_ranges_without_ambient_scan() {
    let mut samples = Vec::new();
    for size in [2u32, 4, 8, 16] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = Memory::new();
        let read = |context: &PureFactContext, memory: &Memory, address: &Pointer| {
            let retained_state = crate::kernel::intern_memory_ref(memory);
            let variable = crate::kernel::load_variable_for_cell_with_origin(
                &retained_state,
                address,
                LoadKind::Int32,
                C_POINTER_BYTE_WIDTH,
                &retained_state,
            );
            let pointer = Pointer::loaded(&MachineTerm::Variable(variable)).unwrap();
            context.register_pointer_read(&pointer, &retained_state, address);
            pointer
        };
        let source = read(&PureFactContext::new(), &before, &field);
        // Match the contract's complete pointer-valued descriptor cell.
        // Its unknown value is retained as the initial opaque read.
        let before = before.store(
            field.clone(),
            ProgramValue::Pointer(PointerValue::new(source.clone(), ProgramType::Int32Pointer)),
        );
        let count = MachineTerm::Variable(Variable(999_321));
        let range = |base| MemoryRange::new_with_element_width(base, 0u32.into(), count.clone(), 4);
        let field_range =
            MemoryRange::new_with_element_width(field.clone(), 0u32.into(), 2u32.into(), 4);
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(field_range.clone())),
            right: Box::new(Resource::Memory(range(source.clone()))),
        };
        let bounded = PureFactContext::new()
            .assume_condition(
                ConditionTerm::signed_less_equal(2u32.into(), count.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(count.clone(), 1000u32.into()),
                true,
            );
        let context = bounded.clone().assume_proposition(separation);
        let held = ResourceFact::own_memory(range(source.clone()));
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(ResourceFact::view_memory(field_range))
            .unchecked_with_fact(held.clone());
        for index in 0..size {
            let unrelated = read(&context, &before, &field.offset_by_bytes(64 + index * 8));
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(range(unrelated)));
        }
        resources.synchronize_memory_equalities(&context);
        let local = Pointer {
            block: PointerBlock::Concrete("local:frame-counter".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let after = before
            .clone()
            .with_block(local.block.clone(), 4)
            .store(source.offset_by_bytes(4), ProgramValue::Int32(7u32.into()))
            .store(local, ProgramValue::Int32(8u32.into()));
        let current = read(&context, &after, &field);
        let required = ResourceFact::own_memory(range(current.clone()));
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources
                .directly_supporting_fact(&required, &context)
                .cloned()
        });
        assert_eq!(found, Some(held.clone()), "size={size}, work={work}");
        assert!(work < 2000, "size={size}, work={work}");
        samples.push(work);
        assert_eq!(
            crate::kernel::memory_provenance::checked_pointer_read_endpoint(&current, &context),
            Some(source.clone()),
            "the complete-cell certificate must recover this exact stored value",
        );
        assert!(!context.equality_graph.are_equal(&source, &current));
        assert!(
            resources
                .clone()
                .without_fact_incrementally(&required, &context)
                .is_some()
        );
        assert!(
            resources
                .directly_supporting_fact(&required, &bounded)
                .is_none()
        );
        let withdrawn = resources
            .clone()
            .without_exact_representation(&held)
            .unwrap();
        assert!(
            withdrawn
                .directly_supporting_fact(&required, &context)
                .is_none()
        );
        let partial = after.store(field.offset_by_bytes(4), ProgramValue::Int32(9u32.into()));
        let changed = ResourceFact::own_memory(range(read(&context, &partial, &field)));
        assert!(
            resources
                .directly_supporting_fact(&changed, &context)
                .is_none()
        );
        assert!(
            resources
                .without_fact_incrementally(&changed, &context)
                .is_none()
        );
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "the checked read's selection read unrelated framed ranges: {samples:?}"
    );
}

#[test]
fn wide_read_keeps_full_buffer_index_beside_a_batch_cursor() {
    let mut samples = Vec::new();
    for count in [0_u64, 4, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(989_200)), 1),
        };
        let prefix = MachineTerm::Variable(Variable(989_201));
        let local = MachineTerm::Variable(Variable(989_202));
        let full = MachineTerm::Variable(Variable(989_203));
        let batch = Pointer::symbolic(Variable(989_204));
        let query = Pointer::symbolic(Variable(989_205));
        let global = base.offset_by_typed_elements(full.clone(), 1, true, true);
        let mut aliases = PureFactContext::new()
            .assume_condition(
                ConditionTerm::pointer_equal(
                    batch.clone(),
                    base.offset_by_typed_elements(prefix, 1, true, true),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::pointer_equal(
                    query.clone(),
                    batch.offset_by_elements(MachineTerm::Variable(Variable(989_206)), 1),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::pointer_equal(
                    query.clone(),
                    batch.offset_by_typed_elements(local, 1, true, true),
                ),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(query.clone(), global), true);
        for i in 0..count {
            aliases = aliases.assume_condition(
                ConditionTerm::pointer_equal(
                    query.clone(),
                    batch.offset_by_elements(MachineTerm::Variable(Variable(990_000 + i)), 1),
                ),
                true,
            );
        }
        let facts = aliases.clone().assume_condition(
            ConditionTerm::uint64_less_than(full.clone(), MachineTerm::uint64_constant(22208)),
            true,
        );
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(
            MemoryRange::new_wide(
                base.clone(),
                MachineTerm::uint64_constant(0),
                MachineTerm::uint64_constant(22208),
                1,
            ),
        ));
        resources.synchronize_memory_equalities(&facts);
        let (permitted, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.permits_memory_read(&query, 1, &facts)
        });
        assert!(
            permitted,
            "alignment: {:?}",
            resources.read_access(&query, 1, &facts).map(|c| c
                .source
                .index
                .graph
                .pointer_at_base_with_wide_index(&query, &base))
        );
        samples.push(work);
        assert!(!resources.permits_memory_read(&query, 2, &facts));
        assert!(!resources.permits_memory_read(&query, 1, &aliases));
        let boundary = aliases.assume_condition(
            ConditionTerm::uint64_equal(full, MachineTerm::uint64_constant(22208)),
            true,
        );
        assert!(!resources.permits_memory_read(&query, 1, &boundary));
        assert!(!ResourceContext::new().permits_memory_read(&query, 1, &facts));
    }
    assert!(
        samples[4] <= samples[1] * 3 + 128,
        "batch read alignment scanned aliases: {samples:?}"
    );
    {
        let costs = samples.clone();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 64);
        assert!(indexed(&costs), "indexed work: {costs:?}");
        let scanned = costs
            .iter()
            .zip([0u64, 4, 16, 64, 256])
            .map(|(work, size)| work + usize::try_from(size).unwrap())
            .collect::<Vec<_>>();
        assert!(
            !indexed(&scanned),
            "the smaller fixture must detect a visit per unrelated item: {costs:?}"
        );
    }
}

#[test]
fn wide_read_keeps_native_index_beside_a_narrow_alias() {
    let mut samples = Vec::new();
    for count in [16_u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let bytes = Pointer::symbolic(Variable(986_000));
        let alternate = Pointer::symbolic(Variable(986_001));
        let native_index = MachineTerm::Variable(Variable(986_002));
        let narrow = alternate.offset_by_elements(MachineTerm::Variable(Variable(986_003)), 1);
        let wide = bytes.offset_by_typed_elements(native_index.clone(), 1, true, true);
        let query = Pointer::symbolic(Variable(986_004));
        let mut facts = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(query.clone(), narrow), true)
            .assume_condition(ConditionTerm::pointer_equal(query.clone(), wide), true)
            .assume_condition(
                ConditionTerm::uint64_less_than(
                    native_index.clone(),
                    MachineTerm::uint64_constant(15),
                ),
                true,
            );
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(
            MemoryRange::new_wide(
                bytes,
                MachineTerm::uint64_constant(0),
                MachineTerm::uint64_constant(15),
                1,
            ),
        ));
        for item in 0..count {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(987_000 + item)),
                    query.clone(),
                ),
                true,
            );
        }
        resources.synchronize_memory_equalities(&facts);
        let (permitted, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.permits_memory_read(&query, 1, &facts)
        });
        assert!(
            permitted,
            "native bounds remain available beside a narrow alias"
        );
        assert!(!resources.permits_memory_read(&query, 2, &facts));
        assert!(!ResourceContext::new().permits_memory_read(&query, 1, &facts));
        samples.push(work);
    }
    assert!(
        samples[3] <= samples[0] * 3 + 128,
        "native read alignment scanned its address class: {samples:?}"
    );
}

#[test]
fn wide_cursor_advance_keeps_its_native_producer_beside_narrow_aliases() {
    let mut samples = Vec::new();
    for count in [4_u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let bytes = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(988_400)), 1),
        };
        let cursor = Pointer::symbolic(Variable(988_402));
        let remaining = MachineTerm::Variable(Variable(988_403));
        let advance = MachineTerm::Variable(Variable(988_404));
        let length = MachineTerm::Variable(Variable(988_410));
        let prefix = MachineTerm::Variable(Variable(988_411));
        let narrow = bytes.offset_by_elements(
            MachineTerm::subtract(
                MachineTerm::legacy_cast(
                    MachineCastSpelling::UInt32From64,
                    Box::new(prefix.clone()),
                ),
                MachineTerm::legacy_cast(
                    MachineCastSpelling::UInt32From64,
                    Box::new(remaining.clone()),
                ),
            ),
            1,
        );
        let wide = bytes.offset_by_typed_elements(
            MachineTerm::uint64_subtract(prefix.clone(), remaining.clone()),
            1,
            true,
            true,
        );
        let bytes_value = crate::kernel::PointerValue::new(
            bytes.clone(),
            crate::kernel::ProgramType::UInt8Pointer,
        );
        let cursor_value = crate::kernel::PointerValue::new(
            cursor.clone(),
            crate::kernel::ProgramType::UInt8Pointer,
        );
        let aliases = PureFactContext::new()
            .assume_condition(
                ConditionTerm::pointer_value_equal(
                    cursor_value.clone(),
                    bytes_value.clone().with_address(wide),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::pointer_value_equal(
                    cursor_value.clone(),
                    bytes_value.clone().with_address(narrow),
                ),
                true,
            );
        let mut facts = aliases
            .clone()
            .assume_condition(
                ConditionTerm::uint64_less_equal(prefix.clone(), length.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(remaining.clone(), prefix.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_equal(advance.clone(), MachineTerm::uint64_constant(22208)),
                true,
            )
            .assume_condition(
                ConditionTerm::uint64_less_equal(advance.clone(), remaining.clone()),
                true,
            );
        for value in [&length, &prefix, &remaining] {
            facts = facts.assume_condition(
                ConditionTerm::uint64_less_equal(
                    value.clone(),
                    MachineTerm::uint64_constant(i32::MAX as u64),
                ),
                true,
            );
        }
        for item in 0..count {
            facts = facts.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(989_000 + item)),
                    cursor.clone(),
                ),
                true,
            );
        }
        let resources = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(
            MemoryRange::new_wide(bytes.clone(), MachineTerm::uint64_constant(0), length, 1)
                .with_pointer_carrier(&bytes_value),
        ));
        resources.synchronize_memory_equalities(&facts);
        let query = cursor.offset_by_typed_elements(advance.clone(), 1, true, true);
        let permits = |resources: &ResourceContext,
                       query: &Pointer,
                       facts: &PureFactContext,
                       designation: (&Pointer, Option<&Pointer>)| {
            resources.permits_designated_pointer_position(query, &cursor, designation, facts)
        };
        let (permitted, work) = crate::instrumentation::measure_deterministic_work(|| {
            permits(
                &resources,
                &query,
                &facts,
                cursor_value.access_designation(),
            )
        });
        assert!(permitted, "the advancing cursor keeps its native bounds");
        assert!(!permits(
            &ResourceContext::new(),
            &query,
            &facts,
            cursor_value.access_designation()
        ));
        assert!(!permits(
            &resources,
            &query,
            &aliases,
            cursor_value.access_designation()
        ));
        assert!(!permits(
            &resources,
            &query,
            &facts,
            (
                &Pointer::symbolic(Variable(988_406)),
                cursor_value.opaque_extent()
            )
        ));
        assert!(!permits(
            &resources,
            &cursor.offset_by_typed_elements(
                MachineTerm::uint64_constant(1u64 << 32),
                1,
                true,
                true
            ),
            &facts,
            cursor_value.access_designation()
        ));
        assert!(!permits(
            &resources,
            &cursor.offset_by_typed_elements(advance, 2, true, true),
            &facts,
            cursor_value.access_designation()
        ));
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "advancing a native cursor scanned aliases: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 1.7s in the parallel gate"]
fn constant_base_interior_lookup_scales_with_selected_range() {
    let mut samples = Vec::new();
    for count in [16_u32, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let parent = Pointer::symbolic(Variable(950_000));
        let model = Pointer::symbolic(Variable(950_001));
        let parameter = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(950_002)), 4),
        };
        let old_read = Pointer {
            block: parent.block.clone(),
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(950_003)), 4),
        };
        let cursor = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(950_004)), 4),
        };
        let prefix = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(parameter, parent), true)
            .assume_condition(
                ConditionTerm::pointer_equal(old_read.clone(), model.clone()),
                true,
            );
        let resources = ResourceContext::new().unchecked_with_facts((0..count).map(|index| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                model.clone(),
                (index * 8 + 2).into(),
                (index * 8 + 6).into(),
                4,
            ))
        }));
        resources.synchronize_memory_equalities(&prefix);
        // A late base alias must update the indexed payload, not force a
        // search through all the other spans relative to that same base.
        let facts = prefix
            .clone()
            .assume_condition(ConditionTerm::pointer_equal(cursor.clone(), old_read), true)
            .assume_condition(ConditionTerm::pointer_equal(cursor.clone(), model), true);
        resources.synchronize_memory_equalities(&facts);
        let required = ResourceFact::own_memory(MemoryRange::new_with_element_width(
            cursor.clone(),
            4u32.into(),
            6u32.into(),
            4,
        ));
        let (remaining, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources
                .clone()
                .without_fact_incrementally(&required, &facts)
        });
        assert!(remaining.is_some());
        assert!(resources.permits_memory_read(&cursor.offset_by_bytes(16), 8, &facts));
        assert!(
            resources
                .clone()
                .without_fact_incrementally(&required, &prefix)
                .is_none()
        );
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 2),
        "interior lookup grew faster than indexed paths: {samples:?}"
    );
    assert!(
        samples[3] <= samples[0] * 3,
        "interior lookup followed unrelated same-base spans: {samples:?}"
    );
}

#[test]
#[ignore = "nightly: 2.4s in the parallel gate"]
fn modeled_pointer_alias_field_lookup_scales_with_selected_addresses() {
    let mut previous = None;
    for count in [4_u32, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let parent = Pointer::symbolic(Variable(940_000));
        let model = Pointer::symbolic(Variable(940_001));
        let parameter = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(940_002)), 4),
        };
        let old_read = Pointer {
            block: parent.block.clone(),
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(940_003)), 4),
        };
        let cursor = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(940_004)), 4),
        };
        let prefix = PureFactContext::new()
            .assume_condition(ConditionTerm::pointer_equal(parameter, parent), true)
            .assume_condition(
                ConditionTerm::pointer_equal(old_read.clone(), model.clone()),
                true,
            );
        let resources = ResourceContext::new().unchecked_with_facts((0..count).map(|index| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                old_read.offset_by_bytes(index * 16),
                0u32.into(),
                1u32.into(),
                8,
            ))
        }));
        resources.synchronize_memory_equalities(&prefix);
        // Publish the cursor alias after the suppliers. Only address
        // applications affected by this equality may be reindexed.
        let facts = prefix
            .clone()
            .assume_condition(
                ConditionTerm::pointer_equal(cursor.clone(), old_read.clone()),
                true,
            )
            .assume_condition(ConditionTerm::pointer_equal(cursor.clone(), model), true);
        resources.synchronize_memory_equalities(&facts);
        let (permitted, work) = crate::instrumentation::measure_deterministic_work(|| {
            resources.permits_memory_read(&cursor.offset_by_bytes(16), 8, &facts)
        });
        assert!(permitted);
        if let Some(previous) = previous {
            assert_eq!(
                work, previous,
                "selected-address work changed with {count} suppliers"
            );
        }
        previous = Some(work);
        assert!(!resources.permits_memory_read(&cursor.offset_by_bytes(16), 8, &prefix));
    }
}

#[test]
#[ignore = "nightly: 0.6s in the parallel gate"]
fn mixed_extent_read_hits_and_misses_do_not_scan_unrelated_ranges() {
    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024] {
        let base = Pointer::symbolic(Variable(851_030));
        let alias = Pointer::symbolic(Variable(851_031));
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(view(&base, 0, 4))
            .unchecked_with_fact(view(&base, 1, 2));
        for index in 1..=size {
            resources =
                resources.unchecked_with_fact(view(&base, index * 8, index * 8 + 1 + index % 2));
        }
        let empty = PureFactContext::new();
        resources.synchronize_memory_equalities(&empty);
        let facts = empty.assume_condition(ConditionTerm::pointer_equal(base, alias.clone()), true);
        resources.synchronize_memory_equalities(&facts);
        let at = |offset| Pointer {
            block: alias.block.clone(),
            offset: PointerOffsetTerm::Constant(offset),
        };
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert_eq!(
                    resources
                        .concrete_read_entries(&at(2), 2, &facts)
                        .unwrap()
                        .count(),
                    1
                );
                assert!(resources.permits_memory_read(&at(2), 2, &facts));
                assert!(!resources.permits_memory_read(&at(4), 1, &facts));
                assert!(!resources.permits_memory_read(&at(2), 3, &facts));
            })
        });
        samples.push((size, work, map_work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "read checker scanned unrelated ranges: {samples:?}"
    );
    assert!(
        samples[3].2 <= samples[0].2 * 3 + 128,
        "interval lookup scanned unrelated ranges: {samples:?}"
    );
}

#[test]
fn a_read_does_not_materialize_all_covering_views() {
    let mut samples = Vec::new();
    for size in [16_u32, 64, 256, 1024] {
        let base = Pointer::symbolic(Variable(851_040));
        let facts = PureFactContext::new();
        let mut resources = ResourceContext::new();
        for end in 1..=size {
            resources = resources.unchecked_with_fact(view(&base, 0, end));
        }
        resources.synchronize_memory_equalities(&facts);
        let (allowed, work) = crate::persistent::measure_persistent_work(|| {
            resources.permits_memory_read(&base, 1, &facts)
        });
        assert!(allowed);
        samples.push((size, work));
    }
    assert!(
        samples[3].1 <= samples[0].1 * 2 + 32,
        "a read enumerated every covering view: {samples:?}"
    );
}

#[test]
fn logical_field_coordinates_keep_symbolic_offsets_without_scanning_aliases() {
    let mut samples = Vec::new();
    for size in [4u64, 16, 64] {
        let _session = crate::kernel::VerificationSession::enter();
        let owner = Pointer::symbolic(Variable(955_930))
            .offset_by_elements(MachineTerm::Variable(Variable(955_931)), 4);
        let alias = Pointer::symbolic(Variable(955_932));
        let mut resources = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(
            MemoryRange::new_with_element_width(owner.clone(), 2u32.into(), 4u32.into(), 4),
        ));
        for i in 0..size {
            resources = resources.unchecked_with_fact(ResourceFact::view_memory(
                MemoryRange::new_with_element_width(
                    Pointer::symbolic(Variable(956_000 + i)),
                    0u32.into(),
                    4u32.into(),
                    4,
                ),
            ));
        }
        resources.synchronize_memory_equalities(&PureFactContext::new());
        let mut context = PureFactContext::new()
            .assume_proposition(Proposition::ResourceComposition(resources))
            .assume_condition(
                ConditionTerm::pointer_equal(owner.clone(), alias.clone()),
                true,
            );
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    alias.clone(),
                    Pointer::symbolic(Variable(957_000 + i)),
                ),
                true,
            );
        }
        context
            .composition_object_resources
            .advance_memory_equalities(&context);
        let ((selected, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                context
                    .composition_object_resources
                    .memory_address_spelling(&alias.offset_by_bytes(8), &context)
            })
        });
        assert_eq!(selected, Some(owner.offset_by_bytes(8)));
        samples.push((work, map_work));
    }
    assert!(
        samples[2].0 <= samples[0].0 * 2 + 64,
        "logical read lookup scanned unrelated entries: {samples:?}"
    );
    assert!(
        samples[2].1 <= samples[0].1 * 3 + 128,
        "logical read lookup copied unrelated indexes: {samples:?}"
    );
}

#[test]
fn prepared_access_provenance_misses_do_not_scan_overlapping_suppliers() {
    let mut samples = Vec::new();
    for size in [8u32, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let base = Pointer::symbolic(Variable(960_000));
        let unrelated_origin = Pointer::symbolic(Variable(960_001));
        let mut resources = ResourceContext::new_with_equalities(&facts);
        for end in 1..=size {
            resources = resources.unchecked_with_fact(ResourceFact::view_memory(MemoryRange::new(
                base.clone(),
                0u32.into(),
                end.into(),
            )));
        }
        resources.synchronize_memory_equalities(&facts);
        assert!(resources.permits_designated_memory_read(
            &base.offset_by_bytes(1),
            Some((&base, None)),
            4,
            &facts
        ));
        assert!(!resources.permits_memory_read(&base.offset_by_bytes(size * 4 + 1), 4, &facts));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!resources.permits_designated_memory_read(
                    &base.offset_by_bytes(1),
                    Some((&unrelated_origin, None)),
                    4,
                    &facts
                ));
            }
        });
        samples.push(work);
    }
    eprintln!("prepared provenance misses: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn prepared_object_provenance_lookup_does_not_enumerate_same_object_views() {
    let mut samples = Vec::new();
    for size in [8u32, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let base = Pointer::symbolic(Variable(961_000));
        let missing = Pointer::symbolic(Variable(961_001));
        let mut resources = ResourceContext::new_with_equalities(&facts);
        for end in 1..=size {
            resources = resources.unchecked_with_fact(ResourceFact::view_memory(MemoryRange::new(
                base.clone(),
                0u32.into(),
                end.into(),
            )));
        }
        resources.synchronize_memory_equalities(&facts);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(resources.memory_object_evidence(&base, &facts).is_some());
                assert!(resources.memory_object_evidence(&missing, &facts).is_none());
            }
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn prepared_write_and_storage_refusals_do_not_scan_owner_buckets() {
    let mut samples = Vec::new();
    for size in [8u32, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let facts = PureFactContext::new();
        let base = Pointer::symbolic(Variable(962_000));
        let missing = Pointer::symbolic(Variable(962_001));
        let query = base.offset_by_bytes(4);
        let mut resources = ResourceContext::new_with_equalities(&facts);
        for end in 1..=size {
            resources = resources.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                base.clone(),
                0u32.into(),
                end.into(),
            )));
        }
        resources.synchronize_memory_equalities(&facts);
        assert!(
            resources
                .designated_memory_write_range(&query, Some((&base, None)), 4, &facts)
                .is_some()
        );
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(
                    resources
                        .designated_memory_write_range(&query, Some((&missing, None)), 4, &facts)
                        .is_none()
                );
                assert!(!resources.owns_designated_storage_access(
                    &query,
                    (&missing, None),
                    4,
                    &facts
                ));
                assert!(!resources.permits_designated_storage_read(
                    &query,
                    Some((&missing, None)),
                    4,
                    &facts
                ));
                assert!(!resources.permits_designated_pointer_position(
                    &query,
                    &base,
                    (&missing, None),
                    &facts
                ));
            }
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}
