// Scaling tests of `src/kernel/tests/wide_scalar_tests.rs`: deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn wide_scalar_observation_work_scales_with_explicit_values() {
    let mut samples = Vec::new();
    for size in [16, 64, 256, 1024] {
        let (observations, work) = crate::instrumentation::measure_deterministic_work(|| {
            (0..size)
                .map(|index| {
                    IntegerTerm::from_machine(
                        MachineIntegerType::UInt128,
                        MachineTerm::Variable(Variable(149_000 + index)),
                    )
                    .unwrap()
                })
                .collect::<Vec<_>>()
        });
        assert_eq!(observations.len(), size as usize);
        assert!(
            work >= size as usize && work <= 32 * size as usize,
            "{size}: {work}"
        );
        samples.push(work);
    }
    for pair in samples.windows(2) {
        assert!(pair[1] <= 4 * pair[0] + 32, "{samples:?}");
    }
}

#[test]
fn wide_scalar_root_validation_does_not_scan_legacy_operand_trees() {
    for size in [16, 64, 256, 1024] {
        let mut term = MachineTerm::Variable(Variable(148_006));
        for _ in 0..size {
            term = MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: Box::new(term),
                right: Box::new(MachineTerm::uint64_constant(1)),
            };
        }
        let (accepted, work) = crate::instrumentation::measure_deterministic_work(|| {
            MachineIntegerType::UInt128.accepts_wide_term(&term)
        });
        assert!(!accepted);
        assert_eq!(work, 1);
    }
}

#[test]
fn wide_cached_load_canonicalization_ignores_unrelated_cells() {
    let mut samples = Vec::new();
    for count in [16, 64, 256] {
        let pointer = Pointer {
            block: "wide-cached-scaling".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let bits = MachineTerm::uint64_constant(0x1_0000_0001);
        let mut memory = Memory::new().with_block("wide-cached-scaling", (count + 1) * 8);
        for index in 1..=count {
            memory = memory.store(
                pointer.offset_by_bytes(index * 8),
                ProgramValue::UInt64(MachineTerm::uint64_constant(index as u64)),
            );
        }
        memory = memory.store(pointer.clone(), ProgramValue::UInt64(bits.clone()));
        let load =
            MachineTerm::MemoryLoad(intern_memory(memory), Box::new(pointer), LoadKind::Bits64);
        crate::kernel::memory_provenance::clear_canonical_form_caches();
        crate::kernel::memory_provenance::reset_atomic_canonicalization_term_visits();
        let (result, work) = crate::persistent::measure_persistent_work(|| {
            crate::kernel::api::canonicalize_atomic_loads(&load)
        });
        assert_eq!(result, bits);
        samples.push((
            crate::kernel::memory_provenance::atomic_canonicalization_term_visits(),
            work,
        ));
    }
    assert!(
        samples.iter().all(|(visits, _)| *visits == samples[0].0),
        "{samples:?}"
    );
    assert!(samples[2].1 <= samples[0].1 * 4 + 32, "{samples:?}");
}

// A named call drops the cache of a stored wide value behind a loaded pointer.
// Its selected alias must recover all eight bytes, without consulting unrelated
// cells or admitting a withdrawn alias, different read kind, or partial write.
#[test]
fn selected_wide_read_value_keeps_alias_authority_and_scales_with_unrelated_cells() {
    let _session = crate::kernel::VerificationSession::enter();
    let read_pointer = Pointer::symbolic(Variable(78_100));
    let owned_pointer = Pointer::symbolic(Variable(78_101));
    let callee = Pointer::symbolic(Variable(78_102));
    let alias = ConditionTerm::pointer_equal(read_pointer.clone(), owned_pointer.clone());
    let selected = PureFactContext::new().assume_condition(alias, true);
    let bits = MachineTerm::uint64_add(
        MachineTerm::Variable(Variable(78_103)),
        MachineTerm::uint64_constant(0x1_0000_0001),
    );
    let kept = CallKeptOwnership::new(
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(memory_range(
            owned_pointer,
            0,
            2,
        ))),
        CallKeptRanges::new(ResourceContext::new(), Vec::new(), None),
        &selected,
    );
    let matches = crate::kernel::memory_provenance::wide_read_has_recorded_value;
    let mut previous = None;
    for count in [16, 64, 256, 1024] {
        let mut memory = Memory::new();
        for index in 0..count {
            memory = memory.store(
                Pointer::symbolic(Variable(79_000 + index)),
                ProgramValue::UInt64(MachineTerm::uint64_constant(index)),
            );
        }
        memory = memory.store(read_pointer.clone(), ProgramValue::UInt64(bits.clone()));
        let after = memory.with_call_memory_havoc(
            Variable(78_104),
            &[memory_range(callee.clone(), 0, 2)],
            &selected,
            Some(&kept),
        );
        let load = MachineTerm::MemoryLoad(
            intern_memory_ref(&after),
            Box::new(read_pointer.clone()),
            LoadKind::Bits64,
        );
        crate::kernel::memory_provenance::clear_canonical_form_caches();
        let (found, work) =
            crate::instrumentation::measure_deterministic_work(|| matches(&load, &bits, &selected));
        assert!(found, "{count} unrelated cells");
        assert!(matches(&bits, &load, &selected));
        if let Some(previous) = previous {
            assert!(work <= previous + 64, "{count}: {work} after {previous}");
        }
        previous = Some(work);
        assert!(!matches(&load, &bits, &PureFactContext::new()));
        assert!(!matches(&load, &MachineTerm::uint64_constant(1), &selected));
        let narrow = MachineTerm::MemoryLoad(
            intern_memory_ref(&after),
            Box::new(read_pointer.clone()),
            LoadKind::Int32,
        );
        assert!(!matches(&narrow, &bits, &selected));
        let partial = read_pointer.offset_by_bytes(4);
        let changed = after
            .without_possible_aliasing_cells(&partial, 4, &selected)
            .store(partial, ProgramValue::Int32(MachineTerm::constant(0)));
        let changed = MachineTerm::MemoryLoad(
            intern_memory(changed),
            Box::new(read_pointer.clone()),
            LoadKind::Bits64,
        );
        assert!(!matches(&changed, &bits, &selected));
    }
}

// Read-value normalization is a bounded local rule, not a scan back through
// an arbitrarily long sequence of calls. Missing a checkpoint must refuse
// with fixed work as the unselected history grows.
#[test]
fn selected_wide_read_value_bounds_unselected_call_history() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(81_100));
    let owner = Pointer::symbolic(Variable(81_101));
    let callee = Pointer::symbolic(Variable(81_102));
    let selected = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(pointer.clone(), owner.clone()),
        true,
    );
    let kept = CallKeptOwnership::new(
        ResourceContext::new()
            .unchecked_with_fact(ResourceFact::own_memory(memory_range(owner, 0, 2))),
        CallKeptRanges::new(ResourceContext::new(), Vec::new(), None),
        &selected,
    );
    let bits = MachineTerm::uint64_constant(7);
    let mut previous = None;
    for count in [128, 256, 512] {
        let mut memory = Memory::new().store(pointer.clone(), ProgramValue::UInt64(bits.clone()));
        for index in 0..count {
            memory = memory.with_call_memory_havoc(
                Variable(82_000 + index),
                &[memory_range(callee.clone(), 0, 2)],
                &selected,
                Some(&kept),
            );
        }
        let load = MachineTerm::MemoryLoad(
            intern_memory(memory),
            Box::new(pointer.clone()),
            LoadKind::Bits64,
        );
        crate::kernel::memory_provenance::clear_canonical_form_caches();
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_provenance::wide_read_has_recorded_value(&load, &bits, &selected)
        });
        assert!(
            !found,
            "history of {count} calls needs an explicit checkpoint"
        );
        if let Some(previous) = previous {
            assert!(work <= previous + 64, "{count}: {work} after {previous}");
        }
        previous = Some(work);
    }
}

// A named-call cache may give two aliases different recorded read states.
// Congruence must retain all eight bytes, reject overwritten histories, and
// avoid visiting unrelated cells or selected facts.
#[test]
fn selected_wide_read_congruence_preserves_history_width_and_scales() {
    let _session = crate::kernel::VerificationSession::enter();
    let read_pointer = Pointer::symbolic(Variable(81_100));
    let owned_pointer = Pointer::symbolic(Variable(81_103));
    let callee = Pointer::symbolic(Variable(81_104));
    let alias = ConditionTerm::pointer_equal(read_pointer.clone(), owned_pointer.clone());
    let matches = crate::kernel::memory_provenance::wide_read_has_recorded_value;
    let mut previous_work = None;
    for count in [4u32, 16, 64, 256] {
        let mut selected = PureFactContext::new().assume_condition(alias.clone(), true);
        let mut memory = Memory::new();
        for index in 0..count {
            memory = memory.store(
                owned_pointer.offset_by_bytes((index + 1) * 8),
                ProgramValue::UInt64(MachineTerm::uint64_constant(u64::from(index))),
            );
            selected = selected.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(82_000 + u64::from(index))),
                    MachineTerm::constant(index),
                ),
                true,
            );
        }
        memory = memory.store(
            owned_pointer.clone(),
            ProgramValue::UInt64(MachineTerm::Variable(Variable(90_000 + u64::from(count)))),
        );
        let kept = CallKeptOwnership::new(
            ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(memory_range(
                owned_pointer.clone(),
                0,
                2,
            ))),
            CallKeptRanges::new(ResourceContext::new(), Vec::new(), None),
            &selected,
        );
        let after = memory.clone().with_call_memory_havoc(
            Variable(91_000 + u64::from(count)),
            &[memory_range(callee.clone(), 0, 2)],
            &selected,
            Some(&kept),
        );
        let read = |retained_state: &Memory, pointer: &Pointer, kind| {
            MachineTerm::MemoryLoad(
                intern_memory_ref(retained_state),
                Box::new(pointer.clone()),
                kind,
            )
        };
        let current = read(&after, &read_pointer, LoadKind::Bits64);
        let same_state = read(&after, &owned_pointer, LoadKind::Bits64);
        let earlier = read(&memory, &owned_pointer, LoadKind::Bits64);
        crate::kernel::memory_provenance::clear_canonical_form_caches();
        let (found, work) = crate::instrumentation::measure_deterministic_work(|| {
            matches(&current, &same_state, &selected) && matches(&current, &earlier, &selected)
        });
        assert!(found, "{count} unrelated cells and facts");
        if let Some(previous) = previous_work {
            assert!(work <= previous + 64, "{count}: {work} after {previous}");
        }
        previous_work = Some(work);
        assert!(matches(&earlier, &current, &selected));
        assert!(!matches(&current, &same_state, &PureFactContext::new()));
        assert!(!matches(
            &current,
            &read(&after, &callee, LoadKind::Bits64),
            &selected,
        ));
        assert!(!matches(
            &current,
            &read(&after, &owned_pointer, LoadKind::Int32),
            &selected,
        ));
        for (offset, value) in [
            (
                0,
                ProgramValue::UInt64(MachineTerm::uint64_constant(1 << 32)),
            ),
            (4, ProgramValue::Int32(MachineTerm::constant(1))),
        ] {
            let address = owned_pointer.offset_by_bytes(offset);
            let changed = after
                .without_possible_aliasing_cells(&address, value.byte_width(), &selected)
                .store(address, value);
            let changed_read = read(&changed, &read_pointer, LoadKind::Bits64);
            assert!(!matches(&changed_read, &earlier, &selected));
            assert!(matches(
                &changed_read,
                &read(&changed, &owned_pointer, LoadKind::Bits64),
                &selected,
            ));
        }
    }
}
