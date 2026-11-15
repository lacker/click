// Scaling tests of `src/kernel/eval/memory_loads.rs` (module `tests`): deterministic work measured at several
// input sizes. Included into its `scaling_tests` module; see "Scaling
// tests" in `docs/internals/testing.md`.

use super::*;

#[test]
fn logical_cached_pointer_read_carries_its_current_cell_equation() {
    let _session = crate::kernel::VerificationSession::enter();
    let empty = PureFactContext::new();
    let base = Memory::new();
    let address = Pointer::symbolic(Variable(955_901));
    let alias = Pointer::symbolic(Variable(955_902));
    let model = Pointer::symbolic(Variable(955_903));
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut memory = base.clone();
        let mut context = empty.clone().assume_condition(
            ConditionTerm::pointer_equal(address.clone(), alias.clone()),
            true,
        );
        for i in 0..size {
            memory = memory.store(Pointer::symbolic(Variable(956_000 + i)), int32(7));
            context = context.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(958_000 + i)),
                    MachineTerm::constant(7),
                ),
                true,
            );
        }
        // Build the ambient state before observing the pointer. Stores
        // through unrelated symbolic names after the observation might alias
        // either half of the pointer and cannot preserve its complete value.
        let cached = logical_pointer_read(&memory, &address, &empty);
        let cached_value = PointerValue::from_read(
            cached.clone(),
            ProgramType::Int64Pointer,
            &intern_memory_ref(&memory),
            &address,
        );
        assert_eq!(
            cached
                .as_loaded_value()
                .expect("typed cached load")
                .defining_address,
            address
        );
        memory = memory
            .materialize_named_cell(address.clone(), ProgramValue::Pointer(cached_value.clone()));
        context = context.assume_condition(
            ConditionTerm::pointer_value_equal(
                cached_value.clone(),
                PointerValue::new(model.clone(), ProgramType::Int64Pointer),
            ),
            true,
        );
        let required = Pointer::loaded_value(&intern_memory_ref(&memory), &alias);
        let equal = |facts: &PureFactContext| {
            crate::kernel::resource_arguments_proven_equal(
                &AlgebraicValue::Program(ProgramValue::typed_pointer(
                    model.clone(),
                    ProgramType::Int64Pointer,
                )),
                &AlgebraicValue::Program(ProgramValue::typed_pointer(
                    required.clone(),
                    ProgramType::Int64Pointer,
                )),
                facts,
            )
        };
        let before_equal = equal(&context);
        let ((paths, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                evaluate_logical_memory_load_paths(
                    &memory,
                    address.clone(),
                    ProgramType::Int64Pointer,
                    ExecutionFacts::new(),
                    Vec::new(),
                    &context,
                )
            })
        });
        samples.push((work, map_work));
        let [path] = paths.as_slice() else {
            panic!("one logical read");
        };
        assert_eq!(
            path.outcome,
            ExpressionOutcome::Value(ProgramValue::Pointer(cached_value.clone()))
        );
        assert!(path.obligations.is_empty());
        // A materialized read needs its current-cell equation, and may
        // also carry the complete stored-value equation.
        assert!((1..=2).contains(&path.facts.len()));
        assert!(
            path.facts
                .iter()
                .all(ExecutionPureFact::is_logical_read_equation)
        );
        assert!(!path.facts.has_path_conditions());
        assert_eq!(
            equal(&context),
            before_equal,
            "constructing the result must not mutate caller evidence"
        );
        let retained = assumptions_with_path_context(&context, &path.facts, &path.obligations);
        assert!(equal(&retained));
        assert_eq!(equal(&context), before_equal);
        assert!(!equal(&retained.restricted_to_facts(&[], &[])));
        assert!(!ResourceContext::new().permits_memory_read(&alias, 8, &retained));
        let missing_alias = empty.clone().assume_condition(
            ConditionTerm::pointer_value_equal(
                cached_value.clone(),
                PointerValue::new(model.clone(), ProgramType::Int64Pointer),
            ),
            true,
        );
        assert!(!equal(&assumptions_with_path_context(
            &missing_alias,
            &path.facts,
            &[]
        )));

        let replacement = Pointer::symbolic(Variable(955_904));
        let changed = memory.clone().store(
            address.clone(),
            ProgramValue::typed_pointer(replacement.clone(), ProgramType::Int64Pointer),
        );
        let changed_paths = evaluate_logical_memory_load_paths(
            &changed,
            address.clone(),
            ProgramType::Int64Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &retained,
        );
        let changed_context =
            assumptions_with_path_context(&retained, &changed_paths[0].facts, &[]);
        let changed_read = Pointer::loaded_value(&intern_memory_ref(&changed), &alias);
        assert!(changed_context.pointers_known_equal(&changed_read, &replacement));
        assert!(!changed_context.pointers_known_equal(&changed_read, &cached));
    }
    assert!(samples[3].0 <= samples[0].0 * 3 + 128, "{samples:?}");
    assert!(samples[3].1 <= samples[0].1 * 6 + 512, "{samples:?}");
    {
        let costs = samples.iter().map(|x| x.0).collect::<Vec<_>>();
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
    {
        let costs = samples.iter().map(|x| x.1).collect::<Vec<_>>();
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

/// Naming a load after a call whose kept memory shares the load's block
/// asks whether the load's address is one of the kept ranges' bases. A
/// load through a pointer read out of memory registers that read, and the
/// reads its own address depends on, in the asking context's equality
/// graph. Naming walks are known-free, so they ask in one empty
/// context per session: each read is registered once, and naming the
/// load after each later call costs the same however deep the address's
/// chain of reads is. A fresh context per walk paid for the whole chain
/// again at every call, which made each call step slower in proportion
/// to how its arguments were reached.
#[test]
fn naming_a_load_after_a_call_is_flat_in_its_address_read_depth() {
    use crate::kernel::primitives::{CallKeptOwnership, CallKeptRanges};
    const CALLS: u64 = 8;
    let mut samples = Vec::new();
    for depth in [1_u64, 2, 4, 8, 16] {
        let _session = crate::kernel::VerificationSession::enter();
        let empty = PureFactContext::new();
        let base = Memory::new();
        let read = |address: &Pointer| {
            let ProgramValue::Pointer(value) = canonicalized_symbolic_load_value_with_identity(
                &base,
                address,
                ProgramType::Int32Pointer,
                &mut Vec::new().into(),
                &empty,
                None,
                LoadPurpose::Logical,
            )
            .unwrap() else {
                panic!("expected a typed pointer read");
            };
            value.pointer().clone()
        };
        let mut array = Pointer::symbolic(Variable(992_000));
        for _ in 0..depth {
            array = read(&array);
        }
        let element =
            |index: u64| array.offset_by_elements(MachineTerm::Variable(Variable(index)), 4);
        let range = |start: Pointer| {
            MemoryRange::new(start, MachineTerm::constant(0), MachineTerm::constant(1))
        };
        // The callee may write one element, and the caller keeps another,
        // each at an unrelated index: neither decides the cell.
        let written = [range(element(992_101))];
        let kept = CallKeptOwnership::new(
            ResourceContext::new(),
            CallKeptRanges::new(
                ResourceContext::new()
                    .unchecked_with_facts([ResourceFact::own_memory(range(element(992_102)))]),
                Vec::new(),
                None,
            ),
            &empty,
        );
        let cell = element(992_103);
        let mut memory = base.clone();
        let mut work = Vec::new();
        for call in 0..CALLS {
            memory = memory.with_call_memory_havoc(
                Variable(992_200 + call),
                &written,
                &empty,
                Some(&kept),
            );
            let load = MachineTerm::MemoryLoad(
                crate::kernel::intern_memory_ref(&memory),
                Box::new(cell.clone()),
                LoadKind::Int32,
            );
            let (named, units) = crate::instrumentation::measure_deterministic_work(|| {
                load_variable_for_term(&load)
            });
            assert!(named.is_some(), "a load term has a name");
            work.push(units);
        }
        // The first call registers the chain; every later one is the
        // per-call cost being measured.
        let later = work[1..].iter().copied().max().unwrap();
        samples.push((depth, later));
    }
    eprintln!("naming after a call (address read depth, units): {samples:?}");
    let (_, shallow) = samples[0];
    for (depth, units) in &samples {
        assert!(
            *units <= shallow + 8,
            "naming after a call grew with address read depth {depth}: {samples:?}"
        );
    }
}

#[test]
fn pointer_read_observations_check_frames_scope_and_scaling() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Pointer::symbolic(Variable(960_000));
    let alias = Pointer::symbolic(Variable(960_001));
    let base = Memory::new();
    let empty = PureFactContext::new();
    let facts = empty.clone().assume_condition(
        ConditionTerm::pointer_equal(address.clone(), alias.clone()),
        true,
    );
    let read = |memory: &Memory, address: &Pointer, purpose| {
        let ProgramValue::Pointer(value) = canonicalized_symbolic_load_value_with_identity(
            memory,
            address,
            ProgramType::Int32Pointer,
            &mut Vec::new().into(),
            &empty,
            None,
            purpose,
        )
        .unwrap() else {
            panic!("expected a typed pointer read");
        };
        value.pointer().clone()
    };
    let left = read(&base, &address, LoadPurpose::Logical);
    let right = read(&base, &alias, LoadPurpose::Logical);
    let equal = |left: &Pointer, right: &Pointer, facts: &PureFactContext| {
        crate::kernel::memory_provenance::pointer_read_has_recorded_value(left, right, facts)
    };
    assert!(equal(&left, &right, &facts));
    assert!(!equal(&left, &right, &empty));
    let partial = base
        .clone()
        .store(address.offset_by_bytes(4), ProgramValue::Int32(0u32.into()));
    let changed = read(&partial, &address, LoadPurpose::Logical);
    assert!(!equal(&left, &changed, &facts));
    let replaced = base.clone().store(
        address.clone(),
        ProgramValue::typed_pointer(Pointer::null(), ProgramType::Int32Pointer),
    );
    let changed = read(&replaced, &address, LoadPurpose::Logical);
    assert!(!equal(&left, &changed, &facts));
    let mut previous = None;
    for count in [16_u64, 64, 256, 1024] {
        for index in 0..count {
            read(
                &base,
                &Pointer::symbolic(Variable(970_000 + index)),
                LoadPurpose::Logical,
            );
        }
        let (proved, work) =
            crate::instrumentation::measure_deterministic_work(|| equal(&left, &right, &facts));
        assert!(proved);
        if let Some(previous) = previous {
            assert!(work <= previous + 16, "{count}: {work} after {previous}");
        }
        previous = Some(work);
    }
    // A typed read is named by its definition: the name decodes to the read
    // itself, not to a per-epoch observation of it.
    let decode = |value: &Pointer| {
        value
            .as_loaded_value()
            .map(|read| (read.defining_memory.arena_id(), read.defining_address))
    };
    let original = decode(&left).unwrap();
    assert_eq!(original.1, address);
    let saved = capture_load_variable_registry();
    begin_load_origin_epoch();
    // A volatile read, and a scalar load of the same cell, are not pointer
    // reads of it and prove nothing about one.
    let volatile = read(&base, &address, LoadPurpose::VolatileProgram);
    assert!(latest_pointer_read_observation(&volatile).is_none());
    assert!(decode(&volatile).is_none());
    assert!(!equal(&left, &volatile, &facts));
    let scalar = MachineTerm::MemoryLoad(
        intern_memory(base.clone()),
        Box::new(address.clone()),
        LoadKind::Int32,
    );
    let scalar = Pointer::symbolic(load_variable_for_term(&scalar).unwrap().0);
    assert!(latest_pointer_read_observation(&scalar).is_none());
    assert!(decode(&scalar).is_none());
    assert!(!equal(&left, &scalar, &facts));
    restore_load_variable_registry(&saved);
    assert_eq!(decode(&left), Some(original));
    clear_load_variable_registry();
    assert!(decode(&left).is_none());
}

// Model arms can share a canonical word but have different live DAGs.
// Refresh only its producer observation, including on a naming-cache hit.
#[test]
fn wide_observations_preserve_width_scope_and_selected_query_scaling() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = Pointer::symbolic(Variable(940_000));
    let other = Pointer::symbolic(Variable(940_001));
    let base = intern_memory(Memory::new());
    let load = |memory: &SharedMemory, pointer: &Pointer, kind| {
        MachineTerm::MemoryLoad(memory.clone(), Box::new(pointer.clone()), kind)
    };
    let first = load(&base, &pointer, LoadKind::Bits64);
    let (word, _) = load_variable_for_term(&first).unwrap();
    let word_term = MachineTerm::Variable(word);
    let second_memory = intern_memory(base.memory().clone().store(
        Pointer {
            block: "observation:unrelated".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        ProgramValue::UInt64(MachineTerm::uint64_constant(7)),
    ));
    // Materialize the same named value in an independent live state.
    let second_memory = intern_memory(
        second_memory
            .memory()
            .clone()
            .store(pointer.clone(), ProgramValue::UInt64(word_term.clone())),
    );
    let second = load(&second_memory, &pointer, LoadKind::Bits64);
    assert_eq!(load_variable_for_term(&second).unwrap().0, word);
    assert_eq!(latest_wide_load_observation(&word), Some(second.clone()));
    assert_eq!(load_variable_for_term(&first).unwrap().0, word);
    assert_eq!(latest_wide_load_observation(&word), Some(first.clone()));
    load_variable_for_term(&second).unwrap();
    let facts = PureFactContext::new();
    assert!(
        crate::kernel::memory_provenance::wide_read_has_recorded_value(&word_term, &second, &facts,)
    );
    assert!(
        !crate::kernel::memory_provenance::wide_read_has_recorded_value(
            &word_term,
            &load(&second_memory, &other, LoadKind::Bits64),
            &facts,
        )
    );
    let changed = intern_memory(second_memory.memory().clone().store(
        pointer.clone(),
        ProgramValue::UInt64(MachineTerm::uint64_constant(9)),
    ));
    assert!(
        !crate::kernel::memory_provenance::wide_read_has_recorded_value(
            &word_term,
            &load(&changed, &pointer, LoadKind::Bits64),
            &facts,
        )
    );
    let narrow = load(&base, &pointer, LoadKind::Int32);
    let (narrow_word, _) = load_variable_for_term(&narrow).unwrap();
    assert!(latest_wide_load_observation(&narrow_word).is_none());
    assert!(
        !crate::kernel::memory_provenance::wide_read_has_recorded_value(
            &word_term,
            &MachineTerm::Variable(narrow_word),
            &facts,
        )
    );
    let mut previous = None;
    for count in [16_u64, 64, 256, 1024] {
        for index in 0..count {
            let unrelated = Pointer::symbolic(Variable(950_000 + index));
            load_variable_for_term(&load(&base, &unrelated, LoadKind::Bits64)).unwrap();
        }
        let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_provenance::wide_read_has_recorded_value(
                &word_term, &second, &facts,
            )
        });
        assert!(proved);
        if let Some(previous) = previous {
            assert!(work <= previous + 16, "{count}: {work} after {previous}");
        }
        previous = Some(work);
    }
    let saved = capture_load_variable_registry();
    load_variable_for_term(&first).unwrap();
    assert_eq!(latest_wide_load_observation(&word), Some(first));
    restore_load_variable_registry(&saved);
    assert_eq!(latest_wide_load_observation(&word), Some(second.clone()));
    begin_load_origin_epoch();
    assert!(latest_wide_load_observation(&word).is_none());
    restore_load_variable_registry(&saved);
    assert_eq!(latest_wide_load_observation(&word), Some(second));
}

#[test]
fn logical_reads_of_a_returned_field_share_checked_alias_identity() {
    let field = Pointer {
        block: "local:parent-guard".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let alias = Pointer::symbolic(Variable(944_019));
    let before = Memory::new()
        .with_block(field.block.clone(), 16)
        .store(field.clone(), ProgramValue::Int32(MachineTerm::constant(1)));
    let range = MemoryRange::new_with_element_width(field.clone(), 0u32.into(), 4u32.into(), 1);
    let memory =
        before.with_call_memory_havoc(Variable(944_020), &[range], &PureFactContext::new(), None);
    let facts = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(alias.clone(), field.clone()),
        true,
    );
    let read = |pointer, assumptions: &PureFactContext| {
        evaluate_logical_memory_load_paths(
            &memory,
            pointer,
            ProgramType::Int32,
            Vec::new().into(),
            Vec::new(),
            assumptions,
        )
    };
    let direct = read(field.clone(), &facts);
    let returned = read(alias.clone(), &facts);
    assert!(matches!(
        direct[0].outcome,
        ExpressionOutcome::Value(ProgramValue::Int32(_))
    ));
    let ExpressionOutcome::Value(ProgramValue::Int32(left)) = &direct[0].outcome else {
        panic!("scalar read expected");
    };
    let ExpressionOutcome::Value(ProgramValue::Int32(right)) = &returned[0].outcome else {
        panic!("scalar read expected");
    };
    assert!(
        facts.equality_graph.are_int32_equal(left, right),
        "the shared graph must retain the producer's projection equation"
    );
    assert!(
        !PureFactContext::new()
            .equality_graph
            .are_int32_equal(left, right),
        "projection identity does not supply an address alias"
    );
    let capture = crate::kernel::memory_provenance::CheckedLoadEqualityCapture::start();
    assert!(facts.memory_loads_proven_equal(left, right));
    let evidence = capture.finish();
    assert!(!evidence.is_empty());
    assert!(evidence.iter().all(|proof| proof.checks(&facts)));
    assert!(
        evidence
            .iter()
            .all(|proof| !proof.checks(&PureFactContext::new()))
    );
    let mut work = Vec::new();
    for count in [4, 16, 64, 256] {
        let mut context = facts.clone();
        for index in 0..count {
            context = context.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(960_000 + index)),
                    MachineTerm::constant(index as u32),
                ),
                true,
            );
        }
        let (valid, units) = crate::instrumentation::measure_deterministic_work(|| {
            let capture = crate::kernel::memory_provenance::CheckedLoadEqualityCapture::start();
            let equal = context.memory_loads_proven_equal(left, right);
            let evidence = capture.finish();
            equal && !evidence.is_empty() && evidence.iter().all(|proof| proof.checks(&context))
        });
        assert!(valid);
        work.push(units);
    }
    assert!(
        work[3] <= work[0] * 4 + 64,
        "ambient alias-equality scan: {work:?}"
    );
    let retained = facts
        .clone()
        .assume_condition(ConditionTerm::equal(right.clone(), 42u32.into()), true);
    for value in [ProgramValue::Int32(7u32.into()), crate::kernel::uint8(7u32)] {
        let changed = memory.clone().store(field.clone(), value);
        let paths = evaluate_logical_memory_load_paths(
            &changed,
            field.clone(),
            ProgramType::Int32,
            ExecutionFacts::new(),
            vec![],
            &retained,
        );
        let ExpressionOutcome::Value(ProgramValue::Int32(after)) = &paths[0].outcome else {
            panic!("scalar after overwrite");
        };
        assert!(
            !retained.equality_graph.are_int32_equal(right, after),
            "a whole or partial overwrite cannot share the old observation"
        );
        assert!(
            retained
                .equality_graph
                .are_int32_equal(right, &42u32.into())
        );
    }
    let unrelated = read(alias, &PureFactContext::new());
    assert_ne!(
        direct[0].outcome, unrelated[0].outcome,
        "a missing alias premise cannot join reads"
    );
    {
        let costs = work.clone();
        let indexed = |costs: &[usize]| costs.iter().all(|work| *work <= costs[0] + 64);
        assert!(indexed(&costs), "indexed work: {costs:?}");
        let scanned = costs
            .iter()
            .zip([4, 16, 64, 256])
            .map(|(work, size)| work + usize::try_from(size).unwrap())
            .collect::<Vec<_>>();
        assert!(
            !indexed(&scanned),
            "the smaller fixture must detect a visit per unrelated item: {costs:?}"
        );
    }
}

#[test]
#[ignore = "nightly: 1.9s in the parallel gate"]
fn logical_read_address_uses_class_index_without_scanning_aliases_or_frames() {
    let samples = logical_read_alias_samples(&[4, 64, 1024]);
    assert!(
        samples[2].0 <= samples[0].0 * 3 + 128,
        "address lookup scanned aliases or frames: {samples:?}"
    );
    assert!(
        samples[2].1 <= samples[0].1 * 4 + 256,
        "address lookup copied unrelated indexes: {samples:?}"
    );
    eprintln!("logical read address work: {samples:?}");
}

#[test]
fn logical_read_through_an_alias_retains_the_stored_word() {
    logical_read_alias_samples(&[4]);
}

fn logical_read_alias_samples(sizes: &[u64]) -> Vec<(usize, usize)> {
    let _session = crate::kernel::VerificationSession::enter();
    let owner = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int64(MachineTerm::Variable(Variable(95_000)), 1, false),
    };
    let alias = Pointer::symbolic(Variable(95_001));
    let empty = PureFactContext::new();
    let resources =
        ResourceContext::new_with_equalities(&empty).unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(owner.clone(), 0u32.into(), 3u32.into(), 4),
        ));
    let before = empty.assume_proposition(Proposition::ResourceComposition(resources));
    let mut memory = Memory::new();
    for offset in [0, 4, 8] {
        memory = memory.store(owner.offset_by_bytes(offset), int32(7));
    }
    let mut samples = Vec::new();
    for &size in sizes {
        let mut context = before.clone().assume_condition(
            ConditionTerm::pointer_equal(owner.clone(), alias.clone()),
            true,
        );
        for i in 0..size {
            // Unrelated admitted frames and many names of the selected
            // address must not become a spelling search at the read.
            let frame = ResourceContext::new_with_equalities(&context).unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new_with_element_width(
                    Pointer::symbolic(Variable(196_000 + i)),
                    0u32.into(),
                    1u32.into(),
                    4,
                )),
            );
            context = context
                .assume_proposition(Proposition::ResourceComposition(frame))
                .assume_condition(
                    ConditionTerm::pointer_equal(
                        alias.clone(),
                        Pointer::symbolic(Variable(297_000 + i)),
                    ),
                    true,
                );
        }
        let mut outcomes = Vec::new();
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for offset in [0, 4, 8] {
                    assert_eq!(
                        logical_memory_load_address(
                            &memory,
                            alias.offset_by_bytes(offset),
                            ProgramType::Int32,
                            &context
                        ),
                        owner.offset_by_bytes(offset)
                    );
                    let paths = evaluate_logical_memory_load_paths(
                        &memory,
                        alias.offset_by_bytes(offset),
                        ProgramType::Int32,
                        Vec::new().into(),
                        Vec::new(),
                        &context,
                    );
                    assert_eq!(paths.len(), 1);
                    let without_alias = evaluate_logical_memory_load_paths(
                        &memory,
                        alias.offset_by_bytes(offset),
                        ProgramType::Int32,
                        ExecutionFacts::new(),
                        Vec::new(),
                        &before,
                    );
                    assert_eq!(
                        paths[0].outcome, without_alias[0].outcome,
                        "alias evidence must not change the read term"
                    );
                    assert!(without_alias[0].facts.is_empty());
                    assert_eq!(paths[0].facts.len(), 1);
                    assert!(
                        paths[0]
                            .facts
                            .iter()
                            .all(ExecutionPureFact::is_logical_read_equation)
                    );
                    let retained = assumptions_with_path_context(&context, &paths[0].facts, &[]);
                    let ExpressionOutcome::Value(ProgramValue::Int32(read)) = &paths[0].outcome
                    else {
                        panic!("int32 read")
                    };
                    assert!(
                        retained
                            .equality_graph
                            .are_int32_equal(read, &MachineTerm::constant(7))
                    );
                    assert!(paths[0].obligations.is_empty());
                    outcomes.push(paths[0].outcome.clone());
                }
            })
        });
        // The read's term is fact-stable; only the returned equation knows
        // the alias. Producing it must not mutate the incoming context.
        for outcome in outcomes {
            let ExpressionOutcome::Value(ProgramValue::Int32(read)) = outcome else {
                panic!("an int32 read: {outcome:?}");
            };
            assert!(
                context
                    .condition_facts
                    .get(&ConditionTerm::equal(
                        read.clone(),
                        MachineTerm::constant(7)
                    ))
                    .is_none(),
                "producing a side fact must not admit it into caller evidence"
            );
            assert!(
                !before
                    .equality_graph
                    .are_int32_equal(&read, &MachineTerm::constant(7)),
                "without the alias fact the read has no stored value"
            );
        }
        // A different offset and a later store cannot inherit the old 7.
        let outside = evaluate_logical_memory_load_paths(
            &memory,
            alias.offset_by_bytes(12),
            ProgramType::Int32,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
        );
        assert!(outside[0].facts.is_empty());
        let changed = memory.clone().store(owner.clone(), int32(9));
        let changed_paths = evaluate_logical_memory_load_paths(
            &changed,
            alias.clone(),
            ProgramType::Int32,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
        );
        let retained = assumptions_with_path_context(&context, &changed_paths[0].facts, &[]);
        let ExpressionOutcome::Value(ProgramValue::Int32(read)) = &changed_paths[0].outcome else {
            panic!("int32 read");
        };
        assert!(retained.equality_graph.are_int32_equal(read, &9u32.into()));
        assert!(!retained.equality_graph.are_int32_equal(read, &7u32.into()));
        samples.push((work, map_work));
        assert_eq!(
            logical_memory_load_address(&memory, alias.clone(), ProgramType::Int32, &before),
            alias
        );
    }
    samples
}

#[test]
fn logical_scalar_read_meets_model_cell_through_later_external_alias() {
    let _session = crate::kernel::VerificationSession::enter();
    let owner = Pointer::symbolic(Variable(95_300));
    let alias = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(95_301)), 4),
    };
    let field = owner.offset_by_bytes(8);
    let queried = alias.offset_by_bytes(8);
    let value = ProgramValue::UInt64(MachineTerm::uint64_constant(17));
    let memory = Memory::new().materialize_named_cell(field.clone(), value.clone());
    let empty = PureFactContext::new();
    let resources =
        ResourceContext::new_with_equalities(&empty).unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(field.clone(), 0u32.into(), 1u32.into(), 8),
        ));
    let before = empty.assume_proposition(Proposition::ResourceComposition(resources));
    let read = |memory: &Memory, pointer: Pointer, context: &PureFactContext| {
        let paths = evaluate_logical_memory_load_paths(
            memory,
            pointer,
            ProgramType::UInt64,
            Vec::new().into(),
            Vec::new(),
            context,
        );
        assert_eq!(paths.len(), 1);
        assert!(paths[0].facts.is_empty());
        assert!(paths[0].obligations.is_empty());
        let ExpressionOutcome::Value(value) = &paths[0].outcome else {
            panic!("logical scalar read")
        };
        // A read of a stored cell is compared through the read-over-write
        // authority: it names its version, not the stored value.
        ExpressionOutcome::Value(crate::kernel::eval::read_over_write_program_value(
            value.numeric_value(),
        ))
    };
    // The read keeps its own term (lowering is fact-stable); the alias makes
    // it equal to the stored value in the context's equality graph.
    let equals = |read: ExpressionOutcome, context: &PureFactContext, expected: &ProgramValue| {
        let (ExpressionOutcome::Value(read), Some(expected)) = (
            read,
            crate::kernel::spec::program_value_bitvector_term(expected),
        ) else {
            return false;
        };
        crate::kernel::spec::program_value_bitvector_term(&read)
            .is_some_and(|read| context.equality_graph.are_uint64_equal(&read, &expected))
    };
    let mut samples = Vec::new();
    for size in [8u64, 64, 512] {
        let mut context = before.clone().assume_condition(
            ConditionTerm::pointer_equal(owner.clone(), alias.clone()),
            true,
        );
        for i in 0..size {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    owner.clone(),
                    Pointer::symbolic(Variable(98_000 + i)),
                ),
                true,
            );
        }
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                assert!(equals(
                    read(&memory, queried.clone(), &context),
                    &context,
                    &value
                ));
                let symbolic = context.clone().keep_spec_loads_symbolic();
                assert!(equals(
                    read(&memory, queried.clone(), &symbolic),
                    &symbolic,
                    &value
                ));
            })
        });
        samples.push((work, map_work));
        assert!(!equals(
            read(&memory, queried.clone(), &before),
            &before,
            &value
        ));
        assert!(!equals(
            read(&memory, alias.offset_by_bytes(16), &context),
            &context,
            &value
        ));
        assert!(!ResourceContext::new().permits_memory_read(&queried, 8, &context));
        let changed_value = ProgramValue::UInt64(MachineTerm::uint64_constant(19));
        let changed = memory.clone().store(field.clone(), changed_value.clone());
        assert!(equals(
            read(&changed, queried.clone(), &context),
            &context,
            &changed_value
        ));
        assert!(!equals(
            read(&changed, queried.clone(), &context),
            &context,
            &value
        ));
        // An exact newer cell takes precedence over a cached alias.
        let direct_value = ProgramValue::UInt64(MachineTerm::uint64_constant(23));
        let direct = memory.clone().store(queried.clone(), direct_value.clone());
        assert_eq!(
            read(&direct, queried.clone(), &context),
            ExpressionOutcome::Value(direct_value)
        );
    }
    assert!(
        samples[2].0 <= samples[0].0 * 3 + 64,
        "cached coordinate lookup scanned aliases: {samples:?}"
    );
    assert!(
        samples[2].1 <= samples[0].1 * 4 + 128,
        "cached coordinate lookup copied indexes: {samples:?}"
    );
}

#[test]
fn pointer_read_premises_register_definitions_before_transitive_queries() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = Memory::new();
    let retained_state = intern_memory_ref(&memory);
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(95_600)), 4),
    };
    let parent = Pointer::symbolic(Variable(95_601));
    let successor = Pointer::symbolic(Variable(95_602));
    let address = base.offset_by_bytes(16);
    let load = canonical_form_of_load(retained_state, address.clone(), LoadKind::Int32);
    let ProgramValue::Pointer(stored) =
        crate::kernel::cell_run_value(ProgramType::Int64Pointer, load)
    else {
        panic!("pointer field");
    };
    let bare = PureFactContext::new();
    let read = logical_pointer_read(&memory, &parent.offset_by_bytes(16), &bare);
    let base_equality = ConditionTerm::pointer_equal(parent.clone(), base);
    let read_equality = ConditionTerm::pointer_equal(stored.pointer().clone(), successor.clone());
    let mut samples = Vec::new();
    for size in [8u64, 32, 128, 512] {
        let mut ambient = bare.clone();
        for i in 0..size {
            ambient = ambient.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(96_600 + i)),
                    Pointer::symbolic(Variable(97_600 + i)),
                ),
                true,
            );
        }
        let (context, insertion_work) = crate::instrumentation::measure_deterministic_work(|| {
            ambient
                .clone()
                .assume_condition(base_equality.clone(), true)
                .assume_condition(read_equality.clone(), true)
        });
        let ((equal, query_work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                context.pointers_known_equal(&read, &successor)
            })
        });
        assert!(
            equal,
            "a query must not depend on first comparing the two read spellings"
        );
        samples.push((insertion_work, query_work));
        // Measured: 4646, 4721, 4795 and 4869 at 8, 32, 128 and 512 ambient
        // facts; 3441 to 3664 before the read took its numeric address and
        // the displaced address its numeric sum. The extra nodes are a
        // constant ~1200, with the same logarithmic growth.
        assert!(
            map_work < 1024 * (size.ilog2() as usize + 2),
            "size={size}, map work={map_work}"
        );
        assert!(!ambient.pointers_known_equal(&read, &successor));
        assert!(
            !ambient
                .clone()
                .assume_condition(base_equality.clone(), true)
                .pointers_known_equal(&read, &successor)
        );
        assert!(
            !ambient
                .assume_condition(read_equality.clone(), true)
                .pointers_known_equal(&read, &successor)
        );
        let other = logical_pointer_read(&memory, &parent.offset_by_bytes(24), &bare);
        assert!(!context.pointers_known_equal(&other, &successor));
        let changed = memory.clone().store(
            address.clone(),
            ProgramValue::typed_pointer(
                Pointer::symbolic(Variable(95_603)),
                ProgramType::Int64Pointer,
            ),
        );
        let replacement = logical_pointer_read(&changed, &address, &context);
        assert!(!context.pointers_known_equal(&replacement, &successor));
        assert!(!ResourceContext::new().permits_memory_read(&address, 8, &context));
    }
    assert!(
        samples
            .iter()
            .all(|(insert, query)| *insert <= samples[0].0 + 100 && *query <= samples[0].1 + 100),
        "read registration scanned unrelated equalities: {samples:?}"
    );
}

#[test]
fn seeded_pointer_cells_retain_their_typed_load_definition() {
    let _session = crate::kernel::VerificationSession::enter();
    let memory = Memory::new();
    let retained_state = intern_memory_ref(&memory);
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(95_400)), 4),
    };
    let alias = Pointer::symbolic(Variable(95_401));
    let address = base.offset_by_bytes(16);
    let alias_address = alias.offset_by_bytes(16);
    let load = canonical_form_of_load(retained_state, address.clone(), LoadKind::Int32);
    let ProgramValue::Pointer(seeded) =
        crate::kernel::cell_run_value(ProgramType::Int64Pointer, load)
    else {
        panic!("seeded pointer");
    };
    let bare = PureFactContext::new();
    let read = logical_pointer_read(&memory, &alias_address, &bare);
    assert!(!bare.pointers_known_equal(seeded.pointer(), &read));
    let mut samples = Vec::new();
    for size in [8u64, 32, 128, 512] {
        for i in 0..size {
            let unrelated = Pointer::symbolic(Variable(96_400 + i)).offset_by_bytes(16);
            let load = canonical_form_of_load(
                intern_memory_ref(&memory),
                unrelated.clone(),
                LoadKind::Int32,
            );
            crate::kernel::cell_run_value(ProgramType::Int64Pointer, load);
        }
        let context = bare.clone().assume_condition(
            ConditionTerm::pointer_equal(base.clone(), alias.clone()),
            true,
        );
        let ((equal, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                context.pointers_known_equal(seeded.pointer(), &read)
            })
        });
        assert!(equal);
        samples.push(work);
        assert!(
            map_work < 512 * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
        assert!(!bare.pointers_known_equal(seeded.pointer(), &read));
        assert!(!ResourceContext::new().permits_memory_read(&alias_address, 8, &context));
        let other = logical_pointer_read(&memory, &alias.offset_by_bytes(24), &context);
        assert!(!context.pointers_known_equal(seeded.pointer(), &other));
        let changed = memory.clone().store(
            address.clone(),
            ProgramValue::typed_pointer(
                Pointer::symbolic(Variable(95_402)),
                ProgramType::Int64Pointer,
            ),
        );
        let replacement = logical_pointer_read(&changed, &address, &context);
        assert!(!context.pointers_known_equal(seeded.pointer(), &replacement));
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 40),
        "read definition lookup scanned unrelated cells: {samples:?}"
    );
}

/// A selected cached load denotes one pointer even when its cell is
/// reached through a loop cursor in another symbolic coordinate system.
#[test]
fn cached_pointer_value_keeps_its_defining_coordinates_and_scales() {
    let _session = crate::kernel::VerificationSession::enter();
    let owner = Pointer::symbolic(Variable(195_100));
    let cursor = Pointer::symbolic(Variable(195_101));
    let address = owner.offset_by_bytes(16);
    let cursor_address = cursor.offset_by_bytes(16);
    let memory = Memory::new();
    let retained_state = intern_memory_ref(&memory);
    let bits = canonical_form_of_load(retained_state, address.clone(), LoadKind::Int32);
    let cached = ProgramValue::Int32(bits);
    let mut samples = Vec::new();
    for count in [4u64, 16, 64, 256] {
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(owner.clone(), cursor.clone()),
            true,
        );
        for i in 0..count {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(196_000 + i)),
                    Pointer::symbolic(Variable(198_000 + i)),
                ),
                true,
            );
        }
        let read = |at: &Pointer| {
            canonicalized_pointer_value_from_int_cell(
                &memory,
                at,
                &cached,
                ProgramType::Int64Pointer,
                &mut ExecutionFacts::new(),
                &context,
                None,
                LoadPurpose::Program,
            )
            .expect("selected pointer cache")
        };
        let expected = read(&address);
        let ((actual, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| read(&cursor_address))
        });
        let (ProgramValue::Pointer(actual), ProgramValue::Pointer(expected)) = (&actual, &expected)
        else {
            panic!("typed pointer cache")
        };
        assert!(context.pointers_known_equal(actual.pointer(), expected.pointer()));
        assert!(context.pointer_designations_match(actual, expected));
        samples.push((work, map_work));
        assert!(
            canonicalized_pointer_value_from_int_cell(
                &memory,
                &cursor_address,
                &ProgramValue::UInt64(MachineTerm::uint64_constant(0)),
                ProgramType::Int64Pointer,
                &mut ExecutionFacts::new(),
                &context,
                None,
                LoadPurpose::Program,
            )
            .is_none(),
            "an arbitrary scalar must not gain pointer identity"
        );
    }
    assert!(
        samples.iter().all(|sample| sample.0 <= samples[0].0 + 32),
        "{samples:?}"
    );
    assert!(
        samples.iter().all(|sample| sample.1 <= samples[0].1 + 128),
        "{samples:?}"
    );
    {
        let costs = samples.iter().map(|x| x.1).collect::<Vec<_>>();
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
fn cached_pointer_reads_retain_their_current_cell_identity() {
    let _session = crate::kernel::VerificationSession::enter();
    let alias = Pointer::symbolic(Variable(95_510));
    let address = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(95_511)), 4),
    };
    let stored = Pointer::symbolic(Variable(95_512));
    let replacement = Pointer::symbolic(Variable(95_513));
    let empty = PureFactContext::new();
    let mut samples = Vec::new();
    for count in [8u64, 32, 128, 512] {
        let mut memory = Memory::new().store(
            alias.clone(),
            ProgramValue::typed_pointer(stored.clone(), ProgramType::Int64Pointer),
        );
        let mut context = empty
            .clone()
            .require_owned_expression_loads()
            .assume_condition(
                ConditionTerm::pointer_equal(alias.clone(), address.clone()),
                true,
            );
        let initial = intern_memory_ref(&memory);
        let initial_read = Pointer::loaded_value(&initial, &address);
        context.register_checked_pointer_read(&initial_read, &initial, &address);
        assert!(context.pointers_known_equal(&stored, &initial_read));
        for index in 0..count {
            let before = memory.clone();
            let write = Pointer {
                block: PointerBlock::Heap(96_000 + index),
                offset: PointerOffsetTerm::Constant(0),
            };
            memory = memory.store(write.clone(), int32(7));
            let (_, _, equality) = crate::kernel::tests::explicit_frame(
                &before,
                &memory,
                &address,
                ProgramType::Int64Pointer,
                &[Proposition::MemoryMutatesOnly {
                    before: before.clone(),
                    after: memory.clone(),
                    writes: vec![(write, 4)],
                }],
                &context,
            )
            .expect("an explicit complete-pointer frame across this fresh heap store");
            context = context.assume_proposition(equality);
            context = context.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(97_000 + index)),
                    MachineTerm::constant(7),
                ),
                true,
            );
        }
        let retained_state = intern_memory_ref(&memory);
        // A logical read keeps its name. The checked C-read producer below
        // supplies the alias-supported equation in this context.
        let proven_equal =
            crate::kernel::reasoning::memory_resolution::pointers_proven_equal_for_memory_resolution;
        let logical = logical_pointer_read(&memory, &address, &context);

        // A later projection may name the same cell by its scalar load.
        // The checked C pointer read must still denote the cached value.
        let name = canonical_form_of_load(retained_state, address.clone(), LoadKind::Int32);
        let projected = memory
            .clone()
            .materialize_named_cell(address.clone(), ProgramValue::Int32(name));
        let paths = evaluate_memory_load_paths(
            &projected,
            address.clone(),
            ProgramType::Int64Pointer,
            ExecutionFacts::new(),
            Vec::new(),
            &context,
            true,
            false,
            None,
            None,
        );
        let [path] = paths.as_slice() else {
            panic!("one C read expected");
        };
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for fact in &path.facts {
                    fact.retain_pointer_read_definition(&context);
                }
            })
        });
        samples.push((work, map_work));
        let ExpressionOutcome::Value(ProgramValue::Pointer(checked)) = &path.outcome else {
            panic!("pointer read expected");
        };
        assert!(context.pointers_known_equal(&stored, checked.pointer()));
        assert!(proven_equal(&logical, &stored, &context));
        // The producer may return the complete stored value directly. The
        // read equation, rather than literal value reflexivity, is scoped.
        let current_read = Pointer::loaded_value(&intern_memory_ref(&projected), &address);
        assert!(context.pointers_known_equal(&stored, &current_read));
        assert!(
            !empty.pointers_known_equal(&stored, &current_read),
            "a cache alias is scoped to its checked context"
        );
        let displaced = logical_pointer_read(&memory, &address.offset_by_bytes(8), &context);
        assert!(!context.pointers_known_equal(&stored, &displaced));
        let later = memory.store(
            alias.clone(),
            ProgramValue::typed_pointer(replacement.clone(), ProgramType::Int64Pointer),
        );
        let changed = logical_pointer_read(&later, &address, &context);
        let later_read = Pointer::symbolic(Variable(98_000 + count));
        context.register_checked_pointer_read(&later_read, &intern_memory_ref(&later), &address);
        assert!(proven_equal(&changed, &replacement, &context));
        assert!(!context.pointers_known_equal(&stored, &changed));
        assert!(context.pointers_known_equal(&replacement, &later_read));
        assert!(!context.pointers_known_equal(&stored, &later_read));
    }
    assert!(samples[3].0 <= samples[0].0 * 3 + 128, "{samples:?}");
    assert!(samples[3].1 <= samples[0].1 * 6 + 512, "{samples:?}");
}

#[test]
fn logical_pointer_read_queries_do_not_scan_unrelated_definitions() {
    let memory = Memory::new();
    let context = PureFactContext::new();
    let a = Pointer::symbolic(Variable(92_220));
    let b = Pointer::symbolic(Variable(92_221));
    let x = logical_pointer_read(&memory, &a, &context);
    let y = logical_pointer_read(&memory, &b, &context);
    let branch = context.assume_condition(ConditionTerm::pointer_equal(a, b), true);
    assert!(branch.pointers_known_equal(&x, &y));
    for size in [16u64, 64, 256, 1024] {
        for i in 0..size {
            logical_pointer_read(&memory, &Pointer::symbolic(Variable(93_000 + i)), &branch);
        }
        let (equal, work) =
            crate::persistent::measure_persistent_work(|| branch.pointers_known_equal(&x, &y));
        assert!(equal);
        assert!(
            work < 80 * (size.ilog2() as usize + 1),
            "size={size}, map work={work}"
        );
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            branch.pointers_known_equal(&x, &y)
        });
        assert!(equal);
        assert!(work < 40, "size={size}, work={work}");
        let ((equal, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                branch.pointers_known_equal(&x.offset_by_bytes(8), &y.offset_by_bytes(8))
            })
        });
        assert!(equal);
        assert!(
            work < 100,
            "shifted read scanned definitions: size={size}, work={work}"
        );
        assert!(
            map_work < 200 * (size.ilog2() as usize + 1),
            "shifted read copied definitions: size={size}, work={map_work}"
        );
        // Cold class lookup must resolve one newly produced term without
        // scanning the session's unrelated retained definitions.
        let address = Pointer::symbolic(Variable(94_000 + size));
        let value = logical_pointer_read(&memory, &address, &branch);
        let application = Pointer::loaded_value(&intern_memory_ref(&memory), &address);
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                let class = branch.equality_graph.address_class(&value).unwrap();
                let other = branch.equality_graph.address_class(&application).unwrap();
                assert_eq!(branch.equality_graph.address_class_root(class), other);
            })
        });
        assert!(work < 100, "size={size}, work={work}");
        assert!(
            map_work < 512 * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
    }
}

#[test]
fn stored_pointer_read_preserves_blocks_and_ignores_unrelated_cells() {
    let mut samples = Vec::new();
    for count in [16, 64, 256] {
        let context = PureFactContext::new();
        let address = Pointer::symbolic(Variable(97_001));
        let stored = Pointer::symbolic(Variable(97_002));
        let wrong = Pointer::symbolic(Variable(97_003));
        let mut memory = Memory::new();
        for index in 1..=count {
            memory = memory.store(
                address.offset_by_bytes(index * 8),
                ProgramValue::Int64(MachineTerm::int64_constant(i64::from(index))),
            );
        }
        memory = memory.store(
            address.clone(),
            ProgramValue::typed_pointer(stored.clone(), ProgramType::Int64Pointer),
        );
        let projected = memory;
        let read = Pointer::symbolic(Variable(98_000 + u64::from(count)));
        record_load_access_width(&projected, &address, 8);
        context.register_pointer_read(&read, &intern_memory(projected.clone()), &address);
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_provenance::pointer_read_has_stored_value(
                &read, &stored, &context,
            )
        });
        assert!(equal);
        assert!(
            !crate::kernel::memory_provenance::pointer_read_has_stored_value(
                &read, &wrong, &context
            )
        );
        assert!(
            !crate::kernel::memory_provenance::pointer_read_has_stored_value(
                &read.offset_by_bytes(8),
                &stored,
                &context
            )
        );
        let changed = projected
            .without_possible_aliasing_cells(&address.offset_by_bytes(4), 4, &context)
            .store(
                address.offset_by_bytes(4),
                ProgramValue::Int32(MachineTerm::constant(0)),
            );
        let changed_read = Pointer::symbolic(Variable(99_000 + u64::from(count)));
        record_load_access_width(&changed, &address, 8);
        context.register_pointer_read(&changed_read, &intern_memory(changed), &address);
        assert!(
            !crate::kernel::memory_provenance::pointer_read_has_stored_value(
                &changed_read,
                &stored,
                &context
            )
        );
        samples.push(work);
    }
    assert!(samples[2] <= samples[0] * 4 + 32, "{samples:?}");
}

/// The selected read does not scan unrelated cached cells, and a failed
/// history search stops at a fixed number of edges as history grows.
#[test]
fn recorded_pointer_normalization_has_bounded_history_work() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Pointer {
        block: "bounded-pointer-normalization".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let stored = Pointer::symbolic(Variable(99_120));
    let assumptions = PureFactContext::new();
    // The first query includes cold graph registration. Larger inputs
    // may reuse it, but must never exceed that constant work bound.
    let mut known_work = None;
    let mut missing_work = None;
    for count in [64, 256, 1024] {
        let mut memory = Memory::new().with_block("bounded-pointer-normalization", 16384);
        for index in 1..=count {
            memory = memory.store(
                address.offset_by_bytes(index * 8),
                ProgramValue::UInt64(MachineTerm::uint64_constant(u64::from(index))),
            );
        }
        let read = Pointer::symbolic(Variable(99_200 + u64::from(count)));
        record_load_access_width(&memory, &address, 8);
        assumptions.register_pointer_read(&read, &intern_memory(memory.clone()), &address);
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_provenance::pointer_read_has_recorded_value(
                &read,
                &stored,
                &assumptions,
            )
        });
        assert!(!equal);
        if let Some(previous) = missing_work {
            assert!(work <= previous, "count={count}: {work} > {previous}");
        }
        missing_work.get_or_insert(work);
        let memory = memory.store(
            address.clone(),
            ProgramValue::typed_pointer(stored.clone(), ProgramType::Int32Pointer),
        );
        let read = Pointer::symbolic(Variable(101_000 + u64::from(count)));
        record_load_access_width(&memory, &address, 8);
        let memory = intern_memory(memory);
        assumptions.register_pointer_read(&read, &memory, &address);
        for index in 0..count {
            let unrelated = Pointer::symbolic(Variable(
                120_000 + u64::from(count) * 2048 + u64::from(index),
            ));
            assumptions.register_pointer_read(&unrelated, &memory, &address);
        }
        let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::memory_provenance::pointer_read_has_recorded_value(
                &read,
                &stored,
                &assumptions,
            )
        });
        assert!(equal);
        if let Some(previous) = known_work {
            assert!(work <= previous, "count={count}: {work} > {previous}");
        }
        known_work.get_or_insert(work);
    }
}

#[test]
fn complete_pointer_domains_across_cached_observations_scale_with_new_cells() {
    let mut samples = Vec::new();
    for count in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(199_101));
        let mut memory = Memory::new();
        let ProgramValue::Pointer(original) =
            symbolic_load_value(&memory, &address, ProgramType::Int64Pointer).unwrap()
        else {
            panic!("pointer read")
        };
        let (((), work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for i in 0..count {
                    let cell = address.clone().offset_by_bytes((i * 4) as u32);
                    memory = memory
                        .clone()
                        .materialize_symbolic_cell(cell, ProgramType::Int32);
                    let ProgramValue::Pointer(read) =
                        symbolic_load_value(&memory, &address, ProgramType::Int64Pointer).unwrap()
                    else {
                        panic!("pointer read")
                    };
                    assert_eq!(read.access_designation(), original.access_designation());
                }
            })
        });
        samples.push((count, work, map_work));
    }
    for pair in samples.windows(2) {
        assert!(pair[1].1 <= pair[0].1 * 6 + 128, "{samples:?}");
        assert!(pair[1].2 <= pair[0].2 * 6 + 512, "{samples:?}");
    }
}

#[test]
fn cached_raw_pointer_names_ignore_unrelated_read_definitions() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Memory::new();
        let origin = intern_memory_ref(&base);
        for i in 0..size {
            base.symbolic_pointer_load(
                &Pointer::symbolic(Variable(990_000 + i)),
                ProgramType::Int32Pointer,
            );
        }
        let a = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(940_091)), 4),
        };
        let b = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(940_092)), 4),
        };
        let field_a = a.clone().offset_by_bytes(8);
        let field_b = b.clone().offset_by_bytes(8);
        let first = base.symbolic_pointer_load(&field_a, ProgramType::Int32Pointer);
        let second = base.symbolic_pointer_load(&field_b, ProgramType::Int32Pointer);
        let slot_a = Pointer {
            block: "local:raw-a".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let slot_b = Pointer {
            block: "local:raw-b".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = base
            .store(slot_a.clone(), first)
            .store(slot_b.clone(), second);
        let context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_value_equal(
                PointerValue::new(a, ProgramType::Int32Pointer),
                PointerValue::new(b, ProgramType::Int32Pointer),
            ),
            true,
        );
        let canonical = |field: &Pointer| {
            Pointer::loaded(&canonical_term(&MachineTerm::MemoryLoad(
                origin.clone(),
                Box::new(field.clone()),
                LoadKind::Int32,
            )))
            .unwrap()
        };
        let direct = canonical(&field_a);
        let indirect = canonical(&field_b);
        let ((equal, work), map_work) = crate::persistent::measure_persistent_work(|| {
            crate::instrumentation::measure_deterministic_work(|| {
                for slot in [&slot_a, &slot_b] {
                    evaluate_logical_memory_load_paths(
                        &memory,
                        slot.clone(),
                        ProgramType::Int32Pointer,
                        ExecutionFacts::new(),
                        Vec::new(),
                        &context,
                    );
                }
                context.equality_graph.are_equal(&direct, &indirect)
            })
        });
        assert!(equal);
        assert!(
            map_work < 2048 * (size.ilog2() as usize + 1),
            "size={size}, map work={map_work}"
        );
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 128),
        "{costs:?}"
    );
}

fn opaque_word_call_frame(size: u32) -> (Memory, PureFactContext, Pointer) {
    let input = |name| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(name)), 4),
    };
    let word = input(989_700);
    let context = PureFactContext::new()
        .allow_symbolic_contract_loads()
        .keep_spec_loads_symbolic()
        .prefer_symbolic_external_loads()
        .assume_condition(ConditionTerm::pointer_aligned(word.clone(), 8), true)
        .assume_condition(
            ConditionTerm::pointer_equal(word.clone(), Pointer::null()),
            false,
        );
    let definition = CompositeResourceDefinition::new(
        "numeric_word_slot",
        vec![crate::kernel::api::program_parameter(
            "p",
            ProgramType::UInt64Pointer,
        )],
        None,
        false,
        vec![ResourceSpec::owned_memory(MemorySegment {
            uninitialized: false,
            value_runs: Default::default(),
            base: crate::kernel::program_expression::variable("p"),
            start: crate::kernel::program_expression::int32_literal(0),
            end: crate::kernel::program_expression::int32_literal(1),
            element_width: 8,
            guard: None,
        })],
        vec![],
    );
    let mut residual = ResourceContext::new();
    for index in 0..size {
        residual = residual.unchecked_with_fact(ResourceFact::own(Resource::Composite {
            name: "numeric_word_slot".into(),
            arguments: vec![
                ProgramValue::typed_pointer(
                    input(990_000 + u64::from(index)),
                    ProgramType::UInt64Pointer,
                )
                .into(),
            ]
            .into(),
        }));
    }
    let kept = crate::kernel::primitives::CallKeptOwnership::new(
        residual,
        crate::kernel::primitives::CallKeptRanges::new(
            ResourceContext::new(),
            vec![],
            Some(std::sync::Arc::new(vec![definition])),
        ),
        &context,
    );
    let memory = Memory::new().with_call_memory_havoc(
        Variable(989_702),
        &[MemoryRange::new_with_element_width(
            input(989_701),
            0u32.into(),
            1u32.into(),
            8,
        )],
        &context,
        Some(&kept),
    );
    (memory, context, word)
}

#[test]
fn normalizing_an_opaque_word_pointer_does_not_search_unrelated_call_resources() {
    let costs = [4u32, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, context, word) = opaque_word_call_frame(size);
        // The load producer's final step creates this opaque word. Avoid
        // measuring its earlier carrier search: this regression targets the
        // subsequent normalization of the already-produced complete value.
        let value = complete_loaded_word(
            ProgramValue::UInt64(MachineTerm::Variable(Variable(989_705))),
            &memory,
            &word,
        );
        assert!(matches!(value, ProgramValue::PointerInteger(_)));
        let ProgramValue::Pointer(pointer) =
            crate::kernel::eval::expression::cast_program_value_to_type(
                value,
                ProgramType::Int32Pointer,
                IntegerConversion::Modular,
                &mut Vec::new(),
                &context,
            )
            .unwrap()
        else {
            panic!("expected pointer")
        };
        assert!(!pointer.extent_is_known());
        let context = context.assume_condition(ConditionTerm::Variable(Variable(989_703)), true);
        let (normalized, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.pointer_value_at_entry(&pointer)
        });
        assert_eq!(normalized, pointer);
        if size == 16 {
            // A full pointer premise still supplies the selected member bounds.
            let root = Pointer::symbolic(Variable(989_704));
            let bounded = PointerValue::new(root.clone(), ProgramType::Int32Pointer).with_extent(
                Some(SubobjectExtent {
                    start: root,
                    width: 4u32.into(),
                }),
            );
            let related = context.assume_condition(
                ConditionTerm::pointer_value_equal(pointer.clone(), bounded.clone()),
                true,
            );
            assert_eq!(
                related.pointer_value_at_entry(&pointer).extent(),
                bounded.extent()
            );
        }
        work
    });
    assert!(costs.iter().all(|work| *work <= costs[0] + 64), "{costs:?}");
}

#[test]
fn a_call_frame_step_queries_its_kept_range_once() {
    for size in [4u32, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let (memory, context, word) = opaque_word_call_frame(size);
        let source = intern_memory_ref(&memory);
        let derivation = source.derivation().unwrap();
        let MemoryDerivation::CallHavoc {
            kept_by_caller: Some(kept),
            ..
        } = derivation.as_ref()
        else {
            panic!("call frame")
        };
        let (range, lookup_work) = crate::instrumentation::measure_deterministic_work(|| {
            kept.range_holding(&context, None, &word, 8)
        });
        assert!(range.is_none());
        if size == 256 {
            // Keep the fixture large enough that a second range lookup
            // exceeds the step's fixed overhead allowance below.
            assert!(
                lookup_work > 512,
                "duplicated lookup must be detectable: {lookup_work}"
            );
        }
        let (effect, step_work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::resource_tracker::step_effect::affects(
                &derivation,
                &source,
                crate::kernel::resource_tracker::TrackedResource::Cell {
                    pointer: &word,
                    bytes: 8,
                },
                &crate::kernel::resource_tracker::step_effect::Evidence {
                    assumptions: &context,
                    cross_loop_havoc: true,
                },
            )
        });
        assert!(matches!(
            effect,
            crate::kernel::resource_tracker::step_effect::StepEffect::NotShownSeparate(_)
        ));
        assert!(
            step_work <= lookup_work + 512,
            "{size}: lookup {lookup_work}, step {step_work}"
        );
    }
}

/// Each read is its own load (R-mem relates the two in the equality
/// graph): an unsigned 32-bit read has a name of its own, defined by its own
/// read. Naming it after its word's `Int32` read costs no more than that
/// naming did, and the same however many unrelated cells the state
/// holds.
#[test]
fn naming_an_unsigned_32_bit_read_costs_what_naming_its_word_costs() {
    let mut samples = Vec::new();
    for size in [16_u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let mut memory = Memory::new();
        for i in 0..size {
            memory = memory.store(Pointer::symbolic(Variable(993_000 + i)), int32(7));
        }
        let memory = crate::kernel::intern_memory(memory);
        // Outside the stored cells at every size: at 1024 the stored range
        // reaches `994_000`.
        let cell = Pointer::symbolic(Variable(995_000));
        let load = |kind| MachineTerm::MemoryLoad(memory.clone(), Box::new(cell.clone()), kind);
        let ((signed, _), signed_units) =
            crate::instrumentation::measure_deterministic_work(|| {
                load_variable_for_term(&load(LoadKind::Int32)).unwrap()
            });
        let ((unsigned, definition), unsigned_units) =
            crate::instrumentation::measure_deterministic_work(|| {
                load_variable_for_term(&load(LoadKind::UInt32)).unwrap()
            });
        assert_ne!(unsigned, signed, "size {size}");
        assert_eq!(definition, load(LoadKind::UInt32), "size {size}");
        assert_eq!(
            registered_load_kind_for_variable(&unsigned),
            Some(LoadKind::UInt32)
        );
        assert_eq!(
            load_variable_for_term(&load(LoadKind::UInt32)).unwrap().0,
            unsigned,
            "size {size}"
        );
        assert!(unsigned_units <= signed_units, "size {size}");
        samples.push(unsigned_units);
    }
    assert!(
        samples.iter().all(|units| *units == samples[0]),
        "naming an unsigned read grew with unrelated cells: {samples:?}"
    );
}

#[test]
fn complete_pointer_read_definitions_scale_with_selected_reads() {
    let measure = |selected: u64, unrelated: u64| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut context = PureFactContext::new();
        for i in 0..unrelated {
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(982_000 + i * 2)),
                    Pointer::symbolic(Variable(982_001 + i * 2)),
                ),
                true,
            );
        }
        let mut queries = Vec::new();
        for i in 0..selected {
            let slot = Pointer::symbolic(Variable(983_000 + i));
            let target = Pointer::symbolic(Variable(984_000 + i));
            let stored = PointerValue::new(target.clone(), ProgramType::Int32Pointer).with_extent(
                Some(SubobjectExtent {
                    start: target,
                    width: 4u32.into(),
                }),
            );
            let memory = intern_memory_ref(
                &Memory::new().store(slot.clone(), ProgramValue::Pointer(stored.clone())),
            );
            let read = PointerValue::new(
                Pointer::version_read(&memory, &slot),
                ProgramType::Int32Pointer,
            );
            queries.push(ConditionTerm::PointerValueEqual(
                Box::new(read),
                Box::new(stored),
            ));
        }
        crate::instrumentation::measure_deterministic_work(|| {
            for query in &queries {
                assert!(context.equality_graph.knows_condition(query, true));
            }
        })
        .1
    };
    let samples: Vec<_> = [8, 16, 32, 64].into_iter().map(|n| measure(n, 0)).collect();
    for pair in samples.windows(2) {
        assert!(
            pair[1] <= pair[0] * 2 + 128,
            "complete pointer reads: {samples:?}"
        );
    }
    let unrelated: Vec<_> = [0, 16, 64, 256]
        .into_iter()
        .map(|n| measure(8, n))
        .collect();
    assert!(
        unrelated.iter().all(|work| *work <= unrelated[0] + 128),
        "unrelated facts: {unrelated:?}"
    );
}

#[test]
fn typed_pointer_read_store_frames_use_the_selected_edge_and_owners() {
    fn work(count: u32, unrelated: u64) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = Pointer::symbolic(Variable(981_100));
        let write = Pointer::symbolic(Variable(981_101));
        let own = |pointer| {
            ResourceFact::own_memory(MemoryRange::new_with_element_width(
                pointer,
                0u32.into(),
                1u32.into(),
                8,
            ))
        };
        let mut resources = ResourceContext::new()
            .unchecked_with_fact(own(slot.clone()))
            .unchecked_with_fact(own(write.clone()));
        for n in 0..unrelated {
            resources =
                resources.unchecked_with_fact(own(Pointer::symbolic(Variable(982_000 + n))));
        }
        let mut context =
            PureFactContext::new().assume_proposition(Proposition::ResourceComposition(resources));
        let mut memory = Memory::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for n in 0..count {
                let before = intern_memory_ref(&memory);
                memory = memory.clone().store(
                    write.clone(),
                    ProgramValue::UInt64(MachineTerm::uint64_constant(n.into())),
                );
                let after = intern_memory_ref(&memory);
                let source = context
                    .pointer_read_source(&after, &slot)
                    .expect("complete owned frame");
                assert_eq!(source.read_identity(), before.read_identity());
                let ProgramValue::Pointer(before_value) =
                    source.symbolic_pointer_version_load(&slot, ProgramType::Int64Pointer)
                else {
                    unreachable!()
                };
                let ProgramValue::Pointer(after_value) =
                    memory.symbolic_pointer_version_load(&slot, ProgramType::Int64Pointer)
                else {
                    unreachable!()
                };
                let fact =
                    ExecutionPureFact::logical_pointer_value_equation(before_value, after_value);
                context = context.clone().assume_execution_pure_fact(&fact);
            }
        });
        work
    }
    let chain = [4, 8, 16, 32].map(|n| work(n, 0));
    assert!(chain[0] > 0);
    assert!(
        chain.windows(2).all(|pair| pair[1] <= pair[0] * 3),
        "{chain:?}"
    );
    let ambient = [0, 16, 64, 256].map(|n| work(4, n));
    assert!(
        ambient.iter().all(|work| *work <= ambient[0] + 32),
        "{ambient:?}"
    );
}

#[test]
fn scalar_projection_congruence_scales_with_selected_versions() {
    fn work(selected: u64, unrelated: u64) -> usize {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "local:projection-scale".into(),
            offset: PointerOffsetTerm::Constant(8),
        };
        let alias = Pointer::symbolic(Variable(946_010));
        let mut facts = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(field.clone(), alias.clone()),
            true,
        );
        for i in 0..unrelated {
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(947_000 + i)),
                    (i as u32).into(),
                ),
                true,
            );
        }
        let range = MemoryRange::new_with_element_width(field.clone(), 0u32.into(), 1u32.into(), 4);
        let mut memory = Memory::new().with_block(field.block.clone(), 16);
        let mut reads = Vec::new();
        for i in 0..selected {
            memory = memory.with_call_memory_havoc(
                Variable(948_000 + i),
                std::slice::from_ref(&range),
                &facts,
                None,
            );
            let read = |address| {
                let paths = evaluate_logical_memory_load_paths(
                    &memory,
                    address,
                    ProgramType::Int32,
                    ExecutionFacts::new(),
                    vec![],
                    &facts,
                );
                let ExpressionOutcome::Value(ProgramValue::Int32(value)) = &paths[0].outcome else {
                    panic!("scalar read");
                };
                value.clone()
            };
            let pair = (read(field.clone()), read(alias.clone()));
            if let Some((previous, _)) = reads.last() {
                assert_ne!(
                    previous, &pair.0,
                    "each selected call must create a new version"
                );
            }
            reads.push(pair);
        }
        let mut graph = facts.equality_graph.clone();
        crate::instrumentation::measure_deterministic_work(|| {
            for (left, right) in reads {
                graph.add_int32_equality(&right, &42u32.into());
                assert!(graph.are_int32_equal(&left, &42u32.into()));
            }
        })
        .1
    }
    let selected: Vec<_> = [2, 8, 32, 128].into_iter().map(|n| work(n, 0)).collect();
    for pair in selected.windows(2) {
        assert!(
            pair[1] <= pair[0] * 5 + 128,
            "selected versions: {selected:?}"
        );
    }
    let unrelated: Vec<_> = [0, 16, 64, 256].into_iter().map(|n| work(4, n)).collect();
    assert!(
        unrelated.iter().all(|n| *n <= unrelated[0] + 64),
        "unrelated facts: {unrelated:?}"
    );
}

#[test]
fn symbolic_logical_wide_reads_do_not_scan_ambient_cells_or_facts() {
    let mut samples = Vec::new();
    let mut cold_samples = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let slot = Pointer::symbolic(Variable(989_970));
        let alias = Pointer::symbolic(Variable(989_971));
        let mut memory = Memory::new();
        let mut context = PureFactContext::new()
            .allow_symbolic_contract_loads()
            .prefer_symbolic_external_loads()
            .keep_spec_loads_symbolic();
        for i in 0..size {
            memory = memory.store(Pointer::symbolic(Variable(990_000 + i)), int32(7));
            context = context.assume_condition(
                ConditionTerm::equal(MachineTerm::Variable(Variable(992_000 + i)), 7u32.into()),
                true,
            );
        }
        memory = memory.store(
            slot.clone(),
            ProgramValue::UInt64(MachineTerm::uint64_constant(7)),
        );
        context = context.assume_condition(ConditionTerm::pointer_equal(slot, alias.clone()), true);
        // The first read catches up the reachable-cell index with the stores
        // constructed above. Charge that startup separately; the next read
        // uses a fresh pointer so a cached load cannot hide an ambient scan.
        let (_, cold_work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_logical_memory_load_paths(
                &memory,
                Pointer::symbolic(Variable(989_972)),
                ProgramType::UInt64,
                ExecutionFacts::new(),
                Vec::new(),
                &context,
            )
        });
        cold_samples.push(cold_work);
        let (paths, work) = crate::instrumentation::measure_deterministic_work(|| {
            evaluate_logical_memory_load_paths(
                &memory,
                alias,
                ProgramType::UInt64,
                ExecutionFacts::new(),
                Vec::new(),
                &context,
            )
        });
        let [path] = paths.as_slice() else {
            panic!("one logical read");
        };
        let ExpressionOutcome::Value(value) = &path.outcome else {
            panic!("logical value");
        };
        assert!(matches!(
            value.numeric_value(),
            ProgramValue::UInt64(MachineTerm::MemoryLoad(..))
        ));
        samples.push(work);
    }
    for pair in cold_samples.windows(2) {
        assert!(pair[1] <= 4 * pair[0] + 128, "startup: {cold_samples:?}");
    }
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 128),
        "fresh reads after startup: {samples:?}"
    );
}

#[test]
fn structural_read_definitions_scale_across_cache_only_records() {
    let mut samples = Vec::new();
    for count in [16u64, 64, 256, 1024] {
        let _session = crate::kernel::VerificationSession::enter();
        let address = Pointer::symbolic(Variable(299_101));
        let mut memory = Memory::new();
        let raw = |memory: &Memory| {
            MachineTerm::MemoryLoad(
                intern_memory_ref(memory),
                Box::new(address.clone()),
                LoadKind::Int32,
            )
        };
        let original = canonical_scalar_read(&raw(&memory));
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 1..=count {
                memory = memory.clone().materialize_symbolic_cell(
                    address.clone().offset_by_bytes((i * 4) as u32),
                    ProgramType::Int32,
                );
                let read = canonical_scalar_read(&raw(&memory));
                assert_eq!(read, original);
                assert_eq!(load_variable_registry_len(), 0);
            }
        });
        samples.push((count, work));
        let written = memory.store(address.clone(), int32(7));
        let read = canonical_form_of_load(intern_memory_ref(&written), address, LoadKind::Int32);
        assert!(matches!(read, MachineTerm::MemoryLoad(..)));
        assert_ne!(read, original);
        assert_ne!(read, MachineTerm::constant(7));
        assert_eq!(read_over_write_value(&read), Some(MachineTerm::constant(7)));
    }
    assert!(
        samples
            .windows(2)
            .all(|pair| pair[1].1 <= pair[0].1 * 6 + 128),
        "{samples:?}"
    );
}

#[test]
fn symbolic_pointer_observations_scale_with_selected_cells() {
    let mut samples = Vec::new();
    for count in [8u32, 32, 128, 512] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(299_301));
        let mut memory = Memory::new();
        // Grow unrelated stored state as well as the chain of observations.
        for i in 0..count {
            memory = memory.store(
                Pointer::symbolic(Variable(300_000 + u64::from(i))),
                int32(7),
            );
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for i in 0..count {
                let address = base.offset_by_bytes(i * 8);
                let value = symbolic_storage_cell_value(
                    &memory,
                    &address,
                    ProgramType::Int32Pointer,
                    false,
                )
                .unwrap();
                assert!(
                    cached_symbolic_storage_cell_value(
                        &memory,
                        &address,
                        ProgramType::Int32Pointer
                    ) == Some(value.clone())
                );
                memory = memory
                    .clone()
                    .materialize_symbolic_cell(address.clone(), ProgramType::Int32Pointer);
                assert!(
                    matches!(memory.load(&address), ExpressionOutcome::Value(held) if held == value)
                );
            }
        });
        assert_eq!(load_variable_registry_len(), 0);
        samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[1] <= pair[0] * 6 + 128),
        "{samples:?}"
    );
}

#[test]
fn structural_index_read_chains_have_near_linear_producer_work() {
    for (unrelated, cold) in [
        (0, false),
        (64, false),
        (256, false),
        (0, true),
        (256, true),
    ] {
        let mut samples = Vec::new();
        for size in [16, 64, 256] {
            let _session = crate::kernel::VerificationSession::enter();
            let mut memory = Memory::new();
            for index in 0..unrelated {
                memory = memory.store(
                    Pointer {
                        block: PointerBlock::Concrete(format!("unrelated{index}")),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    ProgramValue::Int32(MachineTerm::constant(0)),
                );
            }
            let memory = intern_memory(memory);
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut index = MachineTerm::constant(0);
                for _ in 0..size {
                    if cold {
                        crate::kernel::memory_provenance::clear_canonical_form_caches();
                    }
                    let mut facts = ExecutionFacts::new();
                    index = canonicalized_offset_index_term(index, &mut facts);
                    let address = Pointer {
                        block: PointerBlock::Concrete("array".into()),
                        offset: PointerOffsetTerm::scaled_int32_node(index, 4),
                    };
                    index = canonical_form_of_load(memory.clone(), address, LoadKind::Int32);
                }
            });
            eprintln!("chain size={size} unrelated={unrelated} cold={cold} work={work}");
            assert!(
                work <= 1000 * size,
                "size={size} unrelated={unrelated} work={work}"
            );
            samples.push(work);
        }
        for pair in samples.windows(2) {
            assert!(pair[1] <= 5 * pair[0], "unrelated={unrelated}: {samples:?}");
        }
    }
}

#[test]
fn immediate_pointer_store_readability_does_not_walk_history() {
    let _session = crate::kernel::VerificationSession::enter();
    let cell = Pointer {
        block: "pointer-slot".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let target = Pointer {
        block: "local:pointee".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut samples = Vec::new();
    for size in [8, 32, 128, 512] {
        let mut memory = Memory::new()
            .with_block(cell.block.clone(), 8)
            .with_block(target.block.clone(), 4);
        for i in 0..size {
            memory = memory.store(
                Pointer {
                    block: format!("unrelated-{i}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                int32(i),
            );
        }
        let written = crate::kernel::intern_memory(memory.store(
            cell.clone(),
            ProgramValue::typed_pointer(target.clone(), ProgramType::Int32Pointer),
        ));
        let read = Pointer::loaded_value(&written, &cell);
        let later = crate::kernel::intern_memory(written.memory().clone().store(
            Pointer {
                block: "other".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            int32(0),
        ));
        let cached_read = Pointer::loaded_value(&later, &cell);
        let partial =
            crate::kernel::intern_memory(written.memory().clone().store(cell.clone(), int32(0)));
        let partial_read = Pointer::loaded_value(&partial, &cell);
        let ended = later.memory().without_local_block(&target.block);
        let goal = |base: Pointer, bytes| Proposition::MemoryLoadable {
            memory: later.memory().clone(),
            base,
            bytes: MachineTerm::constant(bytes),
            wide: false,
        };
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert_eq!(
                pointer_read_over_immediate_store(&read),
                Some(target.clone())
            );
            assert!(
                crate::kernel::proof::fact_reasoning::normalizes_context_free(&goal(
                    read.clone(),
                    4
                ))
            );
            assert!(
                !crate::kernel::proof::fact_reasoning::normalizes_context_free(&goal(
                    read.clone(),
                    8
                ))
            );
            assert!(pointer_read_over_immediate_store(&cached_read).is_none());
            assert!(pointer_read_over_immediate_store(&partial_read).is_none());
            assert!(
                later.memory().read_region_identity(&read) != ended.read_region_identity(&read)
            );
            assert!(
                !crate::kernel::reasoning::path_facts::memory_range_still_available(
                    later.memory(),
                    &ended,
                    &read,
                    &PureFactContext::new(),
                )
            );
            assert!(
                !crate::kernel::proof::fact_reasoning::normalizes_context_free(
                    &Proposition::MemoryLoadable {
                        memory: ended.clone(),
                        base: read.clone(),
                        bytes: MachineTerm::constant(4),
                        wide: false,
                    },
                )
            );
            assert!(
                !crate::kernel::proof::fact_reasoning::normalizes_context_free(&goal(
                    cached_read.clone(),
                    4
                ))
            );
        });
        samples.push(work);
    }
    assert!(samples[0] > 0);
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}
