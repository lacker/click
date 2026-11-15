// Deterministic scaling coverage for the independent designation index.
use super::*;
use crate::kernel::*;

#[test]
fn designation_queries_ignore_unrelated_origins() {
    let mut measurements = Vec::new();
    for size in [16u64, 64, 256, 1024] {
        let mut classes = ValueClasses::<u64>::default();
        classes.insert(&1, &2, |a, _| *a);
        classes.insert(&2, &3, |a, _| *a);
        for index in 0..size {
            classes.insert(&(10 + index * 2), &(11 + index * 2), |a, _| *a);
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(classes.equal(&1, &3));
            assert!(!classes.equal(&1, &10));
        });
        measurements.push(work);
    }
    assert!(
        measurements.iter().all(|work| *work == measurements[0]),
        "{measurements:?}"
    );
}

#[test]
fn typed_access_does_not_search_unrelated_address_equalities_or_ranges() {
    let value = |id| PointerValue::new(Pointer::symbolic(Variable(id)), ProgramType::Int32Pointer);
    let a = value(870_001);
    let b = value(870_002);
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(a.pointer().clone(), b.pointer().clone()),
            true,
        );
        let mut resources = ResourceContext::new().unchecked_with_fact(ResourceFact::view_memory(
            MemoryRange::from_pointer_value(&b, 0u32.into(), 1u32.into(), 4),
        ));
        for index in 0..size {
            let unrelated = value(880_000 + index * 2);
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    unrelated.pointer().clone(),
                    value(880_001 + index * 2).pointer().clone(),
                ),
                true,
            );
            resources = resources.unchecked_with_fact(ResourceFact::view_memory(
                MemoryRange::from_pointer_value(&unrelated, 0u32.into(), 1u32.into(), 4),
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(resources.permits_designated_memory_read(
                b.pointer(),
                Some(b.access_designation()),
                4,
                &context
            ));
            assert!(!resources.permits_designated_memory_read(
                a.pointer(),
                Some(a.access_designation()),
                4,
                &context
            ));
        });
        samples.push(work);
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
fn pointer_integer_round_trips_ignore_unrelated_facts() {
    let pointer = PointerValue::new(
        Pointer::symbolic(Variable(992_001)),
        ProgramType::Int32Pointer,
    );
    let mut samples = Vec::new();
    for size in [16u64, 64, 256] {
        let mut context = PureFactContext::new();
        for index in 0..size {
            context = context.assume_condition(
                ConditionTerm::uint64_equal(
                    MachineTerm::Variable(Variable(993_000 + index)),
                    MachineTerm::uint64_constant(index),
                ),
                true,
            );
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut obligations = Vec::new();
            let word = crate::kernel::eval::cast_program_value_to_type(
                ProgramValue::Pointer(pointer.clone()),
                ProgramType::UInt64,
                crate::kernel::eval::IntegerConversion::Modular,
                &mut obligations,
                &context,
            )
            .unwrap();
            let back = crate::kernel::eval::cast_program_value_to_type(
                word,
                ProgramType::Int32Pointer,
                crate::kernel::eval::IntegerConversion::Modular,
                &mut obligations,
                &context,
            )
            .unwrap();
            assert_eq!(back, ProgramValue::Pointer(pointer.clone()));
            assert!(obligations.is_empty());
        });
        samples.push(work);
    }
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "{samples:?}"
    );
}

#[test]
fn packed_word_contract_lookup_and_scope_ignore_unrelated_words() {
    let _session = VerificationSession::enter();
    let value = |id| PointerValue::new(Pointer::symbolic(Variable(id)), ProgramType::Int32Pointer);
    let equality = |a: &PointerValue, b: &PointerValue| {
        Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(a.clone()), Box::new(b.clone())),
            true,
        )
    };
    let reconstructed = |id| {
        let word = ProgramValue::UInt64(MachineTerm::Variable(Variable(id)))
            .complete_word(Pointer::symbolic(Variable(id + 1)));
        let value = crate::kernel::eval::cast_program_value_to_type(
            word,
            ProgramType::Int32Pointer,
            crate::kernel::eval::IntegerConversion::Modular,
            &mut Vec::new(),
            &PureFactContext::new(),
        )
        .unwrap();
        let ProgramValue::Pointer(pointer) = value else {
            panic!("pointer")
        };
        pointer
    };
    let source = reconstructed(998_000);
    let target = value(998_002);
    let relation = equality(&source, &target);
    let mut measurements = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let mut parent = PureFactContext::new();
        for index in 0..size {
            parent = parent.assume_proposition(equality(
                &reconstructed(1_000_000 + index * 4),
                &value(1_000_002 + index * 4),
            ));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(!parent.pointer_designations_match(&source, &target));
            let child = parent.clone().assume_proposition(relation.clone());
            assert!(child.pointer_designations_match(&source, &target));
            assert!(!parent.pointer_designations_match(&source, &target));
        });
        measurements.push(work);
    }
    eprintln!("packed-word selected work: {measurements:?}");
    assert!(
        measurements
            .iter()
            .all(|work| *work <= measurements[0] + 32),
        "{measurements:?}"
    );
}

#[test]
fn recent_pointer_read_origin_avoids_older_alias_histories() {
    use crate::kernel::primitives::{CallKeptOwnership, CallKeptRanges};
    let mut samples = Vec::new();
    for size in [16u64, 64, 256] {
        let _session = VerificationSession::enter();
        let cell = |name: String| Pointer {
            block: name.into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let selected = cell("zz-recent-pointer-origin".into());
        let mut memory = Memory::new().with_block(selected.block.clone(), 8);
        let mut older = Vec::new();
        for index in 0..size {
            let pointer = cell(format!("older-pointer-origin-{index:04}"));
            memory = memory.with_block(pointer.block.clone(), 8);
            older.push(pointer);
        }
        let before = intern_memory_ref(&memory);
        let read = |retained_state: &SharedMemory, pointer: &Pointer| {
            PointerValue::from_read(
                Pointer::loaded_value(retained_state, pointer),
                ProgramType::Int32Pointer,
                retained_state,
                pointer,
            )
        };
        let value = PointerValue::new(
            Pointer::symbolic(Variable(994_001)),
            ProgramType::Int32Pointer,
        );
        let fact = |pointer: &Pointer| {
            Proposition::ConditionIs(
                ConditionTerm::PointerValueEqual(
                    Box::new(read(&before, pointer)),
                    Box::new(value.clone()),
                ),
                true,
            )
        };
        let mut context = PureFactContext::new();
        for pointer in &older {
            context = context.assume_proposition(fact(pointer));
        }
        let missing = context.clone();
        let selected_fact = fact(&selected);
        context = context.assume_proposition(selected_fact);
        let range = MemoryRange::new(selected.clone(), 0u32.into(), 2u32.into());
        let kept = CallKeptOwnership::new(
            ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(range.clone())),
            CallKeptRanges::new(ResourceContext::new(), vec![], None),
            &context,
        );
        let writes = [MemoryRange::new(
            Pointer::symbolic(Variable(994_002)),
            0u32.into(),
            1u32.into(),
        )];
        let after =
            memory.with_call_memory_havoc(Variable(994_003), &writes, &context, Some(&kept));
        let separation = Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(writes[0].clone())),
            right: Box::new(Resource::Memory(range)),
        };
        let frame_context = PureFactContext::new().assume_proposition(
            crate::kernel::region_footprint::byte_premise(&separation).unwrap(),
        );
        let (_, _, preservation) = crate::kernel::tests::explicit_frame(
            &before,
            &after,
            &selected,
            ProgramType::Int32Pointer,
            &[Proposition::MemoryEffectSummary {
                before: before.memory().clone(),
                after: after.clone(),
                mutable_ranges: writes.to_vec(),
            }],
            &frame_context,
        )
        .expect("the explicitly separated call preserves the selected pointer");
        let context = context.assume_proposition(preservation.clone());
        let missing = missing.assume_proposition(preservation);
        let target = read(&intern_memory_ref(&after), &selected);
        let (matched, work) = crate::instrumentation::measure_deterministic_work(|| {
            context.pointer_designations_match(&target, &value)
        });
        assert!(matched);
        samples.push(work);
        assert!(!missing.pointer_designations_match(&target, &value));
        let overwritten = after.store(selected.clone(), ProgramValue::UInt32(0u32.into()));
        let partial = read(&intern_memory_ref(&overwritten), &selected);
        assert!(!context.pointer_designations_match(&partial, &value));
    }
    eprintln!("recent pointer origin work: {samples:?}");
    assert!(
        samples.iter().all(|work| *work == samples[0]),
        "older aliases were searched: {samples:?}"
    );
}
