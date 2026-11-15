#[test]
fn read_validity_misses_do_not_walk_pointer_aliases() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::symbolic(Variable(880_000));
        let mut context = PureFactContext::new();
        for index in 0..size {
            context
                .equality_graph
                .add_equality(&base, &Pointer::symbolic(Variable(880_001 + index)));
        }
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(!context.has_memory_read_defined_evidence(
                    &Memory::new(),
                    &base,
                    ProgramType::Int32
                ));
            }
        });
        samples.push(work);
    }
    eprintln!("read validity alias misses: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn kept_frame_misses_do_not_walk_aliases_or_unrelated_ranges() {
    for aliases in [false, true] {
        let mut samples = Vec::new();
        for size in [8u64, 32, 128] {
            let _session = crate::kernel::VerificationSession::enter();
            let pointer = |id| Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Variable(Variable(890_000 + id)),
            };
            let query = pointer(0);
            let mut context = PureFactContext::new();
            let mut ranges = ResourceContext::new();
            for index in 1..=size {
                if aliases {
                    context = context.assume_condition(
                        ConditionTerm::pointer_equal(query.clone(), pointer(index)),
                        true,
                    );
                } else {
                    ranges = ranges.unchecked_with_fact(ResourceFact::own_memory(
                        MemoryRange::new(pointer(index), 0u32.into(), 4u32.into()),
                    ));
                }
            }
            if aliases {
                ranges = ranges.unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                    pointer(1000),
                    0u32.into(),
                    4u32.into(),
                )));
            }
            let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
                for _ in 0..4 {
                    assert!(
                        context
                            .kept_range_holding_access(&ranges, || Some(context.clone()), &query, 4)
                            .is_none()
                    );
                }
            });
            samples.push(work);
        }
        eprintln!("kept frame aliases={aliases}: {samples:?}");
        assert!(
            samples.iter().all(|work| *work <= samples[0] + 32),
            "{samples:?}"
        );
    }
}

#[test]
fn selected_read_validity_and_kept_frames_ignore_large_alias_classes() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Pointer {
            block: PointerBlock::Heap(900_000),
            offset: PointerOffsetTerm::Constant(0),
        };
        let field = source.offset_by_bytes(4);
        let memory = Memory::new()
            .with_heap_allocation_claim(source.clone(), HeapExtent::int32(16))
            .unwrap();
        let mut context =
            PureFactContext::new().assume_proposition(Proposition::MemoryReadDefined {
                memory: memory.clone(),
                pointer: field.clone(),
                value_type: ProgramType::Int32,
            });
        let mut query = source.clone();
        for index in 0..size {
            query = Pointer::symbolic(Variable(900_001 + index));
            context = context.assume_condition(
                ConditionTerm::pointer_equal(source.clone(), query.clone()),
                true,
            );
            context = context.assume_proposition(Proposition::MemoryReadDefined {
                memory: memory.clone(),
                pointer: Pointer::symbolic(Variable(910_000 + index)),
                value_type: ProgramType::Int32,
            });
        }
        let ranges = ResourceContext::new_with_equalities(&context).unchecked_with_fact(
            ResourceFact::own_memory(MemoryRange::new(source, 0u32.into(), 4u32.into())),
        );
        let query = query.offset_by_bytes(4);
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(context.has_memory_read_defined_evidence(
                    &memory,
                    &query,
                    ProgramType::Int32
                ));
                assert!(!context.has_memory_read_defined_evidence(
                    &memory,
                    &query,
                    ProgramType::UInt32
                ));
                assert!(
                    context
                        .kept_range_holding_access(&ranges, || None, &query, 4)
                        .is_some()
                );
                assert!(
                    context
                        .kept_range_holding_access(&ranges, || None, &query, 32)
                        .is_none()
                );
            }
        });
        samples.push(work);
    }
    eprintln!("selected resource alias hits and misses: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}

#[test]
fn read_validity_state_buckets_keep_exact_hits_and_bounded_misses() {
    let mut samples = Vec::new();
    for size in [8u64, 32, 128] {
        let _session = crate::kernel::VerificationSession::enter();
        let source = Pointer::symbolic(Variable(920_000));
        let other = Pointer::symbolic(Variable(920_001));
        let mut memory = Memory::new();
        let mut context = PureFactContext::new();
        for index in 0..size {
            memory = memory.store(other.clone(), ProgramValue::Int32((index as u32).into()));
            context = context.assume_proposition(Proposition::MemoryReadDefined {
                memory: memory.clone(),
                pointer: source.clone(),
                value_type: ProgramType::Int32,
            });
        }
        let missing = Memory::new();
        let (_, work) = crate::instrumentation::measure_deterministic_work(|| {
            for _ in 0..4 {
                assert!(context.has_memory_read_defined_evidence(
                    &memory,
                    &source,
                    ProgramType::Int32
                ));
                assert!(!context.has_memory_read_defined_evidence(
                    &missing,
                    &source,
                    ProgramType::Int32
                ));
            }
        });
        samples.push(work);
    }
    eprintln!("read validity state buckets: {samples:?}");
    assert!(
        samples.iter().all(|work| *work <= samples[0] + 32),
        "{samples:?}"
    );
}
