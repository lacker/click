// Deterministic work for the selected bounded pointer-value query.
use super::*;
use crate::kernel::MachineCastSpelling;

#[test]
fn bounded_pointer_value_skips_unrelated_facts_cells_and_history() {
    let mut samples = Vec::new();
    let mut wide_samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(128),
        };
        let possible_write = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(9_880_301)), 4),
        };
        let stored = Pointer::symbolic(Variable(9_880_302));
        let mut memory = Memory::new();
        let mut context = PureFactContext::new();
        for index in 0..size {
            let block = format!("local:irrelevant-{index}");
            memory = memory.with_block(block.clone(), 4).store(
                Pointer {
                    block: PointerBlock::Concrete(block),
                    offset: PointerOffsetTerm::Constant(0),
                },
                ProgramValue::Int32(MachineTerm::constant(1)),
            );
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(9_881_000 + 2 * index)),
                    Pointer::symbolic(Variable(9_881_001 + 2 * index)),
                ),
                true,
            );
        }
        memory = memory.store(
            field.clone(),
            ProgramValue::typed_pointer(stored.clone(), ProgramType::Int32Pointer),
        );
        memory =
            memory.without_possible_aliasing_cells(&possible_write, 4, &PureFactContext::new());
        let retained_state = intern_memory(memory);
        let read = Pointer::loaded_value(&retained_state, &field);
        context
            .equality_graph
            .register_pointer_read_definition(&read, &retained_state, &field);
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_read_has_recorded_value(&read, &stored, &context)
        });
        assert!(holds);
        assert!(work > 0);
        samples.push(work);
        let wide_address = field.offset_by_bytes(32);
        let write_alias = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(9_880_303)), 4),
        };
        context = context.assume_condition(
            ConditionTerm::pointer_equal(write_alias.clone(), wide_address.clone()),
            true,
        );
        let parent = Pointer::symbolic(Variable(9_880_304));
        let parent_alias = Pointer::symbolic(Variable(9_880_305));
        context = context.assume_condition(
            ConditionTerm::pointer_equal(parent.clone(), parent_alias.clone()),
            true,
        );
        let value =
            MachineTerm::PointerAddress(Box::new(parent), crate::kernel::AddressObjectClass::NONE);
        let wanted = MachineTerm::PointerAddress(
            Box::new(parent_alias),
            crate::kernel::AddressObjectClass::NONE,
        );
        let source = intern_memory(
            retained_state
                .memory()
                .clone()
                .store(write_alias, ProgramValue::UInt64(value.clone())),
        );
        let projected = canonical_projected_load_memory(&source, &wide_address);
        let wide_read =
            MachineTerm::MemoryLoad(projected, Box::new(wide_address), LoadKind::Bits64);
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            wide_read_has_recorded_value(&wide_read, &wanted, &context)
        });
        assert!(holds);
        assert!(work > 0);
        wide_samples.push(work);
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
    assert!(
        wide_samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{wide_samples:?}"
    );
}

#[test]
fn complete_read_domains_use_numeric_storage_classes_without_scanning_other_classes() {
    let costs = [4u64, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let mut facts = PureFactContext::new();
        let equal = |a: Pointer, b: Pointer| {
            ConditionTerm::uint64_equal(
                MachineTerm::pointer_address(a),
                MachineTerm::pointer_address(b),
            )
        };
        for index in 0..size {
            facts = facts.assume_condition(
                equal(
                    Pointer::symbolic(Variable(9_890_000 + index * 2)),
                    Pointer::symbolic(Variable(9_890_001 + index * 2)),
                ),
                true,
            );
        }
        let a = Pointer::symbolic(Variable(9_889_000));
        let b = Pointer::symbolic(Variable(9_889_001));
        facts = facts.assume_condition(equal(a.clone(), b.clone()), true);
        let memory = intern_memory(Memory::new());
        let left = Pointer::loaded_value(&memory, &a);
        let right = Pointer::loaded_value(&memory, &b);
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            pointer_read_designations_equal(&left, &right, &facts)
                && pointer_read_extents_equal(&left, &right, &facts)
        });
        assert!(holds);
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 128),
        "{costs:?}"
    );
}

#[test]
fn copied_pointer_frames_ignore_unrelated_separations() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let _reads = crate::kernel::TransportReadScope::enter();
        let separation = |a: Pointer, a_words: u32, b: Pointer| Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                a,
                0u32.into(),
                a_words.into(),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                b,
                0u32.into(),
                8u32.into(),
            ))),
        };
        let mut facts = PureFactContext::new();
        for index in 0..size {
            facts = facts.assume_proposition(separation(
                Pointer::symbolic(Variable(9_910_000 + index * 2)),
                4,
                Pointer::symbolic(Variable(9_910_001 + index * 2)),
            ));
        }
        let header = Pointer::symbolic(Variable(9_909_000));
        let field = header.clone().offset_by_bytes(8);
        let buffer = Pointer::symbolic(Variable(9_909_001));
        let target = Pointer::symbolic(Variable(9_909_002));
        let stored = PointerValue::new(target.clone(), ProgramType::Int32Pointer).with_extent(
            Some(SubobjectExtent {
                start: target,
                width: 4u32.into(),
            }),
        );
        let before = Memory::new().store(field.clone(), ProgramValue::Pointer(stored.clone()));
        let write = buffer.clone().offset_by_bytes(4);
        let after = before
            .clone()
            .without_possible_aliasing_cells(&write, 4, &PureFactContext::new())
            .store(write.clone(), ProgramValue::Int32(7u32.into()));
        facts = facts.assume_proposition(separation(header, 4, buffer));
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            let (read, equality) =
                explicit_pointer_store_frame(&before, &after, &field, &write, &facts).unwrap();
            let derived = facts.clone().assume_proposition(equality);
            derived.pointer_designations_match(&read, &stored)
        });
        assert!(holds);
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 128),
        "{costs:?}"
    );
}

#[test]
fn sibling_pointer_reads_stop_before_unrelated_shared_history() {
    let costs = [16u64, 64, 256, 1024].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer::symbolic(Variable(9_920_000));
        let mut memory = Memory::new().with_block("local:read-common-history", 4096);
        for index in 0..size {
            memory = memory.store(
                Pointer {
                    block: "local:read-common-history".into(),
                    offset: PointerOffsetTerm::Constant(index as i64 * 4),
                },
                ProgramValue::Int32(0u32.into()),
            );
        }
        let left = intern_memory(memory.clone().store(
            field.offset_by_bytes(8),
            ProgramValue::UInt64(MachineTerm::uint64_constant(1)),
        ));
        let right = intern_memory(memory.store(
            field.offset_by_bytes(16),
            ProgramValue::UInt64(MachineTerm::uint64_constant(2)),
        ));
        let producer = crate::kernel::equality_graph::EqualityGraph::default();
        for index in 0..size {
            producer.register_pointer_read_definition(
                &Pointer {
                    block: field.block.clone(),
                    offset: PointerOffsetTerm::scale_int32(
                        MachineTerm::Variable(Variable(9_930_000 + index)),
                        4,
                    ),
                },
                &left,
                &field.offset_by_bytes(32 + index as u32 * 8),
            );
        }
        let legacy = |memory: &SharedMemory| {
            Pointer::loaded(&MachineTerm::MemoryLoad(
                memory.clone(),
                Box::new(field.clone()),
                LoadKind::Int32,
            ))
            .unwrap()
        };
        let a = legacy(&left);
        let b = legacy(&right);
        producer.register_pointer_read_definition(&a, &left, &field);
        producer.register_pointer_read_definition(&b, &right, &field);
        let context = PureFactContext::new();
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            complete_pointer_reads_equal_across_frame(&a, &b, &context)
                && pointer_read_designations_equal(
                    &Pointer::loaded_value(&left, &field),
                    &Pointer::loaded_value(&right, &field),
                    &context,
                )
                && pointer_read_extents_equal(
                    &Pointer::loaded_value(&left, &field),
                    &Pointer::loaded_value(&right, &field),
                    &context,
                )
        });
        assert!(holds);
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 128),
        "{costs:?}"
    );
}

#[test]
fn packed_word_transport_visits_only_the_selected_word_and_delta() {
    let samples = [4u32, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "packed-scaling".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let mut memory = Memory::new().with_block("packed-scaling", 32);
        let mut context = PureFactContext::new();
        for index in 0..size {
            let name = format!("local:unrelated-packed-{index}");
            memory = memory.with_block(name.clone(), 4).store(
                Pointer {
                    block: name.into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                ProgramValue::Int32(MachineTerm::constant(index)),
            );
            context = context.assume_condition(
                ConditionTerm::pointer_equal(
                    Pointer::symbolic(Variable(9_892_000 + 2 * u64::from(index))),
                    Pointer::symbolic(Variable(9_892_001 + 2 * u64::from(index))),
                ),
                true,
            );
        }
        let before = intern_memory(memory);
        let bits =
            MachineTerm::MemoryLoad(before.clone(), Box::new(field.clone()), LoadKind::Bits64);
        let value = PointerValue::from_read(
            Pointer::integer_address(bits),
            ProgramType::VoidPointer,
            &before,
            &field,
        );
        let parent = PointerValue::new(
            Pointer::symbolic(Variable(9_891_000)),
            ProgramType::VoidPointer,
        );
        let source = Proposition::ConditionIs(
            ConditionTerm::PointerValueEqual(Box::new(value), Box::new(parent)),
            true,
        );
        context = context.assume_proposition(source.clone());
        let one_write = before.memory().clone().store(
            field.offset_by_bytes(24),
            ProgramValue::Int32(MachineTerm::constant(1)),
        );
        let (one_theorem, unrelated_work) =
            crate::instrumentation::measure_deterministic_work(|| {
                prove_program_condition_fact_transport(&source, &one_write, &context)
            });
        assert!(one_theorem.is_some());
        assert!(unrelated_work > 0);
        // The long case supplies each preservation link explicitly. A query
        // naming only the two endpoints must not discover this history.
        let (after, work) = crate::instrumentation::measure_deterministic_work(|| {
            let mut after = before.memory().clone();
            let mut current = source.clone();
            let mut explicit_context = context.clone();
            for index in 0..size {
                after = after.store(
                    field.offset_by_bytes(24),
                    ProgramValue::Int32(MachineTerm::constant(index)),
                );
                let theorem =
                    prove_program_condition_fact_transport(&current, &after, &explicit_context)
                        .expect("the supplied adjacent transition preserves the packed pointer");
                let (premises, target) = program_condition_fact_transport_parts(&theorem, &current)
                    .expect("a condition transport retains its explicit premises");
                assert!(
                    premises
                        .iter()
                        .all(|premise| explicit_context.proves_exact(premise))
                );
                current = target.clone();
                explicit_context = explicit_context.assume_proposition(current.clone());
            }
            after
        });
        assert!(
            prove_program_condition_fact_transport(&source, &after, &context).is_none(),
            "a cold endpoint query must not search the older stores"
        );
        assert!(work > 0);
        (unrelated_work, work)
    });
    assert!(
        samples
            .iter()
            .all(|(unrelated, _)| *unrelated <= samples[0].0 + 128),
        "unrelated state must not increase selected query work: {samples:?}"
    );
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1 * 5,
            "selected history must scale near-linearly: {samples:?}"
        );
    }
}

#[test]
fn converted_narrow_read_value_uses_only_selected_terms_and_cells() {
    let mut samples = Vec::new();
    for size in [4u64, 16, 64, 256] {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = Pointer::symbolic(Variable(9_889_000));
        let mut memory = Memory::new();
        let mut facts = PureFactContext::new();
        for index in 0..size {
            memory = memory.store(
                Pointer::symbolic(Variable(9_890_000 + index)),
                crate::kernel::uint8(7),
            );
            facts = facts.assume_condition(
                ConditionTerm::equal(
                    MachineTerm::Variable(Variable(9_891_000 + index)),
                    MachineTerm::constant(3),
                ),
                true,
            );
        }
        let value = MachineTerm::narrow_constant(MachineIntegerType::UInt8, 129);
        memory = memory.store(pointer.clone(), ProgramValue::UInt8(value.clone()));
        let load =
            MachineTerm::MemoryLoad(intern_memory(memory), Box::new(pointer), LoadKind::UInt8);
        let cast = |value| MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: MachineIntegerType::UInt8,
            to: MachineIntegerType::Int8,
            value: Box::new(value),
        };
        let left = cast(load.clone());
        let right = cast(value.clone());
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            narrow_read_has_recorded_value(&left, &right, &facts)
        });
        assert!(holds);
        assert!(work > 0);
        samples.push(work);
        assert!(!narrow_read_has_recorded_value(
            &left,
            &cast(MachineTerm::narrow_constant(MachineIntegerType::UInt8, 7)),
            &facts
        ));
        let other_cast = MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            from: MachineIntegerType::UInt8,
            to: MachineIntegerType::UInt16,
            value: Box::new(value),
        };
        assert!(!narrow_read_has_recorded_value(&left, &other_cast, &facts));
        let MachineTerm::MemoryLoad(memory, pointer, _) = load else {
            unreachable!()
        };
        let wide = cast(MachineTerm::MemoryLoad(memory, pointer, LoadKind::Int32));
        assert!(!narrow_read_has_recorded_value(&wide, &right, &facts));
    }
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn complete_word_record_at_bounded_stop_has_flat_lookup_work() {
    let samples = [4u64, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer {
            block: "global:word-carrier".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let context = PureFactContext::new();
        let mut memory = Memory::new();
        for index in 0..size {
            memory = memory.store(
                Pointer {
                    block: format!("local:carrier-noise-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                ProgramValue::Int32(7u32.into()),
            );
        }
        let target = Pointer::symbolic(Variable(9_887_001));
        let value = ProgramValue::PointerInteger(PointerIntegerValue {
            numeric: Box::new(ProgramValue::UInt64(MachineTerm::pointer_address(
                target.clone(),
            ))),
            pointer: Box::new(PointerValue::new(target, ProgramType::Int32Pointer)),
            kind: PointerIntegerKind::Exact,
        });
        let memory = memory
            .store(field.clone(), value.clone())
            .without_possible_aliasing_cells(&Pointer::symbolic(Variable(9_887_002)), 8, &context);
        assert!(memory.known_value(&field).is_none());
        let read = Pointer::loaded_value(&intern_memory(memory), &field);
        let (recovered, work) = crate::instrumentation::measure_deterministic_work(|| {
            complete_pointer_carrier_read_value(&read, &context)
        });
        assert_eq!(recovered, Some(value));
        assert!(work > 0);
        work
    });
    assert!(
        samples.windows(2).all(|pair| pair[0] == pair[1]),
        "{samples:?}"
    );
}

#[test]
fn complete_word_frame_reuses_named_versions_across_observations() {
    let costs = [4u32, 16, 64, 256].map(|size| {
        let _session = crate::kernel::VerificationSession::enter();
        let field = Pointer::symbolic(Variable(9_950_001));
        let write = Pointer::symbolic(Variable(9_950_002));
        let base = intern_memory(Memory::new());
        let mut observed = base.memory().clone();
        for index in 0..size {
            observed = observed.materialize_cell_from_source(
                field.offset_by_bytes(index * 8),
                ProgramType::UInt64,
                base.clone(),
            );
        }
        let before = intern_memory(observed);
        // This is the actual read producer, not a warm-up of the query:
        // its designation names the pre-observation version of the word.
        let value = PointerValue::from_read(
            Pointer::integer_address(MachineTerm::uint64_constant(8)),
            ProgramType::Int32Pointer,
            &before,
            &field,
        );
        let after = intern_memory(before.memory().clone().store(
            write.clone(),
            ProgramValue::UInt64(MachineTerm::uint64_constant(1)),
        ));
        let target = PointerValue::from_read(
            Pointer::integer_address(MachineTerm::uint64_constant(8)),
            ProgramType::Int32Pointer,
            &after,
            &field,
        );
        let range = |p| {
            Resource::Memory(MemoryRange::new_with_element_width(
                p,
                0u32.into(),
                1u32.into(),
                8,
            ))
        };
        let context = PureFactContext::new().assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(range(write)),
            right: Box::new(range(field.clone())),
        });
        let overwritten = intern_memory(
            before
                .memory()
                .clone()
                .store(field.offset_by_bytes(4), ProgramValue::UInt32(0u32.into())),
        );
        let changed = Pointer::loaded_value(&overwritten, &field);
        let (holds, work) = crate::instrumentation::measure_deterministic_work(|| {
            complete_pointer_reads_equal_across_frame(
                value.designation(),
                target.designation(),
                &context,
            ) && !complete_pointer_reads_equal_across_frame(value.designation(), &changed, &context)
        });
        assert!(holds, "observation count {size}");
        work
    });
    assert!(
        costs[0] > 0 && costs.iter().all(|work| *work <= costs[0] + 128),
        "{costs:?}"
    );
}
