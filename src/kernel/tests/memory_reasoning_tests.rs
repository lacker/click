use super::*;

#[test]
fn structural_range_offset_precedes_proof_aware_pointer_resolution() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(93_301))),
            byte_width: 4,
        },
    };
    let required = memory_range(
        base.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        0,
        1,
    );
    let assumptions = PureFactContext::new();
    PureFactContext::reset_proof_aware_pointer_index_queries();

    assert!(assumptions.range_covered_by_fact_range(
        &required,
        &base,
        &Bitvector32Term::Constant(0),
        &Bitvector32Term::Constant(8),
    ));
    assert_eq!(PureFactContext::proof_aware_pointer_index_queries(), 0);
}

#[test]
fn safe_positive_subtraction_is_below_its_base() {
    let x = Bitvector32Term::Variable(Variable(87));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(x.clone(), Bitvector32Term::Constant(1)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::subtract(x.clone(), Bitvector32Term::Constant(1)),
            x,
        )),
        Some(true)
    );
}

#[test]
fn mutable_frame_proves_unwritten_load_equal_across_stack_locals() {
    let i = Variable(74);
    let i_bits = Bitvector32Term::Variable(i);
    let old_memory = CMemory::new();
    let loop_entry_memory = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(1));
    let loop_exit_memory = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(i_bits.clone()));
    let first_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(i_bits.clone()),
            byte_width: 4,
        },
    };
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits, Bitvector32Term::Constant(1)),
            true,
        )
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: loop_entry_memory,
            after: loop_exit_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(loop_exit_memory),
                Box::new(first_cell.clone()),
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(old_memory),
                Box::new(first_cell)
            ),
        ),
        true,
    )));
}

#[test]
fn mutable_frame_transports_load_across_certified_effect_chain() {
    let preserved = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let first_write = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let second_write = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(8),
    };
    let before = CMemory::new();
    let middle = before.clone().store(first_write.clone(), int32(1));
    let after = middle.clone().store(second_write.clone(), int32(2));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: before.clone(),
            after: middle.clone(),
            pointers: vec![first_write],
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: middle,
            after: after.clone(),
            pointers: vec![second_write],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after),
                Box::new(preserved.clone())
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before),
                Box::new(preserved)
            ),
        ),
        true,
    )));
}

#[test]
fn loadability_transports_across_long_certified_effect_chain() {
    let loadable = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let before = CMemory::new();
    let mut after = before.clone();
    let mut assumptions = PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
        memory: before,
        base: loadable.clone(),
        bytes: Bitvector32Term::Constant(4),
    });
    for value in 0..12 {
        let next = after.clone().store(written.clone(), int32(value));
        assumptions = assumptions.assume_proposition(Proposition::CMemoryMutatesOnly {
            before: after,
            after: next.clone(),
            pointers: vec![written.clone()],
        });
        after = next;
    }

    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: after,
        base: loadable,
        bytes: Bitvector32Term::Constant(4),
    }));
}

#[test]
fn target_directed_transport_preserves_pointer_field_across_disjoint_buffer_write() {
    let base = Bitvector32Term::Variable(Variable(90_001));
    let buffer = Bitvector32Term::Variable(Variable(90_002));
    let index = Bitvector32Term::Variable(Variable(90_003));
    let field_pointer = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(base.clone(), 4),
            PointerOffsetTerm::Constant(8),
        ),
    };
    let written_pointer = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(buffer, 4),
            PointerOffsetTerm::scale_int32(index, 4),
        ),
    };
    let old_memory = CMemory::new();
    let current_memory = old_memory.clone().store(written_pointer.clone(), int32(7));
    let old_offset = PointerOffsetTerm::scale_int32(
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(old_memory),
            Box::new(field_pointer.clone()),
        ),
        4,
    );
    let current_offset = PointerOffsetTerm::scale_int32(
        Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(current_memory),
            Box::new(field_pointer.clone()),
        ),
        4,
    );
    let assumptions = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
        left: CResource::Memory(memory_range(field_pointer, 0, 1)),
        right: CResource::Memory(memory_range(written_pointer, 0, 1)),
    });
    let source = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let target = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(current_offset, old_offset),
        true,
    );

    prove_c_condition_fact_target_transport(&source, &target, &assumptions)
        .expect("an explicit frame should preserve the pointer-valued field load");
}

#[test]
fn unrelated_external_cell_store_preserves_memory_load_with_stack_temporary() {
    let old_memory = CMemory::new();
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p1 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let stack_memory = CMemory::new()
        .with_block("local:tmp", 4)
        .store(CMemory::local_pointer("tmp"), int32(0));
    let current_memory = stack_memory.clone().store(
        p0.clone(),
        int32(Bitvector32Term::MemoryLoad(
            crate::kernel::intern_c_memory(stack_memory),
            Box::new(p0),
        )),
    );

    assert!(PureFactContext::new().proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(current_memory),
                Box::new(p1.clone())
            ),
            Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(old_memory), Box::new(p1)),
        ),
        true,
    )));
}

#[test]
fn target_directed_transport_preserves_one_old_load_spelling() {
    let old_memory = CMemory::new();
    let written = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let preserved = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let current_memory = old_memory.clone().store(written, int32(7));
    let old_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(old_memory),
        Box::new(preserved.clone()),
    );
    let current_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(current_memory),
        Box::new(preserved),
    );
    let source = Proposition::ConditionIs(
        ConditionTerm::equal(old_load.clone(), old_load.clone()),
        true,
    );
    let target = Proposition::ConditionIs(ConditionTerm::equal(current_load, old_load), true);

    let theorem =
        prove_c_condition_fact_target_transport(&source, &target, &PureFactContext::new())
            .expect("the disjoint store should preserve one side of the target equality");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(Box::new(source), Box::new(target))
    );
}

#[test]
fn exact_changed_cell_frame_precedes_abstract_effect_search() {
    let queried = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(40_000)), 4),
    };
    let materialized = Pointer {
        block: queried.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(40_001)), 4),
    };
    let before = CMemory::new().with_block("call-havoc:0", 0);
    let after = before.clone().store(materialized.clone(), int32(7));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
        left: CResource::Memory(memory_range(queried.clone(), 0, 1)),
        right: CResource::Memory(memory_range(materialized, 0, 1)),
    });

    assert!(c_memory_load_is_unchanged(
        &before,
        &after,
        &queried,
        &assumptions,
    ));
}

#[test]
fn exact_separation_resolves_contained_symbolic_ranges_without_general_search() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(41_000)), 4),
    };
    let data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(41_001)), 4),
    };
    let length = Bitvector32Term::Variable(Variable(41_002));
    let owner_range = memory_range(owner.clone(), 0, 4);
    let data_range = memory_range(data.clone(), 0, length.clone());
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(owner_range.clone()),
            right: CResource::Memory(data_range.clone()),
        })
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        ));
    let owner_field = memory_range(owner.offset_by_int32_elements(2.into()), 0, 1);
    let data_cell = memory_range(data.clone(), 0, 1);

    assert!(
        assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &owner_field,
            &data_cell,
        )
    );

    let memory = CMemory::new().with_block("call-havoc:0", 0);
    let data_field = owner.offset_by_int32_elements(2.into());
    let loaded_data_offset = PointerOffsetTerm::scale_int32(
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(memory), Box::new(data_field)),
        4,
    );
    let loaded_data = Pointer {
        block: data.block.clone(),
        offset: loaded_data_offset.clone(),
    };
    let assumptions = assumptions
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(loaded_data_offset, data.offset.clone()),
            true,
        ))
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), length),
            true,
        ));
    let owner_len_field = memory_range(owner.offset_by_int32_elements(1.into()), 0, 1);
    let second_data_cell = memory_range(loaded_data, 1, 2);
    assert!(
        assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &owner_len_field,
            &second_data_cell,
        )
    );
}

#[test]
fn direct_resource_match_uses_exact_field_load_equalities() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = CMemory::new().with_block("call-havoc:0", 0);
    let loaded_data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(owner.offset_by_int32_elements(2.into())),
            ),
            4,
        ),
    };
    let loaded_length = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory),
        Box::new(owner.offset_by_int32_elements(1.into())),
    );
    let named_data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(41_100)), 4),
    };
    let named_length = Bitvector32Term::Variable(Variable(41_101));
    let loaded = CResource::Memory(memory_range(loaded_data.clone(), 0, loaded_length.clone()));
    let named = CResource::Memory(memory_range(named_data.clone(), 0, named_length.clone()));

    assert!(!c_resources_directly_match(
        &loaded,
        &named,
        &PureFactContext::new()
    ));

    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_offset_equal(loaded_data.offset, named_data.offset),
            true,
        )
        .assume_condition(ConditionTerm::equal(loaded_length, named_length), true);
    assert!(c_resources_directly_match(&loaded, &named, &assumptions));
}

#[test]
fn direct_composite_resource_match_replays_pointer_load_across_block_declaration() {
    if skip_without_memory_dag() {
        return;
    }
    let entry = CMemory::new().with_block("arg-memory", 32);
    let field = arc_pointer(16);
    let later = entry.clone().with_block("local:pivot", 4);
    let resource_at = |memory: CMemory| CResource::Composite {
        name: "tree".to_string(),
        arguments: vec![CValue::Pointer(Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(memory),
                    Box::new(field.clone()),
                ),
                4,
            ),
        })],
    };

    assert!(c_resources_directly_match(
        &resource_at(entry),
        &resource_at(later),
        &PureFactContext::new(),
    ));
}

#[test]
fn memory_separation_candidates_ignore_unrelated_propositions() {
    let left = Pointer {
        block: "indexed-left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "indexed-right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut assumptions =
        PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(left.clone(), 0, 1)),
            right: CResource::Memory(memory_range(right.clone(), 0, 1)),
        });
    for index in 0..128 {
        assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::Variable(Variable(93_000 + index)),
                Bitvector32Term::Constant(index as u32),
            ),
            true,
        ));
    }

    assert_eq!(
        assumptions.memory_separation_candidate_count(&left.block, &right.block),
        1
    );
    assert!(assumptions.pointers_proven_disjoint_by_range(&left, &right));

    PureFactContext::reset_memory_separation_candidate_checks();
    assert!(
        assumptions.pointers_proven_disjoint_by_explicit_range_for_memory_resolution(&left, &right)
    );
    assert_eq!(PureFactContext::memory_separation_candidate_checks(), 1);
}

#[test]
fn memory_loadable_candidates_ignore_unrelated_pointer_blocks() {
    let memory = CMemory::new();
    let target = Pointer {
        block: "indexed-loadable-target".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut assumptions = PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: target.clone(),
        bytes: Bitvector32Term::Constant(8),
    });
    for index in 0..128 {
        assumptions = assumptions.assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: Pointer {
                block: format!("indexed-loadable-unrelated-{index}").into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(4),
        });
    }

    assert_eq!(
        assumptions.memory_loadable_candidate_count(&target.block),
        1
    );
    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory,
        base: target,
        bytes: Bitvector32Term::Constant(4),
    }));
}

#[test]
fn memory_loadable_query_ignores_same_block_unrelated_pointer_shapes() {
    let memory = CMemory::new();
    let target = Pointer {
        block: "indexed-loadable-shapes".into(),
        offset: PointerOffsetTerm::Constant(10_000),
    };
    let samples = [16, 32, 64, 128]
        .into_iter()
        .map(|size| {
            let mut assumptions =
                PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: target.clone(),
                    bytes: Bitvector32Term::Constant(8),
                });
            for index in 0..size {
                assumptions = assumptions.assume_proposition(Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: Pointer {
                        block: target.block.clone(),
                        offset: PointerOffsetTerm::Constant(index as i64),
                    },
                    bytes: Bitvector32Term::Constant(4),
                });
            }
            let (proved, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.proves(&Proposition::CMemoryLoadable {
                    memory: memory.clone(),
                    base: target.clone(),
                    bytes: Bitvector32Term::Constant(4),
                })
            });
            assert!(proved);
            (size, work)
        })
        .collect::<Vec<_>>();

    assert!(
        samples.windows(2).all(|pair| pair[1].1 <= pair[0].1 + 1),
        "fixed loadability query should not inspect unrelated pointer shapes: {samples:?}"
    );
}

#[test]
fn equivalent_memory_load_order_facts_can_be_inconsistent() {
    let old_memory = CMemory::new();
    let stack_memory = CMemory::new()
        .with_block("local:tmp", 4)
        .store(CMemory::local_pointer("tmp"), int32(0));
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let old_p0 = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(old_memory),
        Box::new(p0.clone()),
    );
    let stack_p0 =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(stack_memory), Box::new(p0));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(old_p0.clone(), stack_p0.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(stack_p0, old_p0), true);

    assert!(assumptions.proves(&false_equals_true_proposition()));
}

#[test]
fn equivalent_condition_facts_with_different_truth_values_are_inconsistent() {
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p1 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let memory_a = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(0));
    let memory_b = CMemory::new()
        .with_block("local:i", 4)
        .store(CMemory::local_pointer("i"), int32(1));
    let left_a = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory_a.clone()),
        Box::new(p0.clone()),
    );
    let right_a = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory_a),
        Box::new(p1.clone()),
    );
    let left_b = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory_b.clone()),
        Box::new(p0),
    );
    let right_b =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(memory_b), Box::new(p1));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_than(left_a, right_a), true)
        .assume_condition(ConditionTerm::signed_less_than(left_b, right_b), false);

    assert!(assumptions.proves(&false_equals_true_proposition()));
}

#[test]
fn disjoint_range_proves_mutable_frame_cell_distinct() {
    let i = Variable(81);
    let j = Variable(82);
    let i_bits = Bitvector32Term::Variable(i);
    let j_bits = Bitvector32Term::Variable(j);
    let before_memory = CMemory::new();
    let after_memory = CMemory::new();
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(i_bits.clone()),
            byte_width: 4,
        },
    };
    let read_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(j_bits.clone()),
            byte_width: 4,
        },
    };
    let i_plus_one = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let j_plus_one = Bitvector32Term::Add(
        Box::new(j_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(i_bits.clone(), i_plus_one.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j_bits.clone(), j_plus_one.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: base.clone(),
            left_start: i_bits.clone(),
            left_end: i_plus_one,
            right_base: base,
            right_start: j_bits.clone(),
            right_end: j_plus_one,
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: before_memory.clone(),
            after: after_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after_memory),
                Box::new(read_cell.clone())
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before_memory),
                Box::new(read_cell)
            ),
        ),
        true,
    )));
}

#[test]
fn disjoint_ranges_frame_metadata_across_symbolic_index_store() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(83)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(84)), 4),
    };
    let index = Bitvector32Term::Variable(Variable(85));
    let capacity = Bitvector32Term::Variable(Variable(86));
    let metadata_cell = owner.clone();
    let written_cell = data.offset_by_int32_elements(index.clone());
    let before_memory = CMemory::new();
    let after_memory = before_memory.clone().store(written_cell.clone(), int32(7));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index, capacity.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: owner,
            left_start: Bitvector32Term::Constant(0),
            left_end: Bitvector32Term::Constant(4),
            right_base: data,
            right_start: Bitvector32Term::Constant(0),
            right_end: capacity,
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: before_memory.clone(),
            after: after_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after_memory),
                Box::new(metadata_cell.clone()),
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before_memory),
                Box::new(metadata_cell)
            ),
        ),
        true,
    )));
}

#[test]
fn equivalent_field_derived_bases_frame_symbolic_index_store() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(87)), 4),
    };
    let owner_data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let base_memory = CMemory::new();
    let execution_memory = base_memory
        .clone()
        .with_block("local:data", 8)
        .store(CMemory::local_pointer("data"), int32(0));
    let resource_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(base_memory.clone()),
                Box::new(owner_data_cell.clone()),
            ),
            4,
        ),
    };
    let execution_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(execution_memory.clone()),
                Box::new(owner_data_cell),
            ),
            4,
        ),
    };
    let index = Bitvector32Term::Variable(Variable(88));
    let capacity = Bitvector32Term::Variable(Variable(89));
    let metadata_cell = owner.clone();
    let written_cell = execution_data.offset_by_int32_elements(index.clone());
    let after_memory = execution_memory
        .clone()
        .store(written_cell.clone(), int32(7));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index, capacity.clone()),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                resource_data,
                Bitvector32Term::Constant(0),
                capacity,
            )),
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: execution_memory.clone(),
            after: after_memory.clone(),
            pointers: vec![written_cell],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after_memory),
                Box::new(metadata_cell.clone()),
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(execution_memory),
                Box::new(metadata_cell)
            ),
        ),
        true,
    )));
}

#[test]
fn direct_transport_composes_framed_loads_inside_an_indexed_address() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(95)), 4),
    };
    let owner_len_cell = owner.clone();
    let owner_data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let before = CMemory::new();
    let data_value = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(owner_data_cell),
    );
    let length = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(owner_len_cell),
    );
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data_value, 4),
    };
    let index = Bitvector32Term::Variable(Variable(96));
    let capacity = Bitvector32Term::Variable(Variable(97));
    let written_cell = data.offset_by_int32_elements(index.clone());
    let terminator_cell = data.offset_by_int32_elements(length.clone());
    let after = before.clone().store(written_cell.clone(), int32(7));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(terminator_cell),
            ),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_than(index, length), true)
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                data,
                Bitvector32Term::Constant(0),
                capacity,
            )),
        })
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before,
            after: after.clone(),
            pointers: vec![written_cell],
        });

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("the address loads and then the indexed cell should transport");
    let Proposition::Implies(source, target) = theorem.proposition() else {
        panic!("transport theorem must be an implication");
    };
    assert_eq!(source.as_ref(), &fact);
    assert_ne!(target.as_ref(), &fact);
    assert_eq!(c_condition_fact_memories(target), vec![after]);
}

#[test]
fn direct_transport_rewrites_loads_inside_pointer_equality() {
    let before = CMemory::new();
    let field_cell = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(8),
    };
    let field_value = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(field_cell.clone()),
            ),
            4,
        ),
    };
    let local_value = Pointer {
        block: PointerBlock::Symbolic(Variable(110)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(field_value, local_value.clone()),
        true,
    );
    let after = before.clone().with_block("local:result", 8);

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &PureFactContext::new())
        .expect("an unrelated local-memory change should transport a pointer-valued field load");
    let Proposition::Implies(source, target) = theorem.proposition() else {
        panic!("transport theorem must be an implication");
    };
    assert_eq!(source.as_ref(), &fact);
    let transported_field_value = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after),
                Box::new(field_cell),
            ),
            4,
        ),
    };
    assert_eq!(
        target.as_ref(),
        &Proposition::ConditionIs(
            ConditionTerm::pointer_equal(transported_field_value, local_value),
            true,
        )
    );
}

#[test]
fn direct_transport_rewrites_loads_inside_signed_add_overflow_guard() {
    let before = CMemory::new();
    let field = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let loaded = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(field.clone()),
    );
    let fact = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(loaded, Bitvector32Term::Constant(1)),
        false,
    );
    let after = before.clone().with_block("local:result", 4);

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &PureFactContext::new())
        .expect("an unrelated local allocation should transport an arithmetic definedness guard");
    let Proposition::Implies(source, target) = theorem.proposition() else {
        panic!("transport theorem must be an implication");
    };
    assert_eq!(source.as_ref(), &fact);
    assert_eq!(c_condition_fact_memories(target), vec![after]);
}

#[test]
fn pointer_equality_composes_across_same_block_offset_equalities() {
    let final_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(120)),
    };
    let snapshot_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(121)),
    };
    let local_pointer = Pointer {
        block: PointerBlock::Symbolic(Variable(122)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_offset_equal(
                final_pointer.offset.clone(),
                snapshot_pointer.offset.clone(),
            ),
            true,
        )
        .assume_condition(
            ConditionTerm::pointer_equal(snapshot_pointer, local_pointer.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::pointer_equal(local_pointer, Pointer::null()),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::pointer_equal(
            final_pointer,
            Pointer::null()
        )),
        Some(true)
    );
}

#[test]
fn explicit_separation_contains_one_element_under_a_positive_length() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(98)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(99)), 4),
    };
    let length = Bitvector32Term::Variable(Variable(100));
    let owner_range = CMemoryRange::new(
        owner,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(6),
    );
    let data_range = CMemoryRange::new(data, Bitvector32Term::Constant(0), length.clone());
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(Bitvector32Term::Constant(0), length),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(owner_range.clone()),
            right: CResource::Memory(data_range.clone()),
        });

    assert!(
        assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &CMemoryRange::new(
                data_range.base().clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            ),
            &CMemoryRange::new(
                owner_range.base().clone(),
                Bitvector32Term::Constant(1),
                Bitvector32Term::Constant(2),
            ),
        )
    );
}

#[test]
fn direct_separation_contains_zero_under_a_constant_lower_bound() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(104)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(105)), 4),
    };
    let length = Bitvector32Term::Variable(Variable(106));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                data.clone(),
                Bitvector32Term::Constant(0),
                length,
            )),
        });

    assert!(assumptions.ranges_directly_disjoint_from_pointer(
        &[CMemoryRange::new(
            owner,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
        &data,
    ));
}

#[test]
fn constant_field_offset_is_disjoint_from_earlier_constant_range() {
    let base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(101)), 4),
    };
    let first_field = CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    );
    let third_field = base.offset_by_int32_elements(Bitvector32Term::Constant(2));

    assert!(
        PureFactContext::new().ranges_proven_disjoint_from_pointer(&[first_field], &third_field)
    );
}

#[test]
fn bounded_separation_uses_order_fact_across_equivalent_snapshots() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(102)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(103)), 4),
    };
    let len_cell = owner.clone();
    let cap_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let plain = CMemory::new();
    let cached = CMemory::new().store(
        Pointer {
            block: "local:cache".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        int32(0),
    );
    let query_len = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(plain.clone()),
        Box::new(len_cell.clone()),
    );
    let query_cap = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(plain),
        Box::new(cap_cell.clone()),
    );
    let fact_len = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(cached.clone()),
        Box::new(len_cell),
    );
    let fact_cap =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(cached), Box::new(cap_cell));
    let owner_range = CMemoryRange::new(
        owner.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(4),
    );
    let owned_data_range = CMemoryRange::new(data.clone(), Bitvector32Term::Constant(0), query_cap);
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_equal(fact_len, fact_cap), true)
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(owner_range),
            right: CResource::Memory(owned_data_range),
        });

    assert!(assumptions.ranges_proven_disjoint_from_pointer(
        &[CMemoryRange::new(
            data,
            Bitvector32Term::Constant(0),
            query_len,
        )],
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
    ));
}

#[test]
fn covering_disjoint_fact_handles_shifted_mutable_range() {
    let n = Variable(83);
    let k = Variable(84);
    let n_bits = Bitvector32Term::Variable(n);
    let k_bits = Bitvector32Term::Variable(k);
    let before_memory = CMemory::new();
    let after_memory = CMemory::new();
    let dst_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(85)), 4),
    };
    let src_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(86)), 4),
    };
    let src_cell = src_base.offset_by_int32_elements(k_bits.clone());
    let shifted_dst = dst_base.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(k_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k_bits, n_bits.clone()),
            true,
        )
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: dst_base,
            left_start: Bitvector32Term::Constant(0),
            left_end: n_bits.clone(),
            right_base: src_base,
            right_start: Bitvector32Term::Constant(0),
            right_end: n_bits.clone(),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before: before_memory.clone(),
            after: after_memory.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                shifted_dst,
                Bitvector32Term::Constant(0),
                Bitvector32Term::subtract(n_bits, Bitvector32Term::Constant(1)),
            )],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after_memory),
                Box::new(src_cell.clone())
            ),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before_memory),
                Box::new(src_cell)
            ),
        ),
        true,
    )));
}

#[test]
fn atomic_condition_fact_transport_uses_certified_effect_summary() {
    let before = CMemory::new()
        .with_block("stable", 4)
        .with_block("mutated", 4);
    let after = before.clone().with_block("call-havoc:0", 0);
    let stable = Pointer {
        block: "stable".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mutated = Pointer {
        block: "mutated".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(stable.clone()),
            ),
            Bitvector32Term::Constant(7),
        ),
        true,
    );
    let assumptions =
        PureFactContext::new().assume_proposition(Proposition::CMemoryEffectSummary {
            before: before.clone(),
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                mutated,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_transport(&fact, &after, &assumptions)
        .expect("the framed load should transport");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(after),
                        Box::new(stable)
                    ),
                    Bitvector32Term::Constant(7),
                ),
                true,
            )),
        )
    );
}

#[test]
fn memory_load_equality_does_not_ignore_loop_havoc_identity() {
    let before = CMemory::new();
    let after = before.clone().with_block("havoc:0", 0);
    let pointer = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let equality = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after),
                Box::new(pointer.clone()),
            ),
            Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(before), Box::new(pointer)),
        ),
        true,
    );

    assert!(
        !PureFactContext::new().proves(&equality),
        "a havoced snapshot requires explicit frame evidence"
    );
}

#[test]
fn atomic_condition_fact_transport_ignores_distinct_materialized_cell() {
    let before = CMemory::new()
        .with_block("arg-memory", 8)
        .with_block("call-havoc:0", 0);
    let preserved = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let materialized = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let after = before
        .clone()
        .store(materialized, CValue::Int32(Bitvector32Term::Constant(9)));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(preserved.clone()),
            ),
            Bitvector32Term::Constant(7),
        ),
        true,
    );

    let theorem = prove_c_condition_fact_transport(&fact, &after, &PureFactContext::new())
        .expect("a distinct materialized cell must not change the framed load");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(after),
                        Box::new(preserved)
                    ),
                    Bitvector32Term::Constant(7),
                ),
                true,
            )),
        )
    );
}

#[test]
fn atomic_condition_fact_transport_preserves_pointer_offset_equality() {
    let before = CMemory::new()
        .with_block("stable", 4)
        .with_block("mutated", 4);
    let after = before.clone().with_block("call-havoc:0", 0);
    let stable = Pointer {
        block: "stable".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mutated = Pointer {
        block: "mutated".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let expected = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(345)), 4);
    let fact = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::scale_int32(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(before.clone()),
                    Box::new(stable.clone()),
                ),
                4,
            ),
            expected.clone(),
        ),
        true,
    );
    let assumptions =
        PureFactContext::new().assume_proposition(Proposition::CMemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                mutated,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_transport(&fact, &after, &assumptions)
        .expect("the framed pointer-valued field should transport");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(
                    PointerOffsetTerm::scale_int32(
                        Bitvector32Term::MemoryLoad(
                            crate::kernel::intern_c_memory(after),
                            Box::new(stable)
                        ),
                        4,
                    ),
                    expected,
                ),
                true,
            )),
        )
    );
}

#[test]
fn equality_fact_matching_transports_both_pointer_offset_endpoints() {
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let local = Pointer {
        block: "local:value".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new()
        .with_block("arg-memory", 8)
        .with_block("local:value", 4);
    let after = before
        .clone()
        .store(local, CValue::Int32(Bitvector32Term::Constant(7)));
    let load_offset = |memory: &CMemory, pointer: &Pointer| {
        PointerOffsetTerm::scale_int32(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(pointer.clone()),
            ),
            4,
        )
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            load_offset(&before, &left),
            load_offset(&before, &right),
        ),
        true,
    );
    let target = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            load_offset(&after, &left),
            load_offset(&after, &right),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(fact);

    assert!(assumptions.proves(&target));
}

#[test]
fn memory_load_equality_combines_equal_pointer_base_and_zero_index() {
    let memory = CMemory::new().with_block("arg-memory", 64);
    let owner = Bitvector32Term::Variable(Variable(90));
    let data = Bitvector32Term::Variable(Variable(91));
    let owner_offset = PointerOffsetTerm::scale_int32(owner, 4);
    let data_field = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(owner_offset.clone(), PointerOffsetTerm::Constant(8)),
    };
    let pos_field = Pointer {
        block: "arg-memory".into(),
        offset: owner_offset,
    };
    let data_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(data_field),
    );
    let pos_load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(pos_field),
    );
    let indexed = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_load.clone(), 4),
            PointerOffsetTerm::scale_int32(pos_load.clone(), 4),
        ),
    };
    let direct = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data.clone(), 4),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(
                PointerOffsetTerm::scale_int32(data_load, 4),
                PointerOffsetTerm::scale_int32(data, 4),
            ),
            true,
        ))
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(pos_load, Bitvector32Term::Constant(0)),
            true,
        ));
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory.clone()),
                Box::new(indexed),
            ),
            Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(memory), Box::new(direct)),
        ),
        true,
    );

    assert!(assumptions.proves(&target));
}

#[test]
fn pointer_offset_equality_combines_equal_base_and_zero_index() {
    let base = Bitvector32Term::Variable(Variable(90));
    let target = Bitvector32Term::Variable(Variable(91));
    let index = Bitvector32Term::Variable(Variable(92));
    let base_offset = PointerOffsetTerm::scale_int32(base, 4);
    let target_offset = PointerOffsetTerm::scale_int32(target, 4);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_offset_equal(base_offset.clone(), target_offset.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        );

    assert_eq!(
        assumptions.decide(&ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::add(base_offset, PointerOffsetTerm::scale_int32(index, 4),),
            target_offset,
        )),
        Some(true),
    );
}

#[test]
fn atomic_condition_fact_transport_uses_exact_separate_range() {
    let before = CMemory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(91)), 4),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(left.clone()),
            ),
            Bitvector32Term::Constant(0),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                left.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                right.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                right,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_transport(&fact, &after, &assumptions)
        .expect("the exact separate range should frame the left load");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(after),
                        Box::new(left)
                    ),
                    Bitvector32Term::Constant(0),
                ),
                true,
            )),
        )
    );
}

#[test]
fn direct_condition_transport_uses_relative_separate_range() {
    let before = CMemory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let data_index_from_owner = Bitvector32Term::subtract(
        Bitvector32Term::Variable(Variable(93)),
        Bitvector32Term::Variable(Variable(92)),
    );
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(data.clone()),
            ),
            Bitvector32Term::Variable(Variable(94)),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(
                data_index_from_owner.clone(),
                Bitvector32Term::add(data_index_from_owner.clone(), Bitvector32Term::Constant(2)),
            ),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                data_index_from_owner.clone(),
                Bitvector32Term::add(data_index_from_owner, Bitvector32Term::Constant(2)),
            )),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                owner,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("relative exact separation should directly frame the data load");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(after),
                        Box::new(data)
                    ),
                    Bitvector32Term::Variable(Variable(94)),
                ),
                true,
            )),
        )
    );
}

#[test]
fn direct_condition_transport_uses_indexed_relative_separate_range() {
    let before = CMemory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let data_one = data.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let data_index_from_owner = Bitvector32Term::subtract(
        Bitvector32Term::Variable(Variable(93)),
        Bitvector32Term::Variable(Variable(92)),
    );
    let length = Bitvector32Term::Variable(Variable(95));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(before.clone()),
                Box::new(data_one.clone()),
            ),
            Bitvector32Term::Variable(Variable(94)),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(2), length.clone()),
            true,
        )
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(4),
            )),
            right: CResource::Memory(CMemoryRange::new(
                owner.clone(),
                data_index_from_owner.clone(),
                Bitvector32Term::add(data_index_from_owner, length),
            )),
        })
        .assume_proposition(Proposition::CMemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![CMemoryRange::new(
                owner,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )],
        });

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("an indexed pointer in a relative separate range should be directly framed");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(after),
                        Box::new(data_one)
                    ),
                    Bitvector32Term::Variable(Variable(94)),
                ),
                true,
            )),
        )
    );
}

#[test]
fn condition_fact_transport_preserves_arithmetic_structure() {
    let before = CMemory::new().with_block("stable", 4);
    let after = before.clone().with_block("local:value", 4);
    let stable = Pointer {
        block: "stable".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::add(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(before),
                    Box::new(stable.clone()),
                ),
                Bitvector32Term::Constant(1),
            ),
            Bitvector32Term::Constant(8),
        ),
        true,
    );

    let theorem = prove_c_condition_fact_transport(&fact, &after, &PureFactContext::new())
        .expect("arithmetic around a framed load should transport structurally");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::add(
                        Bitvector32Term::MemoryLoad(
                            crate::kernel::intern_c_memory(after),
                            Box::new(stable)
                        ),
                        Bitvector32Term::Constant(1),
                    ),
                    Bitvector32Term::Constant(8),
                ),
                true,
            )),
        )
    );
}

#[test]
fn adjacent_disjoint_fact_ranges_cover_larger_disjoint_goal() {
    let n_bits = Bitvector32Term::Variable(Variable(87));
    let p_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p_plus_one = p_base.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let q_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(88)), 4),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: p_base.clone(),
            left_start: Bitvector32Term::Constant(0),
            left_end: Bitvector32Term::Constant(1),
            right_base: q_base.clone(),
            right_start: Bitvector32Term::Constant(0),
            right_end: n_bits.clone(),
        })
        .assume_proposition(Proposition::CMemoryDisjoint {
            left_base: p_plus_one,
            left_start: Bitvector32Term::Constant(0),
            left_end: Bitvector32Term::Constant(2),
            right_base: q_base.clone(),
            right_start: Bitvector32Term::Constant(0),
            right_end: n_bits.clone(),
        });

    assert!(assumptions.proves(&Proposition::CMemoryDisjoint {
        left_base: p_base,
        left_start: Bitvector32Term::Constant(0),
        left_end: Bitvector32Term::Constant(2),
        right_base: q_base,
        right_start: Bitvector32Term::Constant(0),
        right_end: n_bits,
    }));
}

#[test]
fn constant_non_overlapping_ranges_on_one_base_are_separate() {
    let base = Pointer {
        block: "object".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left = CResource::Memory(CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    let right = CResource::Memory(CMemoryRange::new(
        base,
        Bitvector32Term::Constant(2),
        Bitvector32Term::Constant(4),
    ));

    assert!(
        PureFactContext::new().proves(&Proposition::CResourceSeparate {
            left: left.clone(),
            right: right.clone(),
        })
    );
    assert!(
        PureFactContext::new().proves(&Proposition::CResourceSeparate {
            left: right,
            right: left,
        })
    );
}

#[test]
fn symbolic_disjoint_fact_proves_itself() {
    let n_bits = Bitvector32Term::Variable(Variable(89));
    let p_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let q_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4),
    };
    let fact = Proposition::CMemoryDisjoint {
        left_base: p_base,
        left_start: Bitvector32Term::Constant(0),
        left_end: n_bits.clone(),
        right_base: q_base,
        right_start: Bitvector32Term::Constant(0),
        right_end: n_bits,
    };
    let assumptions = PureFactContext::new().assume_proposition(fact.clone());

    assert!(assumptions.proves(&fact));
}

#[test]
fn while_invariant_rule_proves_symbolic_loop_exit_fact() {
    let i = Variable(71);
    let n = Variable(72);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let state = CState::new()
        .with_local("i", int32(i_bits.clone()))
        .with_local("n", int32(n_bits.clone()));
    let condition = c_less_than(c_variable("i"), c_variable("n"));
    let body = c_assign("i", c_add(c_variable("i"), c_int32_literal(1)));
    let invariant = vec![
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(i_bits.clone(), n_bits.clone()),
            true,
        ),
    ];
    let assumptions = invariant
        .iter()
        .cloned()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition)
        .assume_condition(
            ConditionTerm::signed_less_equal(
                n_bits.clone(),
                Bitvector32Term::Constant(i32::MAX as u32),
            ),
            true,
        );
    let theorem = prove_c_while_invariant_rule(
        state,
        condition,
        invariant,
        body,
        assumptions,
        vec![
            Proposition::ConditionIs(
                ConditionTerm::signed_greater_equal(
                    incremented.clone(),
                    Bitvector32Term::Constant(0),
                ),
                true,
            ),
            Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(incremented, n_bits.clone()),
                true,
            ),
        ],
        Proposition::ConditionIs(ConditionTerm::equal(i_bits, n_bits), true),
    )
    .expect("invariant rule should prove preservation and i == n on loop exit");

    assert!(matches!(theorem.proposition(), Proposition::Implies(_, _)));
}

/// Pins the unsoundness that `prove_c_while_invariant_rule` is fenced for.
///
/// The rule's acceptance does not depend on the body at all: it matches the
/// body's post-state as `CStatementOutcome::Normal(_)`, throws it away, and
/// discharges `preserved` against the *pre-body* assumption context. So one
/// and the same `preserved` list -- which describes the step `i := i + 1` --
/// is accepted both for a body that increments `i` and for a body that zeroes
/// it.
///
/// If someone teaches the rule to check the invariant at the body's
/// post-state, the second case below must start failing; replace this test
/// with a positive preservation test at that point.
#[test]
fn while_invariant_rule_ignores_what_the_body_does_to_the_invariant() {
    let i = Variable(171);
    let n = Variable(172);
    let i_bits = Bitvector32Term::Variable(i);
    let n_bits = Bitvector32Term::Variable(n);
    let incremented = Bitvector32Term::Add(
        Box::new(i_bits.clone()),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let state = CState::new()
        .with_local("i", int32(i_bits.clone()))
        .with_local("n", int32(n_bits.clone()));
    let condition = c_less_than(c_variable("i"), c_variable("n"));
    let invariant = vec![
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(i_bits.clone(), Bitvector32Term::Constant(0)),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(i_bits.clone(), n_bits.clone()),
            true,
        ),
    ];
    let assumptions = invariant
        .iter()
        .cloned()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition)
        .assume_condition(
            ConditionTerm::signed_less_equal(
                n_bits.clone(),
                Bitvector32Term::Constant(i32::MAX as u32),
            ),
            true,
        );
    // `preserved` describes the state after the step `i := i + 1`.
    let preserved = vec![
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(incremented.clone(), Bitvector32Term::Constant(0)),
            true,
        ),
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(incremented, n_bits.clone()),
            true,
        ),
    ];
    let postcondition = Proposition::ConditionIs(ConditionTerm::equal(i_bits, n_bits), true);

    let prove_with_body = |body: CStatement| {
        prove_c_while_invariant_rule(
            state.clone(),
            condition.clone(),
            invariant.clone(),
            body,
            assumptions.clone(),
            preserved.clone(),
            postcondition.clone(),
        )
    };

    // The body that `preserved` actually describes.
    assert!(
        prove_with_body(c_assign("i", c_add(c_variable("i"), c_int32_literal(1)))).is_some(),
        "the incrementing body should be accepted"
    );
    // A body that sets `i` to 0, so after the step `i` is 0 rather than
    // `i + 1`. The rule accepts the unchanged `preserved` anyway, which is
    // exactly the gap the fence exists to contain.
    assert!(
        prove_with_body(c_assign("i", c_int32_literal(0))).is_some(),
        "the fenced rule is expected to accept a `preserved` list the body does \
         not establish; if it now rejects it, the rule learned to look at the \
         body's post-state and the fence should be revisited"
    );
}

/// The while-invariant rule must stay unreachable from outside the kernel.
///
/// The real guarantee is the `#[cfg(test)]` + `pub(super)` declaration in
/// `api.rs`, which `kernel/mod.rs`'s `pub use api::*` cannot widen. This test
/// pins that declaration so re-exporting the rule fails the gate rather than
/// silently adding an unsound axiom to the trusted base.
#[test]
fn while_invariant_rule_is_not_exported_from_the_kernel() {
    let api_source = include_str!("../api.rs");

    assert!(
        !api_source.contains("pub fn prove_c_while_invariant_rule"),
        "prove_c_while_invariant_rule must not be publicly exported: it is an \
         unsound partial while rule (see its doc comment in api.rs)"
    );
    assert!(
        api_source.contains("#[cfg(test)]\npub(super) fn prove_c_while_invariant_rule("),
        "prove_c_while_invariant_rule must stay declared as \
         `#[cfg(test)] pub(super) fn` so it does not exist in a release build"
    );
}

#[test]
fn same_block_frame_uses_symbolic_offset_inequality() {
    let i = Variable(73);
    let j = Variable(74);
    let i_bits = Bitvector32Term::Variable(i);
    let j_bits = Bitvector32Term::Variable(j);
    let base = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let stored_pointer = base.offset_by_int32_elements(i_bits);
    let loaded_pointer = base.offset_by_int32_elements(j_bits);
    let memory = CMemory::new().store(loaded_pointer.clone(), int32(42));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_offset_equal(
            stored_pointer.offset.clone(),
            loaded_pointer.offset.clone(),
        ),
        false,
    );
    let theorem = prove_memory_load_after_store_distinct_under_assumptions(
        memory.clone(),
        stored_pointer.clone(),
        int32(9),
        loaded_pointer.clone(),
        assumptions,
    )
    .expect("i != j should prove store p[i] preserves load p[j]");

    assert_eq!(
        theorem.proposition().peel_implications(),
        &Proposition::CMemoryLoads {
            memory: memory.store(stored_pointer, int32(9)),
            pointer: loaded_pointer,
            outcome: CExpressionOutcome::Value(int32(42)),
        }
    );
}

#[test]
fn same_symbolic_base_constant_offsets_are_distinct() {
    let base = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4);
    let first = Pointer {
        block: "arg-memory".into(),
        offset: base.clone(),
    };
    let second = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(base, PointerOffsetTerm::Constant(4)),
    };

    assert!(pointers_proven_distinct(
        &first,
        &second,
        &PureFactContext::new()
    ));
}

#[test]
fn additive_equality_cancellation_feeds_range_contradictions() {
    let base = Bitvector32Term::Variable(Variable(91));
    let index = Bitvector32Term::Variable(Variable(92));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(Bitvector32Term::add(base.clone(), index.clone()), base),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(index, Bitvector32Term::Constant(1)),
            true,
        );

    assert!(assumptions.is_inconsistent());
}

#[test]
fn equality_facts_close_signed_order_contradiction_cycles() {
    let left = Bitvector32Term::Variable(Variable(193));
    let right = Bitvector32Term::Variable(Variable(194));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(left.clone(), right.clone()), true)
        .assume_condition(
            ConditionTerm::signed_less_than(left, Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(right, Bitvector32Term::Constant(1)),
            true,
        );

    assert!(assumptions.is_inconsistent());
}

/// Memory-load lowering splits on every cell it cannot resolve, so a
/// quantified invariant over an owned array produces one path per owner field
/// guarded by "this element aliases that field". Those paths are vacuous, but
/// only the index bound assumed *inside* the quantifier rules them out, and
/// the splitter never sees it. The invariant closer does, so the contradiction
/// has to be visible there — and only there: with the bound dropped the guard
/// is genuinely satisfiable and must stay consistent.
#[test]
fn separation_refutes_an_alias_guard_exactly_when_the_index_is_in_range() {
    let block: PointerBlock = "arg-memory".into();
    let owner_offset = PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(801)), 4);
    let data = Bitvector32Term::Variable(Variable(802));
    let capacity = Bitvector32Term::Variable(Variable(803));
    let index = Bitvector32Term::Variable(Variable(804));
    let owner = Pointer {
        block: block.clone(),
        offset: owner_offset.clone(),
    };
    let data_base = Pointer {
        block,
        offset: PointerOffsetTerm::scale_int32(data.clone(), 4),
    };
    // The element address the alias guard claims equals the `cap` field's.
    let element = PointerOffsetTerm::add(
        PointerOffsetTerm::scale_int32(data, 4),
        PointerOffsetTerm::scale_int32(index.clone(), 4),
    );
    let capacity_field = PointerOffsetTerm::add(owner_offset, PointerOffsetTerm::Constant(4));
    let unbounded = PureFactContext::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(owner, 1, 2)),
            right: CResource::Memory(memory_range(data_base, 0, capacity.clone())),
        })
        .assume_condition(
            ConditionTerm::pointer_offset_equal(element, capacity_field),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        );

    assert!(!unbounded.is_inconsistent());
    assert!(
        unbounded
            .assume_condition(ConditionTerm::signed_less_than(index, capacity), true)
            .is_inconsistent()
    );
}

/// A loop back edge re-proves `forall k < b + 1, P(k)` from an invariant that
/// only covers `k < b`. The missing step is one case split, not a theory: `k`
/// is below `b` or equal to it, and the two halves are discharged by facts
/// that are already present. Replay must accept the same split and must reject
/// it when the bound that licensed it is gone.
#[test]
fn an_assumed_upper_bound_splits_a_goal_at_its_final_index() {
    let bound = Bitvector32Term::Variable(Variable(811));
    let index = Bitvector32Term::Variable(Variable(812));
    // Holds strictly below the bound (by the quantified fact) and at it (by
    // reflexivity); neither half's justification covers the other.
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(index.clone(), bound.clone()),
        true,
    );
    let context = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(
            index.clone(),
            Bitvector32Term::add(bound.clone(), Bitvector32Term::Constant(1)),
        ),
        true,
    );

    let derivation = context
        .derive_proposition(&goal)
        .expect("the split closes the goal");
    assert!(matches!(
        derivation.rule,
        PropositionDerivationRule::UpperBoundSplit { .. }
    ));
    assert!(derivation.replay(&context));
    // Without the bound there is no split to license and nothing to prove.
    let unbounded = PureFactContext::new();
    assert!(!derivation.replay(&unbounded));
    assert!(unbounded.derive_proposition(&goal).is_none());
}

#[test]
fn equality_to_constant_feeds_signed_order_decisions() {
    let value = Bitvector32Term::Variable(Variable(93));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(value.clone(), Bitvector32Term::Constant(1)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(0),
            value.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            value,
            Bitvector32Term::Constant(1),
        )),
        Some(true)
    );
}

#[test]
fn range_fold_simplifies_empty_and_one_step_ranges() {
    let accumulator = Variable(93);
    let item = Variable(94);
    let x = Bitvector32Term::Variable(Variable(95));
    let body = Bitvector32Term::add(Bitvector32Term::Variable(accumulator), x.clone());

    assert_eq!(
        Bitvector32Term::range_fold(
            Bitvector32Term::Constant(4),
            Bitvector32Term::Constant(4),
            Bitvector32Term::Constant(7),
            accumulator,
            item,
            body.clone(),
        ),
        Bitvector32Term::Constant(7)
    );

    assert_eq!(
        Bitvector32Term::range_fold(
            Bitvector32Term::Variable(Variable(96)),
            Bitvector32Term::add(
                Bitvector32Term::Variable(Variable(96)),
                Bitvector32Term::Constant(1)
            ),
            Bitvector32Term::Constant(7),
            accumulator,
            item,
            body,
        ),
        Bitvector32Term::add(Bitvector32Term::Constant(7), x)
    );
}

#[test]
fn count_shaped_range_fold_split_is_proven_equal() {
    let lo = Bitvector32Term::Variable(Variable(97));
    let mid = Bitvector32Term::Variable(Variable(98));
    let hi = Bitvector32Term::Variable(Variable(99));
    let x = Bitvector32Term::Variable(Variable(100));
    let accumulator = Variable(101);
    let item = Variable(102);
    let contribution = Bitvector32Term::if_then_else(
        ConditionTerm::equal(Bitvector32Term::Variable(item), x),
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(0),
    );
    let body = Bitvector32Term::add(Bitvector32Term::Variable(accumulator), contribution);
    let count = |start: Bitvector32Term, end: Bitvector32Term| {
        Bitvector32Term::range_fold(
            start,
            end,
            Bitvector32Term::Constant(0),
            accumulator,
            item,
            body.clone(),
        )
    };
    let whole = count(lo.clone(), hi.clone());
    let split = Bitvector32Term::add(
        count(lo.clone(), mid.clone()),
        count(mid.clone(), hi.clone()),
    );

    // The split identity fold(lo,hi) = fold(lo,mid) + fold(mid,hi) only
    // holds for lo <= mid <= hi. Without that ordering it is unsound
    // (half-open ranges make an out-of-order mid over- or under-count),
    // so the rule must not fire on unconstrained bounds.
    assert!(!PureFactContext::new().proves(&Proposition::ConditionIs(
        ConditionTerm::equal(whole.clone(), split.clone()),
        true,
    )));

    let ordered = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_equal(lo, mid.clone()), true)
        .assume_condition(ConditionTerm::signed_less_equal(mid, hi), true);
    assert!(ordered.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(whole, split),
        true,
    )));
}

#[test]
fn symbolic_store_invalidates_only_possible_aliasing_cells() {
    let i = Variable(81);
    let i_bits = Bitvector32Term::Variable(i);
    let concrete_cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let symbolic_cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(i_bits.clone()),
            byte_width: 4,
        },
    };
    let memory = CMemory::new()
        .with_block("array", 12)
        .store(concrete_cell.clone(), int32(42));

    let aliased = memory
        .without_possible_aliasing_cells(&symbolic_cell, &PureFactContext::new())
        .store(symbolic_cell.clone(), int32(7));
    assert_eq!(aliased.known_value(&concrete_cell), None);

    let distinct_assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(i_bits, Bitvector32Term::Constant(1)),
        false,
    );
    let distinct = memory
        .without_possible_aliasing_cells(&symbolic_cell, &distinct_assumptions)
        .store(symbolic_cell, int32(7));
    assert_eq!(distinct.known_value(&concrete_cell), Some(int32(42)));
}

#[test]
fn memory_resolution_alias_check_uses_explicit_separation() {
    let left_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(90)), 4),
    };
    let right_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(91)), 4),
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
        left: CResource::Memory(memory_range(left_base.clone(), 0, 4)),
        right: CResource::Memory(memory_range(right_base.clone(), 0, 4)),
    });

    assert!(pointers_proven_distinct_for_memory_resolution(
        &left_base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &right_base.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));
    assert!(!pointers_proven_equal_for_memory_resolution(
        &left_base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &right_base.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));

    let right_start = Bitvector32Term::subtract(
        Bitvector32Term::Variable(Variable(91)),
        Bitvector32Term::Variable(Variable(90)),
    );
    let normalized_assumptions =
        PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(left_base.clone(), 0, 4)),
            right: CResource::Memory(memory_range(
                left_base.clone(),
                right_start.clone(),
                Bitvector32Term::add(right_start, Bitvector32Term::Constant(4)),
            )),
        });
    assert!(pointers_proven_distinct_for_memory_resolution(
        &left_base.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &right_base.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &normalized_assumptions,
    ));
}

#[test]
fn memory_resolution_uses_compact_resource_composition_with_shallow_equalities() {
    let member_left_index = Bitvector32Term::Variable(Variable(93_410));
    let member_right_index = Bitvector32Term::Variable(Variable(93_411));
    let query_left_index = Bitvector32Term::Variable(Variable(93_412));
    let query_right_index = Bitvector32Term::Variable(Variable(93_413));
    let pointer = |index: Bitvector32Term| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let left_range = memory_range(pointer(member_left_index.clone()), 0, 4);
    let right_range = memory_range(pointer(member_right_index.clone()), 0, 4);
    let context = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(left_range.clone()))
        .unchecked_with_fact(CResourceFact::own_memory(right_range));
    let composition = context
        .observable_facts(&PureFactContext::new())
        .expect("the two owned ranges should compose")
        .into_iter()
        .find(|fact| matches!(fact, Proposition::CResourceComposition(_)))
        .expect("multi-owner contexts should expose one compact authority");
    let assumptions = PureFactContext::new()
        .assume_proposition(composition)
        .assume_condition(
            ConditionTerm::equal(query_left_index.clone(), member_left_index),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(query_right_index.clone(), member_right_index),
            true,
        );
    let query_left = pointer(query_left_index);
    let query_right = pointer(query_right_index);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &query_left,
        &query_right,
        &assumptions,
    ));
    assert!(assumptions.ranges_directly_disjoint_from_pointer(&[left_range], &query_right,));
}

/// The on-demand form of the former materialized separation pairs: with only
/// the compact composition assumed — zero pair facts — a separation between
/// subranges of two distinct owned symbolic ranges must still be provable,
/// because two owned facts of one valid composition are separate and each
/// subrange is provably contained in its parent. Overlapping subranges of one
/// owned fact must stay unprovable.
#[test]
fn compact_composition_projects_symbolic_separation_without_pair_facts() {
    let len = Bitvector32Term::Variable(Variable(93_420));
    let cap = Bitvector32Term::Variable(Variable(93_421));
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let prefix = CMemoryRange::new(base.clone(), Bitvector32Term::Constant(0), len.clone());
    let suffix = CMemoryRange::new(base.clone(), len.clone(), cap.clone());
    let context = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(prefix.clone()))
        .unchecked_with_fact(CResourceFact::own_memory(suffix.clone()));
    let composition = context
        .observable_facts(&PureFactContext::new())
        .expect("the two owned ranges should compose")
        .into_iter()
        .find(|fact| matches!(fact, Proposition::CResourceComposition(_)))
        .expect("multi-owner contexts should expose one compact authority");
    let assumptions = PureFactContext::new()
        .assume_proposition(composition)
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(1), len.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(
                Bitvector32Term::add(len.clone(), Bitvector32Term::Constant(1)),
                cap.clone(),
            ),
            true,
        );

    assert!(
        assumptions.proves(&Proposition::CResourceSeparate {
            left: CResource::Memory(prefix.clone()),
            right: CResource::Memory(suffix.clone()),
        }),
        "the two owned ranges themselves are separate by composition"
    );
    assert!(
        assumptions.proves(&Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                base.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )),
            right: CResource::Memory(CMemoryRange::new(
                base.clone(),
                len.clone(),
                Bitvector32Term::add(len, Bitvector32Term::Constant(1)),
            )),
        }),
        "subranges of distinct owned facts inherit the composition's separation"
    );
    assert!(
        !assumptions.proves(&Proposition::CResourceSeparate {
            left: CResource::Memory(CMemoryRange::new(
                base.clone(),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(2),
            )),
            right: CResource::Memory(CMemoryRange::new(
                base,
                Bitvector32Term::Constant(1),
                Bitvector32Term::Constant(3),
            )),
        }),
        "overlapping subranges of one owned fact must not become separate"
    );
}

#[test]
fn memory_resolution_alias_check_uses_exact_transitive_range_bounds() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let index = Bitvector32Term::Variable(Variable(94));
    let length = Bitvector32Term::Variable(Variable(95));
    let capacity = Bitvector32Term::Variable(Variable(96));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(owner.clone(), 0, 4)),
            right: CResource::Memory(memory_range(data.clone(), 0, capacity.clone())),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(length, capacity), true);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &data.offset_by_int32_elements(index),
        &assumptions,
    ));

    let incremented = Bitvector32Term::add(
        Bitvector32Term::Variable(Variable(94)),
        Bitvector32Term::Constant(1),
    );
    let incremented_assumptions = assumptions
        .assume_condition(
            ConditionTerm::signed_add_overflows(
                Bitvector32Term::Variable(Variable(94)),
                Bitvector32Term::Constant(1),
            ),
            false,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(
                incremented.clone(),
                Bitvector32Term::Variable(Variable(96)),
            ),
            true,
        );
    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &data.offset_by_int32_elements(incremented),
        &incremented_assumptions,
    ));
}

#[test]
fn memory_resolution_alias_check_uses_strict_indices_across_equal_loaded_bases() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(97)), 4),
    };
    let data_cell = owner.offset_by_bytes(8);
    let before = CMemory::new();
    let after = before.clone().with_block("local:temporary", 4);
    let data_before = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(data_cell.clone()),
    );
    let data_after =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(data_cell));
    let length =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(before), Box::new(owner));
    let index = Bitvector32Term::subtract(length.clone(), Bitvector32Term::Constant(1));
    let indexed = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_after.clone(), 4),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        ),
    };
    let terminator = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_before.clone(), 4),
            PointerOffsetTerm::scale_int32(length.clone(), 4),
        ),
    };
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(data_after, data_before), true)
        .assume_condition(ConditionTerm::signed_less_than(index, length), true);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &indexed,
        &terminator,
        &assumptions,
    ));
}

#[test]
fn memory_resolution_alias_check_transports_unchanged_field_loads() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
    };
    let len_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(1));
    let data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let before = CMemory::new();
    let after = before.clone().store(len_cell, int32(7));
    let data_before = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(data_cell.clone()),
    );
    let data_after =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(data_cell));
    let zero_index = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before),
        Box::new(owner.clone()),
    );
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_before, 4),
            PointerOffsetTerm::scale_int32(zero_index.clone(), 4),
        ),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data_after, 4),
    };
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(zero_index, Bitvector32Term::Constant(0)),
        true,
    );

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(1)),
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));
    assert!(pointers_proven_equal_for_memory_resolution(
        &left,
        &right,
        &assumptions,
    ));
}

#[test]
fn memory_resolution_separation_transports_unchanged_range_base_loads() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(93)), 4),
    };
    let len_cell = owner.clone();
    let data_cell = owner.offset_by_int32_elements(Bitvector32Term::Constant(2));
    let before = CMemory::new();
    let after = before.clone().store(len_cell, int32(7));
    let data_before = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(data_cell.clone()),
    );
    let data_after =
        Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(data_cell));
    let length = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(owner.clone()),
    );
    let capacity = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(owner.offset_by_int32_elements(Bitvector32Term::Constant(1))),
    );
    let index = Bitvector32Term::subtract(length.clone(), Bitvector32Term::Constant(1));
    let data_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data_before, 4),
    };
    let indexed_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(
            PointerOffsetTerm::scale_int32(data_after.clone(), 4),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        ),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::CResourceSeparate {
            left: CResource::Memory(memory_range(owner.clone(), 0, 4)),
            right: CResource::Memory(CMemoryRange::new(
                data_base.clone(),
                Bitvector32Term::Constant(0),
                capacity.clone(),
            )),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(length, capacity), true);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner,
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &assumptions,
    ));
    assert!(pointers_proven_equal_for_memory_resolution(
        &data_base,
        &Pointer {
            block: "arg-memory".into(),
            offset: PointerOffsetTerm::scale_int32(data_after, 4),
        },
        &assumptions,
    ));
    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(Bitvector32Term::Constant(2)),
        &indexed_data,
        &assumptions,
    ));
}

#[test]
fn incremented_materialized_index_transports_its_nonnegative_bound() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(931)), 4),
    };
    let local_index = Pointer {
        block: "local:index".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new();
    let old_len = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(before.clone()),
        Box::new(owner.clone()),
    );
    let materialized = before
        .with_block("local:index", 4)
        .store(local_index.clone(), int32(old_len.clone()));
    let materialized_index = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(materialized),
        Box::new(local_index),
    );
    let incremented = Bitvector32Term::add(materialized_index, Bitvector32Term::Constant(1));
    let upper = Bitvector32Term::Variable(Variable(932));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), old_len.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(old_len, upper), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            incremented.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            Bitvector32Term::Constant(0),
            incremented,
        )),
        Some(true)
    );
}

#[test]
fn assumptions_resolve_materialized_symbolic_memory_load_aliases() {
    let k = Variable(75);
    let k_bits = Bitvector32Term::Variable(k);
    let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(k_bits),
            byte_width: 4,
        },
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(base_memory.clone()),
                        Box::new(pointer),
                    )),
                )
            });

    for (index, pointer) in src_pointers.into_iter().enumerate() {
        let assumptions = PureFactContext::new()
            .assume_condition(
                ConditionTerm::pointer_offset_equal(
                    symbolic_src.offset.clone(),
                    pointer.offset.clone(),
                ),
                true,
            )
            .assume_condition(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(k),
                    Bitvector32Term::Constant(index as u32),
                ),
                true,
            );

        assert!(assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(base_memory.clone()),
                    Box::new(pointer)
                ),
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(materialized_memory.clone()),
                    Box::new(symbolic_src.clone()),
                ),
            ),
            true,
        )));
    }
}

#[test]
fn assumptions_reject_forall_based_on_a_shadowed_materialized_load_index() {
    let k = Variable(76);
    let k_bits = Bitvector32Term::Variable(k);
    let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(k_bits.clone()),
            byte_width: 4,
        },
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(base_memory.clone()),
                        Box::new(pointer),
                    )),
                )
            });
    let body = Proposition::Implies(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(k_bits.clone(), Bitvector32Term::Constant(3)),
                true,
            )),
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(base_memory),
                    Box::new(src_pointers[1].clone()),
                ),
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(materialized_memory),
                    Box::new(symbolic_src.clone()),
                ),
            ),
            true,
        )),
    );
    let proposition = Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::pointer_offset_equal(
                symbolic_src.offset.clone(),
                src_pointers[0].offset.clone(),
            ),
            false,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(k_bits.clone(), Bitvector32Term::Constant(0)),
                false,
            )),
            Box::new(Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::pointer_offset_equal(
                        symbolic_src.offset,
                        src_pointers[1].offset.clone(),
                    ),
                    true,
                )),
                Box::new(Proposition::Implies(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::equal(k_bits, Bitvector32Term::Constant(1)),
                        true,
                    )),
                    Box::new(Proposition::ForAll {
                        var: k,
                        sort: Sort::CInt32,
                        body: Box::new(body),
                    }),
                )),
            )),
        )),
    );

    assert!(!PureFactContext::new().proves(&proposition));
}

#[test]
fn assumptions_reject_forall_based_on_a_shadowed_prefix_index() {
    let i = Variable(82);
    let k = Variable(83);
    let i_bits = Bitvector32Term::Variable(i);
    let k_bits = Bitvector32Term::Variable(k);
    let base_memory = CMemory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(k_bits.clone()),
            byte_width: 4,
        },
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(base_memory.clone()),
                        Box::new(pointer),
                    )),
                )
            });
    let body = Proposition::Implies(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), k_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(
                    k_bits.clone(),
                    Bitvector32Term::Add(
                        Box::new(i_bits.clone()),
                        Box::new(Bitvector32Term::Constant(1)),
                    ),
                ),
                true,
            )),
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(base_memory),
                    Box::new(src_pointers[1].clone()),
                ),
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(materialized_memory),
                    Box::new(symbolic_src.clone()),
                ),
            ),
            true,
        )),
    );
    let proposition = Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(i_bits.clone(), Bitvector32Term::Constant(1)),
            true,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(
                    symbolic_src.offset,
                    PointerOffsetTerm::Int32Scaled {
                        value: Box::new(i_bits.clone()),
                        byte_width: 4,
                    },
                ),
                true,
            )),
            Box::new(Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(k_bits, i_bits),
                    true,
                )),
                Box::new(Proposition::ForAll {
                    var: k,
                    sort: Sort::CInt32,
                    body: Box::new(body),
                }),
            )),
        )),
    );

    assert!(!PureFactContext::new().proves(&proposition));
}
