// The proposition search these tests exercise is Surface planning now; see
// `src/surface/planning/proposition_search.rs`. The kernel itself never
// calls it, so the tests import the planner explicitly.
use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

#[test]
fn memory_range_can_be_framed_as_a_byte_footprint() {
    let base = Pointer {
        block: "byte-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = CMemoryRange::new_with_element_width(
        base.clone(),
        Bitvector32Term::Constant(2),
        Bitvector32Term::Constant(5),
        1,
    );
    assert_eq!(range.element_width(), 1);

    let (byte_base, byte_length) = range.byte_footprint();
    assert_eq!(
        byte_base,
        base.offset_by_elements(Bitvector32Term::Constant(2), 1)
    );
    assert_eq!(byte_length, Bitvector32Term::Constant(3));

    let int32_range = CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(2),
        Bitvector32Term::Constant(5),
    );
    assert_eq!(int32_range.element_width(), 4);
    let (int32_base, int32_length) = int32_range.byte_footprint();
    assert_eq!(
        int32_base,
        base.offset_by_elements(Bitvector32Term::Constant(2), 4)
    );
    assert_eq!(int32_length, Bitvector32Term::Constant(12));
    assert_ne!(range, int32_range);

    let rebased = range.with_bounds(
        base,
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(3),
    );
    assert_eq!(rebased.element_width(), 1);
}

/// A footprint is bytes and the element width is only how those bytes are
/// spelled (D6), so ownership coverage is decided bytewise as well: a
/// byte-indexed owner of four bytes is the same authority as an int32-indexed
/// owner of one cell over them, in both directions. Only the bytes decide;
/// coverage that runs off the end is still refused.
#[test]
fn memory_resource_coverage_is_decided_bytewise_for_ownership_and_views() {
    let base = Pointer {
        block: "typed-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let available = ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(
        CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
            1,
        ),
    ));
    let int32_requirement = CResourceFact::own_memory(CMemoryRange::new(
        base.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    assert!(available.satisfies_fact(&int32_requirement, &PureFactContext::new()));
    let int32_available = ResourceContext::new().unchecked_with_fact(int32_requirement.clone());
    assert!(int32_available.satisfies_fact(
        &CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
            1,
        )),
        &PureFactContext::new()
    ));
    assert!(!int32_available.satisfies_fact(
        &CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            base.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(5),
            1,
        )),
        &PureFactContext::new()
    ));

    let byte_requirement = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        base,
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(3),
        1,
    ));
    assert!(available.satisfies_fact(&byte_requirement, &PureFactContext::new()));

    let int32_view_requirement = CResourceFact::view_memory(CMemoryRange::new(
        Pointer {
            block: "typed-buffer".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
    ));
    assert!(available.satisfies_fact(&int32_view_requirement, &PureFactContext::new()));

    let typed_available =
        ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
            Pointer {
                block: "typed-object".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(2),
        )));
    let byte_view_requirement = CResourceFact::view_memory(CMemoryRange::new_with_element_width(
        Pointer {
            block: "typed-object".into(),
            offset: PointerOffsetTerm::Constant(4),
        },
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
        1,
    ));
    assert!(typed_available.satisfies_fact(&byte_view_requirement, &PureFactContext::new()));
    let outside_byte_view = CResourceFact::view_memory(CMemoryRange::new_with_element_width(
        Pointer {
            block: "typed-object".into(),
            offset: PointerOffsetTerm::Constant(8),
        },
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
        1,
    ));
    assert!(!typed_available.satisfies_fact(&outside_byte_view, &PureFactContext::new()));
}

#[test]
fn mixed_width_separation_does_not_block_same_width_coverage() {
    let base = Pointer {
        block: "mixed-width-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let int32_range = CMemoryRange::new_with_element_width(
        base.clone(),
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(2),
        4,
    );
    let wide_range = CMemoryRange::new_with_element_width(
        base.clone(),
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(3),
        8,
    );
    let available = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(int32_range.clone()))
        .unchecked_with_fact(CResourceFact::own_memory(wide_range.clone()));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::CResourceSeparate {
        left: CResource::Memory(int32_range),
        right: CResource::Memory(wide_range),
    });
    let required = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
        base,
        Bitvector32Term::Constant(1),
        Bitvector32Term::Constant(2),
        8,
    ));

    assert!(available.satisfies_fact(&required, &assumptions));
}

#[test]
fn typed_reads_can_use_a_differently_indexed_byte_footprint() {
    let base = Pointer {
        block: "struct-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let byte_field = base.offset_by_elements(Bitvector32Term::Constant(1), 1);
    let assumptions = PureFactContext::new();

    assert!(assumptions.pointer_access_in_range(
        &byte_field,
        1,
        &base,
        &Bitvector32Term::Constant(0),
        &Bitvector32Term::Constant(2),
        4,
    ));
    assert!(!assumptions.pointer_access_in_range(
        &base.offset_by_elements(Bitvector32Term::Constant(8), 1),
        1,
        &base,
        &Bitvector32Term::Constant(0),
        &Bitvector32Term::Constant(2),
        4,
    ));
}

#[test]
fn byte_range_containment_expands_constant_stride_arithmetic() {
    let index = Bitvector32Term::Variable(Variable(93_506));
    let repeated = Bitvector32Term::add(
        Bitvector32Term::add(index.clone(), index.clone()),
        Bitvector32Term::add(index.clone(), index.clone()),
    );
    let scaled = Bitvector32Term::multiply(index, Bitvector32Term::Constant(4));
    let base = Pointer {
        block: "strided-byte-buffer".into(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(repeated),
            byte_width: 1,
        },
    };
    let pointer = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::add(scaled, Bitvector32Term::Constant(3))),
            byte_width: 1,
        },
    };

    assert!(crate::kernel::assumptions::pointer_in_memory_range_shallow(
        &pointer,
        &CMemoryRange::new_with_element_width(
            base,
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
            1,
        ),
    ));
}

#[test]
fn element_index_and_count_support_nonlegacy_widths() {
    for (element_width, index, byte_count) in
        [(1_u32, 3_u32, 3_u32), (2, 7, 14), (4, 5, 20), (8, 2, 16)]
    {
        let index_term = Bitvector32Term::Variable(Variable(93_600 + u64::from(element_width)));
        let offset = PointerOffsetTerm::Int32Scaled {
            value: Box::new(index_term.clone()),
            byte_width: i64::from(element_width),
        };
        assert_eq!(
            element_index_from_offset(&offset, element_width),
            Some(index_term)
        );
        assert_eq!(
            element_count_from_bytes(&Bitvector32Term::Constant(byte_count), element_width),
            Some(Bitvector32Term::Constant(index))
        );
    }
}

#[test]
fn byte_pointer_distinctness_uses_byte_scaled_indices() {
    let i = Bitvector32Term::Variable(Variable(93_500));
    let j = Bitvector32Term::Variable(Variable(93_501));
    let base = Pointer {
        block: "byte-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left = base.offset_by_elements(i.clone(), 1);
    let right = base.offset_by_elements(j.clone(), 1);
    let assumptions = PureFactContext::new().assume_condition(ConditionTerm::equal(i, j), false);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &left,
        &right,
        &assumptions,
    ));
}

#[test]
fn byte_store_does_not_change_a_proven_distinct_byte_load() {
    let i = Bitvector32Term::Variable(Variable(93_502));
    let j = Bitvector32Term::Variable(Variable(93_503));
    let base = Pointer {
        block: "byte-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written = base.offset_by_elements(i.clone(), 1);
    let read = base.offset_by_elements(j.clone(), 1);
    let before = CMemory::new();
    let after = before.clone().store(written.clone(), uint8(7));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(i, j), false)
        .assume_proposition(Proposition::CMemoryMutatesOnly {
            before: before.clone(),
            after: after.clone(),
            pointers: vec![written],
        });

    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::equal(
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after),
                Box::new(read.clone()),
            ),
            Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(before), Box::new(read),),
        ),
        true,
    )));
}

#[test]
fn byte_pointer_access_is_contained_by_a_byte_range() {
    let index = Bitvector32Term::Variable(Variable(93_504));
    let length = Bitvector32Term::Variable(Variable(93_505));
    let base = Pointer {
        block: "byte-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer = base.offset_by_elements(index.clone(), 1);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(index, length.clone()), true);

    assert!(assumptions.pointer_access_in_range(
        &pointer,
        1,
        &base,
        &Bitvector32Term::Constant(0),
        &length,
        1,
    ));
}

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
    let separation = Proposition::CResourceSeparate {
        left: CResource::Memory(memory_range(field_pointer, 0, 1)),
        right: CResource::Memory(memory_range(written_pointer, 0, 1)),
    };
    let assumptions = PureFactContext::new().assume_proposition(separation.clone());
    let source = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let target = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(current_offset, old_offset),
        true,
    );

    let theorem = prove_c_condition_fact_target_transport(&source, &target, &assumptions)
        .expect("an explicit frame should preserve the pointer-valued field load");
    let (premises, theorem_target) = c_condition_fact_transport_parts(&theorem, &source)
        .expect("target transport retains its explicit source");
    assert_eq!(premises, vec![&separation]);
    assert_eq!(theorem_target, &target);
    assert_eq!(
        c_condition_fact_transport_target_in_context(&theorem, &source, &PureFactContext::new()),
        None,
    );
    assert_eq!(
        c_condition_fact_transport_target_in_context(&theorem, &source, &assumptions),
        Some(&target),
        "the source is intrinsically true and the retained frame premise is present",
    );
}

#[test]
fn condition_transport_consumer_accepts_its_separately_proved_source() {
    let source = Proposition::ConditionIs(ConditionTerm::Variable(Variable(90_004)), true);
    let target = Proposition::ConditionIs(ConditionTerm::Variable(Variable(90_005)), true);
    let theorem = c_condition_fact_transport_theorem(&source, target.clone(), []);

    assert_eq!(
        c_condition_fact_transport_target_in_context(&theorem, &source, &PureFactContext::new()),
        Some(&target),
        "the source is the innermost theorem premise, not retained context",
    );
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
fn target_directed_transport_preserves_one_old_load_form() {
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
fn direct_composite_resource_match_checks_pointer_load_across_block_declaration() {
    let entry = CMemory::new().with_block("arg-memory", 32);
    let field = arc_pointer(16);
    let later = entry.clone().with_block("local:pivot", 4);
    let resource_at = |memory: CMemory| CResource::Composite {
        name: "tree".to_string(),
        arguments: vec![
            CValue::pointer(Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(memory),
                        Box::new(field.clone()),
                    ),
                    4,
                ),
            })
            .into(),
        ]
        .into(),
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
    PureFactContext::reset_memory_separation_candidate_checks();
    assert!(
        assumptions.pointers_proven_disjoint_by_explicit_range_for_memory_resolution(&left, &right)
    );
    assert_eq!(PureFactContext::memory_separation_candidate_checks(), 1);
}

#[test]
fn explicit_range_alias_bounds_stay_on_the_shallow_candidate_path() {
    let left_base = Pointer {
        block: "shallow-left".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right_base = Pointer {
        block: "shallow-right".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let index = Bitvector32Term::Variable(Variable(93_100));
    let end = Bitvector32Term::Variable(Variable(93_101));
    let left = left_base.offset_by_int32_elements(index.clone());
    let right = right_base.clone();
    let left_range = CMemoryRange::new(left_base, Bitvector32Term::Constant(0), end.clone());
    let right_range = memory_range(right_base, 0, 1);
    let checks = [16_usize, 64, 256, 1_024, 4_096]
        .into_iter()
        .map(|unrelated| {
            let mut assumptions = PureFactContext::new()
                .assume_proposition(Proposition::CResourceSeparate {
                    left: CResource::Memory(left_range.clone()),
                    right: CResource::Memory(right_range.clone()),
                })
                .assume_condition(
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(0),
                        index.clone(),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(index.clone(), end.clone()),
                    true,
                );
            for fact in 0..unrelated {
                assumptions = assumptions.assume_proposition(Proposition::CResourceSeparate {
                    left: CResource::Memory(memory_range(
                        Pointer {
                            block: format!("unrelated-left-{fact}").into(),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        0,
                        1,
                    )),
                    right: CResource::Memory(memory_range(
                        Pointer {
                            block: format!("unrelated-right-{fact}").into(),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        0,
                        1,
                    )),
                });
            }

            PureFactContext::reset_memory_separation_candidate_checks();
            PureFactContext::reset_memory_separation_recursive_candidate_checks();
            assert!(assumptions
                .pointers_proven_disjoint_by_explicit_range_for_memory_resolution(&left, &right));
            assert_eq!(
                PureFactContext::memory_separation_recursive_candidate_checks(),
                0,
                "an explicit candidate with exact alias bounds must not enter recursive memory resolution"
            );
            PureFactContext::memory_separation_candidate_checks()
        })
        .collect::<Vec<_>>();
    assert!(
        checks.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated separation facts changed indexed candidate work: {checks:?}"
    );
}

#[test]
fn memory_loadable_candidates_ignore_unrelated_pointer_blocks() {
    let memory = CMemory::new();
    let target = Pointer {
        block: "indexed-viewable-target".into(),
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
                block: format!("indexed-viewable-unrelated-{index}").into(),
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
        block: "indexed-viewable-shapes".into(),
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
        "fixed viewability query should not inspect unrelated pointer shapes: {samples:?}"
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
    let (premises, target) = c_condition_fact_transport_parts(&theorem, &fact)
        .expect("transport theorem must retain its explicit source");
    assert!(!premises.is_empty());
    assert!(
        premises
            .iter()
            .all(|premise| assumptions.proves_exact(premise))
    );
    assert_ne!(target, &fact);
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
fn atomic_condition_fact_transport_does_not_plan_from_an_effect_summary() {
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

    assert!(
        prove_c_condition_fact_transport(&fact, &after, &assumptions).is_none(),
        "ordinary fact transport must not plan load equality from ambient effect summaries",
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
fn pointer_offset_fact_transport_does_not_plan_from_an_effect_summary() {
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

    assert!(
        prove_c_condition_fact_transport(&fact, &after, &assumptions).is_none(),
        "pointer-offset transport must require checked load-equality evidence",
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
fn atomic_condition_fact_transport_does_not_plan_from_a_separate_range() {
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

    assert!(
        prove_c_condition_fact_transport(&fact, &after, &assumptions).is_none(),
        "ordinary fact transport must not synthesize a frame from ambient separation",
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
    let effect = Proposition::CMemoryEffectSummary {
        before,
        after: after.clone(),
        mutable_ranges: vec![CMemoryRange::new(
            owner.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    };
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
        .assume_proposition(effect.clone());

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("relative exact separation should directly frame the data load");
    let (premises, target) = c_condition_fact_transport_parts(&theorem, &fact)
        .expect("transport theorem must retain its explicit source");
    assert_eq!(premises.len(), 2);
    assert!(premises.contains(&&effect));
    assert!(
        premises
            .iter()
            .all(|premise| assumptions.proves_exact(premise))
    );
    assert_eq!(
        target,
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(after), Box::new(data)),
                Bitvector32Term::Variable(Variable(94)),
            ),
            true,
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
    let effect = Proposition::CMemoryEffectSummary {
        before,
        after: after.clone(),
        mutable_ranges: vec![CMemoryRange::new(
            owner.clone(),
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(1),
        )],
    };
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
        .assume_proposition(effect.clone());

    let theorem = prove_c_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("an indexed pointer in a relative separate range should be directly framed");
    let (premises, target) = c_condition_fact_transport_parts(&theorem, &fact)
        .expect("transport theorem must retain its explicit source");
    assert_eq!(premises.len(), 3);
    assert!(premises.contains(&&effect));
    assert!(
        premises
            .iter()
            .all(|premise| assumptions.proves_exact(premise))
    );
    assert_eq!(
        target,
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                Bitvector32Term::MemoryLoad(
                    crate::kernel::intern_c_memory(after),
                    Box::new(data_one)
                ),
                Bitvector32Term::Variable(Variable(94)),
            ),
            true,
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

/// Upper-bound case selection belongs to the Surface planner. The kernel's
/// proposition search must not silently create that control flow.
#[test]
fn an_assumed_upper_bound_does_not_split_inside_kernel_search() {
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

    assert!(context.derive_proposition(&goal).is_none());
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

/// An `Integer`-carrier fold over an array cell, with the memory snapshot the
/// body reads left open.
fn integer_array_fold(
    memory: &CMemory,
    start: Bitvector32Term,
    end: Bitvector32Term,
    accumulator: Variable,
    item: Variable,
) -> IntegerTerm {
    let load = Bitvector32Term::MemoryLoad(
        intern_c_memory_ref(memory),
        Box::new(Pointer {
            block: "array".into(),
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(item)),
                byte_width: 4,
            },
        }),
    );
    IntegerTerm::range_fold(
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(start),
            end: SharedIntegerRangeEndpoint::intern(end),
        },
        IntegerTerm::constant_i64(0),
        accumulator,
        item,
        IntegerTerm::add(
            IntegerTerm::var(accumulator),
            IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                MachineIntegerType::Int32,
                load,
            )),
        ),
    )
}

#[test]
fn integer_range_fold_endpoints_are_congruent_under_an_equality() {
    let memory = CMemory::new().with_block("array", 12);
    let lo = Bitvector32Term::Variable(Variable(110));
    let a = Bitvector32Term::Variable(Variable(111));
    let b = Bitvector32Term::Variable(Variable(112));
    let left = integer_array_fold(&memory, lo.clone(), a.clone(), Variable(113), Variable(114));
    let right = integer_array_fold(&memory, lo, b.clone(), Variable(115), Variable(116));
    let goal = Proposition::ConditionIs(
        ConditionTerm::integer_equal(left.clone(), right.clone()),
        true,
    );

    // The two end endpoints are unrelated terms, so nothing equates the folds
    // until the equality is an available fact.
    assert!(!PureFactContext::new().proves(&goal));
    assert!(
        PureFactContext::new()
            .assume_condition(ConditionTerm::equal(a, b), true)
            .proves(&goal)
    );
}

#[test]
fn integer_range_fold_endpoint_congruence_normalizes_an_affine_endpoint() {
    let memory = CMemory::new().with_block("array", 12);
    let lo = Bitvector32Term::Variable(Variable(120));
    let hi = Bitvector32Term::Variable(Variable(121));
    // `(hi - 1) + 1` is the endpoint every induction step carries back to
    // `hi`. It needs no ordering or definedness fact: 32-bit `Add` and
    // `Subtract` wrap, so the two affine normal forms are equal outright.
    let successor_of_predecessor = Bitvector32Term::Add(
        Box::new(Bitvector32Term::Subtract(
            Box::new(hi.clone()),
            Box::new(Bitvector32Term::Constant(1)),
        )),
        Box::new(Bitvector32Term::Constant(1)),
    );
    let left = integer_array_fold(
        &memory,
        lo.clone(),
        successor_of_predecessor,
        Variable(122),
        Variable(123),
    );
    let right = integer_array_fold(&memory, lo, hi, Variable(124), Variable(125));

    assert!(PureFactContext::new().proves(&Proposition::ConditionIs(
        ConditionTerm::integer_equal(left, right),
        true,
    )));
}

#[test]
fn integer_range_fold_endpoint_congruence_rejects_a_free_binder_occurrence() {
    let lo = SharedIntegerRangeEndpoint::intern(Bitvector32Term::Variable(Variable(140)));
    let a = SharedIntegerRangeEndpoint::intern(Bitvector32Term::Variable(Variable(141)));
    let b = SharedIntegerRangeEndpoint::intern(Bitvector32Term::Variable(Variable(142)));
    let bound_accumulator = Variable(143);
    // One body names `bound_accumulator`. In the left fold that is the
    // accumulator binder; in the right fold, which binds a different
    // accumulator, the same name is a free variable standing for something
    // else entirely. Comparing binder names, or accepting an occurrence
    // because the two variables happen to be spelled alike, would equate two
    // folds that mean different things.
    let fold = |end: &SharedIntegerRangeEndpoint, accumulator: Variable| {
        IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Int32 {
                start: lo.clone(),
                end: end.clone(),
            },
            IntegerTerm::constant_i64(0),
            accumulator,
            Variable(144),
            IntegerTerm::var(bound_accumulator),
        )
    };
    let bound = fold(&a, bound_accumulator);
    let free = fold(&b, Variable(145));

    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(a.value().clone(), b.value().clone()),
        true,
    );
    assert!(!assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::integer_equal(bound.clone(), free),
        true,
    )));

    // The same pair with the accumulator bound on both sides is equated, so
    // the refusal above is the free occurrence and not the shape.
    let also_bound = fold(&b, bound_accumulator);
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::integer_equal(bound, also_bound),
        true,
    )));
}

#[test]
fn integer_range_fold_endpoint_congruence_requires_one_memory_snapshot() {
    let cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = CMemory::new().with_block("array", 12);
    let after = before.clone().store(cell, int32(7));
    let lo = Bitvector32Term::Variable(Variable(130));
    let a = Bitvector32Term::Variable(Variable(131));
    let b = Bitvector32Term::Variable(Variable(132));
    let assumptions =
        PureFactContext::new().assume_condition(ConditionTerm::equal(a.clone(), b.clone()), true);

    // Equal endpoints and the same body shape, but the two bodies read
    // different snapshots of the same array. The fold values may genuinely
    // differ, so the congruence must not fire.
    let left = integer_array_fold(&before, lo.clone(), a.clone(), Variable(133), Variable(134));
    let across_a_write =
        integer_array_fold(&after, lo.clone(), b.clone(), Variable(135), Variable(136));
    assert!(!assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::integer_equal(left.clone(), across_a_write),
        true,
    )));

    // The same pair at one snapshot is equated, so the refusal above is the
    // snapshot check and not some other mismatch.
    let same_snapshot = integer_array_fold(&before, lo, b, Variable(135), Variable(136));
    assert!(assumptions.proves(&Proposition::ConditionIs(
        ConditionTerm::integer_equal(left, same_snapshot),
        true,
    )));
}

/// A raw cell and a typed union overlay never both describe one pointer.
///
/// The overlay outranks the raw cell for an exact typed load, so a reader that
/// treats the raw cell as the pointer's content -- as
/// `materialized_registered_load_value` does when it unfolds a registered load
/// variable -- would otherwise be able to read the outranked value. Both
/// writers keep the two disjoint; this pins that they do, in both orders.
#[test]
fn store_and_union_cells_never_coexist_at_one_pointer() {
    let cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let base = CMemory::new().with_block("array", 8);

    let overlay_over_store = base.clone().store(cell.clone(), int32(42)).store_union(
        cell.clone(),
        CType::UInt8,
        CValue::UInt8(Bitvector32Term::Constant(7)),
    );
    assert_eq!(overlay_over_store.known_value(&cell), None);
    assert!(overlay_over_store.has_union_overlay_at(&cell));

    let store_over_overlay = base
        .store_union(
            cell.clone(),
            CType::UInt8,
            CValue::UInt8(Bitvector32Term::Constant(7)),
        )
        .store(cell.clone(), int32(42));
    assert_eq!(store_over_overlay.known_value(&cell), Some(int32(42)));
    assert!(!store_over_overlay.has_union_overlay_at(&cell));
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

/// One hop through an exact pointer equality, and every way that hop must not
/// be taken. Without the rule, a load through a pointer a call returned is
/// framed by nothing at all once `observable_by_load` stopped filtering by
/// name; with it, a contract that says where the pointer points is spent.
#[test]
fn one_exact_pointer_equality_resolves_an_unresolved_pointer_and_nothing_else_does() {
    let symbolic = Pointer {
        block: PointerBlock::Symbolic(Variable(1_000_001)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let other_symbolic = Pointer {
        block: PointerBlock::Symbolic(Variable(1_000_002)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let global = Pointer {
        block: "global:g".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let local = Pointer {
        block: "local:q".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let equal = |left: &Pointer, right: &Pointer| {
        Proposition::ConditionIs(
            ConditionTerm::pointer_equal(left.clone(), right.clone()),
            true,
        )
    };

    // With nothing stated, the symbolic pointer is separated from nothing.
    let bare = PureFactContext::new();
    assert!(!pointers_proven_distinct_for_memory_resolution(
        &local, &symbolic, &bare
    ));

    // `ensures result == &g[0]` resolves it, and `local:q` is then proven
    // distinct from `global:g` by the ordinary structural rule.
    let resolved = PureFactContext::new().assume_proposition(equal(&symbolic, &global));
    assert!(pointers_proven_distinct_for_memory_resolution(
        &local, &symbolic, &resolved
    ));
    assert!(pointers_proven_distinct_for_memory_resolution(
        &symbolic, &local, &resolved
    ));
    // The same equality must NOT separate the read from the block it resolves
    // to: that is `mdtests/returned_pointer_may_alias_a_global.md`.
    assert!(!pointers_proven_distinct_for_memory_resolution(
        &global, &symbolic, &resolved
    ));

    // An equality to another unresolved pointer resolves nothing: the hop
    // always moves towards a block the structural rule can decide.
    let laundered = PureFactContext::new().assume_proposition(equal(&symbolic, &other_symbolic));
    assert!(!pointers_proven_distinct_for_memory_resolution(
        &local, &symbolic, &laundered
    ));

    // Two hops are not one hop: there is no transitive closure over the index.
    let two_hops = PureFactContext::new()
        .assume_proposition(equal(&symbolic, &other_symbolic))
        .assume_proposition(equal(&other_symbolic, &global));
    assert!(!pointers_proven_distinct_for_memory_resolution(
        &local, &symbolic, &two_hops
    ));

    // A disequality is not an alias.
    let disequal = PureFactContext::new().assume_proposition(Proposition::ConditionIs(
        ConditionTerm::pointer_equal(symbolic.clone(), global.clone()),
        false,
    ));
    assert!(!pointers_proven_distinct_for_memory_resolution(
        &local, &symbolic, &disequal
    ));
}

/// The recorded history behind
/// `mdtests/an_unresolved_pointer_sees_the_store_to_a_local.md`, asked of the
/// snapshot comparison that fact transport uses: `x = 5`, then `q = echo(&x)`
/// binding an unresolved pointer into a local, then `x = 1`.
///
/// The two snapshots either side of `x = 1` differ in one cell, and that cell
/// is in a `local:` block. The comparison used to drop every such cell before
/// asking anything, so it called the two snapshots agreed about a load through
/// the returned pointer — which is `&x`, the very address the store wrote. The
/// cells it keeps are now the ones `observable_by_load` keeps, so the answer
/// comes from `pointers_proven_distinct_for_memory_resolution` for every block
/// the structural rule can decide, and from nothing for the one it cannot.
#[test]
fn a_store_to_a_local_is_not_framed_away_for_an_unresolved_pointer() {
    let at = |block: PointerBlock| Pointer {
        block,
        offset: PointerOffsetTerm::Constant(0),
    };
    let symbolic = at(PointerBlock::Symbolic(Variable(1_000_001)));
    let x = at("local:x".into());
    let q = at("local:q".into());
    let argument = at(PointerBlock::ExternalArgument);
    let global = at("global:g".into());
    let bare = PureFactContext::new();

    let entry = CMemory::new()
        .with_block("local:x", 4)
        .with_block("local:q", 8)
        .with_block("global:g", 16);
    // `x = 5`, then the call's result stored into the caller's own `q`, then
    // the store this read has to be told apart from.
    let after_call = entry.store(x.clone(), crate::kernel::api::int32(5));
    let after_binding = after_call.without_possible_aliasing_cells(&q, &bare).store(
        q.clone(),
        CValue::Pointer(CPointerValue::new(symbolic.clone(), CType::Int32Pointer)),
    );
    let after_store = after_binding
        .clone()
        .without_possible_aliasing_cells(&x, &bare)
        .store(x.clone(), crate::kernel::api::int32(1));

    assert!(
        !memory_snapshots_proven_equal_at_pointer(&after_binding, &after_store, &symbolic, &bare),
        "a store to `x` must not be framed away for a load through a pointer \
         nothing resolves: the pointer may be `&x`"
    );

    // Nothing is lost where skipping the `local:` cell was sound: every block
    // a store can name that is not the read's own is proven distinct from a
    // local, so the per-cell check answers those on its first rung.
    assert!(
        memory_snapshots_proven_equal_at_pointer(&after_binding, &after_store, &argument, &bare),
        "memory the caller passed in cannot be this function's own local"
    );
    assert!(
        memory_snapshots_proven_equal_at_pointer(&after_binding, &after_store, &global, &bare),
        "two differently named declared objects are two objects"
    );

    // And the tracker's walk stops at that same store, which is the step the
    // refusal names.
    let point = crate::kernel::resource_tracker::ProgramPoint::at(
        &crate::kernel::intern_c_memory_ref(&after_store),
    );
    let stop = crate::kernel::resource_tracker::last_same(
        crate::kernel::resource_tracker::Resource::Cell(&symbolic),
        &point,
    )
    .expect("a cell always has a naming point");
    assert_eq!(
        stop.stopped_by.change,
        crate::kernel::resource_tracker::Change::Store { pointer: x },
        "the walk must stop at the store to `x`"
    );
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

/// What a separating composition may and may not say about a store and a
/// load (`owned_composition_store_separated_evidence`).
///
/// The rule it implements is the partition invariant and nothing else: two
/// **owned** members of one valid composition hold disjoint bytes. Every
/// attack below is a context where that sentence does not apply, and each one
/// must come back with no evidence.
#[test]
fn a_composition_separates_a_store_from_a_load_only_through_two_owners() {
    use crate::kernel::memory_provenance::owned_composition_store_separated_evidence;

    let value = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(94_001)), 4),
    };
    let acquired = Pointer {
        block: PointerBlock::Symbolic(Variable(1_000_001)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value_cell = memory_range(value.clone(), 0, 1);
    let acquired_cell = memory_range(acquired.clone(), 0, 1);
    let compose = |facts: Vec<CResourceFact>| {
        let context = facts
            .into_iter()
            .fold(ResourceContext::new(), ResourceContext::unchecked_with_fact);
        PureFactContext::new().assume_proposition(Proposition::CResourceComposition(context))
    };

    // The shape `mdtests/c_contract_executes_acquire.md` needs. The two
    // members are spelled in different blocks, and nothing structural relates
    // an `ExternalArgument` address to a pointer a callback returned; only
    // ownership does.
    let owners = compose(vec![
        CResourceFact::own_memory(value_cell.clone()),
        CResourceFact::own_memory(acquired_cell.clone()),
    ]);
    assert!(
        owned_composition_store_separated_evidence(&value, &acquired, &owners).is_some(),
        "two owned members of one composition are disjoint by the partition invariant"
    );

    // An owner beside a *view* is not two owners. The view may be an
    // observation of that very ownership (`owner_observation_core`), which is
    // why `MemoryResourceAlgebra::pair_validity_error` refuses only
    // owner/owner overlap; whether a particular view is independent is
    // decided by its loan binding, which this rule cannot see.
    let owner_and_view = compose(vec![
        CResourceFact::own_memory(value_cell.clone()),
        CResourceFact::view_memory(acquired_cell.clone()),
    ]);
    assert!(
        owned_composition_store_separated_evidence(&value, &acquired, &owner_and_view).is_none(),
        "an owner beside a view is not a partition: the view may describe the owner's own bytes"
    );

    // A cell one element past the owned range is in no member at all.
    let past_the_end = acquired.offset_by_int32_elements(Bitvector32Term::Constant(1));
    assert!(
        owned_composition_store_separated_evidence(&value, &past_the_end, &owners).is_none(),
        "a read outside every owned member inherits nothing from the composition"
    );

    // A folded composite contributes no memory range, so a cell its body
    // would cover is not separated by it: the rule reads `memory_own_range`
    // and never opens a definition.
    let folded = compose(vec![
        CResourceFact::own_memory(value_cell.clone()),
        CResourceFact::own(CResource::Composite {
            name: "Cell".to_string(),
            arguments: vec![CValue::pointer(acquired.clone()).into()].into(),
        }),
    ]);
    assert!(
        owned_composition_store_separated_evidence(&value, &acquired, &folded).is_none(),
        "a composite that is still folded owns no range this rule can read"
    );

    // Two owned members of one block whose bounds are symbolic are the same
    // rule: what makes them disjoint is that one context holds both, and it
    // is whoever handed both out that had to establish the split. Only the
    // spelling changes, which is exactly why the rule may not read one.
    let symbolic_member = |index: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(index)), 4),
    };
    let (front, back) = (symbolic_member(94_002), symbolic_member(94_003));
    let one_block = compose(vec![
        CResourceFact::own_memory(memory_range(front.clone(), 0, 1)),
        CResourceFact::own_memory(memory_range(back.clone(), 0, 1)),
    ]);
    assert!(
        owned_composition_store_separated_evidence(&front, &back, &one_block).is_some(),
        "the partition does not care how the two members are spelled"
    );

    // One member cannot separate an address from itself, whichever end of the
    // question it is asked from.
    let single = compose(vec![CResourceFact::own_memory(value_cell.clone())]);
    assert!(
        owned_composition_store_separated_evidence(&value, &value, &single).is_none(),
        "one member is not two"
    );

    // The evidence names its premise. A composition the context no longer
    // holds does not re-check, which is what keeps a hop retained at an
    // earlier program point from being spent in a context that has moved on.
    let hop = owned_composition_store_separated_evidence(&value, &acquired, &owners)
        .expect("the two-owner case produced evidence");
    let store = CMemoryDerivation::Store {
        base: crate::kernel::intern_c_memory(CMemory::new()),
        pointer: value.clone(),
        value: crate::kernel::api::int32(1),
    };
    assert!(
        hop.checks(&store, &acquired, &owners),
        "the hop re-checks against the composition it named"
    );
    assert!(
        !hop.checks(&store, &acquired, &PureFactContext::new()),
        "a retained hop is worthless in a context that does not hold its composition"
    );
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

#[test]
fn memory_resolution_uses_compact_composition_for_dependent_indexed_range() {
    let arena = Bitvector32Term::Variable(Variable(93_414));
    let data = Bitvector32Term::Variable(Variable(93_415));
    let query_arena = Bitvector32Term::Variable(Variable(93_416));
    let query_data = Bitvector32Term::Variable(Variable(93_417));
    let start = Bitvector32Term::Variable(Variable(93_418));
    let end = Bitvector32Term::Variable(Variable(93_419));
    let index = Bitvector32Term::Variable(Variable(93_420));
    let pointer = |base: Bitvector32Term| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(base, 4),
    };
    let arena_fields = memory_range(pointer(arena.clone()), 0, 2);
    let backing = CMemoryRange::new(pointer(data.clone()), start.clone(), end.clone());
    let context = ResourceContext::new()
        .unchecked_with_fact(CResourceFact::own_memory(arena_fields))
        .unchecked_with_fact(CResourceFact::own_memory(backing));
    let composition = context
        .observable_facts(&PureFactContext::new())
        .expect("the owned metadata and backing should compose")
        .into_iter()
        .find(|fact| matches!(fact, Proposition::CResourceComposition(_)))
        .expect("multiple symbolic owned ranges should expose compact authority");
    let absolute = Bitvector32Term::add(start.clone(), index);
    let assumptions = PureFactContext::new()
        .assume_proposition(composition)
        .assume_condition(ConditionTerm::equal(query_arena.clone(), arena), true)
        .assume_condition(ConditionTerm::equal(query_data.clone(), data), true)
        .assume_condition(
            ConditionTerm::signed_less_equal(start, absolute.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(absolute.clone(), end), true);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &pointer(query_arena),
        &pointer(query_data).offset_by_int32_elements(absolute),
        &assumptions,
    ));
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

#[test]
fn added_composition_carrier_keeps_snapshot_premise_work_bounded() {
    // The lazy-separation monotonicity requirement: adding a valid compact
    // composition carrier must not break, or meaningfully slow, an already
    // provable snapshot premise. Pinned by the bounded-pool regression where
    // a fifth carrier turned an exact-premise check into context-wide
    // repeated range derivation.
    let target = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let neighbor = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(4),
    };
    let before = CMemory::new().with_block("arena", 64);
    let after = before.clone().store(neighbor, int32(7));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(after),
                Box::new(target.clone()),
            ),
        ),
        true,
    );
    let recorded = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            Bitvector32Term::Constant(0),
            Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(before), Box::new(target)),
        ),
        true,
    );
    let carrier = |index: u64| {
        let base = Pointer {
            block: PointerBlock::Concrete(format!("carrier-{index}")),
            offset: PointerOffsetTerm::Constant(0),
        };
        let split = Bitvector32Term::Variable(Variable(95_000 + index));
        let end = Bitvector32Term::Variable(Variable(95_100 + index));
        Proposition::CResourceComposition(
            ResourceContext::new()
                .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    base.clone(),
                    Bitvector32Term::Constant(0),
                    split.clone(),
                )))
                .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    base, split, end,
                ))),
        )
    };
    let context_with = |carriers: u64| {
        let mut assumptions = PureFactContext::new().assume_proposition(recorded.clone());
        for index in 0..carriers {
            assumptions = assumptions.assume_proposition(carrier(index));
        }
        assumptions
    };
    let four = context_with(4);
    let (proved_four, work_four) =
        crate::instrumentation::measure_deterministic_work(|| four.proves(&premise));
    assert!(
        proved_four,
        "the framed premise should prove with four carriers"
    );
    let five = context_with(5);
    let (proved_five, work_five) =
        crate::instrumentation::measure_deterministic_work(|| five.proves(&premise));
    assert!(
        proved_five,
        "adding an unrelated valid carrier must keep the premise provable"
    );
    assert!(
        work_five <= work_four.saturating_mul(2).max(64),
        "an added carrier multiplied premise work: {work_four} -> {work_five}"
    );
}

#[test]
#[should_panic(expected = "load-variable registry capacity exhausted")]
fn load_variable_registry_fails_loudly_at_capacity_instead_of_clearing() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = |block: &str| Pointer {
        block: block.into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = intern_c_memory(
        CMemory::new()
            .with_block("local:a", 4)
            .with_block("local:b", 4)
            .with_block("local:c", 4),
    );
    crate::kernel::with_load_variable_registry_capacity(2, || {
        let first = load_variable_for_cell_with_origin(&memory, &pointer("local:a"), &memory);
        load_variable_for_cell_with_origin(&memory, &pointer("local:b"), &memory);
        // Re-registering an identity the registry already knows is not growth
        // and must keep returning the same variable.
        let again = load_variable_for_cell_with_origin(&memory, &pointer("local:a"), &memory);
        assert_eq!(first, again);
        assert_eq!(crate::kernel::load_variable_registry_len(), 2);
        // The third distinct identity exceeds the capacity: the registry must
        // fail loudly here rather than forget the entries that guard against
        // id collisions.
        load_variable_for_cell_with_origin(&memory, &pointer("local:c"), &memory);
    });
}

/// `(data + i) + j` with `i == INT_MAX`, `j == 1` and `data + k` with
/// `k == INT_MIN` have equal wrapped index sums but exact byte offsets of
/// +2^33 and -2^33, so the equality must not be decided true.
#[test]
fn wrapped_index_sum_does_not_decide_pointer_offsets_equal() {
    let i = Bitvector32Term::Variable(Variable(93_401));
    let j = Bitvector32Term::Variable(Variable(93_402));
    let k = Bitvector32Term::Variable(Variable(93_403));
    let scaled = |value: &Bitvector32Term| PointerOffsetTerm::Int32Scaled {
        value: Box::new(value.clone()),
        byte_width: 4,
    };
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(i.clone(), Bitvector32Term::Constant(i32::MAX as u32)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(j.clone(), Bitvector32Term::Constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(i32::MIN as u32)),
            true,
        );
    let sum = PointerOffsetTerm::Add(Box::new(scaled(&i)), Box::new(scaled(&j)));
    assert_ne!(
        assumptions.decide(&ConditionTerm::pointer_offset_equal(sum, scaled(&k))),
        Some(true),
        "a wrapped index sum must not affirm pointer-offset equality"
    );

    // A shared symbolic base offset cancels exactly, so `base + k` against
    // `base + 2` is decided by `k` alone even though `base + k` may overflow.
    let base = Bitvector32Term::Variable(Variable(93_405));
    let with_base = |offset: PointerOffsetTerm| {
        PointerOffsetTerm::Add(Box::new(scaled(&base)), Box::new(offset))
    };
    let k_is_two = PureFactContext::new().assume_condition(
        ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(2)),
        true,
    );
    assert_eq!(
        k_is_two.decide(&ConditionTerm::pointer_offset_equal(
            with_base(scaled(&k)),
            with_base(PointerOffsetTerm::Constant(8)),
        )),
        Some(true)
    );
    let k_is_three = PureFactContext::new().assume_condition(
        ConditionTerm::equal(k.clone(), Bitvector32Term::Constant(3)),
        true,
    );
    assert_eq!(
        k_is_three.decide(&ConditionTerm::pointer_offset_equal(
            with_base(scaled(&k)),
            with_base(PointerOffsetTerm::Constant(8)),
        )),
        Some(false)
    );

    // Single scaled terms are exact, so equal indices still give equal offsets.
    let m = Bitvector32Term::Variable(Variable(93_404));
    let same =
        PureFactContext::new().assume_condition(ConditionTerm::equal(i.clone(), m.clone()), true);
    assert_eq!(
        same.decide(&ConditionTerm::pointer_offset_equal(scaled(&i), scaled(&m))),
        Some(true)
    );
}

#[test]
fn quantified_load_witness_does_not_certify_loadability_in_a_freed_snapshot() {
    // A universal fact about `load(live, p + k)` witnesses that `p + j` is
    // loadable in `live` (its guard covers `j`), but not in a snapshot where
    // the block is gone.
    let block: PointerBlock = "heap:witness".into();
    let live = CMemory::new().with_block(block.clone(), 4);
    let freed = CMemory::new();
    let base = Pointer {
        block,
        offset: PointerOffsetTerm::Constant(0),
    };
    let k = Variable(93_501);
    let j = Bitvector32Term::Variable(Variable(93_502));
    let witness = forall_int32(
        k,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(
                        Bitvector32Term::Variable(k),
                        Bitvector32Term::Constant(0),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(k),
                        Bitvector32Term::Constant(1),
                    ),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::MemoryLoad(
                        crate::kernel::intern_c_memory(live.clone()),
                        Box::new(base.offset_by_int32_elements(Bitvector32Term::Variable(k))),
                    ),
                    Bitvector32Term::Constant(0),
                ),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(witness)
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), Bitvector32Term::Constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), Bitvector32Term::Constant(1)),
            true,
        );
    let cell = base.offset_by_int32_elements(j);

    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: live,
        base: cell.clone(),
        bytes: Bitvector32Term::Constant(4),
    }));
    assert!(!assumptions.proves(&Proposition::CMemoryLoadable {
        memory: freed,
        base: cell,
        bytes: Bitvector32Term::Constant(4),
    }));
}

#[test]
fn freed_external_allocation_is_not_still_available() {
    // `free` keeps the `ExternalArgument` block, so availability must also
    // compare which allocations each snapshot has freed.
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(93_503))),
            byte_width: 4,
        },
    };
    let live = CMemory::new()
        .with_heap_allocation_claim(base.clone(), Bitvector32Term::Constant(8))
        .expect("a fresh external allocation claim is accepted");
    let freed = live
        .clone()
        .free_heap_block(&base)
        .expect("the claimed allocation can be freed");
    let element = base.offset_by_int32_elements(Bitvector32Term::Constant(1));

    assert!(crate::kernel::reasoning::memory_range_still_available(
        &live, &live, &base
    ));
    assert!(!crate::kernel::reasoning::memory_range_still_available(
        &live, &freed, &base
    ));
    assert!(!crate::kernel::reasoning::memory_range_still_available(
        &live, &freed, &element
    ));

    let assumptions = PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
        memory: live.clone(),
        base: base.clone(),
        bytes: Bitvector32Term::Constant(8),
    });
    assert!(assumptions.proves(&Proposition::CMemoryLoadable {
        memory: live,
        base: base.clone(),
        bytes: Bitvector32Term::Constant(4),
    }));
    assert!(!assumptions.proves(&Proposition::CMemoryLoadable {
        memory: freed,
        base,
        bytes: Bitvector32Term::Constant(4),
    }));
}

/// Load equality resolves through a chain of stored cells of any length:
/// each memory's cell holds the load of the next memory's cell, and the
/// chain ends at a constant. Each hop is one memoized query, so the work
/// follows the chain; the alias depth of 64 that used to cut the recursion
/// refused every chain past it.
#[test]
fn load_equality_resolves_through_stored_cell_chains_of_any_length() {
    let base = Pointer {
        block: "chain".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let cell = |index: usize| base.offset_by_elements(Bitvector32Term::Constant(index as u32), 4);
    let mut samples = Vec::new();
    for length in [32usize, 64, 96, 128] {
        let mut memory =
            CMemory::new().store(cell(length), CValue::Int32(Bitvector32Term::Constant(42)));
        for index in (0..length).rev() {
            let next = Bitvector32Term::MemoryLoad(
                crate::kernel::intern_c_memory(memory),
                Box::new(cell(index + 1)),
            );
            memory = CMemory::new().store(cell(index), CValue::Int32(next));
        }
        let load =
            Bitvector32Term::MemoryLoad(crate::kernel::intern_c_memory(memory), Box::new(cell(0)));
        let (proven, work) = crate::instrumentation::measure_deterministic_work(|| {
            crate::kernel::reasoning::bitvector_terms_proven_equal_for_memory_resolution(
                &load,
                &Bitvector32Term::Constant(42),
                &PureFactContext::new(),
            )
        });
        assert!(
            proven,
            "a chain of {length} stored cells resolves to its constant"
        );
        samples.push((length, work));
    }
    for pair in samples.windows(2) {
        assert!(
            pair[1].1 <= pair[0].1.saturating_mul(3),
            "load resolution through a cell chain is superlinear: {samples:?}"
        );
    }
}

/// A concrete range fold unrolls over ranges of any length: the steps are
/// the range's own length, and a sum over 1,025 to 4,096 items folds to its
/// constant, which the old unroll cap of 1,024 left symbolic.
#[test]
fn range_fold_unrolls_concrete_ranges_of_any_length() {
    let accumulator = Variable(7_800_000);
    let item = Variable(7_800_001);
    let body = Bitvector32Term::add(
        Bitvector32Term::Variable(accumulator),
        Bitvector32Term::Variable(item),
    );
    for length in [1_025u32, 2_048, 4_096] {
        let sum = (0..length).sum::<u32>();
        assert_eq!(
            Bitvector32Term::range_fold(
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(length),
                Bitvector32Term::Constant(0),
                accumulator,
                item,
                body.clone(),
            ),
            Bitvector32Term::Constant(sum),
            "a fold over {length} items unrolls to its sum"
        );
    }
}

#[test]
fn symbolic_blocks_are_never_proven_distinct_by_structure() {
    let symbolic = Pointer {
        block: PointerBlock::Symbolic(Variable(77)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let heap = Pointer {
        block: PointerBlock::Heap(1000001),
        offset: PointerOffsetTerm::Constant(0),
    };
    // A logic variable may later be constrained to any address (a contract
    // postcondition such as `result == destination` does exactly that), so
    // structure alone must not separate it. Otherwise the equality folds to
    // false, gets assumed, and poisons later reasoning.
    assert!(!symbolic.blocks_proven_distinct(&heap));
    assert!(!heap.blocks_proven_distinct(&symbolic));
    // Distinct heap identities remain distinct.
    let other_heap = Pointer {
        block: PointerBlock::Heap(1000002),
        offset: PointerOffsetTerm::Constant(0),
    };
    assert!(heap.blocks_proven_distinct(&other_heap));
}

/// The one filter every load-framing route shares. A block that is merely
/// spelled differently from the load's is still observable by it; only a
/// block the kernel proves distinct drops out.
#[test]
fn a_load_observes_every_block_not_proven_distinct_from_its_own() {
    let argument = PointerBlock::ExternalArgument;
    let object = PointerBlock::ExternalObject(Variable(5));
    let global = PointerBlock::Concrete("global:g".to_string());
    let other_global = PointerBlock::Concrete("global:h".to_string());
    let local = PointerBlock::Concrete("local:caller:x".to_string());
    let fresh = PointerBlock::Heap(1000001);
    let symbolic = PointerBlock::Symbolic(Variable(77));

    // The hole this predicate closes: a caller may pass the global as the
    // argument, so a store to `g` is still in a question about `a`.
    assert!(!global.proven_distinct(&argument));
    assert!(global.may_alias(&argument));
    assert!(global.observable_by_load(&argument));
    assert!(argument.observable_by_load(&global));
    // The same for the opaque object identity a parameter carries.
    assert!(global.observable_by_load(&object));

    // Two file-scope declarations are two objects, and a function's own
    // locals are not memory that existed before the call.
    assert!(global.proven_distinct(&other_global));
    assert!(!global.observable_by_load(&other_global));
    assert!(local.proven_distinct(&argument));
    assert!(!local.observable_by_load(&argument));
    // A block allocated here is fresh, so nothing the caller passed is it.
    assert!(fresh.proven_distinct(&argument));
    assert!(!fresh.observable_by_load(&argument));
    assert!(!fresh.observable_by_load(&global));

    // A block is always observable by a load in it.
    assert!(!global.proven_distinct(&global));
    assert!(global.observable_by_load(&global));
    assert!(argument.observable_by_load(&argument));

    // A symbolic block is proven distinct from nothing, so it may alias
    // everything -- in both directions. A load through a pointer a call
    // returned therefore observes a store to a global: the filter no longer
    // has an exception that would drop it
    // (`mdtests/returned_pointer_may_alias_a_global.md`).
    assert!(symbolic.may_alias(&global));
    assert!(global.may_alias(&symbolic));
    assert!(symbolic.observable_by_load(&global));
    assert!(global.observable_by_load(&symbolic));
    assert!(local.observable_by_load(&symbolic));
    assert!(fresh.observable_by_load(&symbolic));
    assert!(symbolic.observable_by_load(&symbolic));
}

/// The identity the verifier gives an object it introduced itself. Withdrawing
/// the symbolic-load name filter would otherwise have taken the structural
/// frame away from a struct returned by value, which is not a pointer the
/// callee handed over but fresh storage nothing else can name.
#[test]
fn a_verifier_temporary_is_proven_distinct_from_every_named_block() {
    let temporary = PointerBlock::Temporary(1_000_001);
    let other_temporary = PointerBlock::Temporary(1_000_002);
    let global = PointerBlock::Concrete("global:g".to_string());
    let local = PointerBlock::Concrete("local:caller:copy".to_string());
    let argument = PointerBlock::ExternalArgument;
    let object = PointerBlock::ExternalObject(Variable(5));
    let literal = PointerBlock::StringLiteral {
        identity: "string:one".to_string(),
        bytes: b"ok\0".to_vec(),
    };
    let heap = PointerBlock::Heap(1000001);
    let symbolic = PointerBlock::Symbolic(Variable(77));

    // Nothing the program or its caller names is this object, so a store
    // anywhere else drops out of a question about it.
    for other in [&global, &local, &argument, &object, &literal, &heap] {
        assert!(temporary.proven_distinct(other), "{other} vs {temporary}");
        assert!(other.proven_distinct(&temporary), "{temporary} vs {other}");
        assert!(!other.observable_by_load(&temporary));
        assert!(!temporary.observable_by_load(other));
    }
    // Two temporaries are two objects; one is observable by its own load.
    assert!(temporary.proven_distinct(&other_temporary));
    assert!(!temporary.proven_distinct(&temporary));
    assert!(temporary.observable_by_load(&temporary));
    // A symbolic block stays the one thing structure does not separate: an
    // assumed equality may still constrain it to any address, and being
    // coarse here only ever keeps more cells in the question.
    assert!(!temporary.proven_distinct(&symbolic));
    assert!(!symbolic.proven_distinct(&temporary));
    assert!(symbolic.observable_by_load(&temporary));
    assert!(temporary.observable_by_load(&symbolic));
}

/// Two string literal occurrences with different bytes cannot be one object;
/// equal bytes may have been merged by the implementation, so they stay
/// observable by each other.
#[test]
fn string_literal_blocks_separate_only_by_their_bytes() {
    let literal = |identity: &str, bytes: &[u8]| PointerBlock::StringLiteral {
        identity: identity.to_string(),
        bytes: bytes.to_vec(),
    };
    let ok = literal("first", b"ok");
    let no = literal("second", b"no");
    let merged = literal("third", b"ok");
    assert!(ok.proven_distinct(&no));
    assert!(!ok.observable_by_load(&no));
    assert!(!ok.proven_distinct(&merged));
    assert!(ok.observable_by_load(&merged));
    // A literal is not proven distinct from a global either.
    let global = PointerBlock::Concrete("global:g".to_string());
    assert!(ok.observable_by_load(&global));
}

/// Constant range endpoints are `int32` values, and their guard arithmetic
/// must be the true difference. Subtracting the bit patterns underflows for a
/// negative start: in debug that panicked inside the guard, and in release it
/// wrapped to a small unsigned value and declared an impossible extent valid.
mod constant_range_byte_count_guards {
    use super::*;

    fn guards(start: i32, end: i32, element_width: u32) -> Vec<Proposition> {
        crate::kernel::memory_range_byte_count_guards(
            Bitvector32Term::Constant(start as u32),
            Bitvector32Term::Constant(end as u32),
            element_width,
        )
    }

    fn refuses(guards: &[Proposition]) -> bool {
        guards
            == [Proposition::ConditionIs(
                ConditionTerm::Constant(false),
                true,
            )]
    }

    #[test]
    fn a_negative_start_that_fits_needs_no_guard() {
        assert!(guards(-4, 4, 4).is_empty());
        assert!(guards(-1, 0, 4).is_empty());
        assert!(guards(i32::MIN, i32::MIN + 8, 4).is_empty());
    }

    #[test]
    fn a_negative_start_whose_extent_does_not_fit_is_refused() {
        // The true element count is 4_000_000_000, so four bytes each is far
        // past a `u32` extent. Subtracting the bit patterns would have
        // underflowed here instead of reaching this comparison.
        assert!(refuses(&guards(-2_000_000_000, 2_000_000_000, 4)));
        assert!(refuses(&guards(i32::MIN, 0, 4)));
        assert!(refuses(&guards(-1, i32::MAX, 2)));
    }

    #[test]
    fn a_reversed_constant_range_is_refused() {
        assert!(refuses(&guards(4, -4, 4)));
        assert!(refuses(&guards(1, 0, 1)));
        assert!(refuses(&guards(i32::MAX, i32::MIN, 1)));
    }

    /// The bound is the scaled byte count, so the widest fitting element count
    /// depends on the width. One-byte elements reach `u32::MAX` bytes exactly
    /// at the widest `int32` range there is, which is why no one-byte range can
    /// fail the fits guard — only the forward guard.
    #[test]
    fn the_widest_fitting_extent_is_at_the_boundary() {
        assert!(guards(i32::MIN, i32::MAX, 1).is_empty());
        assert!(guards(0, 1_073_741_823, 4).is_empty());
        assert!(refuses(&guards(0, 1_073_741_824, 4)));
        assert!(guards(-1_073_741_823, 0, 4).is_empty());
        assert!(refuses(&guards(-1_073_741_824, 0, 4)));
    }
}

/// Every rule that reads an assumed loadable extent at element granularity
/// must first establish that the extent is a valid 32-bit byte extent.
///
/// The witness is one shape: `loadable(v[0..n])` at `n == 1 << 30` has the
/// byte extent `n * 4`, which is `1 << 32`, which is `0`. The fact is true and
/// covers nothing. A rule that divides that extent by four and reads `n`
/// elements out of it turns nothing into real bytes, and
/// `mdtests/wrapped_viewable_extent_is_not_a_cell.md` is the surface witness
/// for the cell rules specifically. These cover each reader directly, in both
/// polarities: refused without the bound, accepted with it.
mod wrapped_assumed_extent_is_refused {
    use super::*;

    const WRAPPING_COUNT: u32 = 1 << 30;

    fn array_base(byte_offset: i64) -> Pointer {
        Pointer {
            block: "arg-memory".into(),
            offset: PointerOffsetTerm::Constant(byte_offset),
        }
    }

    /// `loadable(v[0..count])` with a symbolic element count, plus the order
    /// facts a reader needs about an index inside it. The extent bound is the
    /// one fact that varies.
    fn context(count: Variable, bounded: bool) -> (CMemory, PureFactContext) {
        let memory = CMemory::new();
        let count_term = Bitvector32Term::Variable(count);
        let mut assumptions = PureFactContext::new()
            .assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: array_base(0),
                bytes: Bitvector32Term::multiply(count_term.clone(), Bitvector32Term::Constant(4)),
            })
            .assume_condition(
                ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), count_term.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(Bitvector32Term::Constant(1), count_term.clone()),
                true,
            );
        if bounded {
            assumptions = assumptions.assume_condition(
                ConditionTerm::signed_less_equal(
                    count_term,
                    Bitvector32Term::Constant(crate::kernel::memory_range_element_count_limit(4)),
                ),
                true,
            );
        }
        (memory, assumptions)
    }

    /// The cell rules: `proves_memory_loadable` for a cell inside the range,
    /// which routes through `proves_loadable_region_from_structural_range` and
    /// `proves_loadable_cell_from_region`.
    #[test]
    fn a_cell_inside_a_wrapped_range_is_refused() {
        let count = Variable(9_100_000);
        for bounded in [false, true] {
            let (memory, assumptions) = context(count, bounded);
            assert_eq!(
                assumptions.proves_memory_access(&memory, &array_base(0), 4),
                bounded,
                "a cell inside `v[0..n]` needs the range's extent bound (bounded: {bounded})"
            );
            assert_eq!(
                assumptions.proves_memory_access(&memory, &array_base(4), 4),
                bounded,
                "so does a later cell (bounded: {bounded})"
            );
        }
    }

    /// The memory-resolution reader, which reads the same extent as an element
    /// count to place a pointer inside it.
    #[test]
    fn memory_resolution_refuses_a_wrapped_range() {
        let count = Variable(9_100_001);
        for bounded in [false, true] {
            let (memory, assumptions) = context(count, bounded);
            assert_eq!(
                assumptions.proves_memory_loadable_for_memory_resolution(
                    &memory,
                    &array_base(4),
                    &Bitvector32Term::Constant(4),
                ),
                bounded,
                "memory resolution reads the extent at element granularity too \
                 (bounded: {bounded})"
            );
        }
    }

    /// The region reader used by covering-span certification.
    #[test]
    fn a_region_read_refuses_a_wrapped_extent() {
        let count = Variable(9_100_002);
        for bounded in [false, true] {
            let (_, assumptions) = context(count, bounded);
            let extent = Bitvector32Term::multiply(
                Bitvector32Term::Variable(count),
                Bitvector32Term::Constant(4),
            );
            assert_eq!(
                assumptions.proves_loadable_cell_from_region(
                    &array_base(0),
                    &extent,
                    &array_base(4),
                    4,
                ),
                bounded,
                "a region's extent is read as an element count (bounded: {bounded})"
            );
        }
    }

    /// A constant range whose element count wraps is decided without facts,
    /// and so is the widest one that does not.
    #[test]
    fn a_constant_wrapped_extent_needs_no_facts_to_refuse() {
        let memory = CMemory::new();
        let wrapped = PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: array_base(0),
            bytes: Bitvector32Term::multiply(
                Bitvector32Term::Constant(WRAPPING_COUNT),
                Bitvector32Term::Constant(4),
            ),
        });
        // `1 << 30` four-byte elements scale to `0` bytes: the fact is true
        // and covers nothing, so no cell comes out of it.
        assert!(
            !wrapped.proves_memory_access(&memory, &array_base(0), 4),
            "a constant wrapped extent yields no cell"
        );
        let widest = PureFactContext::new().assume_proposition(Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: array_base(0),
            bytes: Bitvector32Term::multiply(
                Bitvector32Term::Constant(WRAPPING_COUNT - 1),
                Bitvector32Term::Constant(4),
            ),
        });
        assert!(
            widest.proves_memory_access(&memory, &array_base(0), 4),
            "one element fewer is the widest extent that fits, and it still works"
        );
    }

    /// One-byte elements cannot wrap: the extent is the count, unscaled, so
    /// nothing has to be established before reading it.
    #[test]
    fn a_byte_range_needs_no_extent_bound() {
        let count = Variable(9_100_004);
        let memory = CMemory::new();
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::CMemoryLoadable {
                memory: memory.clone(),
                base: array_base(0),
                bytes: Bitvector32Term::Variable(count),
            })
            .assume_condition(
                ConditionTerm::signed_less_than(
                    Bitvector32Term::Constant(1),
                    Bitvector32Term::Variable(count),
                ),
                true,
            );
        assert!(
            assumptions.proves_memory_access(&memory, &array_base(1), 1),
            "a one-byte element range is its own byte count"
        );
    }
}

/// What a stated range-loadable proposition carries, and what it does not.
///
/// Every site that makes these guards available does so by deriving them from
/// a proposition it already holds, so the derivation is the whole boundary
/// between "the range said this" and "the proof got it for free". Two
/// properties keep that boundary where it belongs: the derivation reads the
/// proposition and consults nothing, and it declines every shape whose range
/// is not a fact about the surrounding scope.
mod stated_range_guard_derivation {
    use super::*;

    fn int32_range_loadable(count: Bitvector32Term) -> Proposition {
        Proposition::CMemoryLoadable {
            memory: CMemory::new(),
            base: Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::multiply(count, Bitvector32Term::Constant(4)),
        }
    }

    /// A range states its count is nonnegative and fits, over the count term
    /// itself — the spelling a proof can write, since the endpoint form's
    /// `fits` half is an unsigned comparison the surface cannot express.
    #[test]
    fn a_range_carries_its_count_bounds() {
        let count = Bitvector32Term::Variable(Variable(9_200_000));
        assert_eq!(
            crate::kernel::stated_loadable_extent_guards(&int32_range_loadable(count.clone())),
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), count.clone()),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(
                        count,
                        Bitvector32Term::Constant(crate::kernel::memory_range_element_count_limit(
                            4
                        )),
                    ),
                    true,
                ),
            ]
        );
    }

    /// A conjunction is walked, because a `requires` clause is written as one.
    #[test]
    fn a_conjunction_of_ranges_carries_both() {
        let left = Bitvector32Term::Variable(Variable(9_200_001));
        let right = Bitvector32Term::Variable(Variable(9_200_002));
        let guards = crate::kernel::stated_loadable_extent_guards(&Proposition::And(
            Box::new(int32_range_loadable(left)),
            Box::new(int32_range_loadable(right)),
        ));
        assert_eq!(guards.len(), 4, "two ranges, two guards each: {guards:?}");
    }

    /// A quantified or implication-wrapped range carries nothing. Its bounds
    /// would be over a bound variable, which is not a fact about anything the
    /// surrounding scope can state, and instantiating such a fact therefore
    /// hands its instance no guard: the instance is read by the ordinary
    /// guarded readers instead.
    #[test]
    fn a_quantified_or_guarded_range_carries_nothing() {
        let bound = Variable(9_200_003);
        let body = int32_range_loadable(Bitvector32Term::Variable(bound));
        let quantified = Proposition::ForAll {
            var: bound,
            sort: Sort::CInt32,
            body: Box::new(body.clone()),
        };
        assert!(
            crate::kernel::stated_loadable_extent_guards(&quantified).is_empty(),
            "a quantified range states no scope-level bound"
        );
        let implication = Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Constant(true),
                true,
            )),
            Box::new(body),
        );
        assert!(
            crate::kernel::stated_loadable_extent_guards(&implication).is_empty(),
            "a conditional range states no unconditional bound"
        );
    }

    /// The guards move with the range. An induction hypothesis is the
    /// theorem's statement at a smaller argument, so substituting that
    /// argument into a range premise has to recompute the guards over the
    /// moved range rather than reuse the theorem's own: `v[lo..hi]` at
    /// `hi - 1` owes `0 <= (hi - 1) - lo`, not `0 <= hi - lo`.
    #[test]
    fn guards_follow_a_substituted_range() {
        let lo = Variable(9_200_010);
        let hi = Variable(9_200_011);
        let range = int32_range_loadable(Bitvector32Term::subtract(
            Bitvector32Term::Variable(hi),
            Bitvector32Term::Variable(lo),
        ));
        let moved = crate::kernel::substitute_int32_variable_in_proposition(
            &range,
            hi,
            Bitvector32Term::subtract(Bitvector32Term::Variable(hi), Bitvector32Term::Constant(1)),
        );
        let moved_count = Bitvector32Term::subtract(
            Bitvector32Term::subtract(Bitvector32Term::Variable(hi), Bitvector32Term::Constant(1)),
            Bitvector32Term::Variable(lo),
        );
        assert_eq!(
            crate::kernel::stated_loadable_extent_guards(&moved),
            crate::kernel::memory_range_element_count_guards(moved_count, 4),
            "the moved range's guards are over the moved count"
        );
        assert_ne!(
            crate::kernel::stated_loadable_extent_guards(&moved),
            crate::kernel::stated_loadable_extent_guards(&range),
            "and are not the guards of the range before substitution"
        );
    }

    /// An extent that is not a scaled element range carries nothing: a cell
    /// width and a block size are already true counts of bytes.
    #[test]
    fn an_unscaled_extent_carries_nothing() {
        let cell = Proposition::CMemoryLoadable {
            memory: CMemory::new(),
            base: Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: Bitvector32Term::Constant(4),
        };
        assert!(crate::kernel::stated_loadable_extent_guards(&cell).is_empty());
    }
}
