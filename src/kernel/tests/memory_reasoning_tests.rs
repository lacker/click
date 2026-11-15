// These tests exercise discovery explicitly through kernel::search::ProofSearch.
use super::*;
use crate::kernel::CompareRelation;
use crate::kernel::binary_node;

mod ordered_range_access_tests {
    use super::*;

    fn ordered_range(size: usize) -> (PureFactContext, Pointer, Vec<MachineTerm>, MachineTerm) {
        let indices = (0..=size)
            .map(|index| MachineTerm::Variable(Variable(9_740_000 - index as u64)))
            .collect::<Vec<_>>();
        let end = MachineTerm::Variable(Variable(9_750_000));
        let mut context = PureFactContext::new().assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), indices[0].clone()),
            true,
        );
        for pair in indices.windows(2) {
            context = context.assume_condition(
                ConditionTerm::signed_less_than(pair[0].clone(), pair[1].clone()),
                true,
            );
        }
        context = context.assume_condition(
            ConditionTerm::signed_less_than(indices[size].clone(), end.clone()),
            true,
        );
        let base = Pointer {
            block: "ordered-range-access".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        (context, base, indices, end)
    }

    fn covered(
        context: &PureFactContext,
        base: &Pointer,
        index: &MachineTerm,
        end: &MachineTerm,
    ) -> bool {
        context.pointer_access_in_range(
            &base.offset_by_elements(index.clone(), 4),
            4,
            base,
            &MachineTerm::constant(0),
            end,
            4,
        )
    }

    #[test]
    fn ordered_access_keeps_the_exclusive_end() {
        let _session = crate::kernel::VerificationSession::enter();
        let (context, base, indices, end) = ordered_range(8);
        for index in &indices {
            assert!(covered(&context, &base, index, &end));
        }
        assert!(!covered(&context, &base, &end, &end));
    }

    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/tests/memory_reasoning_tests/ordered_range_access_tests.rs"
        );
    }
}

#[test]
fn loadability_coverage_refuses_a_wrapped_byte_end() {
    let memory = Memory::new();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(9_300_000)),
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes: MachineTerm::constant(0x4000_0000),
        wide: false,
    });
    let goal = Proposition::MemoryLoadable {
        memory,
        base: base.offset_by_bytes(0x4000_0001),
        bytes: MachineTerm::constant(0xc000_0000),
        wide: false,
    };
    assert!(
        !crate::kernel::api::loadable_covered_by_fact(&assumptions, &goal),
        "a wrapped 32-bit end is not a covered byte count"
    );
}

#[test]
fn loadability_coverage_refuses_a_negative_signed_additive_shift() {
    let memory = Memory::new();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(9_300_003)),
    };
    let count = MachineTerm::Variable(Variable(9_300_004));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes: MachineTerm::add(count.clone(), MachineTerm::constant(1)),
        wide: false,
    });
    let goal = Proposition::MemoryLoadable {
        memory,
        base,
        bytes: MachineTerm::add(count, MachineTerm::constant(0x8000_0000)),
        wide: false,
    };
    assert!(
        !crate::kernel::api::loadable_covered_by_fact(&assumptions, &goal),
        "a large unsigned shift cannot be read as a negative signed shift"
    );
}

#[test]
fn loadability_coverage_compares_wide_concrete_extents_exactly() {
    let memory = Memory::new();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(9_300_001)),
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes: MachineTerm::constant(u32::MAX),
        wide: false,
    });
    let covered = Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: base.offset_by_bytes(0x8000_0000),
        bytes: MachineTerm::constant(1),
        wide: false,
    };
    assert!(crate::kernel::api::loadable_covered_by_fact(
        &assumptions,
        &covered
    ));

    let beyond = Proposition::MemoryLoadable {
        memory,
        base: base.offset_by_bytes(0x8000_0000),
        bytes: MachineTerm::constant(0x8000_0000),
        wide: false,
    };
    assert!(!crate::kernel::api::loadable_covered_by_fact(
        &assumptions,
        &beyond
    ));
}

#[test]
fn loadability_coverage_refuses_a_wrapped_pointer_displacement() {
    let memory = Memory::new();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(9_300_002)),
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: base.clone(),
        bytes: MachineTerm::constant(100),
        wide: false,
    });
    let goal = Proposition::MemoryLoadable {
        memory,
        base: base.offset_by_int32_elements(MachineTerm::constant(0x4000_0001)),
        bytes: MachineTerm::constant(4),
        wide: false,
    };
    assert!(
        !crate::kernel::api::loadable_covered_by_fact(&assumptions, &goal),
        "the physical pointer displacement exceeds the covering span"
    );
}

#[test]
fn memory_range_can_be_framed_as_a_byte_footprint() {
    let base = Pointer {
        block: "byte-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(2),
        MachineTerm::constant(5),
        1,
    );
    assert_eq!(range.element_width(), 1);

    let (byte_base, byte_length) = range.byte_footprint();
    assert_eq!(
        byte_base,
        base.offset_by_elements(MachineTerm::constant(2), 1)
    );
    assert_eq!(byte_length, MachineTerm::constant(3));

    let int32_range = MemoryRange::new(
        base.clone(),
        MachineTerm::constant(2),
        MachineTerm::constant(5),
    );
    assert_eq!(int32_range.element_width(), 4);
    let (int32_base, int32_length) = int32_range.byte_footprint();
    assert_eq!(
        int32_base,
        base.offset_by_elements(MachineTerm::constant(2), 4)
    );
    assert_eq!(int32_length, MachineTerm::constant(12));
    assert_ne!(range, int32_range);

    let rebased = range.with_bounds(base, MachineTerm::constant(0), MachineTerm::constant(3));
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
    let available = ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(
        MemoryRange::new_with_element_width(
            base.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(4),
            1,
        ),
    ));
    let int32_requirement = ResourceFact::own_memory(MemoryRange::new(
        base.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    assert!(available.satisfies_fact(&int32_requirement, &PureFactContext::new()));
    let int32_available = ResourceContext::new().unchecked_with_fact(int32_requirement.clone());
    assert!(int32_available.satisfies_fact(
        &ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(4),
            1,
        )),
        &PureFactContext::new()
    ));
    assert!(!int32_available.satisfies_fact(
        &ResourceFact::own_memory(MemoryRange::new_with_element_width(
            base.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(5),
            1,
        )),
        &PureFactContext::new()
    ));

    let byte_requirement = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base,
        MachineTerm::constant(1),
        MachineTerm::constant(3),
        1,
    ));
    assert!(available.satisfies_fact(&byte_requirement, &PureFactContext::new()));

    let int32_view_requirement = ResourceFact::view_memory(MemoryRange::new(
        Pointer {
            block: "typed-buffer".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    assert!(available.satisfies_fact(&int32_view_requirement, &PureFactContext::new()));

    let typed_available =
        ResourceContext::new().unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
            Pointer {
                block: "typed-object".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            MachineTerm::constant(0),
            MachineTerm::constant(2),
        )));
    let byte_view_requirement = ResourceFact::view_memory(MemoryRange::new_with_element_width(
        Pointer {
            block: "typed-object".into(),
            offset: PointerOffsetTerm::Constant(4),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(1),
        1,
    ));
    assert!(typed_available.satisfies_fact(&byte_view_requirement, &PureFactContext::new()));
    let outside_byte_view = ResourceFact::view_memory(MemoryRange::new_with_element_width(
        Pointer {
            block: "typed-object".into(),
            offset: PointerOffsetTerm::Constant(8),
        },
        MachineTerm::constant(0),
        MachineTerm::constant(1),
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
    let int32_range = MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(1),
        MachineTerm::constant(2),
        4,
    );
    let wide_range = MemoryRange::new_with_element_width(
        base.clone(),
        MachineTerm::constant(1),
        MachineTerm::constant(3),
        8,
    );
    let available = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(int32_range.clone()))
        .unchecked_with_fact(ResourceFact::own_memory(wide_range.clone()));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(int32_range)),
        right: Box::new(Resource::Memory(wide_range)),
    });
    let required = ResourceFact::own_memory(MemoryRange::new_with_element_width(
        base,
        MachineTerm::constant(1),
        MachineTerm::constant(2),
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
    let byte_field = base.offset_by_elements(MachineTerm::constant(1), 1);
    let assumptions = PureFactContext::new();

    assert!(assumptions.pointer_access_in_range(
        &byte_field,
        1,
        &base,
        &MachineTerm::constant(0),
        &MachineTerm::constant(2),
        4,
    ));
    assert!(!assumptions.pointer_access_in_range(
        &base.offset_by_elements(MachineTerm::constant(8), 1),
        1,
        &base,
        &MachineTerm::constant(0),
        &MachineTerm::constant(2),
        4,
    ));
}

#[test]
fn byte_range_containment_expands_constant_stride_arithmetic() {
    let index = MachineTerm::Variable(Variable(93_506));
    let repeated = MachineTerm::add(
        MachineTerm::add(index.clone(), index.clone()),
        MachineTerm::add(index.clone(), index.clone()),
    );
    let scaled = MachineTerm::multiply(index, MachineTerm::constant(4));
    let base = Pointer {
        block: "strided-byte-buffer".into(),
        offset: PointerOffsetTerm::scaled_int32_node(repeated, 1),
    };
    let pointer = Pointer {
        block: base.block.clone(),
        offset: PointerOffsetTerm::scaled_int32_node(
            MachineTerm::add(scaled, MachineTerm::constant(3)),
            1,
        ),
    };

    let range = MemoryRange::new_with_element_width(
        base,
        MachineTerm::constant(0),
        MachineTerm::constant(4),
        1,
    );
    // `4 * i + 3` is three bytes above `i + i + i + i` only while the scaling
    // does not wrap: at `4 * i == i32::MAX` the sum is `i32::MIN + 2`, nearly
    // `2^32` bytes *below* the base, and the range contains nothing of it. The
    // stride arithmetic is still expanded, and the offset it yields is still
    // read as an offset — once something pins the sum out of the wrapped
    // reading.
    let index_is_nonnegative = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_equal(
            MachineTerm::constant(0),
            pointer.offset.native_scaled_values_for_output()[0].clone(),
        ),
        true,
    );
    assert!(
        crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
            &pointer,
            &range,
            &index_is_nonnegative,
        )
    );
    assert!(!crate::kernel::assumptions::pointer_in_memory_range_shallow(&pointer, &range,));
}

#[test]
fn element_index_and_count_support_nonlegacy_widths() {
    for (element_width, index, byte_count) in
        [(1_u32, 3_u32, 3_u32), (2, 7, 14), (4, 5, 20), (8, 2, 16)]
    {
        let index_term = MachineTerm::Variable(Variable(93_600 + u64::from(element_width)));
        let offset =
            PointerOffsetTerm::scaled_int32_node(index_term.clone(), i64::from(element_width));
        assert_eq!(
            element_index_from_offset(&offset, element_width),
            Some(index_term)
        );
        assert_eq!(
            element_count_from_bytes(&MachineTerm::constant(byte_count), element_width),
            Some(MachineTerm::constant(index))
        );
    }
}

/// A 64-bit index is not an element index. `element_index_from_offset` used to
/// hand an `Int64Scaled` displacement's value straight back, so the term every
/// membership, order and equality rule then compared against 32-bit bounds was
/// one of a different width — the arm its exact sibling
/// `exact_element_delta_from_offset` already refused in writing.
#[test]
fn a_sixty_four_bit_index_is_an_element_index_only_where_it_is_pinned() {
    let value = MachineTerm::Variable(Variable(93_610));
    let wide = PointerOffsetTerm::scaled_int64_node(value.clone(), 8, false);
    let narrow = PointerOffsetTerm::scaled_int32_node(value.clone(), 8);
    let empty = PureFactContext::new();
    // The 32-bit index of the same width still answers, with and without facts.
    assert_eq!(element_index_from_offset(&narrow, 8), Some(value.clone()));
    assert_eq!(
        crate::kernel::reasoning::element_index_from_offset_with_facts(&narrow, 8, &empty),
        Some(value.clone())
    );
    // The 64-bit one does not, and nothing but a fact can make it.
    assert_eq!(element_index_from_offset(&wide, 8), None);
    assert_eq!(
        crate::kernel::reasoning::element_index_from_offset_with_facts(&wide, 8, &empty),
        None
    );

    let pinned = |constant: MachineTerm| {
        PureFactContext::new().assume_condition(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(value.clone()),
                right: Box::new(constant),
            },
            true,
        )
    };
    // Pinned to a number an `int32` holds, that number *is* the index.
    assert_eq!(
        crate::kernel::reasoning::element_index_from_offset_with_facts(
            &wide,
            8,
            &pinned(MachineTerm::int64_constant(1)),
        ),
        Some(MachineTerm::constant(1))
    );
    assert_eq!(
        crate::kernel::reasoning::element_index_from_offset_with_facts(
            &wide,
            8,
            &pinned(MachineTerm::int64_constant(-2)),
        ),
        Some(MachineTerm::constant((-2i32) as u32))
    );
    // Pinned outside it, there is no 32-bit index to answer with: element
    // `2^32 + 1` is not element `1`.
    assert_eq!(
        crate::kernel::reasoning::element_index_from_offset_with_facts(
            &wide,
            8,
            &pinned(MachineTerm::int64_constant(4_294_967_297)),
        ),
        None
    );
    assert_eq!(
        crate::kernel::reasoning::element_index_from_offset_with_facts(
            &wide,
            8,
            &pinned(MachineTerm::int64_constant(i64::from(i32::MAX) + 1)),
        ),
        None
    );
}

/// Exact wide strides retain native index comparisons in both branches.
#[test]
fn wide_offset_branches_publish_full_width_index_facts() {
    let index = MachineTerm::Variable(Variable(93_675));
    for unsigned in [false, true] {
        for (stride, target) in [(4, 0), (4, 8), (1, i64::MAX), (-4, -8)] {
            for reversed in [false, true] {
                for value in [false, true] {
                    let scaled =
                        PointerOffsetTerm::scaled_int64_node(index.clone(), stride, unsigned);
                    let constant = PointerOffsetTerm::Constant(target);
                    let (left, right) = if reversed {
                        (constant, scaled)
                    } else {
                        (scaled, constant)
                    };
                    let mut facts = crate::kernel::ExecutionFacts::new();
                    crate::kernel::reasoning::add_pointer_offset_equality_execution_pure_facts(
                        &mut facts,
                        &PureFactContext::new(),
                        left,
                        right,
                        value,
                    )
                    .unwrap();
                    let element = target / stride;
                    let condition = if unsigned {
                        ConditionTerm::uint64_equal(
                            index.clone(),
                            MachineTerm::uint64_constant(element as u64),
                        )
                    } else {
                        ConditionTerm::int64_equal(
                            index.clone(),
                            MachineTerm::int64_constant(element),
                        )
                    };
                    assert!(facts.iter().any(|fact| fact.proposition()
                        == &Proposition::ConditionIs(condition.clone(), value)));
                    // Even a constant whose low word is -1 must not produce
                    // a 32-bit comparison of this wide index.
                    assert!(!facts.iter().any(|fact| matches!(
                        fact.proposition(),
                        Proposition::ConditionIs(
                            ConditionTerm::Compare {
                                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                                ..
                            },
                            _
                        )
                    )));
                }
            }
        }
    }
    for (stride, target, unsigned) in [
        (0, 1, true),
        (4, 1, true),
        (4, -4, true),
        (-1, i64::MIN, false),
    ] {
        let mut facts = crate::kernel::ExecutionFacts::new();
        let _ = crate::kernel::reasoning::add_pointer_offset_equality_execution_pure_facts(
            &mut facts,
            &PureFactContext::new(),
            PointerOffsetTerm::scaled_int64_node(index.clone(), stride, unsigned),
            PointerOffsetTerm::Constant(target),
            false,
        );
        assert!(!facts.iter().any(|fact| matches!(
            fact.proposition(),
            Proposition::ConditionIs(ConditionTerm::Compare { .. }, _)
        )));
    }
}

/// A decided pointer-offset equality is also a statement about element
/// indices, and the two directions are not the same statement. The index a
/// byte offset folds to is the offset divided by the element width *modulo*
/// `2^32`, so equal offsets have equal indices and different offsets need
/// not have different ones.
#[test]
fn an_index_disequality_needs_the_folds_to_be_sums() {
    let i = MachineTerm::Variable(Variable(93_660));
    let j = MachineTerm::Variable(Variable(93_661));
    let k = MachineTerm::Variable(Variable(93_662));
    let scaled = |value: &MachineTerm| PointerOffsetTerm::scaled_int32_node(value.clone(), 4);
    // `p + i + j` against `p + k`: at `i == j == i32::MAX` and `k == -2` the
    // two offsets are `2^34` bytes apart and both indices are `-2`.
    let summed = PointerOffsetTerm::Add(Box::new(scaled(&i)), Box::new(scaled(&j)));
    let single = scaled(&k);
    let index_fact = Proposition::ConditionIs(
        crate::kernel::machine_integer::comparison::condition_for_operand_views(
            crate::kernel::MachineIntegerType::Int32,
            crate::kernel::CompareRelation::Equal,
            [
                crate::kernel::SharedMachineIntegerTerm::index(
                    crate::kernel::MachineIntegerType::Int32,
                    MachineTerm::add(i.clone(), j.clone()),
                )
                .operand_view(),
                crate::kernel::MachineOperandView::Legacy(&k),
            ],
        ),
        false,
    );

    let recorded = |assumptions: &PureFactContext, value: bool| {
        let mut facts = crate::kernel::ExecutionFacts::new();
        crate::kernel::reasoning::add_pointer_offset_equality_execution_pure_facts(
            &mut facts,
            assumptions,
            summed.clone(),
            single.clone(),
            value,
        )
        .expect("the offsets are undecided, so both polarities are consistent");
        facts
            .iter()
            .map(|fact| fact.proposition().clone())
            .collect::<Vec<_>>()
    };

    let empty = PureFactContext::new();
    // The disequality is refused: nothing says the fold of `i + j` is the sum.
    assert!(!recorded(&empty, false).contains(&index_fact));
    // The equality is arithmetic and needs no premise: equal offsets have
    // equal residues however either side wrapped.
    assert!(
        recorded(&empty, true).contains(&Proposition::ConditionIs(
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                crate::kernel::MachineIntegerType::Int32,
                crate::kernel::CompareRelation::Equal,
                [
                    crate::kernel::SharedMachineIntegerTerm::index(
                        crate::kernel::MachineIntegerType::Int32,
                        MachineTerm::add(i.clone(), j.clone())
                    )
                    .operand_view(),
                    crate::kernel::MachineOperandView::Legacy(&k)
                ],
            ),
            true,
        ))
    );

    // The premise is exactly that the one modular add does not carry, which
    // is the condition C's own `+` publishes.
    let unwrapped = PureFactContext::new().assume_condition(
        ConditionTerm::signed_add_overflows(i.clone(), j.clone()),
        false,
    );
    assert!(recorded(&unwrapped, false).contains(&index_fact));

    // One scaled index on each side folds with no add at all, so it is the
    // index exactly and the disequality is recorded with no premise.
    let mut facts = crate::kernel::ExecutionFacts::new();
    crate::kernel::reasoning::add_pointer_offset_equality_execution_pure_facts(
        &mut facts,
        &empty,
        scaled(&i),
        single,
        false,
    )
    .expect("two undecided offsets");
    let single_index_fact = Proposition::ConditionIs(ConditionTerm::equal(i, k), false);
    assert!(
        facts
            .iter()
            .any(|fact| fact.proposition() == &single_index_fact)
    );
}

/// The byte path rebuilds an `Int64Scaled` displacement as a *thirty-two-bit*
/// `Multiply` of a term whose own value is sixty-four bits wide. The
/// thirty-two-bit overflow question is therefore the wrong question about it,
/// and a low word of `0xFFFFFFFF` is what shows so: `-1 * 8` does not
/// overflow an `int32`, while the offset an unsigned index of `4294967295`
/// really names is `8 * 4294967295`, not `-8`.
#[test]
fn a_sixty_four_bit_displacement_is_exact_only_where_a_fact_pins_it() {
    let value = MachineTerm::Variable(Variable(93_670));
    let wide = |unsigned: bool| PointerOffsetTerm::scaled_int64_node(value.clone(), 8, unsigned);
    let decide = |assumptions: &PureFactContext, unsigned: bool, target: i64| {
        assumptions.decide(&ConditionTerm::pointer_offset_equal(
            wide(unsigned),
            PointerOffsetTerm::Constant(target),
        ))
    };

    let low_word_is_minus_one = PureFactContext::new().assume_condition(
        ConditionTerm::equal(value.clone(), MachineTerm::constant(0xFFFF_FFFF)),
        true,
    );
    // A thirty-two-bit fact says nothing about a sixty-four-bit value, so
    // neither reading may be affirmed.
    assert_eq!(decide(&low_word_is_minus_one, true, -8), None);
    assert_eq!(decide(&low_word_is_minus_one, false, -8), None);

    let pinned = |constant: i64| {
        PureFactContext::new().assume_condition(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(value.clone()),
                right: Box::new(MachineTerm::int64_constant(constant)),
            },
            true,
        )
    };
    // Pinned to a number whose scaled product occupies an `int32`, the
    // rebuilt term is the offset and the equality is decided both ways.
    assert_eq!(decide(&pinned(1), false, 8), Some(true));
    assert_ne!(decide(&pinned(1), false, 16), Some(true));
    assert_eq!(decide(&pinned(-1), false, -8), Some(true));
    // An unsigned index read signed is only the unsigned one while it is
    // nonnegative.
    assert_eq!(decide(&pinned(-1), true, -8), None);
    // The exact wide product remains distinguishable from zero even when
    // it leaves int32: no truncated displacement participates in this check.
    assert_eq!(
        decide(&pinned(i64::from(i32::MAX) + 1), false, 0),
        Some(false)
    );
    assert_eq!(decide(&pinned(4_294_967_295), true, -8), None);
}

#[test]
fn byte_pointer_distinctness_uses_byte_scaled_indices() {
    let i = MachineTerm::Variable(Variable(93_500));
    let j = MachineTerm::Variable(Variable(93_501));
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
    let i = MachineTerm::Variable(Variable(93_502));
    let j = MachineTerm::Variable(Variable(93_503));
    let base = Pointer {
        block: "byte-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written = base.offset_by_elements(i.clone(), 1);
    let read = base.offset_by_elements(j.clone(), 1);
    crate::kernel::eval::declare_load_access_width(&read, 1);
    let before = Memory::new();
    let after = before.clone().store(written.clone(), uint8(7));
    let assumptions =
        PureFactContext::new().assume_condition(ConditionTerm::equal(i.clone(), j.clone()), false);
    let assumptions = explicit_signed_elements(base, ProgramType::UInt8, i, j, assumptions);
    let effect = Proposition::MemoryMutatesOnly {
        before: before.clone(),
        after: after.clone(),
        writes: vec![(written, 1)],
    };
    let (_, _, equality) = explicit_frame(
        &before,
        &after,
        &read,
        ProgramType::UInt8,
        &[effect.clone()],
        &assumptions,
    )
    .expect("distinct byte cells have an explicit frame");
    assert!(
        assumptions
            .clone()
            .assume_proposition(equality.clone())
            .contains_known(&equality)
    );
    assert!(
        explicit_frame(
            &before,
            &after,
            &read,
            ProgramType::Int32,
            &[effect.clone()],
            &assumptions
        )
        .is_none(),
        "unequal byte indices do not separate an overlapping four-byte read"
    );
    assert!(
        explicit_frame(
            &before,
            &after,
            &read,
            ProgramType::UInt8,
            &[effect],
            &PureFactContext::new()
        )
        .is_none(),
        "an unknown alias cannot be framed"
    );
}

#[test]
fn byte_pointer_access_is_contained_by_a_byte_range() {
    let index = MachineTerm::Variable(Variable(93_504));
    let length = MachineTerm::Variable(Variable(93_505));
    let base = Pointer {
        block: "byte-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let pointer = base.offset_by_elements(index.clone(), 1);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(index.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(index, length.clone()), true);

    assert!(assumptions.pointer_access_in_range(
        &pointer,
        1,
        &base,
        &MachineTerm::constant(0),
        &length,
        1,
    ));
}

#[test]
fn structural_range_offset_precedes_proof_aware_pointer_resolution() {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(93_301)), 4),
    };
    let required = memory_range(
        base.offset_by_int32_elements(MachineTerm::constant(2)),
        0,
        1,
    );
    let assumptions = PureFactContext::new();
    PureFactContext::reset_proof_aware_pointer_index_queries();

    assert!(assumptions.range_covered_by_fact_range(
        &required,
        &base,
        &MachineTerm::constant(0),
        &MachineTerm::constant(8),
    ));
    assert_eq!(PureFactContext::proof_aware_pointer_index_queries(), 0);
}

#[test]
fn safe_positive_subtraction_is_below_its_base() {
    let x = MachineTerm::Variable(Variable(87));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::signed_greater_equal(x.clone(), MachineTerm::constant(1)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            MachineTerm::subtract(x.clone(), MachineTerm::constant(1)),
            x,
        )),
        Some(true)
    );
}

#[test]
fn mutable_frame_proves_unwritten_load_equal_across_stack_locals() {
    let i = Variable(74);
    let i_bits = MachineTerm::Variable(i);
    let old_memory = Memory::new();
    let loop_entry_memory = Memory::new()
        .with_block("local:i", 4)
        .store(Memory::local_pointer("i"), int32(1));
    let loop_exit_memory = Memory::new()
        .with_block("local:i", 4)
        .store(Memory::local_pointer("i"), int32(i_bits.clone()));
    let first_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::scaled_int32_node(i_bits.clone(), 4),
    };
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(i_bits, MachineTerm::constant(1)),
            true,
        )
        .assume_proposition(Proposition::MemoryMutatesOnly {
            before: loop_entry_memory,
            after: loop_exit_memory.clone(),
            writes: vec![(written_cell, 4)],
        });

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(loop_exit_memory),
                    Box::new(first_cell.clone()),
                    crate::kernel::LoadKind::Int32,
                ),
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(old_memory),
                    Box::new(first_cell),
                    crate::kernel::LoadKind::Int32
                ),
            ),
            true,
        )
    ));
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
    // The transported load is the `int32` at offset zero. Say so: a
    // width-less load stands in eight bytes, which the first write at offset
    // four overlaps, and the two states then do not agree about it.
    crate::kernel::eval::declare_load_access_width(&preserved, 4);
    let before = Memory::new();
    let middle = before.clone().store(first_write.clone(), int32(1));
    let after = middle.clone().store(second_write.clone(), int32(2));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::MemoryMutatesOnly {
            before: before.clone(),
            after: middle.clone(),
            writes: vec![(first_write, 4)],
        })
        .assume_proposition(Proposition::MemoryMutatesOnly {
            before: middle,
            after: after.clone(),
            writes: vec![(second_write, 4)],
        });

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(after),
                    Box::new(preserved.clone()),
                    crate::kernel::LoadKind::Int32
                ),
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(before),
                    Box::new(preserved),
                    crate::kernel::LoadKind::Int32
                ),
            ),
            true,
        )
    ));
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
    let before = Memory::new();
    let mut after = before.clone();
    let mut assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
        memory: before,
        base: loadable.clone(),
        bytes: MachineTerm::constant(4),
        wide: false,
    });
    for value in 0..12 {
        let next = after.clone().store(written.clone(), int32(value));
        assumptions = assumptions.assume_proposition(Proposition::MemoryMutatesOnly {
            before: after,
            after: next.clone(),
            writes: vec![(written.clone(), 4)],
        });
        after = next;
    }

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory: after,
            base: loadable,
            bytes: MachineTerm::constant(4),
            wide: false,
        }
    ));
}

#[test]
fn target_directed_transport_preserves_pointer_field_across_disjoint_buffer_write() {
    let base = MachineTerm::Variable(Variable(90_001));
    let buffer = MachineTerm::Variable(Variable(90_002));
    let index = MachineTerm::Variable(Variable(90_003));
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
    let old_memory = Memory::new();
    let current_memory = old_memory.clone().store(written_pointer.clone(), int32(7));
    let old_offset = PointerOffsetTerm::scale_int32(
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(old_memory),
            Box::new(field_pointer.clone()),
            crate::kernel::LoadKind::Int32,
        ),
        4,
    );
    let current_offset = PointerOffsetTerm::scale_int32(
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(current_memory),
            Box::new(field_pointer.clone()),
            crate::kernel::LoadKind::Int32,
        ),
        4,
    );
    let separation = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(memory_range(field_pointer, 0, 1))),
        right: Box::new(Resource::Memory(memory_range(written_pointer, 0, 1))),
    };
    let assumptions = PureFactContext::new().assume_proposition(separation.clone());
    let source = Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    let target = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(current_offset, old_offset),
        true,
    );

    let theorem = prove_program_condition_fact_target_transport(&source, &target, &assumptions)
        .expect("an explicit frame should preserve the pointer-valued field load");
    let (premises, theorem_target) = program_condition_fact_transport_parts(&theorem, &source)
        .expect("target transport retains its explicit source");
    assert_eq!(premises, vec![&separation]);
    assert_eq!(theorem_target, &target);
    assert_eq!(
        program_condition_fact_transport_target_in_context(
            &theorem,
            &source,
            &PureFactContext::new()
        ),
        None,
    );
    assert_eq!(
        program_condition_fact_transport_target_in_context(&theorem, &source, &assumptions),
        Some(&target),
        "the source is intrinsically true and the retained frame premise is present",
    );
}

#[test]
fn condition_transport_consumer_accepts_its_separately_proved_source() {
    let source = Proposition::ConditionIs(ConditionTerm::Variable(Variable(90_004)), true);
    let target = Proposition::ConditionIs(ConditionTerm::Variable(Variable(90_005)), true);
    let theorem = program_condition_fact_transport_theorem(&source, target.clone(), []);

    assert_eq!(
        program_condition_fact_transport_target_in_context(
            &theorem,
            &source,
            &PureFactContext::new()
        ),
        Some(&target),
        "the source is the innermost theorem premise, not retained context",
    );
}

#[test]
fn unrelated_external_cell_store_preserves_memory_load_with_stack_temporary() {
    let old_memory = Memory::new();
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p1 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let stack_memory = Memory::new()
        .with_block("local:tmp", 4)
        .store(Memory::local_pointer("tmp"), int32(0));
    let current_memory = stack_memory.clone().store(
        p0.clone(),
        int32(MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(stack_memory),
            Box::new(p0),
            crate::kernel::LoadKind::Int32,
        )),
    );

    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(current_memory),
                    Box::new(p1.clone()),
                    crate::kernel::LoadKind::Int32
                ),
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(old_memory),
                    Box::new(p1),
                    crate::kernel::LoadKind::Int32
                ),
            ),
            true,
        )
    ));
}

#[test]
fn target_directed_transport_preserves_one_old_load_form() {
    let old_memory = Memory::new();
    let written = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let preserved = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let current_memory = old_memory.clone().store(written, int32(7));
    let old_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(old_memory),
        Box::new(preserved.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let current_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(current_memory),
        Box::new(preserved),
        crate::kernel::LoadKind::Int32,
    );
    let source = Proposition::ConditionIs(
        ConditionTerm::equal(old_load.clone(), old_load.clone()),
        true,
    );
    let target = Proposition::ConditionIs(ConditionTerm::equal(current_load, old_load), true);

    let theorem =
        prove_program_condition_fact_target_transport(&source, &target, &PureFactContext::new())
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
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(41_000)), 4),
    };
    let data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(41_001)), 4),
    };
    let length = MachineTerm::Variable(Variable(41_002));
    let owner_range = memory_range(owner.clone(), 0, 4);
    let data_range = memory_range(data.clone(), 0, length.clone());
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(owner_range.clone())),
            right: Box::new(Resource::Memory(data_range.clone())),
        })
        .assume_proposition(Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(MachineTerm::constant(2), length.clone()),
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

    let memory = Memory::new().with_block("call-havoc:0", 0);
    let data_field = owner.offset_by_int32_elements(2.into());
    let loaded_data_offset = PointerOffsetTerm::scale_int32(
        MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(memory),
            Box::new(data_field),
            crate::kernel::LoadKind::Int32,
        ),
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
            ConditionTerm::signed_less_than(MachineTerm::constant(1), length),
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
    let memory = Memory::new().with_block("call-havoc:0", 0);
    let loaded_data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory.clone()),
                Box::new(owner.offset_by_int32_elements(2.into())),
                crate::kernel::LoadKind::Int32,
            ),
            4,
        ),
    };
    let loaded_length = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory),
        Box::new(owner.offset_by_int32_elements(1.into())),
        crate::kernel::LoadKind::Int32,
    );
    let named_data = Pointer {
        block: owner.block.clone(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(41_100)), 4),
    };
    let named_length = MachineTerm::Variable(Variable(41_101));
    let loaded = Resource::Memory(memory_range(loaded_data.clone(), 0, loaded_length.clone()));
    let named = Resource::Memory(memory_range(named_data.clone(), 0, named_length.clone()));

    assert!(!resources_directly_match(
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
    assert!(resources_directly_match(&loaded, &named, &assumptions));
}

#[test]
fn memory_range_endpoint_match_uses_graph_loads_in_one_state() {
    let _session = crate::kernel::VerificationSession::enter();
    let before = crate::kernel::intern_memory(Memory::new().with_block("range", 16));
    let pointer = |index| Pointer {
        block: "range".into(),
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let load = |memory: &SharedMemory, index| {
        MachineTerm::Variable(load_variable_for_cell_with_origin(
            memory,
            &pointer(index),
            crate::kernel::LoadKind::Int32,
            4,
            memory,
        ))
    };
    let (a, b) = (
        MachineTerm::Variable(Variable(41_110)),
        MachineTerm::Variable(Variable(41_111)),
    );
    let after = crate::kernel::intern_memory(before.memory().clone().store(
        pointer(b.clone()),
        ProgramValue::Int32(MachineTerm::constant(9)),
    ));
    let resource = |end| {
        Resource::Memory(MemoryRange::new(
            Pointer::symbolic(Variable(41_112)),
            MachineTerm::constant(0),
            end,
        ))
    };
    let left = resource(load(&before, a.clone()));
    let right = resource(load(&before, b.clone()));
    let later = resource(load(&after, b.clone()));
    let premise = ConditionTerm::equal(a, b);
    let parent = PureFactContext::new();
    let branch = parent.clone().assume_condition(premise.clone(), true);
    let _scope = branch.enter_id_scope();
    PureFactContext::reset_bitvector_equality_index_fact_visits();
    assert!(resources_directly_match(&left, &right, &branch));
    assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
    assert!(!resources_directly_match(&left, &later, &branch));
    assert!(!resources_directly_match(&left, &right, &parent));
}

#[test]
fn direct_composite_resource_match_checks_pointer_load_across_block_declaration() {
    let entry = Memory::new().with_block("arg-memory", 32);
    let field = arc_pointer(16);
    let later = entry.clone().with_block("local:pivot", 4);
    let resource_at = |memory: Memory| Resource::Composite {
        name: "tree".to_string(),
        arguments: vec![
            ProgramValue::Pointer(PointerValue::from_read(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(
                        MachineTerm::MemoryLoad(
                            crate::kernel::intern_memory(memory.clone()),
                            Box::new(field.clone()),
                            crate::kernel::LoadKind::Int32,
                        ),
                        4,
                    ),
                },
                ProgramType::Int32Pointer,
                &crate::kernel::intern_memory(memory),
                &field,
            ))
            .into(),
        ]
        .into(),
    };

    assert!(resources_directly_match(
        &resource_at(entry.clone()),
        &resource_at(later.clone()),
        &PureFactContext::new(),
    ));
    // A write to either half of the complete pointer representation breaks
    // the read identity even when the storage allocation remains live.
    for displacement in [0, 4] {
        let overwritten = later.clone().store(
            field.clone().offset_by_bytes(displacement),
            ProgramValue::Int32(MachineTerm::constant(0)),
        );
        assert!(!resources_directly_match(
            &resource_at(entry.clone()),
            &resource_at(overwritten),
            &PureFactContext::new(),
        ));
    }
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
        PureFactContext::new().assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(memory_range(left.clone(), 0, 1))),
            right: Box::new(Resource::Memory(memory_range(right.clone(), 0, 1))),
        });
    for index in 0..128 {
        assumptions = assumptions.assume_proposition(Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::Variable(Variable(93_000 + index)),
                MachineTerm::constant(index as u32),
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
    let index = MachineTerm::Variable(Variable(93_100));
    let end = MachineTerm::Variable(Variable(93_101));
    let left = left_base.offset_by_int32_elements(index.clone());
    let right = right_base.clone();
    let left_range = MemoryRange::new(left_base, MachineTerm::constant(0), end.clone());
    let right_range = memory_range(right_base, 0, 1);
    let checks = [16_usize, 64, 256, 1_024, 4_096]
        .into_iter()
        .map(|unrelated| {
            let mut assumptions = PureFactContext::new()
                .assume_proposition(Proposition::ResourceSeparate {
                    left: Box::new(Resource::Memory(left_range.clone())),
                    right: Box::new(Resource::Memory(right_range.clone())),
                })
                .assume_condition(
                    ConditionTerm::signed_less_equal(
                        MachineTerm::constant(0),
                        index.clone(),
                    ),
                    true,
                )
                .assume_condition(
                    ConditionTerm::signed_less_than(index.clone(), end.clone()),
                    true,
                );
            for fact in 0..unrelated {
                assumptions = assumptions.assume_proposition(Proposition::ResourceSeparate {
                    left: Box::new(Resource::Memory(memory_range(
                        Pointer {
                            block: format!("unrelated-left-{fact}").into(),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        0,
                        1,
                    ))),
                    right: Box::new(Resource::Memory(memory_range(
                        Pointer {
                            block: format!("unrelated-right-{fact}").into(),
                            offset: PointerOffsetTerm::Constant(0),
                        },
                        0,
                        1,
                    ))),
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
    let memory = Memory::new();
    let target = Pointer {
        block: "indexed-viewable-target".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let mut assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
        memory: memory.clone(),
        base: target.clone(),
        bytes: MachineTerm::constant(8),
        wide: false,
    });
    for index in 0..128 {
        assumptions = assumptions.assume_proposition(Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: Pointer {
                block: format!("indexed-viewable-unrelated-{index}").into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: MachineTerm::constant(4),
            wide: false,
        });
    }

    assert_eq!(
        assumptions.memory_loadable_candidate_count(&target.block),
        1
    );
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory,
            base: target,
            bytes: MachineTerm::constant(4),
            wide: false,
        }
    ));
}

#[test]
fn equivalent_memory_load_order_facts_can_be_inconsistent() {
    let old_memory = Memory::new();
    let stack_memory = Memory::new()
        .with_block("local:tmp", 4)
        .store(Memory::local_pointer("tmp"), int32(0));
    let p0 = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let old_p0 = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(old_memory),
        Box::new(p0.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let stack_p0 = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(stack_memory),
        Box::new(p0),
        crate::kernel::LoadKind::Int32,
    );
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(old_p0.clone(), stack_p0.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(stack_p0, old_p0), true);

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &false_equals_true_proposition()
    ));
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
    let memory_a = Memory::new()
        .with_block("local:i", 4)
        .store(Memory::local_pointer("i"), int32(0));
    let memory_b = Memory::new()
        .with_block("local:i", 4)
        .store(Memory::local_pointer("i"), int32(1));
    let left_a = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory_a.clone()),
        Box::new(p0.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let right_a = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory_a),
        Box::new(p1.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let left_b = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory_b.clone()),
        Box::new(p0),
        crate::kernel::LoadKind::Int32,
    );
    let right_b = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory_b),
        Box::new(p1),
        crate::kernel::LoadKind::Int32,
    );
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_than(left_a, right_a), true)
        .assume_condition(ConditionTerm::signed_less_than(left_b, right_b), false);

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &false_equals_true_proposition()
    ));
}

#[test]
fn disjoint_range_proves_mutable_frame_cell_distinct() {
    let i = Variable(81);
    let j = Variable(82);
    let i_bits = MachineTerm::Variable(i);
    let j_bits = MachineTerm::Variable(j);
    let before_memory = Memory::new();
    let after_memory = Memory::new();
    let base = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let written_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::scaled_int32_node(i_bits.clone(), 4),
    };
    let read_cell = Pointer {
        block: "p".into(),
        offset: PointerOffsetTerm::scaled_int32_node(j_bits.clone(), 4),
    };
    let i_plus_one = binary_node!(
        Int32,
        Add,
        Box::new(i_bits.clone()),
        Box::new(MachineTerm::constant(1)),
    );
    let j_plus_one = binary_node!(
        Int32,
        Add,
        Box::new(j_bits.clone()),
        Box::new(MachineTerm::constant(1)),
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
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                base.clone(),
                i_bits.clone(),
                i_plus_one,
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                base,
                j_bits.clone(),
                j_plus_one,
            ))),
        })
        .assume_proposition(Proposition::MemoryMutatesOnly {
            before: before_memory.clone(),
            after: after_memory.clone(),
            writes: vec![(written_cell, 4)],
        });

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(after_memory),
                    Box::new(read_cell.clone()),
                    crate::kernel::LoadKind::Int32
                ),
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(before_memory),
                    Box::new(read_cell),
                    crate::kernel::LoadKind::Int32
                ),
            ),
            true,
        )
    ));
}

#[test]
fn disjoint_ranges_frame_metadata_across_symbolic_index_store() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(83)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(84)), 4),
    };
    let index = MachineTerm::Variable(Variable(85));
    let capacity = MachineTerm::Variable(Variable(86));
    let metadata_cell = owner.clone();
    let written_cell = data.offset_by_int32_elements(index.clone());
    let before_memory = Memory::new();
    let after_memory = before_memory.clone().store(written_cell.clone(), int32(7));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index, capacity.clone()),
            true,
        )
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                owner,
                MachineTerm::constant(0),
                MachineTerm::constant(4),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                data,
                MachineTerm::constant(0),
                capacity,
            ))),
        })
        .assume_proposition(Proposition::MemoryMutatesOnly {
            before: before_memory.clone(),
            after: after_memory.clone(),
            writes: vec![(written_cell, 4)],
        });

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(after_memory),
                    Box::new(metadata_cell.clone()),
                    crate::kernel::LoadKind::Int32,
                ),
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(before_memory),
                    Box::new(metadata_cell),
                    crate::kernel::LoadKind::Int32
                ),
            ),
            true,
        )
    ));
}

#[test]
fn equivalent_field_derived_bases_frame_symbolic_index_store() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(87)), 4),
    };
    let owner_data_cell = owner.offset_by_int32_elements(MachineTerm::constant(2));
    let base_memory = Memory::new();
    let execution_memory = base_memory
        .clone()
        .with_block("local:data", 8)
        .store(Memory::local_pointer("data"), int32(0));
    let resource_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(base_memory.clone()),
                Box::new(owner_data_cell.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            4,
        ),
    };
    let execution_data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(execution_memory.clone()),
                Box::new(owner_data_cell.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            4,
        ),
    };
    let index = MachineTerm::Variable(Variable(88));
    let capacity = MachineTerm::Variable(Variable(89));
    let metadata_cell = owner.clone();
    let written_cell = execution_data.offset_by_int32_elements(index.clone());
    let after_memory = execution_memory
        .clone()
        .store(written_cell.clone(), int32(7));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), capacity.clone()),
            true,
        )
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                owner.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(4),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                resource_data.clone(),
                MachineTerm::constant(0),
                capacity.clone(),
            ))),
        })
        .assume_proposition(Proposition::MemoryMutatesOnly {
            before: execution_memory.clone(),
            after: after_memory.clone(),
            writes: vec![(written_cell.clone(), 4)],
        });

    let (_, _, base_equality) = super::explicit_frame(
        &base_memory,
        &execution_memory,
        &owner_data_cell,
        ProgramType::Int32,
        &[Proposition::MemoryMutatesOnly {
            before: base_memory.clone(),
            after: execution_memory.clone(),
            writes: vec![(Memory::local_pointer("data"), 4)],
        }],
        &assumptions,
    )
    .expect("initializing the local preserves the owner's data field");
    // First connect the two explicit spellings of the array base.
    let address_equality = Proposition::ConditionIs(
        ConditionTerm::pointer_equal(execution_data.clone(), resource_data.clone()),
        true,
    );
    let base_premises = [base_equality.clone()];
    assert!(
        crate::kernel::proof::fact_reasoning::normalize_using_conditions(
            &address_equality,
            &base_premises,
            &crate::kernel::proof::ProofFacts::from_ordered(&base_premises),
        )
        .is_ok(),
        "the preserved field gives equal array addresses"
    );
    let owner_range = Resource::Memory(MemoryRange::new(owner.clone(), 0u32.into(), 4u32.into()));
    let old_data_range = Resource::Memory(MemoryRange::new(
        resource_data.clone(),
        0u32.into(),
        capacity.clone(),
    ));
    let parent_separation = Proposition::ResourceSeparate {
        left: Box::new(owner_range.clone()),
        right: Box::new(old_data_range),
    };
    assert!(assumptions.proves_exact(&parent_separation));
    let rewritten = crate::kernel::proof::term_rewrite::TermRewrite::for_pointer_exact(
        &resource_data,
        &execution_data,
    )
    .proposition(&parent_separation);
    let mut assumptions = assumptions
        .assume_proposition(base_equality)
        .assume_proposition(address_equality)
        .assume_proposition(rewritten);

    // Solve only the written arithmetic bounds, then instantiate subrange.
    let next = MachineTerm::add(index.clone(), 1u32.into());
    let bounds = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), capacity.clone()),
            true,
        );
    for condition in [
        ConditionTerm::signed_less_equal(index.clone(), next.clone()),
        ConditionTerm::signed_less_equal(next.clone(), capacity.clone()),
    ] {
        let fact = Proposition::ConditionIs(condition, true);
        assert!(
            crate::kernel::search::ProofSearch::proves(&(bounds), &fact),
            "selected index bounds imply {fact:?}"
        );
        assumptions = assumptions.assume_proposition(fact);
    }
    fn apply_law(law: Theorem, facts: &mut PureFactContext) -> Proposition {
        let mut result = law.proposition();
        while let Proposition::Implies(premise, body) = result {
            assert!(
                facts.proves_exact(premise),
                "explicit law premise: {premise:?}"
            );
            result = body;
        }
        let result = result.clone();
        *facts = facts.clone().assume_proposition(result.clone());
        result
    }
    apply_law(
        crate::kernel::prove_separation_subrange(
            PointerValue::new(execution_data.clone(), ProgramType::Int32Pointer),
            4,
            MachineIntegerType::Int32,
            0u32.into(),
            capacity.clone(),
            index.clone(),
            next.clone(),
        ),
        &mut assumptions,
    );
    let metadata = Resource::Memory(MemoryRange::new(owner.clone(), 0u32.into(), 1u32.into()));
    let data_range = Resource::Memory(MemoryRange::new(
        execution_data.clone(),
        0u32.into(),
        capacity,
    ));
    let window = Resource::Memory(MemoryRange::new(execution_data, index, next));
    let cell = Resource::Memory(MemoryRange::new(
        written_cell.clone(),
        0u32.into(),
        1u32.into(),
    ));
    for (parent, child) in [
        (owner_range.clone(), metadata.clone()),
        (metadata.clone(), metadata.clone()),
        (window.clone(), cell.clone()),
    ] {
        let fact = Proposition::ResourceContains {
            parent: Box::new(parent),
            child: Box::new(child),
        };
        assert!(
            crate::kernel::proof::fact_reasoning::normalizes_context_free_leaf(&fact),
            "explicit descriptor containment: {fact:?}"
        );
        assumptions = assumptions.assume_proposition(fact);
    }
    apply_law(
        crate::kernel::prove_separation_restrict(
            owner_range,
            data_range,
            metadata.clone(),
            window.clone(),
        ),
        &mut assumptions,
    );
    let cell_separation = apply_law(
        crate::kernel::prove_separation_restrict(metadata.clone(), window, metadata, cell),
        &mut assumptions,
    );
    let assumptions = assumptions.assume_proposition(
        crate::kernel::region_footprint::byte_premise(&cell_separation).unwrap(),
    );
    let (_, _, equality) = super::explicit_frame(
        &execution_memory,
        &after_memory,
        &metadata_cell,
        ProgramType::Int32,
        &[Proposition::MemoryMutatesOnly {
            before: execution_memory.clone(),
            after: after_memory.clone(),
            writes: vec![(written_cell, 4)],
        }],
        &assumptions,
    )
    .expect("the selected data element is separate from owner metadata");
    assert!(
        assumptions
            .assume_proposition(equality.clone())
            .contains_known(&equality)
    );
}

#[test]
fn direct_transport_composes_framed_loads_inside_an_indexed_address() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(95)), 4),
    };
    let owner_len_cell = owner.clone();
    let owner_data_cell = owner.offset_by_int32_elements(MachineTerm::constant(2));
    let before = Memory::new();
    let data_value = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before.clone()),
        Box::new(owner_data_cell),
        crate::kernel::LoadKind::Int32,
    );
    let length = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before.clone()),
        Box::new(owner_len_cell),
        crate::kernel::LoadKind::Int32,
    );
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(data_value, 4),
    };
    let index = MachineTerm::Variable(Variable(96));
    let capacity = MachineTerm::Variable(Variable(97));
    let written_cell = data.offset_by_int32_elements(index.clone());
    let terminator_cell = data.offset_by_int32_elements(length.clone());
    let after = before.clone().store(written_cell.clone(), int32(7));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(before.clone()),
                Box::new(terminator_cell),
                crate::kernel::LoadKind::Int32,
            ),
            MachineTerm::constant(0),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_than(index, length), true)
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                owner,
                MachineTerm::constant(0),
                MachineTerm::constant(4),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                data,
                MachineTerm::constant(0),
                capacity,
            ))),
        })
        .assume_proposition(Proposition::MemoryMutatesOnly {
            before,
            after: after.clone(),
            writes: vec![(written_cell, 4)],
        });

    let theorem = prove_program_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("the address loads and then the indexed cell should transport");
    let (premises, target) = program_condition_fact_transport_parts(&theorem, &fact)
        .expect("transport theorem must retain its explicit source");
    assert!(!premises.is_empty());
    assert!(
        premises
            .iter()
            .all(|premise| assumptions.proves_exact(premise))
    );
    assert_ne!(target, &fact);
    assert_eq!(program_condition_fact_memories(target), vec![after]);
}

#[test]
fn direct_transport_rewrites_loads_inside_pointer_equality() {
    let before = Memory::new();
    let field_cell = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(8),
    };
    let field_value = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(before.clone()),
                Box::new(field_cell.clone()),
                crate::kernel::LoadKind::Int32,
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

    let theorem =
        prove_program_condition_fact_direct_transport(&fact, &after, &PureFactContext::new())
            .expect(
                "an unrelated local-memory change should transport a pointer-valued field load",
            );
    let Proposition::Implies(source, target) = theorem.proposition() else {
        panic!("transport theorem must be an implication");
    };
    assert_eq!(source.as_ref(), &fact);
    let transported_field_value = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(after),
                Box::new(field_cell),
                crate::kernel::LoadKind::Int32,
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
fn packed_word_pointer_transport_requires_all_eight_bytes() {
    let _session = crate::kernel::VerificationSession::enter();
    let field = Pointer {
        block: "packed-word-frame".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = crate::kernel::intern_memory(Memory::new().with_block("packed-word-frame", 32));
    let bits = MachineTerm::MemoryLoad(
        before.clone(),
        Box::new(field.clone()),
        crate::kernel::LoadKind::Bits64,
    );
    let pointer = PointerValue::from_read(
        Pointer::integer_address(bits),
        ProgramType::VoidPointer,
        &before,
        &field,
    );
    let parent = PointerValue::new(
        Pointer::symbolic(Variable(9_889_501)),
        ProgramType::VoidPointer,
    );
    let source = Proposition::ConditionIs(
        ConditionTerm::PointerValueEqual(Box::new(pointer), Box::new(parent)),
        true,
    );
    let context = PureFactContext::new().assume_proposition(source.clone());
    for offset in [8, 12, 24] {
        let after = before.memory().clone().store(
            field.offset_by_bytes(offset),
            ProgramValue::UInt32(MachineTerm::constant(7)),
        );
        let theorem = prove_program_condition_fact_transport(&source, &after, &context)
            .expect("separate metadata preserves the complete packed pointer");
        let (_, target) =
            crate::kernel::program_condition_fact_transport_parts(&theorem, &source).unwrap();
        assert_ne!(target, &source);
    }
    for offset in [0, 4] {
        let after = before.memory().clone().store(
            field.offset_by_bytes(offset),
            ProgramValue::UInt32(MachineTerm::constant(7)),
        );
        assert!(
            prove_program_condition_fact_transport(&source, &after, &context).is_none(),
            "a partial overwrite at {offset} must not preserve the full pointer"
        );
    }
}

#[test]
fn direct_transport_rewrites_loads_inside_signed_add_overflow_guard() {
    let before = Memory::new();
    let field = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let loaded = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before.clone()),
        Box::new(field.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let fact = Proposition::ConditionIs(
        ConditionTerm::signed_add_overflows(loaded, MachineTerm::constant(1)),
        false,
    );
    let after = before.clone().with_block("local:result", 4);

    let theorem =
        prove_program_condition_fact_direct_transport(&fact, &after, &PureFactContext::new())
            .expect(
                "an unrelated local allocation should transport an arithmetic definedness guard",
            );
    let Proposition::Implies(source, target) = theorem.proposition() else {
        panic!("transport theorem must be an implication");
    };
    assert_eq!(source.as_ref(), &fact);
    assert_eq!(program_condition_fact_memories(target), vec![after]);
}

#[test]
fn simple_pointer_equality_composes_interleaved_aliases_in_the_graph() {
    let final_pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(120)),
    };
    let state_pointer = Pointer {
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
                state_pointer.offset.clone(),
            ),
            true,
        )
        .assume_condition(
            ConditionTerm::pointer_equal(state_pointer, local_pointer.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::pointer_equal(local_pointer, Pointer::null()),
            true,
        );

    // Exact offset and block premises must compose in the shared graph,
    // without a consumer walking the exact-alias adjacency index.
    assert!(assumptions.pointers_known_equal(&final_pointer, &Pointer::null()));
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
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(98)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(99)), 4),
    };
    let length = MachineTerm::Variable(Variable(100));
    let owner_range = MemoryRange::new(owner, MachineTerm::constant(0), MachineTerm::constant(6));
    let data_range = MemoryRange::new(data, MachineTerm::constant(0), length.clone());
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_than(MachineTerm::constant(0), length),
            true,
        )
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(owner_range.clone())),
            right: Box::new(Resource::Memory(data_range.clone())),
        });

    assert!(
        assumptions.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &MemoryRange::new(
                data_range.base().clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            ),
            &MemoryRange::new(
                owner_range.base().clone(),
                MachineTerm::constant(1),
                MachineTerm::constant(2),
            ),
        )
    );
}

#[test]
fn direct_separation_contains_zero_under_a_constant_lower_bound() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(104)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(105)), 4),
    };
    let length = MachineTerm::Variable(Variable(106));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(2), length.clone()),
            true,
        )
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                owner.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(4),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                data.clone(),
                MachineTerm::constant(0),
                length,
            ))),
        });

    assert!(assumptions.ranges_directly_disjoint_from_pointer(
        &[MemoryRange::new(
            owner,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )],
        &data,
    ));
}

/// The two polarities of the element length an access occupies in a range's
/// own coordinates.
///
/// A range counts logical elements; an access is measured in bytes. Deciding
/// exclusion from the access's *first* element alone called an eight-byte read
/// at the element below a four-byte range separate from it, while its upper
/// half sits on the range's first element — and every framing route that asks
/// this question then carried the read across a write there.
fn access_outside_range_probe(index: u32, byte_width: u32) -> bool {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = MemoryRange::new(
        base.clone(),
        MachineTerm::constant(4),
        MachineTerm::constant(8),
    );
    let pointer = base.offset_by_int32_elements(MachineTerm::constant(index));
    PureFactContext::new().ranges_directly_disjoint_from_access(&[range], &pointer, byte_width)
}

#[test]
fn a_wide_access_reaching_into_a_range_is_not_separate_from_it() {
    // Elements 3 and 4 of a four-byte range: element 4 is the range's first.
    assert!(
        !access_outside_range_probe(3, 8),
        "an eight-byte read at element 3 covers element 4, which the range holds"
    );
    // The same address read four bytes wide stops before the range.
    assert!(
        access_outside_range_probe(3, 4),
        "a four-byte read at element 3 ends where the range begins"
    );
}

#[test]
fn a_wide_access_that_clears_the_range_stays_separate_from_it() {
    // Elements 2 and 3, one element of gap below the range's first.
    assert!(access_outside_range_probe(2, 8));
    // Above the range, where the access extends away from it.
    assert!(access_outside_range_probe(8, 8));
    // And the last element the range holds is inside it at every width.
    assert!(!access_outside_range_probe(7, 4));
    assert!(!access_outside_range_probe(7, 8));
}

#[test]
fn constant_field_offset_is_disjoint_from_earlier_constant_range() {
    let base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(101)), 4),
    };
    let first_field = MemoryRange::new(
        base.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    );
    let third_field = base.offset_by_int32_elements(MachineTerm::constant(2));

    assert!(
        PureFactContext::new().ranges_proven_disjoint_from_pointer(&[first_field], &third_field)
    );
}

#[test]
fn bounded_separation_uses_order_fact_across_equivalent_states() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(102)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(103)), 4),
    };
    let len_cell = owner.clone();
    let cap_cell = owner.offset_by_int32_elements(MachineTerm::constant(1));
    let plain = Memory::new();
    let cached = Memory::new().store(
        Pointer {
            block: "local:cache".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
        int32(0),
    );
    let query_len = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(plain.clone()),
        Box::new(len_cell.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let query_cap = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(plain),
        Box::new(cap_cell.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let fact_len = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(cached.clone()),
        Box::new(len_cell),
        crate::kernel::LoadKind::Int32,
    );
    let fact_cap = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(cached),
        Box::new(cap_cell),
        crate::kernel::LoadKind::Int32,
    );
    let owner_range = MemoryRange::new(
        owner.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(4),
    );
    let owned_data_range = MemoryRange::new(data.clone(), MachineTerm::constant(0), query_cap);
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_equal(fact_len, fact_cap), true)
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(owner_range)),
            right: Box::new(Resource::Memory(owned_data_range)),
        });

    assert!(assumptions.ranges_proven_disjoint_from_pointer(
        &[MemoryRange::new(data, MachineTerm::constant(0), query_len,)],
        &owner.offset_by_int32_elements(MachineTerm::constant(1)),
    ));
}

#[test]
fn covering_disjoint_fact_handles_shifted_mutable_range() {
    let n = Variable(83);
    let k = Variable(84);
    let n_bits = MachineTerm::Variable(n);
    let k_bits = MachineTerm::Variable(k);
    let before_memory = Memory::new();
    let after_memory = Memory::new();
    let dst_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(85)), 4),
    };
    let src_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(86)), 4),
    };
    let src_cell = src_base.offset_by_int32_elements(k_bits.clone());
    let shifted_dst = dst_base.offset_by_int32_elements(MachineTerm::constant(1));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_greater_equal(k_bits.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(k_bits, n_bits.clone()),
            true,
        )
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                dst_base,
                MachineTerm::constant(0),
                n_bits.clone(),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                src_base,
                MachineTerm::constant(0),
                n_bits.clone(),
            ))),
        })
        .assume_proposition(Proposition::MemoryEffectSummary {
            before: before_memory.clone(),
            after: after_memory.clone(),
            mutable_ranges: vec![MemoryRange::new(
                shifted_dst,
                MachineTerm::constant(0),
                MachineTerm::subtract(n_bits, MachineTerm::constant(1)),
            )],
        });

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(after_memory),
                    Box::new(src_cell.clone()),
                    crate::kernel::LoadKind::Int32
                ),
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(before_memory),
                    Box::new(src_cell),
                    crate::kernel::LoadKind::Int32
                ),
            ),
            true,
        )
    ));
}

#[test]
fn atomic_condition_fact_transport_does_not_plan_from_an_effect_summary() {
    let before = Memory::new()
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
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(before.clone()),
                Box::new(stable.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            MachineTerm::constant(7),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryEffectSummary {
        before: before.clone(),
        after: after.clone(),
        mutable_ranges: vec![MemoryRange::new(
            mutated,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )],
    });

    assert!(
        prove_program_condition_fact_transport(&fact, &after, &assumptions).is_none(),
        "ordinary fact transport must not plan load equality from ambient effect summaries",
    );
}

#[test]
fn memory_load_equality_does_not_ignore_loop_havoc_identity() {
    let before = Memory::new();
    let after = before.clone().with_block("havoc:0", 0);
    let pointer = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let equality = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(after),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(before),
                Box::new(pointer),
                crate::kernel::LoadKind::Int32,
            ),
        ),
        true,
    );

    assert!(
        !crate::kernel::search::ProofSearch::proves(&(PureFactContext::new()), &equality),
        "a havoced state requires explicit frame evidence"
    );
}

#[test]
fn atomic_condition_fact_transport_ignores_distinct_materialized_cell() {
    let before = Memory::new()
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
    // The framed load is the `int32` at offset zero. Say so: a width-less
    // load stands in eight bytes, which the store at offset four overlaps.
    crate::kernel::eval::declare_load_access_width(&preserved, 4);
    let after = before
        .clone()
        .store(materialized, ProgramValue::Int32(MachineTerm::constant(9)));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(before.clone()),
                Box::new(preserved.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            MachineTerm::constant(7),
        ),
        true,
    );

    let theorem = prove_program_condition_fact_transport(&fact, &after, &PureFactContext::new())
        .expect("a distinct materialized cell must not change the framed load");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    MachineTerm::MemoryLoad(
                        crate::kernel::intern_memory(after),
                        Box::new(preserved),
                        crate::kernel::LoadKind::Int32
                    ),
                    MachineTerm::constant(7),
                ),
                true,
            )),
        )
    );
}

#[test]
fn pointer_offset_fact_transport_does_not_plan_from_an_effect_summary() {
    let before = Memory::new()
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
    let expected = PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(345)), 4);
    let fact = Proposition::ConditionIs(
        ConditionTerm::pointer_offset_equal(
            PointerOffsetTerm::scale_int32(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(before.clone()),
                    Box::new(stable.clone()),
                    crate::kernel::LoadKind::Int32,
                ),
                4,
            ),
            expected.clone(),
        ),
        true,
    );
    let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryEffectSummary {
        before,
        after: after.clone(),
        mutable_ranges: vec![MemoryRange::new(
            mutated,
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )],
    });

    assert!(
        prove_program_condition_fact_transport(&fact, &after, &assumptions).is_none(),
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
    let before = Memory::new()
        .with_block("arg-memory", 8)
        .with_block("local:value", 4);
    let after = before
        .clone()
        .store(local, ProgramValue::Int32(MachineTerm::constant(7)));
    let load_offset = |memory: &Memory, pointer: &Pointer| {
        PointerOffsetTerm::scale_int32(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory.clone()),
                Box::new(pointer.clone()),
                crate::kernel::LoadKind::Int32,
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

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &target
    ));
}

#[test]
fn memory_load_equality_combines_equal_pointer_base_and_zero_index() {
    let memory = Memory::new().with_block("arg-memory", 64);
    let owner = MachineTerm::Variable(Variable(90));
    let data = MachineTerm::Variable(Variable(91));
    let owner_offset = PointerOffsetTerm::scale_int32(owner, 4);
    let data_field = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::add(owner_offset.clone(), PointerOffsetTerm::Constant(8)),
    };
    let pos_field = Pointer {
        block: "arg-memory".into(),
        offset: owner_offset,
    };
    let data_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory.clone()),
        Box::new(data_field),
        crate::kernel::LoadKind::Int32,
    );
    let pos_load = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(memory.clone()),
        Box::new(pos_field),
        crate::kernel::LoadKind::Int32,
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
            ConditionTerm::equal(pos_load, MachineTerm::constant(0)),
            true,
        ));
    let target = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory.clone()),
                Box::new(indexed),
                crate::kernel::LoadKind::Int32,
            ),
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(memory),
                Box::new(direct),
                crate::kernel::LoadKind::Int32,
            ),
        ),
        true,
    );

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &target
    ));
}

#[test]
fn pointer_offset_equality_combines_equal_base_and_zero_index() {
    let base = MachineTerm::Variable(Variable(90));
    let target = MachineTerm::Variable(Variable(91));
    let index = MachineTerm::Variable(Variable(92));
    let base_offset = PointerOffsetTerm::scale_int32(base, 4);
    let target_offset = PointerOffsetTerm::scale_int32(target, 4);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::pointer_offset_equal(base_offset.clone(), target_offset.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(index.clone(), MachineTerm::constant(0)),
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
fn a_struct_field_offset_is_distinct_from_offsets_off_its_stride_residue() {
    let index = MachineTerm::Variable(Variable(93));
    // `items[x].y` in an array of 8-byte structs is at `x * 8 + 4`.
    let field = PointerOffsetTerm::add(
        PointerOffsetTerm::scale_int32(index.clone(), 8),
        PointerOffsetTerm::Constant(4),
    );
    for other in [0, 8, -8, 13] {
        assert_eq!(
            ConditionTerm::pointer_offset_equal(field.clone(), PointerOffsetTerm::Constant(other)),
            ConditionTerm::Constant(false),
            "offset {other}",
        );
    }
    // A symbolic offset on the other side shares the residue only when its
    // strides allow it: `y * 4` can be `x * 8 + 4`, `y * 8` cannot.
    let other_index = MachineTerm::Variable(Variable(94));
    assert_eq!(
        ConditionTerm::pointer_offset_equal(
            field.clone(),
            PointerOffsetTerm::scale_int32(other_index.clone(), 8),
        ),
        ConditionTerm::Constant(false),
    );
    assert!(matches!(
        ConditionTerm::pointer_offset_equal(
            field.clone(),
            PointerOffsetTerm::scale_int32(other_index, 4),
        ),
        ConditionTerm::PointerOffsetEqual(_, _),
    ));
    assert!(matches!(
        ConditionTerm::pointer_offset_equal(field, PointerOffsetTerm::Constant(12)),
        ConditionTerm::PointerOffsetEqual(_, _),
    ));
}

#[test]
fn a_struct_field_offset_at_a_constant_is_decided_by_its_index() {
    let index = MachineTerm::Variable(Variable(95));
    let field = PointerOffsetTerm::add(
        PointerOffsetTerm::scale_int32(index.clone(), 8),
        PointerOffsetTerm::Constant(4),
    );
    let at_twelve = ConditionTerm::pointer_offset_equal(field, PointerOffsetTerm::Constant(12));
    for (value, decided) in [(true, true), (false, false)] {
        let assumptions = PureFactContext::new().assume_condition(
            ConditionTerm::equal(index.clone(), MachineTerm::constant(1)),
            value,
        );
        assert_eq!(assumptions.decide(&at_twelve), Some(decided));
    }
}

#[test]
fn memory_resolution_equates_offsets_that_regroup_their_constants() {
    // A byte field's element `s + 5` and its one-slot run's base
    // `(s + 4) + 1` are one address; `(s + 4) + 2` is the next byte.
    let scaled = PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(96)), 4);
    let grouped = |last: i64| {
        PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Add(
                Box::new(scaled.clone()),
                Box::new(PointerOffsetTerm::Constant(4)),
            )),
            Box::new(PointerOffsetTerm::Constant(last)),
        )
    };
    let flat = PointerOffsetTerm::Add(
        Box::new(scaled.clone()),
        Box::new(PointerOffsetTerm::Constant(5)),
    );
    let assumptions = PureFactContext::new();
    for (last, equal) in [(1, true), (2, false)] {
        assert_eq!(
            crate::kernel::reasoning::memory_resolution::pointer_offsets_equal_for_memory_resolution(
                &flat,
                &grouped(last),
                &assumptions,
            ),
            Some(equal),
        );
    }
}

#[test]
fn atomic_condition_fact_transport_does_not_plan_from_a_separate_range() {
    let before = Memory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let left = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(90)), 4),
    };
    let right = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(91)), 4),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(before.clone()),
                Box::new(left.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            MachineTerm::constant(0),
        ),
        true,
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                left.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(4),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                right.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(4),
            ))),
        })
        .assume_proposition(Proposition::MemoryEffectSummary {
            before,
            after: after.clone(),
            mutable_ranges: vec![MemoryRange::new(
                right,
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            )],
        });

    assert!(
        prove_program_condition_fact_transport(&fact, &after, &assumptions).is_none(),
        "ordinary fact transport must not synthesize a frame from ambient separation",
    );
}

/// A range restated in another base's coordinates as `data - owner` names the
/// real delta between the two bases only while that subtraction stays inside
/// `int32`: at `owner == -1` and `data == i32::MAX` the difference is `2^31`,
/// the restated start is `i32::MIN`, and the two sit `2^32` elements apart. The
/// restatement is still how a relative separation fact is read; both indices
/// being nonnegative is the premise that makes it the delta rather than the
/// delta modulo `2^32`.
fn with_nonnegative_owner_and_data_indices(assumptions: PureFactContext) -> PureFactContext {
    [92, 93]
        .into_iter()
        .fold(assumptions, |assumptions, index| {
            assumptions.assume_condition(
                ConditionTerm::signed_less_equal(
                    MachineTerm::constant(0),
                    MachineTerm::Variable(Variable(index)),
                ),
                true,
            )
        })
}

#[test]
fn direct_condition_transport_uses_relative_separate_range() {
    let before = Memory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(93)), 4),
    };
    let data_index_from_owner = MachineTerm::subtract(
        MachineTerm::Variable(Variable(93)),
        MachineTerm::Variable(Variable(92)),
    );
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(before.clone()),
                Box::new(data.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            MachineTerm::Variable(Variable(94)),
        ),
        true,
    );
    let effect = Proposition::MemoryEffectSummary {
        before,
        after: after.clone(),
        mutable_ranges: vec![MemoryRange::new(
            owner.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )],
    };
    let assumptions = with_nonnegative_owner_and_data_indices(PureFactContext::new())
        .assume_condition(
            ConditionTerm::signed_less_than(
                data_index_from_owner.clone(),
                MachineTerm::add(data_index_from_owner.clone(), MachineTerm::constant(2)),
            ),
            true,
        )
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                owner.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(4),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                owner.clone(),
                data_index_from_owner.clone(),
                MachineTerm::add(data_index_from_owner, MachineTerm::constant(2)),
            ))),
        })
        .assume_proposition(effect.clone());

    let theorem = prove_program_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("relative exact separation should directly frame the data load");
    let (premises, target) = program_condition_fact_transport_parts(&theorem, &fact)
        .expect("transport theorem must retain its explicit source");
    // Two more premises than the separation and the effect: the nonnegativity
    // of each index, which is what makes the restated start the real delta.
    assert_eq!(premises.len(), 4);
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
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(after),
                    Box::new(data),
                    crate::kernel::LoadKind::Int32
                ),
                MachineTerm::Variable(Variable(94)),
            ),
            true,
        )
    );
}

#[test]
fn direct_condition_transport_uses_indexed_relative_separate_range() {
    let before = Memory::new();
    let after = before.clone().with_block("call-havoc:0", 0);
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(93)), 4),
    };
    let data_one = data.offset_by_int32_elements(MachineTerm::constant(1));
    let data_index_from_owner = MachineTerm::subtract(
        MachineTerm::Variable(Variable(93)),
        MachineTerm::Variable(Variable(92)),
    );
    let length = MachineTerm::Variable(Variable(95));
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(before.clone()),
                Box::new(data_one.clone()),
                crate::kernel::LoadKind::Int32,
            ),
            MachineTerm::Variable(Variable(94)),
        ),
        true,
    );
    let effect = Proposition::MemoryEffectSummary {
        before,
        after: after.clone(),
        mutable_ranges: vec![MemoryRange::new(
            owner.clone(),
            MachineTerm::constant(0),
            MachineTerm::constant(1),
        )],
    };
    let assumptions = with_nonnegative_owner_and_data_indices(PureFactContext::new())
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(2), length.clone()),
            true,
        )
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                owner.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(4),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                owner.clone(),
                data_index_from_owner.clone(),
                MachineTerm::add(data_index_from_owner, length),
            ))),
        })
        .assume_proposition(effect.clone());

    let theorem = prove_program_condition_fact_direct_transport(&fact, &after, &assumptions)
        .expect("an indexed pointer in a relative separate range should be directly framed");
    let (premises, target) = program_condition_fact_transport_parts(&theorem, &fact)
        .expect("transport theorem must retain its explicit source");
    // Two more premises than the separation and the effect: the nonnegativity
    // of each index, which is what makes the restated start the real delta.
    assert_eq!(premises.len(), 5);
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
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(after),
                    Box::new(data_one),
                    crate::kernel::LoadKind::Int32
                ),
                MachineTerm::Variable(Variable(94)),
            ),
            true,
        )
    );
}

#[test]
fn condition_fact_transport_preserves_arithmetic_structure() {
    let before = Memory::new().with_block("stable", 4);
    let after = before.clone().with_block("local:value", 4);
    let stable = Pointer {
        block: "stable".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let fact = Proposition::ConditionIs(
        ConditionTerm::equal(
            MachineTerm::add(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(before),
                    Box::new(stable.clone()),
                    crate::kernel::LoadKind::Int32,
                ),
                MachineTerm::constant(1),
            ),
            MachineTerm::constant(8),
        ),
        true,
    );

    let theorem = prove_program_condition_fact_transport(&fact, &after, &PureFactContext::new())
        .expect("arithmetic around a framed load should transport structurally");
    assert_eq!(
        theorem.proposition(),
        &Proposition::Implies(
            Box::new(fact),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    MachineTerm::add(
                        MachineTerm::MemoryLoad(
                            crate::kernel::intern_memory(after),
                            Box::new(stable),
                            crate::kernel::LoadKind::Int32
                        ),
                        MachineTerm::constant(1),
                    ),
                    MachineTerm::constant(8),
                ),
                true,
            )),
        )
    );
}

#[test]
fn adjacent_disjoint_fact_ranges_cover_larger_disjoint_goal() {
    let n_bits = MachineTerm::Variable(Variable(87));
    let p_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let p_plus_one = p_base.offset_by_int32_elements(MachineTerm::constant(1));
    let q_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(88)), 4),
    };
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                p_base.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(1),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                q_base.clone(),
                MachineTerm::constant(0),
                n_bits.clone(),
            ))),
        })
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                p_plus_one,
                MachineTerm::constant(0),
                MachineTerm::constant(2),
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                q_base.clone(),
                MachineTerm::constant(0),
                n_bits.clone(),
            ))),
        });

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(MemoryRange::new(
                p_base,
                MachineTerm::constant(0),
                MachineTerm::constant(2)
            ))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                q_base,
                MachineTerm::constant(0),
                n_bits
            )))
        }
    ));
}

#[test]
fn constant_non_overlapping_ranges_on_one_base_are_separate() {
    let base = Pointer {
        block: "object".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let left = Resource::Memory(MemoryRange::new(
        base.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
    ));
    let right = Resource::Memory(MemoryRange::new(
        base,
        MachineTerm::constant(2),
        MachineTerm::constant(4),
    ));

    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &Proposition::ResourceSeparate {
            left: Box::new(left.clone()),
            right: Box::new(right.clone()),
        }
    ));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &Proposition::ResourceSeparate {
            left: Box::new(right),
            right: Box::new(left),
        }
    ));
}

#[test]
fn symbolic_disjoint_fact_proves_itself() {
    let n_bits = MachineTerm::Variable(Variable(89));
    let p_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let q_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(90)), 4),
    };
    let fact = Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(MemoryRange::new(
            p_base,
            MachineTerm::constant(0),
            n_bits.clone(),
        ))),
        right: Box::new(Resource::Memory(MemoryRange::new(
            q_base,
            MachineTerm::constant(0),
            n_bits,
        ))),
    };
    let assumptions = PureFactContext::new().assume_proposition(fact.clone());

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &fact
    ));
}

#[test]
fn additive_equality_cancellation_feeds_range_contradictions() {
    let base = MachineTerm::Variable(Variable(91));
    let index = MachineTerm::Variable(Variable(92));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(MachineTerm::add(base.clone(), index.clone()), base),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(index, MachineTerm::constant(1)),
            true,
        );

    assert!(assumptions.is_inconsistent());
}

#[test]
fn equality_facts_close_signed_order_contradiction_cycles() {
    let left = MachineTerm::Variable(Variable(193));
    let right = MachineTerm::Variable(Variable(194));
    let assumptions = PureFactContext::new()
        .assume_condition(ConditionTerm::equal(left.clone(), right.clone()), true)
        .assume_condition(
            ConditionTerm::signed_less_than(left, MachineTerm::constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_greater_equal(right, MachineTerm::constant(1)),
            true,
        );

    assert!(assumptions.is_inconsistent());
}

/// Upper-bound case selection belongs to the Surface planner. The kernel's
/// proposition search must not silently create that control flow.
#[test]
fn an_assumed_upper_bound_does_not_split_inside_kernel_search() {
    let bound = MachineTerm::Variable(Variable(811));
    let index = MachineTerm::Variable(Variable(812));
    // Holds strictly below the bound (by the quantified fact) and at it (by
    // reflexivity); neither half's justification covers the other.
    let goal = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(index.clone(), bound.clone()),
        true,
    );
    let context = PureFactContext::new().assume_condition(
        ConditionTerm::signed_less_than(
            index.clone(),
            MachineTerm::add(bound.clone(), MachineTerm::constant(1)),
        ),
        true,
    );

    assert!(crate::kernel::search::ProofSearch::derive_proposition(&(context), &goal).is_none());
}

#[test]
fn equality_to_constant_feeds_signed_order_decisions() {
    let value = MachineTerm::Variable(Variable(93));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(value.clone(), MachineTerm::constant(1)),
        true,
    );

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            MachineTerm::constant(0),
            value.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_greater_equal(
            value,
            MachineTerm::constant(1),
        )),
        Some(true)
    );
}

#[test]
fn range_fold_simplifies_empty_and_one_step_ranges() {
    let accumulator = Variable(93);
    let item = Variable(94);
    let x = MachineTerm::Variable(Variable(95));
    let body = MachineTerm::add(MachineTerm::Variable(accumulator), x.clone());

    assert_eq!(
        MachineTerm::range_fold(
            MachineTerm::constant(4),
            MachineTerm::constant(4),
            MachineTerm::constant(7),
            accumulator,
            item,
            body.clone(),
        ),
        MachineTerm::constant(7)
    );

    // A concrete one-element range still unrolls once, by length.
    assert_eq!(
        MachineTerm::range_fold(
            MachineTerm::constant(4),
            MachineTerm::constant(5),
            MachineTerm::constant(7),
            accumulator,
            item,
            body.clone(),
        ),
        MachineTerm::add(MachineTerm::constant(7), x.clone())
    );

    // A symbolic pair one element apart under one value of the start is
    // opaque, because a start of `i32::MAX` makes the signed range empty.
    assert!(matches!(
        MachineTerm::range_fold(
            MachineTerm::Variable(Variable(96)),
            MachineTerm::add(
                MachineTerm::Variable(Variable(96)),
                MachineTerm::constant(1)
            ),
            MachineTerm::constant(7),
            accumulator,
            item,
            body.clone(),
        ),
        MachineTerm::RangeFold { .. }
    ));

    // The wrap bound: the signed range `i32::MAX .. i32::MIN` is empty, and
    // the certified empty law (`prove_integer_range_fold_empty`) returns
    // `initial` there, so the constructor must too rather than unroll once
    // with `end == start + 1` modulo `2^32`.
    assert_eq!(
        MachineTerm::range_fold(
            MachineTerm::constant(i32::MAX as u32),
            MachineTerm::constant(i32::MIN as u32),
            MachineTerm::constant(7),
            accumulator,
            item,
            body,
        ),
        MachineTerm::constant(7)
    );
}

#[test]
fn count_shaped_range_fold_split_is_proven_equal() {
    let lo = MachineTerm::Variable(Variable(97));
    let mid = MachineTerm::Variable(Variable(98));
    let hi = MachineTerm::Variable(Variable(99));
    let x = MachineTerm::Variable(Variable(100));
    let accumulator = Variable(101);
    let item = Variable(102);
    let contribution = MachineTerm::if_then_else(
        ConditionTerm::equal(MachineTerm::Variable(item), x),
        MachineTerm::constant(1),
        MachineTerm::constant(0),
    );
    let body = MachineTerm::add(MachineTerm::Variable(accumulator), contribution);
    let count = |start: MachineTerm, end: MachineTerm| {
        MachineTerm::range_fold(
            start,
            end,
            MachineTerm::constant(0),
            accumulator,
            item,
            body.clone(),
        )
    };
    let whole = count(lo.clone(), hi.clone());
    let split = MachineTerm::add(
        count(lo.clone(), mid.clone()),
        count(mid.clone(), hi.clone()),
    );

    // The split identity fold(lo,hi) = fold(lo,mid) + fold(mid,hi) only
    // holds for lo <= mid <= hi. Without that ordering it is unsound
    // (half-open ranges make an out-of-order mid over- or under-count),
    // so the rule must not fire on unconstrained bounds.
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &Proposition::ConditionIs(ConditionTerm::equal(whole.clone(), split.clone()), true,)
    ));

    let ordered = PureFactContext::new()
        .assume_condition(ConditionTerm::signed_less_equal(lo, mid.clone()), true)
        .assume_condition(ConditionTerm::signed_less_equal(mid, hi), true);
    assert!(crate::kernel::search::ProofSearch::proves(
        &(ordered),
        &Proposition::ConditionIs(ConditionTerm::equal(whole, split), true,)
    ));
}

/// An `Integer`-carrier fold over an array cell, with the memory state the
/// body reads left open.
fn integer_array_fold(
    memory: &Memory,
    start: MachineTerm,
    end: MachineTerm,
    accumulator: Variable,
    item: Variable,
) -> IntegerTerm {
    let load = MachineTerm::MemoryLoad(
        intern_memory_ref(memory),
        Box::new(Pointer {
            block: "array".into(),
            offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(item), 4),
        }),
        crate::kernel::LoadKind::Int32,
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
    let memory = Memory::new().with_block("array", 12);
    let lo = MachineTerm::Variable(Variable(110));
    let a = MachineTerm::Variable(Variable(111));
    let b = MachineTerm::Variable(Variable(112));
    let left = integer_array_fold(&memory, lo.clone(), a.clone(), Variable(113), Variable(114));
    let right = integer_array_fold(&memory, lo, b.clone(), Variable(115), Variable(116));
    let goal = Proposition::ConditionIs(
        ConditionTerm::integer_equal(left.clone(), right.clone()),
        true,
    );

    // The two end endpoints are unrelated terms, so nothing equates the folds
    // until the equality is an available fact.
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &goal
    ));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new().assume_condition(ConditionTerm::equal(a, b), true)),
        &goal
    ));
}

#[test]
fn integer_range_fold_endpoint_congruence_normalizes_an_affine_endpoint() {
    let memory = Memory::new().with_block("array", 12);
    let lo = MachineTerm::Variable(Variable(120));
    let hi = MachineTerm::Variable(Variable(121));
    // `(hi - 1) + 1` is the endpoint every induction step carries back to
    // `hi`. It needs no ordering or definedness fact: 32-bit `Add` and
    // `Subtract` wrap, so the two affine normal forms are equal outright.
    let successor_of_predecessor = binary_node!(
        Int32,
        Add,
        Box::new(binary_node!(
            Int32,
            Subtract,
            Box::new(hi.clone()),
            Box::new(MachineTerm::constant(1)),
        )),
        Box::new(MachineTerm::constant(1)),
    );
    let left = integer_array_fold(
        &memory,
        lo.clone(),
        successor_of_predecessor,
        Variable(122),
        Variable(123),
    );
    let right = integer_array_fold(&memory, lo, hi, Variable(124), Variable(125));

    assert!(crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &Proposition::ConditionIs(ConditionTerm::integer_equal(left, right), true,)
    ));
}

#[test]
fn integer_range_fold_endpoint_congruence_rejects_a_free_binder_occurrence() {
    let lo = SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(140)));
    let a = SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(141)));
    let b = SharedIntegerRangeEndpoint::intern(MachineTerm::Variable(Variable(142)));
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
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(ConditionTerm::integer_equal(bound.clone(), free), true,)
    ));

    // The same pair with the accumulator bound on both sides is equated, so
    // the refusal above is the free occurrence and not the shape.
    let also_bound = fold(&b, bound_accumulator);
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(ConditionTerm::integer_equal(bound, also_bound), true,)
    ));
}

#[test]
fn integer_range_fold_endpoint_congruence_requires_one_memory_state() {
    let cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = Memory::new().with_block("array", 12);
    let after = before.clone().store(cell, int32(7));
    let lo = MachineTerm::Variable(Variable(130));
    let a = MachineTerm::Variable(Variable(131));
    let b = MachineTerm::Variable(Variable(132));
    let assumptions =
        PureFactContext::new().assume_condition(ConditionTerm::equal(a.clone(), b.clone()), true);

    // Equal endpoints and the same body shape, but the two bodies read
    // different states of the same array. The fold values may genuinely
    // differ, so the congruence must not fire.
    let left = integer_array_fold(&before, lo.clone(), a.clone(), Variable(133), Variable(134));
    let across_a_write =
        integer_array_fold(&after, lo.clone(), b.clone(), Variable(135), Variable(136));
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::integer_equal(left.clone(), across_a_write),
            true,
        )
    ));

    // The same pair at one state is equated, so the refusal above is the
    // state check and not some other mismatch.
    let same_state = integer_array_fold(&before, lo, b, Variable(135), Variable(136));
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(ConditionTerm::integer_equal(left, same_state), true,)
    ));
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
    let base = Memory::new().with_block("array", 8);

    let overlay_over_store = base.clone().store(cell.clone(), int32(42)).store_union(
        cell.clone(),
        ProgramType::UInt8,
        crate::kernel::uint8(7),
    );
    assert_eq!(overlay_over_store.known_value(&cell), None);
    assert!(overlay_over_store.has_union_overlay_at(&cell));
    let replacement =
        overlay_over_store.store_union(cell.clone(), ProgramType::Int16, crate::kernel::int16(9));
    assert_eq!(
        replacement.known_union_value(&cell, ProgramType::UInt8),
        None
    );
    assert_eq!(
        replacement.known_union_value(&cell, ProgramType::Int16),
        Some(crate::kernel::int16(9)),
    );

    let same_image_views = base.clone().store_union_views(
        cell.clone(),
        4,
        vec![
            (cell.clone(), ProgramType::UInt8, crate::kernel::uint8(7)),
            (cell.clone(), ProgramType::Int16, crate::kernel::int16(7)),
        ],
    );
    assert_eq!(
        same_image_views.known_union_value(&cell, ProgramType::UInt8),
        Some(crate::kernel::uint8(7)),
    );
    assert_eq!(
        same_image_views.known_union_value(&cell, ProgramType::Int16),
        Some(crate::kernel::int16(7)),
    );

    let store_over_overlay = base
        .store_union(cell.clone(), ProgramType::UInt8, crate::kernel::uint8(7))
        .store(cell.clone(), int32(42));
    assert_eq!(store_over_overlay.known_value(&cell), Some(int32(42)));
    assert!(!store_over_overlay.has_union_overlay_at(&cell));
}

#[test]
fn symbolic_store_invalidates_only_possible_aliasing_cells() {
    let i = Variable(81);
    let i_bits = MachineTerm::Variable(i);
    let concrete_cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Constant(4),
    };
    let symbolic_cell = Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::scaled_int32_node(i_bits.clone(), 4),
    };
    let memory = Memory::new()
        .with_block("array", 12)
        .store(concrete_cell.clone(), int32(42));

    let aliased = memory
        .without_possible_aliasing_cells(&symbolic_cell, 4, &PureFactContext::new())
        .store(symbolic_cell.clone(), int32(7));
    assert_eq!(aliased.known_value(&concrete_cell), None);

    let distinct_assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::equal(i_bits, MachineTerm::constant(1)),
        false,
    );
    let distinct = memory
        .without_possible_aliasing_cells(&symbolic_cell, 4, &distinct_assumptions)
        .store(symbolic_cell, int32(7));
    assert_eq!(distinct.known_value(&concrete_cell), Some(int32(42)));
}

/// A store keeps the cells whose *bytes* it provably misses, and an address
/// ladder does not answer that. `i != j` separates `a[i]` from `a[j]` and
/// says nothing about an eight-byte store at `a[j]`, which covers `a[j]` and
/// `a[j + 1]` both — so the ladder may only stand in for the bytes where the
/// gap it establishes clears the wider access.
///
/// `overwrites` is not what was deciding these: it compares a constant byte
/// interval and declines two offsets carrying different symbolic atoms,
/// which is exactly this pair.
#[test]
fn a_wide_store_does_not_spare_a_narrow_cell_a_ladder_separates() {
    let i = MachineTerm::Variable(Variable(93_640));
    let j = MachineTerm::Variable(Variable(93_641));
    let element = |index: &MachineTerm| Pointer {
        block: "array".into(),
        offset: PointerOffsetTerm::Add(
            Box::new(PointerOffsetTerm::Variable(Variable(93_642))),
            Box::new(PointerOffsetTerm::scaled_int32_node(index.clone(), 4)),
        ),
    };
    let cell = element(&i);
    let write = element(&j);
    let memory = Memory::new()
        .with_block("array", 16)
        .store(cell.clone(), int32(5));
    // The ladder's premise, and the only one: the two element indices differ.
    let indices_differ =
        PureFactContext::new().assume_condition(ConditionTerm::equal(i.clone(), j.clone()), false);

    // A four-byte store at a different element misses a four-byte cell: one
    // element of gap clears both accesses whichever way the ladder runs.
    let narrow = memory
        .clone()
        .without_possible_aliasing_cells(&write, 4, &indices_differ);
    assert_eq!(narrow.known_value(&cell), Some(int32(5)));

    // An eight-byte store at that same element reaches the one above it, and
    // `i != j` does not rule out `i == j + 1`.
    let wide = memory
        .clone()
        .without_possible_aliasing_cells(&write, 8, &indices_differ);
    assert_eq!(wide.known_value(&cell), None);

    // With the direction fixed the gap is decided: the store is the *lower*
    // access, so its eight bytes have to fit, and they do not.
    let store_below = indices_differ
        .clone()
        .assume_condition(ConditionTerm::signed_less_than(j.clone(), i.clone()), true);
    assert_eq!(
        memory
            .clone()
            .without_possible_aliasing_cells(&write, 8, &store_below)
            .known_value(&cell),
        None
    );
    // The other direction puts the *cell* below, and an access extending away
    // from the gap cannot close it, so the eight-byte store is separate.
    let store_above = indices_differ
        .assume_condition(ConditionTerm::signed_less_than(i.clone(), j.clone()), true);
    assert_eq!(
        memory
            .without_possible_aliasing_cells(&write, 8, &store_above)
            .known_value(&cell),
        Some(int32(5))
    );
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
/// state comparison that fact transport uses: `x = 5`, then `q = echo(&x)`
/// binding an unresolved pointer into a local, then `x = 1`.
///
/// The two states either side of `x = 1` differ in one cell, and that cell
/// is in a `local:` block. The comparison used to drop every such cell before
/// asking anything, so it called the two states agreed about a load through
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

    let entry = Memory::new()
        .with_block("local:x", 4)
        .with_block("local:q", 8)
        .with_block("global:g", 16);
    // `x = 5`, then the call's result stored into the caller's own `q`, then
    // the store this read has to be told apart from.
    let after_call = entry.store(x.clone(), crate::kernel::api::int32(5));
    let after_binding = after_call
        .without_possible_aliasing_cells(&q, crate::kernel::C_POINTER_BYTE_WIDTH, &bare)
        .store(
            q.clone(),
            ProgramValue::Pointer(PointerValue::new(
                symbolic.clone(),
                ProgramType::Int32Pointer,
            )),
        );
    let after_store = after_binding
        .clone()
        .without_possible_aliasing_cells(&x, 4, &bare)
        .store(x.clone(), crate::kernel::api::int32(1));

    assert!(
        !memory_states_proven_equal_at_pointer(&after_binding, &after_store, &symbolic, &bare),
        "a store to `x` must not be framed away for a load through a pointer \
         nothing resolves: the pointer may be `&x`"
    );

    // Nothing is lost where skipping the `local:` cell was sound: every block
    // a store can name that is not the read's own is proven distinct from a
    // local, so the per-cell check answers those on its first rung.
    assert!(
        memory_states_proven_equal_at_pointer(&after_binding, &after_store, &argument, &bare),
        "memory the caller passed in cannot be this function's own local"
    );
    assert!(
        memory_states_proven_equal_at_pointer(&after_binding, &after_store, &global, &bare),
        "two differently named declared objects are two objects"
    );

    // And the tracker's walk stops at that same store, which is the step the
    // refusal names.
    let point = crate::kernel::resource_tracker::VersionPoint::at(
        &crate::kernel::intern_memory_ref(&after_store),
    );
    let stop = crate::kernel::resource_tracker::last_same(
        crate::kernel::resource_tracker::TrackedResource::Cell {
            pointer: &symbolic,
            bytes: 4,
        },
        &point,
    )
    .expect("a cell always has a naming point");
    assert_eq!(
        stop.stopped_by.change,
        crate::kernel::resource_tracker::Change::Store { pointer: x },
        "the walk must stop at the store to `x`"
    );
}

/// What a state comparison with **no load pointer** may drop.
///
/// `memories_proven_equal_for_memory_resolution` and its certification twin
/// `memories_definitionally_equal` are whole-state equalities: neither is
/// handed a pointer, so neither can ask `observable_by_load` which cells a
/// read could see. Both used to drop every cell and block spelled `local:`,
/// which is the withdrawn `Symbolic` exception with the sides swapped — the
/// claim that no automatic object is memory a pointer reads. `q = echo(&x)`
/// refutes it.
///
/// What is left is the claim that needs no pointer: an object whose address
/// the program never forms is memory no pointer value designates at all. So
/// `local:hidden` may be dropped and `local:addressed` may not, and the two
/// comparisons must answer that identically because they are one rule.
///
/// The last pair is the order-path caller's question, which does have a
/// pointer and now asks it: two states differing in an address-taken local
/// are not one state for a load through a pointer nothing resolves, and two
/// differing only in a local no pointer can reach are.
#[test]
fn a_pointerless_state_equality_drops_only_a_local_no_pointer_can_reach() {
    use crate::kernel::api::contract_certification::memories_definitionally_equal;

    let at = |block: PointerBlock| Pointer {
        block,
        offset: PointerOffsetTerm::Constant(0),
    };
    let addressed = at("local:addressed".into());
    let hidden = at("local:hidden".into());
    let symbolic = at(PointerBlock::Symbolic(Variable(1_000_001)));
    let bare = PureFactContext::new();

    // `hidden` is the only name this session's sources never take the
    // address of; `addressed` is one a `&addressed` somewhere reaches.
    crate::kernel::primitives::set_never_address_taken_locals(
        ["hidden".to_string()].into_iter().collect(),
    );

    let entry = Memory::new()
        .with_block("local:addressed", 4)
        .with_block("local:hidden", 4);
    let before = entry
        .store(addressed.clone(), crate::kernel::api::int32(5))
        .store(hidden.clone(), crate::kernel::api::int32(5));
    let wrote_addressed = before
        .clone()
        .store(addressed.clone(), crate::kernel::api::int32(1));
    let wrote_hidden = before
        .clone()
        .store(hidden.clone(), crate::kernel::api::int32(1));

    assert!(
        !memories_proven_equal_for_memory_resolution(&before, &wrote_addressed, &bare),
        "a store to an automatic object the program can form the address of \
         changes the state a pointerless comparison is about"
    );
    assert!(
        memories_proven_equal_for_memory_resolution(&before, &wrote_hidden, &bare),
        "an object no pointer value designates cannot tell two states apart"
    );
    assert!(
        !memories_definitionally_equal(&before, &wrote_addressed, &bare),
        "the certification twin is the same rule and must answer the same"
    );
    assert!(
        memories_definitionally_equal(&before, &wrote_hidden, &bare),
        "the certification twin is the same rule and must answer the same"
    );

    // The declared-block half of both comparisons narrows the same way.
    let declared_addressed = Memory::new().with_block("local:addressed", 4);
    let declared_neither = Memory::new();
    let declared_hidden = Memory::new().with_block("local:hidden", 4);
    assert!(
        !memories_proven_equal_for_memory_resolution(&declared_addressed, &declared_neither, &bare),
        "an addressable automatic object's extent is part of the state"
    );
    assert!(
        memories_proven_equal_for_memory_resolution(&declared_hidden, &declared_neither, &bare),
        "an object no pointer can reach has no extent a load consults"
    );

    // And the caller that does have a pointer now asks about it.
    assert!(
        !memory_states_proven_equal_at_pointer(&before, &wrote_addressed, &symbolic, &bare),
        "the pointer may be `&addressed`"
    );
    assert!(
        memory_states_proven_equal_at_pointer(&before, &wrote_hidden, &symbolic, &bare),
        "no pointer value designates `hidden`"
    );

    crate::kernel::primitives::clear_never_address_taken_locals();
}

#[test]
fn memory_resolution_alias_check_uses_explicit_separation() {
    let left_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(90)), 4),
    };
    let right_base = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(91)), 4),
    };
    let assumptions = PureFactContext::new().assume_proposition(Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(memory_range(left_base.clone(), 0, 4))),
        right: Box::new(Resource::Memory(memory_range(right_base.clone(), 0, 4))),
    });

    assert!(pointers_proven_distinct_for_memory_resolution(
        &left_base.offset_by_int32_elements(MachineTerm::constant(1)),
        &right_base.offset_by_int32_elements(MachineTerm::constant(2)),
        &assumptions,
    ));
    assert!(!pointers_proven_equal_for_memory_resolution(
        &left_base.offset_by_int32_elements(MachineTerm::constant(1)),
        &right_base.offset_by_int32_elements(MachineTerm::constant(2)),
        &assumptions,
    ));

    let right_start = MachineTerm::subtract(
        MachineTerm::Variable(Variable(91)),
        MachineTerm::Variable(Variable(90)),
    );
    // The restated start `v91 - v90` is the real delta between the two bases
    // only while that subtraction stays inside `int32`, so the normalized form
    // of the fact needs what the unnormalized one did not.
    let nonnegative_indices =
        [90, 91]
            .into_iter()
            .fold(PureFactContext::new(), |assumptions, index| {
                assumptions.assume_condition(
                    ConditionTerm::signed_less_equal(
                        MachineTerm::constant(0),
                        MachineTerm::Variable(Variable(index)),
                    ),
                    true,
                )
            });
    let normalized_assumptions =
        nonnegative_indices.assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(memory_range(left_base.clone(), 0, 4))),
            right: Box::new(Resource::Memory(memory_range(
                left_base.clone(),
                right_start.clone(),
                MachineTerm::add(right_start, MachineTerm::constant(4)),
            ))),
        });
    assert!(pointers_proven_distinct_for_memory_resolution(
        &left_base.offset_by_int32_elements(MachineTerm::constant(1)),
        &right_base.offset_by_int32_elements(MachineTerm::constant(2)),
        &normalized_assumptions,
    ));
}

/// Two owned members of one composition are disjoint whatever blocks their
/// pointers are spelled in: a read loaded from memory names its own block,
/// and the composition law still separates it from an owned argument. Each
/// entry point asks each side of its own block; one member, or a view beside
/// an owner, still separates nothing.
#[test]
fn owned_members_in_different_blocks_are_separate() {
    let _session = crate::kernel::VerificationSession::enter();
    let source = crate::kernel::intern_memory(Memory::new());
    let argument = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(95_001)), 4),
    };
    let loaded = Pointer::loaded_value(&source, &argument);
    let argument_cell = memory_range(argument.clone(), 0, 2);
    let loaded_cell = memory_range(loaded.clone(), 0, 2);
    let owners = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(argument_cell.clone()))
        .unchecked_with_fact(ResourceFact::own_memory(loaded_cell.clone()));
    let facts =
        PureFactContext::new().assume_proposition(Proposition::ResourceComposition(owners.clone()));
    let inside = |pointer: &Pointer, range: &MemoryRange| {
        crate::kernel::assumptions::pointer_in_memory_range_shallow(pointer, range)
    };

    assert!(owners.proves_owned_pointers_separate_shallow(&argument, &loaded));
    assert!(owners.proves_owned_pointers_separate_by(&argument, &loaded, inside));
    assert!(owners.proves_owned_memory_ranges_separate_by(
        &argument_cell,
        &loaded_cell,
        &facts,
        crate::kernel::assumptions::memory_range_shallowly_contained,
    ));
    assert!(owners.proves_owned_range_separate_from_pointer_shallow(
        &argument_cell,
        &loaded,
        &facts,
        inside,
    ));
    assert!(
        facts
            .composition_separated_members(
                &argument,
                &loaded,
                |range| range == &argument_cell,
                |range| range == &loaded_cell,
                |_, _| true,
            )
            .is_some()
    );

    let owner_and_view = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(argument_cell.clone()))
        .unchecked_with_fact(ResourceFact::view_memory(loaded_cell.clone()));
    let view_facts = PureFactContext::new()
        .assume_proposition(Proposition::ResourceComposition(owner_and_view.clone()));
    assert!(!owner_and_view.proves_owned_pointers_separate_shallow(&argument, &loaded));
    assert!(
        !owner_and_view.proves_owned_range_separate_from_pointer_shallow(
            &argument_cell,
            &loaded,
            &view_facts,
            inside,
        )
    );
    assert!(
        view_facts
            .composition_separated_members(
                &argument,
                &loaded,
                |range| range == &argument_cell,
                |range| range == &loaded_cell,
                |_, _| true,
            )
            .is_none()
    );

    // Equal literals may share their bytes, so owning both separates nothing.
    let literal = |identity: &str| Pointer {
        block: PointerBlock::StringLiteral {
            identity: identity.to_string(),
            bytes: b"ok\0".to_vec(),
        },
        offset: PointerOffsetTerm::Constant(0),
    };
    let (first, second) = (literal("first"), literal("second"));
    let (first_cell, second_cell) = (
        memory_range(first.clone(), 0, 2),
        memory_range(second.clone(), 0, 2),
    );
    let literals = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(first_cell.clone()))
        .unchecked_with_fact(ResourceFact::own_memory(second_cell.clone()));
    let literal_facts = PureFactContext::new()
        .assume_proposition(Proposition::ResourceComposition(literals.clone()));
    assert!(!literals.proves_owned_pointers_separate_shallow(&first, &second));
    assert!(!literals.proves_owned_pointers_separate_by(&first, &second, inside));
    assert!(!literals.proves_owned_memory_ranges_separate_by(
        &first_cell,
        &second_cell,
        &literal_facts,
        crate::kernel::assumptions::memory_range_shallowly_contained,
    ));
    assert!(!literals.proves_owned_range_separate_from_pointer_shallow(
        &first_cell,
        &second,
        &literal_facts,
        inside,
    ));
    assert!(
        literal_facts
            .composition_separated_members(
                &first,
                &second,
                |range| range == &first_cell,
                |range| range == &second_cell,
                |_, _| true,
            )
            .is_none()
    );
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
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(94_001)), 4),
    };
    let acquired = Pointer {
        block: PointerBlock::Symbolic(Variable(1_000_001)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let value_cell = memory_range(value.clone(), 0, 1);
    let acquired_cell = memory_range(acquired.clone(), 0, 1);
    let compose = |facts: Vec<ResourceFact>| {
        let context = facts
            .into_iter()
            .fold(ResourceContext::new(), ResourceContext::unchecked_with_fact);
        PureFactContext::new().assume_proposition(Proposition::ResourceComposition(context))
    };

    // The shape `mdtests/c_contract_executes_acquire.md` needs. The two
    // members are spelled in different blocks, and nothing structural relates
    // an `ExternalArgument` address to a pointer a callback returned; only
    // ownership does.
    let owners = compose(vec![
        ResourceFact::own_memory(value_cell.clone()),
        ResourceFact::own_memory(acquired_cell.clone()),
    ]);
    assert!(
        owned_composition_store_separated_evidence(&value, 4, &acquired, 4, &owners).is_some(),
        "two owned members of one composition are disjoint by the partition invariant"
    );

    // An owner beside a *view* is not two owners. The view may be an
    // observation of that very ownership (`owner_observation_core`), which is
    // why `MemoryResourceAlgebra::pair_validity_error` refuses only
    // owner/owner overlap; whether a particular view is independent is
    // decided by its loan binding, which this rule cannot see.
    let owner_and_view = compose(vec![
        ResourceFact::own_memory(value_cell.clone()),
        ResourceFact::view_memory(acquired_cell.clone()),
    ]);
    assert!(
        owned_composition_store_separated_evidence(&value, 4, &acquired, 4, &owner_and_view)
            .is_none(),
        "an owner beside a view is not a partition: the view may describe the owner's own bytes"
    );

    // A cell one element past the owned range is in no member at all.
    let past_the_end = acquired.offset_by_int32_elements(MachineTerm::constant(1));
    assert!(
        owned_composition_store_separated_evidence(&value, 4, &past_the_end, 4, &owners).is_none(),
        "a read outside every owned member inherits nothing from the composition"
    );

    // A folded composite contributes no memory range, so a cell its body
    // would cover is not separated by it: the rule reads `memory_own_range`
    // and never opens a definition.
    let folded = compose(vec![
        ResourceFact::own_memory(value_cell.clone()),
        ResourceFact::own(Resource::Composite {
            name: "Cell".to_string(),
            arguments: vec![ProgramValue::pointer(acquired.clone()).into()].into(),
        }),
    ]);
    assert!(
        owned_composition_store_separated_evidence(&value, 4, &acquired, 4, &folded).is_none(),
        "a composite that is still folded owns no range this rule can read"
    );

    // Two owned members of one block whose bounds are symbolic are the same
    // rule: what makes them disjoint is that one context holds both, and it
    // is whoever handed both out that had to establish the split. Only the
    // spelling changes, which is exactly why the rule may not read one.
    let symbolic_member = |index: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(index)), 4),
    };
    let (front, back) = (symbolic_member(94_002), symbolic_member(94_003));
    let one_block = compose(vec![
        ResourceFact::own_memory(memory_range(front.clone(), 0, 1)),
        ResourceFact::own_memory(memory_range(back.clone(), 0, 1)),
    ]);
    assert!(
        owned_composition_store_separated_evidence(&front, 4, &back, 4, &one_block).is_some(),
        "the partition does not care how the two members are spelled"
    );

    // One member cannot separate an address from itself, whichever end of the
    // question it is asked from.
    let single = compose(vec![ResourceFact::own_memory(value_cell.clone())]);
    assert!(
        owned_composition_store_separated_evidence(&value, 4, &value, 4, &single).is_none(),
        "one member is not two"
    );

    // The evidence names its premise. A composition the context no longer
    // holds does not re-check, which is what keeps a hop retained at an
    // earlier program point from being spent in a context that has moved on.
    let hop = owned_composition_store_separated_evidence(&value, 4, &acquired, 4, &owners)
        .expect("the two-owner case produced evidence");
    let store = MemoryDerivation::Store {
        base: crate::kernel::intern_memory(Memory::new()),
        pointer: value.clone(),
        value: crate::kernel::api::int32(1).into(),
    };
    assert!(
        hop.checks(&store, &acquired, 4, &owners),
        "the hop re-checks against the composition it named"
    );
    assert!(
        !hop.checks(&store, &acquired, 4, &PureFactContext::new()),
        "a retained hop is worthless in a context that does not hold its composition"
    );
}

/// The entry partition pairs a contract's *transferred* clauses with its
/// *borrowed* ones, and nothing else. This pins the three pairs it must never
/// build and the one clause shape it has to skip rather than approximate;
/// `docs/internals/resource-tracker.md`, "The entry partition", carries the
/// argument, and the mdtests beginning `a_caller_cannot_lend_` carry the
/// call-site attacks.
#[test]
fn the_entry_partition_pairs_a_transferred_clause_only_with_a_borrowed_one() {
    use crate::kernel::ResourceTransferRole;
    use crate::kernel::contract_entry_partition_facts;
    use crate::kernel::functions::CheckedResourceFact;

    let argument = |index: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(index)), 4),
    };
    let (owned_base, viewed_base) = (argument(95_001), argument(95_002));
    let owned_cell = memory_range(owned_base.clone(), 0, 2);
    let viewed_cell = memory_range(viewed_base.clone(), 0, 1);
    let clause = |fact: ResourceFact, role: ResourceTransferRole| CheckedResourceFact {
        fact,
        role,
        state_source: ResourceStateSource::Entry,
        clause_position: None,
        section_index: None,
        selected_mutex_source: None,
    };
    let separation = |left: &MemoryRange, right: &MemoryRange| Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(left.clone())),
        right: Box::new(Resource::Memory(right.clone())),
    };

    // The shape `mdtests/const_callback_field.md` needs: `owns object(r)`
    // beside `views p[0..1]`, both spelled in one `external` block.
    let partition = contract_entry_partition_facts(&[
        clause(
            ResourceFact::own_memory(owned_cell.clone()),
            ResourceTransferRole::Consume,
        ),
        clause(
            ResourceFact::view_memory(viewed_cell.clone()),
            ResourceTransferRole::Borrow,
        ),
    ]);
    assert_eq!(
        partition,
        vec![separation(&owned_cell, &viewed_cell)],
        "a transferred clause and a borrowed clause of one contract are disjoint"
    );

    // Two borrowed views may overlap freely: the caller lends both, and
    // lending twice is exactly what a shared borrow permits.
    assert!(
        contract_entry_partition_facts(&[
            clause(
                ResourceFact::view_memory(owned_cell.clone()),
                ResourceTransferRole::Borrow,
            ),
            clause(
                ResourceFact::view_memory(viewed_cell.clone()),
                ResourceTransferRole::Borrow,
            ),
        ])
        .is_empty(),
        "two borrowed views are not a partition"
    );

    // Two owners are `owned_composition_store_separated_evidence` (Route B)
    // already. Emitting the pair here as well would be one rule written
    // twice, in two places a fix would then have to find.
    assert!(
        contract_entry_partition_facts(&[
            clause(
                ResourceFact::own_memory(owned_cell.clone()),
                ResourceTransferRole::Consume,
            ),
            clause(
                ResourceFact::own_memory(viewed_cell.clone()),
                ResourceTransferRole::Consume,
            ),
        ])
        .is_empty(),
        "two owners are Route B, not the entry partition"
    );

    // An owner beside the owner observation of its own range. The context a
    // body proof runs under holds exactly this pair — `owns r` publishes
    // `views r` (`ResourceContext::observable_facts_assuming_valid`) — and
    // separating a range from itself would be a false theorem. The
    // discriminator is that this rule reads the contract's clause list, which
    // holds one fact per written clause, so the observation never reaches it;
    // were it to, the fact below is what it would produce.
    let self_observation = contract_entry_partition_facts(&[
        clause(
            ResourceFact::own_memory(owned_cell.clone()),
            ResourceTransferRole::Consume,
        ),
        clause(
            ResourceFact::view_memory(owned_cell.clone()),
            ResourceTransferRole::Borrow,
        ),
    ]);
    assert_eq!(
        self_observation,
        vec![separation(&owned_cell, &owned_cell)],
        "the clause list is the only filter: a context's derived views must never be passed here"
    );

    // A pair the block algebra already decides records nothing. Every memory
    // separation the context holds is one more entry in the block-pair bucket
    // that each coverage and overlap query walks, so an answer those queries
    // reach anyway is pure scan cost. An `ExternalArgument` range beside a
    // global is *not* such a pair — that is the case
    // `mdtests/global_may_alias_an_array_argument.md` exists for — so this
    // uses two file-scope declarations, which are two objects.
    let global = |name: &str| Pointer {
        block: PointerBlock::Concrete(name.to_string()),
        offset: PointerOffsetTerm::Constant(0),
    };
    assert!(
        contract_entry_partition_facts(&[
            clause(
                ResourceFact::own_memory(memory_range(global("global:g"), 0, 1)),
                ResourceTransferRole::Consume,
            ),
            clause(
                ResourceFact::view_memory(memory_range(global("global:h"), 0, 1)),
                ResourceTransferRole::Borrow,
            ),
        ])
        .is_empty(),
        "two proven-distinct blocks need no recorded separation"
    );

    // A clause that is not plain memory has no range to name. `separate` over
    // two memory operands cannot express a folded composite's footprint
    // without expanding it, so the pair is skipped outright.
    assert!(
        contract_entry_partition_facts(&[
            clause(
                ResourceFact::own(Resource::Composite {
                    name: "Cell".to_string(),
                    arguments: vec![ProgramValue::pointer(owned_base.clone()).into()].into(),
                }),
                ResourceTransferRole::Consume,
            ),
            clause(
                ResourceFact::view_memory(viewed_cell.clone()),
                ResourceTransferRole::Borrow,
            ),
        ])
        .is_empty(),
        "a folded composite owns no range this rule may approximate"
    );
}

#[test]
fn memory_resolution_uses_compact_resource_composition_with_shallow_equalities() {
    let member_left_index = MachineTerm::Variable(Variable(93_410));
    let member_right_index = MachineTerm::Variable(Variable(93_411));
    let query_left_index = MachineTerm::Variable(Variable(93_412));
    let query_right_index = MachineTerm::Variable(Variable(93_413));
    let pointer = |index: MachineTerm| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(index, 4),
    };
    let left_range = memory_range(pointer(member_left_index.clone()), 0, 4);
    let right_range = memory_range(pointer(member_right_index.clone()), 0, 4);
    let context = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(left_range.clone()))
        .unchecked_with_fact(ResourceFact::own_memory(right_range));
    let composition = context
        .observable_facts(&PureFactContext::new())
        .expect("the two owned ranges should compose")
        .into_iter()
        .find(|fact| matches!(fact, Proposition::ResourceComposition(_)))
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
    let arena = MachineTerm::Variable(Variable(93_414));
    let data = MachineTerm::Variable(Variable(93_415));
    let query_arena = MachineTerm::Variable(Variable(93_416));
    let query_data = MachineTerm::Variable(Variable(93_417));
    let start = MachineTerm::Variable(Variable(93_418));
    let end = MachineTerm::Variable(Variable(93_419));
    let index = MachineTerm::Variable(Variable(93_420));
    let pointer = |base: MachineTerm| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(base, 4),
    };
    let arena_fields = memory_range(pointer(arena.clone()), 0, 2);
    let backing = MemoryRange::new(pointer(data.clone()), start.clone(), end.clone());
    let context = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(arena_fields))
        .unchecked_with_fact(ResourceFact::own_memory(backing));
    let composition = context
        .observable_facts(&PureFactContext::new())
        .expect("the owned metadata and backing should compose")
        .into_iter()
        .find(|fact| matches!(fact, Proposition::ResourceComposition(_)))
        .expect("multiple symbolic owned ranges should expose compact authority");
    let absolute = MachineTerm::add(start.clone(), index);
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
    let len = MachineTerm::Variable(Variable(93_420));
    let cap = MachineTerm::Variable(Variable(93_421));
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let prefix = MemoryRange::new(base.clone(), MachineTerm::constant(0), len.clone());
    let suffix = MemoryRange::new(base.clone(), len.clone(), cap.clone());
    let context = ResourceContext::new()
        .unchecked_with_fact(ResourceFact::own_memory(prefix.clone()))
        .unchecked_with_fact(ResourceFact::own_memory(suffix.clone()));
    let composition = context
        .observable_facts(&PureFactContext::new())
        .expect("the two owned ranges should compose")
        .into_iter()
        .find(|fact| matches!(fact, Proposition::ResourceComposition(_)))
        .expect("multi-owner contexts should expose one compact authority");
    let assumptions = PureFactContext::new()
        .assume_proposition(composition)
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(1), len.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(
                MachineTerm::add(len.clone(), MachineTerm::constant(1)),
                cap.clone(),
            ),
            true,
        );

    assert!(
        crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(prefix.clone())),
                right: Box::new(Resource::Memory(suffix.clone())),
            }
        ),
        "the two owned ranges themselves are separate by composition"
    );
    assert!(
        crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(MemoryRange::new(
                    base.clone(),
                    MachineTerm::constant(0),
                    MachineTerm::constant(1),
                ))),
                right: Box::new(Resource::Memory(MemoryRange::new(
                    base.clone(),
                    len.clone(),
                    MachineTerm::add(len, MachineTerm::constant(1)),
                ))),
            }
        ),
        "subranges of distinct owned facts inherit the composition's separation"
    );
    assert!(
        !crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &Proposition::ResourceSeparate {
                left: Box::new(Resource::Memory(MemoryRange::new(
                    base.clone(),
                    MachineTerm::constant(0),
                    MachineTerm::constant(2),
                ))),
                right: Box::new(Resource::Memory(MemoryRange::new(
                    base,
                    MachineTerm::constant(1),
                    MachineTerm::constant(3),
                ))),
            }
        ),
        "overlapping subranges of one owned fact must not become separate"
    );
}

#[test]
fn memory_resolution_alias_check_uses_exact_transitive_range_bounds() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(92)), 4),
    };
    let data = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(93)), 4),
    };
    let index = MachineTerm::Variable(Variable(94));
    let length = MachineTerm::Variable(Variable(95));
    let capacity = MachineTerm::Variable(Variable(96));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(memory_range(owner.clone(), 0, 4))),
            right: Box::new(Resource::Memory(memory_range(
                data.clone(),
                0,
                capacity.clone(),
            ))),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(length, capacity), true);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(MachineTerm::constant(1)),
        &data.offset_by_int32_elements(index),
        &assumptions,
    ));

    let incremented = MachineTerm::add(
        MachineTerm::Variable(Variable(94)),
        MachineTerm::constant(1),
    );
    let incremented_assumptions = assumptions
        .assume_condition(
            ConditionTerm::signed_add_overflows(
                MachineTerm::Variable(Variable(94)),
                MachineTerm::constant(1),
            ),
            false,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(
                incremented.clone(),
                MachineTerm::Variable(Variable(96)),
            ),
            true,
        );
    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(MachineTerm::constant(1)),
        &data.offset_by_int32_elements(incremented),
        &incremented_assumptions,
    ));
}

#[test]
fn memory_resolution_alias_check_uses_strict_indices_across_equal_loaded_bases() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(97)), 4),
    };
    let data_cell = owner.offset_by_bytes(8);
    let before = Memory::new();
    let after = before.clone().with_block("local:temporary", 4);
    let data_before = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before.clone()),
        Box::new(data_cell.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let data_after = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(after),
        Box::new(data_cell),
        crate::kernel::LoadKind::Int32,
    );
    let length = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before),
        Box::new(owner),
        crate::kernel::LoadKind::Int32,
    );
    let index = MachineTerm::subtract(length.clone(), MachineTerm::constant(1));
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
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(92)), 4),
    };
    let len_cell = owner.offset_by_int32_elements(MachineTerm::constant(1));
    let data_cell = owner.offset_by_int32_elements(MachineTerm::constant(2));
    let before = Memory::new();
    let after = before.clone().store(len_cell, int32(7));
    let data_before = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before.clone()),
        Box::new(data_cell.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let data_after = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(after),
        Box::new(data_cell),
        crate::kernel::LoadKind::Int32,
    );
    let zero_index = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before),
        Box::new(owner.clone()),
        crate::kernel::LoadKind::Int32,
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
        ConditionTerm::equal(zero_index, MachineTerm::constant(0)),
        true,
    );

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner.offset_by_int32_elements(MachineTerm::constant(1)),
        &owner.offset_by_int32_elements(MachineTerm::constant(2)),
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
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(93)), 4),
    };
    let len_cell = owner.clone();
    let data_cell = owner.offset_by_int32_elements(MachineTerm::constant(2));
    let before = Memory::new();
    let after = before.clone().store(len_cell, int32(7));
    let data_before = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before.clone()),
        Box::new(data_cell.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let data_after = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(after),
        Box::new(data_cell),
        crate::kernel::LoadKind::Int32,
    );
    let length = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before.clone()),
        Box::new(owner.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let capacity = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before.clone()),
        Box::new(owner.offset_by_int32_elements(MachineTerm::constant(1))),
        crate::kernel::LoadKind::Int32,
    );
    let index = MachineTerm::subtract(length.clone(), MachineTerm::constant(1));
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
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(memory_range(owner.clone(), 0, 4))),
            right: Box::new(Resource::Memory(MemoryRange::new(
                data_base.clone(),
                MachineTerm::constant(0),
                capacity.clone(),
            ))),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), index.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(index.clone(), length.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(length, capacity), true);

    assert!(pointers_proven_distinct_for_memory_resolution(
        &owner,
        &owner.offset_by_int32_elements(MachineTerm::constant(2)),
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
        &owner.offset_by_int32_elements(MachineTerm::constant(2)),
        &indexed_data,
        &assumptions,
    ));
}

#[test]
fn incremented_materialized_index_transports_its_nonnegative_bound() {
    let owner = Pointer {
        block: "arg-memory".into(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(931)), 4),
    };
    let local_index = Pointer {
        block: "local:index".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = Memory::new();
    let old_len = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(before.clone()),
        Box::new(owner.clone()),
        crate::kernel::LoadKind::Int32,
    );
    let materialized = before
        .with_block("local:index", 4)
        .store(local_index.clone(), int32(old_len.clone()));
    let materialized_index = MachineTerm::MemoryLoad(
        crate::kernel::intern_memory(materialized),
        Box::new(local_index),
        crate::kernel::LoadKind::Int32,
    );
    let incremented = MachineTerm::add(materialized_index, MachineTerm::constant(1));
    let upper = MachineTerm::Variable(Variable(932));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), old_len.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(old_len, upper), true);

    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_equal(
            MachineTerm::constant(0),
            incremented.clone(),
        )),
        Some(true)
    );
    assert_eq!(
        assumptions.decide(&ConditionTerm::signed_less_than(
            MachineTerm::constant(0),
            incremented,
        )),
        Some(true)
    );
}

#[test]
fn assumptions_resolve_materialized_symbolic_memory_load_aliases() {
    let k = Variable(75);
    let k_bits = MachineTerm::Variable(k);
    let base_memory = Memory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::scaled_int32_node(k_bits, 4),
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(MachineTerm::MemoryLoad(
                        crate::kernel::intern_memory(base_memory.clone()),
                        Box::new(pointer),
                        crate::kernel::LoadKind::Int32,
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
                    MachineTerm::Variable(k),
                    MachineTerm::constant(index as u32),
                ),
                true,
            );

        assert!(crate::kernel::search::ProofSearch::proves(
            &(assumptions),
            &Proposition::ConditionIs(
                ConditionTerm::equal(
                    MachineTerm::MemoryLoad(
                        crate::kernel::intern_memory(base_memory.clone()),
                        Box::new(pointer),
                        crate::kernel::LoadKind::Int32
                    ),
                    MachineTerm::MemoryLoad(
                        crate::kernel::intern_memory(materialized_memory.clone()),
                        Box::new(symbolic_src.clone()),
                        crate::kernel::LoadKind::Int32,
                    ),
                ),
                true,
            )
        ));
    }
}

#[test]
fn assumptions_reject_forall_based_on_a_shadowed_materialized_load_index() {
    let k = Variable(76);
    let k_bits = MachineTerm::Variable(k);
    let base_memory = Memory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::scaled_int32_node(k_bits.clone(), 4),
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(MachineTerm::MemoryLoad(
                        crate::kernel::intern_memory(base_memory.clone()),
                        Box::new(pointer),
                        crate::kernel::LoadKind::Int32,
                    )),
                )
            });
    let body = Proposition::Implies(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), k_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(k_bits.clone(), MachineTerm::constant(3)),
                true,
            )),
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(base_memory),
                    Box::new(src_pointers[1].clone()),
                    crate::kernel::LoadKind::Int32,
                ),
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(materialized_memory),
                    Box::new(symbolic_src.clone()),
                    crate::kernel::LoadKind::Int32,
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
                ConditionTerm::equal(k_bits.clone(), MachineTerm::constant(0)),
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
                        ConditionTerm::equal(k_bits, MachineTerm::constant(1)),
                        true,
                    )),
                    Box::new(Proposition::ForAll {
                        name: Default::default(),
                        var: k,
                        sort: Sort::ProgramInt32,
                        body: Box::new(body),
                    }),
                )),
            )),
        )),
    );

    assert!(!crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &proposition
    ));
}

#[test]
fn assumptions_reject_forall_based_on_a_shadowed_prefix_index() {
    let i = Variable(82);
    let k = Variable(83);
    let i_bits = MachineTerm::Variable(i);
    let k_bits = MachineTerm::Variable(k);
    let base_memory = Memory::new().with_block("dst", 12).with_block("src", 12);
    let src_pointers = [0, 4, 8].map(|offset| Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::Constant(offset),
    });
    let symbolic_src = Pointer {
        block: "src".into(),
        offset: PointerOffsetTerm::scaled_int32_node(k_bits.clone(), 4),
    };
    let materialized_memory =
        src_pointers
            .iter()
            .cloned()
            .fold(base_memory.clone(), |memory, pointer| {
                memory.store(
                    pointer.clone(),
                    int32(MachineTerm::MemoryLoad(
                        crate::kernel::intern_memory(base_memory.clone()),
                        Box::new(pointer),
                        crate::kernel::LoadKind::Int32,
                    )),
                )
            });
    let body = Proposition::Implies(
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), k_bits.clone()),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::signed_less_than(
                    k_bits.clone(),
                    binary_node!(
                        Int32,
                        Add,
                        Box::new(i_bits.clone()),
                        Box::new(MachineTerm::constant(1)),
                    ),
                ),
                true,
            )),
        )),
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(base_memory),
                    Box::new(src_pointers[1].clone()),
                    crate::kernel::LoadKind::Int32,
                ),
                MachineTerm::MemoryLoad(
                    crate::kernel::intern_memory(materialized_memory),
                    Box::new(symbolic_src.clone()),
                    crate::kernel::LoadKind::Int32,
                ),
            ),
            true,
        )),
    );
    let proposition = Proposition::Implies(
        Box::new(Proposition::ConditionIs(
            ConditionTerm::equal(i_bits.clone(), MachineTerm::constant(1)),
            true,
        )),
        Box::new(Proposition::Implies(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::pointer_offset_equal(
                    symbolic_src.offset,
                    PointerOffsetTerm::scaled_int32_node(i_bits.clone(), 4),
                ),
                true,
            )),
            Box::new(Proposition::Implies(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(k_bits, i_bits),
                    true,
                )),
                Box::new(Proposition::ForAll {
                    name: Default::default(),
                    var: k,
                    sort: Sort::ProgramInt32,
                    body: Box::new(body),
                }),
            )),
        )),
    );

    assert!(!crate::kernel::search::ProofSearch::proves(
        &(PureFactContext::new()),
        &proposition
    ));
}

#[test]
fn added_composition_carrier_keeps_state_premise_work_bounded() {
    // The lazy-separation monotonicity requirement: adding a valid compact
    // composition carrier must not break, or meaningfully slow, an already
    // provable state premise. Pinned by the bounded-pool regression where
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
    // The framed load is the `int32` at offset zero; the neighbour store is
    // four bytes away, which only a declared width keeps clear of it.
    crate::kernel::eval::declare_load_access_width(&target, 4);
    let before = Memory::new().with_block("arena", 64);
    let after = before.clone().store(neighbor, int32(7));
    let premise = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            MachineTerm::constant(0),
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(after),
                Box::new(target.clone()),
                crate::kernel::LoadKind::Int32,
            ),
        ),
        true,
    );
    let recorded = Proposition::ConditionIs(
        ConditionTerm::signed_less_equal(
            MachineTerm::constant(0),
            MachineTerm::MemoryLoad(
                crate::kernel::intern_memory(before),
                Box::new(target),
                crate::kernel::LoadKind::Int32,
            ),
        ),
        true,
    );
    let carrier = |index: u64| {
        let base = Pointer {
            block: PointerBlock::Concrete(format!("carrier-{index}")),
            offset: PointerOffsetTerm::Constant(0),
        };
        let split = MachineTerm::Variable(Variable(95_000 + index));
        let end = MachineTerm::Variable(Variable(95_100 + index));
        Proposition::ResourceComposition(
            ResourceContext::new()
                .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(
                    base.clone(),
                    MachineTerm::constant(0),
                    split.clone(),
                )))
                .unchecked_with_fact(ResourceFact::own_memory(MemoryRange::new(base, split, end))),
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
    let (proved_four, work_four) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::search::ProofSearch::proves(&(four), &premise)
    });
    assert!(
        proved_four,
        "the framed premise should prove with four carriers"
    );
    let five = context_with(5);
    let (proved_five, work_five) = crate::instrumentation::measure_deterministic_work(|| {
        crate::kernel::search::ProofSearch::proves(&(five), &premise)
    });
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
    let memory = intern_memory(
        Memory::new()
            .with_block("local:a", 4)
            .with_block("local:b", 4)
            .with_block("local:c", 4),
    );
    crate::kernel::with_load_variable_registry_capacity(2, || {
        let first = load_variable_for_cell_with_origin(
            &memory,
            &pointer("local:a"),
            crate::kernel::LoadKind::Int32,
            4,
            &memory,
        );
        load_variable_for_cell_with_origin(
            &memory,
            &pointer("local:b"),
            crate::kernel::LoadKind::Int32,
            4,
            &memory,
        );
        // Re-registering an identity the registry already knows is not growth
        // and must keep returning the same variable.
        let again = load_variable_for_cell_with_origin(
            &memory,
            &pointer("local:a"),
            crate::kernel::LoadKind::Int32,
            4,
            &memory,
        );
        assert_eq!(first, again);
        assert_eq!(crate::kernel::load_variable_registry_len(), 2);
        // The third distinct identity exceeds the capacity: the registry must
        // fail loudly here rather than forget the entries that guard against
        // id collisions.
        load_variable_for_cell_with_origin(
            &memory,
            &pointer("local:c"),
            crate::kernel::LoadKind::Int32,
            4,
            &memory,
        );
    });
}

/// Two distinct loads whose hashes land on one id must still get two ids.
///
/// The id space is narrowed until every hash collides. Each load keeps its
/// own id, each id names only the load it was minted for, and asking again
/// for a load already named returns its id rather than another slot: the
/// registry decides the id, and the hash only says where to start looking.
#[test]
fn colliding_load_hashes_still_mint_distinct_load_variables() {
    let _session = crate::kernel::VerificationSession::enter();
    let pointer = |block: &str| Pointer {
        block: block.into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let memory = intern_memory(
        Memory::new()
            .with_block("local:a", 4)
            .with_block("local:b", 4)
            .with_block("local:c", 4),
    );
    crate::kernel::with_load_variable_range(4, || {
        let blocks = ["local:a", "local:b", "local:c"];
        let variables = blocks.map(|block| {
            crate::kernel::eval::load_variable_for_exact_cell(
                &memory,
                &pointer(block),
                crate::kernel::LoadKind::Int32,
                4,
            )
        });
        for (index, block) in blocks.iter().enumerate() {
            for other in &variables[index + 1..] {
                assert_ne!(variables[index], *other, "two loads share one id");
            }
            assert_eq!(
                crate::kernel::registered_load_for_variable(&variables[index]),
                Some((memory.clone(), pointer(block))),
                "an id must name the load it was minted for"
            );
            assert_eq!(
                crate::kernel::eval::load_variable_for_exact_cell(
                    &memory,
                    &pointer(block),
                    crate::kernel::LoadKind::Int32,
                    4
                ),
                variables[index],
                "a load already named keeps its id"
            );
        }
        assert_eq!(crate::kernel::load_variable_registry_len(), 3);
    });
}

/// `(data + i) + j` with `i == INT_MAX`, `j == 1` and `data + k` with
/// `k == INT_MIN` have equal wrapped index sums but exact byte offsets of
/// +2^33 and -2^33, so the equality must not be decided true.
#[test]
fn wrapped_index_sum_does_not_decide_pointer_offsets_equal() {
    let i = MachineTerm::Variable(Variable(93_401));
    let j = MachineTerm::Variable(Variable(93_402));
    let k = MachineTerm::Variable(Variable(93_403));
    let scaled = |value: &MachineTerm| PointerOffsetTerm::scaled_int32_node(value.clone(), 4);
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::equal(i.clone(), MachineTerm::constant(i32::MAX as u32)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(j.clone(), MachineTerm::constant(1)),
            true,
        )
        .assume_condition(
            ConditionTerm::equal(k.clone(), MachineTerm::constant(i32::MIN as u32)),
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
    let base = MachineTerm::Variable(Variable(93_405));
    let with_base = |offset: PointerOffsetTerm| {
        PointerOffsetTerm::Add(Box::new(scaled(&base)), Box::new(offset))
    };
    let k_is_two = PureFactContext::new().assume_condition(
        ConditionTerm::equal(k.clone(), MachineTerm::constant(2)),
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
        ConditionTerm::equal(k.clone(), MachineTerm::constant(3)),
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
    let m = MachineTerm::Variable(Variable(93_404));
    let same =
        PureFactContext::new().assume_condition(ConditionTerm::equal(i.clone(), m.clone()), true);
    assert_eq!(
        same.decide(&ConditionTerm::pointer_offset_equal(scaled(&i), scaled(&m))),
        Some(true)
    );
}

#[test]
fn quantified_load_witness_does_not_certify_loadability_in_a_freed_state() {
    // A universal fact about `load(live, p + k)` witnesses that `p + j` is
    // loadable in `live` (its guard covers `j`), but not in a state where
    // the block is gone.
    let block: PointerBlock = "heap:witness".into();
    let live = Memory::new().with_block(block.clone(), 4);
    let freed = Memory::new();
    let base = Pointer {
        block,
        offset: PointerOffsetTerm::Constant(0),
    };
    let k = Variable(93_501);
    let j = MachineTerm::Variable(Variable(93_502));
    let witness = forall_int32(
        k,
        Proposition::Implies(
            Box::new(Proposition::And(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(
                        MachineTerm::Variable(k),
                        MachineTerm::constant(0),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        MachineTerm::Variable(k),
                        MachineTerm::constant(1),
                    ),
                    true,
                )),
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::equal(
                    MachineTerm::MemoryLoad(
                        crate::kernel::intern_memory(live.clone()),
                        Box::new(base.offset_by_int32_elements(MachineTerm::Variable(k))),
                        crate::kernel::LoadKind::Int32,
                    ),
                    MachineTerm::constant(0),
                ),
                true,
            )),
        ),
    );
    let assumptions = PureFactContext::new()
        .assume_proposition(witness)
        .assume_condition(
            ConditionTerm::signed_greater_equal(j.clone(), MachineTerm::constant(0)),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_than(j.clone(), MachineTerm::constant(1)),
            true,
        );
    let cell = base.offset_by_int32_elements(j);

    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory: live,
            base: cell.clone(),
            bytes: MachineTerm::constant(4),
            wide: false,
        }
    ));
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory: freed,
            base: cell,
            bytes: MachineTerm::constant(4),
            wide: false,
        }
    ));
}

#[test]
fn freed_external_allocation_is_not_still_available() {
    // `free` keeps the `ExternalArgument` block, so availability must also
    // compare which allocations each state has freed.
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scaled_int32_node(MachineTerm::Variable(Variable(93_503)), 4),
    };
    let live = Memory::new()
        .with_heap_allocation_claim(base.clone(), HeapExtent::int32(8))
        .expect("a fresh external allocation claim is accepted");
    let freed = live
        .clone()
        .free_heap_block(&base, &PureFactContext::new())
        .expect("the claimed allocation can be freed");
    let element = base.offset_by_int32_elements(MachineTerm::constant(1));

    assert!(crate::kernel::reasoning::memory_range_still_available(
        &live,
        &live,
        &base,
        &PureFactContext::new(),
    ));
    assert!(!crate::kernel::reasoning::memory_range_still_available(
        &live,
        &freed,
        &base,
        &PureFactContext::new(),
    ));
    assert!(!crate::kernel::reasoning::memory_range_still_available(
        &live,
        &freed,
        &element,
        &PureFactContext::new(),
    ));

    let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
        memory: live.clone(),
        base: base.clone(),
        bytes: MachineTerm::constant(8),
        wide: false,
    });
    assert!(crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory: live,
            base: base.clone(),
            bytes: MachineTerm::constant(4),
            wide: false,
        }
    ));
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::MemoryLoadable {
            memory: freed,
            base,
            bytes: MachineTerm::constant(4),
            wide: false,
        }
    ));
}

/// A concrete range fold unrolls over ranges of any length: the steps are
/// the range's own length, and a sum over 1,025 to 4,096 items folds to its
/// constant, which the old unroll cap of 1,024 left symbolic.
#[test]
fn range_fold_unrolls_concrete_ranges_of_any_length() {
    let accumulator = Variable(7_800_000);
    let item = Variable(7_800_001);
    let body = MachineTerm::add(
        MachineTerm::Variable(accumulator),
        MachineTerm::Variable(item),
    );
    for length in [1_025u32, 2_048, 4_096] {
        let sum = (0..length).sum::<u32>();
        assert_eq!(
            MachineTerm::range_fold(
                MachineTerm::constant(0),
                MachineTerm::constant(length),
                MachineTerm::constant(0),
                accumulator,
                item,
                body.clone(),
            ),
            MachineTerm::constant(sum),
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
/// observable by each other. Only literals may be merged (C11 6.4.5p7): a
/// literal is never a declared object, but a pointer the caller passed may
/// still point into one.
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
    let global = PointerBlock::Concrete("global:g".to_string());
    let local = PointerBlock::Concrete("local:lifetime:0:tmp".to_string());
    for declared in [&global, &local] {
        assert!(ok.proven_distinct(declared), "{ok} vs {declared}");
        assert!(declared.proven_distinct(&ok), "{declared} vs {ok}");
        assert!(!ok.observable_by_load(declared));
    }
    assert!(!ok.proven_distinct(&PointerBlock::ExternalArgument));
    assert!(ok.observable_by_load(&PointerBlock::ExternalArgument));
}

/// Constant range endpoints are `int32` values, and their guard arithmetic
/// must be the true difference. Subtracting the bit patterns underflows for a
/// negative start: in debug that panicked inside the guard, and in release it
/// wrapped to a small unsigned value and declared an impossible extent valid.
mod constant_range_byte_count_guards {
    use super::*;

    fn guards(start: i32, end: i32, element_width: u32) -> Vec<Proposition> {
        crate::kernel::memory_range_byte_count_guards(
            MachineTerm::constant(start as u32),
            MachineTerm::constant(end as u32),
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
    fn context(count: Variable, bounded: bool) -> (Memory, PureFactContext) {
        let memory = Memory::new();
        let count_term = MachineTerm::Variable(count);
        let mut assumptions = PureFactContext::new()
            .assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: array_base(0),
                bytes: MachineTerm::multiply(count_term.clone(), MachineTerm::constant(4)),
                wide: false,
            })
            .assume_condition(
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), count_term.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_than(MachineTerm::constant(1), count_term.clone()),
                true,
            );
        if bounded {
            assumptions = assumptions.assume_condition(
                ConditionTerm::signed_less_equal(
                    count_term,
                    MachineTerm::constant(crate::kernel::memory_range_element_count_limit(4)),
                ),
                true,
            );
        }
        (memory, assumptions)
    }

    #[test]
    fn wrapped_goal_extent_cannot_pass_by_a_signed_residue() {
        let memory = Memory::new();
        let range_base = array_base(0);
        let range_bytes = MachineTerm::constant(16);
        let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: range_base.clone(),
            bytes: range_bytes.clone(),
            wide: false,
        });
        let wrapped_base = array_base(0x2000_0000);
        let wrapped_bytes = MachineTerm::constant(0x6000_0000);
        assert!(
            !assumptions.proves_loadable_region_from_range(
                &range_base,
                &range_bytes,
                &wrapped_base,
                &wrapped_bytes,
            ),
            "a signed residue must not make an overflowing goal extent fit"
        );
        assert!(
            !assumptions.proves_loadable_cell_from_region(
                &range_base,
                &range_bytes,
                &wrapped_base,
                0x6000_0000,
            ),
            "the constant-width cell route must also reject signed wrap"
        );

        let symbolic_bytes = MachineTerm::Variable(Variable(9_100_005));
        let symbolic_end =
            MachineTerm::add(MachineTerm::constant(0x2000_0000), symbolic_bytes.clone());
        let symbolic_assumptions = assumptions
            .clone()
            .assume_condition(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(symbolic_bytes.clone()),
                    right: Box::new(MachineTerm::constant(0x6000_0000)),
                },
                true,
            )
            .assume_condition(
                ConditionTerm::signed_less_equal(symbolic_end, MachineTerm::constant(16)),
                true,
            );
        assert!(
            !symbolic_assumptions.proves_loadable_region_from_range(
                &range_base,
                &range_bytes,
                &wrapped_base,
                &symbolic_bytes,
            ),
            "symbolic extents must carry evidence that their sum did not wrap"
        );

        assert!(
            assumptions.proves_loadable_region_from_range(
                &range_base,
                &range_bytes,
                &array_base(8),
                &MachineTerm::constant(8),
            ),
            "an exact in-bounds byte window remains covered"
        );
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
                    &MachineTerm::constant(4),
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
            let extent =
                MachineTerm::multiply(MachineTerm::Variable(count), MachineTerm::constant(4));
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
        let memory = Memory::new();
        let wrapped = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: array_base(0),
            bytes: MachineTerm::multiply(
                MachineTerm::constant(WRAPPING_COUNT),
                MachineTerm::constant(4),
            ),
            wide: false,
        });
        // `1 << 30` four-byte elements scale to `0` bytes: the fact is true
        // and covers nothing, so no cell comes out of it.
        assert!(
            !wrapped.proves_memory_access(&memory, &array_base(0), 4),
            "a constant wrapped extent yields no cell"
        );
        let widest = PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: array_base(0),
            bytes: MachineTerm::multiply(
                MachineTerm::constant(WRAPPING_COUNT - 1),
                MachineTerm::constant(4),
            ),
            wide: false,
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
        let memory = Memory::new();
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: array_base(0),
                bytes: MachineTerm::Variable(count),
                wide: false,
            })
            .assume_condition(
                ConditionTerm::signed_less_than(
                    MachineTerm::constant(1),
                    MachineTerm::Variable(count),
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

    fn int32_range_loadable(count: MachineTerm) -> Proposition {
        Proposition::MemoryLoadable {
            memory: Memory::new(),
            base: Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: MachineTerm::multiply(count, MachineTerm::constant(4)),
            wide: false,
        }
    }

    /// A range states its count is nonnegative and fits, over the count term
    /// itself — the spelling a proof can write, since the endpoint form's
    /// `fits` half is an unsigned comparison the surface cannot express.
    #[test]
    fn a_range_carries_its_count_bounds() {
        let count = MachineTerm::Variable(Variable(9_200_000));
        assert_eq!(
            crate::kernel::stated_loadable_extent_guards(&int32_range_loadable(count.clone())),
            vec![
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(MachineTerm::constant(0), count.clone()),
                    true,
                ),
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(
                        count,
                        MachineTerm::constant(crate::kernel::memory_range_element_count_limit(4)),
                    ),
                    true,
                ),
            ]
        );
    }

    /// A conjunction is walked, because a `requires` clause is written as one.
    #[test]
    fn a_conjunction_of_ranges_carries_both() {
        let left = MachineTerm::Variable(Variable(9_200_001));
        let right = MachineTerm::Variable(Variable(9_200_002));
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
        let body = int32_range_loadable(MachineTerm::Variable(bound));
        let quantified = Proposition::ForAll {
            name: Default::default(),
            var: bound,
            sort: Sort::ProgramInt32,
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
        let range = int32_range_loadable(MachineTerm::subtract(
            MachineTerm::Variable(hi),
            MachineTerm::Variable(lo),
        ));
        let moved = crate::kernel::substitute_int32_variable_in_proposition(
            &range,
            hi,
            MachineTerm::subtract(MachineTerm::Variable(hi), MachineTerm::constant(1)),
        );
        let moved_count = MachineTerm::subtract(
            MachineTerm::subtract(MachineTerm::Variable(hi), MachineTerm::constant(1)),
            MachineTerm::Variable(lo),
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

    /// A symbolic range's `fits` guard compares the element count's bits as
    /// a `uint32` count: σ of the `int32` difference, built as written, not
    /// the bare `int32` word under an unsigned comparison.
    #[test]
    fn a_symbolic_range_fits_guard_compares_sigma_of_its_count() {
        use crate::kernel::{ConditionTerm, MachineIntegerType, MemoryRangeExtent};
        let start = MachineTerm::Variable(Variable(9_200_020));
        let end = MachineTerm::Variable(Variable(9_200_021));
        let MemoryRangeExtent::Guards(guards) =
            crate::kernel::memory_range_byte_count_extent(start.clone(), end.clone(), 4)
        else {
            panic!("symbolic endpoints carry guards");
        };
        let count = binary_node!(Int32, Subtract, Box::new(end), Box::new(start));
        let fits = ConditionTerm::unsigned_less_equal(
            MachineTerm::sign_cast32(MachineIntegerType::Int32, MachineIntegerType::UInt32, count),
            MachineTerm::constant(1_073_741_823),
        );
        assert!(
            matches!(&fits, ConditionTerm::Compare { left, .. } if left.sign_cast32_operand().is_some()),
            "{fits:?}"
        );
        assert_eq!(guards[1], Proposition::ConditionIs(fits, true));
    }

    /// A range of one-byte elements keeps its extent unscaled, `a[0..n]` over
    /// `uint8` being `n` bytes, and carries its count bound like a wider
    /// range. One-byte elements have no count limit below `i32::MAX`, so the
    /// nonnegative count is the whole guard.
    #[test]
    fn a_byte_range_carries_its_count_bound() {
        let count = MachineTerm::Variable(Variable(9_200_020));
        let range = Proposition::MemoryLoadable {
            memory: Memory::new(),
            base: Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: count.clone(),
            wide: false,
        };
        assert_eq!(
            crate::kernel::stated_loadable_extent_guards(&range),
            vec![Proposition::ConditionIs(
                ConditionTerm::signed_less_equal(MachineTerm::constant(0), count),
                true,
            )]
        );
    }

    /// A constant extent carries nothing: a cell width or a constant range's
    /// size is already a true count of bytes, decided where it was lowered.
    #[test]
    fn an_unscaled_extent_carries_nothing() {
        let cell = Proposition::MemoryLoadable {
            memory: Memory::new(),
            base: Pointer {
                block: "arg-memory".into(),
                offset: PointerOffsetTerm::Constant(0),
            },
            bytes: MachineTerm::constant(4),
            wide: false,
        };
        assert!(crate::kernel::stated_loadable_extent_guards(&cell).is_empty());
    }

    #[test]
    fn shared_extent_guards_match_wide_integer_arithmetic_at_boundaries() {
        let start_var = Variable(9_200_020);
        let end_var = Variable(9_200_021);
        let assumptions = PureFactContext::new();
        for width in [1, 2, 4, 8] {
            let range = MemoryRange::new_with_element_width(
                Pointer {
                    block: "range".into(),
                    offset: PointerOffsetTerm::Constant(0),
                },
                MachineTerm::Variable(start_var),
                MachineTerm::Variable(end_var),
                width,
            );
            let guards = crate::kernel::memory_range_extent_guard_spellings(&range);
            let limit = (u32::MAX / width).min(i32::MAX as u32) as i32;
            let endpoints = [
                i32::MIN,
                i32::MIN + 1,
                -1,
                0,
                1,
                limit,
                limit.saturating_add(1),
                i32::MAX,
            ];
            for start in endpoints {
                for end in endpoints {
                    let count = i64::from(end) - i64::from(start);
                    let expected = count >= 0 && count * i64::from(width) <= i64::from(u32::MAX);
                    let actual = guards.iter().all(|guard| {
                        let guard = crate::kernel::substitute_int32_variable_in_proposition(
                            guard,
                            start_var,
                            MachineTerm::constant(start as u32),
                        );
                        let guard = crate::kernel::substitute_int32_variable_in_proposition(
                            &guard,
                            end_var,
                            MachineTerm::constant(end as u32),
                        );
                        crate::kernel::prelude::required_obligation_is_exactly_discharged(
                            &assumptions,
                            &guard,
                        )
                    });
                    assert_eq!(actual, expected, "{start}..{end}, width {width}");
                }
            }
        }
    }
}

/// The four tests below pin the two polarities of the element-count bound an
/// affine constant difference needs before it may place an index outside a
/// range. `affine_bitvector_difference_constant` works in `i64` while the
/// endpoints are modular, so the difference it returns is the true one only
/// modulo `2^32`; a residue is outside the range exactly when it reaches the
/// range's element count, and nothing else follows.
fn outside_range_probe(
    range_start: MachineTerm,
    range_end: MachineTerm,
    query_index: MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Constant(0),
    };
    let range = MemoryRange::new(base.clone(), range_start, range_end);
    let pointer = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(query_index, 4),
    };
    assumptions.ranges_directly_disjoint_from_pointer(&[range], &pointer)
}

#[test]
fn a_constant_length_range_bounds_its_own_outside_conclusion() {
    let index = MachineTerm::Variable(Variable(93_940));
    // `p[i..i + 1]` carries its element count structurally, so placing `i + 2`
    // outside it consults nothing.
    assert!(outside_range_probe(
        index.clone(),
        MachineTerm::add(index.clone(), MachineTerm::constant(1)),
        MachineTerm::add(index.clone(), MachineTerm::constant(2)),
        &PureFactContext::new(),
    ));
    // And the other side of the range, by the difference from its start.
    assert!(outside_range_probe(
        index.clone(),
        MachineTerm::add(index.clone(), MachineTerm::constant(1)),
        MachineTerm::subtract(index, MachineTerm::constant(1)),
        &PureFactContext::new(),
    ));
}

#[test]
fn a_stated_ranges_extent_facts_bound_its_outside_conclusion() {
    let count = MachineTerm::Variable(Variable(93_941));
    let assumptions = PureFactContext::new()
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), count.clone()),
            true,
        )
        .assume_condition(
            ConditionTerm::signed_less_equal(
                count.clone(),
                MachineTerm::constant(crate::kernel::memory_range_element_count_limit(4)),
            ),
            true,
        );
    // `p[0..n]` has no constant count, so the bound is the valid-byte-extent
    // condition the stated range carries.
    assert!(outside_range_probe(
        MachineTerm::constant(0),
        count.clone(),
        MachineTerm::add(count.clone(), MachineTerm::constant(1)),
        &assumptions,
    ));
    // Without those facts the same range bounds nothing, so the same query is
    // refused rather than answered from arithmetic that may have wrapped.
    assert!(!outside_range_probe(
        MachineTerm::constant(0),
        count.clone(),
        MachineTerm::add(count, MachineTerm::constant(1)),
        &PureFactContext::new(),
    ));
}

#[test]
fn a_difference_that_wrapped_places_no_index_outside_a_range() {
    let index = MachineTerm::Variable(Variable(93_942));
    // Three constants summing to `2^32`. Each addition is a modular 32-bit
    // add, so this term's value is `i` itself and the cell it names is `p[i]`,
    // which `p[i..i + 1]` contains. The affine difference from the range's end
    // is nonetheless `2^32 - 1`, which the unguarded rule read as "at or above
    // the end".
    let wrapped = MachineTerm::add(
        MachineTerm::add(
            MachineTerm::add(index.clone(), MachineTerm::constant(1_431_655_765)),
            MachineTerm::constant(1_431_655_765),
        ),
        MachineTerm::constant(1_431_655_766),
    );
    assert!(!outside_range_probe(
        index.clone(),
        MachineTerm::add(index, MachineTerm::constant(1)),
        wrapped,
        &PureFactContext::new(),
    ));
}

#[test]
fn an_unbounded_range_places_no_index_outside_itself() {
    let start = MachineTerm::Variable(Variable(93_943));
    let end = MachineTerm::Variable(Variable(93_944));
    // Two unrelated endpoints: the range may span most of the index space, so
    // a residue one below its start proves nothing — at `start == INT_MIN` the
    // predecessor is `INT_MAX`, which such a range can contain.
    assert!(!outside_range_probe(
        start.clone(),
        end,
        MachineTerm::subtract(start, MachineTerm::constant(1)),
        &PureFactContext::new(),
    ));
}

/// The tests below pin both polarities of the premise a *positive* membership
/// conclusion needs, for each rule that draws one from an affine constant
/// difference of modular terms. The mirror image of the four above: an
/// "outside" conclusion survives reduction modulo `2^32` and an "inside" one
/// does not, because the wrapped reading of a residue is outside.
mod membership_needs_an_unwrapped_difference {
    use super::*;

    /// A pointer `base + index * 4 + bytes`.
    fn scaled_pointer(index: MachineTerm, bytes: i64) -> Pointer {
        let offset = PointerOffsetTerm::scale_int32(index, 4);
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset: if bytes == 0 {
                offset
            } else {
                PointerOffsetTerm::add(offset, PointerOffsetTerm::Constant(bytes))
            },
        }
    }

    fn range(start: MachineTerm, end: MachineTerm) -> MemoryRange {
        MemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Constant(0),
            },
            start,
            end,
        )
    }

    fn index_is_nonnegative(index: &MachineTerm) -> PureFactContext {
        PureFactContext::new().assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), index.clone()),
            true,
        )
    }

    /// `i` written so that every addition wraps and the value is `i` again:
    /// three constants summing to `2^32`. Its affine difference from `i` is
    /// `2^32`, whose residue is `0` — which is exactly what the difference
    /// means.
    fn wrapped_identity(index: &MachineTerm) -> MachineTerm {
        MachineTerm::add(
            MachineTerm::add(
                MachineTerm::add(index.clone(), MachineTerm::constant(1_431_655_765)),
                MachineTerm::constant(1_431_655_765),
            ),
            MachineTerm::constant(1_431_655_766),
        )
    }

    #[test]
    fn a_pointer_at_a_constant_byte_offset_is_placed_in_a_range_by_arithmetic_alone() {
        let index = MachineTerm::Variable(Variable(93_950));
        let owned = range(
            index.clone(),
            MachineTerm::add(index.clone(), MachineTerm::constant(4)),
        );
        // A byte displacement is mathematical `i64`, so `&p[i] + 8` is two
        // elements above `p[i]` whatever `i` is, and no fact is needed.
        for elements in 0..4 {
            assert!(crate::kernel::assumptions::pointer_in_memory_range_shallow(
                &scaled_pointer(index.clone(), elements * 4),
                &owned,
            ));
        }
        assert!(
            !crate::kernel::assumptions::pointer_in_memory_range_shallow(
                &scaled_pointer(index.clone(), 16),
                &owned,
            )
        );
        // The same element reached through a start term that wrapped all the
        // way around is still that element.
        assert!(crate::kernel::assumptions::pointer_in_memory_range_shallow(
            &scaled_pointer(index.clone(), 0),
            &range(
                wrapped_identity(&index),
                MachineTerm::add(index, MachineTerm::constant(4)),
            ),
        ));
    }

    #[test]
    fn a_pointer_at_a_wrapping_index_term_needs_the_index_pinned() {
        let index = MachineTerm::Variable(Variable(93_951));
        // `i + 2` is two elements above `i` only while the 32-bit add does not
        // wrap; at `i == i32::MAX - 1` it is `i32::MIN`, nearly `2^32`
        // elements below.
        let bumped = MachineTerm::add(index.clone(), MachineTerm::constant(2));
        let owned = range(
            index.clone(),
            MachineTerm::add(index.clone(), MachineTerm::constant(4)),
        );
        assert!(
            !crate::kernel::assumptions::pointer_in_memory_range_shallow(
                &scaled_pointer(bumped.clone(), 0),
                &owned,
            )
        );
        assert!(
            crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
                &scaled_pointer(bumped.clone(), 0),
                &owned,
                &index_is_nonnegative(&bumped),
            )
        );
        // A start that cannot be positive settles it without any fact, since
        // the wrapped reading needs one.
        assert!(crate::kernel::assumptions::pointer_in_memory_range_shallow(
            &scaled_pointer(MachineTerm::constant(2), 0),
            &range(MachineTerm::constant(0), MachineTerm::constant(4)),
        ));
    }

    // Raw result storage and typed field writes use different element units.
    // Containment must compare complete byte extents, including shifted fields.
    #[test]
    fn constant_typed_fields_fit_only_inside_their_raw_byte_extent() {
        let at = Pointer::symbolic(Variable(93_953));
        let bytes = MemoryRange::new_with_element_width(at.clone(), 0u32.into(), 16u32.into(), 1);
        let field = |offset, width, count| {
            MemoryRange::new_with_element_width(
                at.offset_by_bytes(offset),
                0u32.into(),
                count,
                width,
            )
        };
        for range in [
            field(0, 8, 1u32.into()),
            field(8, 8, 1u32.into()),
            field(4, 4, 3u32.into()),
        ] {
            assert!(crate::kernel::assumptions::memory_range_shallowly_contained(&range, &bytes));
        }
        for range in [
            MemoryRange::new_with_element_width(at.clone(), (-1i32 as u32).into(), 0u32.into(), 4),
            field(12, 8, 1u32.into()),
            field(8, 8, 2u32.into()),
        ] {
            assert!(!crate::kernel::assumptions::memory_range_shallowly_contained(&range, &bytes));
        }
        let symbolic = field(0, 8, MachineTerm::Variable(Variable(93_954)));
        assert!(!crate::kernel::assumptions::memory_range_shallowly_contained(&symbolic, &bytes));
    }

    #[test]
    fn a_child_range_is_contained_by_its_count_or_by_a_forward_parent() {
        let index = MachineTerm::Variable(Variable(93_952));
        let parent = range(
            index.clone(),
            MachineTerm::add(index.clone(), MachineTerm::constant(4)),
        );
        // Same start term: the offset is zero however the endpoints wrapped,
        // and the two counts decide the rest.
        assert!(
            crate::kernel::assumptions::memory_range_shallowly_contained(
                &range(
                    index.clone(),
                    MachineTerm::add(index.clone(), MachineTerm::constant(1)),
                ),
                &parent,
            )
        );
        assert!(
            !crate::kernel::assumptions::memory_range_shallowly_contained(
                &range(
                    index.clone(),
                    MachineTerm::add(index.clone(), MachineTerm::constant(5)),
                ),
                &parent,
            )
        );
        // A child one element in needs that one element not to have wrapped.
        let bumped = MachineTerm::add(index.clone(), MachineTerm::constant(1));
        let child = range(
            bumped.clone(),
            MachineTerm::add(index, MachineTerm::constant(2)),
        );
        assert!(!crate::kernel::assumptions::memory_range_shallowly_contained(&child, &parent));
        assert!(
            crate::kernel::assumptions::memory_range_shallowly_contained_with_facts(
                &child,
                &parent,
                &index_is_nonnegative(&bumped),
            )
        );
    }

    #[test]
    fn a_parent_without_a_count_must_be_known_to_hold_one() {
        let count = MachineTerm::Variable(Variable(93_953));
        let parent = range(MachineTerm::constant(0), count.clone());
        let child = range(MachineTerm::constant(3), count.clone());
        // `p[0..n]` has no constant count, so containment is decided by
        // comparing the two ends. That reads the parent's `end` as
        // `start + count`, which `p[i32::MAX..i32::MIN]` — a forward range of
        // exactly one element — shows is not free.
        assert!(!crate::kernel::assumptions::memory_range_shallowly_contained(&child, &parent));
        assert!(
            crate::kernel::assumptions::memory_range_shallowly_contained_with_facts(
                &child,
                &parent,
                &index_is_nonnegative(&count),
            )
        );
    }

    #[test]
    fn the_fact_graph_membership_rule_needs_the_same_premise() {
        let index = MachineTerm::Variable(Variable(93_954));
        let base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let bumped = MachineTerm::add(index.clone(), MachineTerm::constant(2));
        let pointer = scaled_pointer(bumped.clone(), 0);
        let start = index.clone();
        let end = MachineTerm::add(index, MachineTerm::constant(4));
        assert!(
            !PureFactContext::new().pointer_in_range_by_shallow_fact_graph_with_width(
                &pointer, &base, &start, &end, 4,
            )
        );
        assert!(
            index_is_nonnegative(&bumped).pointer_in_range_by_shallow_fact_graph_with_width(
                &pointer, &base, &start, &end, 4,
            )
        );
    }

    #[test]
    fn the_affine_tail_reads_a_residue_only_as_a_count_may_occupy_it() {
        use crate::kernel::assumptions::element_delta_in_range_by_affine_arithmetic;
        use crate::kernel::reasoning::ExactElementDelta;

        let index = MachineTerm::Variable(Variable(93_955));
        let delta = |term: MachineTerm, constant: i64| ExactElementDelta {
            index: MachineOperandView::Legacy(&term).retain(MachineIntegerType::Int32),
            constant,
        };
        let start = index.clone();
        let end = MachineTerm::add(index.clone(), MachineTerm::constant(4));
        // A residue in the upper half is refused outright: reading it as an
        // offset would place the index `2^31` elements above the start, and no
        // valid extent reaches that far.
        assert!(!element_delta_in_range_by_affine_arithmetic(
            &delta(
                MachineTerm::subtract(index.clone(), MachineTerm::constant(1)),
                0,
            ),
            &start,
            &end,
            &PureFactContext::new(),
        ));
        // The exact `i64` constant beside the index is not a residue and needs
        // no premise of its own.
        assert!(element_delta_in_range_by_affine_arithmetic(
            &delta(index, 3),
            &start,
            &end,
            &PureFactContext::new(),
        ));
    }
}

/// The three assumption-carrying state comparisons decide whether two
/// states agree about one load. Their cell filter is
/// `PointerBlock::observable_by_load`; the filter on the `blocks` extent map
/// beside it was a block-name shortcut, `!block.starts_with("local:")`, which
/// dropped every local's extent from the comparison and never looked at the
/// retirement tombstones at all.
mod state_object_agreement {
    use super::*;
    use crate::kernel::primitives::{
        clear_never_address_taken_locals, set_never_address_taken_locals,
    };
    use crate::kernel::reasoning::memory_states_proven_equal_at_pointer;
    use std::collections::BTreeSet;

    /// A pointer the verifier cannot resolve to a named object: `&a` handed to
    /// a callee and returned is spelled like this, so it may designate the
    /// local whose extent the two states disagree about.
    fn unresolved_pointer() -> Pointer {
        Pointer {
            block: PointerBlock::Symbolic(Variable(94_100)),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn local_cell() -> Pointer {
        Pointer {
            block: PointerBlock::from("local:a"),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn hidden_cell() -> Pointer {
        Pointer {
            block: PointerBlock::from("local:unreachable"),
            offset: PointerOffsetTerm::Constant(0),
        }
    }

    fn agree(left: &Memory, right: &Memory) -> bool {
        memory_states_proven_equal_at_pointer(
            left,
            right,
            &unresolved_pointer(),
            &PureFactContext::new(),
        )
    }

    /// A local whose lifetime has ended in one state and not the other, and
    /// a local whose *cells* differ across the end: both are differences a
    /// load through a pointer that may designate it can see. The tombstone is
    /// the only record left once the cells are gone, and none of the four
    /// comparisons looked at it.
    #[test]
    fn a_local_a_load_may_reach_is_part_of_the_comparison() {
        clear_never_address_taken_locals();
        let bare = Memory::new().with_block("arg-memory", 32);
        let stored = bare
            .clone()
            .with_block("local:a", 8)
            .store(local_cell(), int32(5));
        let ended = stored.without_local_block(&PointerBlock::from("local:a"));
        assert!(!agree(&stored, &ended));
        assert!(!agree(&ended, &stored));
        // Only the tombstone tells these two apart: neither holds the block
        // or any of its cells.
        assert!(!agree(&bare, &ended));
        assert!(!agree(&ended, &bare));
    }

    /// The other polarity, and it has three parts. Declaring a block writes
    /// nothing, so an extent alone never decides a load — which is what
    /// `canonical_memory_for_pointer_load` says by keeping only the load's own
    /// block. A local whose address is never taken anywhere in the program is
    /// not memory any pointer value designates, so its retirement is invisible
    /// too. And a load that cannot reach the block at all is unaffected by
    /// either.
    #[test]
    fn what_a_load_cannot_reach_stays_out_of_the_comparison() {
        clear_never_address_taken_locals();
        let bare = Memory::new().with_block("arg-memory", 32);
        let declared = bare.clone().with_block("local:a", 8);
        assert!(agree(&bare, &declared));
        assert!(agree(&declared, &bare.clone().with_block("local:a", 16)));

        set_never_address_taken_locals(BTreeSet::from(["unreachable".to_string()]));
        let hidden = bare
            .clone()
            .with_block("local:unreachable", 8)
            .store(hidden_cell(), int32(5));
        let hidden_ended = hidden.without_local_block(&PointerBlock::from("local:unreachable"));
        assert!(agree(&bare, &hidden_ended));
        clear_never_address_taken_locals();

        // A load in a block the retired local is proven distinct from: an
        // `ExternalArgument` pointer is never one of this function's own
        // automatic objects.
        let stored = declared.store(local_cell(), int32(5));
        let ended = stored.without_local_block(&PointerBlock::from("local:a"));
        let argument = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        assert!(memory_states_proven_equal_at_pointer(
            &stored,
            &ended,
            &argument,
            &PureFactContext::new(),
        ));
    }
}

#[test]
fn wide_effect_does_not_frame_an_overlapping_narrow_load() {
    let write = Pointer {
        block: "wide-effect".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let read = Pointer {
        block: write.block.clone(),
        offset: PointerOffsetTerm::Constant(4),
    };
    crate::kernel::eval::declare_load_access_width(&read, 4);
    let before = Memory::new();
    let after = before.clone().store(write.clone(), int64(0));
    let assumptions = PureFactContext::new().assume_proposition(Proposition::MemoryMutatesOnly {
        before: before.clone(),
        after: after.clone(),
        writes: vec![(write, 8)],
    });
    assert!(!crate::kernel::search::ProofSearch::proves(
        &(assumptions),
        &Proposition::ConditionIs(
            ConditionTerm::equal(
                MachineTerm::MemoryLoad(
                    before.into(),
                    Box::new(read.clone()),
                    crate::kernel::LoadKind::Int32
                ),
                MachineTerm::MemoryLoad(
                    after.into(),
                    Box::new(read),
                    crate::kernel::LoadKind::Int32
                ),
            ),
            true
        )
    ));
}

#[test]
fn memory_resolution_requires_the_loaded_cell_width() {
    let stored = Pointer {
        block: "typed-cell".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let alias = Pointer {
        block: stored.block.clone(),
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(601_001)), 2),
    };
    let memory = Memory::new()
        .with_block("typed-cell", 8)
        .store(stored.clone(), uint16(7));
    let assumptions = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(alias.clone(), stored.clone()),
        true,
    );
    for pointer in [&stored, &alias] {
        assert_eq!(
            assumptions.resolve_memory_load_value(&memory, pointer, LoadKind::Int32),
            None
        );
        assert_eq!(
            assumptions.resolve_memory_load_value(&memory, pointer, LoadKind::UInt16),
            Some(uint16(7))
        );
    }
    let retained_state = crate::kernel::intern_memory(memory);
    let narrow = crate::kernel::eval::load_variable_for_exact_cell(
        &retained_state,
        &stored,
        crate::kernel::LoadKind::UInt16,
        2,
    );
    assert_eq!(
        assumptions.resolve_memory_load_term(&MachineTerm::Variable(narrow)),
        Some(MachineTerm::narrow_constant(MachineIntegerType::UInt16, 7))
    );
    // The shared load name conservatively widens when another access is
    // recorded; it can no longer resolve through the narrow stored cell.
    let wide = crate::kernel::eval::load_variable_for_exact_cell(
        &retained_state,
        &stored,
        crate::kernel::LoadKind::Int32,
        4,
    );
    assert_eq!(
        assumptions.resolve_memory_load_term(&MachineTerm::Variable(wide)),
        None
    );
}

/// Symbolic run lookup selects an exact slot through index/alias facts, keeps
/// an unknown alias unresolved, and respects holes and the stored width.
#[test]
fn symbolic_run_load_selection_checks_aliases_holes_and_width() {
    for count in [16, 256, 65_536] {
        let base = Pointer {
            block: "symbolic-run-resolution".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let index = MachineTerm::Variable(Variable(601_101));
        let read = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::scale_int32(index.clone(), 4),
        };
        let memory = Memory::new()
            .with_block("symbolic-run-resolution", count * 4)
            .with_constant_run(base.clone(), ProgramType::Int32, count, int32(9))
            .expect("a named scalar run is compact");
        let unknown = PureFactContext::new();
        assert_eq!(
            unknown.resolve_memory_load_value(&memory, &read, LoadKind::Int32),
            None
        );
        let exact = PureFactContext::new()
            .assume_condition(ConditionTerm::equal(index, MachineTerm::constant(3)), true);
        assert_eq!(
            exact.resolve_memory_load_value(&memory, &read, LoadKind::Int32),
            Some(int32(9))
        );
        assert_eq!(
            exact.resolve_memory_load_value(&memory, &read, LoadKind::UInt16),
            None
        );
        let alias = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(read.clone(), base.offset_by_bytes(12)),
            true,
        );
        assert_eq!(
            alias.resolve_memory_load_value(&memory, &read, LoadKind::Int32),
            Some(int32(9))
        );
        let other_base = Pointer {
            block: PointerBlock::Symbolic(Variable(601_102)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let base_alias = PureFactContext::new().assume_condition(
            ConditionTerm::pointer_equal(other_base.clone(), base.clone()),
            true,
        );
        assert_eq!(
            base_alias.resolve_memory_load_value(
                &memory,
                &other_base.offset_by_bytes(12),
                LoadKind::Int32,
            ),
            Some(int32(9))
        );
        let wide_index = MachineTerm::Variable(Variable(601_103));
        let wide_read = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::scale_int64(wide_index.clone(), 4, true),
        };
        let wide_exact = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_equal(wide_index.clone(), MachineTerm::uint64_constant(3)),
            true,
        );
        assert_eq!(
            wide_exact.resolve_memory_load_value(&memory, &wide_read, LoadKind::Int32),
            Some(int32(9))
        );
        let signed_read = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::scale_int64(wide_index.clone(), 4, false),
        };
        let signed_exact = PureFactContext::new().assume_condition(
            ConditionTerm::int64_equal(wide_index.clone(), MachineTerm::int64_constant(3)),
            true,
        );
        assert_eq!(
            signed_exact.resolve_memory_load_value(&memory, &signed_read, LoadKind::Int32),
            Some(int32(9))
        );
        let high_word = PureFactContext::new().assume_condition(
            ConditionTerm::uint64_equal(
                wide_index.clone(),
                MachineTerm::uint64_constant((1 << 32) + 3),
            ),
            true,
        );
        assert_eq!(
            high_word.resolve_memory_load_value(&memory, &wide_read, LoadKind::Int32),
            None
        );
        let low_word_only = PureFactContext::new().assume_condition(
            ConditionTerm::equal(wide_index, MachineTerm::constant(3)),
            true,
        );
        assert_eq!(
            low_word_only.resolve_memory_load_value(&memory, &wide_read, LoadKind::Int32),
            None
        );
        let changed = memory.store(base.offset_by_bytes(12), int32(7));
        assert_eq!(
            exact.resolve_memory_load_value(&changed, &read, LoadKind::Int32),
            Some(int32(7))
        );
        assert_eq!(
            alias.resolve_memory_load_value(&changed, &read, LoadKind::Int32),
            Some(int32(7))
        );
        assert_eq!(
            unknown.resolve_memory_load_value(&changed, &read, LoadKind::Int32),
            None
        );
    }
}

/// A store forgets every cached cell it might alias, and ownership keeps
/// only the cells a composition owns through a *different* member than the
/// written bytes. Two pointer parameters share the `ExternalArgument` block
/// and may alias unless something says otherwise; each context below says
/// less than that, and each must forget the cell. The last one says it, and
/// only it keeps the cell.
#[test]
fn a_store_through_one_parameter_forgets_another_unless_ownership_separates_them() {
    let parameter = |id: u64| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(id)), 4),
    };
    let p = parameter(98_001);
    let q = parameter(98_002);
    let q_field = q.offset_by_elements(MachineTerm::constant(1), 4);
    let memory = Memory::new().store(q_field.clone(), int32(5));
    let survives = |assumptions: &PureFactContext| {
        memory
            .clone()
            .without_possible_aliasing_cells(&p, 4, assumptions)
            .has_known_cell_at(&q_field)
    };
    let compose = |facts: Vec<ResourceFact>| {
        PureFactContext::new().assume_proposition(Proposition::ResourceComposition(
            facts
                .into_iter()
                .fold(ResourceContext::new(), ResourceContext::unchecked_with_fact),
        ))
    };

    assert!(
        !survives(&PureFactContext::new()),
        "two parameters with no distinctness known may alias"
    );
    // The written object is owned; the cached one is in no member.
    assert!(
        !survives(&compose(vec![
            own_memory_fact(p.clone(), 0, 2),
            own_memory_fact(parameter(98_003), 0, 2),
        ])),
        "a cell outside every owned member inherits nothing from the composition"
    );
    // An owner beside a view is not two owners: the view may observe the
    // owned bytes themselves.
    assert!(
        !survives(&compose(vec![
            own_memory_fact(p.clone(), 0, 2),
            view_memory_fact(q.clone(), 0, 2),
        ])),
        "a viewed object is not separated from an owned one"
    );
    // One member holding both addresses is no partition between them.
    let shared_member = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(98_004)), 4),
    };
    let i = MachineTerm::Variable(Variable(98_005));
    let j = MachineTerm::Variable(Variable(98_006));
    let element_i = shared_member.offset_by_elements(i.clone(), 4);
    let element_j = shared_member.offset_by_elements(j.clone(), 4);
    let in_bounds = compose(vec![own_memory_fact(
        shared_member.clone(),
        0,
        MachineTerm::Variable(Variable(98_007)),
    )])
    .assume_condition(
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), i.clone()),
        true,
    )
    .assume_condition(
        ConditionTerm::signed_less_equal(MachineTerm::constant(0), j.clone()),
        true,
    )
    .assume_condition(
        ConditionTerm::signed_less_than(i, MachineTerm::Variable(Variable(98_007))),
        true,
    )
    .assume_condition(
        ConditionTerm::signed_less_than(j, MachineTerm::Variable(Variable(98_007))),
        true,
    );
    assert!(
        !Memory::new()
            .store(element_j.clone(), int32(5))
            .without_possible_aliasing_cells(&element_i, 4, &in_bounds)
            .has_known_cell_at(&element_j),
        "two elements of one owned member may be the same element"
    );

    // Both objects owned, through two members: the partition keeps the cell.
    assert!(
        survives(&compose(vec![
            own_memory_fact(p.clone(), 0, 2),
            own_memory_fact(q.clone(), 0, 2),
        ])),
        "two owned members of one composition hold disjoint bytes"
    );
}

/// Ownership places a whole access, not its first element. Two owned
/// members split one object into words; an eight-byte cell that starts in
/// the lower word also covers the upper one, which the store writes, so no
/// member holds the cell and the partition says nothing about it.
#[test]
fn a_cell_straddling_two_owned_members_is_not_separated_from_either() {
    let object = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(98_101)), 4),
    };
    let upper = object.offset_by_elements(MachineTerm::constant(1), 4);
    let words = PureFactContext::new().assume_proposition(Proposition::ResourceComposition(
        [
            own_memory_fact(object.clone(), 0, 1),
            own_memory_fact(object.clone(), 1, 2),
        ]
        .into_iter()
        .fold(ResourceContext::new(), ResourceContext::unchecked_with_fact),
    ));
    let footprint = words.owned_store_footprint(&upper, 4);
    assert!(
        !words.access_owned_apart_from_store(&footprint, &upper, &object, 8),
        "an eight-byte access at the lower word reaches the upper word"
    );
    assert!(
        !Memory::new()
            .store(object.clone(), int64(9))
            .without_possible_aliasing_cells(&upper, 4, &words)
            .has_known_cell_at(&object),
        "the store forgets the straddling cell"
    );
    assert!(
        !words.access_owned_apart_from_store(&footprint, &upper, &object, 4),
        "automatic ownership selection declines a crowded base bucket"
    );
    assert!(
        Memory::new()
            .store(object.clone(), int32(9))
            .without_possible_aliasing_cells(&upper, 4, &words)
            .has_known_cell_at(&object),
        "the direct byte gap still keeps the nonoverlapping four-byte cell"
    );
    // Selecting one member per written base retains the complete-width check.
    let selected = PureFactContext::new().assume_proposition(Proposition::ResourceComposition(
        ResourceContext::new()
            .unchecked_with_fact(own_memory_fact(object.clone(), 0, 1))
            .unchecked_with_fact(own_memory_fact(upper.clone(), 0, 1)),
    ));
    let footprint = selected.owned_store_footprint(&upper, 4);
    assert!(selected.access_owned_apart_from_store(&footprint, &upper, &object, 4));
    assert!(!selected.access_owned_apart_from_store(&footprint, &upper, &object, 8));
}

#[test]
fn symbolic_zero_based_membership_requires_index_and_byte_extent_bounds() {
    let base = Pointer::symbolic(Variable(94_000));
    let index = MachineTerm::Variable(Variable(94_001));
    let end = MachineTerm::Variable(Variable(94_002));
    let pointer = base.offset_by_int32_elements(index.clone());
    let range = memory_range(base.clone(), 0, end.clone());
    let lower = ConditionTerm::signed_less_equal(0.into(), index.clone());
    let upper = ConditionTerm::signed_less_than(index.clone(), end.clone());
    let extent_lower = ConditionTerm::signed_less_equal(0.into(), end.clone());
    let extent_upper = ConditionTerm::signed_less_equal(end.clone(), 1_073_741_823.into());
    let bounds = [lower, upper, extent_lower, extent_upper];
    let context = |omit: Option<usize>| {
        bounds
            .iter()
            .enumerate()
            .filter(|(i, _)| Some(*i) != omit)
            .fold(PureFactContext::new(), |facts, (_, bound)| {
                facts.assume_condition(bound.clone(), true)
            })
    };
    let contains = |pointer: &Pointer, facts: &PureFactContext| {
        crate::kernel::assumptions::pointer_in_memory_range_shallow_with_facts(
            pointer, &range, facts,
        )
    };
    assert!(contains(&pointer, &context(None)));
    for omit in [0, 1, 3] {
        assert!(
            !contains(&pointer, &context(Some(omit))),
            "missing bound {omit}"
        );
    }
    assert!(
        !contains(&base.offset_by_int32_elements(end.clone()), &context(None)),
        "the upper endpoint is excluded"
    );
    assert!(
        !contains(
            &base.offset_by_int32_elements(u32::MAX.into()),
            &context(None)
        ),
        "negative indices are excluded"
    );
    assert!(
        !contains(&pointer.offset_by_int32_elements(1.into()), &context(None)),
        "a bound on k is not a bound on k+1"
    );
    assert!(
        !crate::kernel::assumptions::pointer_in_memory_range_shallow(&pointer, &range),
        "symbolic bounds require facts"
    );
}

/// A range of one-byte elements narrows by its endpoints as a range of wider
/// elements does: `loadable(a[0..n])` over `uint8`, whose extent is the
/// unscaled `n`, gives `loadable(a[0..k])` from `0 <= k` and `k <= n`, and
/// gives nothing without `k <= n`.
#[test]
fn a_byte_range_narrows_by_its_endpoints() {
    let memory = Memory::new();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(9_310_000)),
    };
    let n = MachineTerm::Variable(Variable(9_310_001));
    let k = MachineTerm::Variable(Variable(9_310_002));
    let held = PureFactContext::new()
        .assume_proposition(Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: n.clone(),
            wide: false,
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(MachineTerm::constant(0), k.clone()),
            true,
        );
    let bounded = held
        .clone()
        .assume_condition(ConditionTerm::signed_less_equal(k.clone(), n.clone()), true);
    assert!(bounded.proves_memory_loadable(&memory, &base, &k));
    assert!(!held.proves_memory_loadable(&memory, &base, &k));
}

mod loadable_extent_graph_tests {
    use super::*;

    fn var(id: u64) -> MachineTerm {
        MachineTerm::Variable(Variable(id))
    }

    fn extent(value: MachineTerm) -> MachineTerm {
        MachineTerm::add(value, MachineTerm::constant(1))
    }

    #[test]
    fn memory_resolution_and_range_reader_share_graph_extent_equality() {
        let memory = Memory::new();
        let base = Pointer::symbolic(Variable(9_320_000));
        let range_bytes = extent(var(9_320_001));
        let goal_bytes = extent(var(9_320_002));
        let fact = Proposition::MemoryLoadable {
            memory: memory.clone(),
            base: base.clone(),
            bytes: range_bytes.clone(),
            wide: false,
        };
        let premise = ConditionTerm::equal(var(9_320_001), var(9_320_002));
        let parent = PureFactContext::new().assume_proposition(fact);
        let branch = parent.clone().assume_condition(premise.clone(), true);
        let _scope = branch.enter_id_scope();

        PureFactContext::reset_bitvector_equality_index_fact_visits();
        assert!(branch.proves_memory_loadable_for_memory_resolution(&memory, &base, &goal_bytes));
        assert!(branch.proves_loadable_region_from_range(&base, &range_bytes, &base, &goal_bytes));
        assert_eq!(PureFactContext::bitvector_equality_index_fact_visits(), 0);
        assert!(!parent.proves_memory_loadable_for_memory_resolution(&memory, &base, &goal_bytes));
        assert!(!parent.proves_loadable_region_from_range(&base, &range_bytes, &base, &goal_bytes));
        let other = Pointer::symbolic(Variable(9_320_003));
        assert!(!branch.proves_memory_loadable_for_memory_resolution(&memory, &other, &goal_bytes));
    }

    #[cfg(test)]
    mod scaling_tests {
        include!(
            "../../scaling_tests/kernel/tests/memory_reasoning_tests/loadable_extent_graph_tests.rs"
        );
    }
}

#[test]
fn explicit_separation_frames_accesses_with_different_element_widths() {
    let field = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(97_700)),
    };
    let data = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::Variable(Variable(97_701)),
    };
    let n = MachineTerm::Variable(Variable(97_702));
    let i = MachineTerm::Variable(Variable(97_703));
    let field_range =
        MemoryRange::new_with_element_width(field.clone(), 0u32.into(), 1u32.into(), 8);
    let data_range = MemoryRange::new(data.clone(), 0u32.into(), n.clone());
    let facts = PureFactContext::new()
        .assume_proposition(Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(field_range.clone())),
            right: Box::new(Resource::Memory(data_range)),
        })
        .assume_condition(
            ConditionTerm::signed_less_equal(0u32.into(), i.clone()),
            true,
        )
        .assume_condition(ConditionTerm::signed_less_than(i.clone(), n), true);
    let cell = MemoryRange::new(data.offset_by_int32_elements(i), 0u32.into(), 1u32.into());
    assert!(
        facts.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &field_range,
            &cell
        )
    );
    // The same eight-byte field expressed as two int32 words is fully covered.
    let words = MemoryRange::new(field.clone(), 0u32.into(), 2u32.into());
    assert!(
        facts.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &words, &cell
        )
    );
    // Containment is of the complete access, not just its starting address.
    let beyond_field = MemoryRange::new(field, 0u32.into(), 3u32.into());
    assert!(
        !facts.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &beyond_field,
            &cell
        )
    );
}

#[test]
fn fixed_overlap_keeps_signed_widths_and_nonoverlap_authority() {
    let _session = crate::kernel::VerificationSession::enter();
    let base = Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(9_895_000)), 4),
    };
    let range = |start: i32, end: i32, width| {
        MemoryRange::new_with_element_width(
            base.clone(),
            MachineTerm::constant(start as u32),
            MachineTerm::constant(end as u32),
            width,
        )
    };
    let separation = |left: &MemoryRange, right: &MemoryRange| Proposition::ResourceSeparate {
        left: Box::new(Resource::Memory(left.clone())),
        right: Box::new(Resource::Memory(right.clone())),
    };
    for (left, right) in [
        (range(-1, 1, 8), range(-1, 0, 4)),
        (range(0, 1, 8), range(1, 2, 4)),
    ] {
        assert!(
            !PureFactContext::new()
                .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                    &left, &right
                )
        );
    }
    for (left, right) in [
        (range(0, 1, 8), range(2, 3, 4)),
        (range(-2, -1, 4), range(-1, 0, 4)),
        (range(0, 0, 4), range(0, 1, 4)),
    ] {
        let facts = PureFactContext::new().assume_proposition(separation(&left, &right));
        assert!(
            facts.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                &left, &right
            )
        );
    }
    let boundary = MachineTerm::Variable(Variable(9_895_001));
    let left = MemoryRange::new(base.clone(), 0u32.into(), boundary.clone());
    let right = MemoryRange::new(
        base,
        boundary.clone(),
        MachineTerm::add(boundary, 1u32.into()),
    );
    let facts = PureFactContext::new().assume_proposition(separation(&left, &right));
    assert!(
        facts.memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
            &left, &right
        )
    );
}

/// A warmed parameter partition is derived metadata, never authority: later
/// alias premises, changed cell widths, and withdrawn ownership must still
/// take the ordinary invalidation path.
#[test]
fn a_cached_parameter_partition_does_not_hide_aliases_or_wide_cells() {
    let parameter = |id| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(id)), 4),
    };
    let p = parameter(990_001);
    let q = parameter(990_002);
    let resources = ResourceContext::new()
        .unchecked_with_fact(own_memory_fact(p.clone(), 0, 1))
        .unchecked_with_fact(own_memory_fact(q.clone(), 0, 1));
    let assumptions = PureFactContext::new()
        .assume_proposition(Proposition::ResourceComposition(resources.clone()));
    let memory = Memory::new().store(q.clone(), int32(5));
    memory.prepare_parameter_store_partition(&resources);
    assert_eq!(
        memory
            .without_possible_aliasing_cells(&p, 4, &assumptions)
            .known_value(&q),
        Some(int32(5))
    );
    let alias = assumptions
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(p.clone(), q.clone()), true);
    assert!(
        !memory
            .without_possible_aliasing_cells(&p, 4, &alias)
            .has_known_cell_at(&q)
    );
    assert!(
        !memory
            .without_possible_aliasing_cells(&p, 4, &PureFactContext::new())
            .has_known_cell_at(&q)
    );
    // The changed cell no longer fits inside its four-byte owner.
    let widened = memory.clone().store(q.clone(), int64(9));
    let reference = crate::kernel::reasoning::store_gap::with_store_gap_skip_disabled(|| {
        widened.without_possible_aliasing_cells(&p, 4, &assumptions)
    });
    assert_eq!(
        widened
            .without_possible_aliasing_cells(&p, 4, &assumptions)
            .known_value(&q),
        reference.known_value(&q)
    );
    // A different resource state no longer owns the cached object.
    let less = PureFactContext::new().assume_proposition(Proposition::ResourceComposition(
        ResourceContext::new().unchecked_with_fact(own_memory_fact(p.clone(), 0, 1)),
    ));
    assert!(
        !memory
            .without_possible_aliasing_cells(&p, 4, &less)
            .has_known_cell_at(&q)
    );
}

/// Cross-block and full-width address copies can equate interior fields even
/// when no direct equality names the parameter bases. The object index must
/// bring the other object's cells back onto the ordinary store ladder.
#[test]
fn a_parameter_partition_follows_transitive_interior_address_aliases() {
    let parameter = |id| Pointer {
        block: PointerBlock::ExternalArgument,
        offset: PointerOffsetTerm::scale_int32(MachineTerm::Variable(Variable(id)), 4),
    };
    let p = parameter(991_001);
    let q = parameter(991_002);
    let foreign = Pointer::symbolic(Variable(991_003));
    let resources = ResourceContext::new()
        .unchecked_with_fact(own_memory_fact(p.clone(), 0, 4))
        .unchecked_with_fact(own_memory_fact(q.clone(), 0, 4));
    let original = PureFactContext::new()
        .assume_proposition(Proposition::ResourceComposition(resources.clone()));
    let memory = Memory::new().store(q.clone(), int32(5));
    memory.prepare_parameter_store_partition(&resources);
    let write = p.offset_by_bytes(8);
    for alias in [
        original
            .clone()
            .assume_condition(
                ConditionTerm::pointer_equal(write.clone(), foreign.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::pointer_equal(foreign.clone(), q.clone()),
                true,
            ),
        original.clone().assume_condition(
            ConditionTerm::uint64_equal(
                MachineTerm::PointerAddress(
                    Box::new(write.clone()),
                    crate::kernel::AddressObjectClass::NONE,
                ),
                MachineTerm::PointerAddress(
                    Box::new(q.clone()),
                    crate::kernel::AddressObjectClass::NONE,
                ),
            ),
            true,
        ),
    ] {
        let reference = crate::kernel::reasoning::store_gap::with_store_gap_skip_disabled(|| {
            memory.without_possible_aliasing_cells(&write, 4, &alias)
        });
        assert!(!reference.has_known_cell_at(&q));
        assert!(
            !memory
                .without_possible_aliasing_cells(&write, 4, &alias)
                .has_known_cell_at(&q)
        );
    }
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/kernel/tests/memory_reasoning_tests.rs");
}

/// Store separation reads the writer's current ownership: the observable
/// composition and any composition the store opened from a held folded
/// instance. A composition stated earlier on the path, and not held now,
/// separates nothing once the writer has stated its owners.
#[test]
fn store_separation_reads_the_store_owners_and_not_earlier_compositions() {
    let written = Pointer::symbolic(Variable(98_401));
    let other = Pointer::symbolic(Variable(98_402));
    let both = [
        own_memory_fact(written.clone(), 0, 1),
        own_memory_fact(other.clone(), 0, 1),
    ]
    .into_iter()
    .fold(ResourceContext::new(), ResourceContext::unchecked_with_fact);
    let writer_alone =
        ResourceContext::new().unchecked_with_fact(own_memory_fact(written.clone(), 0, 1));
    let separated = |context: &PureFactContext| {
        let footprint = context.owned_store_footprint(&written, 4);
        context.access_owned_apart_from_store(&footprint, &written, &other, 4)
    };
    let earlier =
        PureFactContext::new().assume_proposition(Proposition::ResourceComposition(both.clone()));
    assert!(
        separated(&earlier),
        "without owners every stated composition counts"
    );
    let owned_now = earlier.clone().with_store_owner(Some(writer_alone));
    assert!(
        !separated(&owned_now),
        "an earlier composition does not separate a store whose writer stated its owners"
    );
    assert!(
        separated(&owned_now.with_additional_store_owner(both)),
        "a composition the store opened from what it holds now separates"
    );
}

#[test]
fn stated_separation_decides_pointer_forms_with_scoped_nonempty_evidence() {
    for other_block in [
        PointerBlock::ExternalArgument,
        PointerBlock::Symbolic(Variable(940_001)),
    ] {
        let left = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Variable(Variable(940_002)),
        };
        let right = Pointer {
            block: other_block,
            offset: PointerOffsetTerm::Variable(Variable(940_003)),
        };
        let separation = |end: MachineTerm| Proposition::ResourceSeparate {
            left: Box::new(Resource::Memory(memory_range(left.clone(), 0, end.clone()))),
            right: Box::new(Resource::Memory(memory_range(right.clone(), 0, end))),
        };
        let comparison = ConditionTerm::pointer_equal(left.clone(), right.clone());
        assert!(matches!(comparison, ConditionTerm::PointerEqual(_, _)));
        let bare = PureFactContext::new();
        let fact = separation(1u32.into());
        let branch = bare.clone().assume_proposition(fact.clone());
        assert_eq!(branch.decide(&comparison), Some(false));
        let unequal = Proposition::ConditionIs(comparison.clone(), false);
        let equal = Proposition::ConditionIs(comparison.clone(), true);
        let (known, premises) = crate::kernel::assumptions::collect_reasoning_provenance(|| {
            crate::kernel::assumptions::capture_implicit_reasoning_provenance(|| {
                branch.contains_known(&unequal)
            })
        });
        assert!(known);
        assert_eq!(premises, vec![fact.clone()]);
        assert!(branch.contains_known(&Proposition::Not(Box::new(equal.clone()))));
        assert!(!branch.contains_known(&equal));
        assert!(!bare.contains_known(&unequal));
        assert_eq!(
            branch.decide(&ConditionTerm::pointer_equal(right.clone(), left.clone())),
            Some(false)
        );
        assert_eq!(bare.decide(&comparison), None);
        let rebuilt = {
            let mut branch = branch.clone();
            branch.rebuild_separated_anchor_offsets();
            branch
        };
        assert_eq!(rebuilt.decide_pointer_disequality(&comparison), Some(false));
        for end in [0u32.into(), MachineTerm::Variable(Variable(940_004))] {
            let unresolved = bare.clone().assume_proposition(separation(end));
            assert_eq!(unresolved.decide(&comparison), None);
            assert!(!unresolved.contains_known(&unequal));
        }
        if left.block != right.block {
            assert_eq!(
                branch.decide(&ConditionTerm::pointer_offset_equal(
                    left.offset.clone(),
                    right.offset.clone()
                )),
                None,
                "cross-block separation does not distinguish numerical offsets"
            );
        }
    }
}

#[test]
fn kept_call_frame_uses_transitive_model_pointer_classes() {
    let pointer = |id| Pointer {
        block: PointerBlock::Symbolic(Variable(id)),
        offset: PointerOffsetTerm::Constant(0),
    };
    let first = pointer(950_001);
    let middle = pointer(950_002);
    let owner = pointer(950_003);
    let first_link = PureFactContext::new().assume_condition(
        ConditionTerm::pointer_equal(first.clone(), middle.clone()),
        true,
    );
    let assumptions = first_link
        .clone()
        .assume_condition(ConditionTerm::pointer_equal(middle, owner.clone()), true);
    assert!(assumptions.pointers_known_equal(&first, &owner));
    let ranges = ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(
        ResourceFact::own_memory(MemoryRange::new(owner.clone(), 2u32.into(), 4u32.into())),
    );
    let access = first.offset_by_bytes(8);
    assert!(
        ranges
            .memory_write_range(&access, 8, &assumptions)
            .is_some()
    );
    let kept = crate::kernel::primitives::CallKeptRanges::new(ranges, Vec::new(), None);
    assert!(kept.holds_access(&access, 8, &assumptions));
    assert!(!kept.holds_access(&access, 16, &assumptions));
    for offset in [4, 12] {
        assert!(!kept.holds_access(&first.offset_by_bytes(offset), 8, &assumptions));
    }
    assert!(!kept.holds_access(&access, 8, &first_link));
    let views = ResourceContext::new_with_equalities(&assumptions).unchecked_with_fact(
        ResourceFact::view_memory(MemoryRange::new(owner, 2u32.into(), 4u32.into())),
    );
    let borrowed = crate::kernel::primitives::CallKeptRanges::new(views, Vec::new(), None);
    assert!(!borrowed.holds_access(&access, 8, &assumptions));
}

#[test]
fn kept_call_frame_with_loaded_owner_survives_equivalent_input_lineages() {
    let _session = crate::kernel::VerificationSession::enter();
    let address = Pointer::symbolic(Variable(953_001));
    let memory = Memory::new();
    let ProgramValue::Pointer(value) =
        memory.symbolic_pointer_load(&address, ProgramType::Int32Pointer)
    else {
        panic!("a typed pointer read");
    };
    let owner = value.pointer().clone();
    let queried = Pointer::symbolic(Variable(953_002));
    let middle = Pointer::symbolic(Variable(953_003));
    let inputs = || {
        PureFactContext::new()
            .assume_condition(
                ConditionTerm::pointer_equal(queried.clone(), middle.clone()),
                true,
            )
            .assume_condition(
                ConditionTerm::pointer_equal(middle.clone(), owner.clone()),
                true,
            )
    };
    let first = inputs();
    let recheck = inputs();
    let frame = |facts: &PureFactContext| {
        crate::kernel::primitives::CallKeptRanges::new(
            ResourceContext::new_with_equalities(facts).unchecked_with_fact(
                ResourceFact::own_memory(MemoryRange::new(owner.clone(), 4u32.into(), 6u32.into())),
            ),
            Vec::new(),
            None,
        )
    };
    let access = queried.offset_by_bytes(16);
    let kept = frame(&first);
    assert!(kept.holds_access(&access, 8, &first));
    assert!(frame(&recheck).holds_access(&access, 8, &recheck));
    assert!(
        kept.holds_access(&access, 8, &recheck),
        "equivalent stated inputs must not lose the recorded owner"
    );
    assert!(
        !kept.holds_access(&access, 8, &PureFactContext::new()),
        "retained class membership is not evidence in a weaker context"
    );
}

/// Separation queries the block-pair index cannot key scan the separation
/// facts, not every proposition fact. A miss between two symbolic ranges
/// of one block costs the same however many unrelated facts are held;
/// the old `prop_facts` scans grew with them.
#[test]
fn unkeyed_range_separation_ignores_unrelated_propositions() {
    let base = Pointer {
        block: "unkeyed-buffer".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let range_at = |variable| {
        let start = MachineTerm::Variable(Variable(variable));
        MemoryRange::new(
            base.clone(),
            start.clone(),
            MachineTerm::add(start, MachineTerm::constant(1)),
        )
    };
    let (left, right) = (range_at(93_200), range_at(93_201));
    let work = [16_u64, 64, 256]
        .into_iter()
        .map(|unrelated| {
            // Keep term-bridge imports cold at every sample size.
            crate::kernel::clear_integer_bridge_memo();
            let mut assumptions =
                PureFactContext::new().assume_proposition(Proposition::ResourceSeparate {
                    left: Box::new(Resource::Memory(range_at(93_202))),
                    right: Box::new(Resource::Memory(range_at(93_203))),
                });
            for index in 0..unrelated {
                let unrelated = Pointer {
                    block: format!("unrelated-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                };
                assumptions = assumptions.assume_proposition(Proposition::ResourceContains {
                    parent: Box::new(Resource::Memory(memory_range(unrelated.clone(), 0, 2))),
                    child: Box::new(Resource::Memory(memory_range(unrelated, 0, 1))),
                });
            }
            let (separate, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions
                    .memory_ranges_proven_disjoint_by_explicit_separation_for_memory_resolution(
                        &left, &right,
                    )
            });
            assert!(!separate);
            work
        })
        .collect::<Vec<_>>();
    assert!(work[0] > 0);
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated facts changed the separation miss's work: {work:?}"
    );
}

/// A separation over a token held inside a memory range is found from the
/// range's related blocks, not by scanning every separation: the token's
/// containers are walked upward, and a memory container reads the stated
/// separations filed under its base's blocks. Unrelated separations leave
/// the work of a hit and of a miss unchanged.
#[test]
fn a_token_inside_memory_finds_its_separation_without_scanning() {
    let _session = crate::kernel::VerificationSession::enter();
    let home = Pointer {
        block: "token-home".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let token = |name: &str| Resource::Token {
        name: name.into(),
        arguments: Vec::new().into(),
    };
    let work = [16_u64, 64, 256]
        .into_iter()
        .map(|unrelated| {
            // Keep term-bridge imports cold at every sample size.
            crate::kernel::clear_integer_bridge_memo();
            let mut assumptions = PureFactContext::new()
                .assume_proposition(Proposition::ResourceContains {
                    parent: Box::new(Resource::Memory(memory_range(home.clone(), 0, 4))),
                    child: Box::new(token("held")),
                })
                .assume_proposition(Proposition::ResourceSeparate {
                    left: Box::new(Resource::Memory(memory_range(home.clone(), 0, 8))),
                    right: Box::new(token("other")),
                });
            for index in 0..unrelated {
                let base = |side| Pointer {
                    block: format!("unrelated-separation-{index}-{side}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                };
                assumptions = assumptions.assume_proposition(Proposition::ResourceSeparate {
                    left: Box::new(Resource::Memory(memory_range(base(0), 0, 2))),
                    right: Box::new(Resource::Memory(memory_range(base(1), 0, 2))),
                });
            }
            let (separate, hit) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.proves_resource_separate(&token("held"), &token("other"))
            });
            assert!(
                separate,
                "the stated separation covers the token's container"
            );
            let (separate, miss) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.proves_resource_separate(&token("held"), &token("unrelated"))
            });
            assert!(!separate);
            (hit, miss)
        })
        .collect::<Vec<_>>();
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated separations changed the token separation's work: {work:?}"
    );
}

/// Memory state equality for a load matches memories up to the load's pointer,
/// so every effect fact is a candidate, but no other proposition fact is.
/// It once scanned every proposition fact; a miss now costs the same
/// however many unrelated facts are held.
#[test]
fn state_equality_ignores_unrelated_propositions() {
    let _session = crate::kernel::VerificationSession::enter();
    let target = Pointer {
        block: "retained_state-target".into(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let before = Memory::new()
        .store(
            target.clone(),
            ProgramValue::UInt32(MachineTerm::constant(1)),
        )
        .with_block("call-havoc:0", 0);
    let after = before.clone().with_block("call-havoc:1", 0);
    // The call may write the target itself, so the summary shows nothing.
    let summary = Proposition::MemoryEffectSummary {
        before: before.clone(),
        after: after.clone(),
        mutable_ranges: vec![memory_range(target.clone(), 0, 1)],
    };
    let work = [16_usize, 64, 256]
        .into_iter()
        .map(|unrelated| {
            let mut assumptions = PureFactContext::new().assume_proposition(summary.clone());
            for index in 0..unrelated {
                let unrelated = Pointer {
                    block: format!("retained_state-unrelated-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                };
                assumptions = assumptions.assume_proposition(Proposition::ResourceContains {
                    parent: Box::new(Resource::Memory(memory_range(unrelated.clone(), 0, 2))),
                    child: Box::new(Resource::Memory(memory_range(unrelated, 0, 1))),
                });
            }
            // The first query warms per-session caches; measure the second.
            assumptions.memory_states_directly_proven_equal_for_memory_resolution(
                &before, &after, &target,
            );
            let (equal, work) = crate::instrumentation::measure_deterministic_work(|| {
                assumptions.memory_states_directly_proven_equal_for_memory_resolution(
                    &before, &after, &target,
                )
            });
            assert!(!equal);
            work
        })
        .collect::<Vec<_>>();
    assert!(work[0] > 0);
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated facts changed the state equality miss's work: {work:?}"
    );
}

/// An existential obligation is certified from an assumed existential
/// alpha-equal to it, read from its identity bucket. It once scanned every
/// proposition fact, so its work grew with unrelated facts of other kinds
/// and existentials of other sorts.
#[test]
fn existential_obligation_ignores_unrelated_facts() {
    let existential = |var: u64, sort: Sort| Proposition::Exists {
        name: "witness".into(),
        var: Variable(var),
        sort,
        body: Box::new(Proposition::ConditionIs(
            ConditionTerm::signed_less_than(
                MachineTerm::Variable(Variable(var)),
                MachineTerm::constant(9),
            ),
            true,
        )),
    };
    let obligation = existential(97_001, Sort::ProgramInt32);
    let work = [16_u64, 64, 256]
        .into_iter()
        .map(|unrelated| {
            // Keep term-bridge imports cold at every sample size.
            crate::kernel::clear_integer_bridge_memo();
            let mut assumptions =
                PureFactContext::new().assume_proposition(existential(97_000, Sort::ProgramInt32));
            for index in 0..unrelated {
                let block = Pointer {
                    block: format!("existential-unrelated-{index}").into(),
                    offset: PointerOffsetTerm::Constant(0),
                };
                assumptions = assumptions
                    .assume_proposition(Proposition::ResourceContains {
                        parent: Box::new(Resource::Memory(memory_range(block.clone(), 0, 2))),
                        child: Box::new(Resource::Memory(memory_range(block, 0, 1))),
                    })
                    .assume_proposition(existential(97_100 + index, Sort::Bitvector32));
            }
            assumptions.build_stated_proposition_index();
            let (certified, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::api::certification_proves_exists_obligation_from_facts(
                    &assumptions,
                    &obligation,
                )
            });
            assert!(certified);
            work
        })
        .collect::<Vec<_>>();
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated facts changed the existential obligation's work: {work:?}"
    );
}

/// Loadability coverage reads the loadable facts filed under the goal's
/// block. It once scanned every proposition fact, so a miss's work grew with
/// unrelated loadable facts of other blocks.
#[test]
fn loadability_coverage_ignores_other_blocks() {
    let work = [16_usize, 64, 256]
        .into_iter()
        .map(|unrelated| {
            // Compare cold samples: retained literal initialization must not
            // be paid only by the first size in this independent-work test.
            let _session = crate::kernel::VerificationSession::enter();
            let memory = Memory::new();
            let base = Pointer {
                block: "coverage-target".into(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let goal = Proposition::MemoryLoadable {
                memory: memory.clone(),
                base: base.clone(),
                bytes: MachineTerm::constant(16),
                wide: false,
            };
            let mut assumptions =
                PureFactContext::new().assume_proposition(Proposition::MemoryLoadable {
                    memory: memory.clone(),
                    base: base.clone(),
                    bytes: MachineTerm::constant(8),
                    wide: false,
                });
            for index in 0..unrelated {
                assumptions = assumptions.assume_proposition(Proposition::MemoryLoadable {
                    memory: memory.clone(),
                    base: Pointer {
                        block: format!("coverage-unrelated-{index}").into(),
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    bytes: MachineTerm::constant(8),
                    wide: false,
                });
            }
            let (covered, work) = crate::instrumentation::measure_deterministic_work(|| {
                crate::kernel::api::loadable_covered_by_fact(&assumptions, &goal)
            });
            assert!(!covered, "an eight-byte fact does not cover sixteen bytes");
            work
        })
        .collect::<Vec<_>>();
    assert!(work[0] > 0);
    assert!(
        work.windows(2).all(|pair| pair[0] == pair[1]),
        "unrelated blocks changed the coverage check's work: {work:?}"
    );
}

#[test]
fn constant_byte_containment_checks_the_complete_child_span() {
    let base = Pointer {
        block: "byte-containment".into(),
        offset: PointerOffsetTerm::Variable(Variable(9_810_000)),
    };
    for (parent_width, parent_count, offset, child_width, expected) in [
        (8, 1, 7, 1, true),
        (8, 1, 8, 1, false),
        (8, 1, 7, 2, false),
        (4, 1, 0, 8, false),
        (4, 2, 0, 8, true),
    ] {
        let goal = Proposition::ResourceContains {
            parent: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                base.clone(),
                0u32.into(),
                MachineTerm::constant(parent_count),
                parent_width,
            ))),
            child: Box::new(Resource::Memory(MemoryRange::new_with_element_width(
                base.offset_by_bytes(offset),
                0u32.into(),
                1u32.into(),
                child_width,
            ))),
        };
        assert_eq!(
            crate::kernel::proof::fact_reasoning::normalizes_context_free_leaf(&goal),
            expected,
            "{goal:?}",
        );
    }
}
