use super::prelude::*;

pub fn int32(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::Int32(bits.into())
}

pub fn uint8(bits: impl Into<Bitvector32Term>) -> CValue {
    CValue::UInt8(bits.into())
}

pub(crate) fn canonical_c_memory_for_pointer_load(memory: &CMemory, pointer: &Pointer) -> CMemory {
    canonical_memory_for_pointer_load(memory, pointer)
}

/// Checks whether two resource spellings denote the same resource using only
/// exact facts and the bounded memory-resolution relation. This is intended
/// for certificate replay: it does not search for containment or separation.
pub(crate) fn c_resources_directly_match(
    left: &CResource,
    right: &CResource,
    assumptions: &Assumptions,
) -> bool {
    let values_match = |left: &CValue, right: &CValue| match (left, right) {
        (CValue::Int32(left), CValue::Int32(right))
        | (CValue::UInt8(left), CValue::UInt8(right)) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            pointers_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        _ => false,
    };
    match (left, right) {
        (CResource::Memory(left), CResource::Memory(right)) => {
            pointers_proven_equal_for_memory_resolution(left.base(), right.base(), assumptions)
                && bitvector_terms_proven_equal_for_memory_resolution(
                    left.start(),
                    right.start(),
                    assumptions,
                )
                && bitvector_terms_proven_equal_for_memory_resolution(
                    left.end(),
                    right.end(),
                    assumptions,
                )
        }
        (
            CResource::Composite {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Composite {
                name: right_name,
                arguments: right_arguments,
            },
        )
        | (
            CResource::Token {
                name: left_name,
                arguments: left_arguments,
            },
            CResource::Token {
                name: right_name,
                arguments: right_arguments,
            },
        ) => {
            left_name == right_name
                && left_arguments.len() == right_arguments.len()
                && left_arguments
                    .iter()
                    .zip(right_arguments)
                    .all(|(left, right)| values_match(left, right))
        }
        _ => false,
    }
}

pub(crate) fn c_memory_load_is_unchanged(
    before: &CMemory,
    after: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    if memories_match_for_pointer_load(before, after, pointer) {
        return true;
    }
    if memories_match_for_pointer_load_under_assumptions(before, after, pointer, assumptions) {
        return true;
    }
    // Predicate framing is deliberately bounded: use exact certified writes
    // and direct address cancellation, without invoking general alias search.
    if assumptions
        .prop_facts
        .iter()
        .any(|proposition| match proposition {
            Proposition::CMemoryMutatesOnly {
                before: effect_before,
                after: effect_after,
                pointers,
            } => {
                (effect_before == before
                    || memory_materializes_atomic_load(effect_before, before, pointer))
                    && effect_after == after
                    && pointers.iter().all(|write| {
                        write.blocks_proven_distinct(pointer)
                            || pointer_offsets_with_common_base_proven_distinct(
                                write,
                                pointer,
                                assumptions,
                            )
                            || pointers_proven_distinct_for_memory_resolution(
                                write,
                                pointer,
                                assumptions,
                            )
                            || pointer_byte_offset_from_base(write, pointer)
                                .and_then(|offset| offset.as_const())
                                .is_some_and(|offset| offset != 0)
                    })
            }
            Proposition::CMemoryEffectSummary {
                before: effect_before,
                after: effect_after,
                mutable_ranges,
            } => {
                let before_matches =
                    memory_matches_effect_summary_endpoint(effect_before, before, pointer);
                let after_matches =
                    memory_matches_effect_summary_endpoint(effect_after, after, pointer);
                before_matches
                    && after_matches
                    && assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
            }
            _ => false,
        })
    {
        return true;
    }
    false
}

fn c_memory_load_is_directly_unchanged(
    before: &CMemory,
    after: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    if memories_directly_match_for_pointer_load(before, after, pointer, assumptions) {
        return true;
    }
    assumptions
        .prop_facts
        .iter()
        .any(|proposition| match proposition {
            Proposition::CMemoryMutatesOnly {
                before: effect_before,
                after: effect_after,
                pointers,
            } => {
                (effect_before == before
                    || memory_materializes_atomic_load(effect_before, before, pointer))
                    && effect_after == after
                    && pointers.iter().all(|write| {
                        write.blocks_proven_distinct(pointer)
                            || pointer_offsets_with_common_base_proven_distinct(
                                write,
                                pointer,
                                assumptions,
                            )
                            || pointers_proven_distinct_for_memory_resolution(
                                write,
                                pointer,
                                assumptions,
                            )
                            || pointer_byte_offset_from_base(write, pointer)
                                .and_then(|offset| offset.as_const())
                                .is_some_and(|offset| offset != 0)
                    })
            }
            Proposition::CMemoryEffectSummary {
                before: effect_before,
                after: effect_after,
                mutable_ranges,
            } => {
                let before_matches = memories_directly_match_for_pointer_load(
                    effect_before,
                    before,
                    pointer,
                    assumptions,
                );
                let after_matches = before_matches
                    && memories_directly_match_for_pointer_load(
                        effect_after,
                        after,
                        pointer,
                        assumptions,
                    );
                let disjoint = after_matches
                    && assumptions.ranges_directly_disjoint_from_pointer(mutable_ranges, pointer);
                before_matches && after_matches && disjoint
            }
            _ => false,
        })
}

fn memories_directly_match_for_pointer_load(
    left: &CMemory,
    right: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    if memories_match_for_pointer_load(left, right, pointer) {
        return true;
    }
    if pointer.block.starts_with("local:")
        || !left
            .blocks
            .iter()
            .filter(|(block, _)| block.starts_with("havoc:") || block.starts_with("call-havoc:"))
            .eq(right.blocks.iter().filter(|(block, _)| {
                block.starts_with("havoc:") || block.starts_with("call-havoc:")
            }))
        || left.blocks.get(&pointer.block) != right.blocks.get(&pointer.block)
    {
        return false;
    }
    differing_cell_pointers_in_block(left, right, &pointer.block)
        .into_iter()
        .all(|cell| {
            cell.blocks_proven_distinct(pointer)
                || pointer_offsets_with_common_base_proven_distinct(&cell, pointer, assumptions)
                || pointers_proven_distinct_for_memory_resolution(&cell, pointer, assumptions)
                || pointer_byte_offset_from_base(&cell, pointer)
                    .and_then(|offset| offset.as_const())
                    .is_some_and(|offset| offset != 0)
                || assumptions.ranges_directly_disjoint_from_pointer(
                    &[CMemoryRange::new(
                        cell,
                        Bitvector32Term::Constant(0),
                        Bitvector32Term::Constant(1),
                    )],
                    pointer,
                )
        })
}

fn differing_cell_pointers_in_block(
    left: &CMemory,
    right: &CMemory,
    block: &PointerBlock,
) -> BTreeSet<Pointer> {
    left.cells
        .keys()
        .chain(right.cells.keys())
        .filter(|pointer| &pointer.block == block)
        .filter(|pointer| left.cells.get(*pointer) != right.cells.get(*pointer))
        .cloned()
        .collect()
}

fn memory_materializes_atomic_load(
    materialized: &CMemory,
    symbolic: &CMemory,
    pointer: &Pointer,
) -> bool {
    matches!(
        materialized.known_value(pointer),
        Some(CValue::Int32(Bitvector32Term::MemoryLoad(source, source_pointer))
            | CValue::UInt8(Bitvector32Term::MemoryLoad(source, source_pointer)))
            if source_pointer.as_ref() == pointer
                && memories_match_for_pointer_load(&source, symbolic, pointer)
    )
}

/// Certifies the narrow frame rule used by execution proofs for ordinary C
/// conditions. Address-dependent loads are transported from the inside out;
/// other proposition forms must be re-established explicitly.
pub(crate) fn prove_c_condition_fact_transport(
    fact: &Proposition,
    after: &CMemory,
    assumptions: &Assumptions,
) -> Option<Theorem> {
    prove_c_condition_fact_transport_with_assumptions(fact, after, Some((assumptions, false)))
}

pub(crate) fn prove_c_condition_fact_direct_transport(
    fact: &Proposition,
    after: &CMemory,
    assumptions: &Assumptions,
) -> Option<Theorem> {
    prove_c_condition_fact_transport_with_assumptions(fact, after, Some((assumptions, true)))
}

fn prove_c_condition_fact_transport_with_assumptions(
    fact: &Proposition,
    after: &CMemory,
    assumptions: Option<(&Assumptions, bool)>,
) -> Option<Theorem> {
    let Proposition::ConditionIs(condition, value) = fact else {
        return None;
    };
    let transported = transport_framed_atomic_condition(condition, after, assumptions)?;
    if &transported == condition {
        return None;
    }
    let conclusion = Proposition::ConditionIs(transported, *value);
    Some(Theorem::new(Proposition::Implies(
        Box::new(fact.clone()),
        Box::new(conclusion),
    )))
}

pub(crate) fn c_condition_fact_memories(fact: &Proposition) -> Vec<CMemory> {
    let Proposition::ConditionIs(condition, _) = fact else {
        return Vec::new();
    };
    let mut memories = Vec::new();
    collect_condition_memories(condition, &mut memories);
    memories
}

pub(crate) fn c_condition_fact_has_memory(fact: &Proposition) -> bool {
    fn bitvector_has_memory(term: &Bitvector32Term) -> bool {
        match term {
            Bitvector32Term::MemoryLoad(_, _) => true,
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::Remainder(left, right)
            | Bitvector32Term::ShiftLeft(left, right)
            | Bitvector32Term::ArithmeticShiftRight(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right)
            | Bitvector32Term::BitwiseXor(left, right) => {
                bitvector_has_memory(left) || bitvector_has_memory(right)
            }
            Bitvector32Term::BitwiseNot(term) => bitvector_has_memory(term),
            Bitvector32Term::If {
                then_term,
                else_term,
                ..
            } => bitvector_has_memory(then_term) || bitvector_has_memory(else_term),
            Bitvector32Term::RangeFold {
                start,
                end,
                initial,
                body,
                ..
            } => {
                bitvector_has_memory(start)
                    || bitvector_has_memory(end)
                    || bitvector_has_memory(initial)
                    || bitvector_has_memory(body)
            }
            Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => false,
        }
    }
    fn offset_has_memory(offset: &PointerOffsetTerm) -> bool {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                offset_has_memory(left) || offset_has_memory(right)
            }
            PointerOffsetTerm::Int32Scaled { value, .. } => bitvector_has_memory(value),
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => false,
        }
    }
    let Proposition::ConditionIs(condition, _) = fact else {
        return false;
    };
    match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            bitvector_has_memory(left) || bitvector_has_memory(right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            offset_has_memory(left) || offset_has_memory(right)
        }
        ConditionTerm::Constant(_)
        | ConditionTerm::Variable(_)
        | ConditionTerm::PointerEqual(_, _) => false,
    }
}

fn collect_condition_memories(condition: &ConditionTerm, memories: &mut Vec<CMemory>) {
    let mut collect_binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        collect_bitvector_memories(left, memories);
        collect_bitvector_memories(right, memories);
    };
    match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            collect_binary(left, right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            collect_pointer_offset_memories(left, memories);
            collect_pointer_offset_memories(right, memories);
        }
        ConditionTerm::Constant(_)
        | ConditionTerm::Variable(_)
        | ConditionTerm::PointerEqual(_, _) => {}
    }
}

fn collect_pointer_offset_memories(offset: &PointerOffsetTerm, memories: &mut Vec<CMemory>) {
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
        PointerOffsetTerm::Add(left, right) => {
            collect_pointer_offset_memories(left, memories);
            collect_pointer_offset_memories(right, memories);
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => collect_bitvector_memories(value, memories),
    }
}

fn collect_bitvector_memories(term: &Bitvector32Term, memories: &mut Vec<CMemory>) {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => {}
        Bitvector32Term::MemoryLoad(memory, _) => {
            if !memories.contains(memory) {
                memories.push(memory.as_ref().clone());
            }
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            collect_bitvector_memories(left, memories);
            collect_bitvector_memories(right, memories);
        }
        Bitvector32Term::BitwiseNot(term) => collect_bitvector_memories(term, memories),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            collect_condition_memories(condition, memories);
            collect_bitvector_memories(then_term, memories);
            collect_bitvector_memories(else_term, memories);
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_bitvector_memories(start, memories);
            collect_bitvector_memories(end, memories);
            collect_bitvector_memories(initial, memories);
            collect_bitvector_memories(body, memories);
        }
    }
}

fn transport_framed_atomic_condition(
    condition: &ConditionTerm,
    after: &CMemory,
    assumptions: Option<(&Assumptions, bool)>,
) -> Option<ConditionTerm> {
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        Some((
            transport_framed_atomic_bitvector(left, after, assumptions)?,
            transport_framed_atomic_bitvector(right, after, assumptions)?,
        ))
    };
    Some(match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_less_than(left, right)
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_less_equal(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_greater_than(left, right)
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::signed_greater_equal(left, right)
        }
        ConditionTerm::Bitvector32Equal(left, right) => {
            let (left, right) = binary(left, right)?;
            ConditionTerm::equal(left, right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => ConditionTerm::pointer_offset_equal(
            transport_framed_atomic_pointer_offset(left, after, assumptions)?,
            transport_framed_atomic_pointer_offset(right, after, assumptions)?,
        ),
        ConditionTerm::Constant(_)
        | ConditionTerm::Variable(_)
        | ConditionTerm::Bitvector32SignedAddOverflows(_, _)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(_, _)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(_, _)
        | ConditionTerm::Bitvector32SignedDivideOverflows(_, _)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, _)
        | ConditionTerm::PointerEqual(_, _) => return None,
    })
}

fn transport_framed_atomic_pointer_offset(
    offset: &PointerOffsetTerm,
    after: &CMemory,
    assumptions: Option<(&Assumptions, bool)>,
) -> Option<PointerOffsetTerm> {
    Some(match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
            transport_framed_atomic_pointer_offset(left, after, assumptions)?,
            transport_framed_atomic_pointer_offset(right, after, assumptions)?,
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::scale_int32(
            transport_framed_atomic_bitvector(value, after, assumptions)?,
            *byte_width,
        ),
    })
}

fn transport_framed_atomic_bitvector(
    term: &Bitvector32Term,
    after: &CMemory,
    assumptions: Option<(&Assumptions, bool)>,
) -> Option<Bitvector32Term> {
    Some(match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            let transported_pointer = Pointer {
                block: pointer.block.clone(),
                offset: transport_framed_atomic_pointer_offset(
                    &pointer.offset,
                    after,
                    assumptions,
                )?,
            };
            if memories_match_for_pointer_load(memory, after, pointer)
                || memory_materializes_atomic_load(after, memory, pointer)
                || assumptions.is_some_and(|(assumptions, direct)| {
                    if direct {
                        c_memory_load_is_directly_unchanged(memory, after, pointer, assumptions)
                    } else {
                        c_memory_load_is_unchanged(memory, after, pointer, assumptions)
                    }
                })
            {
                Bitvector32Term::MemoryLoad(Box::new(after.clone()), Box::new(transported_pointer))
            } else {
                term.clone()
            }
        }
        Bitvector32Term::Add(left, right) => Bitvector32Term::Add(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::Subtract(left, right) => Bitvector32Term::Subtract(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::Multiply(left, right) => Bitvector32Term::Multiply(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::Divide(left, right) => Bitvector32Term::Divide(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::Remainder(left, right) => Bitvector32Term::Remainder(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::ShiftLeft(left, right) => Bitvector32Term::ShiftLeft(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            Bitvector32Term::ArithmeticShiftRight(
                Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
                Box::new(transport_framed_atomic_bitvector(
                    right,
                    after,
                    assumptions,
                )?),
            )
        }
        Bitvector32Term::BitwiseAnd(left, right) => Bitvector32Term::BitwiseAnd(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::BitwiseOr(left, right) => Bitvector32Term::BitwiseOr(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::BitwiseXor(left, right) => Bitvector32Term::BitwiseXor(
            Box::new(transport_framed_atomic_bitvector(left, after, assumptions)?),
            Box::new(transport_framed_atomic_bitvector(
                right,
                after,
                assumptions,
            )?),
        ),
        Bitvector32Term::BitwiseNot(term) => Bitvector32Term::BitwiseNot(Box::new(
            transport_framed_atomic_bitvector(term, after, assumptions)?,
        )),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
            condition: Box::new(transport_framed_atomic_condition(
                condition,
                after,
                assumptions,
            )?),
            then_term: Box::new(transport_framed_atomic_bitvector(
                then_term,
                after,
                assumptions,
            )?),
            else_term: Box::new(transport_framed_atomic_bitvector(
                else_term,
                after,
                assumptions,
            )?),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Bitvector32Term::RangeFold {
            start: Box::new(transport_framed_atomic_bitvector(
                start,
                after,
                assumptions,
            )?),
            end: Box::new(transport_framed_atomic_bitvector(end, after, assumptions)?),
            initial: Box::new(transport_framed_atomic_bitvector(
                initial,
                after,
                assumptions,
            )?),
            accumulator: *accumulator,
            item: *item,
            body: Box::new(transport_framed_atomic_bitvector(body, after, assumptions)?),
        },
    })
}

pub(crate) fn c_pointer_offsets_proven_equal_for_effect(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &Assumptions,
) -> bool {
    let left = normalize_exact_memory_loads_in_pointer_offset(left, assumptions, 0);
    let right = normalize_exact_memory_loads_in_pointer_offset(right, assumptions, 0);
    left == right
        || assumptions.proves(&Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(left), Box::new(right)),
            true,
        ))
}

pub(super) fn normalize_exact_memory_loads_in_pointer_offset(
    offset: &PointerOffsetTerm,
    assumptions: &Assumptions,
    depth: usize,
) -> PointerOffsetTerm {
    if depth >= 64 {
        return offset.clone();
    }
    match offset {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => offset.clone(),
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::add(
            normalize_exact_memory_loads_in_pointer_offset(left, assumptions, depth + 1),
            normalize_exact_memory_loads_in_pointer_offset(right, assumptions, depth + 1),
        ),
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::scale_int32(
            normalize_exact_memory_loads_in_bitvector(value, assumptions, depth + 1),
            *byte_width,
        ),
    }
}

fn normalize_exact_memory_loads_in_bitvector(
    term: &Bitvector32Term,
    assumptions: &Assumptions,
    depth: usize,
) -> Bitvector32Term {
    if depth >= 64 {
        return term.clone();
    }
    let binary = |left: &Bitvector32Term, right: &Bitvector32Term| {
        (
            normalize_exact_memory_loads_in_bitvector(left, assumptions, depth + 1),
            normalize_exact_memory_loads_in_bitvector(right, assumptions, depth + 1),
        )
    };
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::Add(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::add(left, right)
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::subtract(left, right)
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::multiply(left, right)
        }
        Bitvector32Term::Divide(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::divide(left, right)
        }
        Bitvector32Term::Remainder(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::remainder(left, right)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::shift_left(left, right)
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::arithmetic_shift_right(left, right)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::bitwise_and(left, right)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::bitwise_or(left, right)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            let (left, right) = binary(left, right);
            Bitvector32Term::bitwise_xor(left, right)
        }
        Bitvector32Term::BitwiseNot(value) => Bitvector32Term::bitwise_not(
            normalize_exact_memory_loads_in_bitvector(value, assumptions, depth + 1),
        ),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => Bitvector32Term::If {
            condition: condition.clone(),
            then_term: Box::new(normalize_exact_memory_loads_in_bitvector(
                then_term,
                assumptions,
                depth + 1,
            )),
            else_term: Box::new(normalize_exact_memory_loads_in_bitvector(
                else_term,
                assumptions,
                depth + 1,
            )),
        },
        Bitvector32Term::RangeFold { .. } => term.clone(),
        Bitvector32Term::MemoryLoad(memory, pointer) => {
            if let Some(CValue::Int32(value)) = memory.known_value(pointer)
                && &value != term
            {
                return normalize_exact_memory_loads_in_bitvector(&value, assumptions, depth + 1);
            }
            let Some(value) = assumptions.resolve_memory_load_term(term) else {
                return term.clone();
            };
            normalize_exact_memory_loads_in_bitvector(&value, assumptions, depth + 1)
        }
    }
}

#[derive(Clone, Debug)]
pub struct CLoopPreservationContext {
    state: CState,
    loop_entry_state: CState,
    pure_facts: Vec<Proposition>,
}

impl CLoopPreservationContext {
    pub fn state(&self) -> &CState {
        &self.state
    }

    pub fn loop_entry_state(&self) -> &CState {
        &self.loop_entry_state
    }

    pub fn pure_facts(&self) -> &[Proposition] {
        &self.pure_facts
    }
}

#[allow(clippy::too_many_arguments)]
pub fn c_loop_preservation_contexts(
    loop_entry_state: &CState,
    condition: &CExpression,
    invariant_checks: &[CLoopInvariantCheck],
    effect_checks: &[CLoopEffectCheck],
    body: &CStatement,
    assumptions: &Assumptions,
) -> Result<Vec<CLoopPreservationContext>, String> {
    let mut budget = ExecutionBudget::default();
    let mut existing_variables = BTreeSet::new();
    collect_c_state_bitvector_variables(loop_entry_state, &mut existing_variables);
    collect_c_expression_bitvector_variables(condition, &mut existing_variables);
    for check in invariant_checks {
        collect_spec_proposition_bitvector_variables(check.proposition(), &mut existing_variables);
    }
    for check in effect_checks {
        collect_loop_effect_bitvector_variables(check.effect(), &mut existing_variables);
    }
    collect_c_statement_bitvector_variables(body, &mut existing_variables);
    collect_assumption_variables(assumptions, &mut existing_variables);
    let mut variables = VerificationVariableGenerator::fresh_for(
        budget.next_verification_variable,
        existing_variables,
    );
    let (top_state, whole_loop_effect_summaries) = prepare_loop_top_state(
        loop_entry_state,
        effect_checks,
        body,
        assumptions,
        &mut budget,
        &mut variables,
    )
    .map_err(|error| format!("could not prepare loop effects: {error:?}"))?;
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    let mut contexts = Vec::new();
    for (invariant_facts, invariant_obligations) in assume_invariant_checks(
        &top_state,
        loop_entry_state,
        invariant_checks,
        assumptions,
        &whole_loop_effect_facts,
        &[],
        &mut budget,
    )
    .map_err(|error| format!("could not assume loop invariants: {error:?}"))?
    {
        for (facts, obligations) in assume_condition_truthiness(
            &top_state,
            condition,
            assumptions,
            &invariant_facts,
            &invariant_obligations,
            true,
            &mut budget,
        )
        .map_err(|error| format!("could not assume the loop condition: {error:?}"))?
        {
            let context_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
            if let Some(obligation) = obligations
                .iter()
                .find(|obligation| !context_assumptions.proves(obligation.proposition()))
            {
                return Err(format!(
                    "missing loop-head prerequisite{}: {:?}",
                    obligation
                        .context()
                        .map(|context| format!(" ({context})"))
                        .unwrap_or_default(),
                    obligation.proposition()
                ));
            }
            let mut pure_facts = facts
                .into_iter()
                .map(|fact| fact.proposition().clone())
                .collect::<Vec<_>>();
            pure_facts.sort();
            pure_facts.dedup();
            contexts.push(CLoopPreservationContext {
                state: top_state.clone(),
                loop_entry_state: top_state.clone(),
                pure_facts,
            });
        }
    }
    Ok(contexts)
}

pub fn c_loop_invariants_hold_at_back_edge(
    state: &CState,
    iteration_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
) -> Result<(), String> {
    let obligations = c_loop_invariant_obligations_at_back_edge(
        state,
        iteration_entry_state,
        invariant_checks,
        assumptions,
    )?;
    if let Some(obligation) = obligations.first() {
        return Err(format!(
            "missing invariant fact{}: {:?}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default(),
            obligation.proposition()
        ));
    }
    Ok(())
}

pub fn c_loop_invariant_obligations_at_back_edge(
    state: &CState,
    iteration_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
) -> Result<Vec<ProofObligation>, String> {
    collect_invariant_check_obligations_without_search(
        state,
        iteration_entry_state,
        invariant_checks,
        InvariantPhase::Preservation,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower back-edge invariants: {error:?}"))
}

pub fn c_loop_invariants_hold_at_back_edge_using(
    state: &CState,
    iteration_entry_state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
) -> Result<(), String> {
    verify_invariant_checks_at_back_edge_using(
        state,
        iteration_entry_state,
        invariant_checks,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not replay invariant closer: {error}"))
}

pub fn c_loop_invariant_obligations_at_entry(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
) -> Result<Vec<ProofObligation>, String> {
    collect_invariant_check_obligations_without_search(
        state,
        state,
        invariant_checks,
        InvariantPhase::Entry,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower entry invariants: {error:?}"))
}

pub fn c_loop_effects_hold_at_back_edge(
    iteration_entry_state: &CState,
    state: &CState,
    effect_checks: &[CLoopEffectCheck],
    pure_facts: &[Proposition],
    assumptions: &Assumptions,
) -> Result<(), String> {
    let execution_facts = pure_facts
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    let obligations = collect_loop_effect_check_obligations(
        iteration_entry_state,
        state,
        effect_checks,
        &execution_facts,
        &[],
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower back-edge effects: {error:?}"))?;
    if let Some(obligation) = obligations.first() {
        return Err(format!(
            "missing loop effect fact{}: {:?}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default(),
            obligation.proposition()
        ));
    }
    Ok(())
}

pub fn c_loop_invariants_hold_at_entry(
    state: &CState,
    invariant_checks: &[CLoopInvariantCheck],
    assumptions: &Assumptions,
) -> Result<(), String> {
    let obligations = collect_invariant_check_obligations(
        state,
        state,
        invariant_checks,
        InvariantPhase::Entry,
        assumptions,
        &mut ExecutionBudget::default(),
    )
    .map_err(|error| format!("could not lower entry invariants: {error:?}"))?;
    if let Some(obligation) = obligations.first() {
        return Err(format!(
            "missing invariant fact{}: {:?}",
            obligation
                .context()
                .map(|context| format!(" ({context})"))
                .unwrap_or_default(),
            obligation.proposition()
        ));
    }
    Ok(())
}

/// Builds a branch-independent symbolic state for a proof join.
///
/// Locals that still equal a stable function-entry value retain that identity.
/// Other scalar and pointer locals become fresh symbolic values, and non-stack
/// memory is forgotten. Exported facts and resources constrain those values at
/// the abstract frontier.
pub fn abstract_c_state_for_join(
    state: &CState,
    stable_entry_locals: &BTreeMap<String, CValue>,
) -> Result<CState, String> {
    let mut existing_variables = BTreeSet::new();
    collect_c_state_bitvector_variables(state, &mut existing_variables);
    for value in stable_entry_locals.values() {
        collect_c_value_bitvector_variables(value, &mut existing_variables);
    }
    let mut variables = VerificationVariableGenerator::fresh_for(1_000_000, existing_variables);
    let mut abstract_state = state.clone();
    let mut abstract_objects = Vec::new();
    let mut preserved_blocks = BTreeSet::new();

    for (name, binding) in &state.locals.bindings {
        let CLocalBinding::Object { value, c_type } = binding else {
            continue;
        };
        let abstract_value = if stable_entry_locals.get(name) == Some(value) {
            value.clone()
        } else {
            match c_type {
                CType::Int32 => int32(Bitvector32Term::Variable(variables.next())),
                CType::UInt8 => uint8(Bitvector32Term::Variable(variables.next())),
                CType::Int32Pointer | CType::UInt8Pointer => {
                    CValue::Pointer(Pointer::symbolic(variables.next()))
                }
                CType::Int32Array(_) | CType::UInt8Array(_) => {
                    unreachable!("array objects use CLocalBinding::ArrayObject")
                }
            }
        };
        preserved_blocks.insert(CMemory::local_pointer(name).block);
        abstract_objects.push((name.clone(), abstract_value, *c_type));
    }

    abstract_state.memory = abstract_state
        .memory
        .with_loop_memory_havoc(variables.next(), &preserved_blocks);
    for (name, value, c_type) in abstract_objects {
        sync_stack_local(&mut abstract_state, &name, &value);
        abstract_state.locals.set_typed(name, value, c_type);
    }
    abstract_state.resources = ResourceContext::new();
    Ok(abstract_state)
}

pub fn c_variable(name: impl Into<String>) -> CExpression {
    CExpression::Variable(name.into())
}

pub fn c_addr_of(name: impl Into<String>) -> CExpression {
    CExpression::AddressOf(Box::new(c_variable(name)))
}

pub fn c_pointer_offset_bytes(pointer: CExpression, bytes: u32) -> CExpression {
    if bytes == 0 {
        pointer
    } else {
        CExpression::PointerOffsetBytes {
            pointer: Box::new(pointer),
            bytes,
        }
    }
}

pub fn c_int32_literal(value: u32) -> CExpression {
    CExpression::Value(int32(Bitvector32Term::Constant(value)))
}

pub fn c_uint8_literal(value: u8) -> CExpression {
    CExpression::Value(uint8(Bitvector32Term::Constant(u32::from(value))))
}

pub fn c_pointer_value(pointer: Pointer) -> CExpression {
    CExpression::Value(CValue::Pointer(pointer))
}

pub fn c_less_than(left: CExpression, right: CExpression) -> CExpression {
    CExpression::LessThan(Box::new(left), Box::new(right))
}

pub fn c_less_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::LessEqual(Box::new(left), Box::new(right))
}

pub fn c_greater_than(left: CExpression, right: CExpression) -> CExpression {
    CExpression::GreaterThan(Box::new(left), Box::new(right))
}

pub fn c_greater_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::GreaterEqual(Box::new(left), Box::new(right))
}

pub fn c_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Equal(Box::new(left), Box::new(right))
}

pub fn c_not_equal(left: CExpression, right: CExpression) -> CExpression {
    CExpression::NotEqual(Box::new(left), Box::new(right))
}

pub fn c_not(expression: CExpression) -> CExpression {
    CExpression::Not(Box::new(expression))
}

pub fn c_and(left: CExpression, right: CExpression) -> CExpression {
    CExpression::And(Box::new(left), Box::new(right))
}

pub fn c_or(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Or(Box::new(left), Box::new(right))
}

pub fn c_add(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Add(Box::new(left), Box::new(right))
}

pub fn c_subtract(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Subtract(Box::new(left), Box::new(right))
}

pub fn c_multiply(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Multiply(Box::new(left), Box::new(right))
}

pub fn c_divide(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Divide(Box::new(left), Box::new(right))
}

pub fn c_remainder(left: CExpression, right: CExpression) -> CExpression {
    CExpression::Remainder(Box::new(left), Box::new(right))
}

pub fn c_shift_left(left: CExpression, right: CExpression) -> CExpression {
    CExpression::ShiftLeft(Box::new(left), Box::new(right))
}

pub fn c_shift_right(left: CExpression, right: CExpression) -> CExpression {
    CExpression::ShiftRight(Box::new(left), Box::new(right))
}

pub fn c_bitwise_and(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseAnd(Box::new(left), Box::new(right))
}

pub fn c_bitwise_or(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseOr(Box::new(left), Box::new(right))
}

pub fn c_bitwise_xor(left: CExpression, right: CExpression) -> CExpression {
    CExpression::BitwiseXor(Box::new(left), Box::new(right))
}

pub fn c_bitwise_not(expression: CExpression) -> CExpression {
    CExpression::BitwiseNot(Box::new(expression))
}

pub fn c_load(pointer: CExpression) -> CExpression {
    CExpression::Load(Box::new(pointer))
}

pub fn c_typed_load(pointer: CExpression, value_type: CType) -> CExpression {
    CExpression::TypedLoad {
        pointer: Box::new(pointer),
        value_type,
    }
}

pub fn c_index(base: CExpression, index: CExpression) -> CExpression {
    CExpression::Index(Box::new(base), Box::new(index))
}

pub fn c_assign(name: impl Into<String>, expression: CExpression) -> CStatement {
    CStatement::Assign {
        name: name.into(),
        expression,
    }
}

pub fn c_call_assign(
    target: impl Into<String>,
    function_name: impl Into<String>,
    arguments: Vec<CExpression>,
) -> CStatement {
    CStatement::CallAssign {
        target: target.into(),
        function_name: function_name.into(),
        arguments,
    }
}

pub fn c_declare(name: impl Into<String>, c_type: CType) -> CStatement {
    CStatement::Declare {
        name: name.into(),
        c_type,
    }
}

pub fn c_assert(condition: CExpression) -> CStatement {
    CStatement::Assert {
        condition,
        label: None,
    }
}

pub fn c_labeled_assert(condition: CExpression, label: impl Into<String>) -> CStatement {
    CStatement::Assert {
        condition,
        label: Some(label.into()),
    }
}

pub fn c_seq(first: CStatement, second: CStatement) -> CStatement {
    CStatement::Seq(Box::new(first), Box::new(second))
}

pub fn c_skip() -> CStatement {
    CStatement::Skip
}

pub fn c_return(expression: CExpression) -> CStatement {
    CStatement::Return(expression)
}

pub fn c_store(pointer: CExpression, value: CExpression) -> CStatement {
    CStatement::Store { pointer, value }
}

pub fn c_typed_store(pointer: CExpression, value: CExpression, value_type: CType) -> CStatement {
    CStatement::TypedStore {
        pointer,
        value,
        value_type,
    }
}

pub fn c_if(
    condition: CExpression,
    then_branch: CStatement,
    else_branch: CStatement,
) -> CStatement {
    CStatement::If {
        condition,
        then_branch: Box::new(then_branch),
        else_branch: Box::new(else_branch),
    }
}

pub fn c_while(
    condition: CExpression,
    invariant: Vec<Proposition>,
    body: CStatement,
) -> CStatement {
    c_while_with_invariant_and_effect_checks(condition, invariant, Vec::new(), Vec::new(), body)
}

pub fn c_while_with_invariant_checks(
    condition: CExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<CLoopInvariantCheck>,
    body: CStatement,
) -> CStatement {
    c_while_with_invariant_and_effect_checks(
        condition,
        invariant,
        invariant_checks,
        Vec::new(),
        body,
    )
}

pub fn c_while_with_invariant_and_effect_checks(
    condition: CExpression,
    invariant: Vec<Proposition>,
    invariant_checks: Vec<CLoopInvariantCheck>,
    effect_checks: Vec<CLoopEffectCheck>,
    body: CStatement,
) -> CStatement {
    CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body: Box::new(body),
    }
}

pub fn c_parameter(name: impl Into<String>, c_type: CType) -> CParameter {
    CParameter::new(name, c_type)
}

pub fn c_function(
    return_type: CType,
    name: impl Into<String>,
    parameters: Vec<CParameter>,
    body: CStatement,
) -> CFunction {
    CFunction::new(return_type, name, parameters, body)
}

pub fn c_function_entry_state(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
) -> Option<CState> {
    let values = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()?;
    bind_c_function_arguments(caller_state, function, &values)
}

/// Produces the exact callee entry state used by contract verification.
///
/// In particular, composite resource requirements are expanded to their
/// canonical contained resources. Proof replay and independent whole-function
/// certification must use this same boundary state when certifying reusable
/// rules.
pub fn c_function_contract_entry_state(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    assumptions: &Assumptions,
) -> Result<CState, String> {
    let values = arguments
        .iter()
        .map(|argument| match argument {
            CExpression::Value(value) => Some(value.clone()),
            _ => None,
        })
        .collect::<Option<Vec<_>>>()
        .ok_or_else(|| "contract entry arguments must be concrete symbolic values".to_string())?;
    let mut budget = ExecutionBudget::default();
    match prepare_function_contract_entry_state_with_values(
        caller_state,
        function,
        &values,
        assumptions,
        &mut budget,
    ) {
        Ok(Ok(state)) => Ok(state),
        Ok(Err(error)) => Err(format!("could not prepare contract resources: {error:?}")),
        Err(limit) => Err(format!(
            "contract resource preparation hit execution limit {limit:?}"
        )),
    }
}

pub fn c_function_outcome_from_statement_outcome(
    caller_state: &CState,
    function: &CFunction,
    outcome: CStatementOutcome,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> (CFunctionOutcome, Vec<ProofObligation>) {
    function_outcome_from_body(
        caller_state,
        function,
        outcome,
        obligations,
        assumptions,
        None,
    )
}

pub fn c_function_specification(
    state: CState,
    arguments: Vec<CExpression>,
    requires: Vec<Proposition>,
    outcome: CFunctionOutcome,
) -> CFunctionSpecification {
    CFunctionSpecification::new(state, arguments, requires, outcome)
}

pub fn proposition_and(left: Proposition, right: Proposition) -> Proposition {
    Proposition::And(Box::new(left), Box::new(right))
}

pub fn proposition_and_all(mut propositions: Vec<Proposition>) -> Proposition {
    let Some(first) = propositions.pop() else {
        return Proposition::ConditionIs(ConditionTerm::Constant(true), true);
    };

    propositions
        .into_iter()
        .rev()
        .fold(first, |right, left| proposition_and(left, right))
}

/// Expands C expression definedness into the exact pure proposition under
/// which evaluation reaches a value rather than undefined behavior.
pub fn c_expression_definedness_proposition(
    state: &CState,
    expression: &CExpression,
) -> Result<Proposition, ExecutionLimit> {
    let paths = evaluate_c_expression_paths(
        state,
        expression,
        &Assumptions::new(),
        &mut ExecutionBudget::default(),
    )?;
    let mut normal_paths = paths.into_iter().filter_map(|path| {
        if !matches!(path.outcome, CExpressionOutcome::Value(_)) {
            return None;
        }
        Some(proposition_and_all(
            path.facts
                .into_iter()
                .map(|fact| fact.proposition().clone())
                .chain(
                    path.obligations
                        .into_iter()
                        .map(|obligation| obligation.proposition().clone()),
                )
                .collect(),
        ))
    });
    let Some(first) = normal_paths.next() else {
        return Ok(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        ));
    };
    Ok(normal_paths.fold(first, |left, right| {
        Proposition::Or(Box::new(left), Box::new(right))
    }))
}

pub fn substitute_int32_variable_in_proposition(
    proposition: &Proposition,
    variable: Variable,
    value: Bitvector32Term,
) -> Proposition {
    substitute_bitvector_variable_in_proposition(proposition, variable, &value)
}

pub fn c_max_body() -> CStatement {
    c_if(
        c_less_than(c_variable("a"), c_variable("b")),
        c_return(c_variable("b")),
        c_return(c_variable("a")),
    )
}

pub fn c_max_function() -> CFunction {
    c_function(
        CType::Int32,
        "max",
        vec![
            c_parameter("a", CType::Int32),
            c_parameter("b", CType::Int32),
        ],
        c_max_body(),
    )
}

pub fn c_max_environment(a: CValue, b: CValue) -> CLocalEnvironment {
    CLocalEnvironment::new().with("a", a).with("b", b)
}

pub fn c_max_state(a: CValue, b: CValue) -> CState {
    CState::new().with_local("a", a).with_local("b", b)
}

pub fn c_max_lt_condition(a: Bitvector32Term, b: Bitvector32Term) -> ConditionTerm {
    ConditionTerm::signed_less_than(a, b)
}

pub fn prove_c_expression_evaluation(state: CState, expression: CExpression) -> Option<Theorem> {
    let outcome = evaluate_c_expression(
        &state,
        &expression,
        &Assumptions::new(),
        &mut ExecutionBudget::default(),
    )?;
    Some(Theorem::new(Proposition::CExpressionEvaluates {
        state,
        expression,
        outcome,
    }))
}

pub fn prove_symbolic_c_condition_evaluation(
    state: CState,
    condition: CExpression,
    assumptions: Assumptions,
) -> SymbolicCConditionEvaluation {
    let mut budget = ExecutionBudget::default();
    let expression_paths =
        match evaluate_c_expression_paths(&state, &condition, &assumptions, &mut budget) {
            Ok(paths) => paths,
            Err(limit) => {
                return SymbolicCConditionEvaluation {
                    paths: Vec::new(),
                    limit: Some(limit),
                };
            }
        };
    let mut outcomes = Vec::new();
    for path in expression_paths {
        match path.outcome {
            CExpressionOutcome::Value(value) => {
                outcomes.extend(
                    c_truthiness_paths(value, path.facts, path.obligations, &assumptions)
                        .into_iter()
                        .map(|path| {
                            (
                                CConditionOutcome::Value(path.is_true),
                                path.facts,
                                path.obligations,
                            )
                        }),
                );
            }
            CExpressionOutcome::UndefinedBehavior(kind) => outcomes.push((
                CConditionOutcome::UndefinedBehavior(kind),
                path.facts,
                path.obligations,
            )),
            CExpressionOutcome::RuntimeError(error) => outcomes.push((
                CConditionOutcome::RuntimeError(error),
                path.facts,
                path.obligations,
            )),
        }
    }
    let paths = outcomes
        .into_iter()
        .map(|(outcome, facts, obligations)| {
            let facts = public_execution_pure_facts(&facts);
            let proposition = Proposition::CConditionEvaluates {
                state: state.clone(),
                condition: condition.clone(),
                outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &obligations,
            ));
            SymbolicCConditionEvaluationPath {
                facts,
                obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCConditionEvaluation { paths, limit: None }
}

pub fn prove_c_statement_execution(state: CState, statement: CStatement) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, Assumptions::new())
}

pub fn prove_c_statement_execution_under_assumptions(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_execution(state, statement, assumptions)
}

pub fn prove_symbolic_c_execution(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_budget(
        state,
        statement,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_with_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_execution_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    prove_symbolic_c_execution_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_with_environment_and_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        budget,
    );
    if execution.limit().is_some() {
        return None;
    }
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_execution_paths(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_budget(
        state,
        statement,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_paths_with_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_execution_paths_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_execution_paths_with_environment_and_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_execution_paths_with_environment_and_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
) -> SymbolicCExecution {
    let paths = match execute_c_statement_paths(
        &state,
        &statement,
        &assumptions,
        &environment,
        execution_semantics,
        &mut budget,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = Proposition::CStatementExecutes {
                state: state.clone(),
                statement: statement.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_symbolic_c_statement_verification_paths_with_environment(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
    )
    .0
}

pub fn prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut budget = ExecutionBudget::default();
    prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
        state,
        statement,
        assumptions,
        environment,
        execution_semantics,
        &mut budget,
    )
}

fn statement_verification_variables(
    lower_bound: u64,
    state: &CState,
    statement: &CStatement,
    assumptions: &Assumptions,
    environment: &CExecutionEnvironment,
) -> VerificationVariableGenerator {
    let mut existing = BTreeSet::new();
    collect_c_state_bitvector_variables(state, &mut existing);
    collect_c_statement_bitvector_variables(statement, &mut existing);
    collect_assumption_variables(assumptions, &mut existing);
    collect_execution_environment_variables(environment, &mut existing);
    VerificationVariableGenerator::fresh_for(lower_bound, existing)
}

pub(crate) fn prove_symbolic_c_statement_verification_paths_with_environment_and_loop_rule_using_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut variables = statement_verification_variables(
        budget.next_verification_variable,
        &state,
        &statement,
        &assumptions,
        &environment,
    );
    let execution = execute_c_statement_verification_paths(
        &state,
        &statement,
        &assumptions,
        &environment,
        execution_semantics,
        budget,
        &mut variables,
    );
    budget.next_verification_variable = budget.next_verification_variable.max(variables.next);
    let paths = match execution {
        Ok(paths) => paths,
        Err(limit) => {
            return (
                SymbolicCExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
                None,
            );
        }
    };
    symbolic_c_statement_execution_with_loop_rule(state, statement, assumptions, paths)
}

#[cfg(test)]
pub(crate) fn prove_symbolic_c_loop_exit_with_proven_phases(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let mut budget = ExecutionBudget::default();
    prove_symbolic_c_loop_exit_with_proven_phases_using_budget(
        state,
        statement,
        assumptions,
        environment,
        initialization_proven,
        preservation_proven,
        &mut budget,
    )
}

pub(crate) fn prove_symbolic_c_loop_exit_with_proven_phases_using_budget(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    initialization_proven: bool,
    preservation_proven: bool,
    budget: &mut ExecutionBudget,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let CStatement::While {
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body,
    } = &statement
    else {
        return (
            SymbolicCExecution {
                paths: Vec::new(),
                limit: None,
            },
            None,
        );
    };
    let mut variables = statement_verification_variables(
        budget.next_verification_variable,
        &state,
        &statement,
        &assumptions,
        &environment,
    );
    let execution = execute_c_while_exit_paths_with_proven_phases(
        &state,
        condition,
        invariant,
        invariant_checks,
        effect_checks,
        body,
        &assumptions,
        &environment,
        CExecutionSemantics::APPLY_VERIFIED_RULES,
        initialization_proven,
        preservation_proven,
        budget,
        &mut variables,
    );
    budget.next_verification_variable = budget.next_verification_variable.max(variables.next);
    let paths = match execution {
        Ok(paths) => paths,
        Err(limit) => {
            return (
                SymbolicCExecution {
                    paths: Vec::new(),
                    limit: Some(limit),
                },
                None,
            );
        }
    };
    symbolic_c_statement_execution_with_loop_rule(state, statement, assumptions, paths)
}

fn symbolic_c_statement_execution_with_loop_rule(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    paths: Vec<CStatementExecutionPath>,
) -> (SymbolicCExecution, Option<CVerifiedLoopRule>) {
    let loop_rule = (matches!(statement, CStatement::While { .. })
        && paths.iter().all(|path| {
            matches!(path.outcome, CStatementOutcome::Normal(_))
                && path.obligations.iter().all(ProofObligation::is_assumable)
        }))
    .then(|| CVerifiedLoopRule {
        symbolic_entry_state: state.clone(),
        loop_statement: statement.clone(),
        required_assumptions: assumptions.clone(),
        paths: paths.clone(),
    });
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = Proposition::CStatementExecutes {
                state: state.clone(),
                statement: statement.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    (SymbolicCExecution { paths, limit: None }, loop_rule)
}

pub fn prove_symbolic_c_function_execution(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_budget(
        state,
        function,
        arguments,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_with_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    prove_symbolic_c_function_execution_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> Option<Theorem> {
    let execution = prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
    );
    if execution.limit().is_some() {
        return None;
    }
    let mut paths = execution.paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.theorem)
}

pub fn prove_symbolic_c_function_execution_paths(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_budget(
        state,
        function,
        arguments,
        assumptions,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        budget,
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_execution_paths_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_execution_paths_with_environment_and_budget_mode(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        false,
    )
}

#[allow(clippy::too_many_arguments)]
fn prove_symbolic_c_function_execution_paths_with_environment_and_budget_mode(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
    prepare_contract_resources: bool,
) -> SymbolicCExecution {
    let paths = match execute_c_function_paths_with_contract_resources(
        &state,
        &function,
        &arguments,
        &assumptions,
        &environment,
        execution_semantics,
        &mut budget,
        prepare_contract_resources,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = Proposition::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                arguments: arguments.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn prove_symbolic_c_function_verification_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths_with_environment_and_budget(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
    )
}

pub fn prove_symbolic_c_function_verification_paths_with_environment_and_budget(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: ExecutionBudget,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        budget,
        false,
    )
}

/// Verifies an exact function body from its declared contract-entry resources.
///
/// Unlike ordinary proof replay, this canonicalizes composite requirements
/// before body execution. It is the independent execution used to certify
/// opaque contract claims.
pub fn prove_symbolic_c_function_contract_verification_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> SymbolicCExecution {
    prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
        state,
        function,
        arguments,
        assumptions,
        environment,
        execution_semantics,
        ExecutionBudget::default(),
        true,
    )
}

/// Produces the only execution frontier accepted for opaque contract
/// certification.
///
/// The initial assumptions are derived inside the kernel solely from the
/// function's exact contract and resource entry state. Callers cannot inject
/// additional hypotheses.
pub fn prove_c_function_contract_execution_paths_with_environment(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    derived_entry_facts: Vec<Proposition>,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mode: CFunctionContractExecutionMode,
) -> CFunctionContractExecution {
    let selection_assumptions =
        assumptions_with_propositions(&Assumptions::new(), &derived_entry_facts);
    let execution = match c_function_contract_certification_assumptions(
        &state,
        &function,
        &arguments,
        Assumptions::new(),
        &selection_assumptions,
    ) {
        Some(mut assumptions) => {
            let Some(mut entry_state) = c_function_entry_state(&state, &function, &arguments)
            else {
                return CFunctionContractExecution {
                    execution: SymbolicCExecution {
                        paths: Vec::new(),
                        limit: None,
                    },
                };
            };
            let Some(entry_resources) = expand_all_composite_resource_facts(
                entry_state.resources(),
                function.composite_resource_definitions(),
                entry_state.memory(),
                &assumptions,
            ) else {
                return CFunctionContractExecution {
                    execution: SymbolicCExecution {
                        paths: Vec::new(),
                        limit: None,
                    },
                };
            };
            entry_state.resources = entry_resources.clone();
            for fact in derived_entry_facts {
                if certification_proves_proposition(&assumptions, &fact)
                    || resources_certify_loadability(
                        &entry_state,
                        &entry_resources,
                        &fact,
                        &assumptions,
                    )
                {
                    assumptions = assumptions.assume_proposition(fact);
                }
            }
            match mode {
                CFunctionContractExecutionMode::VerifyLoops => {
                    prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
                        state,
                        function,
                        arguments,
                        assumptions,
                        environment,
                        execution_semantics,
                        ExecutionBudget::default(),
                        true,
                    )
                }
                CFunctionContractExecutionMode::ExecuteLoops => {
                    prove_symbolic_c_function_execution_paths_with_environment_and_budget_mode(
                        state,
                        function,
                        arguments,
                        assumptions,
                        environment,
                        execution_semantics,
                        ExecutionBudget::default(),
                        true,
                    )
                }
            }
        }
        None => SymbolicCExecution {
            paths: Vec::new(),
            limit: None,
        },
    };
    CFunctionContractExecution { execution }
}

fn c_function_contract_certification_assumptions(
    caller_state: &CState,
    function: &CFunction,
    arguments: &[CExpression],
    mut assumptions: Assumptions,
    selection_assumptions: &Assumptions,
) -> Option<Assumptions> {
    let mut entry_state = c_function_entry_state(caller_state, function, arguments)?;
    let mut budget = ExecutionBudget::default();
    for requirement in function.contract_requires() {
        let paths = lower_spec_proposition_at_state_with_loop_entry(
            &entry_state,
            requirement,
            None,
            &assumptions,
            &mut budget,
        )
        .ok()?;
        let path = if let [path] = paths.as_slice() {
            path
        } else {
            let selection_context =
                assumptions_with_propositions(&assumptions, &selection_assumptions.pure_facts());
            let proposition_matches = paths
                .iter()
                .filter(|path| {
                    certification_proves_proposition(&selection_context, &path.proposition)
                })
                .collect::<Vec<_>>();
            if let [path] = proposition_matches.as_slice() {
                *path
            } else {
                let consistent = paths
                    .iter()
                    .filter(|path| {
                        !assumptions_with_propositions(
                            &selection_context,
                            &path
                                .facts
                                .iter()
                                .map(|fact| fact.proposition().clone())
                                .collect::<Vec<_>>(),
                        )
                        .is_inconsistent()
                    })
                    .collect::<Vec<_>>();
                let [path] = consistent.as_slice() else {
                    return None;
                };
                *path
            }
        };
        for obligation in &path.obligations {
            assumptions = assumptions.assume_proposition(obligation.proposition().clone());
        }
        for fact in &path.facts {
            assumptions = assumptions.assume_proposition(fact.proposition().clone());
        }
        assumptions = assumptions.assume_proposition(path.proposition.clone());
    }
    let required_resources = evaluate_function_resource_context(
        &entry_state,
        function.resource_requires(),
        &assumptions,
        &mut budget,
    )
    .ok()?
    .ok()?;
    let (_, resource_definition_facts) = expand_all_composite_resource_facts_and_propositions(
        &required_resources,
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    )?;
    for proposition in resource_definition_facts {
        assumptions = assumptions.assume_proposition(proposition);
    }
    let expanded_required_resources = expand_all_composite_resource_facts(
        &required_resources,
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    )?;
    let entry_resources = expand_all_composite_resource_facts(
        entry_state.resources(),
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    )?;
    if !expanded_required_resources
        .facts()
        .iter()
        .all(|required| entry_resources.satisfies_fact(required, &assumptions))
    {
        return None;
    }
    for proposition in entry_resources.observable_facts(&assumptions).ok()? {
        assumptions = assumptions.assume_proposition(proposition);
    }
    entry_state.resources = entry_resources.clone();
    Some(assumptions)
}

#[allow(clippy::too_many_arguments)]
fn prove_symbolic_c_function_verification_paths_with_environment_and_budget_mode(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    mut budget: ExecutionBudget,
    prepare_contract_resources: bool,
) -> SymbolicCExecution {
    let mut existing = BTreeSet::new();
    collect_c_state_bitvector_variables(&state, &mut existing);
    collect_c_function_bitvector_variables(&function, &mut existing);
    for argument in &arguments {
        collect_c_expression_bitvector_variables(argument, &mut existing);
    }
    collect_assumption_variables(&assumptions, &mut existing);
    collect_execution_environment_variables(&environment, &mut existing);
    let mut variables =
        VerificationVariableGenerator::fresh_for(budget.next_verification_variable, existing);
    let paths = match execute_c_function_verification_paths(
        &state,
        &function,
        &arguments,
        &assumptions,
        &environment,
        execution_semantics,
        &mut budget,
        &mut variables,
        prepare_contract_resources,
    ) {
        Ok(paths) => paths,
        Err(limit) => {
            return SymbolicCExecution {
                paths: Vec::new(),
                limit: Some(limit),
            };
        }
    };
    let paths = paths
        .into_iter()
        .map(|path| {
            let effect_facts = memory_effect_execution_facts(&path.facts);
            let facts = public_execution_pure_facts(&path.facts);
            let proposition = Proposition::CFunctionExecutes {
                state: state.clone(),
                function: function.clone(),
                arguments: arguments.clone(),
                outcome: path.outcome,
            };
            let theorem = Theorem::new(wrap_proof_facts(
                proposition,
                &assumptions,
                &facts,
                &path.obligations,
            ));
            SymbolicCExecutionPath {
                assumptions: assumptions.clone(),
                facts,
                effect_facts,
                obligations: path.obligations,
                theorem,
            }
        })
        .collect();

    SymbolicCExecution { paths, limit: None }
}

pub fn c_function_execution_candidates_from_outcomes(
    state: CState,
    function: CFunction,
    arguments: Vec<CExpression>,
    paths: Vec<(
        CFunctionOutcome,
        Vec<ExecutionPureFact>,
        Vec<ProofObligation>,
    )>,
) -> CFunctionExecutionCandidates {
    let paths = paths
        .into_iter()
        .map(|(outcome, facts, obligations)| {
            let effect_facts = memory_effect_execution_facts(&facts);
            let facts = public_execution_pure_facts(&facts);
            CFunctionExecutionCandidate {
                outcome,
                facts,
                effect_facts,
                obligations,
            }
        })
        .collect();

    CFunctionExecutionCandidates {
        state,
        function,
        arguments,
        paths,
    }
}

pub fn prove_c_function_satisfies_specification_from_symbolic_path(
    function: CFunction,
    specification: CFunctionSpecification,
    path: &SymbolicCExecutionPath,
) -> Option<Theorem> {
    let mut proved = path.theorem().proposition();
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, body) = proved {
        premises.push(premise.as_ref().clone());
        proved = body;
    }
    let Proposition::CFunctionExecutes {
        state,
        function: proved_function,
        arguments,
        outcome,
    } = proved
    else {
        return None;
    };
    if state != specification.state()
        || proved_function != &function
        || arguments != specification.arguments()
        || outcome != specification.outcome()
    {
        return None;
    }

    let requires = specification.requires().to_vec();
    let proposition = requires.into_iter().rev().fold(
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        },
        |body, requirement| Proposition::Implies(Box::new(requirement), Box::new(body)),
    );
    Some(Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(proposition, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    ))
}

fn certified_function_path_parts<'a>(
    function: &CFunction,
    path: &'a SymbolicCExecutionPath,
) -> Option<(
    &'a CState,
    &'a [CExpression],
    &'a CFunctionOutcome,
    Assumptions,
)> {
    let mut proposition = path.theorem().proposition();
    while let Proposition::Implies(_, body) = proposition {
        proposition = body;
    }
    let Proposition::CFunctionExecutes {
        state,
        function: proved_function,
        arguments,
        outcome,
    } = proposition
    else {
        return None;
    };
    if proved_function != function {
        return None;
    }
    let mut assumptions = path.assumptions.clone();
    assumptions = assumptions_with_propositions(
        &assumptions,
        &path
            .execution_facts()
            .iter()
            .map(|fact| fact.proposition().clone())
            .collect::<Vec<_>>(),
    );
    Some((state, arguments, outcome, assumptions))
}

fn resource_contexts_definitionally_equal(
    function: &CFunction,
    memory: &CMemory,
    left: &ResourceContext,
    right: &ResourceContext,
    assumptions: &Assumptions,
) -> bool {
    let directly_equal = |left: &ResourceContext, right: &ResourceContext| {
        left.facts()
            .iter()
            .all(|fact| right.satisfies_fact(fact, assumptions))
            && right
                .facts()
                .iter()
                .all(|fact| left.satisfies_fact(fact, assumptions))
    };
    if left == right {
        return true;
    }
    let Some(left) = expand_all_composite_resource_facts(
        left,
        function.composite_resource_definitions(),
        memory,
        assumptions,
    ) else {
        return false;
    };
    let Some(right) = expand_all_composite_resource_facts(
        right,
        function.composite_resource_definitions(),
        memory,
        assumptions,
    ) else {
        return false;
    };
    directly_equal(&left, &right)
}

/// Extracts constant bounds `lo <= var < hi` from a universal premise made
/// exclusively of constant comparisons against `var`. Returns `None` when any
/// conjunct is not such a bound, so instantiating the conclusion stays sound.
fn constant_variable_bounds(var: Variable, premise: &Proposition) -> Option<(u32, u32)> {
    fn collect(var: Variable, premise: &Proposition, lo: &mut Option<u32>, hi: &mut Option<u32>) -> bool {
        let bound = Bitvector32Term::Variable(var);
        match premise {
            Proposition::And(left, right) => {
                collect(var, left, lo, hi) && collect(var, right, lo, hi)
            }
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(left, right),
                true,
            ) if **right == bound => {
                let Bitvector32Term::Constant(value) = **left else {
                    return false;
                };
                if value > i32::MAX as u32 {
                    return false;
                }
                *lo = Some(lo.map_or(value, |current: u32| current.max(value)));
                true
            }
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(left, right),
                true,
            ) if **left == bound => {
                let Bitvector32Term::Constant(value) = **right else {
                    return false;
                };
                if value > i32::MAX as u32 {
                    return false;
                }
                *hi = Some(hi.map_or(value, |current: u32| current.min(value)));
                true
            }
            _ => false,
        }
    }
    let mut lo = None;
    let mut hi = None;
    if !collect(var, premise, &mut lo, &mut hi) {
        return None;
    }
    Some((lo?, hi?))
}

const FORALL_INSTANTIATION_LIMIT: u32 = 16;

/// Evaluates a premise whose variables have been substituted away to a
/// constant truth value; `None` when it is not a closed constant condition.
fn constant_premise_value(premise: &Proposition) -> Option<bool> {
    match premise {
        Proposition::And(left, right) => {
            Some(constant_premise_value(left)? && constant_premise_value(right)?)
        }
        Proposition::ConditionIs(condition, expected) => {
            let holds = match condition {
                ConditionTerm::Constant(value) => *value,
                ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                    let (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) =
                        (left.as_ref(), right.as_ref())
                    else {
                        return None;
                    };
                    (*left as i32) <= (*right as i32)
                }
                ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                    let (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) =
                        (left.as_ref(), right.as_ref())
                    else {
                        return None;
                    };
                    (*left as i32) < (*right as i32)
                }
                ConditionTerm::Bitvector32SignedAddOverflows(left, right) => {
                    let (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) =
                        (left.as_ref(), right.as_ref())
                    else {
                        return None;
                    };
                    (*left as i32).checked_add(*right as i32).is_none()
                }
                _ => return None,
            };
            Some(holds == *expected)
        }
        _ => None,
    }
}

/// Instantiates finitely-bounded universal facts (`forall x. guards -> lo <=
/// x < hi -> P(x)` with small constant bounds) at every point in the bound,
/// so the certifier can use per-index conclusions the way an unfolded proof
/// does. Guard premises (such as overflow side conditions) must evaluate to
/// constant truth after substitution, or the point is skipped.
fn finite_forall_instantiations(facts: &[Proposition]) -> Vec<Proposition> {
    let mut instantiated = Vec::new();
    for fact in facts {
        let Proposition::ForAll {
            var,
            sort: Sort::CInt32 | Sort::Bitvector32,
            body,
        } = fact
        else {
            continue;
        };
        let mut premises = Vec::new();
        let mut conclusion = body.as_ref();
        while let Proposition::Implies(premise, rest) = conclusion {
            premises.push(premise.as_ref());
            conclusion = rest.as_ref();
        }
        let Some((lo, hi)) = premises
            .iter()
            .find_map(|premise| constant_variable_bounds(*var, premise))
        else {
            continue;
        };
        if hi <= lo || hi - lo > FORALL_INSTANTIATION_LIMIT {
            continue;
        }
        for value in lo..hi {
            let witness = Bitvector32Term::Constant(value);
            let premises_hold = premises.iter().all(|premise| {
                constant_variable_bounds(*var, premise).is_some()
                    || constant_premise_value(&substitute_bitvector_variable_in_proposition(
                        premise, *var, &witness,
                    )) == Some(true)
            });
            if premises_hold {
                instantiated.push(substitute_bitvector_variable_in_proposition(
                    conclusion, *var, &witness,
                ));
            }
        }
    }
    instantiated
}

/// Collects one-point-rule witness candidates for an existential body: any
/// conjunct shaped `var == term` (on either side) pins the bound variable to
/// `term`, provided `term` does not itself mention the variable.
fn exists_equality_witness_candidates(
    var: Variable,
    body: &Proposition,
    candidates: &mut Vec<Bitvector32Term>,
) {
    match body {
        Proposition::And(left, right) => {
            exists_equality_witness_candidates(var, left, candidates);
            exists_equality_witness_candidates(var, right, candidates);
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
            let bound = Bitvector32Term::Variable(var);
            for (side, other) in [(left, right), (right, left)] {
                let mentions_var = super::reasoning::substitute_bitvector_variable(
                    other,
                    var,
                    &Bitvector32Term::Constant(0),
                ) != **other;
                if **side == bound && !mentions_var {
                    candidates.push((**other).clone());
                }
            }
        }
        _ => {}
    }
}

fn certification_proves_proposition(assumptions: &Assumptions, proposition: &Proposition) -> bool {
    if assumptions.proves(proposition) {
        return true;
    }
    match proposition {
        Proposition::And(left, right) => {
            certification_proves_proposition(assumptions, left)
                && certification_proves_proposition(assumptions, right)
        }
        Proposition::Exists {
            var,
            sort: sort @ (Sort::CInt32 | Sort::Bitvector32),
            body,
            ..
        } => {
            // An assumed existential proves the goal up to renaming of the
            // bound variable; bound variables are freshened per lowering
            // pass, so exact matching alone would never fire.
            let alpha_matched = assumptions.prop_facts.iter().any(|fact| {
                let Proposition::Exists {
                    var: fact_var,
                    sort: fact_sort,
                    body: fact_body,
                    ..
                } = fact
                else {
                    return false;
                };
                fact_sort == sort
                    && substitute_bitvector_variable_in_proposition(
                        fact_body,
                        *fact_var,
                        &Bitvector32Term::Variable(*var),
                    ) == **body
            });
            if alpha_matched {
                return true;
            }
            // One-point rule: `P[t/x]` proves `exists x. P` when a conjunct
            // pins `x` to a witness term `t`.
            let mut candidates = Vec::new();
            exists_equality_witness_candidates(*var, body, &mut candidates);
            candidates.into_iter().any(|witness| {
                let instantiated =
                    substitute_bitvector_variable_in_proposition(body, *var, &witness);
                certification_proves_proposition(assumptions, &instantiated)
            })
        }
        Proposition::ConditionIs(condition, value)
            if assumptions.decide_condition_for_simp(condition) == Some(*value) =>
        {
            true
        }
        Proposition::ConditionIs(condition, value)
            if assumptions.has_matching_condition_fact_for_memory_resolution(condition, *value) =>
        {
            true
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
            bitvector_terms_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => {
            pointers_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
            pointer_offsets_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        Proposition::Equal(Term::CValue(left), Term::CValue(right)) => {
            c_values_proven_equal_for_memory_resolution(left, right, assumptions)
        }
        _ => false,
    }
}

fn certification_proves_post_proposition(
    assumptions: &Assumptions,
    proposition: &Proposition,
    post_memory: &CMemory,
) -> bool {
    if certification_proves_proposition(assumptions, proposition) {
        return true;
    }
    assumptions
        .prop_facts
        .iter()
        .filter(|fact| {
            matches!(
                (fact, proposition),
                (
                    Proposition::ConditionIs(_, _),
                    Proposition::ConditionIs(_, _)
                ) | (Proposition::Equal(_, _), Proposition::Equal(_, _))
            )
        })
        .any(|fact| {
            let Some(theorem) = prove_c_condition_fact_transport(fact, post_memory, assumptions)
            else {
                return false;
            };
            let Proposition::Implies(source, target) = theorem.proposition() else {
                return false;
            };
            if source.as_ref() != fact {
                return false;
            }
            let transported_assumptions =
                assumptions_with_propositions(assumptions, &[target.as_ref().clone()]);
            certification_proves_proposition(&transported_assumptions, proposition)
        })
}

fn resources_certify_loadability(
    state: &CState,
    resources: &ResourceContext,
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> bool {
    match proposition {
        Proposition::ForAll { body, .. } => {
            return resources_certify_loadability(state, resources, body, assumptions);
        }
        Proposition::Implies(premise, conclusion) => {
            let assumptions = assumptions
                .clone()
                .assume_proposition(premise.as_ref().clone());
            return resources_certify_loadability(state, resources, conclusion, &assumptions);
        }
        Proposition::And(left, right) => {
            return resources_certify_loadability(state, resources, left, assumptions)
                && resources_certify_loadability(state, resources, right, assumptions);
        }
        _ => {}
    }
    let Proposition::CMemoryLoadable {
        memory,
        base,
        bytes,
    } = proposition
    else {
        return false;
    };
    memory_snapshots_proven_equal_at_pointer(memory, state.memory(), base, assumptions)
        && bytes
            .as_const()
            .and_then(|bytes| u32::try_from(bytes).ok())
            .is_some_and(|bytes| resource_context_has_read(resources, base, bytes, assumptions))
}

fn contract_endpoints_certify_loadability(
    entry_state: &CState,
    entry_resources: &ResourceContext,
    post_state: &CState,
    post_resources: &ResourceContext,
    proposition: &Proposition,
    assumptions: &Assumptions,
) -> bool {
    resources_certify_loadability(entry_state, entry_resources, proposition, assumptions)
        || resources_certify_loadability(post_state, post_resources, proposition, assumptions)
}

pub fn c_function_outcomes_definitionally_equal(
    function: &CFunction,
    left: &CFunctionOutcome,
    right: &CFunctionOutcome,
    assumptions: &Assumptions,
) -> bool {
    match (left, right) {
        (
            CFunctionOutcome::Return {
                value: left_value,
                state: left_state,
            },
            CFunctionOutcome::Return {
                value: right_value,
                state: right_state,
            },
        ) => {
            let values =
                c_values_proven_equal_for_memory_resolution(left_value, right_value, assumptions);
            let memories = c_memories_definitionally_equal(
                left_state.memory(),
                right_state.memory(),
                assumptions,
            );
            let resources = resource_contexts_definitionally_equal(
                function,
                left_state.memory(),
                left_state.resources(),
                right_state.resources(),
                assumptions,
            );
            values && memories && resources
        }
        _ => left == right,
    }
}

fn c_memories_definitionally_equal(
    left: &CMemory,
    right: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    if memories_proven_equal_for_memory_resolution(left, right, assumptions) {
        return true;
    }
    if !left
        .blocks
        .iter()
        .filter(|(block, _)| !block.starts_with("local:"))
        .eq(right
            .blocks
            .iter()
            .filter(|(block, _)| !block.starts_with("local:")))
    {
        return false;
    }
    memory_cells_definitionally_contained(left, right, assumptions)
        && memory_cells_definitionally_contained(right, left, assumptions)
}

fn memory_cells_definitionally_contained(
    source: &CMemory,
    target: &CMemory,
    assumptions: &Assumptions,
) -> bool {
    for (source_pointer, source_value) in source
        .cells
        .iter()
        .filter(|(pointer, _)| !pointer.block.starts_with("local:"))
    {
        let matching = target.cells.iter().find(|(target_pointer, _)| {
            pointers_proven_equal_for_memory_resolution(source_pointer, target_pointer, assumptions)
        });
        let equal = if let Some((_, target_value)) = matching {
            c_values_proven_equal_for_memory_resolution(source_value, target_value, assumptions)
        } else {
            materialized_load_is_unchanged(source_value, target, source_pointer, assumptions)
        };
        if !equal {
            return false;
        }
    }
    true
}

fn materialized_load_is_unchanged(
    value: &CValue,
    symbolic_memory: &CMemory,
    pointer: &Pointer,
    assumptions: &Assumptions,
) -> bool {
    let load = match value {
        CValue::Int32(Bitvector32Term::MemoryLoad(memory, load_pointer))
        | CValue::UInt8(Bitvector32Term::MemoryLoad(memory, load_pointer)) => {
            (memory.as_ref(), load_pointer.as_ref())
        }
        _ => return false,
    };
    pointers_proven_equal_for_memory_resolution(load.1, pointer, assumptions)
        && c_memory_load_is_unchanged(load.0, symbolic_memory, pointer, assumptions)
}

/// Changes only the bounded symbolic representation of a certified return path.
///
/// Program values and memory must be definitionally equal using the path's
/// certified pure, memory-effect, and resource-separation facts. The old and
/// new resource contexts must mutually satisfy every fact under those same
/// assumptions.
pub fn certify_c_function_execution_path_resource_representation(
    path: &SymbolicCExecutionPath,
    desired_outcome: CFunctionOutcome,
) -> Option<SymbolicCExecutionPath> {
    let mut proposition = path.theorem().proposition();
    let mut premises = Vec::new();
    while let Proposition::Implies(premise, body) = proposition {
        premises.push(premise.as_ref().clone());
        proposition = body;
    }
    let Proposition::CFunctionExecutes {
        state,
        function,
        arguments,
        outcome,
    } = proposition
    else {
        return None;
    };
    let (
        CFunctionOutcome::Return {
            value,
            state: return_state,
        },
        CFunctionOutcome::Return {
            value: desired_value,
            state: desired_state,
        },
    ) = (outcome, &desired_outcome)
    else {
        return (outcome == &desired_outcome).then(|| path.clone());
    };
    premises.extend(
        path.execution_facts()
            .iter()
            .map(|fact| fact.proposition().clone()),
    );
    let preliminary_assumptions = assumptions_with_propositions(&path.assumptions, &premises);
    let observable_resource_facts = return_state
        .resources()
        .observable_facts(&preliminary_assumptions)
        .ok()?;
    premises.extend(observable_resource_facts);
    let assumptions = assumptions_with_propositions(&path.assumptions, &premises);
    if !c_values_proven_equal_for_memory_resolution(value, desired_value, &assumptions)
        || !c_memories_definitionally_equal(
            return_state.memory(),
            desired_state.memory(),
            &assumptions,
        )
    {
        return None;
    }
    if !resource_contexts_definitionally_equal(
        function,
        return_state.memory(),
        return_state.resources(),
        desired_state.resources(),
        &assumptions,
    ) {
        return None;
    }

    let conclusion = Proposition::CFunctionExecutes {
        state: state.clone(),
        function: function.clone(),
        arguments: arguments.clone(),
        outcome: desired_outcome,
    };
    let theorem = Theorem::new(
        premises
            .into_iter()
            .rev()
            .fold(conclusion, |body, premise| {
                Proposition::Implies(Box::new(premise), Box::new(body))
            }),
    );
    Some(SymbolicCExecutionPath {
        assumptions: path.assumptions.clone(),
        facts: path.facts.clone(),
        effect_facts: path.effect_facts.clone(),
        obligations: path.obligations.clone(),
        theorem,
    })
}

struct CertifiedFunctionClaimPath {
    caller_state: CState,
    return_state: CState,
    entry_state: CState,
    entry_resources: ResourceContext,
    post_state: CState,
    post_resources: ResourceContext,
    assumptions: Assumptions,
    execution_facts: Vec<ExecutionPureFact>,
}

fn prepare_function_claim_path(
    function: &CFunction,
    path: &SymbolicCExecutionPath,
) -> Result<CertifiedFunctionClaimPath, String> {
    let Some((caller_state, arguments, outcome, assumptions)) =
        certified_function_path_parts(function, path)
    else {
        return Err("the certified path does not belong to the exact function".to_string());
    };
    let CFunctionOutcome::Return {
        value,
        state: return_state,
    } = outcome
    else {
        return Err(format!("the certified path does not return: {outcome:?}"));
    };
    let Some(mut entry_state) = c_function_entry_state(caller_state, function, arguments) else {
        return Err("the function entry state cannot be reconstructed".to_string());
    };
    let mut budget = ExecutionBudget::default();
    let Ok(Ok(required_resources)) = evaluate_function_resource_context(
        &entry_state,
        function.resource_requires(),
        &assumptions,
        &mut budget,
    ) else {
        return Err("the required resource context cannot be evaluated".to_string());
    };
    let Some((_, definition_facts)) = expand_all_composite_resource_facts_and_propositions(
        &required_resources,
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    ) else {
        return Err("the required composite resources cannot be expanded".to_string());
    };
    let assumptions = assumptions_with_propositions(&assumptions, &definition_facts);
    let Some(entry_resources) = expand_all_composite_resource_facts(
        entry_state.resources(),
        function.composite_resource_definitions(),
        entry_state.memory(),
        &assumptions,
    ) else {
        return Err("the entry resource context cannot be expanded".to_string());
    };
    let Ok(resource_facts) = entry_resources.observable_facts(&assumptions) else {
        return Err("the entry resource context is not observable".to_string());
    };
    entry_state.resources = entry_resources.clone();
    let assumptions = assumptions_with_propositions(&assumptions, &resource_facts);
    let Some(post_resources) = expand_all_composite_resource_facts(
        return_state.resources(),
        function.composite_resource_definitions(),
        return_state.memory(),
        &assumptions,
    ) else {
        return Err("the returned resource context cannot be expanded".to_string());
    };
    let Ok(post_resource_facts) = post_resources.observable_facts(&assumptions) else {
        return Err("the returned resource context is not observable".to_string());
    };
    let assumptions = assumptions_with_propositions(&assumptions, &post_resource_facts);
    let mut post_state = entry_state
        .clone()
        .with_memory(return_state.memory().clone());
    post_state.resources = post_resources.clone();
    post_state
        .locals
        .set_typed("result".to_string(), value.clone(), function.return_type());
    if !path.obligations().iter().all(|obligation| {
        let proved = certification_proves_proposition(&assumptions, obligation.proposition())
            || contract_endpoints_certify_loadability(
                &entry_state,
                &entry_resources,
                &post_state,
                &post_resources,
                obligation.proposition(),
                &assumptions,
            );
        proved
    }) {
        return Err("the execution path has an unproved verification condition".to_string());
    }

    Ok(CertifiedFunctionClaimPath {
        caller_state: caller_state.clone(),
        return_state: return_state.clone(),
        entry_state,
        entry_resources,
        post_state,
        post_resources,
        assumptions,
        execution_facts: path.execution_facts().to_vec(),
    })
}

fn function_claim_holds_on_prepared_path(
    function: &CFunction,
    claim: &CFunctionContractClaim,
    path: &CertifiedFunctionClaimPath,
) -> bool {
    let CertifiedFunctionClaimPath {
        caller_state,
        return_state,
        entry_state,
        entry_resources,
        post_state,
        post_resources,
        assumptions,
        execution_facts,
    } = path;
    let mut budget = ExecutionBudget::default();
    match claim.target() {
        CFunctionContractClaimTarget::BodySafety => true,
        CFunctionContractClaimTarget::EnsureProposition(index) => {
            let Some(ensure) = function.contract_ensures().get(*index) else {
                return false;
            };
            let Ok(paths) = lower_spec_proposition_at_state_with_loop_entry(
                &post_state,
                ensure,
                Some(&entry_state),
                &assumptions,
                &mut budget,
            ) else {
                return false;
            };
            paths.into_iter().any(|path| {
                let obligations_hold = path.obligations.iter().all(|obligation| {
                    certification_proves_proposition(&assumptions, obligation.proposition())
                        || contract_endpoints_certify_loadability(
                            &entry_state,
                            &entry_resources,
                            &post_state,
                            &post_resources,
                            obligation.proposition(),
                            &assumptions,
                        )
                });
                let mut path_propositions = path
                    .facts
                    .iter()
                    .map(|fact| fact.proposition().clone())
                    .collect::<Vec<_>>();
                let assumption_facts = assumptions.prop_facts.iter().cloned().collect::<Vec<_>>();
                path_propositions.extend(finite_forall_instantiations(&assumption_facts));
                path_propositions.extend(finite_forall_instantiations(&path_propositions.clone()));
                let path_assumptions =
                    assumptions_with_propositions(&assumptions, &path_propositions);
                let proposition_holds = certification_proves_post_proposition(
                    &path_assumptions,
                    &path.proposition,
                    return_state.memory(),
                );
                obligations_hold && proposition_holds
            })
        }
        CFunctionContractClaimTarget::EnsureResource(index) => {
            let Some(resource) = function.resource_ensures().get(*index) else {
                return false;
            };
            let Ok(Ok(expected)) = evaluate_function_resource_context(
                &post_state,
                std::slice::from_ref(resource),
                &assumptions,
                &mut budget,
            ) else {
                return false;
            };
            expected.facts().iter().all(|fact| {
                resource_context_satisfies_definitional_fact(
                    return_state.resources(),
                    fact,
                    function.composite_resource_definitions(),
                    return_state.memory(),
                    &assumptions,
                )
            })
        }
        CFunctionContractClaimTarget::Effect => {
            let mut mutable_ranges = Vec::new();
            for segment in function.contract_mutable() {
                let Ok(Ok(segment)) =
                    evaluate_loop_effect_segment(&entry_state, segment, &assumptions, &mut budget)
                else {
                    return false;
                };
                mutable_ranges.push(CMemoryRange::new(segment.base, segment.start, segment.end));
            }
            let mut effect_memory = caller_state.memory().clone();
            // A verified region can emit several effect summaries for the
            // same before/after transition (for example a loop's explicit
            // effects clause plus the inherited function effect). The first
            // advances the tracked memory; the others are parallel bounds on
            // the same transition and must not be chained sequentially.
            let mut previous_transition: Option<&CMemory> = None;
            let effects_are_bounded = execution_facts.iter().all(|fact| match fact.proposition() {
                Proposition::CMemoryMutatesOnly {
                    before,
                    after,
                    pointers,
                } => {
                    if !c_memories_definitionally_equal(&effect_memory, before, &assumptions) {
                        return false;
                    }
                    previous_transition = None;
                    effect_memory = after.clone();
                    pointers
                        .iter()
                        .filter(|pointer| !pointer.block.starts_with("local:"))
                        .all(|pointer| {
                            mutable_ranges.iter().any(|range| {
                                assumptions.pointer_access_in_range(
                                    pointer,
                                    4,
                                    range.base(),
                                    range.start(),
                                    range.end(),
                                )
                            })
                        })
                }
                Proposition::CMemoryEffectSummary {
                    before,
                    after,
                    mutable_ranges: nested_ranges,
                } => {
                    if c_memories_definitionally_equal(&effect_memory, before, &assumptions) {
                        previous_transition = Some(before);
                        effect_memory = after.clone();
                    } else if !previous_transition.is_some_and(|previous_before| {
                        c_memories_definitionally_equal(previous_before, before, &assumptions)
                            && c_memories_definitionally_equal(
                                &effect_memory,
                                after,
                                &assumptions,
                            )
                    }) {
                        return false;
                    }
                    nested_ranges.iter().all(|nested| {
                        mutable_ranges
                            .iter()
                            .any(|allowed| memory_range_covers(allowed, nested, &assumptions))
                    })
                }
                _ => true,
            });
            let endpoint_matches = c_memories_definitionally_equal(
                &effect_memory,
                return_state.memory(),
                &assumptions,
            );
            effects_are_bounded && endpoint_matches
        }
    }
}

/// Certifies every exact contract claim in one pass over a kernel-produced,
/// complete execution frontier.
///
/// Path validity, resource expansion, and verification conditions are checked
/// once per path and then shared by the individual claim checks.
pub fn c_verified_function_contract_claims(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
) -> Option<Vec<CVerifiedFunctionContractClaim>> {
    let execution = &contract_execution.execution;
    if execution.limit().is_some() || execution.paths().is_empty() {
        return None;
    }
    let paths = execution
        .paths()
        .iter()
        .map(|path| prepare_function_claim_path(function, path))
        .collect::<Result<Vec<_>, _>>()
        .ok()?;
    function
        .contract_claims()
        .iter()
        .map(|claim| {
            paths
                .iter()
                .all(|path| function_claim_holds_on_prepared_path(function, claim, path))
                .then(|| CVerifiedFunctionContractClaim {
                    function: function.clone(),
                    key: claim.key().clone(),
                })
        })
        .collect()
}

/// Reports the exact contract claims that the checked execution frontier does
/// not establish. This is diagnostic information only: unlike the companion
/// certification API, it cannot mint proof objects.
///
/// `None` means the frontier itself is incomplete or could not be prepared for
/// claim checking. An empty vector means every claim holds.
pub fn c_unverified_function_contract_claims(
    function: &CFunction,
    contract_execution: &CFunctionContractExecution,
) -> Result<Vec<CFunctionContractClaimKey>, String> {
    let execution = &contract_execution.execution;
    if let Some(limit) = execution.limit() {
        return Err(format!("symbolic execution reached its {limit:?} limit"));
    }
    if execution.paths().is_empty() {
        return Err("symbolic execution produced no paths".to_string());
    }
    let paths = execution
        .paths()
        .iter()
        .enumerate()
        .map(|(index, path)| {
            prepare_function_claim_path(function, path)
                .map_err(|reason| format!("execution path {index} is invalid: {reason}"))
        })
        .collect::<Result<Vec<_>, _>>()?;
    Ok(function
        .contract_claims()
        .iter()
        .filter(|claim| {
            !paths
                .iter()
                .all(|path| function_claim_holds_on_prepared_path(function, claim, path))
        })
        .map(|claim| claim.key().clone())
        .collect())
}

/// Certifies one contract claim only after a kernel-produced complete
/// execution frontier establishes that exact claim for the exact function.
pub fn c_verified_function_contract_claim(
    function: &CFunction,
    key: CFunctionContractClaimKey,
    execution: &CFunctionContractExecution,
) -> Option<CVerifiedFunctionContractClaim> {
    c_verified_function_contract_claims(function, execution)?
        .into_iter()
        .find(|proof| proof.key == key)
}

/// Packages an opaque rule only after every recorded contract claim has a
/// certificate for this exact function.
pub fn c_verified_function_rule(
    function: CFunction,
    proofs: &[CVerifiedFunctionContractClaim],
) -> Option<CVerifiedFunctionRule> {
    if !function.opaque_contract_supported()
        || function.contract_claims().is_empty()
        || proofs.iter().any(|proof| proof.function != function)
        || function
            .contract_claims()
            .iter()
            .any(|claim| !proofs.iter().any(|proof| proof.key == *claim.key()))
    {
        return None;
    }
    Some(CVerifiedFunctionRule { function })
}

pub fn prove_c_function_satisfies_specification(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: Assumptions,
) -> Option<Theorem> {
    prove_c_function_satisfies_specification_with_environment(
        function,
        specification,
        assumptions,
        CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
    )
}

pub fn prove_c_function_satisfies_specification_with_environment(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: Assumptions,
    environment: CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
) -> Option<Theorem> {
    let specification_assumptions =
        assumptions_with_propositions(&assumptions, specification.requires());
    let paths = execute_c_function_paths(
        specification.state(),
        &function,
        specification.arguments(),
        &specification_assumptions,
        &environment,
        execution_semantics,
        &mut ExecutionBudget::default(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some()
        || path.facts.iter().any(ExecutionPureFact::is_public)
        || !path.obligations.is_empty()
        || &path.outcome != specification.outcome()
    {
        return None;
    }

    let requires = specification.requires().to_vec();
    let proposition = requires.iter().rev().fold(
        Proposition::CFunctionSatisfiesSpecification {
            function,
            specification,
        },
        |body, requirement| Proposition::Implies(Box::new(requirement.clone()), Box::new(body)),
    );
    Some(Theorem::new(wrap_proof_facts(
        proposition,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_function_satisfies_specification_and_propositions(
    function: CFunction,
    specification: CFunctionSpecification,
    assumptions: Assumptions,
    propositions: Vec<Proposition>,
) -> Option<Theorem> {
    prove_c_function_satisfies_specification(
        function.clone(),
        specification.clone(),
        assumptions.clone(),
    )?;

    let specification_assumptions =
        assumptions_with_propositions(&assumptions, specification.requires());
    if propositions
        .iter()
        .any(|proposition| !specification_assumptions.proves(proposition))
    {
        return None;
    }

    let conclusion = proposition_and_all(
        std::iter::once(Proposition::CFunctionSatisfiesSpecification {
            function: function.clone(),
            specification: specification.clone(),
        })
        .chain(propositions)
        .collect(),
    );
    let proposition = specification
        .requires()
        .iter()
        .rev()
        .fold(conclusion, |body, requirement| {
            Proposition::Implies(Box::new(requirement.clone()), Box::new(body))
        });
    Some(Theorem::new(wrap_proof_facts(
        proposition,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_statement_executes_and_propositions(
    state: CState,
    statement: CStatement,
    assumptions: Assumptions,
    propositions: Vec<Proposition>,
) -> Option<Theorem> {
    let paths = execute_c_statement_paths(
        &state,
        &statement,
        &assumptions,
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() || !path.facts.is_empty() || !path.obligations.is_empty() {
        return None;
    }
    if propositions
        .iter()
        .any(|proposition| !assumptions.proves(proposition))
    {
        return None;
    }
    let conclusion = proposition_and_all(
        std::iter::once(Proposition::CStatementExecutes {
            state,
            statement,
            outcome: path.outcome,
        })
        .chain(propositions)
        .collect(),
    );
    Some(Theorem::new(wrap_proof_facts(
        conclusion,
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_max_lt_returns_right(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits.clone(), b_bits.clone());
    let state = c_max_state(a_value, b_value.clone());
    let assumptions = Assumptions::new().assume_condition(condition.clone(), true);
    let outcome = execute_c_statement(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStatementOutcome::Return {
            value: b_value,
            state: state.clone(),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, true)),
                Box::new(Proposition::CStatementExecutes {
                    state,
                    statement: c_max_body(),
                    outcome,
                }),
            ),
        ),
    )))
}

pub fn prove_c_max_not_lt_returns_left(a: Variable, b: Variable) -> Option<Theorem> {
    let a_bits = Bitvector32Term::Variable(a);
    let b_bits = Bitvector32Term::Variable(b);
    let a_value = int32(a_bits.clone());
    let b_value = int32(b_bits.clone());
    let condition = c_max_lt_condition(a_bits, b_bits);
    let state = c_max_state(a_value.clone(), b_value);
    let assumptions = Assumptions::new().assume_condition(condition.clone(), false);
    let outcome = execute_c_statement(&state, &c_max_body(), &assumptions)?;

    if outcome
        != (CStatementOutcome::Return {
            value: a_value,
            state: state.clone(),
        })
    {
        return None;
    }

    Some(Theorem::new(forall_int32(
        a,
        forall_int32(
            b,
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition, false)),
                Box::new(Proposition::CStatementExecutes {
                    state,
                    statement: c_max_body(),
                    outcome,
                }),
            ),
        ),
    )))
}

pub fn prove_memory_load(memory: CMemory, pointer: Pointer) -> Theorem {
    let outcome = memory.load(&pointer);
    Theorem::new(Proposition::CMemoryLoads {
        memory,
        pointer,
        outcome,
    })
}

pub fn prove_memory_load_after_store_same(
    memory: CMemory,
    pointer: Pointer,
    value: CValue,
) -> Theorem {
    let stored = memory.store(pointer.clone(), value.clone());
    Theorem::new(Proposition::CMemoryLoads {
        memory: stored,
        pointer,
        outcome: CExpressionOutcome::Value(value),
    })
}

pub fn prove_memory_load_after_store_other(
    memory: CMemory,
    stored_pointer: Pointer,
    stored_value: CValue,
    loaded_pointer: Pointer,
) -> Option<Theorem> {
    if stored_pointer == loaded_pointer {
        return None;
    }

    let outcome = memory.load(&loaded_pointer);
    let stored = memory.store(stored_pointer, stored_value);
    if stored.load(&loaded_pointer) != outcome {
        return None;
    }

    Some(Theorem::new(Proposition::CMemoryLoads {
        memory: stored,
        pointer: loaded_pointer,
        outcome,
    }))
}

pub fn prove_memory_load_after_store_distinct_under_assumptions(
    memory: CMemory,
    stored_pointer: Pointer,
    stored_value: CValue,
    loaded_pointer: Pointer,
    assumptions: Assumptions,
) -> Option<Theorem> {
    if !pointers_proven_distinct(&stored_pointer, &loaded_pointer, &assumptions) {
        return None;
    }

    let outcome = memory.load(&loaded_pointer);
    let stored = memory.store(stored_pointer, stored_value);
    if stored.load(&loaded_pointer) != outcome {
        return None;
    }

    Some(Theorem::new(wrap_proof_facts(
        Proposition::CMemoryLoads {
            memory: stored,
            pointer: loaded_pointer,
            outcome,
        },
        &assumptions,
        &[],
        &[],
    )))
}

pub fn prove_c_while_invariant_rule(
    state: CState,
    condition: CExpression,
    invariant: Vec<Proposition>,
    body: CStatement,
    assumptions: Assumptions,
    preserved: Vec<Proposition>,
    postcondition: Proposition,
) -> Option<Theorem> {
    if invariant
        .iter()
        .any(|invariant| !assumptions.proves(invariant))
    {
        return None;
    }

    let loop_assumptions = assumptions_with_propositions(&assumptions, &invariant);
    let step_ok = condition_contexts_for_truthiness(&state, &condition, &loop_assumptions, true)
        .into_iter()
        .any(|step_assumptions| {
            let body_paths = execute_c_statement_paths(
                &state,
                &body,
                &step_assumptions,
                &CExecutionEnvironment::new(),
                CExecutionSemantics::EXECUTE_BODIES,
                &mut ExecutionBudget::default(),
            );
            let Ok(body_paths) = body_paths else {
                return false;
            };
            let mut body_paths = body_paths.into_iter();
            let Some(body_path) = body_paths.next() else {
                return false;
            };
            if body_paths.next().is_some()
                || !body_path.facts.is_empty()
                || !body_path.obligations.is_empty()
                || !matches!(body_path.outcome, CStatementOutcome::Normal(_))
            {
                return false;
            }
            preserved
                .iter()
                .all(|preserved| step_assumptions.proves(preserved))
        });

    if !step_ok {
        return None;
    }

    let exit_ok = condition_contexts_for_truthiness(&state, &condition, &loop_assumptions, false)
        .into_iter()
        .any(|exit_assumptions| exit_assumptions.proves(&postcondition));

    if !exit_ok {
        return None;
    }

    Some(Theorem::new(wrap_proof_facts(
        Proposition::CWhileInvariantRule {
            state,
            condition,
            invariant,
            body,
            preserved,
            postcondition: Box::new(postcondition),
        },
        &assumptions,
        &[],
        &[],
    )))
}
