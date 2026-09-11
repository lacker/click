use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

/// Checks that a returning path wrote no caller-visible memory.
///
/// A contract that owns no memory has an empty write footprint: ownership,
/// not an effect clause, is what permits a store. This is the ownership-side
/// check that a contract with nothing owned really left every caller-visible
/// cell alone.
pub(in crate::surface) fn prove_empty_write_footprint(
    claim_label: &str,
    path_index: usize,
    execution_pure_facts: &[crate::kernel::ExecutionPureFact],
    available_pure_facts: &[Proposition],
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    pre_state: &CState,
    outcome: &CFunctionOutcome,
) -> Result<(), ClickError> {
    let CFunctionOutcome::Return { .. } = outcome else {
        return Err(ClickError::new(format!(
            "`{claim_label}` failed on path {path_index}: {}",
            describe_function_outcome(outcome, parameters, arguments)
        )));
    };
    let mut effect_facts = execution_pure_facts.to_vec();
    effect_facts.extend(
        available_pure_facts
            .iter()
            .filter(|proposition| {
                matches!(
                    proposition,
                    Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CHeapAllocationFreed { .. }
                )
            })
            .cloned()
            .map(ExecutionPureFact::new),
    );
    let mut writes = memory_effect_write_pointers(&effect_facts);
    writes.retain(|pointer| is_preexisting_write_pointer(pointer, pre_state));
    if let Some(pointer) = writes.first() {
        return Err(ClickError::new(format!(
            "`{claim_label}` failed on path {path_index}: write to `{}` is outside the mutable footprint\n  execution pure facts: {}",
            describe_pointer(pointer, parameters, arguments),
            describe_execution_pure_facts(execution_pure_facts)
        )));
    }
    let summary_range = effect_facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::CMemoryEffectSummary {
                before,
                mutable_ranges,
                ..
            } => Some(mutable_ranges.iter().map(move |range| (before, range))),
            _ => None,
        })
        .flatten()
        .filter(|(before, range)| {
            is_preexisting_write_pointer(range.base(), pre_state)
                && (!crate::kernel::c_memory_holds_live_heap_allocation_at(before, range.base())
                    || crate::kernel::c_memory_holds_live_heap_allocation_at(
                        pre_state.memory(),
                        range.base(),
                    ))
        })
        .map(|(_, range)| range)
        .next();
    if let Some(range) = summary_range {
        return Err(ClickError::new(format!(
            "`{claim_label}` failed on path {path_index}: write range `{}` is outside the mutable footprint\n  execution pure facts: {}",
            describe_memory_range(range, parameters, arguments),
            describe_execution_pure_facts(execution_pure_facts)
        )));
    }
    Ok(())
}

fn is_preexisting_write_pointer(pointer: &Pointer, pre_state: &CState) -> bool {
    !pointer.block.starts_with("local:")
        && !pointer.block.starts_with("havoc:")
        && (!matches!(
            pointer.block,
            PointerBlock::Heap(_) | PointerBlock::Symbolic(_)
        ) || pre_state.memory().has_block(&pointer.block)
            || pre_state.memory().is_live_heap_address(pointer))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct EvaluatedContractSegment {
    pub(in crate::surface) source: ContractSegment,
    pub(in crate::surface) base: Pointer,
    pub(in crate::surface) start: Bitvector32Term,
    pub(in crate::surface) end: Bitvector32Term,
    pub(in crate::surface) element_width: u32,
}

pub(in crate::surface) fn evaluate_requirement_segment(
    parameters: &[syntax::C0Parameter],
    arguments: &[CExpression],
    entry_state: &CState,
    segment: &ContractSegment,
) -> Result<EvaluatedContractSegment, String> {
    if segment.state != ContractSegmentState::Current {
        return Err(
            "requirement segments are entry-state references; `old(...)` is not supported here"
                .to_string(),
        );
    }
    let parameter_values =
        parameter_values(parameters, arguments).map_err(|error| error.message)?;
    let array_refs = array_refs_for_parameters(parameters, &parameter_values, entry_state.memory());
    evaluate_segment_bounds(
        segment,
        &PureFactContext::new(),
        &parameter_values,
        &array_refs,
        entry_state,
        contract_segment_element_width(parameters, segment),
    )
}

/// A segment's base, start, and end, each evaluated by the kernel at
/// `state` as the C fragment it is.
fn evaluate_segment_bounds(
    segment: &ContractSegment,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    state: &CState,
    element_width: u32,
) -> Result<EvaluatedContractSegment, String> {
    let evaluate = |expression: &CExpression| {
        crate::surface::proof::evaluate_c_fragment_through_kernel(
            expression,
            assumptions,
            values,
            array_refs,
            state,
            None,
        )
    };
    let CValue::Pointer(base) = evaluate(&segment.base)? else {
        return Err("segment base did not evaluate to a pointer".to_string());
    };
    let CValue::Int32(start) = evaluate(&segment.start)? else {
        return Err("segment start did not evaluate to int32".to_string());
    };
    let CValue::Int32(end) = evaluate(&segment.end)? else {
        return Err("segment end did not evaluate to int32".to_string());
    };
    Ok(EvaluatedContractSegment {
        source: segment.clone(),
        base: base.into_pointer(),
        start,
        end,
        element_width,
    })
}

pub(in crate::surface) fn segment_contains_pointer(
    segment: &EvaluatedContractSegment,
    pointer: &Pointer,
    assumptions: &PureFactContext,
) -> bool {
    let Some(index) = pointer_element_index_from_base_with_width(
        pointer,
        &segment.base,
        segment.element_width,
        assumptions,
    ) else {
        return false;
    };
    assumptions.proves(&Proposition::ConditionIs(
        signed_less_equal(segment.start.clone(), index.clone()),
        true,
    )) && assumptions.proves(&Proposition::ConditionIs(
        signed_less_than(index, segment.end.clone()),
        true,
    ))
}

#[allow(dead_code)]
pub(in crate::surface) fn pointer_element_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    assumptions: &PureFactContext,
) -> Option<Bitvector32Term> {
    pointer_element_index_from_base_with_width(pointer, base, 4, assumptions)
}

fn pointer_element_index_from_base_with_width(
    pointer: &Pointer,
    base: &Pointer,
    element_width: u32,
    assumptions: &PureFactContext,
) -> Option<Bitvector32Term> {
    if pointer.block != base.block {
        return None;
    }

    if pointer.offset == base.offset
        || pointer_offsets_equal_for_effect(&pointer.offset, &base.offset, assumptions)
    {
        return Some(Bitvector32Term::Constant(0));
    }

    if base.offset == PointerOffsetTerm::Constant(0) {
        return element_index_from_pointer_offset(&pointer.offset, element_width);
    }

    match &pointer.offset {
        PointerOffsetTerm::Add(left, right)
            if left.as_ref() == &base.offset
                || pointer_offsets_equal_for_effect(left, &base.offset, assumptions) =>
        {
            element_index_from_pointer_offset(right, element_width)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &base.offset
                || pointer_offsets_equal_for_effect(right, &base.offset, assumptions) =>
        {
            element_index_from_pointer_offset(left, element_width)
        }
        _ => {
            if let (Some(pointer_index), Some(base_index)) = (
                element_index_from_pointer_offset(&pointer.offset, element_width),
                element_index_from_pointer_offset(&base.offset, element_width),
            ) {
                Some(bitvector_index_relative_to_base(pointer_index, base_index))
            } else {
                None
            }
        }
    }
}

fn pointer_offsets_equal_for_effect(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
    assumptions: &PureFactContext,
) -> bool {
    c_pointer_offsets_proven_equal_for_effect(left, right, assumptions)
}

fn element_index_from_pointer_offset(
    offset: &PointerOffsetTerm,
    element_width: u32,
) -> Option<Bitvector32Term> {
    if element_width == 0 {
        return None;
    }
    match offset {
        PointerOffsetTerm::Constant(offset) if offset % i64::from(element_width) == 0 => {
            let index = offset / i64::from(element_width);
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width }
            if *byte_width == i64::from(element_width) =>
        {
            Some(value.as_ref().clone())
        }
        PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        } if *byte_width == i64::from(element_width) => Some(value.as_ref().clone()),
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            element_index_from_pointer_offset(right, element_width)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            element_index_from_pointer_offset(left, element_width)
        }
        PointerOffsetTerm::Add(left, right) => Some(bitvector32_add(
            element_index_from_pointer_offset(left, element_width)?,
            element_index_from_pointer_offset(right, element_width)?,
        )),
        _ => None,
    }
}
fn bitvector_index_relative_to_base(
    pointer_index: Bitvector32Term,
    base_index: Bitvector32Term,
) -> Bitvector32Term {
    if pointer_index == base_index {
        return Bitvector32Term::Constant(0);
    }
    if let Bitvector32Term::Add(left, right) = &pointer_index {
        if left.as_ref() == &base_index {
            return right.as_ref().clone();
        }
        if right.as_ref() == &base_index {
            return left.as_ref().clone();
        }
    }
    bitvector32_subtract(pointer_index, base_index)
}
