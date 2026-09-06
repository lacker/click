use super::*;

/// Whether a memory fact about `base` established in `range_memory` still
/// describes an available region in `current_memory`: the block must be
/// present in both or absent in both, and no heap allocation that may
/// contain `base` may have been freed in one snapshot but not the other.
/// The second condition is what distinguishes the snapshots for an
/// `ExternalArgument` allocation, whose block survives `free`.
pub(in crate::kernel) fn memory_range_still_available(
    range_memory: &CMemory,
    current_memory: &CMemory,
    base: &Pointer,
) -> bool {
    range_memory == current_memory
        || range_memory.has_block(&base.block) == current_memory.has_block(&base.block)
            && range_memory.freed_heap_allocation_may_contain(base)
                == current_memory.freed_heap_allocation_may_contain(base)
}

pub(in crate::kernel) fn forall_int32(var: Variable, body: Proposition) -> Proposition {
    Proposition::ForAll {
        var,
        sort: Sort::CInt32,
        body: Box::new(body),
    }
}

pub(in crate::kernel) fn wrap_proof_facts(
    proposition: Proposition,
    assumptions: &PureFactContext,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> Proposition {
    let proposition = obligations
        .iter()
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    let proposition = facts
        .iter()
        .filter(|fact| fact.is_public())
        .filter(|fact| !crate::kernel::eval::is_load_variable_defining_fact(fact.proposition()))
        .rev()
        .fold(proposition, |body, fact| {
            Proposition::Implies(Box::new(fact.proposition().clone()), Box::new(body))
        });

    let proposition = assumptions
        .prop_facts
        .iter()
        .rev()
        .fold(proposition, |body, proposition| {
            Proposition::Implies(Box::new(proposition.clone()), Box::new(body))
        });

    assumptions
        .condition_facts
        .iter()
        .rev()
        .fold(proposition, |body, (condition, value)| {
            Proposition::Implies(
                Box::new(Proposition::ConditionIs(condition.clone(), *value)),
                Box::new(body),
            )
        })
}

pub(in crate::kernel) fn wrap_path_context(
    proposition: Proposition,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> Proposition {
    let proposition = obligations
        .iter()
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    facts
        .iter()
        .filter(|fact| {
            // A load-variable defining equation is true by construction;
            // wrapping it as a premise only buries the consequent behind an
            // antecedent every prover then has to discharge.
            !crate::kernel::eval::is_load_variable_defining_fact(fact.proposition())
        })
        .rev()
        .fold(proposition, |body, fact| {
            Proposition::Implies(Box::new(fact.proposition().clone()), Box::new(body))
        })
}

pub(in crate::kernel) fn public_execution_pure_facts(
    facts: &[ExecutionPureFact],
) -> Vec<ExecutionPureFact> {
    facts
        .iter()
        .filter(|fact| fact.is_public())
        .cloned()
        .collect()
}

pub(in crate::kernel) fn memory_effect_execution_facts(
    facts: &[ExecutionPureFact],
) -> Vec<ExecutionPureFact> {
    // Internal memory effects and their theorem-backed provenance must
    // survive the public-fact projection. The latter is planning metadata,
    // not an additional path premise, and is consumed when Click constructs
    // the corresponding explicit transport step.
    facts
        .iter()
        .filter(|fact| {
            fact.transport_theorem().is_some()
                || matches!(
                    fact.proposition(),
                    Proposition::CMemoryMutatesOnly { .. }
                        | Proposition::CMemoryEffectSummary { .. }
                        | Proposition::CHeapAllocationFreed { .. }
                )
        })
        .cloned()
        .collect()
}

pub(in crate::kernel) fn solve_builtin_prop(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
            algebraic_terms_equal(left, right)
        }
        Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) => {
            sequence_terms_equal_by_elements(left, right)
        }
        Proposition::Equal(left, right) => left == right,
        Proposition::ConditionIs(ConditionTerm::Constant(actual), expected) => actual == expected,
        Proposition::And(left, right) => solve_builtin_prop(left) && solve_builtin_prop(right),
        Proposition::Or(left, right) => solve_builtin_prop(left) || solve_builtin_prop(right),
        Proposition::Not(body) => disprove_builtin_prop(body),
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => bytes
            .as_const()
            .is_some_and(|bytes| memory.access_in_bounds(base, bytes)),
        Proposition::CMemoryDisjoint {
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        } => memory_ranges_disjoint_builtin(
            left_base,
            left_start,
            left_end,
            right_base,
            right_start,
            right_end,
        ),
        Proposition::CResourceSeparate { .. } | Proposition::CResourceContains { .. } => false,
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => memory.access_in_bounds(pointer, *byte_width),
        _ => false,
    }
}

fn disprove_builtin_prop(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::Constant(actual), expected) => actual != expected,
        Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) => {
            sequence_terms_definitely_distinct(left, right)
        }
        Proposition::Equal(Term::CValue(left), Term::CValue(right)) => {
            c_values_definitely_distinct(left, right)
        }
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
            algebraic_terms_definitely_distinct(left, right)
        }
        Proposition::And(left, right) => {
            disprove_builtin_prop(left) || disprove_builtin_prop(right)
        }
        Proposition::Or(left, right) => disprove_builtin_prop(left) && disprove_builtin_prop(right),
        Proposition::Not(body) => solve_builtin_prop(body),
        _ => false,
    }
}

fn algebraic_terms_equal(left: &AlgebraicTerm, right: &AlgebraicTerm) -> bool {
    if left.algebraic_type != right.algebraic_type {
        return false;
    }
    match (&left.node, &right.node) {
        (AlgebraicTermNode::Variable(left), AlgebraicTermNode::Variable(right)) => left == right,
        (
            AlgebraicTermNode::Constructor {
                variant: left_variant,
                fields: left_fields,
            },
            AlgebraicTermNode::Constructor {
                variant: right_variant,
                fields: right_fields,
            },
        ) => left_variant == right_variant && left_fields == right_fields,
        _ => false,
    }
}

fn algebraic_terms_definitely_distinct(left: &AlgebraicTerm, right: &AlgebraicTerm) -> bool {
    if left.algebraic_type != right.algebraic_type {
        return true;
    }
    match (&left.node, &right.node) {
        (
            AlgebraicTermNode::Constructor {
                variant: left_variant,
                fields: left_fields,
            },
            AlgebraicTermNode::Constructor {
                variant: right_variant,
                fields: right_fields,
            },
        ) => {
            left_variant != right_variant
                || left_fields.len() != right_fields.len()
                || left_fields
                    .iter()
                    .zip(right_fields)
                    .any(|(left, right)| c_values_definitely_distinct(left, right))
        }
        _ => false,
    }
}

fn sequence_terms_equal_by_elements(left: &SequenceTerm, right: &SequenceTerm) -> bool {
    if let (Some(left_type), Some(right_type)) = (left.element_type, right.element_type)
        && left_type != right_type
    {
        return false;
    }
    let mut left = SequenceElements::new(left);
    let mut right = SequenceElements::new(right);
    loop {
        match (left.next(), right.next()) {
            (Some(left), Some(right)) if left == right => {}
            (None, None) => return true,
            _ => return false,
        }
    }
}

fn sequence_terms_definitely_distinct(left: &SequenceTerm, right: &SequenceTerm) -> bool {
    if let (Some(left_type), Some(right_type)) = (left.element_type, right.element_type)
        && left_type != right_type
    {
        return true;
    }
    let mut left = SequenceElements::new(left);
    let mut right = SequenceElements::new(right);
    loop {
        match (left.next(), right.next()) {
            (Some(left), Some(right)) if c_values_definitely_distinct(left, right) => return true,
            (Some(_), Some(_)) => {}
            (None, None) => return false,
            _ => return true,
        }
    }
}

struct SequenceElements<'a> {
    pending: Vec<&'a SequenceTerm>,
    current: Option<std::slice::Iter<'a, CValue>>,
}

impl<'a> SequenceElements<'a> {
    fn new(sequence: &'a SequenceTerm) -> Self {
        Self {
            pending: vec![sequence],
            current: None,
        }
    }
}

impl<'a> Iterator for SequenceElements<'a> {
    type Item = &'a CValue;

    fn next(&mut self) -> Option<Self::Item> {
        loop {
            if let Some(values) = &mut self.current {
                if let Some(value) = values.next() {
                    return Some(value);
                }
                self.current = None;
            }
            match self.pending.pop()?.node.as_ref() {
                SequenceTermNode::Literal(values) => self.current = Some(values.iter()),
                SequenceTermNode::Concat(left, right) => {
                    self.pending.push(right);
                    self.pending.push(left);
                }
            }
        }
    }
}

fn c_values_definitely_distinct(left: &CValue, right: &CValue) -> bool {
    fn constant(bits: &Bitvector32Term) -> Option<u64> {
        match bits {
            Bitvector32Term::Constant(value) => Some(u64::from(*value)),
            Bitvector32Term::Int64Constant(value) => Some(*value as u64),
            Bitvector32Term::UInt64Constant(value) => Some(*value),
            _ => None,
        }
    }

    match (left, right) {
        (CValue::Int16(left), CValue::Int16(right))
        | (CValue::Int32(left), CValue::Int32(right))
        | (CValue::UInt8(left), CValue::UInt8(right))
        | (CValue::UInt16(left), CValue::UInt16(right))
        | (CValue::UInt32(left), CValue::UInt32(right))
        | (CValue::Int64(left), CValue::Int64(right))
        | (CValue::UInt64(left), CValue::UInt64(right)) => {
            matches!((constant(left), constant(right)), (Some(left), Some(right)) if left != right)
        }
        _ => false,
    }
}

#[cfg(test)]
mod sequence_equality_tests {
    use super::*;

    fn singleton(value: u32) -> SequenceTerm {
        SequenceTerm {
            element_type: Some(CType::Int32),
            node: std::sync::Arc::new(SequenceTermNode::Literal(
                vec![crate::kernel::api::int32(value)].into(),
            )),
        }
    }

    fn concatenate(left: SequenceTerm, right: SequenceTerm) -> SequenceTerm {
        SequenceTerm {
            element_type: Some(CType::Int32),
            node: std::sync::Arc::new(SequenceTermNode::Concat(left, right)),
        }
    }

    #[test]
    fn associative_sequence_equality_is_iterative_across_rope_shapes() {
        for size in [8u32, 64, 512] {
            let mut left_associated = singleton(0);
            for value in 1..size {
                left_associated = concatenate(left_associated, singleton(value));
            }

            let mut right_associated = singleton(size - 1);
            for value in (0..size - 1).rev() {
                right_associated = concatenate(singleton(value), right_associated);
            }

            assert!(solve_builtin_prop(&Proposition::Equal(
                Term::Sequence(left_associated),
                Term::Sequence(right_associated),
            )));
        }
    }
}

pub(in crate::kernel) fn memory_ranges_disjoint_builtin(
    left_base: &Pointer,
    left_start: &Bitvector32Term,
    left_end: &Bitvector32Term,
    right_base: &Pointer,
    right_start: &Bitvector32Term,
    right_end: &Bitvector32Term,
) -> bool {
    if left_base.blocks_proven_distinct(right_base) {
        return true;
    }

    let Some(left_base_index) = left_base.element_index_from_base(&Pointer {
        block: left_base.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    }) else {
        return false;
    };
    let Some(right_base_index) = right_base.element_index_from_base(&Pointer {
        block: right_base.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    }) else {
        return false;
    };
    let (Some(left_base_index), Some(left_start), Some(left_end)) = (
        signed_bitvector_constant(&left_base_index),
        signed_bitvector_constant(left_start),
        signed_bitvector_constant(left_end),
    ) else {
        return false;
    };
    let (Some(right_base_index), Some(right_start), Some(right_end)) = (
        signed_bitvector_constant(&right_base_index),
        signed_bitvector_constant(right_start),
        signed_bitvector_constant(right_end),
    ) else {
        return false;
    };

    let left_start = left_base_index + left_start;
    let left_end = left_base_index + left_end;
    let right_start = right_base_index + right_start;
    let right_end = right_base_index + right_end;
    left_end <= right_start || right_end <= left_start
}

pub(in crate::kernel) fn element_index_from_offset(
    offset: &PointerOffsetTerm,
    element_width: u32,
) -> Option<Bitvector32Term> {
    if element_width == 0 {
        return None;
    }
    match offset {
        PointerOffsetTerm::Add(left, right) if left.as_ref() == &PointerOffsetTerm::Constant(0) => {
            element_index_from_offset(right, element_width)
        }
        PointerOffsetTerm::Add(left, right)
            if right.as_ref() == &PointerOffsetTerm::Constant(0) =>
        {
            element_index_from_offset(left, element_width)
        }
        PointerOffsetTerm::Add(left, right) => Some(Bitvector32Term::add(
            element_index_from_offset(left, element_width)?,
            element_index_from_offset(right, element_width)?,
        )),
        PointerOffsetTerm::Int32Scaled { value, byte_width }
            if *byte_width == i64::from(element_width) =>
        {
            Some(value.as_ref().clone())
        }
        PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        } if *byte_width == i64::from(element_width) => Some(value.as_ref().clone()),
        PointerOffsetTerm::Constant(offset) if offset % i64::from(element_width) == 0 => {
            let index = offset / i64::from(element_width);
            (i32::MIN as i64..=i32::MAX as i64)
                .contains(&index)
                .then_some(Bitvector32Term::Constant((index as i32) as u32))
        }
        _ => None,
    }
}

pub(in crate::kernel) fn int32_element_index_from_offset(
    offset: &PointerOffsetTerm,
) -> Option<Bitvector32Term> {
    element_index_from_offset(offset, 4)
}

pub(in crate::kernel) fn common_pointer_offset_element_width(
    left: &PointerOffsetTerm,
    right: &PointerOffsetTerm,
) -> Option<u32> {
    fn offset_element_width(offset: &PointerOffsetTerm) -> Option<u32> {
        match offset {
            PointerOffsetTerm::Int32Scaled { byte_width, .. }
            | PointerOffsetTerm::Int64Scaled { byte_width, .. } => {
                u32::try_from(*byte_width).ok().filter(|width| *width > 0)
            }
            PointerOffsetTerm::Add(left, right) => {
                match (offset_element_width(left), offset_element_width(right)) {
                    (Some(left), Some(right)) if left == right => Some(left),
                    (Some(width), None) | (None, Some(width)) => Some(width),
                    (None, None) => None,
                    _ => None,
                }
            }
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => None,
        }
    }

    match (offset_element_width(left), offset_element_width(right)) {
        (Some(left), Some(right)) if left == right => Some(left),
        (Some(width), None) | (None, Some(width)) => Some(width),
        _ => None,
    }
}

pub(in crate::kernel) fn pointer_byte_offset_from_base(
    pointer: &Pointer,
    base: &Pointer,
) -> Option<Bitvector32Term> {
    if pointer.block != base.block {
        return None;
    }
    if pointer.offset == base.offset {
        return Some(Bitvector32Term::Constant(0));
    }
    if base.offset == PointerOffsetTerm::Constant(0) {
        return byte_offset_from_pointer_offset(&pointer.offset);
    }

    // Pointer arithmetic is represented as a binary tree. A field access
    // after an indexed access therefore has the shape
    // `((base + stride) + field)`, rather than a single addition whose left
    // child is exactly `base`. Walk the additive tree so the common base is
    // cancelled before constructing the byte offset; this keeps resource
    // checks independent of harmless grouping differences in pointer
    // arithmetic.
    fn offset_from_nested_base(
        offset: &PointerOffsetTerm,
        base: &PointerOffsetTerm,
    ) -> Option<Bitvector32Term> {
        if offset == base {
            return Some(Bitvector32Term::Constant(0));
        }
        let PointerOffsetTerm::Add(left, right) = offset else {
            return None;
        };
        if left.as_ref() == base {
            return byte_offset_from_pointer_offset(right);
        }
        if right.as_ref() == base {
            return byte_offset_from_pointer_offset(left);
        }
        if let Some(left_offset) = offset_from_nested_base(left, base) {
            return Some(Bitvector32Term::add(
                left_offset,
                byte_offset_from_pointer_offset(right)?,
            ));
        }
        if let Some(right_offset) = offset_from_nested_base(right, base) {
            return Some(Bitvector32Term::add(
                byte_offset_from_pointer_offset(left)?,
                right_offset,
            ));
        }
        None
    }

    offset_from_nested_base(&pointer.offset, &base.offset).or_else(|| {
        let pointer_offset = byte_offset_from_pointer_offset(&pointer.offset)?;
        let base_offset = byte_offset_from_pointer_offset(&base.offset)?;
        Some(Bitvector32Term::subtract(pointer_offset, base_offset))
    })
}

pub(in crate::kernel) fn byte_offset_from_pointer_offset(
    offset: &PointerOffsetTerm,
) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(offset) => (i32::MIN as i64..=i32::MAX as i64)
            .contains(offset)
            .then_some(Bitvector32Term::Constant((*offset as i32) as u32)),
        PointerOffsetTerm::Add(left, right) => Some(Bitvector32Term::add(
            byte_offset_from_pointer_offset(left)?,
            byte_offset_from_pointer_offset(right)?,
        )),
        PointerOffsetTerm::Int32Scaled { value, byte_width }
        | PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        } => {
            let width = u32::try_from(*byte_width).ok()?;
            match width {
                0 => Some(Bitvector32Term::Constant(0)),
                1 => Some(value.as_ref().clone()),
                _ => Some(Bitvector32Term::Multiply(
                    Box::new(value.as_ref().clone()),
                    Box::new(Bitvector32Term::Constant(width)),
                )),
            }
        }
        PointerOffsetTerm::Variable(_) => None,
    }
}

pub(in crate::kernel) fn element_count_from_bytes(
    bytes: &Bitvector32Term,
    element_width: u32,
) -> Option<Bitvector32Term> {
    if element_width == 0 {
        return None;
    }
    if element_width == 1 {
        return Some(bytes.clone());
    }
    let element_width = Bitvector32Term::Constant(element_width);
    match bytes {
        Bitvector32Term::Multiply(left, right) if right.as_ref() == &element_width => {
            Some(left.as_ref().clone())
        }
        Bitvector32Term::Multiply(left, right) if left.as_ref() == &element_width => {
            Some(right.as_ref().clone())
        }
        Bitvector32Term::Constant(bytes) if bytes % element_width.as_const()? == 0 => {
            Some(Bitvector32Term::Constant(bytes / element_width.as_const()?))
        }
        _ => None,
    }
}

pub(in crate::kernel) fn int32_element_count_from_bytes(
    bytes: &Bitvector32Term,
) -> Option<Bitvector32Term> {
    element_count_from_bytes(bytes, 4)
}

pub(in crate::kernel) fn signed_const_add(
    term: &Bitvector32Term,
    addend: u32,
) -> Option<Bitvector32Term> {
    let addend = i32::try_from(addend).ok()?;
    let sum = (term.as_const()? as i32).checked_add(addend)?;
    Some(Bitvector32Term::Constant(sum as u32))
}

pub(in crate::kernel) fn add_path_fact(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    proposition: Proposition,
) -> Option<()> {
    add_path_fact_with_visibility(facts, assumptions, proposition, true)
}

pub(in crate::kernel) fn add_path_fact_with_visibility(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    public: bool,
) -> Option<()> {
    add_path_fact_with_visibility_after_effect(facts, assumptions, proposition, public, false)
}

fn add_path_fact_with_visibility_after_effect(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    public: bool,
    certified_after_effect: bool,
) -> Option<()> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        return add_condition_path_fact_with_visibility(
            facts,
            assumptions,
            condition,
            value,
            public,
            certified_after_effect,
        );
    }

    if assumptions.proves(&proposition) || facts.iter().any(|fact| fact.proposition == proposition)
    {
        return Some(());
    }

    facts.push(if public {
        ExecutionPureFact::new(proposition)
    } else {
        ExecutionPureFact::internal(proposition)
    });
    Some(())
}

pub(in crate::kernel) fn add_condition_path_fact(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, true, false)
}

pub(in crate::kernel) fn add_internal_condition_path_fact(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, false, false)
}

fn add_condition_path_fact_with_visibility(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
    public: bool,
    certified_after_effect: bool,
) -> Option<()> {
    // A fact certified after a memory effect is part of that transition's
    // public post-state, even when the pre-effect assumptions can derive the
    // same truth value. Dropping it here loses the exact snapshot fact that a
    // later statement (and its surface certificate) may require.
    if let Some(known) = assumptions.exact_condition_value(&condition) {
        if known == value && !certified_after_effect {
            return Some(());
        }
        if known != value && !certified_after_effect {
            return None;
        }
    }
    if let Some(known) = PureFactContext::decide_intrinsically(&condition) {
        return (known == value).then_some(());
    }
    if !assumptions.should_defer_non_exact_condition_reasoning()
        && let Some(known) = assumptions.decide(&condition)
    {
        if known == value && !certified_after_effect {
            return Some(());
        }
        if known != value && !certified_after_effect {
            return None;
        }
    }

    if let Some(existing) = facts
        .iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::ConditionIs(existing_condition, existing_value)
                if existing_condition == &condition =>
            {
                Some(*existing_value)
            }
            _ => None,
        })
        .next()
    {
        return (existing == value).then_some(());
    }

    let proposition = Proposition::ConditionIs(condition, value);
    facts.push(if public {
        ExecutionPureFact::new(proposition)
    } else {
        ExecutionPureFact::internal(proposition)
    });
    Some(())
}

pub(in crate::kernel) fn add_pointer_offset_equality_execution_pure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    left: PointerOffsetTerm,
    right: PointerOffsetTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact(
        facts,
        assumptions,
        ConditionTerm::pointer_offset_equal(left.clone(), right.clone()),
        value,
    )?;

    if let (Some(left_index), Some(right_index)) = (
        int32_element_index_from_offset(&left),
        int32_element_index_from_offset(&right),
    ) {
        add_condition_path_fact(
            facts,
            assumptions,
            ConditionTerm::equal(left_index, right_index),
            value,
        )?;
    }

    Some(())
}

pub(in crate::kernel) fn add_proof_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
) -> Option<()> {
    add_proof_obligation_with_context(obligations, assumptions, proposition, None)
}

pub(in crate::kernel) fn add_proof_obligation_with_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
) -> Option<()> {
    if let Proposition::ConditionIs(condition, value) = proposition {
        return add_condition_obligation(obligations, assumptions, condition, value, context);
    }

    let defer_contextual_proof = assumptions.should_defer_non_exact_loadability_obligations()
        && matches!(proposition, Proposition::CMemoryLoadable { .. });
    if assumptions.proves_exact(&proposition)
        || !defer_contextual_proof && assumptions.proves(&proposition)
        || obligations
            .iter()
            .any(|obligation| obligation.proposition == proposition)
    {
        return Some(());
    }

    let obligation = ProofObligation::new(proposition);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
    Some(())
}

pub(in crate::kernel) fn add_required_proof_obligation_with_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
) {
    if assumptions.proves(&proposition)
        || obligations
            .iter()
            .any(|obligation| obligation.proposition == proposition)
    {
        return;
    }

    let obligation = ProofObligation::verification_condition(proposition);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
}

pub(in crate::kernel) fn add_required_proof_obligation_without_search(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
) {
    if assumptions.proves_exact(&proposition)
        || obligations
            .iter()
            .any(|obligation| obligation.proposition == proposition)
    {
        return;
    }
    let obligation = ProofObligation::new(proposition);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
}

pub(in crate::kernel) fn append_required_proof_obligations(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    new_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_with_context(
            obligations,
            assumptions,
            obligation.proposition().clone(),
            obligation.context(),
        );
    }
}

pub(in crate::kernel) fn append_required_proof_obligations_without_search(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    new_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_without_search(
            obligations,
            assumptions,
            obligation.proposition().clone(),
            obligation.context(),
        );
    }
}

pub(in crate::kernel) fn append_required_proof_obligations_under_path_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    new_obligations: &[ProofObligation],
    facts: &[ExecutionPureFact],
    context_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_with_context(
            obligations,
            assumptions,
            wrap_path_context(obligation.proposition().clone(), facts, context_obligations),
            obligation.context(),
        );
    }
}

pub(in crate::kernel) fn add_condition_obligation(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
    context: Option<&str>,
) -> Option<()> {
    if assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), value)) {
        return Some(());
    }
    if assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), !value)) {
        return None;
    }
    if let Some(known) = PureFactContext::decide_intrinsically(&condition) {
        return (known == value).then_some(());
    }
    if !assumptions.should_defer_non_exact_condition_reasoning()
        && let Some(known) = assumptions.decide(&condition)
    {
        return (known == value).then_some(());
    }

    if let Some(existing) = obligations
        .iter()
        .filter_map(|obligation| match obligation.proposition() {
            Proposition::ConditionIs(existing_condition, existing_value)
                if existing_condition == &condition =>
            {
                Some(*existing_value)
            }
            _ => None,
        })
        .next()
    {
        return (existing == value).then_some(());
    }

    let obligation = ProofObligation::condition(condition, value);
    obligations.push(match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    });
    Some(())
}

pub(in crate::kernel) fn merge_obligations(
    left: &[ProofObligation],
    right: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<Vec<ProofObligation>> {
    let mut obligations = left.to_vec();
    for obligation in right {
        if obligation.is_assumable() {
            // `right` was produced while executing under the complete left
            // path context. Preserve its path guard without asking the
            // general prover to reconsider it against an older memory
            // snapshot. Exact and intrinsic contradictions still reject the
            // merge; non-exact cross-snapshot reasoning cannot erase a path
            // that the executor just certified as possible.
            if assumptions.proves_exact(obligation.proposition())
                || obligations
                    .iter()
                    .any(|existing| existing.proposition() == obligation.proposition())
            {
                continue;
            }
            if let Proposition::ConditionIs(condition, value) = obligation.proposition()
                && (assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), !*value))
                    || PureFactContext::decide_intrinsically(condition)
                        .is_some_and(|known| known != *value)
                    || obligations.iter().any(|existing| {
                        matches!(
                            existing.proposition(),
                            Proposition::ConditionIs(existing_condition, existing_value)
                                if existing_condition == condition && existing_value != value
                        )
                    }))
            {
                return None;
            }
            obligations.push(obligation.clone());
        } else {
            // A required obligation was already tested against the path
            // context that created it.  Merging path fragments must preserve
            // that verification condition, not rerun the general prover
            // against an older base context.  The latter cannot discharge a
            // new obligation and becomes catastrophically expensive as
            // verified-call chains accumulate implication facts.
            add_required_proof_obligation_without_search(
                &mut obligations,
                assumptions,
                obligation.proposition().clone(),
                obligation.context(),
            );
        }
    }
    Some(obligations)
}

pub(in crate::kernel) fn merge_facts(
    left: &[ExecutionPureFact],
    right: &[ExecutionPureFact],
    assumptions: &PureFactContext,
) -> Option<Vec<ExecutionPureFact>> {
    let mut facts = left.to_vec();
    let mut saw_memory_effect = false;
    for fact in right {
        add_path_fact_with_visibility_after_effect(
            &mut facts,
            assumptions,
            fact.proposition().clone(),
            fact.is_public(),
            saw_memory_effect && fact.is_certified(),
        )?;
        if fact.is_certified()
            && let Some(existing) = facts
                .iter_mut()
                .find(|existing| existing.proposition() == fact.proposition())
        {
            *existing = fact.clone();
        }
        // A verified call emits its effect before its certified
        // postconditions. Entry-state condition facts cannot reject those
        // theorem-backed postconditions after memory has changed, although
        // agreeing entry facts can still make a postcondition redundant.
        if matches!(
            fact.proposition(),
            Proposition::CMemoryMutatesOnly { .. }
                | Proposition::CMemoryEffectSummary { .. }
                | Proposition::CHeapAllocationFreed { .. }
        ) {
            saw_memory_effect = true;
        }
    }
    Some(facts)
}

pub(in crate::kernel) fn merge_execution_pure_facts_and_obligations(
    left_facts: &[ExecutionPureFact],
    left_obligations: &[ProofObligation],
    right_facts: &[ExecutionPureFact],
    right_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<ExecutionPureFact>, Vec<ProofObligation>)> {
    let facts = merge_facts(left_facts, right_facts, assumptions)?;
    // The right fragment was executed under the left fragment's path
    // context. Recheck its assumable obligations against that same context,
    // not against the older base assumptions. In particular, a verified call
    // can change a field that an entry-state branch constrained; checking a
    // post-call load guard against only the entry snapshot can incorrectly
    // discard a valid successor path.
    let prefix_assumptions =
        assumptions_with_path_context(assumptions, left_facts, left_obligations);
    let obligations = merge_obligations(left_obligations, right_obligations, &prefix_assumptions)?;
    Some((facts, obligations))
}

pub(in crate::kernel) fn decide_with_facts(
    assumptions: &PureFactContext,
    facts: &[ExecutionPureFact],
    condition: &ConditionTerm,
) -> Option<bool> {
    [true, false]
        .into_iter()
        .find(|value| {
            assumptions.proves_exact(&Proposition::ConditionIs(condition.clone(), *value))
        })
        .or_else(|| PureFactContext::decide_intrinsically(condition))
        .or_else(|| {
            (!assumptions.should_defer_non_exact_condition_reasoning())
                .then(|| assumptions.decide(condition))
                .flatten()
        })
        .or_else(|| {
            facts.iter().find_map(|fact| match fact.proposition() {
                Proposition::ConditionIs(existing_condition, value)
                    if existing_condition == condition =>
                {
                    Some(*value)
                }
                _ => None,
            })
        })
        .or_else(|| {
            facts
                .iter()
                .fold(
                    if assumptions.should_defer_non_exact_condition_reasoning() {
                        PureFactContext::new()
                    } else {
                        assumptions.clone()
                    },
                    |assumptions, fact| assumptions.assume_proposition(fact.proposition().clone()),
                )
                .decide(condition)
        })
}

pub(in crate::kernel) fn assumptions_with_path_context(
    assumptions: &PureFactContext,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> PureFactContext {
    let mut assumptions = assumptions.clone();
    for fact in facts {
        assumptions = assumptions.assume_proposition(fact.proposition().clone());
    }
    for obligation in obligations {
        if obligation.is_assumable() {
            assumptions = assumptions.assume_proposition(obligation.proposition().clone());
        }
    }
    assumptions
}

pub(in crate::kernel) fn assumptions_with_propositions(
    assumptions: &PureFactContext,
    propositions: &[Proposition],
) -> PureFactContext {
    let mut assumptions = assumptions.clone();
    for proposition in propositions {
        assumptions = assumptions.assume_proposition(proposition.clone());
    }
    assumptions
}
