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
            && range_memory.is_ended_local_address(base)
                == current_memory.is_ended_local_address(base)
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

/// Why one node at the head of a lowered proposition exists.
///
/// Lowering is not an isomorphism from written Surface syntax to kernel
/// propositions: it inserts `Implies` nodes that no Surface connective
/// wrote, guarding a body with a path fact the lowering established or with
/// a load obligation the state did not discharge. A proof step that
/// introduces the head of a lowered goal must know which kind of node it is
/// reaching, because only a written connective consumes a written Surface
/// connective, and a written universal binds a written Surface name to the
/// exact kernel variable the lowering chose.
///
/// One value describes one node. The head chain of a lowered proposition,
/// outermost first, is a [`LoweringIntroductions`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LoweringIntroduction {
    /// An `Implies` inserted by lowering to guard the body with a path fact
    /// the lowering established. No Surface connective corresponds to it.
    PathFactGuard,
    /// An `Implies` inserted by lowering to guard the body with a path
    /// obligation. No Surface connective corresponds to it.
    ObligationGuard,
    /// An `Implies` written as a spec, and therefore Surface, implication.
    WrittenImplication,
    /// A `Not` written as a spec, and therefore Surface, negation.
    WrittenNegation,
    /// A `Not` introduced by lowering a written `!=` comparison. The source
    /// has no separate negation connective to consume.
    ComparisonNegation,
    /// A `ForAll` written as a spec, and therefore Surface, universal.
    /// `name` is the written binder spelling and `variable` is the exact
    /// kernel variable the lowering bound it to.
    WrittenUniversal {
        name: String,
        variable: Variable,
        pointer: bool,
        integer: bool,
    },
}

/// The head chain of a lowered proposition, outermost first: one entry per
/// node a proposition introduction can reach before any other step. A negation
/// ends the chain: introducing it assumes its body and leaves a false goal.
pub type LoweringIntroductions = Vec<LoweringIntroduction>;

pub(in crate::kernel) fn wrap_path_context(
    proposition: Proposition,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> Proposition {
    wrap_path_context_with_introductions(proposition, facts, obligations).0
}

/// Guards an existentially quantified body with the path facts the lowering
/// of that body established.
///
/// A path fact may mention the quantified variable, so it belongs under the
/// binder that binds it, exactly as [`wrap_path_context`] puts it under a
/// universal. The polarity is the other one: a guard restricts a universal's
/// domain, so it is the antecedent of an implication, and it restricts an
/// existential's witness, so it is a conjunct. Guarding an existential by
/// implication instead would make the claim vacuously true of any witness the
/// guard excludes.
///
/// Work is one traversal of `facts` under the same filter `wrap_path_context`
/// uses, so the two cannot disagree about which facts are retained.
pub(in crate::kernel) fn guard_quantified_witness(
    proposition: Proposition,
    facts: &[ExecutionPureFact],
) -> Proposition {
    facts
        .iter()
        .filter(|fact| !crate::kernel::eval::is_load_variable_defining_fact(fact.proposition()))
        .rev()
        .fold(proposition, |body, fact| {
            Proposition::And(Box::new(fact.proposition().clone()), Box::new(body))
        })
}

/// [`wrap_path_context`], also reporting the guard nodes it inserted, in the
/// order they appear from the outside in. Both results come from one
/// traversal under one filter, so the record cannot drift from the
/// proposition it describes.
pub(in crate::kernel) fn wrap_path_context_with_introductions(
    proposition: Proposition,
    facts: &[ExecutionPureFact],
    obligations: &[ProofObligation],
) -> (Proposition, LoweringIntroductions) {
    let proposition = obligations
        .iter()
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    // A load-variable defining equation is true by construction;
    // wrapping it as a premise only buries the consequent behind an
    // antecedent every prover then has to discharge.
    let retained = || {
        facts
            .iter()
            .filter(|fact| !crate::kernel::eval::is_load_variable_defining_fact(fact.proposition()))
    };

    let introductions = retained()
        .map(|_| LoweringIntroduction::PathFactGuard)
        .chain(
            obligations
                .iter()
                .map(|_| LoweringIntroduction::ObligationGuard),
        )
        .collect();

    let proposition = retained().rev().fold(proposition, |body, fact| {
        Proposition::Implies(Box::new(fact.proposition().clone()), Box::new(body))
    });

    (proposition, introductions)
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

pub(crate) fn solve_builtin_prop(proposition: &Proposition) -> bool {
    match proposition {
        Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
            algebraic_terms_equal(left, right)
        }
        Proposition::Equal(Term::Integer(left), Term::Integer(right)) => left == right,
        Proposition::Equal(Term::Sequence(left), Term::Sequence(right)) => {
            sequence_terms_equal_by_elements(left, right)
        }
        Proposition::Equal(left, right) => left == right,
        Proposition::ConditionIs(ConditionTerm::Constant(actual), expected) => actual == expected,
        Proposition::And(left, right) => solve_builtin_prop(left) && solve_builtin_prop(right),
        Proposition::Or(left, right) => solve_builtin_prop(left) || solve_builtin_prop(right),
        Proposition::Not(body) => {
            disprove_builtin_prop(body) || conjunction_order_facts_are_inconsistent(body)
        }
        // A guarded proposition is true wherever its guard has no model, and
        // a universal over one is true for the arbitrary binder. Only the
        // unsatisfiable-guard case is decided here; a guard that may hold
        // keeps its consequent as an ordinary obligation.
        Proposition::Implies(antecedent, _) => conjunction_order_facts_are_inconsistent(antecedent),
        Proposition::ForAll { body, .. } => {
            matches!(body.as_ref(), Proposition::Implies(antecedent, _)
                if conjunction_order_facts_are_inconsistent(antecedent))
        }
        Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
        } => bytes
            .as_const()
            .is_some_and(|bytes| memory.access_in_bounds(base, bytes)),
        Proposition::CResourceSeparate { .. } | Proposition::CResourceContains { .. } => false,
        Proposition::CMemoryCanStore {
            memory,
            pointer,
            byte_width,
        } => memory.access_in_bounds(pointer, *byte_width),
        _ => false,
    }
}

/// A conjunction of signed order facts with no model, such as the guard
/// `t <= k and k < t` of a universal whose range is empty at a loop entry.
/// The check reads only the conjunction's own order facts. A cycle through
/// constants only (`0 <= k and k < 0`) is deliberately not decided here:
/// constant ranges keep their finite-range treatment, whose `enumerate`
/// certificates written proofs rely on.
pub(in crate::kernel) fn conjunction_order_facts_are_inconsistent(
    proposition: &Proposition,
) -> bool {
    let mut facts = Vec::new();
    super::order_reasoning::collect_order_facts_from_assumed_proposition(proposition, &mut facts);
    facts.len() >= 2 && super::order_reasoning::order_facts_form_strict_cycle(&facts)
}

pub(in crate::kernel) fn disprove_builtin_prop(proposition: &Proposition) -> bool {
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
        Proposition::Equal(Term::Integer(left), Term::Integer(right)) => left != right,
        Proposition::And(left, right) => {
            disprove_builtin_prop(left) || disprove_builtin_prop(right)
        }
        Proposition::Or(left, right) => disprove_builtin_prop(left) && disprove_builtin_prop(right),
        Proposition::Not(body) => solve_builtin_prop(body),
        _ => false,
    }
}

fn algebraic_terms_equal(left: &AlgebraicTerm, right: &AlgebraicTerm) -> bool {
    if !left.is_well_formed()
        || !right.is_well_formed()
        || left.algebraic_type != right.algebraic_type
    {
        return false;
    }
    // Reflexivity applies to opaque applications and symbolic matches too.
    // This checks exact terms, not injectivity or evaluation of pure calls.
    left.node == right.node
}

fn algebraic_terms_definitely_distinct(left: &AlgebraicTerm, right: &AlgebraicTerm) -> bool {
    if !left.is_well_formed() || !right.is_well_formed() {
        return false;
    }
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
                    .any(|(left, right)| match (left, right) {
                        (AlgebraicValue::C(left), AlgebraicValue::C(right)) => {
                            c_values_definitely_distinct(left, right)
                        }
                        (AlgebraicValue::Algebraic(left), AlgebraicValue::Algebraic(right)) => {
                            algebraic_terms_definitely_distinct(left, right)
                        }
                        _ => true,
                    })
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

/// An element delta split so that it is *exact*: the true delta in `i64` is
/// `sext(index) + constant`.
///
/// [`element_index_from_offset`] answers with one `Bitvector32Term`, and that
/// is a lossy answer for anything but an equality. A byte offset is
/// mathematical `i64` — [`PointerOffsetTerm::scale_int32`] sign-extends its
/// index before scaling, and `Add` adds exactly — while a `Bitvector32Term` is
/// modular, so collapsing a sum of offsets into [`Bitvector32Term::add`] keeps
/// the delta only *modulo* `2^32`. A membership or order conclusion drawn from
/// such a term would be reading a residue as a number.
///
/// Keeping the constant part in `i64` beside the index loses nothing and wraps
/// nothing: every constant byte displacement a struct field or a fixed array
/// subscript contributes lands here, exactly, and only a *second* symbolic
/// index would need an add this cannot do.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct ExactElementDelta {
    /// The one symbolic element index in the delta, or `Constant(0)` when the
    /// delta is wholly constant. Its *signed* value is part of the delta.
    pub(in crate::kernel) index: Bitvector32Term,
    /// The exact constant part, in elements. Not reduced to `i32`: a delta far
    /// outside `i32` is still an exact delta, and refusing it here would be a
    /// silent truncation.
    pub(in crate::kernel) constant: i64,
}

impl ExactElementDelta {
    /// The delta of a wholly constant number of elements.
    fn constant(constant: i64) -> Self {
        Self {
            index: Bitvector32Term::Constant(0),
            constant,
        }
    }

    /// The zero delta: a pointer at its base.
    pub(in crate::kernel) fn zero() -> Self {
        Self::constant(0)
    }

    /// This delta as one `Bitvector32Term` whose *signed* value is the delta,
    /// for a caller that states it as an ordinary index bound. `None` when the
    /// two parts cannot be joined without a modular add, which a symbolic index
    /// beside a nonzero constant cannot.
    pub(in crate::kernel) fn as_index_term(&self) -> Option<Bitvector32Term> {
        if self.constant == 0 {
            return Some(self.index.clone());
        }
        if !self.is_constant() {
            return None;
        }
        i32::try_from(self.constant)
            .ok()
            .map(|constant| Bitvector32Term::Constant(constant as u32))
    }

    /// Whether this delta names no symbolic index, so its `i64` value is the
    /// whole of it.
    pub(in crate::kernel) fn is_constant(&self) -> bool {
        self.index == Bitvector32Term::Constant(0)
    }

    /// The two deltas added, when at most one of them is symbolic. Two
    /// symbolic indices would need a modular add, which is the loss this type
    /// exists to avoid.
    fn add(self, other: Self) -> Option<Self> {
        let index = match (self.is_constant(), other.is_constant()) {
            (_, true) => self.index,
            (true, false) => other.index,
            (false, false) => return None,
        };
        Some(Self {
            index,
            constant: self.constant.checked_add(other.constant)?,
        })
    }

    /// `self - other`, when the subtraction stays exact: either the subtrahend
    /// is constant, or the two symbolic indices cancel.
    ///
    /// Two indices cancel only when their difference is the true one and not a
    /// residue — `4 * i + 3` is three elements above `i + i + i + i` only while
    /// the scaling does not wrap — so the cancellation goes through the same
    /// [`crate::kernel::assumptions::exact_affine_index_difference`] every other
    /// membership conclusion uses, and answers `None` without the premise it
    /// needs.
    pub(in crate::kernel) fn subtract(
        self,
        other: Self,
        assumptions: Option<&PureFactContext>,
    ) -> Option<Self> {
        let constant = self.constant.checked_sub(other.constant)?;
        if other.is_constant() {
            return Some(Self {
                index: self.index,
                constant,
            });
        }
        if let Some(difference) = crate::kernel::assumptions::exact_affine_index_difference(
            &self.index,
            &other.index,
            assumptions,
        ) {
            return difference.checked_add(constant).map(Self::constant);
        }
        // Two indices with no constant difference between them. Their modular
        // difference still names the delta while neither is negative, since
        // `sext(a) - sext(b)` then lies in `(-2^31, 2^31)` and the 32-bit
        // subtraction is the subtraction. That is the premise a range restated
        // in another base's coordinates as `b - a` needs, and without it the
        // restated start and the real delta can sit `2^32` elements apart.
        (crate::kernel::assumptions::element_index_is_nonnegative(&self.index, assumptions)
            && crate::kernel::assumptions::element_index_is_nonnegative(&other.index, assumptions))
        .then(|| Self {
            index: Bitvector32Term::subtract(self.index, other.index),
            constant,
        })
    }
}

/// [`element_index_from_offset`] for a caller that needs the delta's value and
/// not merely its residue. See [`ExactElementDelta`].
pub(in crate::kernel) fn exact_element_delta_from_offset(
    offset: &PointerOffsetTerm,
    element_width: u32,
) -> Option<ExactElementDelta> {
    if element_width == 0 {
        return None;
    }
    match offset {
        PointerOffsetTerm::Add(left, right) => {
            exact_element_delta_from_offset(left, element_width)?
                .add(exact_element_delta_from_offset(right, element_width)?)
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width }
            if *byte_width == i64::from(element_width) =>
        {
            Some(ExactElementDelta {
                index: value.as_ref().clone(),
                constant: 0,
            })
        }
        PointerOffsetTerm::Constant(offset) if offset % i64::from(element_width) == 0 => Some(
            ExactElementDelta::constant(offset / i64::from(element_width)),
        ),
        // An `Int64Scaled` index scales its *64-bit* value, which is not the
        // signed value of the 32-bit term holding it, so the term cannot stand
        // for the delta. A constant one has already been folded into
        // `Constant` by `scale_int64`.
        PointerOffsetTerm::Constant(_)
        | PointerOffsetTerm::Variable(_)
        | PointerOffsetTerm::Int32Scaled { .. }
        | PointerOffsetTerm::Int64Scaled { .. } => None,
    }
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

    // Redundant-fact suppression is an exact test only. A general proof that
    // the path fact already follows is proof search inside lowering; keeping
    // the fact instead costs one fact-store entry and keeps the path's public
    // post-state exact.
    if assumptions.proves_exact(&proposition)
        || facts.iter().any(|fact| fact.proposition == proposition)
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

    // Obligation suppression keeps two routes: the exact fact index, and the
    // retained atomic memory/resource checkers for a proposition that is
    // already one of those atomic shapes. A proposition with logical
    // structure is emitted as an obligation instead of being discharged by a
    // proof search inside lowering.
    let defer_contextual_proof = assumptions.should_defer_non_exact_loadability_obligations()
        && matches!(proposition, Proposition::CMemoryLoadable { .. });
    if assumptions.proves_exact(&proposition)
        || !defer_contextual_proof && assumptions.proves_atomic_memory_or_resource(&proposition)
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

/// Whether `proposition` is one bare condition that the frozen condition
/// checker already decides with the value it asserts.
///
/// This is the migration's sanctioned replacement for a general prover call
/// on a bare `ConditionIs`: it adds no theory, traverses no logical
/// structure, and answers nothing about a proposition of any other shape.
fn bare_condition_is_decided(assumptions: &PureFactContext, proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return false;
    };
    if PureFactContext::decide_intrinsically(condition) == Some(*value) {
        return true;
    }
    !assumptions.should_defer_non_exact_condition_reasoning()
        && assumptions.decide(condition) == Some(*value)
}

/// Whether a required verification condition is already discharged by one of
/// the routes the kernel retains: the exact fact index, the frozen condition
/// checker on a proposition that is already one bare condition, or the
/// retained atomic memory/resource checkers.
///
/// This is the complete suppression rule for a required obligation. A
/// proposition with logical structure is never discharged here; it is emitted
/// for an ordinary Surface tactic to prove.
pub(in crate::kernel) fn required_obligation_is_exactly_discharged(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    assumptions.states_required_goal(proposition)
        || assumptions.proves_exact(proposition)
        || bare_condition_is_decided(assumptions, proposition)
        || assumptions.proves_atomic_memory_or_resource(proposition)
}

/// Emits one required verification condition, carrying the head chain the
/// lowering that built `proposition` recorded for it when there is one.
pub(in crate::kernel) fn add_required_proof_obligation_with_context(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
    introductions: Option<&std::sync::Arc<LoweringIntroductions>>,
) {
    add_required_proof_obligation_with_context_and_site(
        obligations,
        assumptions,
        proposition,
        context,
        introductions,
        None,
    );
}

fn add_required_proof_obligation_with_context_and_site(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
    introductions: Option<&std::sync::Arc<LoweringIntroductions>>,
    call_site: Option<&std::sync::Arc<CallRequirementSource>>,
) {
    // Suppression is the exact index, the frozen condition checker for a
    // proposition that is already one bare condition, or the retained atomic
    // memory/resource checkers. A required verification condition with
    // logical structure is emitted for an ordinary Surface tactic to
    // discharge.
    if required_obligation_is_exactly_discharged(assumptions, &proposition) {
        return;
    }
    let mut obligation = ProofObligation::verification_condition(proposition)
        .with_shared_introductions(introductions);
    if let Some(call_site) = call_site {
        obligation = obligation.with_call_requirement_site(call_site.clone());
    }
    let obligation = match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    };
    if let Some(existing) = obligations
        .iter_mut()
        .find(|existing| existing.proposition == obligation.proposition)
    {
        match (
            existing.call_requirement_site(),
            obligation.call_requirement_site(),
        ) {
            (None, Some(_)) => {
                // Replace the complete tuple, not only source metadata.
                *existing = obligation;
                return;
            }
            (Some(_), None) | (None, None) => return,
            (Some(existing), Some(incoming)) if existing.as_ref() == incoming.as_ref() => return,
            (Some(_), Some(_)) => {
                // Distinct source carriers remain finite alternatives. One
                // checked Have can discharge equal propositions from both.
                obligations.push(obligation);
                return;
            }
        }
    }
    obligations.push(obligation);
}

/// The same, suppressing only by the exact fact index, and carrying the same
/// recorded head chain.
pub(in crate::kernel) fn add_required_proof_obligation_without_search(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
    introductions: Option<&std::sync::Arc<LoweringIntroductions>>,
) {
    add_required_proof_obligation_without_search_and_site(
        obligations,
        assumptions,
        proposition,
        context,
        introductions,
        None,
    );
}

fn add_required_proof_obligation_without_search_and_site(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    proposition: Proposition,
    context: Option<&str>,
    introductions: Option<&std::sync::Arc<LoweringIntroductions>>,
    call_site: Option<&std::sync::Arc<CallRequirementSource>>,
) {
    if assumptions.proves_exact(&proposition) {
        return;
    }
    let mut obligation = ProofObligation::new(proposition).with_shared_introductions(introductions);
    if let Some(call_site) = call_site {
        obligation = obligation.with_call_requirement_site(call_site.clone());
    }
    let obligation = match context {
        Some(context) => obligation.with_context(context),
        None => obligation,
    };
    if let Some(existing) = obligations
        .iter_mut()
        .find(|existing| existing.proposition == obligation.proposition)
    {
        match (
            existing.call_requirement_site(),
            obligation.call_requirement_site(),
        ) {
            (None, Some(_)) => {
                *existing = obligation;
                return;
            }
            (Some(_), None) | (None, None) => return,
            (Some(existing), Some(incoming)) if existing.as_ref() == incoming.as_ref() => return,
            (Some(_), Some(_)) => {
                obligations.push(obligation);
                return;
            }
        }
    }
    obligations.push(obligation);
}

pub(in crate::kernel) fn append_required_proof_obligations(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    new_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_with_context_and_site(
            obligations,
            assumptions,
            obligation.proposition().clone(),
            obligation.context(),
            obligation.shared_introductions(),
            obligation.call_requirement_site(),
        );
    }
}

pub(in crate::kernel) fn append_required_proof_obligations_without_search(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    new_obligations: &[ProofObligation],
) {
    for obligation in new_obligations {
        add_required_proof_obligation_without_search_and_site(
            obligations,
            assumptions,
            obligation.proposition().clone(),
            obligation.context(),
            obligation.shared_introductions(),
            obligation.call_requirement_site(),
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
        // This wrap adds head nodes in front of the obligation, so the
        // record it carries forward is the new guards followed by the chain
        // already recorded for the proposition underneath them.
        let (proposition, guards) = wrap_path_context_with_introductions(
            obligation.proposition().clone(),
            facts,
            context_obligations,
        );
        let introductions = obligation.introductions().map(|recorded| {
            let mut introductions = guards.clone();
            introductions.extend(recorded.iter().cloned());
            std::sync::Arc::new(introductions)
        });
        add_required_proof_obligation_with_context_and_site(
            obligations,
            assumptions,
            proposition,
            obligation.context(),
            introductions.as_ref(),
            obligation.call_requirement_site(),
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
            if assumptions.proves_exact(obligation.proposition()) {
                continue;
            }
            if let Some(existing) = obligations
                .iter_mut()
                .find(|existing| existing.proposition() == obligation.proposition())
            {
                match (
                    existing.call_requirement_site(),
                    obligation.call_requirement_site(),
                ) {
                    (None, Some(_)) => {
                        // Replace the complete tuple, preserving the incoming
                        // source's context, introductions, and kind.
                        *existing = obligation.clone();
                        continue;
                    }
                    (Some(_), None) | (None, None) => continue,
                    (Some(existing), Some(incoming)) if existing.as_ref() == incoming.as_ref() => {
                        continue;
                    }
                    (Some(_), Some(_)) => {
                        // Distinct source carriers remain finite alternatives.
                    }
                }
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
            // Preserve mandatory conditions as mandatory across composition.
            // Rebuilding with `ProofObligation::new` would make an unresolved
            // condition available as an assumption to later evaluation.
            obligations.push(obligation.clone());
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

#[cfg(test)]
mod mandatory_integer_obligation_tests {
    use super::*;

    fn call_source(interface: &str, ordinal: usize) -> std::sync::Arc<CallRequirementSource> {
        std::sync::Arc::new(CallRequirementSource::new(
            std::sync::Arc::new(CallRequirementSite::for_requirement(
                "callee",
                interface,
                0,
                &[],
                &CMemory::new(),
            )),
            ordinal,
            Some(ordinal),
            true,
            None,
        ))
    }

    #[test]
    fn required_obligation_append_variants_preserve_call_source_and_reject_conflicts() {
        let proposition = Proposition::Predicate {
            name: "required".to_string(),
            arguments: vec![],
        };
        let source = call_source("selected", 0);
        let required = ProofObligation::verification_condition(proposition.clone())
            .with_call_requirement_site(source.clone());
        let assumptions = PureFactContext::new();

        let appenders: [fn(&mut Vec<ProofObligation>, &PureFactContext, &[ProofObligation]); 2] = [
            append_required_proof_obligations,
            append_required_proof_obligations_without_search,
        ];
        for append in appenders {
            let mut obligations = Vec::new();
            append(
                &mut obligations,
                &assumptions,
                std::slice::from_ref(&required),
            );
            assert!(std::sync::Arc::ptr_eq(
                obligations[0]
                    .call_requirement_site()
                    .expect("append preserves call source"),
                &source
            ));
        }

        let mut under_path = Vec::new();
        append_required_proof_obligations_under_path_context(
            &mut under_path,
            &assumptions,
            std::slice::from_ref(&required),
            &[],
            &[],
        );
        assert!(under_path[0].call_requirement_site().is_some());

        let conflicting = ProofObligation::verification_condition(proposition.clone())
            .with_call_requirement_site(call_source("other", 0));
        append_required_proof_obligations(
            &mut under_path,
            &assumptions,
            std::slice::from_ref(&conflicting),
        );
        assert!(
            under_path[0].call_requirement_site().is_some()
                && under_path[1].call_requirement_site().is_some(),
            "conflicting duplicate provenance must remain source-bearing"
        );
        assert_eq!(under_path.len(), 2);

        let same_site_different_ordinal = ProofObligation::verification_condition(proposition)
            .with_call_requirement_site(call_source("selected", 1));
        append_required_proof_obligations(
            &mut under_path,
            &assumptions,
            std::slice::from_ref(&same_site_different_ordinal),
        );
        assert_eq!(under_path.len(), 3);
        assert!(under_path[2].call_requirement_site().is_some());

        let carrierless_duplicate =
            ProofObligation::verification_condition(Proposition::Predicate {
                name: "required".to_string(),
                arguments: vec![],
            });
        append_required_proof_obligations(
            &mut under_path,
            &assumptions,
            std::slice::from_ref(&carrierless_duplicate),
        );
        assert_eq!(under_path.len(), 3);
        assert!(
            under_path
                .iter()
                .all(|obligation| obligation.call_requirement_site().is_some())
        );

        let tuple_proposition = Proposition::Predicate {
            name: "tuple".to_string(),
            arguments: vec![],
        };
        let incoming_introductions =
            std::sync::Arc::new(vec![LoweringIntroduction::WrittenNegation]);
        let incoming_source = call_source("incoming", 2);
        let mut tuple_obligations = vec![
            ProofObligation::verification_condition(tuple_proposition.clone())
                .with_context("old context")
                .with_introductions(vec![LoweringIntroduction::PathFactGuard]),
        ];
        add_required_proof_obligation_with_context_and_site(
            &mut tuple_obligations,
            &assumptions,
            tuple_proposition,
            Some("incoming context"),
            Some(&incoming_introductions),
            Some(&incoming_source),
        );
        assert_eq!(tuple_obligations.len(), 1);
        assert_eq!(
            tuple_obligations[0].context.as_deref(),
            Some("incoming context")
        );
        assert_eq!(
            tuple_obligations[0].introductions.as_deref(),
            Some(incoming_introductions.as_ref())
        );
        assert!(std::sync::Arc::ptr_eq(
            tuple_obligations[0]
                .call_requirement_site()
                .expect("replacement keeps incoming source"),
            &incoming_source
        ));
    }

    #[test]
    fn integer_conversion_obligation_merge_preserves_kind_and_context() {
        let proposition = Proposition::ConditionIs(ConditionTerm::Constant(false), true);
        let required = ProofObligation::verification_condition(proposition.clone())
            .with_context("Integer argument definedness");
        let base = PureFactContext::new();
        for (left, right) in [
            (vec![required.clone()], vec![]),
            (vec![], vec![required.clone()]),
        ] {
            let merged = merge_obligations(&left, &right, &base).unwrap();
            assert_eq!(merged, vec![required.clone()]);
            let context = assumptions_with_path_context(&base, &[], &merged);
            assert!(!context.proves_exact(&proposition));
        }
    }
}
