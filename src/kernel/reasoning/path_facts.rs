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
    assumptions: &PureFactContext,
) -> bool {
    range_memory == current_memory
        || range_memory.has_block(&base.block) == current_memory.has_block(&base.block)
            && range_memory.is_ended_local_address(base)
                == current_memory.is_ended_local_address(base)
            && range_memory.freed_heap_allocation_may_contain(base, assumptions)
                == current_memory.freed_heap_allocation_may_contain(base, assumptions)
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
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
) -> Proposition {
    let proposition = obligations
        .iter()
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    let proposition = facts
        .fact_iter()
        .filter(|fact| fact.is_public())
        .filter(|fact| {
            !fact.is_logical_read_equation()
                && !crate::kernel::eval::is_load_variable_defining_fact(fact.proposition())
        })
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
    facts: &(impl ExecutionFactSource + ?Sized),
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
    facts: &(impl ExecutionFactSource + ?Sized),
) -> Proposition {
    facts
        .fact_iter()
        .filter(|fact| {
            !fact.is_logical_read_equation()
                && !crate::kernel::eval::is_load_variable_defining_fact(fact.proposition())
        })
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
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
) -> (Proposition, LoweringIntroductions) {
    let proposition = obligations
        .iter()
        .rev()
        .fold(proposition, |body, obligation| {
            Proposition::Implies(Box::new(obligation.proposition().clone()), Box::new(body))
        });

    // Load definitions and producer-derived read equations are consequences
    // of term evaluation, not additional hypotheses. Wrapping either as a
    // premise would change the goal instead of retaining its read evidence.
    let retained = || {
        facts.fact_iter().filter(|fact| {
            !fact.is_logical_read_equation()
                && !crate::kernel::eval::is_load_variable_defining_fact(fact.proposition())
        })
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
    facts: &(impl ExecutionFactSource + ?Sized),
) -> ExecutionFacts {
    facts.persistent_facts().filtered(|fact| fact.is_public())
}

pub(in crate::kernel) fn memory_effect_execution_facts(
    facts: &(impl ExecutionFactSource + ?Sized),
) -> ExecutionFacts {
    // Internal memory effects and their theorem-backed provenance must
    // survive the public-fact projection. The latter is planning metadata,
    // not an additional path premise, and is consumed when Click constructs
    // the corresponding explicit transport step.
    facts.persistent_facts().filtered(|fact| {
        fact.transport_theorem().is_some()
            || matches!(
                fact.proposition(),
                Proposition::CMemoryMutatesOnly { .. }
                    | Proposition::CMemoryEffectSummary { .. }
                    | Proposition::CHeapAllocationFreed { .. }
            )
    })
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
            wide: false,
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
    let mut left = crate::kernel::spec::sequence_elements(left);
    let mut right = crate::kernel::spec::sequence_elements(right);
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
    let mut left = crate::kernel::spec::sequence_elements(left);
    let mut right = crate::kernel::spec::sequence_elements(right);
    loop {
        match (left.next(), right.next()) {
            (Some(left), Some(right)) if c_values_definitely_distinct(left, right) => return true,
            (Some(_), Some(_)) => {}
            (None, None) => return false,
            _ => return true,
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
        (CValue::Int8(left), CValue::Int8(right)) => {
            matches!((constant(left), constant(right)), (Some(left), Some(right)) if left != right)
        }
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

/// The element index a byte offset names, *modulo `2^32`*.
///
/// A residue is enough for a disequality and for an exclusion; a caller that
/// reads the answer as a number wants [`exact_element_delta_from_offset`].
/// Either way the answer has to be a residue of the delta, and an
/// `Int64Scaled` one is not: it scales its *64-bit* value, so the 32-bit term
/// holding that value denotes the index only when the value happens to fit
/// `int32`, and `unsigned int k; a[k]` reaches here as
/// `UInt64From32(k)` — a term of a different width from the one every
/// consumer compares it against. This is the arm
/// [`exact_element_delta_from_offset`] already refused, for the same reason,
/// and it is refused here too rather than carried: a width threaded alongside
/// the index would have to be got right independently at each of the dozen
/// consumers and at every certificate that re-checks them, while refusing
/// costs an answer none of them can use.
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
        // A byte index is the byte offset. A struct-array element is scaled
        // by its stride, and its byte offset is the same residue the byte
        // spelling `items + i * stride` gives.
        PointerOffsetTerm::Int32Scaled { .. } if element_width == 1 => {
            byte_offset_from_pointer_offset(offset)
        }
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

/// [`element_index_from_offset`] for a caller holding facts, which is the one
/// thing that turns a 64-bit index into a 32-bit one.
///
/// An `Int64Scaled` displacement scales its *64-bit* value, so the term
/// holding that value names an element index only where full-width evidence
/// places it in the signed word range. Exact constants work for either sign;
/// unsigned symbolic values require their native upper bound. Checked scalar
/// aliases preserve that bound, including a constant subtraction whose bound
/// the proof establishes explicitly. No low-word fact establishes high bits.
pub(in crate::kernel) fn element_index_from_offset_with_facts(
    offset: &PointerOffsetTerm,
    element_width: u32,
    assumptions: &PureFactContext,
) -> Option<Bitvector32Term> {
    if element_width == 0 {
        return None;
    }
    if let Some(index) = element_index_from_offset(offset, element_width) {
        return Some(index);
    }
    match offset {
        PointerOffsetTerm::Add(left, right) => Some(Bitvector32Term::add(
            element_index_from_offset_with_facts(left, element_width, assumptions)?,
            element_index_from_offset_with_facts(right, element_width, assumptions)?,
        )),
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned,
        } if *byte_width == i64::from(element_width) => {
            // The value is sixty-four bits wide, so only a sixty-four-bit
            // fact pins it: a thirty-two-bit one names the low word and
            // leaves the rest, and `exact_signed_constant` accepts those.
            // `unsigned` is part of the question rather than a check after
            // it, because the two readings of one word are different numbers.
            if let Some(index) = crate::kernel::assumptions::exact_sixty_four_bit_constant(
                value,
                *unsigned,
                assumptions,
            ) {
                return i32::try_from(index)
                    .ok()
                    .map(|index| Bitvector32Term::Constant(index as u32));
            }
            if !*unsigned {
                // A signed index in `0..=INT_MAX` is its own low word.
                return assumptions
                    .int64_index_fits_int32(value)
                    .then(|| Bitvector32Term::uint32_from_64(value.as_ref().clone()));
            }
            let bounded =
                |candidate: &Bitvector32Term| assumptions.uint64_index_fits_int32(candidate);
            if bounded(value) {
                return Some(Bitvector32Term::uint32_from_64(value.as_ref().clone()));
            }
            // Modular calls can name an unchanged native index through a
            // checked scalar-result equality. Transport the bound through
            // that full-width equality, never through equality of low words.
            for (alias, fact) in assumptions.exact_uint64_equalities(value) {
                crate::instrumentation::record_deterministic_work(1);
                if bounded(alias) {
                    crate::kernel::assumptions::record_implicit_reasoning_provenance(
                        assumptions,
                        &Proposition::ConditionIs(fact.clone(), true),
                    );
                    return Some(Bitvector32Term::uint32_from_64(alias.clone()));
                }
            }
            // A constant subtraction retains equality of the full-width
            // operands. Its bound must still be proved explicitly; this does
            // not infer nonemptiness or arithmetic ranges from a low word.
            if let Bitvector32Term::UInt64Subtract(left, right) = value.as_ref()
                && right.uint64_as_const().is_some()
            {
                for (alias, fact) in assumptions.exact_uint64_equalities(left) {
                    crate::instrumentation::record_deterministic_work(1);
                    let candidate =
                        Bitvector32Term::uint64_subtract(alias.clone(), right.as_ref().clone());
                    if bounded(&candidate) {
                        crate::kernel::assumptions::record_implicit_reasoning_provenance(
                            assumptions,
                            &Proposition::ConditionIs(fact.clone(), true),
                        );
                        return Some(Bitvector32Term::uint32_from_64(candidate));
                    }
                }
            }
            None
        }
        _ => None,
    }
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
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
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
        PointerOffsetTerm::Int64Scaled { byte_width: 0, .. } => Some(Bitvector32Term::Constant(0)),
        // A 64-bit index is not a 32-bit byte residue, even when its stride
        // is one. Callers that need its numeric value must use a 64-bit bound.
        PointerOffsetTerm::Int64Scaled { .. } | PointerOffsetTerm::Variable(_) => None,
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
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    proposition: Proposition,
) -> Option<()> {
    add_path_fact_with_visibility(facts, assumptions, proposition, true)
}

pub(in crate::kernel) fn add_path_fact_with_visibility(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    proposition: Proposition,
    public: bool,
) -> Option<()> {
    add_path_fact_with_visibility_after_effect(facts, assumptions, proposition, public, false)
}

fn add_path_fact_with_visibility_after_effect(
    facts: &mut ExecutionFacts,
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
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, true, false)
}

pub(in crate::kernel) fn add_internal_condition_path_fact(
    facts: &mut ExecutionFacts,
    assumptions: &PureFactContext,
    condition: ConditionTerm,
    value: bool,
) -> Option<()> {
    add_condition_path_fact_with_visibility(facts, assumptions, condition, value, false, false)
}

fn add_condition_path_fact_with_visibility(
    facts: &mut ExecutionFacts,
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
    facts: &mut ExecutionFacts,
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

    // The element index a byte offset folds to is that offset divided by the
    // element width, *modulo* `2^32`: every leaf contributes a whole multiple
    // of the width, but `Bitvector32Term::add` folds the pieces modularly.
    //
    // That makes the two directions different statements. Equal offsets have
    // equal residues, so the affirmative half is arithmetic and needs no
    // premise. Different offsets need not have different residues: `p + i + j`
    // and `p + k` are `2^34` bytes apart at `i == j == i32::MAX`, `k == -2`,
    // and their indices are the same `-2`. Recording `i + j != k` there is
    // recording a false fact, which proves anything.
    //
    // So the disequality is recorded only where each fold is the sum —
    // `rebuilt_offset_is_exact` on the element path, the same premise the
    // opposite polarity of the same question already asks for in
    // `exact_or_unequal`, and exact for the opposite reason: there a residue
    // may refute an offset equality and may not affirm one, while here an
    // offset disequality may not be read off a residue that could have
    // wrapped onto it.
    if let (Some(left_index), Some(right_index)) = (
        int32_element_index_from_offset(&left),
        int32_element_index_from_offset(&right),
    ) && (value
        || assumptions.element_index_rebuild_is_exact(&left)
            && assumptions.element_index_rebuild_is_exact(&right))
    {
        add_condition_path_fact(
            facts,
            assumptions,
            ConditionTerm::equal(left_index, right_index),
            value,
        )?;
    } else if let Some((index, element)) = single_scaled_index_equal_to_constant(&left, &right)
        .or_else(|| single_scaled_index_equal_to_constant(&right, &left))
    {
        add_condition_path_fact(
            facts,
            assumptions,
            ConditionTerm::equal(index.clone(), Bitvector32Term::Constant(element as u32)),
            value,
        )?;
    }

    Some(())
}

/// `scaled == constant` as the index it selects, when `scaled` is one scaled
/// `int32` index plus constants, `sext(x) * stride + c`: `x * 8 + 4 == 12`
/// holds exactly when `x == 1`. The offset sum is exact, so the equivalence
/// holds in both polarities, at any stride. `None` when the constant is not
/// one of the offsets the index reaches; the offset equality then folds to
/// false (see `pointer_offsets_differ_by_residue`).
pub(in crate::kernel) fn single_scaled_index_equal_to_constant<'term>(
    scaled: &'term PointerOffsetTerm,
    constant: &PointerOffsetTerm,
) -> Option<(&'term Bitvector32Term, i32)> {
    let target = constant.as_const()?;
    let (leaves, offset) = scaled.int32_scaled_linear_form()?;
    let [(index, stride)] = leaves.as_slice() else {
        return None;
    };
    let delta = target.checked_sub(offset)?;
    if *stride == 0 || delta % stride != 0 {
        return None;
    }
    i32::try_from(delta / stride)
        .ok()
        .map(|element| (*index, element))
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
    if let ConditionTerm::Bitvector64Equal(left, right) = condition
        && *value
        && assumptions.uint64_values_known_equal(left, right)
    {
        crate::kernel::assumptions::record_implicit_reasoning_provenance(assumptions, proposition);
        return true;
    }
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
    facts: &(impl ExecutionFactSource + ?Sized),
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
    merge_obligations_with_changes(left, right, assumptions).map(|(obligations, _)| obligations)
}

fn merge_obligations_with_changes(
    left: &[ProofObligation],
    right: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<ProofObligation>, Vec<usize>)> {
    let mut obligations = left.to_vec();
    let mut changed = Vec::new();
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
            if let Some(index) = obligations
                .iter()
                .position(|existing| existing.proposition() == obligation.proposition())
            {
                let existing = &mut obligations[index];
                match (
                    existing.call_requirement_site(),
                    obligation.call_requirement_site(),
                ) {
                    (None, Some(_)) => {
                        // Replace the complete tuple, preserving the incoming
                        // source's context, introductions, and kind.
                        *existing = obligation.clone();
                        changed.push(index);
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
            changed.push(obligations.len());
            obligations.push(obligation.clone());
        } else {
            // Preserve mandatory conditions as mandatory across composition.
            // Rebuilding with `ProofObligation::new` would make an unresolved
            // condition available as an assumption to later evaluation.
            changed.push(obligations.len());
            obligations.push(obligation.clone());
        }
    }
    Some((obligations, changed))
}

pub(in crate::kernel) fn merge_facts(
    left: &(impl ExecutionFactSource + ?Sized),
    right: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> Option<ExecutionFacts> {
    merge_facts_with_changes(left, right, assumptions).map(|(facts, _)| facts)
}

fn merge_facts_with_changes(
    left: &(impl ExecutionFactSource + ?Sized),
    right: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> Option<(ExecutionFacts, Vec<usize>)> {
    let mut changed = Vec::new();
    let prefix = left.persistent_facts();
    let suffix = right.persistent_facts();
    let mut facts = prefix.clone();
    let mut share_append = true;
    let mut appended = Vec::new();
    let mut saw_memory_effect = false;
    for (source_index, fact) in suffix.iter().enumerate() {
        let before = facts.len();
        add_path_fact_with_visibility_after_effect(
            &mut facts,
            assumptions,
            fact.proposition().clone(),
            fact.is_public(),
            saw_memory_effect && fact.is_certified(),
        )?;
        let existing_index = fact
            .is_certified()
            .then(|| {
                facts
                    .iter()
                    .position(|existing| existing.proposition() == fact.proposition())
            })
            .flatten();
        if let Some(index) = existing_index
            && &facts[index] != fact
        {
            share_append &= index >= before;
            *facts.get_mut(index) = fact.clone();
            changed.push(index);
        }
        if facts.len() == before + 1 {
            share_append &= &facts[before] == fact;
            appended.push(source_index);
            changed.push(before);
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
    if share_append {
        // Validation may suppress redundant right facts, but it did not
        // change the prefix or normalize an appended fact. Retain the source
        // objects for the accepted delta instead of validation scratch copies.
        let mut combined = prefix;
        let accepted = suffix.selected(&appended);
        combined.extend_shared(&accepted);
        Some((combined, changed))
    } else {
        Some((facts, changed))
    }
}

pub(in crate::kernel) fn merge_execution_pure_facts_and_obligations(
    left_facts: &(impl ExecutionFactSource + ?Sized),
    left_obligations: &[ProofObligation],
    right_facts: &(impl ExecutionFactSource + ?Sized),
    right_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(ExecutionFacts, Vec<ProofObligation>)> {
    merge_execution_pure_facts_and_obligations_in(
        left_facts,
        left_obligations,
        right_facts,
        right_obligations,
        assumptions,
        None,
    )
}

/// [`merge_execution_pure_facts_and_obligations`] for a caller that already
/// built the left fragment's path context,
/// `assumptions_with_path_context(assumptions, left_facts, left_obligations)`,
/// to execute the right fragment under: the merge rechecks against that same
/// context, so building it again is the same work twice.
pub(in crate::kernel) fn merge_execution_pure_facts_and_obligations_under(
    left_facts: &(impl ExecutionFactSource + ?Sized),
    left_obligations: &[ProofObligation],
    right_facts: &(impl ExecutionFactSource + ?Sized),
    right_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
    prefix_assumptions: &PureFactContext,
) -> Option<(ExecutionFacts, Vec<ProofObligation>)> {
    merge_execution_pure_facts_and_obligations_in(
        left_facts,
        left_obligations,
        right_facts,
        right_obligations,
        assumptions,
        Some(prefix_assumptions),
    )
}

fn merge_execution_pure_facts_and_obligations_in(
    left_facts: &(impl ExecutionFactSource + ?Sized),
    left_obligations: &[ProofObligation],
    right_facts: &(impl ExecutionFactSource + ?Sized),
    right_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
    prefix_assumptions: Option<&PureFactContext>,
) -> Option<(ExecutionFacts, Vec<ProofObligation>)> {
    let facts = merge_facts(left_facts, right_facts, assumptions)?;
    // The right fragment was executed under the left fragment's path
    // context. Recheck its assumable obligations against that same context,
    // not against the older base assumptions. In particular, a verified call
    // can change a field that an entry-state branch constrained; checking a
    // post-call load guard against only the entry snapshot can incorrectly
    // discard a valid successor path. Only an assumable obligation reads the
    // context, so a right fragment without one builds none.
    let built;
    let prefix_assumptions = match prefix_assumptions {
        Some(prefix_assumptions) => prefix_assumptions,
        None if right_obligations.iter().any(ProofObligation::is_assumable) => {
            built = assumptions_with_path_context(assumptions, left_facts, left_obligations);
            &built
        }
        None => assumptions,
    };
    let obligations = merge_obligations(left_obligations, right_obligations, prefix_assumptions)?;
    Some((facts, obligations))
}

/// A canonical merge and the context of its assumable members. Changed
/// positions include replacements of complete source-bearing tuples, not just
/// appended positions. Mandatory obligations are retained but never assumed.
pub(in crate::kernel) struct PreparedExecutionPath {
    pub facts: ExecutionFacts,
    pub obligations: Vec<ProofObligation>,
    pub assumptions: PureFactContext,
    pub changed_obligations: Vec<usize>,
}

/// Compose a pure lowering fragment under its already prepared left context.
/// The caller retains that persistent context between declarations, rather
/// than rebuilding every earlier fact and member at each declaration.
pub(in crate::kernel) fn merge_prepared_execution_path(
    left_facts: &ExecutionFacts,
    left_obligations: &[ProofObligation],
    right_facts: &ExecutionFacts,
    right_obligations: &[ProofObligation],
    base: &PureFactContext,
    prepared: &PureFactContext,
    effective: &PureFactContext,
) -> Option<PreparedExecutionPath> {
    let (facts, mut changed_facts) = merge_facts_with_changes(left_facts, right_facts, effective)?;
    let (obligations, mut changed_obligations) =
        merge_obligations_with_changes(left_obligations, right_obligations, effective)?;
    changed_facts.sort_unstable();
    changed_facts.dedup();
    changed_obligations.sort_unstable();
    changed_obligations.dedup();
    // Invariant reading is pure. Keep the general merge's ordering if this
    // helper is later used with an effect-bearing fragment: post-effect facts
    // can supersede an entry-state condition, unlike a pure monotone extension.
    let assumptions = if right_facts.iter().any(|fact| {
        matches!(
            fact.proposition(),
            Proposition::CMemoryMutatesOnly { .. }
                | Proposition::CMemoryEffectSummary { .. }
                | Proposition::CHeapAllocationFreed { .. }
        )
    }) {
        assumptions_with_path_context(base, &facts, &obligations)
    } else {
        count_context_rebuild_entries(changed_facts.len() + changed_obligations.len());
        let mut context = prepared.clone();
        for index in changed_facts {
            context = context.assume_execution_pure_fact(&facts[index]);
        }
        for &index in &changed_obligations {
            if obligations[index].is_assumable() {
                context = context.assume_proposition(obligations[index].proposition().clone());
            }
        }
        context
    };
    Some(PreparedExecutionPath {
        facts,
        obligations,
        assumptions,
        changed_obligations,
    })
}

pub(in crate::kernel) fn decide_with_facts(
    assumptions: &PureFactContext,
    facts: &(impl ExecutionFactSource + ?Sized),
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
            facts.fact_iter().find_map(|fact| match fact.proposition() {
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
                .fact_iter()
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

#[cfg(test)]
thread_local! {
    static CONTEXT_REBUILD_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
    static CONTRACT_PATH_CONTEXT_ENTRIES: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

#[cfg(test)]
pub(crate) fn record_contract_path_context_entries(entries: usize) {
    CONTRACT_PATH_CONTEXT_ENTRIES.with(|count| count.set(count.get() + entries));
}

#[cfg(test)]
pub(crate) fn contract_path_context_entries() -> usize {
    CONTRACT_PATH_CONTEXT_ENTRIES.with(std::cell::Cell::get)
}

/// Counts, in test builds, the entries a fact context built from a list
/// assumes (`assumptions_with_path_context`, `assumptions_with_propositions`,
/// `PropositionSource::pure_context`, `ProofFacts::from_ordered`, and the
/// contexts a `PureFactList` extends). The work itself is charged where
/// every context is built, one unit per fact
/// (`PureFactContext::assume_proposition`), so a caller that rebuilds a
/// context from a growing list once per item shows as quadratic work; this
/// count lets a scaling regression pin the builds alone.
pub(crate) fn count_context_rebuild_entries(_entries: usize) {
    #[cfg(test)]
    record_context_entries_for_tests(_entries);
}

/// Counts, in test builds, the entries of a context build that is charged
/// nothing (`PureFactContext::assume_proposition_uncharged`): a known
/// violation of the complexity contract, listed in
/// `docs/internals/verification-efficiency.md`, whose charge would fail a
/// scaling regression until its representation changes.
pub(crate) fn count_uncharged_context_entries(_entries: usize) {
    #[cfg(test)]
    record_context_entries_for_tests(_entries);
}

#[cfg(test)]
fn record_context_entries_for_tests(entries: usize) {
    CONTEXT_REBUILD_ENTRIES.with(|count| count.set(count.get() + entries));
}

/// The context entries built so far on this thread, charged or not.
#[cfg(test)]
pub(crate) fn context_rebuild_entries() -> usize {
    CONTEXT_REBUILD_ENTRIES.with(std::cell::Cell::get)
}

pub(in crate::kernel) fn assumptions_with_path_context(
    assumptions: &PureFactContext,
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
) -> PureFactContext {
    count_context_rebuild_entries(facts.len() + obligations.len());
    let mut assumptions = assumptions.clone();
    for fact in facts.fact_iter() {
        assumptions = assumptions.assume_execution_pure_fact(fact);
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
    count_context_rebuild_entries(propositions.len());
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

    // A cached path must retain canonical source metadata and must not turn
    // an unresolved verification condition into a fact for the next member.
    #[test]
    fn prepared_path_delta_matches_fresh_context_and_complete_source_replacement() {
        let predicate = |name: &str| Proposition::Predicate {
            name: name.to_string(),
            arguments: vec![],
        };
        let old_fact = ExecutionPureFact::new(predicate("old fact"));
        let upgraded = ExecutionPureFact::certified(old_fact.proposition().clone());
        let new_fact = ExecutionPureFact::new(predicate("new fact"));
        let left_facts = ExecutionFacts::from(vec![old_fact]);
        let right_facts = ExecutionFacts::from(vec![upgraded.clone(), new_fact.clone()]);
        let mandatory = ProofObligation::verification_condition(Proposition::ConditionIs(
            ConditionTerm::Constant(false),
            true,
        ))
        .with_context("still owed");
        let replaceable = ProofObligation::verification_condition(predicate("replacement"))
            .with_context("old source")
            .with_introductions(vec![LoweringIntroduction::PathFactGuard]);
        let source = call_source("incoming", 2);
        let incoming = ProofObligation::new(predicate("replacement"))
            .with_context("incoming source")
            .with_introductions(vec![LoweringIntroduction::WrittenNegation])
            .with_call_requirement_site(source.clone());
        let left_obligations = vec![replaceable, mandatory.clone()];
        let right_obligations = vec![incoming.clone(), mandatory.clone()];
        let base = PureFactContext::new();
        let prepared = assumptions_with_path_context(&base, &left_facts, &left_obligations);
        let effective = prepared
            .clone()
            .defer_non_exact_condition_reasoning()
            .defer_non_exact_loadability_obligations();
        let merged = merge_prepared_execution_path(
            &left_facts,
            &left_obligations,
            &right_facts,
            &right_obligations,
            &base,
            &prepared,
            &effective,
        )
        .unwrap();
        let (fresh_facts, fresh_obligations) = merge_execution_pure_facts_and_obligations(
            &left_facts,
            &left_obligations,
            &right_facts,
            &right_obligations,
            &effective,
        )
        .unwrap();
        assert_eq!(merged.facts, fresh_facts);
        assert_eq!(merged.facts[0], upgraded);
        assert_eq!(merged.facts[1], new_fact);
        assert_eq!(merged.obligations, fresh_obligations);
        assert_eq!(merged.changed_obligations, vec![0, 2]);
        assert_eq!(
            merged.obligations[0].introductions(),
            incoming.introductions()
        );
        assert!(std::sync::Arc::ptr_eq(
            merged.obligations[0].call_requirement_site().unwrap(),
            &source
        ));
        assert_eq!(
            merged.assumptions,
            assumptions_with_path_context(&base, &fresh_facts, &fresh_obligations)
        );
        assert!(!merged.assumptions.proves_exact(mandatory.proposition()));
        assert!(merged.assumptions.proves_exact(incoming.proposition()));
    }

    #[test]
    fn prepared_path_extensions_with_new_facts_and_obligations_build_only_the_delta() {
        let mut samples = Vec::new();
        for size in [8usize, 16, 32] {
            let mut ambient_samples = Vec::new();
            for ambient in [0usize, 128, 512] {
                let mut base = PureFactContext::new();
                for index in 0..ambient {
                    base = base.assume_proposition(Proposition::Predicate {
                        name: format!("ambient_{index}"),
                        arguments: vec![],
                    });
                }
                let before = context_rebuild_entries();
                let ((facts, obligations, context), work) =
                    crate::instrumentation::measure_deterministic_work(|| {
                        let mut facts = ExecutionFacts::new();
                        let mut obligations = Vec::new();
                        let mut context = base.clone();
                        for index in 0..size {
                            let incoming_facts =
                                ExecutionFacts::from(vec![ExecutionPureFact::new(
                                    Proposition::Predicate {
                                        name: format!("fact_{index}"),
                                        arguments: vec![],
                                    },
                                )]);
                            let incoming_obligations =
                                vec![ProofObligation::new(Proposition::Predicate {
                                    name: format!("obligation_{index}"),
                                    arguments: vec![],
                                })];
                            let merged = merge_prepared_execution_path(
                                &facts,
                                &obligations,
                                &incoming_facts,
                                &incoming_obligations,
                                &base,
                                &context,
                                &context,
                            )
                            .unwrap();
                            assert_eq!(merged.changed_obligations, vec![index]);
                            facts = merged.facts;
                            obligations = merged.obligations;
                            context = merged.assumptions;
                        }
                        (facts, obligations, context)
                    });
                let entries = context_rebuild_entries() - before;
                assert_eq!(entries, 2 * size);
                assert_eq!(
                    context,
                    assumptions_with_path_context(&base, &facts, &obligations)
                );
                ambient_samples.push((entries, work));
            }
            assert!(
                ambient_samples.windows(2).all(|pair| pair[0] == pair[1]),
                "{ambient_samples:?}"
            );
            samples.push(ambient_samples[0]);
        }
        assert!(
            samples
                .windows(2)
                .all(|pair| pair[1].1 <= 2 * pair[0].1 + 32),
            "{samples:?}"
        );
    }

    #[test]
    fn prepared_path_effect_fragment_keeps_fresh_rebuild_ordering() {
        let condition = ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(912_347)),
            Bitvector32Term::Constant(3),
        );
        let base = PureFactContext::new();
        let left = vec![ProofObligation::condition(condition.clone(), true)];
        let prepared = assumptions_with_path_context(&base, &[], &left);
        let memory = CMemory::new();
        let right = ExecutionFacts::from(vec![
            ExecutionPureFact::new(Proposition::CMemoryMutatesOnly {
                before: memory.clone(),
                after: memory,
                writes: vec![],
            }),
            ExecutionPureFact::certified(Proposition::ConditionIs(condition, false)),
        ]);
        let merged = merge_prepared_execution_path(
            &ExecutionFacts::new(),
            &left,
            &right,
            &[],
            &base,
            &prepared,
            &prepared,
        )
        .unwrap();
        let (facts, obligations) = merge_execution_pure_facts_and_obligations(
            &ExecutionFacts::new(),
            &left,
            &right,
            &[],
            &prepared,
        )
        .unwrap();
        assert_eq!(merged.facts, facts);
        assert_eq!(merged.obligations, obligations);
        assert_eq!(
            merged.assumptions,
            assumptions_with_path_context(&base, &facts, &obligations)
        );
    }

    #[test]
    fn prepared_path_delta_rejects_a_conflicting_pure_successor() {
        let condition = ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(912_345)),
            Bitvector32Term::Constant(3),
        );
        let base = PureFactContext::new();
        let left = vec![ProofObligation::condition(condition.clone(), true)];
        let prepared = assumptions_with_path_context(&base, &[], &left);
        let right = ExecutionFacts::from(vec![ExecutionPureFact::new(Proposition::ConditionIs(
            condition, false,
        ))]);
        assert!(
            merge_prepared_execution_path(
                &ExecutionFacts::new(),
                &left,
                &right,
                &[],
                &base,
                &prepared,
                &prepared,
            )
            .is_none()
        );
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
