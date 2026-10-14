use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) enum SimpProposition {
    True,
    False,
    Proposition(Proposition),
}

pub(in crate::surface) fn normalize_proposition(proposition: &Proposition) -> SimpProposition {
    match proposition {
        Proposition::Equal(left, right) => match simp_terms_equal(left, right) {
            Some(true) => SimpProposition::True,
            Some(false) => SimpProposition::False,
            None => {
                SimpProposition::Proposition(Proposition::Equal(simp_term(left), simp_term(right)))
            }
        },
        Proposition::ConditionIs(condition, expected) => {
            match simp_condition_without_assumptions(condition) {
                Some(actual) if actual == *expected => SimpProposition::True,
                Some(_) => SimpProposition::False,
                None => SimpProposition::Proposition(proposition.clone()),
            }
        }
        Proposition::And(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::True, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (left, SimpProposition::True) => left,
                (left, right) => SimpProposition::Proposition(Proposition::And(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Or(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (SimpProposition::True, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::False, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::False, right) => right,
                (left, SimpProposition::False) => left,
                (left, right) => SimpProposition::Proposition(Proposition::Or(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Not(body) => match normalize_proposition(body) {
            SimpProposition::True => SimpProposition::False,
            SimpProposition::False => SimpProposition::True,
            body => {
                SimpProposition::Proposition(Proposition::Not(Box::new(body.into_proposition())))
            }
        },
        Proposition::Implies(left, right) => {
            let left = normalize_proposition(left);
            let right = normalize_proposition(right);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (_, SimpProposition::False) => SimpProposition::False,
                (left, right) => SimpProposition::Proposition(Proposition::Implies(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        _ => SimpProposition::Proposition(proposition.clone()),
    }
}

pub(in crate::surface) use crate::kernel::proof::equality_rewrite::rewrite_proposition_by_exact_equality;

/// The single explicit-certificate search shared by every smart-simplification
/// construction path. Both the fixed-state proof `simp() using` chain and the
/// post-execution outcome planner must call through here (directly or via
/// [`plan_explicit_equality_rewrites_then`]), so a named simple rule available
/// to one is available to the other. `is_available` is the caller's judgment
/// of when the current goal closes by `assumption`.
pub(in crate::surface) fn plan_explicit_equality_rewrites_from(
    goal: &Proposition,
    premises: &[(Proposition, ClickProposition)],
    available: &[Proposition],
    is_available: &impl Fn(&Proposition) -> bool,
    closer: &impl Fn(&Proposition) -> Option<Vec<ProofTactic>>,
) -> Option<Vec<ProofTactic>> {
    fn reverse_equality(
        kernel: &Proposition,
        surface: &ClickProposition,
    ) -> Option<(Proposition, ClickProposition)> {
        let kernel = match kernel {
            Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(right.clone(), left.clone()),
                    true,
                )
            }
            Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector64Equal(right.clone(), left.clone()),
                    true,
                )
            }
            Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::PointerEqual(right.clone(), left.clone()),
                    true,
                )
            }
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
                Proposition::ConditionIs(
                    ConditionTerm::PointerOffsetEqual(right.clone(), left.clone()),
                    true,
                )
            }
            Proposition::Equal(Term::Algebraic(left), Term::Algebraic(right)) => {
                Proposition::Equal(
                    Term::Algebraic(right.clone()),
                    Term::Algebraic(left.clone()),
                )
            }
            _ => return None,
        };
        let ClickProposition::Comparison {
            left,
            operator: ComparisonOperator::Equal,
            right,
        } = surface
        else {
            return None;
        };
        Some((
            kernel,
            ClickProposition::Comparison {
                left: right.clone(),
                operator: ComparisonOperator::Equal,
                right: left.clone(),
            },
        ))
    }

    fn search(
        current: Proposition,
        premises: &[(Proposition, ClickProposition)],
        available: &[Proposition],
        used: &mut [bool],
        tactics: &mut Vec<ProofTactic>,
        is_available: &impl Fn(&Proposition) -> bool,
        closer: &impl Fn(&Proposition) -> Option<Vec<ProofTactic>>,
    ) -> bool {
        // The search tries premise orders depth first, so its node count is
        // factorial in the equalities it may use. Each node observes the
        // enclosing tactic's deadline and work budget, so a search that
        // cannot close fails when its tactic's bound runs out rather than
        // running on to finish.
        if crate::instrumentation::deadline_exceeded() {
            return false;
        }
        if is_available(&current) {
            tactics.push(ProofTactic::Assumption);
            return true;
        }
        if normalizes_context_free(&current) {
            tactics.push(ProofTactic::Normalize);
            return true;
        }
        if let Some(suffix) = closer(&current) {
            tactics.extend(suffix);
            return true;
        }
        // A disjunction closes the way `assumption` closes it: one
        // disjunct must be the same total boolean condition as an
        // available fact up to polarity (`x > 0` from `not (x <= 0)`).
        // Construction mirrors exactly that rule, and commits only
        // when a disjunct closes, so nothing beyond the two children is
        // examined.
        if let Proposition::Or(left_child, right_child) = &current {
            for child in [left_child.as_ref(), right_child.as_ref()] {
                if available
                    .iter()
                    .any(|fact| condition_polarity_equivalent(fact, child))
                {
                    tactics.push(ProofTactic::Assumption);
                    return true;
                }
            }
        }
        for (index, (kernel, surface)) in premises.iter().enumerate() {
            if used[index] {
                continue;
            }
            let mut orientations = vec![(kernel.clone(), surface.clone())];
            if let Some(reverse) = reverse_equality(kernel, surface) {
                orientations.push(reverse);
            }
            for (oriented_kernel, oriented_surface) in orientations {
                let Ok(rewritten) =
                    rewrite_proposition_by_exact_equality(&current, &oriented_kernel, available)
                else {
                    continue;
                };
                used[index] = true;
                tactics.push(ProofTactic::Rewrite(oriented_surface));
                if search(
                    rewritten,
                    premises,
                    available,
                    used,
                    tactics,
                    is_available,
                    closer,
                ) {
                    return true;
                }
                tactics.pop();
                used[index] = false;
            }
        }
        false
    }

    let mut used = vec![false; premises.len()];
    let mut tactics = Vec::new();
    search(
        goal.clone(),
        premises,
        available,
        &mut used,
        &mut tactics,
        is_available,
        closer,
    )
    .then_some(tactics)
}

/// The checked kernel evidence behind one successful smart simplification.
/// Search produces this at the moment it succeeds and immediately writes it
/// as explicit surface tactics; it is never stored, ordered into a plan, or
/// checked as a private operation program. A derivation the surface
/// vocabulary cannot write is a search failure, not a lowering error.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) enum SimpEvidence {
    /// The goal normalizes to true without consulting any context.
    Normalize,
    /// A kernel derivation of the goal from its context premises.
    Derivation(PropositionDerivation),
}

pub(in crate::surface) fn plan_simp_certificate(
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> Option<SimpEvidence> {
    if matches!(normalize_proposition(proposition), SimpProposition::True) {
        Some(SimpEvidence::Normalize)
    } else {
        Some(SimpEvidence::Derivation(
            assumptions.derive_simp_proposition(proposition)?,
        ))
    }
}

#[cfg(test)]
fn check_simp_certificate(
    proposition: &Proposition,
    assumptions: &PureFactContext,
    certificate: &SimpEvidence,
) -> bool {
    match certificate {
        SimpEvidence::Normalize => {
            matches!(normalize_proposition(proposition), SimpProposition::True)
        }
        SimpEvidence::Derivation(derivation) => {
            derivation.conclusion() == proposition && derivation.check(assumptions)
        }
    }
}

#[cfg(test)]
pub(in crate::surface) fn simp_proposition(
    proposition: &Proposition,
    assumptions: &PureFactContext,
) -> SimpProposition {
    if let Some(certificate) = plan_simp_certificate(proposition, assumptions)
        && check_simp_certificate(proposition, assumptions, &certificate)
    {
        return SimpProposition::True;
    }
    let simplified = match proposition {
        Proposition::Equal(left, right) => match simp_terms_equal(left, right) {
            Some(true) => SimpProposition::True,
            Some(false) => SimpProposition::False,
            None => {
                SimpProposition::Proposition(Proposition::Equal(simp_term(left), simp_term(right)))
            }
        },
        Proposition::ConditionIs(condition, expected) => {
            match simp_condition(condition, assumptions) {
                Some(actual) if actual == *expected => SimpProposition::True,
                Some(_) => SimpProposition::False,
                None => SimpProposition::Proposition(proposition.clone()),
            }
        }
        Proposition::And(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::True, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (left, SimpProposition::True) => left,
                (left, right) => SimpProposition::Proposition(Proposition::And(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Or(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::True, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::False, SimpProposition::False) => SimpProposition::False,
                (SimpProposition::False, right) => right,
                (left, SimpProposition::False) => left,
                (left, right) => SimpProposition::Proposition(Proposition::Or(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::Not(body) => match simp_proposition(body, assumptions) {
            SimpProposition::True => SimpProposition::False,
            SimpProposition::False => SimpProposition::True,
            body => {
                SimpProposition::Proposition(Proposition::Not(Box::new(body.into_proposition())))
            }
        },
        Proposition::Implies(left, right) => {
            let left = simp_proposition(left, assumptions);
            let right = simp_proposition(right, assumptions);
            match (left, right) {
                (SimpProposition::False, _) | (_, SimpProposition::True) => SimpProposition::True,
                (SimpProposition::True, right) => right,
                (_, SimpProposition::False) => SimpProposition::False,
                (left, right) => SimpProposition::Proposition(Proposition::Implies(
                    Box::new(left.into_proposition()),
                    Box::new(right.into_proposition()),
                )),
            }
        }
        Proposition::ForAll { .. }
        | Proposition::Exists { .. }
        | Proposition::Predicate { .. }
        | Proposition::CExpressionEvaluates { .. }
        | Proposition::CConditionEvaluates { .. }
        | Proposition::CStatementExecutes { .. }
        | Proposition::CStatementVerifies { .. }
        | Proposition::CFunctionExecutes { .. }
        | Proposition::CFunctionVerifies { .. }
        | Proposition::CFunctionSatisfiesSpecification { .. }
        | Proposition::CFunctionPartiallySatisfiesSpecification { .. }
        | Proposition::CMemoryLoads { .. }
        | Proposition::CValidPlace { .. }
        | Proposition::CMemoryReadDefined { .. }
        | Proposition::CMemoryInitialized { .. }
        | Proposition::CMemoryLoadable { .. }
        | Proposition::CMemoryCanStore { .. }
        | Proposition::CResourceSeparate { .. }
        | Proposition::CResourceComposition(_)
        | Proposition::CResourceContains { .. }
        | Proposition::CMemoryMutatesOnly { .. }
        | Proposition::CMemoryEffectSummary { .. }
        | Proposition::CHeapAllocationFreed { .. } => {
            SimpProposition::Proposition(proposition.clone())
        }
    };
    if matches!(simplified, SimpProposition::True) {
        // A successful smart tactic must come from the certificate path above.
        SimpProposition::Proposition(proposition.clone())
    } else {
        simplified
    }
}

impl SimpProposition {
    fn into_proposition(self) -> Proposition {
        match self {
            Self::True => Proposition::ConditionIs(ConditionTerm::Constant(true), true),
            Self::False => Proposition::ConditionIs(ConditionTerm::Constant(false), true),
            Self::Proposition(proposition) => proposition,
        }
    }
}

pub(in crate::surface) fn simp_terms_equal(left: &Term, right: &Term) -> Option<bool> {
    let left = simp_term(left);
    let right = simp_term(right);
    if left == right {
        return Some(true);
    }
    match (&left, &right) {
        (Term::Bitvector32(left), Term::Bitvector32(right)) => Some(
            simp_bitvector_const(&simp_bitvector(left))?
                == simp_bitvector_const(&simp_bitvector(right))?,
        ),
        (Term::Condition(left), Term::Condition(right)) => Some(
            simp_condition_without_assumptions(left)? == simp_condition_without_assumptions(right)?,
        ),
        _ => None,
    }
}

pub(in crate::surface) fn simp_term(term: &Term) -> Term {
    match term {
        Term::Condition(condition) => match simp_condition_without_assumptions(condition) {
            Some(value) => Term::Condition(ConditionTerm::Constant(value)),
            None => term.clone(),
        },
        Term::Bitvector32(term) => Term::Bitvector32(simp_bitvector(term)),
        Term::CValue(CValue::Int32(term)) => Term::CValue(CValue::Int32(simp_bitvector(term))),
        Term::CValue(CValue::Int64(term)) => Term::CValue(CValue::Int64(simp_bitvector(term))),
        Term::CValue(CValue::UInt64(term)) => Term::CValue(CValue::UInt64(simp_bitvector(term))),
        Term::CValue(CValue::PointerInteger(value)) => {
            Term::CValue(CValue::PointerInteger(std::sync::Arc::new(
                value.with_parts(simp_bitvector(value.bits()), value.origin().clone()),
            )))
        }
        _ => term.clone(),
    }
}

#[cfg(test)]
pub(in crate::surface) fn simp_condition(
    condition: &ConditionTerm,
    assumptions: &PureFactContext,
) -> Option<bool> {
    simp_condition_without_assumptions(condition)
        .or_else(|| assumptions.decide_condition_for_simp(condition))
}

pub(in crate::surface) fn simp_condition_without_assumptions(
    condition: &ConditionTerm,
) -> Option<bool> {
    match condition {
        ConditionTerm::AlgebraicEqual(_, _) => {
            PureFactContext::new().decide_condition_for_simp(condition)
        }
        ConditionTerm::IntegerEqual(left, right) => {
            if left == right {
                Some(true)
            } else {
                Some(left.as_const()? == right.as_const()?)
            }
        }
        ConditionTerm::IntegerNotEqual(left, right) => {
            if left == right {
                Some(false)
            } else {
                Some(left.as_const()? != right.as_const()?)
            }
        }
        ConditionTerm::IntegerLessThan(left, right) => Some(left.as_const()? < right.as_const()?),
        ConditionTerm::IntegerLessEqual(left, right) => Some(left.as_const()? <= right.as_const()?),
        ConditionTerm::IntegerGreaterThan(left, right) => {
            Some(left.as_const()? > right.as_const()?)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            Some(left.as_const()? >= right.as_const()?)
        }
        ConditionTerm::Constant(value) => Some(*value),
        ConditionTerm::Bitvector32Equal(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(simp_bitvector_const(&left)? == simp_bitvector_const(&right)?)
            }
        }
        ConditionTerm::Bitvector32SignedLessThan(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(false)
            } else {
                Some((simp_bitvector_const(&left)? as i32) < (simp_bitvector_const(&right)? as i32))
            }
        }
        ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(
                    (simp_bitvector_const(&left)? as i32) <= (simp_bitvector_const(&right)? as i32),
                )
            }
        }
        ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(false)
            } else {
                Some((simp_bitvector_const(&left)? as i32) > (simp_bitvector_const(&right)? as i32))
            }
        }
        ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                Some(true)
            } else {
                Some(
                    (simp_bitvector_const(&left)? as i32) >= (simp_bitvector_const(&right)? as i32),
                )
            }
        }
        ConditionTerm::Bitvector64SignedLessThan(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                return Some(false);
            }
            Some(left.int64_as_const()? < right.int64_as_const()?)
        }
        ConditionTerm::Bitvector64SignedLessEqual(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                return Some(true);
            }
            Some(left.int64_as_const()? <= right.int64_as_const()?)
        }
        ConditionTerm::Bitvector64SignedGreaterThan(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                return Some(false);
            }
            Some(left.int64_as_const()? > right.int64_as_const()?)
        }
        ConditionTerm::Bitvector64SignedGreaterEqual(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                return Some(true);
            }
            Some(left.int64_as_const()? >= right.int64_as_const()?)
        }
        ConditionTerm::Bitvector64UnsignedLessThan(left, right) => Some({
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                return Some(false);
            }
            left.uint64_as_const()? < right.uint64_as_const()?
        }),
        ConditionTerm::Bitvector64UnsignedLessEqual(left, right) => Some({
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                return Some(true);
            }
            left.uint64_as_const()? <= right.uint64_as_const()?
        }),
        ConditionTerm::Bitvector64UnsignedGreaterThan(left, right) => Some({
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                return Some(false);
            }
            left.uint64_as_const()? > right.uint64_as_const()?
        }),
        ConditionTerm::Bitvector64UnsignedGreaterEqual(left, right) => Some({
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                return Some(true);
            }
            left.uint64_as_const()? >= right.uint64_as_const()?
        }),
        ConditionTerm::Bitvector64Equal(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            if left == right {
                return Some(true);
            }
            let left = left
                .int64_as_const()
                .map(|value| value as u64)
                .or_else(|| left.uint64_as_const())?;
            let right = right
                .int64_as_const()
                .map(|value| value as u64)
                .or_else(|| right.uint64_as_const())?;
            Some(left == right)
        }
        ConditionTerm::Variable(_)
        | ConditionTerm::Bitvector32SignedAddOverflows(_, _)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(_, _)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(_, _)
        | ConditionTerm::Bitvector32SignedDivideOverflows(_, _)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(_, _)
        | ConditionTerm::Bitvector64SignedAddOverflows(_, _)
        | ConditionTerm::Bitvector64SignedSubtractOverflows(_, _)
        | ConditionTerm::Bitvector64SignedMultiplyOverflows(_, _)
        | ConditionTerm::Bitvector64SignedDivideOverflows(_, _)
        | ConditionTerm::Bitvector64SignedShiftLeftOverflows(_, _)
        | ConditionTerm::Float32(_)
        | ConditionTerm::Float64(_)
        | ConditionTerm::PointerOffsetEqual(_, _)
        | ConditionTerm::PointerEqual(_, _) => None,
    }
}

pub(in crate::surface) fn simp_bitvector_const(term: &Bitvector32Term) -> Option<u32> {
    match term {
        Bitvector32Term::MachineIntegerCast { .. } => None,

        Bitvector32Term::Constant(value) => Some(*value),
        Bitvector32Term::Variable(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_)
        | Bitvector32Term::Int64From32(_)
        | Bitvector32Term::UInt64From32(_)
        | Bitvector32Term::UInt32From64(_)
        | Bitvector32Term::Int64FromUInt32(_)
        | Bitvector32Term::UInt64FromInt32(_)
        | Bitvector32Term::UInt64FromInt64(_)
        | crate::kernel::binary_int64_term!(_, _)
        | Bitvector32Term::Int64BitwiseNot(_)
        | crate::kernel::binary_uint64_term!(_, _)
        | Bitvector32Term::UInt64BitwiseNot(_)
        | Bitvector32Term::Float32Negate(_)
        | Bitvector32Term::Float32Binary { .. }
        | Bitvector32Term::Float64Negate(_)
        | Bitvector32Term::Float64Binary { .. }
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::PureFunctionApplication { .. }
        | Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. }
        | Bitvector32Term::PointerAddress(_)
        | Bitvector32Term::MemoryLoad(_, _, _) => None,
        Bitvector32Term::Add(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_add(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Subtract(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_sub(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Multiply(left, right) => {
            Some(simp_bitvector_const(left)?.wrapping_mul(simp_bitvector_const(right)?))
        }
        Bitvector32Term::Divide(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = simp_bitvector_const(right)? as i32;
            if right == 0 || (left == i32::MIN && right == -1) {
                None
            } else {
                Some((left / right) as u32)
            }
        }
        Bitvector32Term::UnsignedDivide(left, right) => {
            let left = simp_bitvector_const(left)?;
            let right = simp_bitvector_const(right)?;
            (right != 0).then_some(left / right)
        }
        Bitvector32Term::Remainder(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = simp_bitvector_const(right)? as i32;
            if right == 0 || (left == i32::MIN && right == -1) {
                None
            } else {
                Some((left % right) as u32)
            }
        }
        Bitvector32Term::UnsignedRemainder(left, right) => {
            let left = simp_bitvector_const(left)?;
            let right = simp_bitvector_const(right)?;
            (right != 0).then_some(left % right)
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = bitvector32_shift_count(simp_bitvector_const(right)?)?;
            if left < 0 {
                None
            } else {
                let shifted = (left as i64) << right;
                (shifted <= i64::from(i32::MAX)).then_some((shifted as i32) as u32)
            }
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let left = simp_bitvector_const(left)? as i32;
            let right = bitvector32_shift_count(simp_bitvector_const(right)?)?;
            Some((left >> right) as u32)
        }
        Bitvector32Term::LogicalShiftRight(left, right) => {
            let left = simp_bitvector_const(left)?;
            let right = bitvector32_shift_count(simp_bitvector_const(right)?)?;
            Some(left >> right)
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            Some(simp_bitvector_const(left)? & simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            Some(simp_bitvector_const(left)? | simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            Some(simp_bitvector_const(left)? ^ simp_bitvector_const(right)?)
        }
        Bitvector32Term::BitwiseNot(value) => Some(!simp_bitvector_const(value)?),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match simp_condition_without_assumptions(condition)? {
            true => simp_bitvector_const(then_term),
            false => simp_bitvector_const(else_term),
        },
        Bitvector32Term::IntegerToMachine { .. } => None,
    }
}

pub(in crate::surface) fn simp_bitvector(term: &Bitvector32Term) -> Bitvector32Term {
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::MachineIntegerConstant(_)
        | Bitvector32Term::Variable(_) => term.clone(),
        Bitvector32Term::IntegerToMachine { .. } => term.clone(),
        Bitvector32Term::Add(left, right) => {
            bitvector32_add(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Subtract(left, right) => {
            bitvector32_subtract(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Multiply(left, right) => {
            bitvector32_multiply(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::Divide(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_divide(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::Divide(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::Remainder(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_remainder(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::Remainder(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_shift_left(left.clone(), right.clone())
                .unwrap_or_else(|_| Bitvector32Term::ShiftLeft(Box::new(left), Box::new(right)))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let left = simp_bitvector(left);
            let right = simp_bitvector(right);
            bitvector32_shift_right(left.clone(), right.clone()).unwrap_or_else(|_| {
                Bitvector32Term::ArithmeticShiftRight(Box::new(left), Box::new(right))
            })
        }
        Bitvector32Term::BitwiseAnd(left, right) => {
            bitvector32_and(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseOr(left, right) => {
            bitvector32_or(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseXor(left, right) => {
            bitvector32_xor(simp_bitvector(left), simp_bitvector(right))
        }
        Bitvector32Term::BitwiseNot(value) => bitvector32_not(simp_bitvector(value)),
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => match simp_condition_without_assumptions(condition) {
            Some(true) => simp_bitvector(then_term),
            Some(false) => simp_bitvector(else_term),
            None => Bitvector32Term::if_then_else(
                condition.as_ref().clone(),
                simp_bitvector(then_term),
                simp_bitvector(else_term),
            ),
        },
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => Bitvector32Term::range_fold(
            simp_bitvector(start),
            simp_bitvector(end),
            simp_bitvector(initial),
            *accumulator,
            *item,
            simp_bitvector(body),
        ),
        Bitvector32Term::PureFunctionApplication { name, arguments } => {
            Bitvector32Term::PureFunctionApplication {
                name: name.clone(),
                arguments: arguments.iter().map(simp_bitvector).collect(),
            }
        }
        Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. } => term.clone(),
        Bitvector32Term::MemoryLoad(memory, pointer, kind) => {
            Bitvector32Term::MemoryLoad(memory.clone(), pointer.clone(), *kind)
        }
        Bitvector32Term::PointerAddress(pointer) => {
            Bitvector32Term::PointerAddress(pointer.clone())
        }
        term => match (term.as_binary(), term.as_unary()) {
            (Some((op, left, right)), _) => op.build(simp_bitvector(left), simp_bitvector(right)),
            (_, Some((op, value))) => op.build(simp_bitvector(value)),
            _ => unreachable!("every other variant has its own arm"),
        },
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{
        IntegerRangeFoldIndex, IntegerTerm, MachineIntegerType, SharedIntegerRangeEndpoint,
        SharedMachineIntegerTerm,
    };

    /// The equality-rewrite search visits premise orders depth first, and a
    /// goal it cannot close makes it visit all of them. Under an exhausted
    /// deadline it stops at its first node.
    #[test]
    #[ignore = "nightly: 1.8s in the parallel gate"]
    fn equality_rewrite_search_observes_the_deadline() {
        let variable = |index: u64| Bitvector32Term::Variable(Variable(93_400 + index));
        let count = 6;
        let sum = (1..count).fold(variable(0), |sum, index| {
            Bitvector32Term::add(sum, variable(index))
        });
        let goal = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(
                Box::new(sum),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let premises = (0..count)
            .map(|index| {
                let kernel = Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(variable(index)),
                        Box::new(variable(100 + index)),
                    ),
                    true,
                );
                let surface = ClickProposition::Comparison {
                    left: ContractExpression::IntegerLiteral(index.to_string()),
                    operator: ComparisonOperator::Equal,
                    right: ContractExpression::IntegerLiteral((100 + index).to_string()),
                };
                (kernel, surface)
            })
            .collect::<Vec<_>>();
        let available = premises
            .iter()
            .map(|(kernel, _)| kernel.clone())
            .collect::<Vec<_>>();
        let nodes = std::cell::Cell::new(0_usize);
        let closer = |_: &Proposition| {
            nodes.set(nodes.get() + 1);
            None
        };
        let unbounded =
            plan_explicit_equality_rewrites_from(&goal, &premises, &available, &|_| false, &closer);
        assert!(unbounded.is_none());
        assert!(
            nodes.get() > 1_000,
            "an unclosable goal visits every premise order: {} nodes",
            nodes.get()
        );
        nodes.set(0);
        let expired = crate::instrumentation::with_deadline(std::time::Duration::ZERO, || {
            plan_explicit_equality_rewrites_from(&goal, &premises, &available, &|_| false, &closer)
        });
        assert!(expired.is_none());
        assert_eq!(
            nodes.get(),
            0,
            "an exhausted deadline stops the search at once"
        );
    }

    #[test]
    fn registered_pointer_rewrite_uses_observed_snapshot() {
        // Projected identity snapshots have no target-cell content. Rewriting
        // the address must use the observed snapshot, including its latest
        // overwrite, rather than inventing a disconnected target load.
        for (case, stored) in [(0, 17), (1, 29)] {
            let source = Pointer::symbolic(Variable(910_000 + case));
            let target = Pointer {
                block: PointerBlock::Heap(920_000 + case),
                offset: PointerOffsetTerm::Constant(4),
            };
            let identity = crate::kernel::intern_c_memory(
                CMemory::new().with_block(format!("rewrite-origin-{case}"), 16),
            );
            let observed = crate::kernel::intern_c_memory(
                identity
                    .memory()
                    .clone()
                    .store(target.clone(), CValue::Int32(Bitvector32Term::Constant(17)))
                    .store(
                        target.clone(),
                        CValue::Int32(Bitvector32Term::Constant(stored)),
                    ),
            );
            let load = crate::kernel::load_variable_for_cell_with_origin(
                &identity,
                &source,
                crate::kernel::LoadKind::Bits32,
                4,
                &observed,
            );
            let goal = Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(Bitvector32Term::Variable(load)),
                    Box::new(Bitvector32Term::Constant(17)),
                ),
                true,
            );
            let equality =
                Proposition::ConditionIs(ConditionTerm::pointer_equal(source, target), true);
            let rewritten = rewrite_proposition_by_exact_equality(
                &goal,
                &equality,
                std::slice::from_ref(&equality),
            )
            .expect("rewrite the registered load at its observed snapshot");
            assert_eq!(
                rewritten,
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Constant(stored)),
                        Box::new(Bitvector32Term::Constant(17)),
                    ),
                    true,
                )
            );
        }
    }

    #[test]
    fn pointer_rewrite_reaches_through_a_loaded_pointer() {
        // `w` is the pointer read from `source`. Rewriting `source` to
        // `target` rewrites the load `w` names, so a read through `w`
        // becomes a read through the pointer read from `target`.
        let source = Pointer::symbolic(Variable(930_000));
        let target = Pointer {
            block: PointerBlock::Heap(930_001),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = crate::kernel::intern_c_memory(
            CMemory::new().with_block(PointerBlock::Heap(930_001), 16),
        );
        let loaded = crate::kernel::load_variable_for_cell_with_origin(
            &memory,
            &source,
            crate::kernel::LoadKind::Bits32,
            8,
            &memory,
        );
        let (target_loaded, _) =
            crate::kernel::load_variable_for_term(&Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(target.clone()),
                crate::kernel::LoadKind::Bits32,
            ))
            .expect("the target read has a name");
        let read_through = |variable| {
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: PointerBlock::Symbolic(variable),
                    offset: PointerOffsetTerm::Constant(8),
                }),
                crate::kernel::LoadKind::Bits32,
            )
        };
        let goal = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(read_through(loaded)),
                Box::new(Bitvector32Term::Constant(5)),
            ),
            true,
        );
        let equality = Proposition::ConditionIs(ConditionTerm::pointer_equal(source, target), true);
        let rewritten = rewrite_proposition_by_exact_equality(
            &goal,
            &equality,
            std::slice::from_ref(&equality),
        )
        .expect("rewrite through the loaded pointer");
        assert_eq!(
            rewritten,
            Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(read_through(target_loaded)),
                    Box::new(Bitvector32Term::Constant(5)),
                ),
                true,
            )
        );
    }

    #[test]
    fn pointer_rewrite_changes_every_matching_field_load_at_one_snapshot() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let source = Pointer {
            block: PointerBlock::Symbolic(Variable(91)),
            offset: PointerOffsetTerm::Constant(0),
        };
        let target = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(92)), 4),
        };
        let field_load = |base: &Pointer, displacement| {
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: base.block.clone(),
                    offset: PointerOffsetTerm::add(
                        base.offset.clone(),
                        PointerOffsetTerm::Constant(displacement),
                    ),
                }),
                crate::kernel::LoadKind::Bits32,
            )
        };
        let equality = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(source.clone(), target.clone()),
            true,
        );
        let goal = Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(field_load(&source, 4)),
                    Box::new(field_load(&target, 4)),
                ),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(field_load(&source, 8)),
                    Box::new(field_load(&target, 12)),
                ),
                true,
            )),
        );
        assert!(
            rewrite_proposition_by_exact_equality(&goal, &equality, &[])
                .expect_err("the equality must be available")
                .contains("exact available fact")
        );
        let rewritten = rewrite_proposition_by_exact_equality(
            &goal,
            &equality,
            std::slice::from_ref(&equality),
        )
        .expect("one cited equality rewrites both field addresses");
        let expected = Proposition::And(
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(field_load(&target, 4)),
                    Box::new(field_load(&target, 4)),
                ),
                true,
            )),
            Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(field_load(&target, 8)),
                    Box::new(field_load(&target, 12)),
                ),
                true,
            )),
        );
        assert_eq!(rewritten, expected);
    }

    #[test]
    fn rewrite_uses_pointer_offset_equalities_inside_pointer_goals() {
        let left = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(41))),
            byte_width: 4,
        };
        let right = PointerOffsetTerm::Int32Scaled {
            value: Box::new(Bitvector32Term::Variable(Variable(42))),
            byte_width: 4,
        };
        let equality = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(left.clone()), Box::new(right.clone())),
            true,
        );
        let pointer = |offset| Pointer {
            block: PointerBlock::ExternalArgument,
            offset,
        };
        let null = Pointer {
            block: "null".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let goal = Proposition::ConditionIs(
            ConditionTerm::pointer_equal(pointer(left), null.clone()),
            true,
        );

        assert_eq!(
            rewrite_proposition_by_exact_equality(
                &goal,
                &equality,
                std::slice::from_ref(&equality),
            )
            .unwrap(),
            Proposition::ConditionIs(ConditionTerm::pointer_equal(pointer(right), null), true,),
        );
    }

    #[test]
    fn rewrite_substitutes_index_and_base_equalities_inside_load_addresses() {
        let memory = crate::kernel::intern_c_memory(CMemory::new());
        let data = Bitvector32Term::Variable(Variable(51));
        let alias = Bitvector32Term::Variable(Variable(52));
        let index = Bitvector32Term::Variable(Variable(53));
        let pointer = |offset| Pointer {
            block: PointerBlock::ExternalArgument,
            offset,
        };
        let load = |offset| {
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(pointer(offset)),
                crate::kernel::LoadKind::Bits32,
            )
        };
        let data_offset = PointerOffsetTerm::scale_int32(data.clone(), 4);
        let alias_offset = PointerOffsetTerm::scale_int32(alias.clone(), 4);
        let indexed_offset = PointerOffsetTerm::add(
            data_offset.clone(),
            PointerOffsetTerm::scale_int32(index.clone(), 4),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(load(indexed_offset)),
                Box::new(load(alias_offset.clone())),
            ),
            true,
        );
        let index_is_zero = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(index),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );
        let data_is_alias = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(data_offset), Box::new(alias_offset)),
            true,
        );
        let available = [index_is_zero.clone(), data_is_alias.clone()];

        let indexed =
            rewrite_proposition_by_exact_equality(&goal, &index_is_zero, &available).unwrap();
        let aliased =
            rewrite_proposition_by_exact_equality(&indexed, &data_is_alias, &available).unwrap();
        assert_eq!(normalize_proposition(&aliased), SimpProposition::True);
    }

    #[test]
    fn rewrite_substitutes_length_and_base_equalities_inside_memory_resources() {
        let source = Bitvector32Term::Variable(Variable(61));
        let target = Bitvector32Term::Variable(Variable(62));
        let source_len = Bitvector32Term::Variable(Variable(63));
        let target_len = Bitvector32Term::Variable(Variable(64));
        let fixed = CResource::Memory(CMemoryRange::new(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::scale_int32(Bitvector32Term::Variable(Variable(65)), 4),
            },
            Bitvector32Term::Constant(0),
            Bitvector32Term::Constant(4),
        ));
        let range = |base: Bitvector32Term, end: Bitvector32Term| {
            CResource::Memory(CMemoryRange::new(
                Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: PointerOffsetTerm::scale_int32(base, 4),
                },
                Bitvector32Term::Constant(0),
                end,
            ))
        };
        let goal = Proposition::CResourceSeparate {
            left: Box::new(fixed.clone()),
            right: Box::new(range(source.clone(), source_len.clone())),
        };
        let length_equality = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(source_len), Box::new(target_len.clone())),
            true,
        );
        let base_equality = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(
                Box::new(PointerOffsetTerm::scale_int32(source, 4)),
                Box::new(PointerOffsetTerm::scale_int32(target.clone(), 4)),
            ),
            true,
        );
        let available = [length_equality.clone(), base_equality.clone()];

        let resized =
            rewrite_proposition_by_exact_equality(&goal, &length_equality, &available).unwrap();
        let replaced =
            rewrite_proposition_by_exact_equality(&resized, &base_equality, &available).unwrap();
        assert_eq!(
            replaced,
            Proposition::CResourceSeparate {
                left: Box::new(fixed),
                right: Box::new(range(target, target_len)),
            }
        );
    }

    #[test]
    fn integer_simp_planner_emits_explicit_bound_certificate() {
        let x = IntegerTerm::Variable(Variable(71));
        let y = IntegerTerm::Variable(Variable(72));
        let lower = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(x.clone().into(), y.clone().into()),
            true,
        );
        let upper = Proposition::ConditionIs(
            ConditionTerm::IntegerLessEqual(y.clone().into(), x.clone().into()),
            true,
        );
        let goal = Proposition::ConditionIs(ConditionTerm::IntegerEqual(x.into(), y.into()), true);
        let certificate = plan_integer_affine_certificate(&goal, &[lower.clone(), upper.clone()])
            .expect("opposite integer bounds should produce a certificate");
        certificate
            .check(&goal, &[lower, upper])
            .expect("the planned certificate should pass the kernel checker");
    }
    #[test]
    fn integer_observation_rewrite_requires_an_available_machine_equality() {
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("rewrite-cell", 4));
        let pointer = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let load =
            Bitvector32Term::MemoryLoad(memory, Box::new(pointer), crate::kernel::LoadKind::Bits32);
        let observed = IntegerTerm::from_machine(MachineIntegerType::Int32, load.clone())
            .expect("a symbolic int32 load is a mathematical observation");
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(IntegerTerm::constant_i64(0).into(), observed.into()),
            true,
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(load), Box::new(Bitvector32Term::Constant(0))),
            true,
        );

        let error = rewrite_proposition_by_exact_equality(&goal, &equality, &[])
            .expect_err("an equality absent from the checked facts must be rejected");
        assert!(error.contains("exact available fact"), "{error}");
    }

    #[test]
    fn integer_range_fold_rewrite_changes_only_int32_endpoints() {
        let from = Bitvector32Term::Variable(Variable(71));
        let to = Bitvector32Term::Variable(Variable(72));
        let memory = crate::kernel::intern_c_memory(CMemory::new().with_block("fold", 4));
        let body = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "fold".into(),
                    offset: PointerOffsetTerm::Constant(0),
                }),
                crate::kernel::LoadKind::Bits32,
            ),
        ));
        let fold = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Int32 {
                start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
                end: SharedIntegerRangeEndpoint::intern(from.clone()),
            },
            IntegerTerm::constant_i64(0),
            Variable(73),
            Variable(74),
            body.clone(),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(fold.clone().into(), IntegerTerm::constant_i64(0).into()),
            true,
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(from), Box::new(to.clone())),
            true,
        );
        let rewritten = rewrite_proposition_by_exact_equality(
            &goal,
            &equality,
            std::slice::from_ref(&equality),
        )
        .expect("a checked endpoint equality should rewrite the Int32 fold bound");
        let expected = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Int32 {
                start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
                end: SharedIntegerRangeEndpoint::intern(to),
            },
            IntegerTerm::constant_i64(0),
            Variable(73),
            Variable(74),
            body,
        );
        assert_eq!(
            rewritten,
            Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(expected.into(), IntegerTerm::constant_i64(0).into()),
                true,
            )
        );
    }

    #[test]
    fn integer_range_fold_rewrite_rejects_missing_or_integer_bound_equalities() {
        let from = Bitvector32Term::Variable(Variable(81));
        let to = Bitvector32Term::Variable(Variable(82));
        let fold = IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(0).into(),
                end: IntegerTerm::var(Variable(81)).into(),
            },
            IntegerTerm::constant_i64(0),
            Variable(83),
            Variable(84),
            IntegerTerm::add(
                IntegerTerm::var(Variable(83)),
                IntegerTerm::var(Variable(84)),
            ),
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(fold.into(), IntegerTerm::constant_i64(0).into()),
            true,
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(from), Box::new(to)),
            true,
        );
        let missing = rewrite_proposition_by_exact_equality(&goal, &equality, &[])
            .expect_err("an absent endpoint equality must be rejected");
        assert!(missing.contains("exact available fact"), "{missing}");
        let unchanged = rewrite_proposition_by_exact_equality(
            &goal,
            &equality,
            std::slice::from_ref(&equality),
        )
        .expect_err("machine equality must not rewrite an Integer range bound");
        assert!(unchanged.contains("does not occur"), "{unchanged}");
    }

    #[test]
    fn integer_observation_rewrite_does_not_cross_memory_snapshots() {
        let pointer = Pointer {
            block: PointerBlock::Concrete("rewrite-cell".into()),
            offset: PointerOffsetTerm::Constant(0),
        };
        let first_memory = crate::kernel::intern_c_memory(
            CMemory::new()
                .with_block("rewrite-cell", 4)
                .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(0))),
        );
        let second_memory = crate::kernel::intern_c_memory(
            CMemory::new()
                .with_block("rewrite-cell", 4)
                .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(7))),
        );
        assert_ne!(first_memory, second_memory);
        let first_load = Bitvector32Term::MemoryLoad(
            first_memory,
            Box::new(pointer.clone()),
            crate::kernel::LoadKind::Bits32,
        );
        let second_load = Bitvector32Term::MemoryLoad(
            second_memory,
            Box::new(pointer),
            crate::kernel::LoadKind::Bits32,
        );
        let observed = IntegerTerm::from_machine(MachineIntegerType::Int32, second_load)
            .expect("a symbolic int32 load is a mathematical observation");
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(IntegerTerm::constant_i64(0).into(), observed.into()),
            true,
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(
                Box::new(first_load),
                Box::new(Bitvector32Term::Constant(0)),
            ),
            true,
        );

        let error = rewrite_proposition_by_exact_equality(
            &goal,
            &equality,
            std::slice::from_ref(&equality),
        )
        .expect_err("a checked equality from another memory snapshot must not rewrite this load");
        assert!(
            error.contains("does not occur in the current goal"),
            "{error}"
        );
    }
}
