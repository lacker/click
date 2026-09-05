use crate::kernel::*;
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum ArithmeticCheckError {
    UnsupportedGoal,
    UnsupportedPremise(usize),
    GoalMayBeUndefined,
    DoesNotFollow,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SignedAffineForm {
    terms: BTreeMap<Bitvector32Term, i64>,
    constant: i64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct SignedAffineInequality {
    /// The normalized judgment is `sum(terms) <= bound`.
    terms: BTreeMap<Bitvector32Term, i64>,
    bound: i64,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SignedAffineClaim {
    Inequality(SignedAffineInequality),
    Equality(SignedAffineForm),
    Disequality(SignedAffineForm),
    Constant(bool),
}

const SIGNED_MIN: i64 = i32::MIN as i64;
const SIGNED_MAX: i64 = i32::MAX as i64;
const ARITHMETIC_INTERVAL_DEPTH: usize = 32;

fn signed_term_interval(
    term: &Bitvector32Term,
    bounds: &BTreeMap<Bitvector32Term, (i64, i64)>,
    depth: usize,
) -> Option<(i64, i64)> {
    crate::instrumentation::record_deterministic_work(1);
    if depth == 0 {
        return None;
    }
    if let Some(value) = term.as_const() {
        let value = i64::from(value as i32);
        return Some((value, value));
    }
    match term {
        Bitvector32Term::Constant(value) => {
            let value = i64::from(*value as i32);
            Some((value, value))
        }
        Bitvector32Term::Variable(_)
        | Bitvector32Term::MemoryLoad(_, _)
        | Bitvector32Term::PointerAddress(_)
        | Bitvector32Term::PureFunctionApplication { .. }
        | Bitvector32Term::Float32Negate(_)
        | Bitvector32Term::Float32Binary { .. }
        | Bitvector32Term::Float64Negate(_)
        | Bitvector32Term::Float64Binary { .. } => Some(
            bounds
                .get(&crate::kernel::eval::canonical_term(term))
                .copied()
                .unwrap_or((SIGNED_MIN, SIGNED_MAX)),
        ),
        Bitvector32Term::Add(left, right) => {
            let (left_lower, left_upper) = signed_term_interval(left, bounds, depth - 1)?;
            let (right_lower, right_upper) = signed_term_interval(right, bounds, depth - 1)?;
            let lower = left_lower.checked_add(right_lower)?;
            let upper = left_upper.checked_add(right_upper)?;
            (SIGNED_MIN <= lower && upper <= SIGNED_MAX).then_some((lower, upper))
        }
        Bitvector32Term::Subtract(left, right) => {
            let (left_lower, left_upper) = signed_term_interval(left, bounds, depth - 1)?;
            let (right_lower, right_upper) = signed_term_interval(right, bounds, depth - 1)?;
            let lower = left_lower.checked_sub(right_upper)?;
            let upper = left_upper.checked_sub(right_lower)?;
            (SIGNED_MIN <= lower && upper <= SIGNED_MAX).then_some((lower, upper))
        }
        Bitvector32Term::Multiply(left, right) => {
            let (left_lower, left_upper) = signed_term_interval(left, bounds, depth - 1)?;
            let (right_lower, right_upper) = signed_term_interval(right, bounds, depth - 1)?;
            let products = [
                i128::from(left_lower) * i128::from(right_lower),
                i128::from(left_lower) * i128::from(right_upper),
                i128::from(left_upper) * i128::from(right_lower),
                i128::from(left_upper) * i128::from(right_upper),
            ];
            let lower = *products.iter().min()?;
            let upper = *products.iter().max()?;
            (i128::from(SIGNED_MIN) <= lower && upper <= i128::from(SIGNED_MAX))
                .then_some((lower as i64, upper as i64))
        }
        Bitvector32Term::Remainder(left, right) => {
            let divisor = i64::from(right.as_const()? as i32);
            if divisor == 0 {
                return None;
            }
            let (left_lower, left_upper) = signed_term_interval(left, bounds, depth - 1)?;
            if divisor == -1 && left_lower <= SIGNED_MIN && SIGNED_MIN <= left_upper {
                return None;
            }
            let magnitude = divisor.checked_abs()?.saturating_sub(1).min(SIGNED_MAX);
            if left_lower >= 0 {
                Some((0, magnitude))
            } else if left_upper <= 0 {
                Some((-magnitude, 0))
            } else {
                Some((-magnitude, magnitude))
            }
        }
        Bitvector32Term::ShiftLeft(left, right) => {
            let shift = i64::from(right.as_const()? as i32);
            if !(0..32).contains(&shift) {
                return None;
            }
            let (left_lower, left_upper) = signed_term_interval(left, bounds, depth - 1)?;
            if left_lower < 0 {
                return None;
            }
            let factor = 1_i128.checked_shl(shift as u32)?;
            let lower = i128::from(left_lower).checked_mul(factor)?;
            let upper = i128::from(left_upper).checked_mul(factor)?;
            (i128::from(SIGNED_MIN) <= lower && upper <= i128::from(SIGNED_MAX))
                .then_some((lower as i64, upper as i64))
        }
        Bitvector32Term::ArithmeticShiftRight(left, right) => {
            let shift = i64::from(right.as_const()? as i32);
            if !(0..32).contains(&shift) {
                return None;
            }
            let (left_lower, left_upper) = signed_term_interval(left, bounds, depth - 1)?;
            Some((
                i64::from((left_lower as i32) >> shift),
                i64::from((left_upper as i32) >> shift),
            ))
        }
        Bitvector32Term::LogicalShiftRight(_, _) => None,
        Bitvector32Term::BitwiseAnd(left, right) => {
            let mask = right.as_const().or_else(|| left.as_const())?;
            if mask > i32::MAX as u32 {
                return None;
            }
            let operand = if right.as_const().is_some() {
                left
            } else {
                right
            };
            signed_term_interval(operand, bounds, depth - 1)?;
            Some((0, i64::from(mask as i32)))
        }
        Bitvector32Term::Divide(_, _)
        | Bitvector32Term::UnsignedDivide(_, _)
        | Bitvector32Term::UnsignedRemainder(_, _)
        | Bitvector32Term::BitwiseOr(_, _)
        | Bitvector32Term::BitwiseXor(_, _)
        | Bitvector32Term::BitwiseNot(_)
        | Bitvector32Term::If { .. }
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Int64From32(_)
        | Bitvector32Term::UInt64From32(_)
        | Bitvector32Term::Int64FromUInt32(_)
        | Bitvector32Term::UInt64FromInt32(_)
        | Bitvector32Term::UInt64FromInt64(_)
        | Bitvector32Term::Int64Add(_, _)
        | Bitvector32Term::Int64Subtract(_, _)
        | Bitvector32Term::Int64Multiply(_, _)
        | Bitvector32Term::Int64Divide(_, _)
        | Bitvector32Term::Int64Remainder(_, _)
        | Bitvector32Term::Int64ShiftLeft(_, _)
        | Bitvector32Term::Int64ArithmeticShiftRight(_, _)
        | Bitvector32Term::Int64BitwiseAnd(_, _)
        | Bitvector32Term::Int64BitwiseOr(_, _)
        | Bitvector32Term::Int64BitwiseXor(_, _)
        | Bitvector32Term::Int64BitwiseNot(_)
        | Bitvector32Term::UInt64Add(_, _)
        | Bitvector32Term::UInt64Subtract(_, _)
        | Bitvector32Term::UInt64Multiply(_, _)
        | Bitvector32Term::UInt64Divide(_, _)
        | Bitvector32Term::UInt64Remainder(_, _)
        | Bitvector32Term::UInt64ShiftLeft(_, _)
        | Bitvector32Term::UInt64LogicalShiftRight(_, _)
        | Bitvector32Term::UInt64BitwiseAnd(_, _)
        | Bitvector32Term::UInt64BitwiseOr(_, _)
        | Bitvector32Term::UInt64BitwiseXor(_, _)
        | Bitvector32Term::UInt64BitwiseNot(_) => None,
    }
}

fn signed_order_goal(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(&Bitvector32Term, &Bitvector32Term, bool)> {
    match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true) => Some((left, right, true)),
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false) => {
            Some((right, left, false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            Some((left, right, false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false) => {
            Some((right, left, true))
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true) => {
            Some((right, left, true))
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            Some((left, right, false))
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true) => {
            Some((right, left, false))
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            Some((left, right, true))
        }
        _ => None,
    }
}

fn non_affine_goal_is_proven(
    goal: &Proposition,
    bounds: &BTreeMap<Bitvector32Term, (i64, i64)>,
) -> Option<bool> {
    let (condition, value) = match goal {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !value),
            _ => return None,
        },
        _ => return None,
    };
    if let ConditionTerm::Bitvector32Equal(left, right) = condition {
        let (left_lower, left_upper) =
            signed_term_interval(left, bounds, ARITHMETIC_INTERVAL_DEPTH)?;
        let (right_lower, right_upper) =
            signed_term_interval(right, bounds, ARITHMETIC_INTERVAL_DEPTH)?;
        return Some(if value {
            left_lower == left_upper && right_lower == right_upper && left_lower == right_lower
        } else {
            left_upper < right_lower || right_upper < left_lower
        });
    }
    let (left, right, strict) = signed_order_goal(condition, value)?;

    // Arithmetic right shift preserves the order against a nonnegative
    // operand. An interval comparison cannot see that both sides share the
    // same operand, so retain this checked algebraic rule explicitly.
    if let Bitvector32Term::ArithmeticShiftRight(shifted, shift) = left
        && shifted.as_ref() == right
        && (0..32).contains(&(shift.as_const()? as i32))
    {
        let (lower, _) = signed_term_interval(shifted, bounds, ARITHMETIC_INTERVAL_DEPTH)?;
        return Some(lower >= 0);
    }

    let (_, left_upper) = signed_term_interval(left, bounds, ARITHMETIC_INTERVAL_DEPTH)?;
    let (right_lower, _) = signed_term_interval(right, bounds, ARITHMETIC_INTERVAL_DEPTH)?;
    Some(if strict {
        left_upper < right_lower
    } else {
        left_upper <= right_lower
    })
}

fn collect_signed_affine_terms(
    term: &Bitvector32Term,
    coefficient: i64,
    terms: &mut BTreeMap<Bitvector32Term, i64>,
    constant: &mut i64,
) -> Option<()> {
    crate::instrumentation::record_deterministic_work(1);
    match term {
        Bitvector32Term::Constant(value) => {
            let value = i64::from(*value as i32);
            *constant = constant.checked_add(coefficient.checked_mul(value)?)?;
        }
        Bitvector32Term::Add(left, right) => {
            collect_signed_affine_terms(left, coefficient, terms, constant)?;
            collect_signed_affine_terms(right, coefficient, terms, constant)?;
        }
        Bitvector32Term::Subtract(left, right) => {
            collect_signed_affine_terms(left, coefficient, terms, constant)?;
            collect_signed_affine_terms(right, coefficient.checked_neg()?, terms, constant)?;
        }
        Bitvector32Term::Multiply(left, right) => {
            if let Some(value) = left.as_const() {
                let value = i64::from(value as i32);
                collect_signed_affine_terms(
                    right,
                    coefficient.checked_mul(value)?,
                    terms,
                    constant,
                )?;
            } else if let Some(value) = right.as_const() {
                let value = i64::from(value as i32);
                collect_signed_affine_terms(
                    left,
                    coefficient.checked_mul(value)?,
                    terms,
                    constant,
                )?;
            } else {
                return None;
            }
        }
        Bitvector32Term::Variable(_)
        | Bitvector32Term::MemoryLoad(_, _)
        | Bitvector32Term::PointerAddress(_)
        | Bitvector32Term::PureFunctionApplication { .. } => {
            let atom = crate::kernel::eval::canonical_term(term);
            let updated = terms
                .get(&atom)
                .copied()
                .unwrap_or_default()
                .checked_add(coefficient)?;
            if updated == 0 {
                terms.remove(&atom);
            } else {
                terms.insert(atom, updated);
            }
        }
        Bitvector32Term::Divide(_, _)
        | Bitvector32Term::UnsignedDivide(_, _)
        | Bitvector32Term::Remainder(_, _)
        | Bitvector32Term::UnsignedRemainder(_, _)
        | Bitvector32Term::ShiftLeft(_, _)
        | Bitvector32Term::ArithmeticShiftRight(_, _)
        | Bitvector32Term::LogicalShiftRight(_, _)
        | Bitvector32Term::BitwiseAnd(_, _)
        | Bitvector32Term::BitwiseOr(_, _)
        | Bitvector32Term::BitwiseXor(_, _)
        | Bitvector32Term::BitwiseNot(_)
        | Bitvector32Term::If { .. }
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Int64From32(_)
        | Bitvector32Term::UInt64From32(_)
        | Bitvector32Term::Int64FromUInt32(_)
        | Bitvector32Term::UInt64FromInt32(_)
        | Bitvector32Term::UInt64FromInt64(_)
        | Bitvector32Term::Int64Add(_, _)
        | Bitvector32Term::Int64Subtract(_, _)
        | Bitvector32Term::Int64Multiply(_, _)
        | Bitvector32Term::Int64Divide(_, _)
        | Bitvector32Term::Int64Remainder(_, _)
        | Bitvector32Term::Int64ShiftLeft(_, _)
        | Bitvector32Term::Int64ArithmeticShiftRight(_, _)
        | Bitvector32Term::Int64BitwiseAnd(_, _)
        | Bitvector32Term::Int64BitwiseOr(_, _)
        | Bitvector32Term::Int64BitwiseXor(_, _)
        | Bitvector32Term::Int64BitwiseNot(_)
        | Bitvector32Term::UInt64Add(_, _)
        | Bitvector32Term::UInt64Subtract(_, _)
        | Bitvector32Term::UInt64Multiply(_, _)
        | Bitvector32Term::UInt64Divide(_, _)
        | Bitvector32Term::UInt64Remainder(_, _)
        | Bitvector32Term::UInt64ShiftLeft(_, _)
        | Bitvector32Term::UInt64LogicalShiftRight(_, _)
        | Bitvector32Term::UInt64BitwiseAnd(_, _)
        | Bitvector32Term::UInt64BitwiseOr(_, _)
        | Bitvector32Term::UInt64BitwiseXor(_, _)
        | Bitvector32Term::UInt64BitwiseNot(_)
        | Bitvector32Term::Float32Negate(_)
        | Bitvector32Term::Float32Binary { .. }
        | Bitvector32Term::Float64Negate(_)
        | Bitvector32Term::Float64Binary { .. } => return None,
    }
    Some(())
}

fn signed_affine_difference(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<SignedAffineForm> {
    let mut terms = BTreeMap::new();
    let mut constant = 0;
    collect_signed_affine_terms(left, 1, &mut terms, &mut constant)?;
    collect_signed_affine_terms(right, -1, &mut terms, &mut constant)?;
    Some(SignedAffineForm { terms, constant })
}

fn signed_affine_inequality(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    strict: bool,
) -> Option<SignedAffineInequality> {
    let difference = signed_affine_difference(left, right)?;
    let threshold = if strict { -1i64 } else { 0 };
    Some(SignedAffineInequality {
        terms: difference.terms,
        bound: threshold.checked_sub(difference.constant)?,
    })
}

fn signed_affine_condition(condition: &ConditionTerm, value: bool) -> Option<SignedAffineClaim> {
    match (condition, value) {
        (ConditionTerm::Constant(constant), value) => {
            Some(SignedAffineClaim::Constant(*constant == value))
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterThan(right, left), true)
        | (ConditionTerm::Bitvector32SignedLessEqual(right, left), false)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => Some(
            SignedAffineClaim::Inequality(signed_affine_inequality(left, right, true)?),
        ),
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(right, left), true)
        | (ConditionTerm::Bitvector32SignedLessThan(right, left), false)
        | (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => Some(
            SignedAffineClaim::Inequality(signed_affine_inequality(left, right, false)?),
        ),
        (ConditionTerm::Bitvector32Equal(left, right), true) => Some(SignedAffineClaim::Equality(
            signed_affine_difference(left, right)?,
        )),
        (ConditionTerm::Bitvector32Equal(left, right), false) => Some(
            SignedAffineClaim::Disequality(signed_affine_difference(left, right)?),
        ),
        _ => None,
    }
}

fn signed_affine_claim(proposition: &Proposition) -> Option<SignedAffineClaim> {
    match proposition {
        Proposition::ConditionIs(condition, value) => signed_affine_condition(condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                signed_affine_condition(condition, !*value)
            }
            _ => None,
        },
        _ => None,
    }
}

fn signed_affine_atom_bounds(
    inequalities: &[SignedAffineInequality],
) -> BTreeMap<Bitvector32Term, (i64, i64)> {
    let mut bounds = BTreeMap::new();
    for inequality in inequalities {
        crate::instrumentation::record_deterministic_work(1);
        if inequality.terms.len() != 1 {
            continue;
        }
        let (term, coefficient) = inequality
            .terms
            .iter()
            .next()
            .expect("one-term inequality has one entry");
        let entry = bounds
            .entry(term.clone())
            .or_insert((i64::from(i32::MIN), i64::from(i32::MAX)));
        match *coefficient {
            1 => entry.1 = entry.1.min(inequality.bound),
            -1 => entry.0 = entry.0.max(inequality.bound.saturating_neg()),
            _ => {}
        }
    }
    bounds
}

fn signed_affine_form_range(
    form: &SignedAffineForm,
    bounds: &BTreeMap<Bitvector32Term, (i64, i64)>,
) -> Option<(i128, i128)> {
    let mut minimum = i128::from(form.constant);
    let mut maximum = i128::from(form.constant);
    for (term, coefficient) in &form.terms {
        crate::instrumentation::record_deterministic_work(1);
        let (lower, upper) = bounds
            .get(term)
            .copied()
            .unwrap_or((i64::from(i32::MIN), i64::from(i32::MAX)));
        let coefficient = i128::from(*coefficient);
        let lower = i128::from(lower);
        let upper = i128::from(upper);
        if 0 <= coefficient {
            minimum = minimum.checked_add(coefficient.checked_mul(lower)?)?;
            maximum = maximum.checked_add(coefficient.checked_mul(upper)?)?;
        } else {
            minimum = minimum.checked_add(coefficient.checked_mul(upper)?)?;
            maximum = maximum.checked_add(coefficient.checked_mul(lower)?)?;
        }
    }
    Some((minimum, maximum))
}

fn signed_affine_term_is_defined(
    term: &Bitvector32Term,
    bounds: &BTreeMap<Bitvector32Term, (i64, i64)>,
) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    match term {
        Bitvector32Term::Constant(_)
        | Bitvector32Term::Variable(_)
        | Bitvector32Term::MemoryLoad(_, _)
        | Bitvector32Term::PointerAddress(_)
        | Bitvector32Term::PureFunctionApplication { .. } => true,
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right) => {
            if !signed_affine_term_is_defined(left, bounds)
                || !signed_affine_term_is_defined(right, bounds)
            {
                return false;
            }
            let Some(form) = signed_affine_difference(term, &Bitvector32Term::Constant(0)) else {
                return false;
            };
            let Some((minimum, maximum)) = signed_affine_form_range(&form, bounds) else {
                return false;
            };
            i128::from(i32::MIN) <= minimum && maximum <= i128::from(i32::MAX)
        }
        Bitvector32Term::Divide(_, _)
        | Bitvector32Term::UnsignedDivide(_, _)
        | Bitvector32Term::Remainder(_, _)
        | Bitvector32Term::UnsignedRemainder(_, _)
        | Bitvector32Term::ShiftLeft(_, _)
        | Bitvector32Term::ArithmeticShiftRight(_, _)
        | Bitvector32Term::LogicalShiftRight(_, _)
        | Bitvector32Term::BitwiseAnd(_, _)
        | Bitvector32Term::BitwiseOr(_, _)
        | Bitvector32Term::BitwiseXor(_, _)
        | Bitvector32Term::BitwiseNot(_)
        | Bitvector32Term::If { .. }
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Int64From32(_)
        | Bitvector32Term::UInt64From32(_)
        | Bitvector32Term::Int64FromUInt32(_)
        | Bitvector32Term::UInt64FromInt32(_)
        | Bitvector32Term::UInt64FromInt64(_)
        | Bitvector32Term::Int64Add(_, _)
        | Bitvector32Term::Int64Subtract(_, _)
        | Bitvector32Term::Int64Multiply(_, _)
        | Bitvector32Term::Int64Divide(_, _)
        | Bitvector32Term::Int64Remainder(_, _)
        | Bitvector32Term::Int64ShiftLeft(_, _)
        | Bitvector32Term::Int64ArithmeticShiftRight(_, _)
        | Bitvector32Term::Int64BitwiseAnd(_, _)
        | Bitvector32Term::Int64BitwiseOr(_, _)
        | Bitvector32Term::Int64BitwiseXor(_, _)
        | Bitvector32Term::Int64BitwiseNot(_)
        | Bitvector32Term::UInt64Add(_, _)
        | Bitvector32Term::UInt64Subtract(_, _)
        | Bitvector32Term::UInt64Multiply(_, _)
        | Bitvector32Term::UInt64Divide(_, _)
        | Bitvector32Term::UInt64Remainder(_, _)
        | Bitvector32Term::UInt64ShiftLeft(_, _)
        | Bitvector32Term::UInt64LogicalShiftRight(_, _)
        | Bitvector32Term::UInt64BitwiseAnd(_, _)
        | Bitvector32Term::UInt64BitwiseOr(_, _)
        | Bitvector32Term::UInt64BitwiseXor(_, _)
        | Bitvector32Term::UInt64BitwiseNot(_)
        | Bitvector32Term::Float32Negate(_)
        | Bitvector32Term::Float32Binary { .. }
        | Bitvector32Term::Float64Negate(_)
        | Bitvector32Term::Float64Binary { .. } => false,
    }
}

fn signed_affine_goal_is_defined(
    goal: &Proposition,
    inequalities: &[SignedAffineInequality],
) -> bool {
    let bounds = signed_affine_atom_bounds(inequalities);
    let condition = match goal {
        Proposition::ConditionIs(condition, _) => condition,
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, _) => condition,
            _ => return false,
        },
        _ => return false,
    };
    match condition {
        ConditionTerm::Constant(_) => true,
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right) => {
            signed_affine_term_is_defined(left, &bounds)
                && signed_affine_term_is_defined(right, &bounds)
        }
        _ => false,
    }
}

fn inequality_implies(available: &SignedAffineInequality, goal: &SignedAffineInequality) -> bool {
    crate::instrumentation::record_deterministic_work(1);
    available.terms == goal.terms && available.bound <= goal.bound
}

fn add_inequality(sum: &mut SignedAffineInequality, addend: &SignedAffineInequality) -> Option<()> {
    sum.bound = sum.bound.checked_add(addend.bound)?;
    for (term, coefficient) in &addend.terms {
        crate::instrumentation::record_deterministic_work(1);
        let updated = sum
            .terms
            .get(term)
            .copied()
            .unwrap_or_default()
            .checked_add(*coefficient)?;
        if updated == 0 {
            sum.terms.remove(term);
        } else {
            sum.terms.insert(term.clone(), updated);
        }
    }
    Some(())
}

/// Checks one explicit signed arithmetic certificate.
///
/// The listed propositions are the checker's entire premise universe. A
/// combined inequality uses each selected inequality with coefficient one, so
/// repeating a premise explicitly permits a larger positive coefficient.
/// Bounded nonlinear and bitwise terms use only intervals reconstructed from
/// those same premises. Checking is one structural pass over the selected
/// propositions; no ambient facts are searched and no closure is retained
/// after the current goal closes.
pub(crate) fn check_signed_affine_arithmetic(
    goal: &Proposition,
    premises: &[Proposition],
) -> Result<(), ArithmeticCheckError> {
    let goal_proposition = goal;
    let affine_goal = signed_affine_claim(goal);
    let mut inequalities = Vec::new();
    let mut equalities = Vec::new();
    for (index, premise) in premises.iter().enumerate() {
        crate::instrumentation::record_deterministic_work(1);
        let mut conjuncts = Vec::new();
        atomic_conjuncts(premise, &mut conjuncts);
        for conjunct in conjuncts {
            match signed_affine_claim(conjunct)
                .ok_or(ArithmeticCheckError::UnsupportedPremise(index))?
            {
                SignedAffineClaim::Inequality(inequality) => inequalities.push(inequality),
                SignedAffineClaim::Equality(equality) => equalities.push(equality),
                SignedAffineClaim::Constant(true) => {}
                SignedAffineClaim::Constant(false) | SignedAffineClaim::Disequality(_) => {
                    return Err(ArithmeticCheckError::UnsupportedPremise(index));
                }
            }
        }
    }
    let proved = if let Some(goal) = affine_goal {
        if !signed_affine_goal_is_defined(goal_proposition, &inequalities) {
            return Err(ArithmeticCheckError::GoalMayBeUndefined);
        }
        match goal {
            SignedAffineClaim::Constant(value) => value,
            SignedAffineClaim::Equality(form) => {
                (form.terms.is_empty() && form.constant == 0)
                    || equalities.iter().any(|available| {
                        available == &form
                            || (available.constant
                                == form.constant.checked_neg().unwrap_or(i64::MIN)
                                && available.terms.len() == form.terms.len()
                                && available.terms.iter().all(|(term, coefficient)| {
                                    form.terms.get(term) == coefficient.checked_neg().as_ref()
                                }))
                    })
            }
            SignedAffineClaim::Disequality(form) => {
                form.terms.is_empty() && form.constant.rem_euclid(1i64 << 32) != 0
            }
            SignedAffineClaim::Inequality(goal) => {
                if goal.terms.is_empty() && 0 <= goal.bound {
                    true
                } else if inequalities
                    .iter()
                    .any(|available| inequality_implies(available, &goal))
                {
                    true
                } else if inequalities.is_empty() {
                    false
                } else {
                    let mut sum = SignedAffineInequality {
                        terms: BTreeMap::new(),
                        bound: 0,
                    };
                    inequalities
                        .iter()
                        .all(|inequality| add_inequality(&mut sum, inequality).is_some())
                        && inequality_implies(&sum, &goal)
                }
            }
        }
    } else {
        non_affine_goal_is_proven(goal_proposition, &signed_affine_atom_bounds(&inequalities))
            .ok_or(ArithmeticCheckError::UnsupportedGoal)?
    };
    proved
        .then_some(())
        .ok_or(ArithmeticCheckError::DoesNotFollow)
}

#[cfg(test)]
mod arithmetic_tests {
    use super::*;

    fn proposition(condition: ConditionTerm) -> Proposition {
        Proposition::ConditionIs(condition, true)
    }

    fn nonnegative(term: Bitvector32Term) -> Proposition {
        proposition(ConditionTerm::signed_greater_equal(
            term,
            Bitvector32Term::Constant(0),
        ))
    }

    fn less_equal(left: u64, right: u64) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessEqual(
                Box::new(Bitvector32Term::Variable(Variable(left))),
                Box::new(Bitvector32Term::Variable(Variable(right))),
            ),
            true,
        )
    }

    #[test]
    fn explicit_affine_chain_check_scales_near_linearly() {
        let mut samples = Vec::new();
        for size in [16_u64, 32, 64, 128] {
            let premises = (0..size)
                .map(|index| less_equal(index, index + 1))
                .collect::<Vec<_>>();
            let goal = less_equal(0, size);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                check_signed_affine_arithmetic(&goal, &premises)
            });
            result.expect("the explicit inequality chain should prove its endpoint order");
            assert!(
                work > 0,
                "the arithmetic checker must account deterministic work"
            );
            samples.push((size, work));
        }
        assert!(
            samples
                .windows(2)
                .all(|pair| pair[1].1 <= pair[0].1.saturating_mul(3)),
            "explicit arithmetic checking grew faster than near-linearly: {samples:?}"
        );
    }

    #[test]
    fn arithmetic_proves_nonnegative_remainder_range() {
        let x = Bitvector32Term::Variable(Variable(94_001));
        let remainder = Bitvector32Term::remainder(x.clone(), Bitvector32Term::Constant(4));
        let premises = vec![nonnegative(x)];
        let lower_bound = proposition(ConditionTerm::signed_greater_equal(
            remainder.clone(),
            Bitvector32Term::Constant(0),
        ));
        let upper_bound = proposition(ConditionTerm::signed_less_than(
            remainder,
            Bitvector32Term::Constant(4),
        ));

        check_signed_affine_arithmetic(&lower_bound, &premises)
            .expect("a nonnegative remainder should have a nonnegative lower bound");
        check_signed_affine_arithmetic(&upper_bound, &premises)
            .expect("a remainder by four should be less than four");
    }

    #[test]
    fn arithmetic_proves_mask_range_without_operand_bounds() {
        let x = Bitvector32Term::Variable(Variable(94_002));
        let masked = Bitvector32Term::bitwise_and(x, Bitvector32Term::Constant(0xff));
        let goal = proposition(ConditionTerm::signed_less_equal(
            masked,
            Bitvector32Term::Constant(0xff),
        ));

        check_signed_affine_arithmetic(&goal, &[])
            .expect("a nonnegative constant mask bounds a bitwise-and result");
    }

    #[test]
    fn arithmetic_proves_right_shift_does_not_increase_nonnegative_value() {
        let x = Bitvector32Term::Variable(Variable(94_003));
        let shifted =
            Bitvector32Term::arithmetic_shift_right(x.clone(), Bitvector32Term::Constant(1));
        let goal = proposition(ConditionTerm::signed_less_equal(shifted, x.clone()));

        check_signed_affine_arithmetic(&goal, &[nonnegative(x)])
            .expect("arithmetic right shift should not increase a nonnegative value");
    }

    #[test]
    fn arithmetic_rejects_unbounded_product() {
        let x = Bitvector32Term::Variable(Variable(94_004));
        let y = Bitvector32Term::Variable(Variable(94_005));
        let product = Bitvector32Term::multiply(x.clone(), y.clone());
        let goal = proposition(ConditionTerm::signed_less_equal(
            product,
            Bitvector32Term::Constant(100),
        ));

        assert!(matches!(
            check_signed_affine_arithmetic(&goal, &[nonnegative(x)]),
            Err(ArithmeticCheckError::UnsupportedGoal)
        ));
    }
}

pub(crate) fn normalizes_context_free(goal: &Proposition) -> bool {
    PureFactContext::new()
        .derive_atomic_proposition(goal)
        .or_else(|| PureFactContext::new().derive_proposition(goal))
        .is_some()
}

pub(crate) enum ForallInt32InstantiationError {
    RequiresUniversal,
    UnsupportedSort,
    MissingGuard(Proposition),
    KernelRejected,
    InvalidTheorem,
    ChangedQuantifiedPremise,
    OmittedGuard,
    ChangedGuard,
    UnexpectedConclusion,
}

pub(crate) fn discharge_instantiated_guards(
    instantiated: Proposition,
    premises: &[Proposition],
) -> Result<(Vec<Proposition>, Proposition), ForallInt32InstantiationError> {
    let premise_assumptions = assumptions_from_propositions(premises);
    let mut premise_conjuncts = Vec::new();
    for premise in premises {
        atomic_conjuncts(premise, &mut premise_conjuncts);
    }
    let premise_conjuncts = premise_conjuncts.into_iter().cloned().collect::<Vec<_>>();
    let discharges = |conjunct: &Proposition| {
        normalizes_context_free(conjunct)
            || premise_conjuncts.iter().any(|premise| {
                premise == conjunct || condition_polarity_equivalent(premise, conjunct)
            })
            || premise_assumptions
                .derive_atomic_proposition(conjunct)
                .is_some()
            || premise_assumptions
                .derive_simp_atomic_proposition(conjunct)
                .is_some()
    };
    let mut guards = Vec::new();
    let mut current = instantiated;
    while let Proposition::Implies(guard, body) = current {
        let mut conjuncts = Vec::new();
        atomic_conjuncts(&guard, &mut conjuncts);
        if let Some(missing) = conjuncts.iter().find(|conjunct| !discharges(conjunct)) {
            return Err(ForallInt32InstantiationError::MissingGuard(
                (*missing).clone(),
            ));
        }
        guards.push(*guard);
        current = *body;
    }
    Ok((guards, current))
}

pub(crate) fn check_forall_int32_instantiation(
    quantified: &Proposition,
    argument: Bitvector32Term,
    premises: &[Proposition],
) -> Result<Proposition, ForallInt32InstantiationError> {
    let Proposition::ForAll { var, sort, body } = quantified else {
        return Err(ForallInt32InstantiationError::RequiresUniversal);
    };
    if *sort != Sort::CInt32 {
        return Err(ForallInt32InstantiationError::UnsupportedSort);
    }

    let instantiated = substitute_int32_variable_in_proposition(body, *var, argument.clone());
    let (guards, conclusion) = discharge_instantiated_guards(instantiated, premises)?;
    let theorem = prove_forall_int32_application(quantified, argument, &guards)
        .ok_or(ForallInt32InstantiationError::KernelRejected)?;
    let Proposition::Implies(theorem_quantified, mut theorem_body) = theorem.proposition().clone()
    else {
        return Err(ForallInt32InstantiationError::InvalidTheorem);
    };
    if theorem_quantified.as_ref() != quantified {
        return Err(ForallInt32InstantiationError::ChangedQuantifiedPremise);
    }
    for guard in &guards {
        let Proposition::Implies(theorem_guard, next) = theorem_body.as_ref() else {
            return Err(ForallInt32InstantiationError::OmittedGuard);
        };
        if theorem_guard.as_ref() != guard {
            return Err(ForallInt32InstantiationError::ChangedGuard);
        }
        theorem_body = next.clone();
    }
    if theorem_body.as_ref() != &conclusion {
        return Err(ForallInt32InstantiationError::UnexpectedConclusion);
    }
    Ok(conclusion)
}

fn assumptions_from_propositions(propositions: &[Proposition]) -> PureFactContext {
    propositions
        .iter()
        .cloned()
        .fold(PureFactContext::new(), PureFactContext::assume_proposition)
}

/// Checks the small float certificate used by `simp using`: an IEEE
/// comparison of one finite value with itself has the corresponding reflexive
/// result. The finite classification must be one of the explicit premises;
/// no ambient context is consulted here.
pub(crate) fn check_float_reflexive_comparison(
    proposition: &Proposition,
    premises: &[Proposition],
) -> bool {
    let Proposition::ConditionIs(condition, expected) = proposition else {
        return false;
    };
    let (operator, left, right, finite) = match condition {
        ConditionTerm::Float32(CFloatCondition::Comparison {
            operator,
            left,
            right,
        }) => (
            *operator,
            left.as_ref(),
            right.as_ref(),
            ConditionTerm::float32_classification(
                left.as_ref().clone(),
                CFloatClassification::Finite,
            ),
        ),
        ConditionTerm::Float64(CFloatCondition::Comparison {
            operator,
            left,
            right,
        }) => (
            *operator,
            left.as_ref(),
            right.as_ref(),
            ConditionTerm::float64_classification(
                left.as_ref().clone(),
                CFloatClassification::Finite,
            ),
        ),
        _ => return false,
    };
    if left != right {
        return false;
    }
    let assumptions = assumptions_from_propositions(premises);
    if assumptions.decide(&finite) != Some(true) {
        return false;
    }
    let reflexive = matches!(
        operator,
        CComparisonOperator::Equal
            | CComparisonOperator::LessEqual
            | CComparisonOperator::GreaterEqual
    );
    *expected == reflexive
}

pub(crate) fn is_implicit_fact_transport_context(proposition: &Proposition) -> bool {
    matches!(
        proposition,
        Proposition::CMemoryLoadable { .. }
            | Proposition::CMemoryCanStore { .. }
            | Proposition::CMemoryDisjoint { .. }
            | Proposition::CResourceSeparate { .. }
    )
}

/// The fixed set of condition forms accepted by
/// `condition_polarity_equivalent`. Callers can probe an exact index for these
/// instead of maintaining another project-sized index.
pub(crate) fn condition_polarity_forms(proposition: &Proposition) -> Vec<Proposition> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition.clone(), *value),
        Proposition::Not(negated) => match negated.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition.clone(), !value),
            _ => return Vec::new(),
        },
        _ => return Vec::new(),
    };
    let mut conditions = vec![(condition, value)];
    if let Some((left, right, strict)) =
        canonical_order_condition(&conditions[0].0, conditions[0].1)
    {
        let left = Box::new(left);
        let right = Box::new(right);
        let mut equivalent = if strict {
            vec![
                (
                    ConditionTerm::Bitvector32SignedLessThan(left.clone(), right.clone()),
                    true,
                ),
                (
                    ConditionTerm::Bitvector32SignedGreaterEqual(left.clone(), right.clone()),
                    false,
                ),
                (
                    ConditionTerm::Bitvector32SignedLessEqual(right.clone(), left.clone()),
                    false,
                ),
                (
                    ConditionTerm::Bitvector32SignedGreaterThan(right, left),
                    true,
                ),
            ]
        } else {
            vec![
                (
                    ConditionTerm::Bitvector32SignedLessEqual(left.clone(), right.clone()),
                    true,
                ),
                (
                    ConditionTerm::Bitvector32SignedGreaterThan(left.clone(), right.clone()),
                    false,
                ),
                (
                    ConditionTerm::Bitvector32SignedLessThan(right.clone(), left.clone()),
                    false,
                ),
                (
                    ConditionTerm::Bitvector32SignedGreaterEqual(right, left),
                    true,
                ),
            ]
        };
        conditions.append(&mut equivalent);
    }
    let mut forms = Vec::new();
    for (condition, value) in conditions {
        let direct = Proposition::ConditionIs(condition.clone(), value);
        if !forms.contains(&direct) {
            forms.push(direct);
        }
        let negated = Proposition::Not(Box::new(Proposition::ConditionIs(condition, !value)));
        if !forms.contains(&negated) {
            forms.push(negated);
        }
    }
    forms
}

pub(crate) fn exact_fact_is_available(required: &Proposition, available: &[Proposition]) -> bool {
    available
        .iter()
        .any(|fact| exact_fact_contains_conjunct(fact, required))
}

/// Structural proposition equality whose condition leaves are decided by the
/// kernel's snapshot bridge: two forms of one compound fact whose load
/// atoms carry different certified snapshots. Structure must match exactly,
/// so this never accepts a weaker or stronger proposition.
fn propositions_equal_modulo_proven_snapshots(
    left: &Proposition,
    right: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    if left == right {
        return true;
    }
    match (left, right) {
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => {
            left_value == right_value
                && assumptions
                    .conditions_equal_modulo_proven_snapshots(left_condition, right_condition)
        }
        (Proposition::Implies(left_a, left_b), Proposition::Implies(right_a, right_b)) => {
            propositions_equal_modulo_proven_snapshots(left_a, right_a, assumptions)
                && propositions_equal_modulo_proven_snapshots(left_b, right_b, assumptions)
        }
        (Proposition::And(left_a, left_b), Proposition::And(right_a, right_b))
        | (Proposition::Or(left_a, left_b), Proposition::Or(right_a, right_b)) => {
            propositions_equal_modulo_proven_snapshots(left_a, right_a, assumptions)
                && propositions_equal_modulo_proven_snapshots(left_b, right_b, assumptions)
        }
        (Proposition::Not(left_body), Proposition::Not(right_body)) => {
            propositions_equal_modulo_proven_snapshots(left_body, right_body, assumptions)
        }
        // Separations compare part-wise; the work lives in a never-inlined
        // helper because this function participates in deep proposition
        // recursion where added frame bytes overflow the stack.
        (
            left @ Proposition::CResourceSeparate { .. },
            right @ Proposition::CResourceSeparate { .. },
        ) => separations_equal_modulo_proven_snapshots(left, right, assumptions),
        _ => false,
    }
}

/// Proves that one already-selected structural candidate is the same fact as
/// `required` across certified memory snapshots. Candidate selection remains
/// the caller's responsibility; this operation never searches a context.
/// Resolves load variables in comparison term positions only:
/// condition terms and pointer offsets, never descending into embedded
/// memory snapshots. The full resolver walks whole snapshots and is far too
/// expensive for per-candidate comparison paths.
fn expand_load_variables_shallow(bits: &Bitvector32Term) -> Bitvector32Term {
    match bits {
        Bitvector32Term::Variable(variable) if crate::kernel::is_load_variable(variable) => {
            match crate::kernel::registered_load_for_variable(variable) {
                Some((memory, pointer)) => Bitvector32Term::MemoryLoad(memory, Box::new(pointer)),
                None => bits.clone(),
            }
        }
        Bitvector32Term::Add(left, right) => Bitvector32Term::Add(
            Box::new(expand_load_variables_shallow(left)),
            Box::new(expand_load_variables_shallow(right)),
        ),
        Bitvector32Term::Subtract(left, right) => Bitvector32Term::Subtract(
            Box::new(expand_load_variables_shallow(left)),
            Box::new(expand_load_variables_shallow(right)),
        ),
        Bitvector32Term::Multiply(left, right) => Bitvector32Term::Multiply(
            Box::new(expand_load_variables_shallow(left)),
            Box::new(expand_load_variables_shallow(right)),
        ),
        _ => bits.clone(),
    }
}

fn expand_offset_load_variables_shallow(value: &PointerOffsetTerm) -> PointerOffsetTerm {
    match value {
        PointerOffsetTerm::Int32Scaled { value, byte_width } => PointerOffsetTerm::Int32Scaled {
            value: Box::new(expand_load_variables_shallow(value)),
            byte_width: *byte_width,
        },
        PointerOffsetTerm::Add(left, right) => PointerOffsetTerm::Add(
            Box::new(expand_offset_load_variables_shallow(left)),
            Box::new(expand_offset_load_variables_shallow(right)),
        ),
        _ => value.clone(),
    }
}

/// `snapshot_bridged_fact_is_available` where the caller already holds the
/// assumption context the bridge should reason in.
///
/// Candidates still come only from `available`, so widening the assumptions
/// cannot make an unlisted fact available — the wider context only decides
/// whether two forms denote one fact.
/// A separation required at one snapshot is available when an available
/// separation names the same regions modulo the certified frame. Condition
/// facts need no such bridge: terms are canonical at creation, so one fact
/// has one form.
pub(crate) fn separation_bridged_fact_is_available(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &PureFactContext,
    framing: &[ExecutionPureFact],
) -> bool {
    matches!(required, Proposition::CResourceSeparate { .. })
        && separation_bridged_available(required, available, assumptions, framing)
}

pub(crate) fn exact_fact_contains_conjunct(fact: &Proposition, required: &Proposition) -> bool {
    condition_polarity_equivalent(fact, required)
        || matches!(fact, Proposition::And(left, right)
            if exact_fact_contains_conjunct(left, required)
                || exact_fact_contains_conjunct(right, required))
}

/// True only when `required` is a proper conjunct of an available conjunction.
/// This is the exact, structural rule checked by the simple `extract` tactic;
/// it performs no normalization, snapshot transport, or proposition search.
pub(crate) fn exact_proper_conjunct_is_available(
    required: &Proposition,
    available: &[Proposition],
) -> bool {
    available.iter().any(|fact| {
        matches!(fact, Proposition::And(_, _)) && exact_fact_contains_conjunct(fact, required)
    })
}

/// Modus ponens as a bounded structural rule for the simple `extract` tactic:
/// `required` is a consequent reached by walking an available (possibly
/// chained) implication whose antecedents are each themselves available
/// facts. Antecedents and the consequent match exactly, up to condition
/// polarity, or by the snapshot bridge — never by derivation. Work is linear
/// in the available facts times the implication depth; nothing is searched.
pub(crate) fn discharged_implication_consequent_is_available(
    required: &Proposition,
    available: &[Proposition],
) -> bool {
    if !available
        .iter()
        .any(|fact| matches!(fact, Proposition::Implies(_, _)))
    {
        return false;
    }
    let assumptions = assumptions_from_propositions(available);
    let fact_available = |needed: &Proposition| {
        pure_fact_is_available(needed, available)
            || available.iter().any(|fact| {
                condition_polarity_equivalent(fact, needed)
                    || propositions_equal_modulo_proven_snapshots(fact, needed, &assumptions)
            })
    };
    available.iter().any(|fact| {
        let mut current = fact;
        while let Proposition::Implies(antecedent, consequent) = current {
            if !fact_available(antecedent) {
                return false;
            }
            if propositions_equal_modulo_proven_snapshots(consequent, required, &assumptions) {
                return true;
            }
            current = consequent;
        }
        false
    })
}

pub(crate) fn propositions_are_exact_negations(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => left_condition == right_condition && left_value != right_value,
        (Proposition::Not(body), proposition) | (proposition, Proposition::Not(body)) => {
            body.as_ref() == proposition
                || matches!(
                    (body.as_ref(), proposition),
                    (
                        Proposition::ConditionIs(left_condition, left_value),
                        Proposition::ConditionIs(right_condition, right_value),
                    ) if left_condition == right_condition && left_value == right_value
                )
        }
        _ => false,
    }
}

pub(crate) fn condition_polarity_equivalent(left: &Proposition, right: &Proposition) -> bool {
    if left == right {
        return true;
    }
    // A negated condition fact is the same total boolean condition with the
    // opposite expected value; flattening lets one form compare against
    // the other and against the canonical order form of either.
    let flatten = |proposition: &Proposition| match proposition {
        Proposition::ConditionIs(condition, value) => Some((condition.clone(), *value)),
        Proposition::Not(negated) => match negated.as_ref() {
            Proposition::ConditionIs(condition, value) => Some((condition.clone(), !value)),
            _ => None,
        },
        _ => None,
    };
    let (Some((left_condition, left_value)), Some((right_condition, right_value))) =
        (flatten(left), flatten(right))
    else {
        return false;
    };
    if left_condition == right_condition && left_value == right_value {
        return true;
    }
    matches!(
        (
            canonical_order_condition(&left_condition, left_value),
            canonical_order_condition(&right_condition, right_value),
        ),
        (Some(left), Some(right)) if left == right
    )
}

fn canonical_order_condition(
    condition: &ConditionTerm,
    value: bool,
) -> Option<(Bitvector32Term, Bitvector32Term, bool)> {
    match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            Some((left.as_ref().clone(), right.as_ref().clone(), false))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true) => {
            Some((right.as_ref().clone(), left.as_ref().clone(), true))
        }
        _ => None,
    }
}

pub(crate) fn quantified_equivalent_available_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    let required = required.clone();
    if !matches!(required, Proposition::ForAll { .. }) {
        return None;
    }
    available.iter().find_map(|fact| {
        let fact = fact.clone();
        if !matches!(fact, Proposition::ForAll { .. }) {
            return None;
        }
        let forward = assumptions_from_propositions(std::slice::from_ref(&fact))
            .derive_simp_proposition(&required)
            .is_some();
        let reverse = assumptions_from_propositions(std::slice::from_ref(&required))
            .derive_simp_proposition(&fact)
            .is_some();
        (forward && reverse).then_some(fact)
    })
}

pub(crate) fn quantified_binder_equivalent(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (
            Proposition::ForAll {
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::ForAll {
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_sort == right_sort
                && substitute_int32_variable_in_proposition(
                    left_body,
                    *left_var,
                    Bitvector32Term::Variable(*right_var),
                ) == **right_body
        }
        (
            Proposition::Exists {
                name: left_name,
                var: left_var,
                sort: left_sort,
                body: left_body,
            },
            Proposition::Exists {
                name: right_name,
                var: right_var,
                sort: right_sort,
                body: right_body,
            },
        ) => {
            left_name == right_name
                && left_sort == right_sort
                && substitute_int32_variable_in_proposition(
                    left_body,
                    *left_var,
                    Bitvector32Term::Variable(*right_var),
                ) == **right_body
        }
        _ => false,
    }
}

pub(crate) fn pure_fact_is_available(required: &Proposition, available: &[Proposition]) -> bool {
    available.contains(required)
        || exactly_available_fact(required, available).is_some()
        || available
            .iter()
            .any(|fact| quantified_binder_equivalent(required, fact))
        || quantified_equivalent_available_fact(required, available).is_some()
}

pub(crate) fn atomic_conjuncts<'a>(
    proposition: &'a Proposition,
    output: &mut Vec<&'a Proposition>,
) {
    match proposition {
        Proposition::And(left, right) => {
            atomic_conjuncts(left, output);
            atomic_conjuncts(right, output);
        }
        proposition => output.push(proposition),
    }
}

/// The available fact, or conjunct of one, exactly equal to `required`.
pub(crate) fn exactly_available_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    fn matching_conjunct(fact: &Proposition, required: &Proposition) -> Option<Proposition> {
        if fact == required {
            return Some(fact.clone());
        }
        let Proposition::And(left, right) = fact else {
            return None;
        };
        matching_conjunct(left, required).or_else(|| matching_conjunct(right, required))
    }

    available
        .iter()
        .find_map(|fact| matching_conjunct(fact, required))
}

pub(crate) fn directly_matching_separation_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    let assumptions = assumptions_from_propositions(available);
    directly_matching_separation_fact_under(required, available, &assumptions)
}

/// `directly_matching_separation_fact` where the caller already holds the
/// assumption context the match should reason in (for example the available
/// facts plus recorded execution effect facts, which let the bounded resource
/// matcher see that two load terms from different snapshots denote one
/// pointer). Candidates still come only from `available`, so widening the
/// assumptions cannot make an unlisted fact available.
pub(crate) fn directly_matching_separation_fact_under(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &PureFactContext,
) -> Option<Proposition> {
    let Proposition::CResourceSeparate {
        left: required_left,
        right: required_right,
    } = required
    else {
        return None;
    };
    available.iter().find_map(|fact| {
        let Proposition::CResourceSeparate { left, right } = fact else {
            return None;
        };
        let same_orientation = c_resources_directly_match(left, required_left, assumptions)
            && c_resources_directly_match(right, required_right, assumptions);
        let reverse_orientation = c_resources_directly_match(left, required_right, assumptions)
            && c_resources_directly_match(right, required_left, assumptions);
        (same_orientation || reverse_orientation).then(|| fact.clone())
    })
}

pub(crate) fn directly_covering_loadability_fact(
    required: &Proposition,
    available: &[Proposition],
) -> Option<Proposition> {
    matches!(required, Proposition::CMemoryLoadable { .. }).then_some(())?;
    available.iter().find_map(|fact| {
        matches!(fact, Proposition::CMemoryLoadable { .. })
            .then(|| {
                assumptions_from_propositions(std::slice::from_ref(fact))
                    .derive_atomic_proposition(required)
                    .map(|_| fact.clone())
            })
            .flatten()
    })
}

pub(crate) fn proposition_has_contextual_derivation_rules(proposition: &Proposition) -> bool {
    !matches!(
        proposition,
        Proposition::CMemoryMutatesOnly { .. }
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapAllocationFreed { .. }
    )
}

pub(crate) fn exact_facts_directly_conflict(left: &Proposition, right: &Proposition) -> bool {
    let left = left.clone();
    let right = right.clone();
    normalized_exact_facts_directly_conflict(&left, &right)
}

fn normalized_exact_facts_directly_conflict(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (Proposition::And(first, second), _) => {
            normalized_exact_facts_directly_conflict(first, right)
                || normalized_exact_facts_directly_conflict(second, right)
        }
        (_, Proposition::And(first, second)) => {
            normalized_exact_facts_directly_conflict(left, first)
                || normalized_exact_facts_directly_conflict(left, second)
        }
        (
            Proposition::ConditionIs(left_condition, left_value),
            Proposition::ConditionIs(right_condition, right_value),
        ) => left_condition == right_condition && left_value != right_value,
        (Proposition::Not(body), proposition) | (proposition, Proposition::Not(body)) => {
            body.as_ref() == proposition
        }
        _ => false,
    }
}

pub(crate) fn fact_conflicts_with_assumptions(
    fact: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    match fact {
        Proposition::And(left, right) => {
            fact_conflicts_with_assumptions(left, assumptions)
                || fact_conflicts_with_assumptions(right, assumptions)
        }
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves(&Proposition::ConditionIs(condition.clone(), !value))
        }
        Proposition::Not(body) => assumptions.proves(body),
        fact => assumptions.proves(&Proposition::Not(Box::new(fact.clone()))),
    }
}

pub(crate) fn assumptions_for_direct_fact_transport(
    propositions: &[Proposition],
) -> PureFactContext {
    fn collect(proposition: &Proposition, facts: &mut Vec<Proposition>) {
        match proposition {
            Proposition::ConditionIs(_, _)
            | Proposition::CMemoryEffectSummary { .. }
            | Proposition::CHeapAllocationFreed { .. }
            | Proposition::CResourceSeparate { .. }
            // Owned ranges in one composition are pairwise separate; the
            // effect-disjointness legs of direct transport need that
            // separation when no explicit separate(...) fact writes it.
            | Proposition::CResourceComposition(_) => facts.push(proposition.clone()),
            Proposition::And(left, right) => {
                collect(left, facts);
                collect(right, facts);
            }
            _ => {}
        }
    }

    let mut facts = Vec::new();
    for proposition in propositions {
        collect(proposition, &mut facts);
    }
    assumptions_from_propositions(&facts)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::proof::facts::ProofFacts;
    use crate::kernel::proof::quantified_equivalence_index_key;
    use crate::kernel::{
        CMemory, CMemoryRange, CResource, CValue, Pointer, PointerBlock, PointerOffsetTerm,
        Variable, intern_c_memory, load_variable_for_cell_with_origin,
    };

    #[test]
    fn canonical_origin_transport_uses_bounded_snapshot_alias_check() {
        let preserved = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(0),
        };
        let written = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Constant(4),
        };
        let before = CMemory::new();
        let after = before
            .clone()
            .store(written.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
        let assumptions =
            PureFactContext::new().assume_proposition(Proposition::CMemoryMutatesOnly {
                before: before.clone(),
                after: after.clone(),
                pointers: vec![written],
            });
        // The canonical memories are the cells' epochs. Snapshots that
        // differ only by a declared block or a write to another cell share
        // an epoch, so a synthetic marker block would not separate these
        // load variables; a write to the queried cell does (the second pair).
        let left = load_variable_for_cell_with_origin(
            &intern_c_memory(before.clone()),
            &preserved,
            &intern_c_memory(before.clone()),
        );
        let right = load_variable_for_cell_with_origin(
            &intern_c_memory(after.clone()),
            &preserved,
            &intern_c_memory(after.clone()),
        );

        let unchanged = OriginsUnchanged::new(&assumptions).decide(left, right);
        assert!(
            unchanged,
            "the effect fact should transport the preserved cell"
        );

        // Also force snapshot comparison with a write to the queried cell.
        // The answer is false, and the load-variable bridge must reach it
        // through the bounded alias route.
        let loaded = preserved;
        let changed_before =
            CMemory::new().store(loaded.clone(), CValue::Int32(Bitvector32Term::Constant(1)));
        let changed_after = changed_before
            .clone()
            .store(loaded.clone(), CValue::Int32(Bitvector32Term::Constant(2)));
        let changed_left = load_variable_for_cell_with_origin(
            &intern_c_memory(changed_before.clone()),
            &loaded,
            &intern_c_memory(changed_before),
        );
        let changed_right = load_variable_for_cell_with_origin(
            &intern_c_memory(changed_after.clone()),
            &loaded,
            &intern_c_memory(changed_after),
        );
        assert_ne!(
            changed_left, changed_right,
            "a write to the cell separates its names"
        );
        let (changed_unchanged, events) = crate::instrumentation::collect(|| {
            OriginsUnchanged::new(&PureFactContext::new()).decide(changed_left, changed_right)
        });
        assert!(
            !changed_unchanged,
            "a write to the loaded cell must not be transported as unchanged"
        );
        assert!(
            events.iter().any(|event| matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "snapshot comparison: bounded alias"
            )),
            "the regression must exercise bounded snapshot comparison: {events:#?}"
        );
    }

    #[test]
    fn quantified_check_key_is_alpha_invariant_and_preserves_free_variables() {
        let quantified =
            |outer: Variable, inner: Variable, free: Variable, name: &str| Proposition::ForAll {
                var: outer,
                sort: Sort::CInt32,
                body: Box::new(Proposition::And(
                    Box::new(Proposition::ConditionIs(
                        ConditionTerm::Bitvector32Equal(
                            Box::new(Bitvector32Term::Variable(outer)),
                            Box::new(Bitvector32Term::Variable(free)),
                        ),
                        true,
                    )),
                    Box::new(Proposition::Exists {
                        name: name.to_string(),
                        var: inner,
                        sort: Sort::CInt32,
                        body: Box::new(Proposition::ConditionIs(
                            ConditionTerm::Bitvector32Equal(
                                Box::new(Bitvector32Term::Variable(inner)),
                                Box::new(Bitvector32Term::Variable(outer)),
                            ),
                            true,
                        )),
                    }),
                )),
            };

        let left = quantified(Variable(0), Variable(1), Variable(7), "left name");
        let renamed = quantified(
            Variable(10_000),
            Variable(20_000),
            Variable(7),
            "right name",
        );
        let different_free = quantified(
            Variable(10_000),
            Variable(20_000),
            Variable(8),
            "right name",
        );

        assert_eq!(
            quantified_equivalence_index_key(&left),
            quantified_equivalence_index_key(&renamed),
            "binder identities and existential display names are not semantic"
        );
        assert_ne!(
            quantified_equivalence_index_key(&left),
            quantified_equivalence_index_key(&different_free),
            "free variable identities remain part of the key"
        );
    }

    #[test]
    fn quantified_check_key_sees_through_load_variables() {
        // A universal lowered to load variables keys as the loads those
        // variables represent. A bound index inside a load variable keys by
        // binder ordinal, so renamed binders share a bucket with each other
        // and with the same universal written in load terms.
        let memory = intern_c_memory(CMemory::new().with_block("p", 12));
        let cell = |index: Variable| {
            Bitvector32Term::MemoryLoad(
                memory.clone(),
                Box::new(Pointer {
                    block: "p".into(),
                    offset: PointerOffsetTerm::Int32Scaled {
                        value: Box::new(Bitvector32Term::Variable(index)),
                        byte_width: 4,
                    },
                }),
            )
        };
        let universal = |index: Variable, term: Bitvector32Term| Proposition::ForAll {
            var: index,
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32Equal(
                    Box::new(term),
                    Box::new(Bitvector32Term::Variable(index)),
                ),
                true,
            )),
        };
        let named = |index: Variable| crate::kernel::canonical_term(&cell(index));
        assert!(matches!(
            named(Variable(3_000_000)),
            Bitvector32Term::Variable(_)
        ));
        let left = universal(Variable(3_000_000), named(Variable(3_000_000)));
        let renamed = universal(Variable(2_000_000), named(Variable(2_000_000)));
        let written = universal(Variable(3_000_001), cell(Variable(3_000_001)));
        assert_eq!(
            quantified_equivalence_index_key(&left),
            quantified_equivalence_index_key(&renamed)
        );
        assert_eq!(
            quantified_equivalence_index_key(&left),
            quantified_equivalence_index_key(&written)
        );
        assert!(quantified_binder_equivalent(&left, &renamed));
    }

    #[test]
    fn quantified_check_key_canonicalizes_range_fold_binders() {
        let universal = |index: Variable, accumulator: Variable, item: Variable| {
            let fold = Bitvector32Term::range_fold(
                Bitvector32Term::Variable(index),
                Bitvector32Term::add(
                    Bitvector32Term::Variable(index),
                    Bitvector32Term::Constant(4),
                ),
                Bitvector32Term::Constant(0),
                accumulator,
                item,
                Bitvector32Term::add(
                    Bitvector32Term::Variable(accumulator),
                    Bitvector32Term::Variable(item),
                ),
            );
            Proposition::ForAll {
                var: index,
                sort: Sort::CInt32,
                body: Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(fold, Bitvector32Term::Constant(0)),
                    true,
                )),
            }
        };

        let left = universal(Variable(30_000), Variable(30_001), Variable(30_002));
        let renamed = universal(Variable(40_000), Variable(40_001), Variable(40_002));
        assert_eq!(
            quantified_equivalence_index_key(&left),
            quantified_equivalence_index_key(&renamed),
            "range-fold binders should be alpha-equivalent in quantified fact keys"
        );

        let facts = ProofFacts::from_ordered(std::slice::from_ref(&left));
        assert_eq!(
            facts.matching_quantified_fact(&renamed),
            Some(left),
            "the alpha-equivalent range-fold fact should be found through its index"
        );
    }

    /// The perpetual-service `fold(service(owner))` near-miss: the body's
    /// separation fact is available from the unfold, but the fold state
    /// rewrites it through a memory that retains this path's store cells, so
    /// the two forms print identically yet compare structurally unequal.
    /// The bounded separation matcher must equate them from the recorded
    /// pointer-offset equality and separation facts, without the open-ended
    /// kernel search whose budget truncation used to be misreported as a
    /// missing fact.
    #[test]
    fn fold_body_separation_fact_matches_across_store_snapshots() {
        let owner_base = Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Int32Scaled {
                value: Box::new(Bitvector32Term::Variable(Variable(100_000))),
                byte_width: 4,
            },
        };
        let owner_field = |bytes: i64| Pointer {
            block: PointerBlock::ExternalArgument,
            offset: PointerOffsetTerm::Add(
                Box::new(owner_base.offset.clone()),
                Box::new(PointerOffsetTerm::Constant(bytes)),
            ),
        };
        let phase_field = owner_field(4);
        let cell_field = owner_field(8);
        let load = |memory: &CMemory, pointer: &Pointer| {
            Bitvector32Term::MemoryLoad(intern_c_memory(memory.clone()), Box::new(pointer.clone()))
        };
        let empty = CMemory::new();
        // The form recorded when the resource body was unfolded: the cell
        // pointer read through the call-havoc snapshot.
        let havoc = CMemory::new().with_block("havoc:1000000", 0);
        // The form carried by the recorded execution facts: the same
        // loads read through the branch-entry memory with its retained cells.
        let entry = empty
            .clone()
            .store(
                phase_field.clone(),
                CValue::Int32(load(&empty, &phase_field)),
            )
            .store(owner_base.clone(), CValue::Int32(load(&empty, &owner_base)));
        let cell_element_offset = |memory: &CMemory| PointerOffsetTerm::Int32Scaled {
            value: Box::new(load(memory, &cell_field)),
            byte_width: 4,
        };
        // The fold-state form reads the cell pointer through a memory
        // that still carries the `owner->cell[0] = owner->phase` store, whose
        // written address is itself written through a loaded pointer, so no
        // assumption-free normalization can drop the cell.
        let folded = havoc.clone().store(
            Pointer {
                block: PointerBlock::ExternalArgument,
                offset: cell_element_offset(&havoc),
            },
            CValue::Int32(load(&havoc, &owner_base)),
        );
        let separation = |left_start: u32, left_end: u32, cell_memory: &CMemory| {
            Proposition::CResourceSeparate {
                left: CResource::Memory(CMemoryRange::new(
                    owner_base.clone(),
                    Bitvector32Term::Constant(left_start),
                    Bitvector32Term::Constant(left_end),
                )),
                right: CResource::Memory(CMemoryRange::new(
                    Pointer {
                        block: PointerBlock::ExternalArgument,
                        offset: cell_element_offset(cell_memory),
                    },
                    Bitvector32Term::Constant(0),
                    Bitvector32Term::Constant(1),
                )),
            }
        };
        let required = separation(0, 4, &folded);
        let available = separation(0, 4, &havoc);

        // The two forms are different propositions, so plain exact matching
        // must miss even though source diagnostics render the same resource.
        assert_ne!(required, available);
        assert!(!exact_fact_is_available(
            &required,
            std::slice::from_ref(&available)
        ));

        // The recorded execution facts: the two forms of the cell pointer
        // denote one offset, and the loaded pointer's field is separate from
        // the written cell range.
        let offsets_equal = Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(
                Box::new(cell_element_offset(&havoc)),
                Box::new(cell_element_offset(&entry)),
            ),
            true,
        );
        let fields_separate = separation(2, 4, &entry);
        let assumptions =
            assumptions_from_propositions(&[offsets_equal.clone(), fields_separate.clone()]);
        assert_eq!(
            directly_matching_separation_fact_under(
                &required,
                std::slice::from_ref(&available),
                &assumptions,
            ),
            Some(available.clone()),
            "the bounded separation matcher must transport the unfold form to the fold state"
        );
    }
}

/// One side of an equality that load-variable bridging can walk.
///
/// The bridging argument is identical for pointer-offset and int32
/// equalities — only the shape of a side and of the equality differ — so one
/// implementation serves both.
trait LoadVariableBridgeSide: Clone + PartialEq + Sized {
    /// The load variable this side represents, when it represents one.
    fn load_variable(&self) -> Option<Variable>;
    /// The two sides of an equality of this shape.
    fn equality_sides(proposition: &Proposition) -> Option<(Self, Self)>;
    /// An equality of this shape over the two sides.
    fn equality(left: Self, right: Self) -> Proposition;
}

impl LoadVariableBridgeSide for PointerOffsetTerm {
    fn load_variable(&self) -> Option<Variable> {
        let PointerOffsetTerm::Int32Scaled { value, .. } = self else {
            return None;
        };
        value.as_ref().load_variable()
    }

    fn equality_sides(proposition: &Proposition) -> Option<(Self, Self)> {
        let Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) =
            proposition
        else {
            return None;
        };
        Some((left.as_ref().clone(), right.as_ref().clone()))
    }

    fn equality(left: Self, right: Self) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::PointerOffsetEqual(Box::new(left), Box::new(right)),
            true,
        )
    }
}

impl LoadVariableBridgeSide for Bitvector32Term {
    /// A side represents a load either with its load variable or with the
    /// load term itself; both forms denote one atom, so both answer here.
    fn load_variable(&self) -> Option<Variable> {
        match self {
            Bitvector32Term::Variable(variable) => {
                crate::kernel::is_load_variable(variable).then_some(*variable)
            }
            Bitvector32Term::MemoryLoad(_, _) => {
                crate::kernel::load_variable_for_term(self).map(|(variable, _)| variable)
            }
            _ => None,
        }
    }

    fn equality_sides(proposition: &Proposition) -> Option<(Self, Self)> {
        let Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(left, right), true) =
            proposition
        else {
            return None;
        };
        Some((left.as_ref().clone(), right.as_ref().clone()))
    }

    fn equality(left: Self, right: Self) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
            true,
        )
    }
}

/// Whether an equality premise follows from recorded equalities of the same
/// shape by chaining through load variables. Load variables are invisible to
/// Click source, so a premise and the recorded facts may legitimately write
/// one user-level equality through different intermediate variables. The
/// closure is bounded: only equality facts with a load-variable endpoint
/// contribute edges, and the walk visits each side at most once.
fn bridged_by_load_variable_edges<S: LoadVariableBridgeSide>(
    premise: &Proposition,
    facts: &[Proposition],
) -> bool {
    let Some((start, goal)) = S::equality_sides(premise) else {
        return false;
    };
    let edges: Vec<(S, S)> = facts
        .iter()
        .filter_map(S::equality_sides)
        .filter(|(left, right)| left.load_variable().is_some() || right.load_variable().is_some())
        .collect();
    if edges.is_empty() {
        return false;
    }
    let mut frontier = vec![start];
    let mut visited: Vec<S> = Vec::new();
    while let Some(current) = frontier.pop() {
        if current == goal {
            return true;
        }
        if visited.contains(&current) {
            continue;
        }
        visited.push(current.clone());
        for (left, right) in &edges {
            if left == &current && !visited.contains(right) {
                frontier.push(right.clone());
            } else if right == &current && !visited.contains(left) {
                frontier.push(left.clone());
            }
        }
    }
    false
}

/// Decides, and remembers, whether two load variables stand for one cell
/// that framing shows unchanged between their origin snapshots.
struct OriginsUnchanged<'a> {
    assumptions: &'a PureFactContext,
    decided: std::collections::HashMap<(Variable, Variable), bool>,
}

impl<'a> OriginsUnchanged<'a> {
    fn new(assumptions: &'a PureFactContext) -> Self {
        Self {
            assumptions,
            decided: std::collections::HashMap::new(),
        }
    }

    fn decide(&mut self, left: Variable, right: Variable) -> bool {
        let key = if left.0 <= right.0 {
            (left, right)
        } else {
            (right, left)
        };
        if let Some(decided) = self.decided.get(&key) {
            return *decided;
        }
        let decided = self.compute(key.0, key.1);
        self.decided.insert(key, decided);
        decided
    }

    fn compute(&self, left: Variable, right: Variable) -> bool {
        let (Some((left_memory, left_pointer)), Some((right_memory, right_pointer))) = (
            crate::kernel::registered_load_origin_for_variable(&left),
            crate::kernel::registered_load_origin_for_variable(&right),
        ) else {
            return false;
        };
        // The unchanged proof comes from the cheap routes — recorded
        // derivations crossed with exact-fact distinctness — never from
        // whole-snapshot alias search, which is the giant-term recursion
        // load-variable construction exists to avoid.
        left_pointer == right_pointer
            && crate::kernel::with_bounded_snapshot_comparison(|| {
                crate::kernel::c_memory_load_is_unchanged(
                    &left_memory,
                    &right_memory,
                    &left_pointer,
                    self.assumptions,
                ) || crate::kernel::c_memory_load_is_unchanged(
                    &right_memory,
                    &left_memory,
                    &left_pointer,
                    self.assumptions,
                )
            })
    }
}

/// The forms of `side` that represent the same cell as one of `endpoints`.
fn origin_renamings<S: LoadVariableBridgeSide>(
    side: &S,
    endpoints: &[S],
    origins: &mut OriginsUnchanged<'_>,
) -> Vec<S> {
    let Some(variable) = side.load_variable() else {
        return vec![side.clone()];
    };
    let mut forms = vec![side.clone()];
    for endpoint in endpoints {
        let candidate = endpoint.load_variable().expect("filtered by the caller");
        if candidate != variable && origins.decide(variable, candidate) && !forms.contains(endpoint)
        {
            forms.push(endpoint.clone());
        }
    }
    forms
}

fn bridged_with_origins<S: LoadVariableBridgeSide>(
    premise: &Proposition,
    facts: &[Proposition],
    assumptions: &PureFactContext,
) -> bool {
    let Some((start, goal)) = S::equality_sides(premise) else {
        return false;
    };
    let mut origins = OriginsUnchanged::new(assumptions);
    // Two load variables for one unchanged cell need no fact edge at all:
    // when the premise equates them directly, the origins-unchanged proof is
    // the whole content.
    if let (Some(start_variable), Some(goal_variable)) =
        (start.load_variable(), goal.load_variable())
        && origins.decide(start_variable, goal_variable)
    {
        return true;
    }
    // One implicit hop only: restate the premise's load-variable endpoints as
    // fact endpoints naming the same cell, with `OriginsUnchanged` providing
    // the contextual evidence, then ask the plain fact-edge closure.
    let endpoints: Vec<S> = facts
        .iter()
        .filter_map(S::equality_sides)
        .flat_map(|(left, right)| [left, right])
        .filter(|side| side.load_variable().is_some())
        .collect();
    let start_forms = origin_renamings(&start, &endpoints, &mut origins);
    let goal_forms = origin_renamings(&goal, &endpoints, &mut origins);
    for start_form in &start_forms {
        for goal_form in &goal_forms {
            if start_form == goal_form {
                return true;
            }
            let candidate = S::equality(start_form.clone(), goal_form.clone());
            if bridged_by_load_variable_edges::<S>(&candidate, facts) {
                return true;
            }
        }
    }
    false
}

pub(crate) fn premise_bridged_by_load_variable_chain(
    premise: &Proposition,
    facts: &[Proposition],
) -> bool {
    match premise {
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), true) => {
            bridged_by_load_variable_edges::<PointerOffsetTerm>(premise, facts)
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true) => {
            bridged_by_load_variable_edges::<Bitvector32Term>(premise, facts)
        }
        _ => false,
    }
}

/// The chain closure with origin-unchanged implicit edges. Two load variables
/// additionally connect when the loads they represent are
/// provably unchanged between their origin snapshots under the supplied
/// assumptions (call effect summaries and frame evidence). Reserved for
/// once-per-tactic consumers such as explicit transport and rewrite premise
/// checks — the unchanged proof is assumption-based and must stay off hot
/// fact paths.
pub(crate) fn premise_bridged_by_load_variable_chain_with_origins(
    premise: &Proposition,
    facts: &[Proposition],
    assumptions: &PureFactContext,
) -> bool {
    if premise_bridged_by_load_variable_chain(premise, facts) {
        return true;
    }
    match premise {
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(_, _), true) => {
            bridged_with_origins::<PointerOffsetTerm>(premise, facts, assumptions)
        }
        Proposition::ConditionIs(ConditionTerm::Bitvector32Equal(_, _), true) => {
            bridged_with_origins::<Bitvector32Term>(premise, facts, assumptions)
        }
        _ => false,
    }
}

/// The separation branch of bridged availability. Keep its range and
/// proposition temporaries out of the shared fact-dispatch frame; the
/// expansion small-stack regression pins that boundary.
#[inline(never)]
fn separation_bridged_available(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &PureFactContext,
    framing: &[ExecutionPureFact],
) -> bool {
    let assumptions = framing
        .iter()
        .fold(assumptions.clone(), |assumptions, fact| {
            assumptions.assume_proposition(fact.proposition().clone())
        });
    available.iter().any(|candidate| {
        matches!(candidate, Proposition::CResourceSeparate { .. })
            && propositions_equal_modulo_proven_snapshots(candidate, required, &assumptions)
    })
}

/// Whether two separations denote the same fact after canonicalization and
/// proven snapshot comparison: each range's base offset and extent terms
/// compare with load variables resolved shallowly and load atoms bridged
/// across proven snapshots — the relation the condition arm uses, applied
/// to the terms a separation is made of. Separation is symmetric, so both pairings are
/// tried. Keep its range temporaries local rather than charging every caller;
/// the expansion small-stack regression pins that boundary.
#[inline(never)]
fn separations_equal_modulo_proven_snapshots(
    left: &Proposition,
    right: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    let (
        Proposition::CResourceSeparate {
            left: CResource::Memory(left_a),
            right: CResource::Memory(left_b),
        },
        Proposition::CResourceSeparate {
            left: CResource::Memory(right_a),
            right: CResource::Memory(right_b),
        },
    ) = (left, right)
    else {
        return false;
    };
    let ranges_equal = |left: &CMemoryRange, right: &CMemoryRange| {
        left.base().block == right.base().block
            && assumptions.conditions_equal_modulo_proven_snapshots(
                &ConditionTerm::PointerOffsetEqual(
                    Box::new(expand_offset_load_variables_shallow(&left.base().offset)),
                    Box::new(PointerOffsetTerm::Constant(0)),
                ),
                &ConditionTerm::PointerOffsetEqual(
                    Box::new(expand_offset_load_variables_shallow(&right.base().offset)),
                    Box::new(PointerOffsetTerm::Constant(0)),
                ),
            )
            && assumptions.conditions_equal_modulo_proven_snapshots(
                &ConditionTerm::Bitvector32Equal(
                    Box::new(expand_load_variables_shallow(left.start())),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
                &ConditionTerm::Bitvector32Equal(
                    Box::new(expand_load_variables_shallow(right.start())),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
            )
            && assumptions.conditions_equal_modulo_proven_snapshots(
                &ConditionTerm::Bitvector32Equal(
                    Box::new(expand_load_variables_shallow(left.end())),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
                &ConditionTerm::Bitvector32Equal(
                    Box::new(expand_load_variables_shallow(right.end())),
                    Box::new(Bitvector32Term::Constant(0)),
                ),
            )
    };
    ranges_equal(left_a, right_a) && ranges_equal(left_b, right_b)
        || ranges_equal(left_a, right_b) && ranges_equal(left_b, right_a)
}
