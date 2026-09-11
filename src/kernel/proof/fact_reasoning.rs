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
        | Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. }
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
        Bitvector32Term::BitwiseXor(left, right) => {
            // Unsigned comparisons are represented by signed comparisons
            // after flipping the sign bit. On either side of zero this is
            // an exact translation; an interval crossing zero wraps and
            // must conservatively retain the entire signed range.
            let operand = if right.as_const() == Some(0x8000_0000) {
                left
            } else if left.as_const() == Some(0x8000_0000) {
                right
            } else {
                return None;
            };
            let (lower, upper) = signed_term_interval(operand, bounds, depth - 1)?;
            if lower >= 0 {
                Some((lower + SIGNED_MIN, upper + SIGNED_MIN))
            } else if upper < 0 {
                Some((lower - SIGNED_MIN, upper - SIGNED_MIN))
            } else {
                Some((SIGNED_MIN, SIGNED_MAX))
            }
        }
        Bitvector32Term::Divide(_, _)
        | Bitvector32Term::UnsignedDivide(_, _)
        | Bitvector32Term::UnsignedRemainder(_, _)
        | Bitvector32Term::BitwiseOr(_, _)
        | Bitvector32Term::BitwiseNot(_)
        | Bitvector32Term::If { .. }
        | Bitvector32Term::RangeFold { .. }
        | Bitvector32Term::Int64Constant(_)
        | Bitvector32Term::UInt64Constant(_)
        | Bitvector32Term::Int64From32(_)
        | Bitvector32Term::UInt64From32(_)
        | Bitvector32Term::UInt32From64(_)
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
        | Bitvector32Term::IntegerToMachine { .. } => None,
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
            } else {
                let value = right.as_const()?;
                let value = i64::from(value as i32);
                collect_signed_affine_terms(
                    left,
                    coefficient.checked_mul(value)?,
                    terms,
                    constant,
                )?;
            }
        }
        Bitvector32Term::Variable(_)
        | Bitvector32Term::MemoryLoad(_, _)
        | Bitvector32Term::PointerAddress(_)
        | Bitvector32Term::PureFunctionApplication { .. }
        | Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. } => {
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
        | Bitvector32Term::UInt32From64(_)
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
        | Bitvector32Term::Float64Binary { .. }
        | Bitvector32Term::IntegerToMachine { .. } => return None,
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
        | Bitvector32Term::PureFunctionApplication { .. }
        | Bitvector32Term::ClickFunctionApplication { .. }
        | Bitvector32Term::AlgebraicMatch { .. } => true,
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
        | Bitvector32Term::UInt32From64(_)
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
        | Bitvector32Term::Float64Binary { .. }
        | Bitvector32Term::IntegerToMachine { .. } => false,
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
fn affine_equality_follows_from_bounds(
    form: &SignedAffineForm,
    inequalities: &[SignedAffineInequality],
) -> Option<bool> {
    let forward = SignedAffineInequality {
        terms: form.terms.clone(),
        bound: form.constant.checked_neg()?,
    };
    let reverse = SignedAffineInequality {
        terms: form
            .terms
            .iter()
            .map(|(term, coefficient)| Some((term.clone(), coefficient.checked_neg()?)))
            .collect::<Option<_>>()?,
        bound: form.constant,
    };
    Some(
        inequalities
            .iter()
            .any(|premise| inequality_implies(premise, &forward))
            && inequalities
                .iter()
                .any(|premise| inequality_implies(premise, &reverse)),
    )
}

pub(crate) fn check_signed_affine_arithmetic(
    goal: &Proposition,
    premises: &[Proposition],
) -> Result<(), ArithmeticCheckError> {
    if check_pointer_translation_arithmetic(goal, premises) {
        return Ok(());
    }
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
                    || affine_equality_follows_from_bounds(&form, &inequalities) == Some(true)
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
                if (goal.terms.is_empty() && 0 <= goal.bound)
                    || inequalities
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
    fn arithmetic_equality_requires_both_matching_bounds() {
        let goal = proposition(ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(0)),
            Bitvector32Term::Variable(Variable(1)),
        ));
        assert!(
            check_signed_affine_arithmetic(&goal, &[less_equal(0, 1), less_equal(1, 0)]).is_ok()
        );
        for premises in [
            vec![],
            vec![less_equal(0, 1)],
            vec![less_equal(1, 0)],
            vec![less_equal(0, 1), less_equal(2, 0)],
        ] {
            assert!(check_signed_affine_arithmetic(&goal, &premises).is_err());
        }
        let x = Bitvector32Term::Variable(Variable(0));
        let zero = Bitvector32Term::Constant(0);
        let one = Bitvector32Term::Constant(1);
        let zero_goal = proposition(ConditionTerm::equal(x.clone(), zero.clone()));
        assert!(
            check_signed_affine_arithmetic(
                &zero_goal,
                &[
                    proposition(ConditionTerm::signed_less_equal(zero, x.clone())),
                    proposition(ConditionTerm::signed_less_equal(x, one)),
                ]
            )
            .is_err()
        );
    }

    #[test]
    fn arithmetic_equality_bounds_scale_with_explicit_premises() {
        let goal = proposition(ConditionTerm::equal(
            Bitvector32Term::Variable(Variable(0)),
            Bitvector32Term::Variable(Variable(1)),
        ));
        let mut previous = None;
        for size in [16, 32, 64, 128] {
            let mut premises = (2..size)
                .map(|index| less_equal(index, index + 1))
                .collect::<Vec<_>>();
            premises.extend([less_equal(0, 1), less_equal(1, 0)]);
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                check_signed_affine_arithmetic(&goal, &premises)
            });
            result.unwrap();
            assert!(work > 0);
            if let Some(previous) = previous {
                assert!(work <= previous * 3);
            }
            previous = Some(work);
        }
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

    #[test]
    fn sign_bit_interval_translation_checks_boundaries_and_rejects_missing_bounds() {
        let x = Bitvector32Term::Variable(Variable(94_006));
        for (lower, upper) in [
            (i32::MIN, -1),
            (-1, -1),
            (0, 0),
            (0, 1_073_741_823),
            (0, i32::MAX),
            (-1, 0),
            (i32::MIN, i32::MAX),
        ] {
            let bounds = BTreeMap::from([(x.clone(), (i64::from(lower), i64::from(upper)))]);
            for term in [
                Bitvector32Term::BitwiseXor(
                    Box::new(x.clone()),
                    Box::new(Bitvector32Term::Constant(0x8000_0000)),
                ),
                Bitvector32Term::BitwiseXor(
                    Box::new(Bitvector32Term::Constant(0x8000_0000)),
                    Box::new(x.clone()),
                ),
            ] {
                let (actual_lower, actual_upper) =
                    signed_term_interval(&term, &bounds, ARITHMETIC_INTERVAL_DEPTH).unwrap();
                for value in [
                    lower,
                    upper,
                    lower + ((i64::from(upper) - i64::from(lower)) / 2) as i32,
                ] {
                    let transformed = i64::from(((value as u32) ^ 0x8000_0000) as i32);
                    assert!(actual_lower <= transformed && transformed <= actual_upper);
                }
                if lower < 0 && upper >= 0 {
                    assert_eq!((actual_lower, actual_upper), (SIGNED_MIN, SIGNED_MAX));
                }
            }
        }
        let upper = proposition(ConditionTerm::signed_less_equal(
            x.clone(),
            Bitvector32Term::Constant(1_073_741_823),
        ));
        let goal = proposition(ConditionTerm::unsigned_less_equal(
            x.clone(),
            Bitvector32Term::Constant(1_073_741_823),
        ));
        check_signed_affine_arithmetic(&goal, &[nonnegative(x.clone()), upper.clone()]).unwrap();
        assert!(check_signed_affine_arithmetic(&goal, &[upper]).is_err());
        assert!(check_signed_affine_arithmetic(&goal, &[nonnegative(x)]).is_err());
    }
}

pub(crate) fn normalizes_context_free(goal: &Proposition) -> bool {
    if let Proposition::ConditionIs(condition, value) = goal {
        match condition {
            ConditionTerm::IntegerEqual(left, right) if left == right => return *value,
            ConditionTerm::IntegerNotEqual(left, right) if left == right => return !*value,
            ConditionTerm::IntegerEqual(left, right)
                if super::fact_keys::integer_terms_alpha_equivalent(left, right) == Some(true) =>
            {
                return *value;
            }
            ConditionTerm::IntegerNotEqual(left, right)
                if super::fact_keys::integer_terms_alpha_equivalent(left, right) == Some(true) =>
            {
                return !*value;
            }
            _ => {}
        }
    }
    if crate::kernel::reasoning::path_facts::solve_builtin_prop(goal) {
        return true;
    }
    // Constructor congruence is definitional reduction over the goal's own
    // structure: two applications of one constructor are equal when their
    // corresponding fields are. The walk is bounded by the goal.
    if let Some(fields) = crate::kernel::assumptions::algebraic_constructor_field_equalities(goal)
        && !fields.is_empty()
    {
        return fields.iter().all(normalizes_context_free);
    }
    // No premises, so what remains is the atomic theory on the empty
    // context. The ambient legs of the relocated planner -- fact lookup,
    // case splits over disjunction facts, universal instantiation,
    // singleton substitution, the inconsistency fallback -- are vacuous
    // here by construction.
    PureFactContext::new().proves_atomic_for_derivation(goal, false)
}

/// Transitional leaf check for structural-normalization migration:
/// top-level conjunction, disjunction, and implication construction must be
/// explicit, while the remaining logical constructors continue through the
/// compatibility path below.
pub(crate) fn normalizes_context_free_leaf(goal: &Proposition) -> bool {
    if matches!(
        goal,
        Proposition::And(_, _)
            | Proposition::Or(_, _)
            | Proposition::Implies(_, _)
            | Proposition::ForAll { .. }
            | Proposition::Exists { .. }
    ) {
        return false;
    }
    normalizes_context_free(goal)
}

/// Whether one enumerated instance of a finite universal is discharged
/// without a proof search.
///
/// `enumerate` names its instances, so checking them is structural: a
/// conjunction splits, an instance guard that folds to true is consumed, and
/// every leaf must be an exactly available fact or close through the
/// normalization leaf. A leaf that is itself a quantifier is a further proof
/// step, not something this enumeration discharges.
pub(crate) fn enumerated_instance_is_discharged(
    instance: &Proposition,
    facts: &super::ProofFacts,
) -> bool {
    if facts.contains(instance) {
        return true;
    }
    match instance {
        Proposition::And(left, right) => {
            enumerated_instance_is_discharged(left, facts)
                && enumerated_instance_is_discharged(right, facts)
        }
        Proposition::Implies(guard, conclusion) => {
            // A guard this instantiation folds to false makes the instance
            // vacuous; one that folds to true leaves the conclusion.
            instance_guard_folds_to_false(guard)
                || instance_guard_folds_to_true(guard)
                    && enumerated_instance_is_discharged(conclusion, facts)
        }
        _ => normalizes_context_free_leaf(instance),
    }
}

/// Whether an instance guard folds to true with no ambient fact and no
/// logical search: conjunction splits structurally and each conjunct closes
/// through the normalization leaf.
fn instance_guard_folds_to_true(guard: &Proposition) -> bool {
    match guard {
        Proposition::And(left, right) => {
            instance_guard_folds_to_true(left) && instance_guard_folds_to_true(right)
        }
        _ => normalizes_context_free_leaf(guard),
    }
}

/// Whether an instance guard folds to false the same way: one false conjunct
/// refutes a conjunction, and a disjunction needs both sides refuted. Each
/// leaf is refuted through the normalization leaf on its negation.
fn instance_guard_folds_to_false(guard: &Proposition) -> bool {
    match guard {
        Proposition::And(left, right) => {
            instance_guard_folds_to_false(left) || instance_guard_folds_to_false(right)
        }
        Proposition::Or(left, right) => {
            instance_guard_folds_to_false(left) && instance_guard_folds_to_false(right)
        }
        _ => normalizes_context_free_leaf(&Proposition::Not(Box::new(guard.clone()))),
    }
}

pub(crate) fn is_single_normalization_condition(proposition: &Proposition) -> bool {
    crate::kernel::spec::proposition_as_single_condition(proposition).is_some()
}

/// Reduce only checked, explicitly cited conditions; never search ambient facts.
pub(crate) fn normalize_using_conditions(
    goal: &Proposition,
    premises: &[Proposition],
    facts: &super::ProofFacts,
) -> Result<(), ConditionalNormalizationError> {
    let mut conditions = std::collections::HashMap::new();
    // Integer equality is symmetric.  Keep the exact reverse spelling in
    // this selected-condition map so `normalize using` can close a goal
    // whose operands were lowered in the opposite order.  This is deliberately
    // built from the cited premises only; it never searches ambient facts.
    let mut integer_alpha_conditions: std::collections::HashMap<
        u64,
        Vec<(super::fact_keys::IntegerEqualityAlphaKey, bool)>,
    > = std::collections::HashMap::new();
    for (index, premise) in premises.iter().enumerate() {
        if !facts.contains(premise)
            && !condition_polarity_forms(premise)
                .iter()
                .any(|form| facts.contains(form))
        {
            return Err(ConditionalNormalizationError::UnavailablePremise(index));
        }
        let (condition, value) = crate::kernel::spec::proposition_as_single_condition(premise)
            .ok_or(ConditionalNormalizationError::UnsupportedPremise(index))?;
        if let Some(previous) = conditions.insert(condition.clone(), value)
            && previous != value
        {
            return Err(ConditionalNormalizationError::UnsupportedPremise(index));
        }
        let reverse = match &condition {
            ConditionTerm::IntegerEqual(left, right) => {
                Some(ConditionTerm::IntegerEqual(right.clone(), left.clone()))
            }
            ConditionTerm::IntegerNotEqual(left, right) => {
                Some(ConditionTerm::IntegerNotEqual(right.clone(), left.clone()))
            }
            _ => None,
        };
        if let Some(reverse) = reverse
            && let Some(previous) = conditions.insert(reverse, value)
            && previous != value
        {
            return Err(ConditionalNormalizationError::UnsupportedPremise(index));
        }
        // Exact condition lookup above handles ordinary scalar terms.  Fold
        // binders can be freshly allocated while lowering the cited premise
        // and the goal, so retain a checked snapshot-aware alpha index for
        // the same two orientations.  The fingerprint is charged before it
        // becomes a map key; collision candidates are checked with the
        // bounded key comparator below.
        if value && let ConditionTerm::IntegerEqual(left, right) = &condition {
            for condition in [
                ConditionTerm::IntegerEqual(left.clone(), right.clone()),
                ConditionTerm::IntegerEqual(right.clone(), left.clone()),
            ] {
                let proposition = Proposition::ConditionIs(condition, true);
                let Some(key) = super::fact_keys::integer_equality_alpha_key(&proposition) else {
                    continue;
                };
                let Some(fingerprint) = key.checked_fingerprint() else {
                    continue;
                };
                integer_alpha_conditions
                    .entry(fingerprint)
                    .or_default()
                    .push((key, value));
            }
        }
    }
    // A single reverse-key lookup is enough for the common case.  If the
    // separately lowered fold has fresh binder IDs, use the checked alpha
    // bucket instead of scanning all cited conditions.  Only a top-level
    // atomic goal is admitted here; compound goals still follow the ordinary
    // explicit structural normalizer below.
    if let Some((condition, goal_value)) =
        crate::kernel::spec::proposition_as_single_condition(goal)
        && goal_value
        && let ConditionTerm::IntegerEqual(_, _) = &condition
        && !conditions.contains_key(&condition)
    {
        let proposition = Proposition::ConditionIs(condition.clone(), true);
        if let Some(key) = super::fact_keys::integer_equality_alpha_key(&proposition)
            && let Some(fingerprint) = key.checked_fingerprint()
            && let Some(candidates) = integer_alpha_conditions.get(&fingerprint)
        {
            for (candidate, value) in candidates {
                match candidate.checked_eq(&key) {
                    Some(true) => {
                        conditions.insert(condition.clone(), *value);
                        break;
                    }
                    Some(false) => {}
                    None => break,
                }
            }
        }
    }
    let reduced = super::term_rewrite::TermRewrite::for_conditions(&conditions).proposition(goal);
    normalizes_context_free_leaf(&reduced)
        .then_some(())
        .ok_or(ConditionalNormalizationError::DoesNotNormalize)
}

#[derive(Debug)]
pub(crate) enum ConditionalNormalizationError {
    UnavailablePremise(usize),
    UnsupportedPremise(usize),
    DoesNotNormalize,
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
            || premise_assumptions.proves_atomic_for_derivation(conjunct, false)
            || premise_assumptions.proves_atomic_for_derivation(conjunct, true)
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

/// Translate one explicitly named pointer equality by the same exact byte
/// displacement. No equality graph or ambient fact context is consulted.
/// Scaled signed sums may be distributed only with explicit overflow bounds.
pub(crate) fn check_pointer_translation_arithmetic(
    goal: &Proposition,
    premises: &[Proposition],
) -> bool {
    fn sides(
        proposition: &Proposition,
    ) -> Option<(
        &PointerOffsetTerm,
        &PointerOffsetTerm,
        Option<(&PointerBlock, &PointerBlock)>,
    )> {
        match proposition {
            Proposition::ConditionIs(ConditionTerm::PointerEqual(a, b), true) => {
                Some((&a.offset, &b.offset, Some((&a.block, &b.block))))
            }
            Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(a, b), true) => {
                Some((a, b, None))
            }
            _ => None,
        }
    }
    let Some((left, right, blocks)) = sides(goal) else {
        return false;
    };
    let mut relation = None;
    let mut inequalities = Vec::new();
    for premise in premises {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(parts) = sides(premise) {
            if relation.replace(parts).is_some() {
                return false;
            }
        } else {
            let Proposition::ConditionIs(condition, _) = premise else {
                return false;
            };
            let (x, y) = match condition {
                ConditionTerm::Bitvector32SignedLessThan(x, y)
                | ConditionTerm::Bitvector32SignedLessEqual(x, y)
                | ConditionTerm::Bitvector32SignedGreaterThan(x, y)
                | ConditionTerm::Bitvector32SignedGreaterEqual(x, y) => (x, y),
                _ => return false,
            };
            if ![x, y].iter().all(|term| {
                matches!(
                    term.as_ref(),
                    Bitvector32Term::Variable(_) | Bitvector32Term::Constant(_)
                )
            }) {
                return false;
            }
            let Some(SignedAffineClaim::Inequality(bound)) = signed_affine_claim(premise) else {
                return false;
            };
            inequalities.push(bound);
        }
    }
    let Some((a, b, premise_blocks)) = relation else {
        return false;
    };
    let (a, b) = match (blocks, premise_blocks) {
        (None, None) => (a, b),
        (Some((l, r)), Some((x, y))) if l == x && r == y => (a, b),
        (Some((l, r)), Some((x, y))) if l == y && r == x => (b, a),
        _ => return false,
    };
    let mut bounds = signed_affine_atom_bounds(&inequalities);
    // x < y, where both are int32 atoms, also supplies x < INT_MAX.
    // This is a direct interval consequence, not a transitive bound search.
    for premise in premises {
        let (x, y) = match premise {
            Proposition::ConditionIs(ConditionTerm::Bitvector32SignedLessThan(x, y), true)
            | Proposition::ConditionIs(ConditionTerm::Bitvector32SignedGreaterThan(y, x), true) => {
                (x, y)
            }
            _ => continue,
        };
        if matches!(x.as_ref(), Bitvector32Term::Variable(_))
            && matches!(
                y.as_ref(),
                Bitvector32Term::Variable(_) | Bitvector32Term::Constant(_)
            )
        {
            let upper = match y.as_ref() {
                Bitvector32Term::Constant(value) => i64::from(*value as i32),
                _ => i64::from(i32::MAX),
            };
            let entry = bounds
                .entry(x.as_ref().clone())
                .or_insert((i64::from(i32::MIN), i64::from(i32::MAX)));
            entry.1 = entry.1.min(upper - 1);
        }
    }
    // Only split a sum of two scalar atoms here. Larger expressions stay
    // opaque; checking an enclosing sum must not repeatedly traverse every
    // nested prefix to rediscover its bounds.
    let atom_range = |value: &Bitvector32Term| match value {
        Bitvector32Term::Constant(value) => {
            Some((i64::from(*value as i32), i64::from(*value as i32)))
        }
        Bitvector32Term::Variable(_) => Some(
            bounds
                .get(value)
                .copied()
                .unwrap_or((i64::from(i32::MIN), i64::from(i32::MAX))),
        ),
        _ => None,
    };
    let sum_is_defined = |x: &Bitvector32Term, y: &Bitvector32Term| {
        let (Some((xmin, xmax)), Some((ymin, ymax))) = (atom_range(x), atom_range(y)) else {
            return false;
        };
        xmin + ymin >= i64::from(i32::MIN) && xmax + ymax <= i64::from(i32::MAX)
    };
    enum Part<'a> {
        Offset(&'a PointerOffsetTerm),
        Scaled(&'a Bitvector32Term, i64),
    }
    let mut terms = BTreeMap::<PointerOffsetTerm, i128>::new();
    let mut constant = 0i128;
    for (offset, sign) in [(left, 1i128), (a, -1), (right, -1), (b, 1)] {
        let mut pending = vec![Part::Offset(offset)];
        while let Some(part) = pending.pop() {
            crate::instrumentation::record_deterministic_work(1);
            let atom = match part {
                Part::Offset(PointerOffsetTerm::Constant(value)) => {
                    let Some(next) = constant.checked_add(sign * i128::from(*value)) else {
                        return false;
                    };
                    constant = next;
                    continue;
                }
                Part::Offset(PointerOffsetTerm::Add(x, y)) => {
                    pending.push(Part::Offset(x));
                    pending.push(Part::Offset(y));
                    continue;
                }
                Part::Offset(PointerOffsetTerm::Int32Scaled { value, byte_width }) => {
                    pending.push(Part::Scaled(value, *byte_width));
                    continue;
                }
                Part::Scaled(Bitvector32Term::Constant(value), width) => {
                    let value = i128::from(*value as i32) * i128::from(width);
                    let Some(next) = constant.checked_add(sign * value) else {
                        return false;
                    };
                    constant = next;
                    continue;
                }
                Part::Scaled(Bitvector32Term::Add(x, y), width) if sum_is_defined(x, y) => {
                    pending.push(Part::Scaled(x, width));
                    pending.push(Part::Scaled(y, width));
                    continue;
                }
                Part::Scaled(value, width) => PointerOffsetTerm::Int32Scaled {
                    value: Box::new(value.clone()),
                    byte_width: width,
                },
                Part::Offset(value) => value.clone(),
            };
            let entry = terms.entry(atom).or_default();
            let Some(next) = entry.checked_add(sign) else {
                return false;
            };
            *entry = next;
        }
    }
    constant == 0 && terms.values().all(|coefficient| *coefficient == 0)
}

#[cfg(test)]
mod pointer_translation_tests {
    use super::*;

    fn add(a: PointerOffsetTerm, b: PointerOffsetTerm) -> PointerOffsetTerm {
        PointerOffsetTerm::Add(Box::new(a), Box::new(b))
    }
    fn scaled(value: Bitvector32Term) -> PointerOffsetTerm {
        PointerOffsetTerm::Int32Scaled {
            value: Box::new(value),
            byte_width: 4,
        }
    }
    fn eq(a: PointerOffsetTerm, b: PointerOffsetTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::PointerEqual(
                Box::new(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: a,
                }),
                Box::new(Pointer {
                    block: PointerBlock::ExternalArgument,
                    offset: b,
                }),
            ),
            true,
        )
    }
    fn example() -> (Proposition, Vec<Proposition>) {
        let p = PointerOffsetTerm::Variable(Variable(100));
        let arr = PointerOffsetTerm::Variable(Variable(101));
        let i = Bitvector32Term::Variable(Variable(1));
        let n = Bitvector32Term::Variable(Variable(2));
        let relation = eq(p.clone(), add(arr.clone(), scaled(i.clone())));
        let bound = Proposition::ConditionIs(ConditionTerm::signed_less_than(i.clone(), n), true);
        let goal = eq(
            add(p, PointerOffsetTerm::Constant(4)),
            add(
                arr,
                scaled(Bitvector32Term::Add(
                    Box::new(i),
                    Box::new(Bitvector32Term::Constant(1)),
                )),
            ),
        );
        (goal, vec![relation, bound])
    }

    #[test]
    fn pointer_translation_requires_relation_bounds_and_matching_displacement() {
        let (goal, premises) = example();
        assert!(check_pointer_translation_arithmetic(&goal, &premises));
        assert!(!check_pointer_translation_arithmetic(&goal, &premises[..1]));
        assert!(!check_pointer_translation_arithmetic(&goal, &premises[1..]));
        let Proposition::ConditionIs(ConditionTerm::PointerEqual(a, b), true) = goal else {
            unreachable!()
        };
        let mut wrong_advance = a.clone();
        wrong_advance.offset = add(wrong_advance.offset, PointerOffsetTerm::Constant(4));
        assert!(!check_pointer_translation_arithmetic(
            &Proposition::ConditionIs(ConditionTerm::PointerEqual(wrong_advance, b.clone()), true),
            &premises
        ));
        let mut wrong_block = a.clone();
        wrong_block.block = PointerBlock::Symbolic(Variable(99));
        assert!(!check_pointer_translation_arithmetic(
            &Proposition::ConditionIs(ConditionTerm::PointerEqual(wrong_block, b.clone()), true),
            &premises
        ));
        assert!(!check_pointer_translation_arithmetic(
            &Proposition::ConditionIs(ConditionTerm::PointerEqual(a, b), false),
            &premises
        ));
    }

    #[test]
    fn pointer_translation_does_not_distribute_wrapped_signed_sum() {
        let p = PointerOffsetTerm::Variable(Variable(1));
        let q = PointerOffsetTerm::Variable(Variable(2));
        let premises = [eq(p.clone(), q.clone())];
        let goal = eq(
            add(
                add(p, scaled(Bitvector32Term::Constant(i32::MAX as u32))),
                PointerOffsetTerm::Constant(4),
            ),
            add(
                q,
                scaled(Bitvector32Term::Add(
                    Box::new(Bitvector32Term::Constant(i32::MAX as u32)),
                    Box::new(Bitvector32Term::Constant(1)),
                )),
            ),
        );
        assert!(!check_pointer_translation_arithmetic(&goal, &premises));
    }

    #[test]
    fn pointer_translation_checking_scales_with_explicit_input() {
        let mut previous = None;
        for size in [16, 32, 64, 128] {
            let (mut goal, mut premises) = example();
            let Proposition::ConditionIs(ConditionTerm::PointerEqual(a, b), true) = &mut goal
            else {
                unreachable!()
            };
            for index in 0..size {
                let delta = PointerOffsetTerm::Variable(Variable(1000 + index));
                a.offset = add(a.offset.clone(), delta.clone());
                b.offset = add(b.offset.clone(), delta);
                premises.push(Proposition::ConditionIs(
                    ConditionTerm::signed_less_than(
                        Bitvector32Term::Variable(Variable(2000 + index)),
                        Bitvector32Term::Constant(100),
                    ),
                    true,
                ));
            }
            let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
                check_pointer_translation_arithmetic(&goal, &premises)
            });
            assert!(valid);
            assert!(work > size as usize);
            if let Some(previous) = previous {
                assert!(work <= previous * 3);
            }
            previous = Some(work);
        }
    }
}

/// `arithmetic using (aligned(base, m))` closes `aligned(base + k, n)` (or
/// its negation) exactly as the atomic prover decides it: from the one listed
/// base fact, or from nothing for a heap base.
pub(crate) fn check_pointer_alignment_arithmetic(
    goal: &Proposition,
    premises: &[Proposition],
) -> bool {
    let Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(left, right), value) = goal else {
        return false;
    };
    let mut used = crate::kernel::eval::pointer_tags::UsedFacts::new();
    assumptions_from_propositions(premises)
        .decide_pointer_word_equality_citing(left, right, &mut used)
        == Some(*value)
}

/// Checks the small float proof used by `simp using`: an IEEE
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
    let Some((condition, value)) =
        crate::kernel::spec::proposition_as_single_condition(proposition)
    else {
        return Vec::new();
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
        if let ConditionTerm::AlgebraicEqual(left, right) = &condition {
            let equality = Proposition::Equal(
                Term::Algebraic(*left.clone()),
                Term::Algebraic(*right.clone()),
            );
            forms.push(if value {
                equality
            } else {
                Proposition::Not(Box::new(equality))
            });
        }
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
pub(crate) fn propositions_equal_modulo_proven_snapshots(
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
/// facts use [`condition_bridged_fact_is_available`] for the same purpose.
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
    let flatten = crate::kernel::spec::proposition_as_single_condition;
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
    if !matches!(required, Proposition::ForAll { .. }) {
        return None;
    }
    available
        .iter()
        .find(|fact| quantified_binder_equivalent(required, fact))
        .cloned()
}

pub(crate) fn quantified_binder_equivalent(left: &Proposition, right: &Proposition) -> bool {
    // A loadability premise carries an exact memory snapshot. Compare the
    // selected typed alpha keys before falling back to int32 substitution;
    // the latter would clone and rewrite the entire opaque memory snapshot.
    if let Some(equivalent) = super::fact_keys::snapshot_quantified_alpha_equivalent(left, right) {
        return equivalent;
    }
    // A supported structural mismatch is definitive; do not substitute or
    // search to turn it into an equivalence. Loads and unsupported fragments
    // retain the existing one-binder, memory-aware structural check below.
    if let (Some(left), Some(right)) = (
        super::fact_keys::memory_free_quantified_key(left),
        super::fact_keys::memory_free_quantified_key(right),
    ) {
        return left == right;
    }
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
                    .proves_atomic_for_derivation(required, false)
                    .then(|| fact.clone())
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

/// Whether `fact` is refuted by the assumptions, by the retained exact
/// routes only.
///
/// The walk is structural over `fact`: a conjunction conflicts when one
/// conjunct does, and each leaf's negation must be exactly available, decided
/// by the frozen condition checker on a bare condition, or settled by a
/// retained atomic memory/resource checker. There is no logical search, so a
/// contradiction that needs a derivation is reported as "no conflict" and the
/// fact stays; the consumers all treat this as a suppression or vacuity hint.
pub(crate) fn fact_conflicts_with_assumptions(
    fact: &Proposition,
    assumptions: &PureFactContext,
) -> bool {
    let refuted = |goal: Proposition| {
        crate::kernel::prelude::required_obligation_is_exactly_discharged(assumptions, &goal)
    };
    match fact {
        Proposition::And(left, right) => {
            fact_conflicts_with_assumptions(left, assumptions)
                || fact_conflicts_with_assumptions(right, assumptions)
        }
        Proposition::ConditionIs(condition, value) => {
            refuted(Proposition::ConditionIs(condition.clone(), !value))
        }
        Proposition::Not(body) => refuted(body.as_ref().clone()),
        fact => refuted(Proposition::Not(Box::new(fact.clone()))),
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
    fn quantified_structural_matching_preserves_scope_and_rejects_logic() {
        let eq = |a, b| {
            Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(a)),
                    Bitvector32Term::Variable(Variable(b)),
                ),
                true,
            )
        };
        let forall = |v, body| Proposition::ForAll {
            var: Variable(v),
            sort: Sort::CInt32,
            body: Box::new(body),
        };
        let nested = forall(1, forall(2, eq(1, 2)));
        assert!(quantified_binder_equivalent(
            &nested,
            &forall(3, forall(4, eq(3, 4)))
        ));
        assert!(!quantified_binder_equivalent(
            &nested,
            &forall(3, forall(3, eq(3, 3)))
        ));
        assert!(!quantified_binder_equivalent(
            &forall(1, eq(1, 3)),
            &forall(3, eq(3, 3))
        ));
        assert!(!quantified_binder_equivalent(
            &forall(1, eq(1, 7)),
            &forall(2, eq(2, 8))
        ));
        // A shadowing binder must not change the binding of its sibling.
        let left = forall(
            1,
            Proposition::And(Box::new(forall(1, eq(1, 1))), Box::new(eq(1, 7))),
        );
        let right = forall(
            2,
            Proposition::And(Box::new(forall(3, eq(3, 3))), Box::new(eq(2, 7))),
        );
        assert!(quantified_binder_equivalent(&left, &right));
        let exists = Proposition::Exists {
            name: "witness".into(),
            var: Variable(2),
            sort: Sort::CInt32,
            body: Box::new(eq(2, 2)),
        };
        assert!(!quantified_binder_equivalent(&forall(1, eq(1, 1)), &exists));
        let reflexive = forall(1, eq(1, 1));
        let wrong_sort = Proposition::ForAll {
            var: Variable(1),
            sort: Sort::CInt64,
            body: Box::new(eq(1, 1)),
        };
        assert!(!quantified_binder_equivalent(&reflexive, &wrong_sort));
        let tautology = forall(
            2,
            Proposition::ConditionIs(ConditionTerm::Constant(true), true),
        );
        assert!(
            quantified_equivalent_available_fact(&tautology, &[reflexive]).is_none(),
            "logical equivalence is not binder renaming"
        );
    }

    #[test]
    fn quantified_single_match_does_not_check_the_whole_alpha_bucket() {
        let quantified = |name: String| Proposition::ForAll {
            var: Variable(1),
            sort: Sort::CInt32,
            body: Box::new(Proposition::Exists {
                name,
                var: Variable(2),
                sort: Sort::CInt32,
                body: Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(
                        Bitvector32Term::Variable(Variable(1)),
                        Bitvector32Term::Variable(Variable(2)),
                    ),
                    true,
                )),
            }),
        };
        let goal = quantified("goal".into());
        let mut curve = Vec::new();
        for size in [8, 16, 32, 64] {
            let facts = ProofFacts::from_ordered(
                &(0..size)
                    .map(|i| quantified(format!("witness{i}")))
                    .collect::<Vec<_>>(),
            );
            assert_eq!(
                facts.quantified_bucket_len(&quantified_equivalence_index_key(&goal).unwrap()),
                Some(size)
            );
            let (matched, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.matching_quantified_fact(&goal)
            });
            assert!(matched.is_some());
            curve.push(work);
        }
        assert!(curve[0] > 0);
        assert!(
            curve.iter().all(|work| *work == curve[0]),
            "single-match bucket work: {curve:?}"
        );
    }

    #[test]
    fn quantified_memory_free_key_rejects_raw_and_registered_loads() {
        let pointer = Pointer {
            block: "p".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before = intern_c_memory(CMemory::new().with_block("p", 4));
        let after = intern_c_memory(
            before
                .as_ref()
                .clone()
                .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(9))),
        );
        let quantified = |memory: SharedCMemory, named: bool| {
            let load = if named {
                Bitvector32Term::Variable(load_variable_for_cell_with_origin(
                    &memory, &pointer, &memory,
                ))
            } else {
                Bitvector32Term::MemoryLoad(memory, Box::new(pointer.clone()))
            };
            Proposition::ForAll {
                var: Variable(1),
                sort: Sort::CInt32,
                body: Box::new(Proposition::ConditionIs(
                    ConditionTerm::equal(load, Bitvector32Term::Variable(Variable(1))),
                    true,
                )),
            }
        };
        for named in [false, true] {
            let left = quantified(before.clone(), named);
            let right = quantified(after.clone(), named);
            assert!(super::super::fact_keys::memory_free_quantified_key(&left).is_none());
            assert_eq!(
                quantified_equivalence_index_key(&left),
                quantified_equivalence_index_key(&right)
            );
            assert!(!quantified_binder_equivalent(&left, &right));
        }
    }

    #[test]
    fn quantified_nested_matching_work_is_linear_and_context_indexed() {
        let nested = |depth: usize, base: u64| {
            let mut p = Proposition::ConditionIs(
                ConditionTerm::equal(
                    Bitvector32Term::Variable(Variable(base)),
                    Bitvector32Term::Constant(0),
                ),
                true,
            );
            for index in (0..depth).rev() {
                p = Proposition::ForAll {
                    var: Variable(base + index as u64),
                    sort: Sort::CInt32,
                    body: Box::new(p),
                };
            }
            p
        };
        let mut depths = Vec::new();
        let mut contexts = Vec::new();
        for size in [8, 16, 32, 64] {
            let left = nested(size, 100);
            let right = nested(size, 1000);
            let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
                quantified_binder_equivalent(&left, &right)
            });
            assert!(matches);
            depths.push(work);
            let mut facts = ProofFacts::from_ordered(&[nested(2, 100)]);
            for index in 0..size {
                facts = facts.with_fact(Proposition::ForAll {
                    var: Variable(9000),
                    sort: Sort::CInt32,
                    body: Box::new(Proposition::ConditionIs(
                        ConditionTerm::equal(
                            Bitvector32Term::Variable(Variable(9000)),
                            Bitvector32Term::Constant(index as u32 + 1),
                        ),
                        true,
                    )),
                });
            }
            let goal = nested(2, 1000);
            let (matches, work) = crate::instrumentation::measure_deterministic_work(|| {
                facts.matching_quantified_fact(&goal).is_some()
            });
            assert!(matches);
            contexts.push(work);
        }
        assert!(depths[0] > 0);
        for pair in depths.windows(2) {
            assert!(pair[1] <= pair[0] * 2, "binder work: {depths:?}");
        }
        assert!(
            contexts.iter().all(|work| *work == contexts[0]),
            "unrelated context work: {contexts:?}"
        );
    }

    #[test]
    fn quantified_binder_comparison_respects_occurrences_inside_snapshots() {
        let pointer = Pointer {
            block: "cell".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let memory = CMemory::new().with_block("cell", 4).store(
            pointer.clone(),
            CValue::Int32(Bitvector32Term::Variable(Variable(11))),
        );
        let proposition = |binder| Proposition::ForAll {
            var: Variable(binder),
            sort: Sort::CInt32,
            body: Box::new(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(Bitvector32Term::MemoryLoad(
                        memory.clone().into(),
                        Box::new(pointer.clone()),
                    )),
                    Box::new(Bitvector32Term::Variable(Variable(binder))),
                ),
                true,
            )),
        };
        // Both formulas name the same snapshot, but 11 is bound inside its
        // stored value only in the first formula. Snapshot identity plus an
        // outer-binder key cannot establish their equivalence.
        assert!(!quantified_binder_equivalent(
            &proposition(11),
            &proposition(22)
        ));
    }

    #[test]
    fn canonical_origin_transport_uses_explicit_memory_derivations() {
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
        // The explicit derivation check must reject this pair without entering
        // the global snapshot-comparison planner.
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
            !events.iter().any(|event| matches!(
                event,
                crate::instrumentation::VerificationEvent::OperationFinished { name, .. }
                    if name == "snapshot comparison: bounded alias"
            )),
            "explicit origin transport must not plan a snapshot comparison: {events:#?}"
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
        // The unchanged proof comes from recorded derivations crossed with
        // exact-fact distinctness, never from whole-snapshot alias search.
        left_pointer == right_pointer
            && crate::kernel::explicit_atomic_equality_from_memory_derivations(
                &Bitvector32Term::MemoryLoad(left_memory, Box::new(left_pointer.clone())),
                &Bitvector32Term::MemoryLoad(right_memory, Box::new(right_pointer)),
                self.assumptions,
            )
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

/// The condition branch of bridged availability. A load named at one
/// snapshot and the same cell named at a later snapshot are different load
/// variables whenever the edge between them is crossed only in context:
/// call-havoc and store edges carry no path assumptions (see
/// `CMemoryDerivation`). A required condition is therefore available when an
/// already-selected candidate is the same condition with each pair of load
/// atoms proven equal under these assumptions.
/// Candidate selection remains the caller's snapshot-blind bucket; nothing is
/// searched, and structurally different propositions never match.
pub(crate) fn condition_bridged_fact_is_available(
    required: &Proposition,
    available: &[Proposition],
    assumptions: &PureFactContext,
) -> bool {
    if matches!(required, Proposition::CResourceSeparate { .. }) || available.is_empty() {
        return false;
    }
    available.iter().any(|candidate| {
        propositions_equal_modulo_origin_unchanged(candidate, required, assumptions)
    })
}

/// [`condition_bridged_fact_is_available`] over an unindexed fact slice:
/// candidates are the facts sharing the required proposition's snapshot-blind
/// key, selected by one pass over the slice, as the exact slice checks beside
/// it already do.
pub(crate) fn condition_bridged_fact_is_available_among(
    required: &Proposition,
    facts: &[Proposition],
    assumptions: &PureFactContext,
) -> bool {
    if matches!(required, Proposition::CResourceSeparate { .. }) {
        return false;
    }
    let key = super::fact_keys::snapshot_blind_proposition_key(required);
    let candidates: Vec<Proposition> = facts
        .iter()
        .filter(|fact| {
            *fact != required && super::fact_keys::snapshot_blind_proposition_key(fact) == key
        })
        .cloned()
        .collect();
    condition_bridged_fact_is_available(required, &candidates, assumptions)
}

/// [`propositions_equal_modulo_proven_snapshots`] for the condition bridge:
/// load atoms additionally match when the memory DAG proves the two loads
/// unchanged between their snapshots under `assumptions`. Separations keep
/// their own branch.
fn propositions_equal_modulo_origin_unchanged(
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
                    .conditions_equal_modulo_origin_unchanged(left_condition, right_condition)
        }
        (Proposition::Implies(left_a, left_b), Proposition::Implies(right_a, right_b))
        | (Proposition::And(left_a, left_b), Proposition::And(right_a, right_b))
        | (Proposition::Or(left_a, left_b), Proposition::Or(right_a, right_b)) => {
            propositions_equal_modulo_origin_unchanged(left_a, right_a, assumptions)
                && propositions_equal_modulo_origin_unchanged(left_b, right_b, assumptions)
        }
        (Proposition::Not(left_body), Proposition::Not(right_body)) => {
            propositions_equal_modulo_origin_unchanged(left_body, right_body, assumptions)
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

#[cfg(test)]
mod integer_reflexivity_tests {
    use super::*;
    use crate::kernel::{
        Bitvector32Term, CMemory, CValue, IntegerRangeFoldIndex, IntegerTerm, MachineIntegerType,
        Pointer, PointerOffsetTerm, SharedIntegerRangeEndpoint, SharedMachineIntegerTerm, Variable,
    };

    #[test]
    fn integer_reflexivity_normalization_checks_polarity_and_exact_terms() {
        for term in [
            IntegerTerm::Variable(Variable(920)),
            IntegerTerm::from_machine(
                MachineIntegerType::Int32,
                Bitvector32Term::Variable(Variable(920)),
            )
            .unwrap(),
        ] {
            let equal = ConditionTerm::IntegerEqual(term.clone().into(), term.clone().into());
            let unequal = ConditionTerm::IntegerNotEqual(term.clone().into(), term.clone().into());
            assert!(normalizes_context_free(&Proposition::ConditionIs(
                equal.clone(),
                true
            )));
            assert!(!normalizes_context_free(&Proposition::ConditionIs(
                equal, false
            )));
            assert!(normalizes_context_free(&Proposition::ConditionIs(
                unequal.clone(),
                false
            )));
            assert!(!normalizes_context_free(&Proposition::ConditionIs(
                unequal, true
            )));
            let successor = IntegerTerm::add(term.clone(), IntegerTerm::constant_i64(1));
            assert!(!normalizes_context_free(&Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(term.into(), successor.into()),
                true,
            )));
        }
    }

    fn integer_fold(
        index: IntegerRangeFoldIndex,
        accumulator: Variable,
        item: Variable,
        body: IntegerTerm,
    ) -> IntegerTerm {
        IntegerTerm::range_fold(index, IntegerTerm::constant_i64(0), accumulator, item, body)
    }

    fn integer_index() -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Integer {
            start: IntegerTerm::constant_i64(0).into(),
            end: IntegerTerm::constant_i64(2).into(),
        }
    }

    fn int32_index() -> IntegerRangeFoldIndex {
        IntegerRangeFoldIndex::Int32 {
            start: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(0)),
            end: SharedIntegerRangeEndpoint::intern(Bitvector32Term::Constant(2)),
        }
    }

    #[test]
    fn integer_equality_normalization_accepts_alpha_equivalent_fold_carriers() {
        let left_accumulator = Variable(93_000);
        let left_item = Variable(93_001);
        let right_accumulator = Variable(94_000);
        let right_item = Variable(94_001);
        let left = integer_fold(
            integer_index(),
            left_accumulator,
            left_item,
            IntegerTerm::add(
                IntegerTerm::var(left_accumulator),
                IntegerTerm::var(left_item),
            ),
        );
        let right = integer_fold(
            integer_index(),
            right_accumulator,
            right_item,
            IntegerTerm::add(
                IntegerTerm::var(right_accumulator),
                IntegerTerm::var(right_item),
            ),
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(left.clone().into(), right.clone().into()),
            true,
        );
        assert_eq!(
            crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(
                &left.into(),
                &right.into(),
            ),
            Some(true)
        );
        assert!(normalizes_context_free(&equality));

        let left_accumulator = Variable(95_000);
        let left_item = Variable(95_001);
        let right_accumulator = Variable(96_000);
        let right_item = Variable(96_001);
        let left = integer_fold(
            int32_index(),
            left_accumulator,
            left_item,
            IntegerTerm::add(
                IntegerTerm::var(left_accumulator),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::Variable(left_item),
                )),
            ),
        );
        let right = integer_fold(
            int32_index(),
            right_accumulator,
            right_item,
            IntegerTerm::add(
                IntegerTerm::var(right_accumulator),
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::Variable(right_item),
                )),
            ),
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(left.clone().into(), right.clone().into()),
            true,
        );
        assert_eq!(
            crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(
                &left.into(),
                &right.into(),
            ),
            Some(true)
        );
        assert!(normalizes_context_free(&equality));
    }

    #[test]
    fn normalize_using_accepts_reversed_alpha_renamed_integer_fold_equality() {
        let source = integer_fold(
            integer_index(),
            Variable(93_100),
            Variable(93_101),
            IntegerTerm::add(
                IntegerTerm::var(Variable(93_100)),
                IntegerTerm::var(Variable(93_101)),
            ),
        );
        let renamed = integer_fold(
            integer_index(),
            Variable(94_100),
            Variable(94_101),
            IntegerTerm::add(
                IntegerTerm::var(Variable(94_100)),
                IntegerTerm::var(Variable(94_101)),
            ),
        );
        let source: SharedIntegerTerm = source.into();
        let renamed: SharedIntegerTerm = renamed.into();
        assert_eq!(
            crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(&source, &renamed),
            Some(true)
        );
        let premise = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(source.clone(), IntegerTerm::constant_i64(0).into()),
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(IntegerTerm::constant_i64(0).into(), renamed),
            true,
        );
        let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&premise));
        assert!(normalize_using_conditions(&goal, &[premise], &facts).is_ok());
    }

    #[test]
    fn normalize_using_alpha_reverse_keeps_snapshot_identity_and_premise_scope() {
        let pointer = Pointer {
            block: "normalize-fold-snapshot".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before =
            crate::kernel::intern_c_memory(CMemory::new().with_block("normalize-fold-snapshot", 8));
        let after = crate::kernel::intern_c_memory(
            before
                .as_ref()
                .clone()
                .store(pointer.clone(), CValue::Int32(Bitvector32Term::Constant(1))),
        );
        let load_fold = |memory: &crate::kernel::SharedCMemory, accumulator, item| {
            integer_fold(
                int32_index(),
                accumulator,
                item,
                IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                    MachineIntegerType::Int32,
                    Bitvector32Term::MemoryLoad(memory.clone(), Box::new(pointer.clone())),
                )),
            )
        };
        let source = load_fold(&before, Variable(94_200), Variable(94_201));
        let changed_snapshot = load_fold(&after, Variable(95_200), Variable(95_201));
        let premise = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(source.into(), IntegerTerm::constant_i64(0).into()),
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(
                IntegerTerm::constant_i64(0).into(),
                changed_snapshot.into(),
            ),
            true,
        );
        let facts = crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&premise));
        assert!(matches!(
            normalize_using_conditions(&goal, &[premise], &facts),
            Err(ConditionalNormalizationError::DoesNotNormalize)
        ));

        let missing_facts = crate::kernel::proof::ProofFacts::from_ordered(&[]);
        let missing = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(
                IntegerTerm::constant_i64(0).into(),
                IntegerTerm::constant_i64(0).into(),
            ),
            true,
        );
        assert!(matches!(
            normalize_using_conditions(&missing, std::slice::from_ref(&missing), &missing_facts),
            Err(ConditionalNormalizationError::UnavailablePremise(0))
        ));
    }

    #[test]
    fn normalize_using_reverses_scalar_integer_equalities_and_disequalities() {
        let left = IntegerTerm::var(Variable(95_300));
        let right = IntegerTerm::var(Variable(95_301));
        for (condition, reversed) in [
            (
                ConditionTerm::IntegerEqual(left.clone().into(), right.clone().into()),
                ConditionTerm::IntegerEqual(right.clone().into(), left.clone().into()),
            ),
            (
                ConditionTerm::IntegerNotEqual(left.clone().into(), right.clone().into()),
                ConditionTerm::IntegerNotEqual(right.into(), left.into()),
            ),
        ] {
            let premise = Proposition::ConditionIs(condition, true);
            let goal = Proposition::ConditionIs(reversed, true);
            let facts =
                crate::kernel::proof::ProofFacts::from_ordered(std::slice::from_ref(&premise));
            assert!(normalize_using_conditions(&goal, &[premise], &facts).is_ok());
        }
    }

    #[test]
    fn integer_equality_normalization_rejects_free_and_cross_carrier_bindings() {
        let bound = integer_fold(
            integer_index(),
            Variable(97_000),
            Variable(97_001),
            IntegerTerm::var(Variable(97_000)),
        );
        let free = integer_fold(
            integer_index(),
            Variable(98_000),
            Variable(98_001),
            IntegerTerm::var(Variable(97_000)),
        );
        let equality = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(bound.clone().into(), free.clone().into()),
            true,
        );
        assert_eq!(
            crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(
                &bound.into(),
                &free.into(),
            ),
            Some(false)
        );
        assert!(!normalizes_context_free(&equality));

        let integer_item = Variable(99_000);
        let machine_item = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            Bitvector32Term::Variable(integer_item),
        ));
        let integer_bound = integer_fold(
            integer_index(),
            Variable(99_001),
            integer_item,
            IntegerTerm::var(integer_item),
        );
        let machine_bound =
            integer_fold(int32_index(), Variable(99_001), integer_item, machine_item);
        let equality = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(integer_bound.clone().into(), machine_bound.clone().into()),
            true,
        );
        assert_eq!(
            crate::kernel::proof::fact_keys::integer_terms_alpha_equivalent(
                &integer_bound.into(),
                &machine_bound.into(),
            ),
            Some(false)
        );
        assert!(!normalizes_context_free(&equality));
    }
}
