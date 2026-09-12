//! Locally checkable certificates for signed machine arithmetic.
//!
//! This module deliberately does not contain a planner.  A caller supplies a
//! flat, topologically ordered certificate and an explicit premise slice;
//! checking recomputes every result from only those inputs.  The old
//! `fact_reasoning` decision procedure remains in place while the surface
//! migration is in progress.

// This checker lands before its surface caller; suppress dead-code warnings
// for the complete internal API until the planner integration tranche wires
// these nodes into proof application.
#![allow(dead_code)]

use super::super::{Bitvector32Term, ConditionTerm, Proposition};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::BTreeMap;

const SIGNED_MIN: i64 = i32::MIN as i64;
const SIGNED_MAX: i64 = i32::MAX as i64;

/// Carriers are explicit even though this first checker accepts only signed
/// int32.  Keeping the carrier on every result prevents a future widening or
/// signedness extension from silently changing an existing certificate.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
// Future machine carriers are part of the typed boundary before their
// checkers are enabled; keep the enum closed over those planned extensions.
#[allow(dead_code)]
pub(crate) enum SignedArithmeticCarrier {
    SignedInt32,
    SignedInt64,
    UnsignedInt32,
    UnsignedInt64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SignedArithmeticRelation {
    LessEqual,
    Equal,
    Disequal,
}

/// A normalized signed-machine affine proposition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SignedArithmeticClaim {
    pub(crate) carrier: SignedArithmeticCarrier,
    pub(crate) relation: SignedArithmeticRelation,
    pub(crate) terms: BTreeMap<Bitvector32Term, BigInt>,
    pub(crate) constant: BigInt,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SignedArithmeticInterval {
    pub(crate) carrier: SignedArithmeticCarrier,
    pub(crate) term: Bitvector32Term,
    pub(crate) lower: i64,
    pub(crate) upper: i64,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub(crate) enum SignedArithmeticComparison {
    LessThan,
    LessEqual,
    Equal,
    Disequal,
}

/// The checked result of one local node.  It is intentionally private to the
/// checker: callers can construct certificates, but cannot manufacture a
/// checked value and feed it to a later node.
#[derive(Clone, Debug, Eq, PartialEq)]
enum CheckedValue {
    Affine(SignedArithmeticClaim),
    Interval(SignedArithmeticInterval),
    Defined {
        carrier: SignedArithmeticCarrier,
        term: Bitvector32Term,
    },
    Proposition(Proposition),
}

/// One topologically ordered local derivation node.
#[derive(Clone, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub(crate) enum SignedArithmeticNode {
    Premise {
        index: usize,
        result: SignedArithmeticClaim,
    },
    Scale {
        source: usize,
        coefficient: BigInt,
        result: SignedArithmeticClaim,
    },
    Add {
        left: usize,
        right: usize,
        result: SignedArithmeticClaim,
    },
    EqualityToLessEqual {
        source: usize,
        reverse: bool,
        result: SignedArithmeticClaim,
    },
    EqualityFromBounds {
        lower: usize,
        upper: usize,
        result: SignedArithmeticClaim,
    },
    Trivial {
        result: SignedArithmeticClaim,
    },
    /// Obtain an interval for an exact one-atom affine bound.
    IntervalFromAffine {
        source: usize,
        term: Bitvector32Term,
        lower: i64,
        upper: i64,
    },
    IntervalIntersect {
        left: usize,
        right: usize,
        result: SignedArithmeticInterval,
    },
    /// An opaque atom has the complete signed-int32 interval.
    IntervalAtom {
        carrier: SignedArithmeticCarrier,
        term: Bitvector32Term,
        lower: i64,
        upper: i64,
    },
    DefinedPremise {
        index: usize,
        carrier: SignedArithmeticCarrier,
        term: Bitvector32Term,
    },
    IntervalAdd {
        left: usize,
        right: usize,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    IntervalSubtract {
        left: usize,
        right: usize,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    IntervalMultiply {
        left: usize,
        right: usize,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    IntervalRemainder {
        operand: usize,
        divisor: i32,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    IntervalShiftLeft {
        operand: usize,
        shift: i32,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    IntervalArithmeticShiftRight {
        operand: usize,
        shift: i32,
        result: SignedArithmeticInterval,
    },
    IntervalBitwiseAnd {
        operand: usize,
        mask: u32,
        defined: usize,
        result: SignedArithmeticInterval,
    },
    IntervalSignBitFlip {
        operand: usize,
        result: SignedArithmeticInterval,
    },
    IntervalCompare {
        left: usize,
        right: usize,
        comparison: SignedArithmeticComparison,
        result: Proposition,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SignedArithmeticCertificate {
    pub(crate) nodes: Vec<SignedArithmeticNode>,
    pub(crate) conclusion: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub(crate) enum SignedArithmeticCheckError {
    InvalidPremise(usize),
    InvalidNodeReference(usize),
    UnsupportedCarrier,
    UnsupportedPremise(usize),
    UnsupportedGoal,
    InvalidDefinedness(usize),
    InvalidOperator(usize),
    InvalidCoefficient(usize),
    InvalidEndpoint(usize),
    InvalidRelation(usize),
    NodeResultMismatch(usize),
    Overflow(usize),
    DoesNotFollow,
}

impl SignedArithmeticCertificate {
    pub(crate) fn check(
        &self,
        goal: &Proposition,
        premises: &[Proposition],
    ) -> Result<(), SignedArithmeticCheckError> {
        if self.conclusion >= self.nodes.len() {
            return Err(SignedArithmeticCheckError::InvalidNodeReference(
                self.conclusion,
            ));
        }
        let mut checked = Vec::with_capacity(self.nodes.len());
        for (node_index, node) in self.nodes.iter().enumerate() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return Err(SignedArithmeticCheckError::Overflow(node_index));
            }
            let value = match node {
                SignedArithmeticNode::Premise { index, result } => {
                    let proposition = premises
                        .get(*index)
                        .ok_or(SignedArithmeticCheckError::InvalidPremise(*index))?;
                    let expected = affine_claim(proposition)
                        .ok_or(SignedArithmeticCheckError::UnsupportedPremise(*index))?;
                    if !same_int32_claim(&expected, result) {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    CheckedValue::Affine(expected)
                }
                SignedArithmeticNode::Scale {
                    source,
                    coefficient,
                    result,
                } => {
                    let source = affine_at(&checked, *source)?;
                    if source.relation == SignedArithmeticRelation::LessEqual
                        && coefficient.is_negative()
                    {
                        return Err(SignedArithmeticCheckError::InvalidCoefficient(node_index));
                    }
                    let expected = scale_claim(source, coefficient)
                        .ok_or(SignedArithmeticCheckError::Overflow(node_index))?;
                    if !same_int32_claim(&expected, result) {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    CheckedValue::Affine(expected)
                }
                SignedArithmeticNode::Add {
                    left,
                    right,
                    result,
                } => {
                    let left = affine_at(&checked, *left)?;
                    let right = affine_at(&checked, *right)?;
                    if left.relation != right.relation {
                        return Err(SignedArithmeticCheckError::InvalidRelation(node_index));
                    }
                    let expected = add_claim(left, right)
                        .ok_or(SignedArithmeticCheckError::Overflow(node_index))?;
                    if !same_int32_claim(&expected, result) {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    CheckedValue::Affine(expected)
                }
                SignedArithmeticNode::EqualityToLessEqual {
                    source,
                    reverse,
                    result,
                } => {
                    let source = affine_at(&checked, *source)?;
                    if source.relation != SignedArithmeticRelation::Equal {
                        return Err(SignedArithmeticCheckError::InvalidRelation(node_index));
                    }
                    let expected = if *reverse {
                        negate_claim(source, SignedArithmeticRelation::LessEqual)
                    } else {
                        SignedArithmeticClaim {
                            relation: SignedArithmeticRelation::LessEqual,
                            ..source.clone()
                        }
                    };
                    if !same_int32_claim(&expected, result) {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    CheckedValue::Affine(expected)
                }
                SignedArithmeticNode::EqualityFromBounds {
                    lower,
                    upper,
                    result,
                } => {
                    let lower = affine_at(&checked, *lower)?;
                    let upper = affine_at(&checked, *upper)?;
                    if lower.relation != SignedArithmeticRelation::LessEqual
                        || upper.relation != SignedArithmeticRelation::LessEqual
                    {
                        return Err(SignedArithmeticCheckError::InvalidRelation(node_index));
                    }
                    let expected = equality_from_bounds(lower, upper)
                        .ok_or(SignedArithmeticCheckError::InvalidRelation(node_index))?;
                    if !same_int32_claim(&expected, result) {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    CheckedValue::Affine(expected)
                }
                SignedArithmeticNode::Trivial { result } => {
                    if !is_trivial(result) || result.carrier != SignedArithmeticCarrier::SignedInt32
                    {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    CheckedValue::Affine(result.clone())
                }
                SignedArithmeticNode::IntervalFromAffine {
                    source,
                    term,
                    lower,
                    upper,
                } => {
                    let source = affine_at(&checked, *source)?;
                    let (expected_lower, expected_upper) = affine_term_bounds(source, term)
                        .ok_or(SignedArithmeticCheckError::InvalidEndpoint(node_index))?;
                    if (*lower, *upper) != (expected_lower, expected_upper) {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    CheckedValue::Interval(SignedArithmeticInterval {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        term: term.clone(),
                        lower: *lower,
                        upper: *upper,
                    })
                }
                SignedArithmeticNode::IntervalAtom {
                    carrier,
                    term,
                    lower,
                    upper,
                } => {
                    require_int32(*carrier)?;
                    if *lower > *upper || *lower < SIGNED_MIN || *upper > SIGNED_MAX {
                        return Err(SignedArithmeticCheckError::InvalidEndpoint(node_index));
                    }
                    let valid_atom =
                        is_opaque_atom(term) && (*lower, *upper) == (SIGNED_MIN, SIGNED_MAX);
                    let valid_constant = term
                        .as_const()
                        .map(|value| i64::from(value as i32))
                        .is_some_and(|value| (*lower, *upper) == (value, value));
                    if !valid_atom && !valid_constant {
                        return Err(SignedArithmeticCheckError::InvalidOperator(node_index));
                    }
                    CheckedValue::Interval(SignedArithmeticInterval {
                        carrier: *carrier,
                        term: term.clone(),
                        lower: *lower,
                        upper: *upper,
                    })
                }
                SignedArithmeticNode::IntervalIntersect {
                    left,
                    right,
                    result,
                } => {
                    let left = interval_at(&checked, *left)?;
                    let right = interval_at(&checked, *right)?;
                    if left.carrier != right.carrier || left.term != right.term {
                        return Err(SignedArithmeticCheckError::InvalidRelation(node_index));
                    }
                    let expected = SignedArithmeticInterval {
                        carrier: left.carrier,
                        term: left.term.clone(),
                        lower: left.lower.max(right.lower),
                        upper: left.upper.min(right.upper),
                    };
                    if expected.lower > expected.upper {
                        return Err(SignedArithmeticCheckError::DoesNotFollow);
                    }
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval(expected)
                }
                SignedArithmeticNode::DefinedPremise {
                    index,
                    carrier,
                    term,
                } => {
                    require_int32(*carrier)?;
                    let proposition = premises
                        .get(*index)
                        .ok_or(SignedArithmeticCheckError::InvalidPremise(*index))?;
                    if !is_exact_definedness(proposition, term) {
                        return Err(SignedArithmeticCheckError::InvalidDefinedness(node_index));
                    }
                    CheckedValue::Defined {
                        carrier: *carrier,
                        term: term.clone(),
                    }
                }
                SignedArithmeticNode::IntervalAdd {
                    left,
                    right,
                    defined,
                    result,
                } => {
                    let left = interval_at(&checked, *left)?;
                    let right = interval_at(&checked, *right)?;
                    let term = Bitvector32Term::Add(
                        Box::new(left.term.clone()),
                        Box::new(right.term.clone()),
                    );
                    require_defined(&checked, *defined, &term, node_index)?;
                    let expected = interval_add(left, right, term, node_index)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval(expected)
                }
                SignedArithmeticNode::IntervalSubtract {
                    left,
                    right,
                    defined,
                    result,
                } => {
                    let left = interval_at(&checked, *left)?;
                    let right = interval_at(&checked, *right)?;
                    let term = Bitvector32Term::Subtract(
                        Box::new(left.term.clone()),
                        Box::new(right.term.clone()),
                    );
                    require_defined(&checked, *defined, &term, node_index)?;
                    let expected = interval_subtract(left, right, term, node_index)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval(expected)
                }
                SignedArithmeticNode::IntervalMultiply {
                    left,
                    right,
                    defined,
                    result,
                } => {
                    let left = interval_at(&checked, *left)?;
                    let right = interval_at(&checked, *right)?;
                    let term = Bitvector32Term::Multiply(
                        Box::new(left.term.clone()),
                        Box::new(right.term.clone()),
                    );
                    require_defined(&checked, *defined, &term, node_index)?;
                    let expected = interval_multiply(left, right, term, node_index)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval(expected)
                }
                SignedArithmeticNode::IntervalRemainder {
                    operand,
                    divisor,
                    defined,
                    result,
                } => {
                    let operand = interval_at(&checked, *operand)?;
                    let divisor_term = Bitvector32Term::Constant(*divisor as u32);
                    let term = Bitvector32Term::Remainder(
                        Box::new(operand.term.clone()),
                        Box::new(divisor_term),
                    );
                    require_defined(&checked, *defined, &term, node_index)?;
                    let expected = interval_remainder(operand, *divisor, term, node_index)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval(expected)
                }
                SignedArithmeticNode::IntervalShiftLeft {
                    operand,
                    shift,
                    defined,
                    result,
                } => {
                    let operand = interval_at(&checked, *operand)?;
                    let shift_term = Bitvector32Term::Constant(*shift as u32);
                    let term = Bitvector32Term::ShiftLeft(
                        Box::new(operand.term.clone()),
                        Box::new(shift_term),
                    );
                    require_defined(&checked, *defined, &term, node_index)?;
                    if !(0..32).contains(shift) || operand.lower < 0 {
                        return Err(SignedArithmeticCheckError::InvalidOperator(node_index));
                    }
                    let factor = 1_i128 << (*shift as u32);
                    let lower = i128::from(operand.lower) * factor;
                    let upper = i128::from(operand.upper) * factor;
                    let expected = interval_checked(term, lower, upper, node_index)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval(expected)
                }
                SignedArithmeticNode::IntervalArithmeticShiftRight {
                    operand,
                    shift,
                    result,
                } => {
                    let operand = interval_at(&checked, *operand)?;
                    if !(0..32).contains(shift) {
                        return Err(SignedArithmeticCheckError::InvalidOperator(node_index));
                    }
                    let term = Bitvector32Term::ArithmeticShiftRight(
                        Box::new(operand.term.clone()),
                        Box::new(Bitvector32Term::Constant(*shift as u32)),
                    );
                    let expected = SignedArithmeticInterval {
                        carrier: operand.carrier,
                        term,
                        lower: i64::from((operand.lower as i32) >> shift),
                        upper: i64::from((operand.upper as i32) >> shift),
                    };
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval(expected)
                }
                SignedArithmeticNode::IntervalBitwiseAnd {
                    operand,
                    mask,
                    defined,
                    result,
                } => {
                    let operand = interval_at(&checked, *operand)?;
                    if *mask > i32::MAX as u32 {
                        return Err(SignedArithmeticCheckError::InvalidOperator(node_index));
                    }
                    let term = Bitvector32Term::BitwiseAnd(
                        Box::new(operand.term.clone()),
                        Box::new(Bitvector32Term::Constant(*mask)),
                    );
                    require_defined(&checked, *defined, &operand.term, node_index)?;
                    let expected = SignedArithmeticInterval {
                        carrier: operand.carrier,
                        term,
                        lower: 0,
                        upper: i64::from(*mask as i32),
                    };
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval(expected)
                }
                SignedArithmeticNode::IntervalSignBitFlip { operand, result } => {
                    let operand = interval_at(&checked, *operand)?;
                    let term = Bitvector32Term::BitwiseXor(
                        Box::new(operand.term.clone()),
                        Box::new(Bitvector32Term::Constant(0x8000_0000)),
                    );
                    let (lower, upper) = if operand.lower >= 0 {
                        (operand.lower + SIGNED_MIN, operand.upper + SIGNED_MIN)
                    } else if operand.upper < 0 {
                        (operand.lower - SIGNED_MIN, operand.upper - SIGNED_MIN)
                    } else {
                        (SIGNED_MIN, SIGNED_MAX)
                    };
                    let expected = SignedArithmeticInterval {
                        carrier: operand.carrier,
                        term,
                        lower,
                        upper,
                    };
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval(expected)
                }
                SignedArithmeticNode::IntervalCompare {
                    left,
                    right,
                    comparison,
                    result,
                } => {
                    let left = interval_at(&checked, *left)?;
                    let right = interval_at(&checked, *right)?;
                    if left.carrier != SignedArithmeticCarrier::SignedInt32
                        || right.carrier != SignedArithmeticCarrier::SignedInt32
                        || left.carrier != right.carrier
                    {
                        return Err(SignedArithmeticCheckError::UnsupportedCarrier);
                    }
                    let expected = comparison_proposition(&left.term, &right.term, *comparison);
                    if &expected != result || !interval_proves(left, right, *comparison) {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    CheckedValue::Proposition(expected)
                }
            };
            checked.push(value);
        }

        let conclusion = checked.get(self.conclusion).ok_or(
            SignedArithmeticCheckError::InvalidNodeReference(self.conclusion),
        )?;
        if conclusion_matches(conclusion, goal) {
            Ok(())
        } else {
            Err(SignedArithmeticCheckError::DoesNotFollow)
        }
    }
}

fn require_int32(carrier: SignedArithmeticCarrier) -> Result<(), SignedArithmeticCheckError> {
    if carrier == SignedArithmeticCarrier::SignedInt32 {
        Ok(())
    } else {
        Err(SignedArithmeticCheckError::UnsupportedCarrier)
    }
}

fn same_int32_claim(expected: &SignedArithmeticClaim, actual: &SignedArithmeticClaim) -> bool {
    expected == actual && expected.carrier == SignedArithmeticCarrier::SignedInt32
}

fn affine_at(
    checked: &[CheckedValue],
    index: usize,
) -> Result<&SignedArithmeticClaim, SignedArithmeticCheckError> {
    match checked.get(index) {
        Some(CheckedValue::Affine(value)) => Ok(value),
        Some(_) => Err(SignedArithmeticCheckError::InvalidRelation(index)),
        None => Err(SignedArithmeticCheckError::InvalidNodeReference(index)),
    }
}

fn interval_at(
    checked: &[CheckedValue],
    index: usize,
) -> Result<&SignedArithmeticInterval, SignedArithmeticCheckError> {
    match checked.get(index) {
        Some(CheckedValue::Interval(value)) => Ok(value),
        Some(_) => Err(SignedArithmeticCheckError::InvalidRelation(index)),
        None => Err(SignedArithmeticCheckError::InvalidNodeReference(index)),
    }
}

fn require_defined(
    checked: &[CheckedValue],
    index: usize,
    term: &Bitvector32Term,
    node: usize,
) -> Result<(), SignedArithmeticCheckError> {
    match checked.get(index) {
        Some(CheckedValue::Defined {
            carrier,
            term: actual,
        }) if *carrier == SignedArithmeticCarrier::SignedInt32 && actual == term => Ok(()),
        Some(_) => Err(SignedArithmeticCheckError::InvalidDefinedness(node)),
        None => Err(SignedArithmeticCheckError::InvalidNodeReference(index)),
    }
}

fn scale_claim(
    source: &SignedArithmeticClaim,
    coefficient: &BigInt,
) -> Option<SignedArithmeticClaim> {
    let terms = source
        .terms
        .iter()
        .map(|(term, value)| Some((term.clone(), value * coefficient)))
        .collect::<Option<BTreeMap<_, _>>>()?;
    Some(SignedArithmeticClaim {
        carrier: source.carrier,
        relation: source.relation,
        terms,
        constant: &source.constant * coefficient,
    })
}

fn add_claim(
    left: &SignedArithmeticClaim,
    right: &SignedArithmeticClaim,
) -> Option<SignedArithmeticClaim> {
    if left.carrier != right.carrier {
        return None;
    }
    let mut terms = left.terms.clone();
    for (term, coefficient) in &right.terms {
        let value = terms.entry(term.clone()).or_default().clone() + coefficient;
        if value.is_zero() {
            terms.remove(term);
        } else {
            terms.insert(term.clone(), value);
        }
    }
    Some(SignedArithmeticClaim {
        carrier: left.carrier,
        relation: left.relation,
        terms,
        constant: &left.constant + &right.constant,
    })
}

fn negate_claim(
    source: &SignedArithmeticClaim,
    relation: SignedArithmeticRelation,
) -> SignedArithmeticClaim {
    SignedArithmeticClaim {
        carrier: source.carrier,
        relation,
        terms: source
            .terms
            .iter()
            .map(|(term, coefficient)| (term.clone(), -coefficient))
            .collect(),
        constant: -&source.constant,
    }
}

fn equality_from_bounds(
    lower: &SignedArithmeticClaim,
    upper: &SignedArithmeticClaim,
) -> Option<SignedArithmeticClaim> {
    if lower.carrier != upper.carrier {
        return None;
    }
    let opposite = upper
        .terms
        .iter()
        .map(|(term, coefficient)| (term.clone(), -coefficient))
        .collect::<BTreeMap<_, _>>();
    if lower.terms != opposite || lower.constant != -&upper.constant {
        return None;
    }
    Some(SignedArithmeticClaim {
        carrier: lower.carrier,
        relation: SignedArithmeticRelation::Equal,
        terms: lower.terms.clone(),
        constant: lower.constant.clone(),
    })
}

fn is_trivial(claim: &SignedArithmeticClaim) -> bool {
    claim.terms.is_empty()
        && match claim.relation {
            SignedArithmeticRelation::LessEqual => claim.constant <= BigInt::zero(),
            SignedArithmeticRelation::Equal => claim.constant.is_zero(),
            SignedArithmeticRelation::Disequal => !claim.constant.is_zero(),
        }
}

fn affine_term_bounds(claim: &SignedArithmeticClaim, term: &Bitvector32Term) -> Option<(i64, i64)> {
    if claim.terms.len() != 1 || claim.relation != SignedArithmeticRelation::LessEqual {
        return None;
    }
    let (atom, coefficient) = claim.terms.iter().next()?;
    if atom != term {
        return None;
    }
    let bound = claim.constant.to_i64()?;
    match coefficient.to_i64()? {
        1 => Some((SIGNED_MIN, bound.min(SIGNED_MAX))),
        -1 => Some(((-bound).max(SIGNED_MIN), SIGNED_MAX)),
        _ => None,
    }
}

fn is_opaque_atom(term: &Bitvector32Term) -> bool {
    matches!(
        term,
        Bitvector32Term::Variable(_)
            | Bitvector32Term::MemoryLoad(_, _)
            | Bitvector32Term::PointerAddress(_)
            | Bitvector32Term::PureFunctionApplication { .. }
            | Bitvector32Term::ClickFunctionApplication { .. }
            | Bitvector32Term::AlgebraicMatch { .. }
    )
}

fn interval_checked(
    term: Bitvector32Term,
    lower: i128,
    upper: i128,
    node: usize,
) -> Result<SignedArithmeticInterval, SignedArithmeticCheckError> {
    if lower < i128::from(SIGNED_MIN) || upper > i128::from(SIGNED_MAX) || lower > upper {
        return Err(SignedArithmeticCheckError::Overflow(node));
    }
    Ok(SignedArithmeticInterval {
        carrier: SignedArithmeticCarrier::SignedInt32,
        term,
        lower: lower as i64,
        upper: upper as i64,
    })
}

fn check_interval_result(
    expected: &SignedArithmeticInterval,
    actual: &SignedArithmeticInterval,
    node: usize,
) -> Result<(), SignedArithmeticCheckError> {
    if expected == actual {
        Ok(())
    } else {
        Err(SignedArithmeticCheckError::NodeResultMismatch(node))
    }
}

fn interval_add(
    left: &SignedArithmeticInterval,
    right: &SignedArithmeticInterval,
    term: Bitvector32Term,
    node: usize,
) -> Result<SignedArithmeticInterval, SignedArithmeticCheckError> {
    interval_checked(
        term,
        i128::from(left.lower) + i128::from(right.lower),
        i128::from(left.upper) + i128::from(right.upper),
        node,
    )
}

fn interval_subtract(
    left: &SignedArithmeticInterval,
    right: &SignedArithmeticInterval,
    term: Bitvector32Term,
    node: usize,
) -> Result<SignedArithmeticInterval, SignedArithmeticCheckError> {
    interval_checked(
        term,
        i128::from(left.lower) - i128::from(right.upper),
        i128::from(left.upper) - i128::from(right.lower),
        node,
    )
}

fn interval_multiply(
    left: &SignedArithmeticInterval,
    right: &SignedArithmeticInterval,
    term: Bitvector32Term,
    node: usize,
) -> Result<SignedArithmeticInterval, SignedArithmeticCheckError> {
    let values = [
        i128::from(left.lower) * i128::from(right.lower),
        i128::from(left.lower) * i128::from(right.upper),
        i128::from(left.upper) * i128::from(right.lower),
        i128::from(left.upper) * i128::from(right.upper),
    ];
    interval_checked(
        term,
        *values.iter().min().unwrap(),
        *values.iter().max().unwrap(),
        node,
    )
}

fn interval_remainder(
    operand: &SignedArithmeticInterval,
    divisor: i32,
    term: Bitvector32Term,
    node: usize,
) -> Result<SignedArithmeticInterval, SignedArithmeticCheckError> {
    if divisor == 0 {
        return Err(SignedArithmeticCheckError::InvalidOperator(node));
    }
    // The explicit definedness premise rules out the one overflowing
    // INT_MIN % -1 case.  Every other signed remainder has magnitude less
    // than the divisor's magnitude and keeps the dividend's sign.
    let magnitude = i64::from(divisor).abs().saturating_sub(1);
    let (lower, upper) = if operand.lower >= 0 {
        (0, magnitude)
    } else if operand.upper < 0 {
        (-magnitude, 0)
    } else {
        (-magnitude, magnitude)
    };
    interval_checked(term, i128::from(lower), i128::from(upper), node)
}

fn is_exact_definedness(proposition: &Proposition, term: &Bitvector32Term) -> bool {
    let Proposition::ConditionIs(condition, false) = proposition else {
        return false;
    };
    match (condition, term) {
        (ConditionTerm::Bitvector32SignedAddOverflows(left, right), Bitvector32Term::Add(a, b))
        | (
            ConditionTerm::Bitvector32SignedSubtractOverflows(left, right),
            Bitvector32Term::Subtract(a, b),
        )
        | (
            ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right),
            Bitvector32Term::Multiply(a, b),
        ) => left.as_ref() == a.as_ref() && right.as_ref() == b.as_ref(),
        (
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right),
            Bitvector32Term::ShiftLeft(a, b),
        ) => left.as_ref() == a.as_ref() && right.as_ref() == b.as_ref(),
        (
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right),
            Bitvector32Term::Remainder(a, b),
        ) => left.as_ref() == a.as_ref() && right.as_ref() == b.as_ref(),
        _ => false,
    }
}

fn comparison_proposition(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    comparison: SignedArithmeticComparison,
) -> Proposition {
    let condition = match comparison {
        SignedArithmeticComparison::LessThan => ConditionTerm::Bitvector32SignedLessThan(
            Box::new(left.clone()),
            Box::new(right.clone()),
        ),
        SignedArithmeticComparison::LessEqual => ConditionTerm::Bitvector32SignedLessEqual(
            Box::new(left.clone()),
            Box::new(right.clone()),
        ),
        SignedArithmeticComparison::Equal => {
            ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone()))
        }
        SignedArithmeticComparison::Disequal => {
            ConditionTerm::Bitvector32Equal(Box::new(left.clone()), Box::new(right.clone()))
        }
    };
    if comparison == SignedArithmeticComparison::Disequal {
        Proposition::ConditionIs(condition, false)
    } else {
        Proposition::ConditionIs(condition, true)
    }
}

fn interval_proves(
    left: &SignedArithmeticInterval,
    right: &SignedArithmeticInterval,
    comparison: SignedArithmeticComparison,
) -> bool {
    match comparison {
        SignedArithmeticComparison::LessThan => left.upper < right.lower,
        SignedArithmeticComparison::LessEqual => left.upper <= right.lower,
        SignedArithmeticComparison::Equal => {
            left.lower == left.upper && left.lower == right.lower && right.lower == right.upper
        }
        SignedArithmeticComparison::Disequal => {
            left.upper < right.lower || right.upper < left.lower
        }
    }
}

fn affine_claim(proposition: &Proposition) -> Option<SignedArithmeticClaim> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !*value),
            _ => return None,
        },
        _ => return None,
    };
    let (relation, left, right, strict) = match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterThan(right, left), true) => {
            (SignedArithmeticRelation::LessEqual, left, right, true)
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(right, left), true) => {
            (SignedArithmeticRelation::LessEqual, left, right, false)
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false)
        | (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, right, left, true)
        }
        (ConditionTerm::Bitvector32SignedLessThan(right, left), false)
        | (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, right, left, false)
        }
        (ConditionTerm::Bitvector32Equal(left, right), true) => {
            let (terms, constant) = affine_difference(left, right)?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Equal,
                terms,
                constant,
            });
        }
        (ConditionTerm::Bitvector32Equal(left, right), false) => {
            let (terms, constant) = affine_difference(left, right)?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Disequal,
                terms,
                constant,
            });
        }
        (ConditionTerm::Constant(constant), value) => {
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Equal,
                terms: BTreeMap::new(),
                constant: if *constant == value {
                    BigInt::zero()
                } else {
                    BigInt::one()
                },
            });
        }
        _ => return None,
    };
    let (terms, mut constant) = affine_difference(left, right)?;
    if strict {
        constant += 1;
    }
    constant = -constant;
    Some(SignedArithmeticClaim {
        carrier: SignedArithmeticCarrier::SignedInt32,
        relation,
        terms,
        constant,
    })
}

fn affine_difference(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(BTreeMap<Bitvector32Term, BigInt>, BigInt)> {
    let mut terms: BTreeMap<Bitvector32Term, BigInt> = BTreeMap::new();
    let mut constant = BigInt::zero();
    let mut pending = vec![(left, BigInt::one()), (right, -BigInt::one())];
    while let Some((term, coefficient)) = pending.pop() {
        match term {
            Bitvector32Term::Constant(value) => {
                constant += coefficient * BigInt::from(*value as i32);
            }
            Bitvector32Term::Add(a, b) => {
                pending.push((a, coefficient.clone()));
                pending.push((b, coefficient));
            }
            Bitvector32Term::Subtract(a, b) => {
                pending.push((a, coefficient.clone()));
                pending.push((b, -coefficient));
            }
            Bitvector32Term::Multiply(a, b) => {
                if let Some(value) = a.as_const() {
                    pending.push((b, coefficient * BigInt::from(value as i32)));
                } else {
                    let value = b.as_const()?;
                    pending.push((a, coefficient * BigInt::from(value as i32)));
                }
            }
            term if is_opaque_atom(term) => {
                let atom = crate::kernel::eval::canonical_term(term);
                let updated = terms.entry(atom.clone()).or_default().clone() + coefficient;
                if updated.is_zero() {
                    terms.remove(&atom);
                } else {
                    terms.insert(atom, updated);
                }
            }
            _ => return None,
        }
    }
    Some((terms, constant))
}

fn conclusion_matches(value: &CheckedValue, goal: &Proposition) -> bool {
    match value {
        CheckedValue::Affine(claim) => {
            affine_claim(goal).is_some_and(|expected| expected == *claim)
        }
        CheckedValue::Proposition(proposition) => proposition == goal,
        CheckedValue::Interval(_) | CheckedValue::Defined { .. } => false,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Variable;

    fn x() -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(1))
    }

    fn y() -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(2))
    }

    fn prop(condition: ConditionTerm) -> Proposition {
        Proposition::ConditionIs(condition, true)
    }

    fn claim(proposition: &Proposition) -> SignedArithmeticClaim {
        affine_claim(proposition).unwrap()
    }

    fn le(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        prop(ConditionTerm::signed_less_equal(left, right))
    }

    #[test]
    fn certificate_checks_scaled_affine_interval_and_definedness_derivation() {
        let lower_premise = le(Bitvector32Term::Constant(0), x());
        let upper_premise = le(x(), Bitvector32Term::Constant(100));
        let add_term = Bitvector32Term::Add(Box::new(x()), Box::new(x()));
        let defined =
            Proposition::ConditionIs(ConditionTerm::signed_add_overflows(x(), x()), false);
        let goal = le(add_term.clone(), Bitvector32Term::Constant(200));
        let mut doubled = claim(&upper_premise);
        doubled.terms.values_mut().for_each(|value| *value *= 2);
        doubled.constant *= 2;
        let certificate = SignedArithmeticCertificate {
            nodes: vec![
                SignedArithmeticNode::Premise {
                    index: 0,
                    result: claim(&lower_premise),
                },
                SignedArithmeticNode::Premise {
                    index: 1,
                    result: claim(&upper_premise),
                },
                SignedArithmeticNode::Scale {
                    source: 1,
                    coefficient: BigInt::from(2),
                    result: doubled,
                },
                SignedArithmeticNode::DefinedPremise {
                    index: 2,
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: add_term.clone(),
                },
                SignedArithmeticNode::IntervalFromAffine {
                    source: 0,
                    term: x(),
                    lower: 0,
                    upper: SIGNED_MAX,
                },
                SignedArithmeticNode::IntervalFromAffine {
                    source: 1,
                    term: x(),
                    lower: SIGNED_MIN,
                    upper: 100,
                },
                SignedArithmeticNode::IntervalIntersect {
                    left: 4,
                    right: 5,
                    result: SignedArithmeticInterval {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        term: x(),
                        lower: 0,
                        upper: 100,
                    },
                },
                SignedArithmeticNode::IntervalAdd {
                    left: 6,
                    right: 6,
                    defined: 3,
                    result: SignedArithmeticInterval {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        term: add_term.clone(),
                        lower: 0,
                        upper: 200,
                    },
                },
                SignedArithmeticNode::IntervalAtom {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: Bitvector32Term::Constant(200),
                    lower: 200,
                    upper: 200,
                },
                SignedArithmeticNode::IntervalCompare {
                    left: 7,
                    right: 8,
                    comparison: SignedArithmeticComparison::LessEqual,
                    result: goal.clone(),
                },
            ],
            conclusion: 9,
        };
        certificate
            .check(&goal, &[lower_premise, upper_premise, defined])
            .unwrap();
    }

    #[test]
    fn rejects_forward_and_out_of_range_references() {
        let goal = le(x(), Bitvector32Term::Constant(1));
        let certificate = SignedArithmeticCertificate {
            nodes: vec![SignedArithmeticNode::Scale {
                source: 1,
                coefficient: BigInt::one(),
                result: claim(&goal),
            }],
            conclusion: 0,
        };
        assert_eq!(
            certificate.check(&goal, std::slice::from_ref(&goal)),
            Err(SignedArithmeticCheckError::InvalidNodeReference(1))
        );
        let certificate = SignedArithmeticCertificate {
            nodes: vec![],
            conclusion: 0,
        };
        assert_eq!(
            certificate.check(&goal, &[]),
            Err(SignedArithmeticCheckError::InvalidNodeReference(0))
        );
    }

    #[test]
    fn rejects_changed_terms_carriers_operators_endpoints_and_coefficients() {
        let premise = le(x(), Bitvector32Term::Constant(10));
        let goal = le(x(), Bitvector32Term::Constant(20));
        let mut result = claim(&premise);
        result.constant = BigInt::from(20);
        let bad_premise = SignedArithmeticCertificate {
            nodes: vec![SignedArithmeticNode::Premise { index: 0, result }],
            conclusion: 0,
        };
        assert!(matches!(
            bad_premise.check(&goal, std::slice::from_ref(&premise)),
            Err(SignedArithmeticCheckError::NodeResultMismatch(0))
        ));

        let atom = SignedArithmeticNode::IntervalAtom {
            carrier: SignedArithmeticCarrier::SignedInt64,
            term: x(),
            lower: SIGNED_MIN,
            upper: SIGNED_MAX,
        };
        let bad_type = SignedArithmeticCertificate {
            nodes: vec![atom],
            conclusion: 0,
        };
        assert_eq!(
            bad_type.check(&goal, &[]),
            Err(SignedArithmeticCheckError::UnsupportedCarrier)
        );

        let bad_operator = SignedArithmeticCertificate {
            nodes: vec![SignedArithmeticNode::IntervalAtom {
                carrier: SignedArithmeticCarrier::SignedInt32,
                term: Bitvector32Term::Add(Box::new(x()), Box::new(y())),
                lower: SIGNED_MIN,
                upper: SIGNED_MAX,
            }],
            conclusion: 0,
        };
        assert_eq!(
            bad_operator.check(&goal, &[]),
            Err(SignedArithmeticCheckError::InvalidOperator(0))
        );

        let bad_endpoints = SignedArithmeticCertificate {
            nodes: vec![SignedArithmeticNode::IntervalAtom {
                carrier: SignedArithmeticCarrier::SignedInt32,
                term: x(),
                lower: 10,
                upper: 1,
            }],
            conclusion: 0,
        };
        assert_eq!(
            bad_endpoints.check(&goal, &[]),
            Err(SignedArithmeticCheckError::InvalidEndpoint(0))
        );

        let mut scaled = claim(&premise);
        scaled.constant *= 3;
        let bad_coefficient = SignedArithmeticCertificate {
            nodes: vec![
                SignedArithmeticNode::Premise {
                    index: 0,
                    result: claim(&premise),
                },
                SignedArithmeticNode::Scale {
                    source: 0,
                    coefficient: BigInt::from(2),
                    result: scaled,
                },
            ],
            conclusion: 1,
        };
        assert!(matches!(
            bad_coefficient.check(&goal, std::slice::from_ref(&premise)),
            Err(SignedArithmeticCheckError::NodeResultMismatch(1))
        ));
    }

    #[test]
    fn rejects_overflow_and_wrong_definedness_locally() {
        let left_term = Bitvector32Term::Constant(i32::MAX as u32);
        let right_term = Bitvector32Term::Constant(1);
        let left = SignedArithmeticNode::IntervalAtom {
            carrier: SignedArithmeticCarrier::SignedInt32,
            term: left_term.clone(),
            lower: i32::MAX as i64,
            upper: i32::MAX as i64,
        };
        let right = SignedArithmeticNode::IntervalAtom {
            carrier: SignedArithmeticCarrier::SignedInt32,
            term: right_term.clone(),
            lower: 1,
            upper: 1,
        };
        let overflow = SignedArithmeticCertificate {
            nodes: vec![
                left,
                right,
                SignedArithmeticNode::DefinedPremise {
                    index: 0,
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: Bitvector32Term::Add(
                        Box::new(left_term.clone()),
                        Box::new(right_term.clone()),
                    ),
                },
                SignedArithmeticNode::IntervalAdd {
                    left: 0,
                    right: 1,
                    defined: 2,
                    result: SignedArithmeticInterval {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        term: Bitvector32Term::Add(
                            Box::new(left_term.clone()),
                            Box::new(right_term.clone()),
                        ),
                        lower: i32::MAX as i64,
                        upper: i32::MAX as i64,
                    },
                },
            ],
            conclusion: 3,
        };
        let wrong_defined = Proposition::ConditionIs(
            ConditionTerm::signed_add_overflows(left_term.clone(), Bitvector32Term::Constant(2)),
            false,
        );
        assert_eq!(
            overflow.check(
                &le(
                    Bitvector32Term::Add(
                        Box::new(left_term.clone()),
                        Box::new(right_term.clone()),
                    ),
                    Bitvector32Term::Constant(i32::MAX as u32),
                ),
                &[wrong_defined],
            ),
            Err(SignedArithmeticCheckError::InvalidDefinedness(2))
        );
    }
}
