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

use super::super::{Bitvector32Term, ConditionTerm, Proposition, Variable};
use num_bigint::BigInt;
use num_traits::{One, Signed, ToPrimitive, Zero};
use std::collections::{BTreeMap, HashMap};

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

#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum SignedArithmeticAtomToken {
    Constant(u32),
    Variable(Variable),
    PureFunction { name: String, arity: usize },
    Binary(SignedArithmeticBinaryOperator),
    UnaryNot,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
enum SignedArithmeticBinaryOperator {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
    ShiftLeft,
    ArithmeticShiftRight,
    LogicalShiftRight,
    BitwiseAnd,
    BitwiseOr,
    BitwiseXor,
}

/// Flat, iterative identity for the supported signed-machine term fragment.
/// Claim maps and checked arena atoms use this key rather than deriving
/// equality/ordering over the recursive source term. New payload families must
/// add tokens here or remain rejected by `signed_arithmetic_atom_key`.
#[derive(Clone, Debug, Eq, PartialEq, Hash, Ord, PartialOrd)]
pub(crate) struct SignedArithmeticAtom {
    tokens: Vec<SignedArithmeticAtomToken>,
}

impl SignedArithmeticAtom {
    /// Build the bounded identity used by claims and checked term arenas.
    /// Unsupported payload families fail closed until their own flat token
    /// encoding is added here.
    pub(crate) fn from_term(term: &Bitvector32Term) -> Option<Self> {
        signed_arithmetic_atom_key(term)
    }

    pub(crate) fn work(&self) -> usize {
        signed_atom_work(self)
    }

    fn is_opaque_root(&self) -> bool {
        matches!(
            self.tokens.first(),
            Some(SignedArithmeticAtomToken::Variable(_))
                | Some(SignedArithmeticAtomToken::PureFunction { .. })
        ) && self.tokens.iter().all(|token| {
            matches!(
                token,
                SignedArithmeticAtomToken::Constant(_)
                    | SignedArithmeticAtomToken::Variable(_)
                    | SignedArithmeticAtomToken::PureFunction { .. }
            )
        })
    }
}

fn signed_arithmetic_atom_key(root: &Bitvector32Term) -> Option<SignedArithmeticAtom> {
    let mut tokens = Vec::new();
    let mut pending = vec![root];
    macro_rules! push_token {
        ($token:expr) => {{
            let growth = if tokens.len() == tokens.capacity() {
                tokens.capacity().max(1)
            } else {
                1
            };
            if crate::instrumentation::deadline_exceeded_with_work(growth) {
                return None;
            }
            tokens.push($token);
        }};
    }
    while let Some(term) = pending.pop() {
        let units = match term {
            Bitvector32Term::Constant(value) => (u32::BITS - value.leading_zeros()) as usize + 2,
            Bitvector32Term::Variable(_) => 2,
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                name.len().saturating_add(arguments.len()).saturating_add(3)
            }
            Bitvector32Term::Add(_, _)
            | Bitvector32Term::Subtract(_, _)
            | Bitvector32Term::Multiply(_, _)
            | Bitvector32Term::Divide(_, _)
            | Bitvector32Term::Remainder(_, _)
            | Bitvector32Term::ShiftLeft(_, _)
            | Bitvector32Term::ArithmeticShiftRight(_, _)
            | Bitvector32Term::LogicalShiftRight(_, _)
            | Bitvector32Term::BitwiseAnd(_, _)
            | Bitvector32Term::BitwiseOr(_, _)
            | Bitvector32Term::BitwiseXor(_, _) => 3,
            Bitvector32Term::BitwiseNot(_) => 2,
            _ => 1,
        };
        if crate::instrumentation::deadline_exceeded_with_work(units) {
            return None;
        }
        match term {
            Bitvector32Term::Constant(value) => {
                push_token!(SignedArithmeticAtomToken::Constant(*value));
            }
            Bitvector32Term::Variable(variable) => {
                push_token!(SignedArithmeticAtomToken::Variable(*variable));
            }
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                push_token!(SignedArithmeticAtomToken::PureFunction {
                    name: name.clone(),
                    arity: arguments.len(),
                });
                pending.extend(arguments.iter().rev());
            }
            Bitvector32Term::Add(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::Add,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::Subtract(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::Subtract,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::Multiply(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::Multiply,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::Divide(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::Divide,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::Remainder(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::Remainder,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::ShiftLeft(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::ShiftLeft,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::ArithmeticShiftRight(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::ArithmeticShiftRight,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::LogicalShiftRight(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::LogicalShiftRight,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::BitwiseAnd(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::BitwiseAnd,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::BitwiseOr(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::BitwiseOr,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::BitwiseXor(left, right) => {
                push_token!(SignedArithmeticAtomToken::Binary(
                    SignedArithmeticBinaryOperator::BitwiseXor,
                ));
                pending.push(right);
                pending.push(left);
            }
            Bitvector32Term::BitwiseNot(operand) => {
                push_token!(SignedArithmeticAtomToken::UnaryNot);
                pending.push(operand);
            }
            _ => return None,
        }
    }
    Some(SignedArithmeticAtom { tokens })
}

/// A normalized signed-machine affine proposition.
///
/// The invariant is `sum(terms * atoms) + constant relation 0`.  For example,
/// `x <= 5` is stored as `x - 5 <= 0`, while `x == 5` is stored as
/// `x - 5 == 0`; there is no separate RHS convention for equality.  Keeping
/// one zero-centered convention makes equality-to-order and interval
/// extraction local checks.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SignedArithmeticClaim {
    pub(crate) carrier: SignedArithmeticCarrier,
    pub(crate) relation: SignedArithmeticRelation,
    pub(crate) terms: BTreeMap<SignedArithmeticAtom, BigInt>,
    pub(crate) constant: BigInt,
}

/// Claimed endpoints for an interval.  The expression identity is held in
/// the checker's linear term arena and operation nodes refer to child handles;
/// repeating a deep expression in every result would make a deep certificate
/// quadratic before checking began.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SignedArithmeticInterval {
    pub(crate) carrier: SignedArithmeticCarrier,
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
    Interval {
        value: SignedArithmeticInterval,
        term: usize,
    },
    Defined {
        carrier: SignedArithmeticCarrier,
        term: Bitvector32Term,
    },
    Proposition(Proposition),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CheckedBinaryOperator {
    Add,
    Subtract,
    Multiply,
    Remainder,
    ShiftLeft,
    ArithmeticShiftRight,
    BitwiseAnd,
    BitwiseXor,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum CheckedUnaryOperator {
    BitwiseNot,
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum CheckedTerm {
    Atom(SignedArithmeticAtom),
    Binary {
        operator: CheckedBinaryOperator,
        left: usize,
        right: usize,
    },
    Unary {
        operator: CheckedUnaryOperator,
        operand: usize,
    },
}

#[derive(Default)]
struct TermArena {
    terms: Vec<CheckedTerm>,
    equivalence_cache: HashMap<(usize, usize), bool>,
}

fn pair_is_equivalent(cache: &HashMap<(usize, usize), bool>, left: usize, right: usize) -> bool {
    left == right || cache.get(&(left, right)).is_some_and(|result| *result)
}

impl TermArena {
    fn atom(&mut self, term: Bitvector32Term) -> Option<usize> {
        let term = SignedArithmeticAtom::from_term(&term)?;
        Some(self.atom_key(term))
    }

    fn atom_key(&mut self, term: SignedArithmeticAtom) -> usize {
        let reference = self.terms.len();
        self.terms.push(CheckedTerm::Atom(term));
        reference
    }

    fn binary(&mut self, operator: CheckedBinaryOperator, left: usize, right: usize) -> usize {
        let reference = self.terms.len();
        self.terms.push(CheckedTerm::Binary {
            operator,
            left,
            right,
        });
        reference
    }

    fn unary(&mut self, operator: CheckedUnaryOperator, operand: usize) -> usize {
        let reference = self.terms.len();
        self.terms.push(CheckedTerm::Unary { operator, operand });
        reference
    }

    fn equivalent(&mut self, left: usize, right: usize) -> bool {
        if left == right {
            return true;
        }
        if let Some(result) = self.equivalence_cache.get(&(left, right)) {
            return *result;
        }
        // The third tuple element is a postorder marker. Every completed pair,
        // including shared subgraphs beneath distinct wrapper roots, is
        // memoized before its parent is discharged.
        let mut pending = vec![(left, right, false)];
        while let Some((left, right, expanded)) = pending.pop() {
            if left == right {
                continue;
            }
            if self.equivalence_cache.contains_key(&(left, right)) {
                continue;
            }
            if !expanded {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    return false;
                }
                match (&self.terms[left], &self.terms[right]) {
                    (CheckedTerm::Atom(left_term), CheckedTerm::Atom(right_term)) => {
                        if !charge_atom_pair_work(left_term, right_term) {
                            return false;
                        }
                        let equivalent = left_term == right_term;
                        self.equivalence_cache.insert((left, right), equivalent);
                        self.equivalence_cache.insert((right, left), equivalent);
                        if !equivalent {
                            return false;
                        }
                    }
                    (
                        CheckedTerm::Binary {
                            operator: left_operator,
                            left: left_left,
                            right: left_right,
                        },
                        CheckedTerm::Binary {
                            operator: right_operator,
                            left: right_left,
                            right: right_right,
                        },
                    ) if left_operator == right_operator => {
                        pending.push((left, right, true));
                        pending.push((*left_right, *right_right, false));
                        pending.push((*left_left, *right_left, false));
                    }
                    (
                        CheckedTerm::Unary {
                            operator: left_operator,
                            operand: left_operand,
                        },
                        CheckedTerm::Unary {
                            operator: right_operator,
                            operand: right_operand,
                        },
                    ) if left_operator == right_operator => {
                        pending.push((left, right, true));
                        pending.push((*left_operand, *right_operand, false));
                    }
                    _ => {
                        self.equivalence_cache.insert((left, right), false);
                        self.equivalence_cache.insert((right, left), false);
                        return false;
                    }
                }
            } else {
                let equivalent = match (&self.terms[left], &self.terms[right]) {
                    (
                        CheckedTerm::Binary {
                            left: left_left,
                            right: left_right,
                            ..
                        },
                        CheckedTerm::Binary {
                            left: right_left,
                            right: right_right,
                            ..
                        },
                    ) => {
                        pair_is_equivalent(&self.equivalence_cache, *left_left, *right_left)
                            && pair_is_equivalent(
                                &self.equivalence_cache,
                                *left_right,
                                *right_right,
                            )
                    }
                    (
                        CheckedTerm::Unary {
                            operand: left_operand,
                            ..
                        },
                        CheckedTerm::Unary {
                            operand: right_operand,
                            ..
                        },
                    ) => pair_is_equivalent(&self.equivalence_cache, *left_operand, *right_operand),
                    _ => false,
                };
                self.equivalence_cache.insert((left, right), equivalent);
                self.equivalence_cache.insert((right, left), equivalent);
                if !equivalent {
                    return false;
                }
            }
        }
        true
    }

    fn equivalent_explicit(&self, reference: usize, explicit: &Bitvector32Term) -> bool {
        let mut pending = vec![(reference, explicit)];
        while let Some((reference, explicit)) = pending.pop() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return false;
            }
            match (&self.terms[reference], explicit) {
                (CheckedTerm::Atom(expected), actual) => {
                    let Some(actual) = SignedArithmeticAtom::from_term(actual) else {
                        return false;
                    };
                    if !charge_atom_pair_work(expected, &actual) || expected != &actual {
                        return false;
                    }
                }
                (
                    CheckedTerm::Binary {
                        operator,
                        left,
                        right,
                    },
                    actual,
                ) => {
                    let Some((actual_operator, actual_left, actual_right)) =
                        explicit_binary(*operator, actual)
                    else {
                        return false;
                    };
                    if *operator != actual_operator {
                        return false;
                    }
                    pending.push((*left, actual_left));
                    pending.push((*right, actual_right));
                }
                (CheckedTerm::Unary { operator, operand }, actual) => {
                    let Some((actual_operator, actual_operand)) = explicit_unary(*operator, actual)
                    else {
                        return false;
                    };
                    if *operator != actual_operator {
                        return false;
                    }
                    pending.push((*operand, actual_operand));
                }
            }
        }
        true
    }
}

fn explicit_binary(
    operator: CheckedBinaryOperator,
    term: &Bitvector32Term,
) -> Option<(CheckedBinaryOperator, &Bitvector32Term, &Bitvector32Term)> {
    let (actual_operator, left, right) = match (operator, term) {
        (CheckedBinaryOperator::Add, Bitvector32Term::Add(left, right)) => {
            (CheckedBinaryOperator::Add, left, right)
        }
        (CheckedBinaryOperator::Subtract, Bitvector32Term::Subtract(left, right)) => {
            (CheckedBinaryOperator::Subtract, left, right)
        }
        (CheckedBinaryOperator::Multiply, Bitvector32Term::Multiply(left, right)) => {
            (CheckedBinaryOperator::Multiply, left, right)
        }
        (CheckedBinaryOperator::Remainder, Bitvector32Term::Remainder(left, right)) => {
            (CheckedBinaryOperator::Remainder, left, right)
        }
        (CheckedBinaryOperator::ShiftLeft, Bitvector32Term::ShiftLeft(left, right)) => {
            (CheckedBinaryOperator::ShiftLeft, left, right)
        }
        (
            CheckedBinaryOperator::ArithmeticShiftRight,
            Bitvector32Term::ArithmeticShiftRight(left, right),
        ) => (CheckedBinaryOperator::ArithmeticShiftRight, left, right),
        (CheckedBinaryOperator::BitwiseAnd, Bitvector32Term::BitwiseAnd(left, right)) => {
            (CheckedBinaryOperator::BitwiseAnd, left, right)
        }
        (CheckedBinaryOperator::BitwiseXor, Bitvector32Term::BitwiseXor(left, right)) => {
            (CheckedBinaryOperator::BitwiseXor, left, right)
        }
        _ => return None,
    };
    Some((actual_operator, left, right))
}

fn explicit_unary(
    operator: CheckedUnaryOperator,
    term: &Bitvector32Term,
) -> Option<(CheckedUnaryOperator, &Bitvector32Term)> {
    match (operator, term) {
        (CheckedUnaryOperator::BitwiseNot, Bitvector32Term::BitwiseNot(operand)) => {
            Some((CheckedUnaryOperator::BitwiseNot, operand))
        }
        _ => None,
    }
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
    /// Add two intervals whose endpoint sum is already within int32.  The
    /// child intervals therefore establish definedness without requiring a
    /// separate source-level overflow proposition.
    IntervalAddBounded {
        left: usize,
        right: usize,
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
        // Bitwise-and is total for signed int32 values.  UB-sensitive work
        // needed to construct `operand` is checked by its child interval
        // nodes, so this node intentionally has no definedness reference.
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
    /// Re-express an interval-justified affine machine term as a checked
    /// proposition.  The source affine node supplies the algebraic fact;
    /// the interval node proves that every decomposed machine operation is
    /// defined (or has bounded endpoints).
    AffineConclusion {
        source: usize,
        evidence: usize,
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
        let mut terms = TermArena::default();
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
                    if source.relation == SignedArithmeticRelation::Disequal
                        && coefficient.is_zero()
                    {
                        return Err(SignedArithmeticCheckError::InvalidCoefficient(node_index));
                    }
                    if !charge_scale_work(source, coefficient) {
                        return Err(SignedArithmeticCheckError::Overflow(node_index));
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
                    if left.relation == SignedArithmeticRelation::Disequal {
                        return Err(SignedArithmeticCheckError::InvalidRelation(node_index));
                    }
                    if !charge_claim_work(left)
                        || !charge_claim_work(right)
                        || !charge_claim_pair_work(left, right)
                    {
                        return Err(SignedArithmeticCheckError::Overflow(node_index));
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
                    if !charge_claim_work(source) {
                        return Err(SignedArithmeticCheckError::Overflow(node_index));
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
                    if !charge_claim_pair_work(lower, upper) {
                        return Err(SignedArithmeticCheckError::Overflow(node_index));
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
                    let atom = SignedArithmeticAtom::from_term(term)
                        .ok_or(SignedArithmeticCheckError::InvalidOperator(node_index))?;
                    if !atom.is_opaque_root() {
                        return Err(SignedArithmeticCheckError::InvalidOperator(node_index));
                    }
                    let (expected_lower, expected_upper) = affine_term_bounds(source, &atom)
                        .ok_or(SignedArithmeticCheckError::InvalidEndpoint(node_index))?;
                    if (*lower, *upper) != (expected_lower, expected_upper) {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    let term_reference = terms.atom_key(atom);
                    CheckedValue::Interval {
                        value: SignedArithmeticInterval {
                            carrier: SignedArithmeticCarrier::SignedInt32,
                            lower: *lower,
                            upper: *upper,
                        },
                        term: term_reference,
                    }
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
                    let atom = SignedArithmeticAtom::from_term(term)
                        .ok_or(SignedArithmeticCheckError::InvalidOperator(node_index))?;
                    let valid_atom =
                        atom.is_opaque_root() && (*lower, *upper) == (SIGNED_MIN, SIGNED_MAX);
                    let valid_constant = term
                        .as_const()
                        .map(|value| i64::from(value as i32))
                        .is_some_and(|value| (*lower, *upper) == (value, value));
                    if !valid_atom && !valid_constant {
                        return Err(SignedArithmeticCheckError::InvalidOperator(node_index));
                    }
                    let term_reference = terms.atom_key(atom);
                    CheckedValue::Interval {
                        value: SignedArithmeticInterval {
                            carrier: *carrier,
                            lower: *lower,
                            upper: *upper,
                        },
                        term: term_reference,
                    }
                }
                SignedArithmeticNode::IntervalIntersect {
                    left,
                    right,
                    result,
                } => {
                    let (left, left_term) = interval_at(&checked, *left)?;
                    let (right, right_term) = interval_at(&checked, *right)?;
                    if left.carrier != right.carrier || !terms.equivalent(left_term, right_term) {
                        return Err(SignedArithmeticCheckError::InvalidRelation(node_index));
                    }
                    let expected = SignedArithmeticInterval {
                        carrier: left.carrier,
                        lower: left.lower.max(right.lower),
                        upper: left.upper.min(right.upper),
                    };
                    if expected.lower > expected.upper {
                        return Err(SignedArithmeticCheckError::DoesNotFollow);
                    }
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval {
                        value: expected,
                        term: left_term,
                    }
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
                    let (left, left_term) = interval_at(&checked, *left)?;
                    let (right, right_term) = interval_at(&checked, *right)?;
                    let term = terms.binary(CheckedBinaryOperator::Add, left_term, right_term);
                    require_defined(&checked, &terms, *defined, term, node_index)?;
                    let expected = interval_add(left, right, node_index, true)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval {
                        value: expected,
                        term,
                    }
                }
                SignedArithmeticNode::IntervalAddBounded {
                    left,
                    right,
                    result,
                } => {
                    let (left, left_term) = interval_at(&checked, *left)?;
                    let (right, right_term) = interval_at(&checked, *right)?;
                    let term = terms.binary(CheckedBinaryOperator::Add, left_term, right_term);
                    let expected = interval_add(left, right, node_index, false)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval {
                        value: expected,
                        term,
                    }
                }
                SignedArithmeticNode::IntervalSubtract {
                    left,
                    right,
                    defined,
                    result,
                } => {
                    let (left, left_term) = interval_at(&checked, *left)?;
                    let (right, right_term) = interval_at(&checked, *right)?;
                    let term = terms.binary(CheckedBinaryOperator::Subtract, left_term, right_term);
                    require_defined(&checked, &terms, *defined, term, node_index)?;
                    let expected = interval_subtract(left, right, node_index)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval {
                        value: expected,
                        term,
                    }
                }
                SignedArithmeticNode::IntervalMultiply {
                    left,
                    right,
                    defined,
                    result,
                } => {
                    let (left, left_term) = interval_at(&checked, *left)?;
                    let (right, right_term) = interval_at(&checked, *right)?;
                    let term = terms.binary(CheckedBinaryOperator::Multiply, left_term, right_term);
                    require_defined(&checked, &terms, *defined, term, node_index)?;
                    let expected = interval_multiply(left, right, node_index)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval {
                        value: expected,
                        term,
                    }
                }
                SignedArithmeticNode::IntervalRemainder {
                    operand,
                    divisor,
                    defined,
                    result,
                } => {
                    let (operand, operand_term) = interval_at(&checked, *operand)?;
                    let divisor_term = terms
                        .atom(Bitvector32Term::Constant(*divisor as u32))
                        .ok_or(SignedArithmeticCheckError::InvalidOperator(node_index))?;
                    let term =
                        terms.binary(CheckedBinaryOperator::Remainder, operand_term, divisor_term);
                    require_defined(&checked, &terms, *defined, term, node_index)?;
                    let expected = interval_remainder(operand, *divisor, node_index)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval {
                        value: expected,
                        term,
                    }
                }
                SignedArithmeticNode::IntervalShiftLeft {
                    operand,
                    shift,
                    defined,
                    result,
                } => {
                    let (operand, operand_term) = interval_at(&checked, *operand)?;
                    let shift_term = terms
                        .atom(Bitvector32Term::Constant(*shift as u32))
                        .ok_or(SignedArithmeticCheckError::InvalidOperator(node_index))?;
                    let term =
                        terms.binary(CheckedBinaryOperator::ShiftLeft, operand_term, shift_term);
                    require_defined(&checked, &terms, *defined, term, node_index)?;
                    if !(0..32).contains(shift) || operand.lower < 0 {
                        return Err(SignedArithmeticCheckError::InvalidOperator(node_index));
                    }
                    let factor = 1_i128 << (*shift as u32);
                    let lower = i128::from(operand.lower) * factor;
                    let upper = i128::from(operand.upper) * factor;
                    let expected = interval_checked(lower, upper, node_index)?;
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval {
                        value: expected,
                        term,
                    }
                }
                SignedArithmeticNode::IntervalArithmeticShiftRight {
                    operand,
                    shift,
                    result,
                } => {
                    let (operand, operand_term) = interval_at(&checked, *operand)?;
                    if !(0..32).contains(shift) {
                        return Err(SignedArithmeticCheckError::InvalidOperator(node_index));
                    }
                    let shift_term = terms
                        .atom(Bitvector32Term::Constant(*shift as u32))
                        .ok_or(SignedArithmeticCheckError::InvalidOperator(node_index))?;
                    let term = terms.binary(
                        CheckedBinaryOperator::ArithmeticShiftRight,
                        operand_term,
                        shift_term,
                    );
                    let expected = SignedArithmeticInterval {
                        carrier: operand.carrier,
                        lower: i64::from((operand.lower as i32) >> shift),
                        upper: i64::from((operand.upper as i32) >> shift),
                    };
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval {
                        value: expected,
                        term,
                    }
                }
                SignedArithmeticNode::IntervalBitwiseAnd {
                    operand,
                    mask,
                    result,
                } => {
                    let (operand, operand_term) = interval_at(&checked, *operand)?;
                    if *mask > i32::MAX as u32 {
                        return Err(SignedArithmeticCheckError::InvalidOperator(node_index));
                    }
                    let mask_term = terms
                        .atom(Bitvector32Term::Constant(*mask))
                        .ok_or(SignedArithmeticCheckError::InvalidOperator(node_index))?;
                    let term =
                        terms.binary(CheckedBinaryOperator::BitwiseAnd, operand_term, mask_term);
                    let expected = SignedArithmeticInterval {
                        carrier: operand.carrier,
                        lower: 0,
                        upper: i64::from(*mask as i32),
                    };
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval {
                        value: expected,
                        term,
                    }
                }
                SignedArithmeticNode::IntervalSignBitFlip { operand, result } => {
                    let (operand, operand_term) = interval_at(&checked, *operand)?;
                    let sign_bit = terms
                        .atom(Bitvector32Term::Constant(0x8000_0000))
                        .ok_or(SignedArithmeticCheckError::InvalidOperator(node_index))?;
                    let term =
                        terms.binary(CheckedBinaryOperator::BitwiseXor, operand_term, sign_bit);
                    let (lower, upper) = if operand.lower >= 0 {
                        (operand.lower + SIGNED_MIN, operand.upper + SIGNED_MIN)
                    } else if operand.upper < 0 {
                        (operand.lower - SIGNED_MIN, operand.upper - SIGNED_MIN)
                    } else {
                        (SIGNED_MIN, SIGNED_MAX)
                    };
                    let expected = SignedArithmeticInterval {
                        carrier: operand.carrier,
                        lower,
                        upper,
                    };
                    check_interval_result(&expected, result, node_index)?;
                    CheckedValue::Interval {
                        value: expected,
                        term,
                    }
                }
                SignedArithmeticNode::IntervalCompare {
                    left,
                    right,
                    comparison,
                    result,
                } => {
                    let (left, left_term) = interval_at(&checked, *left)?;
                    let (right, right_term) = interval_at(&checked, *right)?;
                    if left.carrier != SignedArithmeticCarrier::SignedInt32
                        || right.carrier != SignedArithmeticCarrier::SignedInt32
                        || left.carrier != right.carrier
                    {
                        return Err(SignedArithmeticCheckError::UnsupportedCarrier);
                    }
                    if !comparison_proposition_matches(
                        result,
                        &terms,
                        left_term,
                        right_term,
                        *comparison,
                    ) || !interval_proves(left, right, *comparison)
                    {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    CheckedValue::Proposition(result.clone())
                }
                SignedArithmeticNode::AffineConclusion {
                    source,
                    evidence,
                    result,
                } => {
                    let source = affine_at(&checked, *source)?;
                    let _ = interval_at(&checked, *evidence)?;
                    let expected = affine_claim_from_interval_evidence(
                        &self.nodes,
                        &checked,
                        &mut terms,
                        *evidence,
                        result,
                    )
                    .ok_or(SignedArithmeticCheckError::NodeResultMismatch(node_index))?;
                    if !charge_claim_work(&expected) {
                        return Err(SignedArithmeticCheckError::Overflow(node_index));
                    }
                    if !same_int32_claim(&expected, source) {
                        return Err(SignedArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    CheckedValue::Proposition(result.clone())
                }
            };
            if let CheckedValue::Affine(claim) = &value
                && !charge_claim_work(claim)
            {
                return Err(SignedArithmeticCheckError::Overflow(node_index));
            }
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
    charge_claim_pair_work(expected, actual)
        && expected == actual
        && expected.carrier == SignedArithmeticCarrier::SignedInt32
}

fn btree_log_work(entries: usize) -> usize {
    (usize::BITS - entries.saturating_add(1).leading_zeros()) as usize
}

fn affine_map_work(map: &BTreeMap<SignedArithmeticAtom, BigInt>) -> usize {
    let logarithmic = btree_log_work(map.len()).max(1);
    map.iter().fold(1usize, |units, (atom, coefficient)| {
        units.saturating_add(
            signed_atom_work(atom)
                .saturating_add(coefficient.bits() as usize + 1)
                .saturating_mul(logarithmic),
        )
    })
}

fn charge_affine_map_work(map: &BTreeMap<SignedArithmeticAtom, BigInt>) -> bool {
    !crate::instrumentation::deadline_exceeded_with_work(affine_map_work(map))
}

fn charge_affine_map_update_work(
    map: &BTreeMap<SignedArithmeticAtom, BigInt>,
    atom: &SignedArithmeticAtom,
    coefficient: &BigInt,
) -> bool {
    let units = signed_atom_work(atom)
        .saturating_add(coefficient.bits() as usize + 1)
        .saturating_mul(btree_log_work(map.len()).max(1))
        .saturating_mul(3);
    !crate::instrumentation::deadline_exceeded_with_work(units)
}

fn charge_atom_pair_work(left: &SignedArithmeticAtom, right: &SignedArithmeticAtom) -> bool {
    let units = left.work().saturating_add(right.work()).saturating_add(1);
    !crate::instrumentation::deadline_exceeded_with_work(units)
}

fn charge_bigint_binary_work(left: &BigInt, right: &BigInt) -> bool {
    let units = (left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1);
    !crate::instrumentation::deadline_exceeded_with_work(units.max(1))
}

fn charge_term_work(root: &Bitvector32Term) -> bool {
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        let units = match term {
            Bitvector32Term::Constant(value) => (u32::BITS - value.leading_zeros()) as usize + 2,
            Bitvector32Term::Variable(_) => 2,
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                name.len().saturating_add(arguments.len()).saturating_add(2)
            }
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::Remainder(left, right)
            | Bitvector32Term::ShiftLeft(left, right)
            | Bitvector32Term::ArithmeticShiftRight(left, right)
            | Bitvector32Term::LogicalShiftRight(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right)
            | Bitvector32Term::BitwiseXor(left, right) => {
                pending.push(left);
                pending.push(right);
                3
            }
            Bitvector32Term::BitwiseNot(operand) => {
                pending.push(operand);
                2
            }
            _ => 1,
        };
        if crate::instrumentation::deadline_exceeded_with_work(units) {
            return false;
        }
    }
    true
}

fn canonical_term_budgeted(term: &Bitvector32Term) -> Option<Bitvector32Term> {
    if !charge_term_work(term) {
        return None;
    }
    let canonical = crate::kernel::eval::canonical_term(term);
    if !charge_term_work(&canonical) {
        return None;
    }
    Some(canonical)
}

fn charge_claim_work(claim: &SignedArithmeticClaim) -> bool {
    let units = (claim.constant.bits().saturating_add(1) as usize)
        .saturating_add(affine_map_work(&claim.terms));
    !crate::instrumentation::deadline_exceeded_with_work(units.max(1))
}

pub(crate) fn charge_claim_pair_work(
    left: &SignedArithmeticClaim,
    right: &SignedArithmeticClaim,
) -> bool {
    let units = (left.constant.bits().saturating_add(right.constant.bits()) as usize)
        .saturating_add(2)
        .saturating_add(affine_map_work(&left.terms))
        .saturating_add(affine_map_work(&right.terms));
    !crate::instrumentation::deadline_exceeded_with_work(units.max(1))
}

fn charge_scale_work(claim: &SignedArithmeticClaim, coefficient: &BigInt) -> bool {
    if !charge_affine_map_work(&claim.terms) {
        return false;
    }
    for (term, value) in claim
        .terms
        .iter()
        .map(|(term, value)| (Some(term), value))
        .chain(std::iter::once((None, &claim.constant)))
    {
        let atom_units = term.map_or(0, signed_atom_work);
        let units = atom_units.saturating_add(
            (value.bits() as usize + 1).saturating_mul(coefficient.bits() as usize + 1),
        );
        if crate::instrumentation::deadline_exceeded_with_work(units) {
            return false;
        }
    }
    true
}

fn signed_atom_work(atom: &SignedArithmeticAtom) -> usize {
    atom.tokens.iter().fold(0usize, |units, token| {
        let token_units = match token {
            SignedArithmeticAtomToken::Constant(value) => {
                (u32::BITS - value.leading_zeros()) as usize + 1
            }
            SignedArithmeticAtomToken::Variable(_) => 1,
            SignedArithmeticAtomToken::PureFunction { name, arity } => {
                name.len().saturating_add(*arity).saturating_add(1)
            }
            SignedArithmeticAtomToken::Binary(_) | SignedArithmeticAtomToken::UnaryNot => 1,
        };
        units.saturating_add(token_units)
    })
}

fn signed_term_work(root: &Bitvector32Term) -> usize {
    let mut units = 0usize;
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        units = units.saturating_add(1);
        match term {
            Bitvector32Term::Constant(value) => {
                units = units.saturating_add((u32::BITS - value.leading_zeros()) as usize + 1);
            }
            Bitvector32Term::Variable(_) => {}
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::Divide(left, right)
            | Bitvector32Term::Remainder(left, right)
            | Bitvector32Term::ShiftLeft(left, right)
            | Bitvector32Term::ArithmeticShiftRight(left, right)
            | Bitvector32Term::LogicalShiftRight(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right)
            | Bitvector32Term::BitwiseXor(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Bitvector32Term::BitwiseNot(operand) => pending.push(operand),
            Bitvector32Term::PureFunctionApplication { name, arguments } => {
                // Function application identity compares the name and every
                // argument. Arguments are restricted to this same safe
                // machine-term fragment, so an iterative walk charges the
                // complete payload without formatting or allocating it.
                units = units.saturating_add(name.len());
                units = units.saturating_add(arguments.len());
                pending.extend(arguments.iter());
            }
            _ => {
                // Unsupported opaque payloads are rejected before they can
                // enter a checked affine claim; keep this branch bounded for
                // defensive direct callers.
            }
        }
    }
    units
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
) -> Result<(&SignedArithmeticInterval, usize), SignedArithmeticCheckError> {
    match checked.get(index) {
        Some(CheckedValue::Interval { value, term }) => Ok((value, *term)),
        Some(_) => Err(SignedArithmeticCheckError::InvalidRelation(index)),
        None => Err(SignedArithmeticCheckError::InvalidNodeReference(index)),
    }
}

fn require_defined(
    checked: &[CheckedValue],
    terms: &TermArena,
    index: usize,
    term: usize,
    node: usize,
) -> Result<(), SignedArithmeticCheckError> {
    match checked.get(index) {
        Some(CheckedValue::Defined {
            carrier,
            term: actual,
        }) if *carrier == SignedArithmeticCarrier::SignedInt32
            && terms.equivalent_explicit(term, actual) =>
        {
            Ok(())
        }
        Some(_) => Err(SignedArithmeticCheckError::InvalidDefinedness(node)),
        None => Err(SignedArithmeticCheckError::InvalidNodeReference(index)),
    }
}

pub(crate) fn scale_claim(
    source: &SignedArithmeticClaim,
    coefficient: &BigInt,
) -> Option<SignedArithmeticClaim> {
    if !charge_affine_map_work(&source.terms) {
        return None;
    }
    let terms = source
        .terms
        .iter()
        .map(|(term, value)| {
            if !charge_affine_map_update_work(&source.terms, term, value)
                || !charge_bigint_binary_work(value, coefficient)
            {
                return None;
            }
            Some((term.clone(), value * coefficient))
        })
        .collect::<Option<BTreeMap<_, _>>>()?;
    if !charge_bigint_binary_work(&source.constant, coefficient) {
        return None;
    }
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
    if !charge_affine_map_work(&left.terms) || !charge_affine_map_work(&right.terms) {
        return None;
    }
    if !charge_bigint_binary_work(&left.constant, &right.constant) {
        return None;
    }
    let mut terms = left.terms.clone();
    for (term, coefficient) in &right.terms {
        if !charge_affine_map_update_work(&terms, term, coefficient) {
            return None;
        }
        let previous = terms.get(term).cloned().unwrap_or_default();
        if !charge_bigint_binary_work(&previous, coefficient) {
            return None;
        }
        let value = previous + coefficient;
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
    if !charge_affine_map_work(&lower.terms) || !charge_affine_map_work(&upper.terms) {
        return None;
    }
    if !charge_bigint_binary_work(&upper.constant, &BigInt::one())
        || !charge_bigint_binary_work(&lower.constant, &upper.constant)
    {
        return None;
    }
    let opposite = upper
        .terms
        .iter()
        .map(|(term, coefficient)| (term.clone(), -coefficient))
        .collect::<BTreeMap<_, _>>();
    let opposite_constant = -&upper.constant;
    if lower.terms != opposite || lower.constant != opposite_constant {
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

fn affine_term_bounds(
    claim: &SignedArithmeticClaim,
    atom: &SignedArithmeticAtom,
) -> Option<(i64, i64)> {
    if claim.terms.len() != 1 || claim.relation != SignedArithmeticRelation::LessEqual {
        return None;
    }
    let (claim_atom, coefficient) = claim.terms.iter().next()?;
    if !charge_atom_pair_work(claim_atom, atom) || claim_atom != atom {
        return None;
    }
    let minimum = BigInt::from(SIGNED_MIN);
    let maximum = BigInt::from(SIGNED_MAX);
    match coefficient.to_i64()? {
        1 => {
            let upper = -&claim.constant;
            if upper < minimum {
                return None;
            }
            Some((SIGNED_MIN, upper.min(maximum).to_i64()?))
        }
        -1 => {
            let lower = &claim.constant;
            if lower > &maximum {
                return None;
            }
            Some((lower.max(&minimum).to_i64()?, SIGNED_MAX))
        }
        _ => None,
    }
}

fn affine_claim_from_interval_evidence(
    nodes: &[SignedArithmeticNode],
    checked: &[CheckedValue],
    terms: &mut TermArena,
    evidence: usize,
    proposition: &Proposition,
) -> Option<SignedArithmeticClaim> {
    let (evidence_term, evidence_affine) = interval_affine_evidence(nodes, checked, evidence)?;
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !value),
            _ => return None,
        },
        _ => return None,
    };
    let (relation, left, right, strict) = match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, left, right, true)
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, left, right, false)
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, right, left, true)
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, right, left, false)
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, right, left, false)
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, right, left, true)
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, left, right, false)
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, left, right, true)
        }
        (ConditionTerm::Bitvector32Equal(left, right), true) => {
            let (terms, constant) = affine_difference_from_evidence(
                left,
                right,
                terms,
                &evidence_term,
                &evidence_affine,
            )?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Equal,
                terms,
                constant,
            });
        }
        (ConditionTerm::Bitvector32Equal(left, right), false) => {
            let (terms, constant) = affine_difference_from_evidence(
                left,
                right,
                terms,
                &evidence_term,
                &evidence_affine,
            )?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Disequal,
                terms,
                constant,
            });
        }
        _ => return None,
    };
    let (terms, mut constant) =
        affine_difference_from_evidence(left, right, terms, &evidence_term, &evidence_affine)?;
    if strict {
        if !charge_bigint_binary_work(&constant, &BigInt::one()) {
            return None;
        }
        constant += 1;
    }
    Some(SignedArithmeticClaim {
        carrier: SignedArithmeticCarrier::SignedInt32,
        relation,
        terms,
        constant,
    })
}

fn affine_difference_from_evidence(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    terms: &mut TermArena,
    evidence_term: &usize,
    evidence_affine: &(BTreeMap<SignedArithmeticAtom, BigInt>, BigInt),
) -> Option<(BTreeMap<SignedArithmeticAtom, BigInt>, BigInt)> {
    let difference = |term: &Bitvector32Term, coefficient: i8| {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        if terms.equivalent_explicit(*evidence_term, term) {
            let multiplier = BigInt::from(coefficient);
            let mut result = BTreeMap::new();
            for (atom, value) in &evidence_affine.0 {
                if crate::instrumentation::deadline_exceeded_with_work(
                    signed_atom_work(atom)
                        .saturating_add(value.bits() as usize + 1)
                        .saturating_add(multiplier.bits() as usize + 1),
                ) {
                    return None;
                }
                if !charge_affine_map_update_work(&result, atom, value) {
                    return None;
                }
                if !charge_bigint_binary_work(value, &multiplier) {
                    return None;
                }
                result.insert(atom.clone(), value * &multiplier);
            }
            if !charge_bigint_binary_work(&evidence_affine.1, &multiplier) {
                return None;
            }
            return Some((result, evidence_affine.1.clone() * multiplier));
        }
        if contains_affine_machine_operation(term) {
            return None;
        }
        affine_leaf(term).map(|(mut result, constant)| {
            if coefficient == -1 {
                for value in result.values_mut() {
                    *value = -value.clone();
                }
                (result, -constant)
            } else {
                (result, constant)
            }
        })
    };
    let (left_terms, left_constant) = difference(left, 1)?;
    let (right_terms, right_constant) = difference(right, -1)?;
    let mut result = left_terms;
    for (atom, coefficient) in right_terms {
        if !charge_affine_map_update_work(&result, &atom, &coefficient) {
            return None;
        }
        let previous = result.get(&atom).cloned().unwrap_or_default();
        if !charge_bigint_binary_work(&previous, &coefficient) {
            return None;
        }
        let updated = previous + coefficient;
        if updated.is_zero() {
            result.remove(&atom);
        } else {
            result.insert(atom, updated);
        }
    }
    if !charge_bigint_binary_work(&left_constant, &right_constant) {
        return None;
    }
    Some((result, left_constant + right_constant))
}

fn interval_affine_evidence(
    nodes: &[SignedArithmeticNode],
    checked: &[CheckedValue],
    _evidence: usize,
) -> Option<(usize, (BTreeMap<SignedArithmeticAtom, BigInt>, BigInt))> {
    enum Task {
        Visit(usize),
        Add,
        Subtract,
    }
    let mut tasks = vec![Task::Visit(_evidence)];
    let mut results = Vec::new();
    while let Some(task) = tasks.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        match task {
            Task::Visit(index) => {
                let node = nodes.get(index)?;
                match node {
                    SignedArithmeticNode::IntervalAtom { term, .. }
                    | SignedArithmeticNode::IntervalFromAffine { term, .. } => {
                        let (affine_terms, constant) = affine_leaf(term)?;
                        let term_reference = match checked.get(index)? {
                            CheckedValue::Interval { term, .. } => *term,
                            _ => return None,
                        };
                        results.push((term_reference, (affine_terms, constant)));
                    }
                    SignedArithmeticNode::IntervalIntersect { left, .. } => {
                        tasks.push(Task::Visit(*left));
                    }
                    SignedArithmeticNode::IntervalAdd { left, right, .. }
                    | SignedArithmeticNode::IntervalAddBounded { left, right, .. } => {
                        tasks.push(Task::Add);
                        tasks.push(Task::Visit(*right));
                        tasks.push(Task::Visit(*left));
                    }
                    SignedArithmeticNode::IntervalSubtract { left, right, .. } => {
                        tasks.push(Task::Subtract);
                        tasks.push(Task::Visit(*right));
                        tasks.push(Task::Visit(*left));
                    }
                    _ => return None,
                }
            }
            Task::Add | Task::Subtract => {
                let right = results.pop()?;
                let left = results.pop()?;
                let mut affine_terms: BTreeMap<SignedArithmeticAtom, BigInt> = left.1.0;
                let add = matches!(task, Task::Add);
                for (atom, coefficient) in right.1.0 {
                    if crate::instrumentation::deadline_exceeded_with_work(1) {
                        return None;
                    }
                    let contribution = if add { coefficient } else { -coefficient };
                    if crate::instrumentation::deadline_exceeded_with_work(
                        signed_atom_work(&atom).saturating_add(contribution.bits() as usize + 1),
                    ) {
                        return None;
                    }
                    if !charge_affine_map_update_work(&affine_terms, &atom, &contribution) {
                        return None;
                    }
                    let previous = affine_terms.get(&atom).cloned().unwrap_or_default();
                    if !charge_bigint_binary_work(&previous, &contribution) {
                        return None;
                    }
                    let updated: BigInt = previous + contribution;
                    if updated.is_zero() {
                        affine_terms.remove(&atom);
                    } else {
                        affine_terms.insert(atom, updated);
                    }
                }
                if !charge_bigint_binary_work(&left.1.1, &right.1.1) {
                    return None;
                }
                let constant = if add {
                    left.1.1 + right.1.1
                } else {
                    left.1.1 - right.1.1
                };
                let term_reference = match checked.get(_evidence) {
                    Some(CheckedValue::Interval { term, .. }) => *term,
                    _ => 0,
                };
                results.push((term_reference, (affine_terms, constant)));
            }
        }
    }
    let (term_reference, affine) = results.pop()?;
    if !results.is_empty() {
        return None;
    }
    Some((term_reference, affine))
}

fn affine_leaf(term: &Bitvector32Term) -> Option<(BTreeMap<SignedArithmeticAtom, BigInt>, BigInt)> {
    if let Some(value) = term.as_const().map(|value| i64::from(value as i32)) {
        return Some((BTreeMap::new(), BigInt::from(value)));
    }
    let canonical = canonical_term_budgeted(term)?;
    let atom = SignedArithmeticAtom::from_term(&canonical)?;
    if crate::instrumentation::deadline_exceeded_with_work(atom.work()) {
        return None;
    }
    Some((BTreeMap::from([(atom, BigInt::one())]), BigInt::zero()))
}

fn contains_affine_machine_operation(root: &Bitvector32Term) -> bool {
    matches!(
        root,
        Bitvector32Term::Add(_, _) | Bitvector32Term::Subtract(_, _)
    )
}

fn is_opaque_atom(term: &Bitvector32Term) -> bool {
    SignedArithmeticAtom::from_term(term).is_some_and(|atom| atom.is_opaque_root())
}

fn interval_checked(
    lower: i128,
    upper: i128,
    node: usize,
) -> Result<SignedArithmeticInterval, SignedArithmeticCheckError> {
    if lower < i128::from(SIGNED_MIN) || upper > i128::from(SIGNED_MAX) || lower > upper {
        return Err(SignedArithmeticCheckError::Overflow(node));
    }
    Ok(SignedArithmeticInterval {
        carrier: SignedArithmeticCarrier::SignedInt32,
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
    node: usize,
    has_exact_definedness: bool,
) -> Result<SignedArithmeticInterval, SignedArithmeticCheckError> {
    let lower = i128::from(left.lower) + i128::from(right.lower);
    let upper = i128::from(left.upper) + i128::from(right.upper);
    if has_exact_definedness {
        interval_checked(
            lower.max(i128::from(SIGNED_MIN)),
            upper.min(i128::from(SIGNED_MAX)),
            node,
        )
    } else {
        interval_checked(lower, upper, node)
    }
}

fn interval_subtract(
    left: &SignedArithmeticInterval,
    right: &SignedArithmeticInterval,
    node: usize,
) -> Result<SignedArithmeticInterval, SignedArithmeticCheckError> {
    interval_checked(
        i128::from(left.lower) - i128::from(right.upper),
        i128::from(left.upper) - i128::from(right.lower),
        node,
    )
}

fn interval_multiply(
    left: &SignedArithmeticInterval,
    right: &SignedArithmeticInterval,
    node: usize,
) -> Result<SignedArithmeticInterval, SignedArithmeticCheckError> {
    let values = [
        i128::from(left.lower) * i128::from(right.lower),
        i128::from(left.lower) * i128::from(right.upper),
        i128::from(left.upper) * i128::from(right.lower),
        i128::from(left.upper) * i128::from(right.upper),
    ];
    interval_checked(
        *values.iter().min().unwrap(),
        *values.iter().max().unwrap(),
        node,
    )
}

fn interval_remainder(
    operand: &SignedArithmeticInterval,
    divisor: i32,
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
    interval_checked(i128::from(lower), i128::from(upper), node)
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
        ) => signed_arithmetic_terms_equal(left, a) && signed_arithmetic_terms_equal(right, b),
        (
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right),
            Bitvector32Term::ShiftLeft(a, b),
        ) => signed_arithmetic_terms_equal(left, a) && signed_arithmetic_terms_equal(right, b),
        (
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right),
            Bitvector32Term::Remainder(a, b),
        ) => signed_arithmetic_terms_equal(left, a) && signed_arithmetic_terms_equal(right, b),
        _ => false,
    }
}

fn signed_arithmetic_terms_equal(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    match (
        SignedArithmeticAtom::from_term(left),
        SignedArithmeticAtom::from_term(right),
    ) {
        (Some(left), Some(right)) => charge_atom_pair_work(&left, &right) && left == right,
        _ => false,
    }
}

fn comparison_proposition_matches(
    proposition: &Proposition,
    terms: &TermArena,
    left: usize,
    right: usize,
    comparison: SignedArithmeticComparison,
) -> bool {
    let Proposition::ConditionIs(condition, value) = proposition else {
        return false;
    };
    let (expected_value, expected_left, expected_right) = match (comparison, condition) {
        (
            SignedArithmeticComparison::LessThan,
            ConditionTerm::Bitvector32SignedLessThan(left, right),
        )
        | (
            SignedArithmeticComparison::LessEqual,
            ConditionTerm::Bitvector32SignedLessEqual(left, right),
        )
        | (SignedArithmeticComparison::Equal, ConditionTerm::Bitvector32Equal(left, right)) => {
            (true, left.as_ref(), right.as_ref())
        }
        (SignedArithmeticComparison::Disequal, ConditionTerm::Bitvector32Equal(left, right)) => {
            (false, left.as_ref(), right.as_ref())
        }
        _ => return false,
    };
    *value == expected_value
        && terms.equivalent_explicit(left, expected_left)
        && terms.equivalent_explicit(right, expected_right)
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
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, left, right, true)
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, left, right, false)
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, right, left, true)
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), true) => {
            (SignedArithmeticRelation::LessEqual, right, left, false)
        }
        (ConditionTerm::Bitvector32SignedLessThan(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, right, left, false)
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, right, left, true)
        }
        (ConditionTerm::Bitvector32SignedGreaterThan(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, left, right, false)
        }
        (ConditionTerm::Bitvector32SignedGreaterEqual(left, right), false) => {
            (SignedArithmeticRelation::LessEqual, left, right, true)
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
        if !charge_bigint_binary_work(&constant, &BigInt::one()) {
            return None;
        }
        constant += 1;
    }
    Some(SignedArithmeticClaim {
        carrier: SignedArithmeticCarrier::SignedInt32,
        relation,
        terms,
        constant,
    })
}

pub(crate) fn signed_arithmetic_claim(proposition: &Proposition) -> Option<SignedArithmeticClaim> {
    affine_claim(proposition)
}

fn affine_difference(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(BTreeMap<SignedArithmeticAtom, BigInt>, BigInt)> {
    let mut terms: BTreeMap<SignedArithmeticAtom, BigInt> = BTreeMap::new();
    let mut constant = BigInt::zero();
    let mut pending = vec![(left, BigInt::one()), (right, -BigInt::one())];
    while let Some((term, coefficient)) = pending.pop() {
        match term {
            Bitvector32Term::Constant(value) => {
                let value = BigInt::from(*value as i32);
                if !charge_bigint_binary_work(&coefficient, &value) {
                    return None;
                }
                let product = coefficient * &value;
                if !charge_bigint_binary_work(&constant, &product) {
                    return None;
                }
                constant += product;
            }
            term => {
                let atom = canonical_term_budgeted(term)?;
                if crate::instrumentation::deadline_exceeded_with_work(
                    coefficient.bits() as usize + 1,
                ) {
                    return None;
                }
                let key = SignedArithmeticAtom::from_term(&atom)?;
                if !charge_affine_map_update_work(&terms, &key, &coefficient) {
                    return None;
                }
                let previous = terms.get(&key).cloned().unwrap_or_default();
                if !charge_bigint_binary_work(&previous, &coefficient) {
                    return None;
                }
                let updated = previous + coefficient;
                if updated.is_zero() {
                    terms.remove(&key);
                } else {
                    terms.insert(key, updated);
                }
            }
        }
    }
    Some((terms, constant))
}

fn conclusion_matches(value: &CheckedValue, goal: &Proposition) -> bool {
    match value {
        CheckedValue::Affine(claim) => affine_claim(goal)
            .is_some_and(|expected| charge_claim_pair_work(&expected, claim) && expected == *claim),
        CheckedValue::Proposition(proposition) => propositions_match(proposition, goal),
        CheckedValue::Interval { .. } | CheckedValue::Defined { .. } => false,
    }
}

fn propositions_match(left: &Proposition, right: &Proposition) -> bool {
    let Some(left_claim) = affine_claim(left) else {
        return false;
    };
    let Some(right_claim) = affine_claim(right) else {
        return false;
    };
    charge_claim_pair_work(&left_claim, &right_claim) && left_claim == right_claim
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{Pointer, Variable};

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

    fn equal(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        prop(ConditionTerm::Bitvector32Equal(
            Box::new(left),
            Box::new(right),
        ))
    }

    #[test]
    fn affine_claims_use_one_zero_centered_constant_convention() {
        let premise = equal(x(), Bitvector32Term::Constant(5));
        let good_goal = le(x(), Bitvector32Term::Constant(5));
        let bad_goal = le(x(), Bitvector32Term::Constant((-5_i32) as u32));
        let equality_claim = claim(&premise);
        assert_eq!(equality_claim.constant, BigInt::from(-5));
        let certificate = SignedArithmeticCertificate {
            nodes: vec![
                SignedArithmeticNode::Premise {
                    index: 0,
                    result: equality_claim,
                },
                SignedArithmeticNode::EqualityToLessEqual {
                    source: 0,
                    reverse: false,
                    result: claim(&good_goal),
                },
            ],
            conclusion: 1,
        };
        certificate
            .check(&good_goal, std::slice::from_ref(&premise))
            .unwrap();
        assert_eq!(
            certificate.check(&bad_goal, std::slice::from_ref(&premise)),
            Err(SignedArithmeticCheckError::DoesNotFollow)
        );
    }

    #[test]
    fn affine_premises_do_not_decompose_undefined_machine_operations_or_lp64_addresses() {
        let operation = Bitvector32Term::Add(Box::new(x()), Box::new(Bitvector32Term::Constant(1)));
        let operation_premise = le(operation, Bitvector32Term::Constant(0));
        let unrelated_goal = le(x(), Bitvector32Term::Constant(0));
        let operation_certificate = SignedArithmeticCertificate {
            nodes: vec![SignedArithmeticNode::Premise {
                index: 0,
                result: claim(&operation_premise),
            }],
            conclusion: 0,
        };
        assert_eq!(
            operation_certificate.check(&unrelated_goal, std::slice::from_ref(&operation_premise),),
            Err(SignedArithmeticCheckError::DoesNotFollow)
        );

        let pointer = Bitvector32Term::PointerAddress(Box::new(Pointer::symbolic(Variable(3))));
        let pointer_premise = le(pointer.clone(), Bitvector32Term::Constant(0));
        let pointer_certificate = SignedArithmeticCertificate {
            nodes: vec![SignedArithmeticNode::Premise {
                index: 0,
                result: SignedArithmeticClaim {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    relation: SignedArithmeticRelation::LessEqual,
                    terms: BTreeMap::new(),
                    constant: BigInt::zero(),
                },
            }],
            conclusion: 0,
        };
        assert_eq!(
            pointer_certificate.check(&pointer_premise, std::slice::from_ref(&pointer_premise)),
            Err(SignedArithmeticCheckError::UnsupportedPremise(0))
        );
    }

    #[test]
    fn trivial_directions_and_disequality_combinations_are_checked() {
        let true_proposition = prop(ConditionTerm::Constant(true));
        let true_claim = claim(&true_proposition);
        assert_eq!(true_claim.constant, BigInt::zero());
        let true_certificate = SignedArithmeticCertificate {
            nodes: vec![SignedArithmeticNode::Trivial {
                result: true_claim.clone(),
            }],
            conclusion: 0,
        };
        true_certificate.check(&true_proposition, &[]).unwrap();

        let false_proposition = prop(ConditionTerm::Constant(false));
        let false_claim = claim(&false_proposition);
        assert_eq!(false_claim.constant, BigInt::one());
        let false_certificate = SignedArithmeticCertificate {
            nodes: vec![SignedArithmeticNode::Trivial {
                result: false_claim,
            }],
            conclusion: 0,
        };
        assert_eq!(
            false_certificate.check(&false_proposition, &[]),
            Err(SignedArithmeticCheckError::NodeResultMismatch(0))
        );

        let disequality = Proposition::ConditionIs(
            ConditionTerm::Bitvector32Equal(Box::new(x()), Box::new(Bitvector32Term::Constant(5))),
            false,
        );
        let disequality_claim = claim(&disequality);
        let zero_scale = SignedArithmeticCertificate {
            nodes: vec![
                SignedArithmeticNode::Premise {
                    index: 0,
                    result: disequality_claim.clone(),
                },
                SignedArithmeticNode::Scale {
                    source: 0,
                    coefficient: BigInt::zero(),
                    result: scale_claim(&disequality_claim, &BigInt::zero()).unwrap(),
                },
            ],
            conclusion: 1,
        };
        assert_eq!(
            zero_scale.check(&disequality, std::slice::from_ref(&disequality)),
            Err(SignedArithmeticCheckError::InvalidCoefficient(1))
        );

        let added_disequalities = SignedArithmeticCertificate {
            nodes: vec![
                SignedArithmeticNode::Premise {
                    index: 0,
                    result: disequality_claim.clone(),
                },
                SignedArithmeticNode::Premise {
                    index: 0,
                    result: disequality_claim.clone(),
                },
                SignedArithmeticNode::Add {
                    left: 0,
                    right: 1,
                    result: add_claim(&disequality_claim, &disequality_claim).unwrap(),
                },
            ],
            conclusion: 2,
        };
        assert_eq!(
            added_disequalities.check(&disequality, std::slice::from_ref(&disequality)),
            Err(SignedArithmeticCheckError::InvalidRelation(2))
        );
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
        let premises = vec![lower_premise, upper_premise, defined];
        certificate.check(&goal, &premises).unwrap();
    }

    #[test]
    fn bitwise_and_is_total_after_checked_compound_operand() {
        let lower_premise = le(Bitvector32Term::Constant(0), x());
        let upper_premise = le(x(), Bitvector32Term::Constant(100));
        let add_term = Bitvector32Term::Add(Box::new(x()), Box::new(x()));
        let defined =
            Proposition::ConditionIs(ConditionTerm::signed_add_overflows(x(), x()), false);
        let masked_term = Bitvector32Term::BitwiseAnd(
            Box::new(add_term.clone()),
            Box::new(Bitvector32Term::Constant(255)),
        );
        let goal = le(masked_term.clone(), Bitvector32Term::Constant(255));
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
                    left: 3,
                    right: 4,
                    result: SignedArithmeticInterval {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        lower: 0,
                        upper: 100,
                    },
                },
                SignedArithmeticNode::IntervalAdd {
                    left: 5,
                    right: 5,
                    defined: 2,
                    result: SignedArithmeticInterval {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        lower: 0,
                        upper: 200,
                    },
                },
                SignedArithmeticNode::IntervalBitwiseAnd {
                    operand: 6,
                    mask: 255,
                    result: SignedArithmeticInterval {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        lower: 0,
                        upper: 255,
                    },
                },
                SignedArithmeticNode::IntervalAtom {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: Bitvector32Term::Constant(255),
                    lower: 255,
                    upper: 255,
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
        let premises = vec![lower_premise, upper_premise, defined];
        certificate.check(&goal, &premises).unwrap();
    }

    #[test]
    fn bitwise_and_accepts_safe_atoms_and_rejects_undefined_affine_interval_reuse() {
        let masked_term =
            Bitvector32Term::BitwiseAnd(Box::new(x()), Box::new(Bitvector32Term::Constant(255)));
        let goal = le(masked_term.clone(), Bitvector32Term::Constant(255));
        let certificate = SignedArithmeticCertificate {
            nodes: vec![
                SignedArithmeticNode::IntervalAtom {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: x(),
                    lower: SIGNED_MIN,
                    upper: SIGNED_MAX,
                },
                SignedArithmeticNode::IntervalBitwiseAnd {
                    operand: 0,
                    mask: 255,
                    result: SignedArithmeticInterval {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        lower: 0,
                        upper: 255,
                    },
                },
                SignedArithmeticNode::IntervalAtom {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: Bitvector32Term::Constant(255),
                    lower: 255,
                    upper: 255,
                },
                SignedArithmeticNode::IntervalCompare {
                    left: 1,
                    right: 2,
                    comparison: SignedArithmeticComparison::LessEqual,
                    result: goal.clone(),
                },
            ],
            conclusion: 3,
        };
        certificate.check(&goal, &[]).unwrap();

        let compound = Bitvector32Term::Add(Box::new(x()), Box::new(x()));
        let unsafe_reuse = SignedArithmeticCertificate {
            nodes: vec![
                SignedArithmeticNode::Premise {
                    index: 0,
                    result: claim(&le(compound.clone(), Bitvector32Term::Constant(200))),
                },
                SignedArithmeticNode::IntervalFromAffine {
                    source: 0,
                    term: compound.clone(),
                    lower: SIGNED_MIN,
                    upper: 200,
                },
            ],
            conclusion: 1,
        };
        let premise = le(
            Bitvector32Term::Add(Box::new(x()), Box::new(x())),
            Bitvector32Term::Constant(200),
        );
        assert_eq!(
            unsafe_reuse.check(&premise, std::slice::from_ref(&premise)),
            Err(SignedArithmeticCheckError::InvalidOperator(1))
        );

        let masked_compound = Bitvector32Term::BitwiseAnd(
            Box::new(compound.clone()),
            Box::new(Bitvector32Term::Constant(255)),
        );
        let unsafe_operand = SignedArithmeticCertificate {
            nodes: vec![
                SignedArithmeticNode::IntervalAtom {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: compound,
                    lower: SIGNED_MIN,
                    upper: SIGNED_MAX,
                },
                SignedArithmeticNode::IntervalBitwiseAnd {
                    operand: 0,
                    mask: 255,
                    result: SignedArithmeticInterval {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        lower: 0,
                        upper: 255,
                    },
                },
            ],
            conclusion: 1,
        };
        assert_eq!(
            unsafe_operand.check(&le(masked_compound, Bitvector32Term::Constant(255)), &[]),
            Err(SignedArithmeticCheckError::InvalidOperator(0))
        );
    }

    #[test]
    fn repeated_deep_term_equivalence_has_linear_work_scaling() {
        let mut measurements = Vec::new();
        for depth in [8usize, 16, 32, 64] {
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut arena = TermArena::default();
                let mut left = arena.atom(x()).unwrap();
                let mut right = arena.atom(x()).unwrap();
                for index in 0..depth {
                    let left_atom = arena
                        .atom(Bitvector32Term::Variable(Variable(1000 + index as u64)))
                        .unwrap();
                    let right_atom = arena
                        .atom(Bitvector32Term::Variable(Variable(1000 + index as u64)))
                        .unwrap();
                    left = arena.binary(CheckedBinaryOperator::Add, left, left_atom);
                    right = arena.binary(CheckedBinaryOperator::Add, right, right_atom);
                }
                for _ in 0..depth {
                    assert!(arena.equivalent(left, right));
                }
            });
            measurements.push(work);
        }
        for pair in measurements.windows(2) {
            assert!(
                pair[1] <= 3 * pair[0] + 8,
                "memoized deep equivalence should scale linearly: {measurements:?}"
            );
        }
    }

    #[test]
    fn shared_subgraph_equivalence_is_cached_across_distinct_roots() {
        let mut measurements = Vec::new();
        for size in [8usize, 16, 32, 64] {
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                let mut arena = TermArena::default();
                let mut left_shared = arena.atom(x()).unwrap();
                let mut right_shared = arena.atom(x()).unwrap();
                for index in 0..size {
                    let left_atom = arena
                        .atom(Bitvector32Term::Variable(Variable(2000 + index as u64)))
                        .unwrap();
                    let right_atom = arena
                        .atom(Bitvector32Term::Variable(Variable(2000 + index as u64)))
                        .unwrap();
                    left_shared = arena.binary(CheckedBinaryOperator::Add, left_shared, left_atom);
                    right_shared =
                        arena.binary(CheckedBinaryOperator::Add, right_shared, right_atom);
                }
                for index in 0..size {
                    let left_atom = arena
                        .atom(Bitvector32Term::Variable(Variable(3000 + index as u64)))
                        .unwrap();
                    let right_atom = arena
                        .atom(Bitvector32Term::Variable(Variable(3000 + index as u64)))
                        .unwrap();
                    let left_root =
                        arena.binary(CheckedBinaryOperator::Add, left_shared, left_atom);
                    let right_root =
                        arena.binary(CheckedBinaryOperator::Add, right_shared, right_atom);
                    assert!(arena.equivalent(left_root, right_root));
                }
            });
            measurements.push(work);
        }
        for pair in measurements.windows(2) {
            assert!(
                pair[1] <= 4 * pair[0] + 16,
                "shared subgraph comparison should not retraverse roots: {measurements:?}"
            );
        }
    }

    #[test]
    fn opaque_payload_work_scales_with_application_identity() {
        let mut measurements = Vec::new();
        for payload_size in [8usize, 16, 32, 64] {
            let term = Bitvector32Term::PureFunctionApplication {
                name: "opaque".repeat(payload_size),
                arguments: (0..payload_size)
                    .map(|index| Bitvector32Term::Variable(Variable(index as u64)))
                    .collect(),
            };
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(!crate::instrumentation::deadline_exceeded_with_work(
                    signed_term_work(&term,)
                ));
            });
            measurements.push(work);
        }
        for pair in measurements.windows(2) {
            assert!(
                pair[1] > pair[0],
                "opaque payloads must be charged by their full identity: {measurements:?}"
            );
            assert!(pair[1] <= 5 * pair[0], "{measurements:?}");
        }
    }

    #[test]
    fn deep_opaque_payload_work_is_iterative_and_budgeted() {
        let mut term = x();
        for _ in 0..4096 {
            term = Bitvector32Term::PureFunctionApplication {
                name: "f".to_string(),
                arguments: vec![term],
            };
        }
        assert!(is_opaque_atom(&term));
        let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
            assert!(!crate::instrumentation::deadline_exceeded_with_work(
                signed_term_work(&term)
            ));
        });
        assert!(work > 4096);
    }

    #[test]
    fn deep_opaque_payload_certificate_check_is_iterative() {
        let mut term = x();
        for _ in 0..4096 {
            term = Bitvector32Term::PureFunctionApplication {
                name: "f".to_string(),
                arguments: vec![term],
            };
        }
        let premise = le(term, Bitvector32Term::Constant(1));
        let certificate = SignedArithmeticCertificate {
            nodes: vec![SignedArithmeticNode::Premise {
                index: 0,
                result: claim(&premise),
            }],
            conclusion: 0,
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&premise, std::slice::from_ref(&premise))
        });
        assert_eq!(result, Ok(()));
        assert!(work > 4096);
    }

    #[test]
    fn deep_interval_proposition_conclusion_uses_bounded_identity() {
        let mut term = x();
        for _ in 0..1024 {
            term = Bitvector32Term::PureFunctionApplication {
                name: "f".to_string(),
                arguments: vec![term],
            };
        }
        let goal = le(term.clone(), Bitvector32Term::Constant(0));
        let premise_claim = claim(&goal);
        let certificate = SignedArithmeticCertificate {
            nodes: vec![
                SignedArithmeticNode::Premise {
                    index: 0,
                    result: premise_claim,
                },
                SignedArithmeticNode::IntervalFromAffine {
                    source: 0,
                    term: term.clone(),
                    lower: SIGNED_MIN,
                    upper: 0,
                },
                SignedArithmeticNode::IntervalAtom {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: Bitvector32Term::Constant(0),
                    lower: 0,
                    upper: 0,
                },
                SignedArithmeticNode::IntervalCompare {
                    left: 1,
                    right: 2,
                    comparison: SignedArithmeticComparison::LessEqual,
                    result: goal.clone(),
                },
            ],
            conclusion: 3,
        };
        let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
            certificate.check(&goal, std::slice::from_ref(&goal))
        });
        assert_eq!(result, Ok(()));
        assert!(work > 1024);
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
    fn scale_work_grows_with_coefficient_magnitude() {
        let premise = le(Bitvector32Term::Constant(0), Bitvector32Term::Constant(0));
        let mut measurements = Vec::new();
        for bits in [8usize, 16, 32, 64] {
            let coefficient = BigInt::one() << bits;
            let result = claim(&premise);
            let certificate = SignedArithmeticCertificate {
                nodes: vec![
                    SignedArithmeticNode::Premise {
                        index: 0,
                        result: claim(&premise),
                    },
                    SignedArithmeticNode::Scale {
                        source: 0,
                        coefficient,
                        result,
                    },
                ],
                conclusion: 1,
            };
            let (checked, work) = crate::instrumentation::measure_deterministic_work(|| {
                certificate.check(&premise, std::slice::from_ref(&premise))
            });
            assert_eq!(checked, Ok(()));
            measurements.push(work);
        }
        assert!(measurements.windows(2).all(|pair| pair[1] > pair[0]));
    }

    #[test]
    fn affine_multi_key_and_deep_atom_work_scales() {
        let mut measurements = Vec::new();
        for size in [4usize, 8, 16, 32] {
            let mut terms = BTreeMap::new();
            for index in 0..size {
                let mut atom = Bitvector32Term::Variable(Variable(index as u64));
                for depth in 0..size {
                    atom = Bitvector32Term::PureFunctionApplication {
                        name: format!("f{depth}"),
                        arguments: vec![atom],
                    };
                }
                let key = SignedArithmeticAtom::from_term(&atom).unwrap();
                terms.insert(key, BigInt::one());
            }
            let claim = SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::LessEqual,
                terms,
                constant: BigInt::zero(),
            };
            let ((), work) = crate::instrumentation::measure_deterministic_work(|| {
                assert!(same_int32_claim(&claim, &claim));
            });
            measurements.push(work);
        }
        assert!(
            measurements.windows(2).all(|pair| pair[1] > pair[0]),
            "multi-key deep atom work must scale: {measurements:?}"
        );
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
