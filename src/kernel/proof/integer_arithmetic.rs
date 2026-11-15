//! Explicit certificates for linear arithmetic over mathematical integers.
//!
//! A planner supplies a flat, topologically ordered certificate. Checking
//! validates only the referenced premises and local nodes; it does not invoke
//! the machine signed arithmetic checker or search ambient facts.

pub(crate) use super::integer_affine_atoms::IntegerAffineAtom;
use super::integer_affine_atoms::{IntegerFoldAtomRecord, intern_integer_fold_atom};
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::machine_integer::bounds::operation_bound;
use crate::kernel::{ConditionTerm, IntegerTerm, Proposition};
use num_bigint::BigInt;
use num_traits::{One, Zero};
use std::collections::{BTreeMap, HashMap, HashSet};
use std::sync::Arc;

/// The normalized relation `sum(coeff * variable) + constant REL 0`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum IntegerAffineRelation {
    LessEqual,
    Equal,
}

/// A claimed local affine result. The checker recomputes this value at every
/// node, making changes to terms, coefficients, operators, or constants
/// visible to the certificate boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IntegerAffineClaim {
    pub(crate) relation: IntegerAffineRelation,
    pub(crate) terms: BTreeMap<IntegerAffineAtom, BigInt>,
    pub(crate) constant: BigInt,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum IntegerArithmeticNode {
    Premise {
        index: usize,
        result: IntegerAffineClaim,
    },
    Scale {
        source: usize,
        coefficient: BigInt,
        result: IntegerAffineClaim,
    },
    Add {
        left: usize,
        right: usize,
        result: IntegerAffineClaim,
    },
    /// Turn an equality into one of its two non-strict directions.
    EqualityToLessEqual {
        source: usize,
        reverse: bool,
        result: IntegerAffineClaim,
    },
    /// Close an equality from opposite non-strict bounds.
    EqualityFromBounds {
        lower: usize,
        upper: usize,
        result: IntegerAffineClaim,
    },
    /// Context-free tautologies such as `x + 1 > x` and `x - x == 0`.
    Trivial { result: IntegerAffineClaim },
    /// Assume the integer negation of a non-strict goal: from the goal
    /// `t <= 0`, the claim `-t + 1 <= 0`. A certificate that uses it must
    /// conclude with the goal or with a contradiction.
    NegatedGoal { result: IntegerAffineClaim },
    /// Divide a non-strict claim by a positive common factor of its
    /// coefficients and round the constant up (a Chvatal-Gomory step):
    /// `g*t + k <= 0` gives `t + ceil(k / g) <= 0` over the integers.
    Divide {
        source: usize,
        divisor: BigInt,
        result: IntegerAffineClaim,
    },
    /// A machine value lies in its type's range: `MIN <= to_integer(v)`,
    /// or with `upper`, `to_integer(v) <= MAX`. `value` is the machine
    /// observation `to_integer(v)`; any other term is refused.
    TypeRange {
        value: IntegerTerm,
        upper: bool,
        result: IntegerAffineClaim,
    },
    /// An unsigned machine quotient, shift, or remainder by a constant is
    /// bounded by its operand ([`operation_bound`]): for `q = x / c`, or
    /// `q = x >> k` with `c = 2^k`, `c * q <= x`, or with `upper`,
    /// `x <= c * q + (c - 1)`; for `r = x % c`, with `upper`, `r <= c - 1`.
    /// `value` is the observation `to_integer(q)` or `to_integer(r)`.
    OperationBound {
        value: IntegerTerm,
        upper: bool,
        result: IntegerAffineClaim,
    },
    /// A premise `v != m`, where `m` is the minimum of `v`'s machine type,
    /// gives `m + 1 <= v`; at the type's maximum it gives `v <= m - 1`
    /// ([`excluded_type_bound`]).
    ExcludedTypeBound {
        index: usize,
        result: IntegerAffineClaim,
    },
    /// A non-strict bound and a disequality of the same difference give the
    /// strict bound: from node `bound`, `t <= 0`, and premise `disequal`,
    /// `l != r` with `l - r` equal to `t` or `-t`, the claim `t + 1 <= 0`
    /// ([`integer_disequality_claims`]). Over the integers `t <= 0` and
    /// `t != 0` leave `t <= -1`. The Integer counterpart of the
    /// `signed_int32` certificate's `less_than_from_not_equal`, stated once
    /// for every format and for plain `Integer`.
    StrictFromDisequal {
        bound: usize,
        disequal: usize,
        result: IntegerAffineClaim,
    },
}

/// A flat, locally checkable linear arithmetic certificate.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct IntegerArithmeticCertificate {
    pub(crate) nodes: Vec<IntegerArithmeticNode>,
    pub(crate) conclusion: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum IntegerArithmeticCheckError {
    InvalidPremise(usize),
    InvalidNodeReference(usize),
    UnsupportedPremise(usize),
    UnsupportedGoal,
    NodeResultMismatch(usize),
    InvalidCoefficient(usize),
    InvalidRelation(usize),
    InvalidDivisor(usize),
    NegatedGoalUnsupported(usize),
    WorkLimitExceeded,
    DoesNotFollow,
}

impl IntegerArithmeticCertificate {
    pub(crate) fn check(
        &self,
        goal: &Proposition,
        premises: &[Proposition],
    ) -> Result<(), IntegerArithmeticCheckError> {
        let mut collection_context = IntegerAffineCollectionContext::default();
        // Keep fold alpha keys scoped to this checked certificate. This
        // reuses one key for shared source nodes across the goal and all
        // explicitly selected premises without retaining a process-wide
        // source-id cache.
        let goal_claims = integer_affine_claims_with_context(goal, &mut collection_context);
        let expected = goal_claims
            .first()
            .cloned()
            .ok_or(IntegerArithmeticCheckError::UnsupportedGoal)?;
        let mut checked: Vec<IntegerAffineClaim> = Vec::with_capacity(self.nodes.len());
        // A premise can be referenced by many nodes. Cache by its explicit
        // index so a large expression is normalized once per check.
        #[derive(Clone)]
        enum CachedPremise {
            Unknown,
            Supported(Vec<IntegerAffineClaim>),
            Unsupported,
        }
        let mut premise_cache = vec![CachedPremise::Unknown; premises.len()];
        for (node_index, node) in self.nodes.iter().enumerate() {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
            }
            let result = match node {
                IntegerArithmeticNode::Premise { index, result } => {
                    let premise = premises
                        .get(*index)
                        .ok_or(IntegerArithmeticCheckError::InvalidPremise(*index))?;
                    if matches!(premise_cache[*index], CachedPremise::Unknown) {
                        let claims =
                            integer_affine_claims_with_context(premise, &mut collection_context);
                        if claims.is_empty() {
                            premise_cache[*index] = CachedPremise::Unsupported;
                            return Err(IntegerArithmeticCheckError::UnsupportedPremise(*index));
                        }
                        premise_cache[*index] = CachedPremise::Supported(claims);
                    }
                    let claims = match &premise_cache[*index] {
                        CachedPremise::Supported(claims) => claims,
                        CachedPremise::Unsupported => {
                            return Err(IntegerArithmeticCheckError::UnsupportedPremise(*index));
                        }
                        CachedPremise::Unknown => unreachable!(),
                    };
                    // A premise is cited by any one of its exact readings.
                    let Some(expected) = claims.iter().find(|claim| *claim == result) else {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    };
                    if !charge_claim_work(expected) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    expected.clone()
                }
                IntegerArithmeticNode::Scale {
                    source,
                    coefficient,
                    result,
                } => {
                    let source = checked
                        .get(*source)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*source))?;
                    if matches!(source.relation, IntegerAffineRelation::LessEqual)
                        && coefficient < &BigInt::zero()
                    {
                        return Err(IntegerArithmeticCheckError::InvalidCoefficient(node_index));
                    }
                    let expected = scale_claim(source, coefficient)
                        .ok_or(IntegerArithmeticCheckError::WorkLimitExceeded)?;
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::Add {
                    left,
                    right,
                    result,
                } => {
                    let left = checked
                        .get(*left)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*left))?;
                    let right = checked
                        .get(*right)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*right))?;
                    if left.relation != right.relation {
                        return Err(IntegerArithmeticCheckError::InvalidRelation(node_index));
                    }
                    if !charge_claim_work(left) || !charge_claim_work(right) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    let expected = add_claim(left, right);
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::EqualityToLessEqual {
                    source,
                    reverse,
                    result,
                } => {
                    let source = checked
                        .get(*source)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*source))?;
                    if source.relation != IntegerAffineRelation::Equal {
                        return Err(IntegerArithmeticCheckError::InvalidRelation(node_index));
                    }
                    if !charge_claim_work(source) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    let expected = if *reverse {
                        negate_claim(source, IntegerAffineRelation::LessEqual)
                    } else {
                        IntegerAffineClaim {
                            relation: IntegerAffineRelation::LessEqual,
                            terms: source.terms.clone(),
                            constant: source.constant.clone(),
                        }
                    };
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::EqualityFromBounds {
                    lower,
                    upper,
                    result,
                } => {
                    let lower = checked
                        .get(*lower)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*lower))?;
                    let upper = checked
                        .get(*upper)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*upper))?;
                    if lower.relation != IntegerAffineRelation::LessEqual
                        || upper.relation != IntegerAffineRelation::LessEqual
                    {
                        return Err(IntegerArithmeticCheckError::InvalidRelation(node_index));
                    }
                    if !charge_claim_work(lower) || !charge_claim_work(upper) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    let expected = IntegerAffineClaim {
                        relation: IntegerAffineRelation::Equal,
                        terms: lower.terms.clone(),
                        constant: lower.constant.clone(),
                    };
                    if !claims_are_opposites(lower, upper) || &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::Trivial { result } => {
                    if !charge_claim_work(result) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    if !claim_is_trivial(result) {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    result.clone()
                }
                IntegerArithmeticNode::NegatedGoal { result } => {
                    if expected.relation != IntegerAffineRelation::LessEqual {
                        return Err(IntegerArithmeticCheckError::NegatedGoalUnsupported(
                            node_index,
                        ));
                    }
                    if !charge_claim_work(&expected) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    let mut negated = negate_claim(&expected, IntegerAffineRelation::LessEqual);
                    negated.constant += BigInt::one();
                    if &negated != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    negated
                }
                IntegerArithmeticNode::TypeRange {
                    value,
                    upper,
                    result,
                } => {
                    let IntegerTerm::Machine(value) = value else {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    };
                    let expected = machine_type_range_claim(value, *upper)
                        .ok_or(IntegerArithmeticCheckError::WorkLimitExceeded)?;
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::OperationBound {
                    value,
                    upper,
                    result,
                } => {
                    let IntegerTerm::Machine(value) = value else {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    };
                    let expected = operation_bound(value, *upper)
                        .and_then(|bound| integer_affine_claim(&bound))
                        .ok_or(IntegerArithmeticCheckError::NodeResultMismatch(node_index))?;
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::ExcludedTypeBound { index, result } => {
                    let premise = premises
                        .get(*index)
                        .ok_or(IntegerArithmeticCheckError::InvalidPremise(*index))?;
                    let expected = excluded_type_bound(premise)
                        .and_then(|bound| integer_affine_claim(&bound))
                        .ok_or(IntegerArithmeticCheckError::UnsupportedPremise(*index))?;
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::StrictFromDisequal {
                    bound,
                    disequal,
                    result,
                } => {
                    let bound = checked
                        .get(*bound)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*bound))?;
                    if bound.relation != IntegerAffineRelation::LessEqual {
                        return Err(IntegerArithmeticCheckError::InvalidRelation(node_index));
                    }
                    let premise = premises
                        .get(*disequal)
                        .ok_or(IntegerArithmeticCheckError::InvalidPremise(*disequal))?;
                    // One reading per side of the one cited disequality; the
                    // bound is matched as it stands or negated, never searched.
                    let differences = integer_disequality_claims(premise);
                    if differences.is_empty() {
                        return Err(IntegerArithmeticCheckError::UnsupportedPremise(*disequal));
                    }
                    if !charge_claim_work(bound) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    let matches = differences.iter().any(|difference| {
                        charge_claim_work(difference)
                            && ((difference.terms == bound.terms
                                && difference.constant == bound.constant)
                                || claims_are_opposites(difference, bound))
                    });
                    if !matches {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    let mut expected = bound.clone();
                    expected.constant += BigInt::one();
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
                IntegerArithmeticNode::Divide {
                    source,
                    divisor,
                    result,
                } => {
                    let source = checked
                        .get(*source)
                        .ok_or(IntegerArithmeticCheckError::InvalidNodeReference(*source))?;
                    if source.relation != IntegerAffineRelation::LessEqual {
                        return Err(IntegerArithmeticCheckError::InvalidRelation(node_index));
                    }
                    if !charge_claim_work(source) {
                        return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
                    }
                    let expected = divide_claim(source, divisor)
                        .ok_or(IntegerArithmeticCheckError::InvalidDivisor(node_index))?;
                    if &expected != result {
                        return Err(IntegerArithmeticCheckError::NodeResultMismatch(node_index));
                    }
                    expected
                }
            };
            if !charge_claim_work(&result) {
                return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
            }
            checked.push(result);
        }
        let actual = checked.get(self.conclusion).ok_or(
            IntegerArithmeticCheckError::InvalidNodeReference(self.conclusion),
        )?;
        if !charge_claim_work(actual) || !charge_claim_work(&expected) {
            return Err(IntegerArithmeticCheckError::WorkLimitExceeded);
        }
        // A contradiction proves any supported goal: either the premises
        // are inconsistent, or they are inconsistent with the negated goal,
        // and then the goal holds.
        (goal_claims.contains(actual)
            || claim_is_contradiction(actual)
            || claim_is_trivial(&expected))
        .then_some(())
        .ok_or(IntegerArithmeticCheckError::DoesNotFollow)
    }
}

fn charge_claim_work(claim: &IntegerAffineClaim) -> bool {
    let mut bits = claim.constant.bits() as usize;
    for coefficient in claim.terms.values() {
        bits = bits.saturating_add(1 + coefficient.bits() as usize);
    }
    !crate::instrumentation::deadline_exceeded_with_work(
        bits.saturating_add(claim.terms.len()).max(1),
    )
}

fn charge_integer_product(left: &BigInt, right: &BigInt) -> bool {
    let units = (left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1);
    if crate::instrumentation::deadline_exceeded_with_work(units) {
        return false;
    }
    true
}

pub(crate) fn scale_claim(
    claim: &IntegerAffineClaim,
    coefficient: &BigInt,
) -> Option<IntegerAffineClaim> {
    let mut terms = Vec::with_capacity(claim.terms.len());
    for (term, value) in &claim.terms {
        if !charge_integer_product(value, coefficient) {
            return None;
        }
        let value = value * coefficient;
        if !value.is_zero() {
            terms.push((term.clone(), value));
        }
    }
    if !charge_integer_product(&claim.constant, coefficient) {
        return None;
    }
    Some(IntegerAffineClaim {
        relation: claim.relation.clone(),
        terms: terms.into_iter().collect(),
        constant: &claim.constant * coefficient,
    })
}

pub(crate) fn add_claim(
    left: &IntegerAffineClaim,
    right: &IntegerAffineClaim,
) -> IntegerAffineClaim {
    let mut terms = left.terms.clone();
    for (term, coefficient) in &right.terms {
        let value = terms.get(term).cloned().unwrap_or_else(BigInt::zero) + coefficient;
        if value.is_zero() {
            terms.remove(term);
        } else {
            terms.insert(term.clone(), value);
        }
    }
    IntegerAffineClaim {
        relation: left.relation.clone(),
        terms,
        constant: &left.constant + &right.constant,
    }
}

pub(crate) fn negate_claim(
    claim: &IntegerAffineClaim,
    relation: IntegerAffineRelation,
) -> IntegerAffineClaim {
    let terms = claim
        .terms
        .iter()
        .map(|(term, coefficient)| (term.clone(), -coefficient))
        .filter(|(_, coefficient)| !coefficient.is_zero())
        .collect();
    IntegerAffineClaim {
        relation,
        terms,
        constant: -&claim.constant,
    }
}

/// Divide every coefficient exactly by `divisor` and round the constant up.
/// Over the integers, `g*t + k <= 0` means `t <= -k/g`, so `t <= floor(-k/g)`,
/// which is `t + ceil(k/g) <= 0`.
fn divide_claim(claim: &IntegerAffineClaim, divisor: &BigInt) -> Option<IntegerAffineClaim> {
    if divisor <= &BigInt::zero() {
        return None;
    }
    let mut terms = BTreeMap::new();
    for (term, value) in &claim.terms {
        if !charge_integer_product(value, divisor) {
            return None;
        }
        if !(value % divisor).is_zero() {
            return None;
        }
        terms.insert(term.clone(), value / divisor);
    }
    if !charge_integer_product(&claim.constant, divisor) {
        return None;
    }
    // BigInt division truncates toward zero; ceil(k/g) = -floor(-k/g).
    let negated = -&claim.constant;
    let mut floor = &negated / divisor;
    if (&floor * divisor) > negated {
        floor -= BigInt::one();
    }
    Some(IntegerAffineClaim {
        relation: IntegerAffineRelation::LessEqual,
        terms,
        constant: -floor,
    })
}

fn claim_is_contradiction(claim: &IntegerAffineClaim) -> bool {
    claim.terms.is_empty()
        && match claim.relation {
            IntegerAffineRelation::LessEqual => claim.constant > BigInt::zero(),
            IntegerAffineRelation::Equal => !claim.constant.is_zero(),
        }
}

fn claims_are_opposites(lower: &IntegerAffineClaim, upper: &IntegerAffineClaim) -> bool {
    lower.terms.len() == upper.terms.len()
        && lower
            .terms
            .iter()
            .zip(&upper.terms)
            .all(|((left, a), (right, b))| left == right && -a == *b)
        && -&lower.constant == upper.constant
}

/// The machine value and constant of a disequality `v != m`, read as an
/// Integer comparison: natively, `x != 0u64`, or as written,
/// `to_integer(v) != m`, either side first.
fn integer_disequality(
    proposition: &Proposition,
) -> Option<(crate::kernel::SharedMachineIntegerTerm, BigInt)> {
    let readings =
        crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
            proposition,
        );
    let reading = readings.first().unwrap_or(proposition);
    let (left, right) = match reading {
        Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), false)
        | Proposition::ConditionIs(ConditionTerm::IntegerNotEqual(left, right), true) => {
            (left, right)
        }
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), true) => {
                (left, right)
            }
            _ => return None,
        },
        _ => return None,
    };
    // The written constant may be literal arithmetic, such as INT_MIN spelled
    // `-2147483647 - 1`. Read its value from this selected premise; do not rely
    // on admission having filed a folded native copy of the disequality.
    match (left.as_ref(), right.as_ref()) {
        (IntegerTerm::Machine(value), _) => Some((value.clone(), literal_integer_value(right)?)),
        (_, IntegerTerm::Machine(value)) => Some((value.clone(), literal_integer_value(left)?)),
        _ => None,
    }
}

/// The differences `l - r` of a disequality `l != r`, as `Equal` claims
/// whose terms and constant are the difference's, one per exact reading (a
/// native disequality of 32- or 64-bit words has two, as for
/// [`integer_affine_claims`]). Empty when the proposition is no
/// disequality, or one whose difference has no atom: a disequality of
/// constants is already a claim. `StrictFromDisequal` reads it.
pub(crate) fn integer_disequality_claims(proposition: &Proposition) -> Vec<IntegerAffineClaim> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !value),
            _ => return Vec::new(),
        },
        _ => return Vec::new(),
    };
    let readings = if matches!(
        condition,
        crate::kernel::integer_comparison_condition!(_, _)
    ) {
        vec![Proposition::ConditionIs(condition.clone(), value)]
    } else {
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            &Proposition::ConditionIs(condition.clone(), value),
        )
    };
    let mut context = IntegerAffineCollectionContext::default();
    let mut differences = Vec::with_capacity(readings.len());
    for reading in &readings {
        let (left, right) = match reading {
            Proposition::ConditionIs(ConditionTerm::IntegerNotEqual(left, right), true)
            | Proposition::ConditionIs(ConditionTerm::IntegerEqual(left, right), false) => {
                (left, right)
            }
            _ => continue,
        };
        let mut terms = BTreeMap::new();
        let mut constant = BigInt::zero();
        if collect_integer_affine_terms(
            left,
            &BigInt::one(),
            &mut terms,
            &mut constant,
            &mut context,
        )
        .is_none()
            || collect_integer_affine_terms(
                right,
                &BigInt::from(-1),
                &mut terms,
                &mut constant,
                &mut context,
            )
            .is_none()
            || terms.is_empty()
        {
            continue;
        }
        let difference = IntegerAffineClaim {
            relation: IntegerAffineRelation::Equal,
            terms,
            constant,
        };
        if !differences.contains(&difference) {
            differences.push(difference);
        }
    }
    differences
}

/// The bound a disequality with a machine type's endpoint gives:
/// `v != MIN` is `MIN + 1 <= v`, and `v != MAX` is `v <= MAX - 1`. A
/// disequality with any other constant is no bound.
pub(crate) fn excluded_type_bound(premise: &Proposition) -> Option<Proposition> {
    let (value, constant) = integer_disequality(premise)?;
    let (min, max) = value.ty().format().bounds();
    let observed = IntegerTerm::Machine(value);
    let condition = if constant == min {
        ConditionTerm::integer_less_equal(IntegerTerm::constant(min + BigInt::one()), observed)
    } else if constant == max {
        ConditionTerm::integer_less_equal(observed, IntegerTerm::constant(max - BigInt::one()))
    } else {
        return None;
    };
    Some(Proposition::ConditionIs(condition, true))
}

pub(crate) fn machine_type_range_claim(
    value: &crate::kernel::SharedMachineIntegerTerm,
    upper: bool,
) -> Option<IntegerAffineClaim> {
    integer_affine_claim(&crate::kernel::machine_integer::range::range_fact(
        value, upper,
    ))
}

/// The machine values that are atoms of `proposition`'s affine claim, each
/// once, in first-occurrence order.
pub(crate) fn integer_affine_machine_values(
    proposition: &Proposition,
) -> Vec<crate::kernel::SharedMachineIntegerTerm> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !value),
            _ => return Vec::new(),
        },
        _ => return Vec::new(),
    };
    // A native comparison observes the machine values its Integer reading
    // does, as `integer_affine_claim` reads it.
    if !matches!(
        condition,
        crate::kernel::integer_comparison_condition!(_, _)
    ) && let Some(reading) =
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            &Proposition::ConditionIs(condition.clone(), value),
        )
        .into_iter()
        .next()
    {
        return integer_affine_machine_values(&reading);
    }
    let (left, right) = match condition {
        ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right)
        | ConditionTerm::IntegerEqual(left, right) => (left, right),
        _ => return Vec::new(),
    };
    let mut seen = HashSet::new();
    let mut values = Vec::new();
    let mut stack = vec![right.clone(), left.clone()];
    while let Some(node) = stack.pop() {
        if !seen.insert(node.id()) {
            continue;
        }
        match node.as_ref() {
            IntegerTerm::Machine(value) => values.push(value.clone()),
            IntegerTerm::Negate(child) => stack.push(child.clone()),
            IntegerTerm::Add(left, right) | IntegerTerm::Subtract(left, right) => {
                stack.push(right.clone());
                stack.push(left.clone());
            }
            IntegerTerm::Multiply(left, right) => {
                if left.as_const().is_some() {
                    stack.push(right.clone());
                } else if right.as_const().is_some() {
                    stack.push(left.clone());
                }
            }
            _ => {}
        }
    }
    values
}

fn claim_is_trivial(claim: &IntegerAffineClaim) -> bool {
    claim.terms.is_empty()
        && match claim.relation {
            IntegerAffineRelation::LessEqual => claim.constant <= BigInt::zero(),
            IntegerAffineRelation::Equal => claim.constant.is_zero(),
        }
}

/// Per-claim cache for fold identities.  This is deliberately scoped to one
/// normalization: a shared source node is never alpha-keyed once for each
/// occurrence in the same claim, while load-registry epochs cannot make a
/// process-wide source-id cache stale.
#[derive(Default)]
struct IntegerAffineCollectionContext {
    constants: HashMap<u64, Option<BigInt>>,
    fold_atoms: HashMap<crate::kernel::SharedIntegerTerm, Arc<IntegerFoldAtomRecord>>,
}

#[cfg(test)]
thread_local! {
    static INTEGER_FOLD_ALPHA_CONSTRUCTIONS: std::cell::Cell<usize> = const {
        std::cell::Cell::new(0)
    };
}

#[cfg(test)]
fn reset_fold_alpha_constructions() {
    INTEGER_FOLD_ALPHA_CONSTRUCTIONS.with(|count| count.set(0));
}

#[cfg(test)]
fn fold_alpha_constructions() -> usize {
    INTEGER_FOLD_ALPHA_CONSTRUCTIONS.with(std::cell::Cell::get)
}

fn fold_atom_for_claim(
    context: &mut IntegerAffineCollectionContext,
    term: &crate::kernel::SharedIntegerTerm,
) -> Option<Arc<IntegerFoldAtomRecord>> {
    if let Some(atom) = context.fold_atoms.get(term) {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        return Some(atom.clone());
    }
    #[cfg(test)]
    INTEGER_FOLD_ALPHA_CONSTRUCTIONS.with(|count| count.set(count.get() + 1));
    let atom = intern_integer_fold_atom(term)?;
    context.fold_atoms.insert(term.clone(), atom.clone());
    Some(atom)
}

/// Normalize one integer proposition for use in a certificate node.
///
/// This is intentionally a small, context-free conversion. The returned
/// atom map contains only checked source identities: variables, machine
/// observations, pure applications, state-aware opaque folds, and complete
/// symbolic products and truncating terms. An
/// arbitrary deep Integer term is never used directly as a map key.
/// Every Integer affine claim `proposition` holds exactly when. A native
/// equality of 32- or 64-bit words does not say whether its operands are
/// signed, and both readings are exact, so it has two; any other proposition
/// has at most one. A promoted `int32` comparison of widenings (C's
/// comparison of an 8- or 16-bit value) is the Integer comparison of its
/// sides' values. The kernel accepts a premise or goal as any of them.
pub(crate) fn integer_affine_claims(proposition: &Proposition) -> Vec<IntegerAffineClaim> {
    let mut context = IntegerAffineCollectionContext::default();
    integer_affine_claims_with_context(proposition, &mut context)
}

fn integer_affine_claims_with_context(
    proposition: &Proposition,
    context: &mut IntegerAffineCollectionContext,
) -> Vec<IntegerAffineClaim> {
    let readings = match proposition {
        Proposition::ConditionIs(condition, _)
            if !matches!(
                condition,
                crate::kernel::integer_comparison_condition!(_, _)
            ) =>
        {
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                proposition,
            )
        }
        _ => Vec::new(),
    };
    if readings.is_empty() {
        return integer_affine_claim_with_context(proposition, context)
            .into_iter()
            .collect();
    }
    let mut claims = Vec::with_capacity(readings.len());
    for reading in &readings {
        if let Some(claim) = integer_affine_claim_with_context(reading, context)
            && !claims.contains(&claim)
        {
            claims.push(claim);
        }
    }
    claims
}

/// Whether `proposition` is an Integer affine claim as written, rather than
/// a native comparison read as one. Diagnostics name the fragment a goal is
/// written in.
pub(crate) fn written_integer_affine_claim(proposition: &Proposition) -> bool {
    let native = match proposition {
        Proposition::Not(inner) => match inner.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                !crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                    &Proposition::ConditionIs(condition.clone(), !value),
                )
                .is_empty()
            }
            _ => false,
        },
        _ => !crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            proposition,
        )
        .is_empty(),
    };
    !native && integer_affine_claim(proposition).is_some()
}

pub(crate) fn integer_affine_claim(proposition: &Proposition) -> Option<IntegerAffineClaim> {
    let mut context = IntegerAffineCollectionContext::default();
    integer_affine_claim_with_context(proposition, &mut context)
}

fn integer_affine_claim_with_context(
    proposition: &Proposition,
    context: &mut IntegerAffineCollectionContext,
) -> Option<IntegerAffineClaim> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        Proposition::Not(body) => match body.as_ref() {
            Proposition::ConditionIs(condition, value) => (condition, !value),
            _ => return None,
        },
        _ => return None,
    };
    // A native comparison of machine values holds exactly when the Integer
    // comparison of their exact observations does, so it is that Integer
    // claim. One constant-size reading; nothing else is consulted.
    if !matches!(
        condition,
        crate::kernel::integer_comparison_condition!(_, _) | ConditionTerm::Constant(_)
    ) && let Some(reading) =
        crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
            &Proposition::ConditionIs(condition.clone(), value),
        )
        .into_iter()
        .next()
    {
        return integer_affine_claim_with_context(&reading, context);
    }
    if let ConditionTerm::Constant(actual) = condition {
        return Some(IntegerAffineClaim {
            relation: IntegerAffineRelation::Equal,
            terms: BTreeMap::new(),
            constant: if *actual == value {
                BigInt::zero()
            } else {
                BigInt::one()
            },
        });
    }
    let (left, right, relation, strict) = match condition {
        ConditionTerm::IntegerLessThan(left, right) if value => {
            (left, right, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerLessEqual(left, right) if value => {
            (left, right, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerGreaterThan(left, right) if value => {
            (right, left, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) if value => {
            (right, left, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerEqual(left, right) if value => {
            (left, right, IntegerAffineRelation::Equal, false)
        }
        ConditionTerm::IntegerLessThan(left, right) => {
            (right, left, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerLessEqual(left, right) => {
            (right, left, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerGreaterThan(left, right) => {
            (left, right, IntegerAffineRelation::LessEqual, false)
        }
        ConditionTerm::IntegerGreaterEqual(left, right) => {
            (left, right, IntegerAffineRelation::LessEqual, true)
        }
        ConditionTerm::IntegerEqual(left, right) => {
            // Disequality is outside this fragment, except for constants.
            let mut terms = BTreeMap::new();
            let mut constant = BigInt::zero();
            collect_integer_affine_terms(left, &BigInt::one(), &mut terms, &mut constant, context)?;
            collect_integer_affine_terms(
                right,
                &BigInt::from(-1),
                &mut terms,
                &mut constant,
                context,
            )?;
            return (terms.is_empty() && !constant.is_zero()).then_some(IntegerAffineClaim {
                relation: IntegerAffineRelation::LessEqual,
                terms,
                constant: BigInt::from(-1),
            });
        }
        ConditionTerm::IntegerNotEqual(left, right) if value => {
            let mut terms = BTreeMap::new();
            let mut constant = BigInt::zero();
            collect_integer_affine_terms(left, &BigInt::one(), &mut terms, &mut constant, context)?;
            collect_integer_affine_terms(
                right,
                &BigInt::from(-1),
                &mut terms,
                &mut constant,
                context,
            )?;
            return (terms.is_empty() && !constant.is_zero()).then_some(IntegerAffineClaim {
                relation: IntegerAffineRelation::LessEqual,
                terms,
                constant: BigInt::from(-1),
            });
        }
        ConditionTerm::IntegerNotEqual(left, right) => {
            // A false disequality is the same affine equality as a true
            // IntegerEqual, including under a negated branch premise.
            (left, right, IntegerAffineRelation::Equal, false)
        }
        _ => return None,
    };
    let mut terms = BTreeMap::new();
    let mut constant = BigInt::zero();
    collect_integer_affine_terms(left, &BigInt::one(), &mut terms, &mut constant, context)?;
    collect_integer_affine_terms(right, &BigInt::from(-1), &mut terms, &mut constant, context)?;
    if strict {
        if crate::instrumentation::deadline_exceeded_with_work(constant.bits() as usize + 1) {
            return None;
        }
        constant += BigInt::one();
    }
    Some(IntegerAffineClaim {
        relation,
        terms,
        constant,
    })
}

/// A constant value for checking, with a shallow refusal for symbolic terms.
pub(crate) fn literal_integer_value(term: &crate::kernel::SharedIntegerTerm) -> Option<BigInt> {
    if !term.is_literal_arithmetic() {
        return None;
    }
    let mut cache = HashMap::new();
    collect_integer_constants(term, &mut cache)?;
    cache.remove(&term.id())?
}

/// Literal arithmetic is builtin proof checking, not a lowering rewrite.
/// Cached shape flags refuse symbolic operands in constant time.
pub(crate) fn literal_integer_comparison_value(condition: &ConditionTerm) -> Option<bool> {
    let (left, right) = match condition {
        ConditionTerm::IntegerEqual(left, right)
        | ConditionTerm::IntegerNotEqual(left, right)
        | ConditionTerm::IntegerLessThan(left, right)
        | ConditionTerm::IntegerLessEqual(left, right)
        | ConditionTerm::IntegerGreaterThan(left, right)
        | ConditionTerm::IntegerGreaterEqual(left, right) => (left, right),
        _ => return None,
    };
    if !left.is_literal_arithmetic() || !right.is_literal_arithmetic() {
        return None;
    }
    let mut cache = HashMap::new();
    collect_integer_constants(left, &mut cache)?;
    collect_integer_constants(right, &mut cache)?;
    let left = cache.get(&left.id())?.as_ref()?;
    let right = cache.get(&right.id())?.as_ref()?;
    if crate::instrumentation::deadline_exceeded_with_work(
        left.bits() as usize + right.bits() as usize + 1,
    ) {
        return None;
    }
    Some(match condition {
        ConditionTerm::IntegerEqual(..) => left == right,
        ConditionTerm::IntegerNotEqual(..) => left != right,
        ConditionTerm::IntegerLessThan(..) => left < right,
        ConditionTerm::IntegerLessEqual(..) => left <= right,
        ConditionTerm::IntegerGreaterThan(..) => left > right,
        ConditionTerm::IntegerGreaterEqual(..) => left >= right,
        _ => unreachable!(),
    })
}

/// Evaluate only the explicit arithmetic DAG, once per node and under the
/// checker's numeric budget. None in the cache means a symbolic or undefined
/// value, not zero. Lowering and rewriting never call this evaluator.
fn collect_integer_constants(
    root: &crate::kernel::SharedIntegerTerm,
    cache: &mut HashMap<u64, Option<BigInt>>,
) -> Option<()> {
    let mut stack = vec![(root.clone(), false)];
    while let Some((node, expanded)) = stack.pop() {
        if cache.contains_key(&node.id()) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        if !node.is_literal_arithmetic() {
            cache.insert(node.id(), None);
            continue;
        }
        if !expanded {
            stack.push((node.clone(), true));
            match node.as_ref() {
                IntegerTerm::Negate(child) => stack.push((child.clone(), false)),
                IntegerTerm::Add(left, right)
                | IntegerTerm::Subtract(left, right)
                | IntegerTerm::Multiply(left, right)
                | IntegerTerm::TruncatingQuotient(left, right)
                | IntegerTerm::TruncatingRemainder(left, right) => {
                    stack.push((right.clone(), false));
                    stack.push((left.clone(), false));
                }
                _ => {}
            }
            continue;
        }
        let value = match node.as_ref() {
            IntegerTerm::Constant(value) => {
                if crate::instrumentation::deadline_exceeded_with_work(value.bits() as usize + 1) {
                    return None;
                }
                Some(value.clone())
            }
            IntegerTerm::Negate(child) => match cache.get(&child.id()).and_then(Option::as_ref) {
                Some(value) => {
                    if crate::instrumentation::deadline_exceeded_with_work(
                        value.bits() as usize + 1,
                    ) {
                        return None;
                    }
                    Some(-value)
                }
                None => None,
            },
            IntegerTerm::Add(left, right)
            | IntegerTerm::Subtract(left, right)
            | IntegerTerm::Multiply(left, right)
            | IntegerTerm::TruncatingQuotient(left, right)
            | IntegerTerm::TruncatingRemainder(left, right) => {
                match (
                    cache.get(&left.id()).and_then(Option::as_ref),
                    cache.get(&right.id()).and_then(Option::as_ref),
                ) {
                    (Some(left), Some(right)) => {
                        let work = if matches!(
                            node.as_ref(),
                            IntegerTerm::Add(..) | IntegerTerm::Subtract(..)
                        ) {
                            (left.bits() as usize + 1).saturating_add(right.bits() as usize + 1)
                        } else {
                            (left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1)
                        };
                        if crate::instrumentation::numeric_operation_work_exceeded(work) {
                            return None;
                        }
                        match node.as_ref() {
                            IntegerTerm::Add(..) => Some(left + right),
                            IntegerTerm::Subtract(..) => Some(left - right),
                            IntegerTerm::Multiply(..) => Some(left * right),
                            IntegerTerm::TruncatingQuotient(..) if !right.is_zero() => {
                                Some(left / right)
                            }
                            IntegerTerm::TruncatingRemainder(..) if !right.is_zero() => {
                                Some(left % right)
                            }
                            _ => None,
                        }
                    }
                    _ => None,
                }
            }
            _ => None,
        };
        cache.insert(node.id(), value);
    }
    Some(())
}

fn collect_integer_affine_terms(
    term: &crate::kernel::SharedIntegerTerm,
    coefficient: &BigInt,
    terms: &mut BTreeMap<IntegerAffineAtom, BigInt>,
    constant: &mut BigInt,
    context: &mut IntegerAffineCollectionContext,
) -> Option<()> {
    collect_integer_constants(term, &mut context.constants)?;
    // First collect the reachable DAG in postorder.  The interner gives each
    // node a stable identity, so this schedules a shared node exactly once.
    let mut scheduled = HashSet::new();
    let mut stack = vec![(term.clone(), false)];
    let mut order = Vec::new();
    while let Some((node, expanded)) = stack.pop() {
        if expanded {
            order.push(node);
            continue;
        }
        if !scheduled.insert(node.id()) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return None;
        }
        stack.push((node.clone(), true));
        collect_integer_constants(&node, &mut context.constants)?;
        if context
            .constants
            .get(&node.id())
            .and_then(Option::as_ref)
            .is_some()
        {
            continue;
        }
        match node.as_ref() {
            IntegerTerm::Negate(child) => stack.push((child.clone(), false)),
            IntegerTerm::Add(left, right) | IntegerTerm::Subtract(left, right) => {
                stack.push((right.clone(), false));
                stack.push((left.clone(), false));
            }
            IntegerTerm::Multiply(left, right) => {
                // A symbolic product is one opaque atom. Cached shape flags
                // let constant coefficients be checked without walking a
                // symbolic operand's DAG.
                if left.is_literal_arithmetic() {
                    collect_integer_constants(left, &mut context.constants)?;
                }
                if right.is_literal_arithmetic() {
                    collect_integer_constants(right, &mut context.constants)?;
                }
                if context.constants.get(&left.id()).and_then(Option::as_ref).is_some() {
                    stack.push((right.clone(), false));
                } else if context.constants.get(&right.id()).and_then(Option::as_ref).is_some() {
                    stack.push((left.clone(), false));
                }
            }
            IntegerTerm::TruncatingQuotient(_, _) | IntegerTerm::TruncatingRemainder(_, _) => {}
            IntegerTerm::Constant(_)
            | IntegerTerm::Variable(_)
            | IntegerTerm::Machine(_)
            | IntegerTerm::PureFunctionApplication(_)
            | IntegerTerm::AlgebraicMatch { .. }
            // An unresolved conditional is an opaque atom, as a machine
            // conditional's observation is.
            | IntegerTerm::If { .. } => {}
            // A RangeFold is a checked opaque atom.  Its body and endpoints
            // are represented by the kernel-issued alpha key below; affine
            // normalization must never enumerate or lower the range here.
            IntegerTerm::RangeFold { .. } => {}
        }
    }

    // Propagate the coefficient from each root toward the leaves.  This
    // keeps only one scalar per reachable node; no internal node constructs
    // or clones a complete affine map.
    let mut weights = HashMap::new();
    weights.insert(term.id(), coefficient.clone());
    for node in order.into_iter().rev() {
        let Some(weight) = weights.remove(&node.id()) else {
            continue;
        };
        if crate::instrumentation::deadline_exceeded_with_work(weight.bits() as usize + 1) {
            return None;
        }
        if weight.is_zero() {
            continue;
        }
        if let Some(value) = context.constants.get(&node.id()).and_then(Option::as_ref) {
            if !charge_integer_product(&weight, value)
                || crate::instrumentation::deadline_exceeded_with_work(
                    constant.bits() as usize + weight.bits() as usize + value.bits() as usize + 1,
                )
            {
                return None;
            }
            *constant += &weight * value;
            continue;
        }
        match node.as_ref() {
            IntegerTerm::Constant(_) => unreachable!("constants were evaluated above"),
            IntegerTerm::Variable(_)
            | IntegerTerm::Machine(_)
            | IntegerTerm::PureFunctionApplication(_)
            | IntegerTerm::AlgebraicMatch { .. }
            | IntegerTerm::If { .. }
            | IntegerTerm::TruncatingQuotient(_, _)
            | IntegerTerm::TruncatingRemainder(_, _) => {
                let atom = match node.as_ref() {
                    IntegerTerm::Variable(variable) => IntegerAffineAtom::Variable(*variable),
                    // An observation is the atom of its value reading
                    // (rule W): `to_integer(widen(v))` and `to_integer(v)`
                    // are one atom. One cached lookup per observation.
                    IntegerTerm::Machine(source) => match source.value_reading() {
                        Some(IntegerTerm::Machine(read)) => {
                            IntegerAffineAtom::Machine(read.clone())
                        }
                        Some(IntegerTerm::Constant(value)) => {
                            if !charge_integer_product(&weight, value) {
                                return None;
                            }
                            *constant += &weight * value;
                            continue;
                        }
                        _ => IntegerAffineAtom::Machine(source.clone()),
                    },
                    IntegerTerm::AlgebraicMatch { .. } => return None,
                    // An unresolved conditional is an opaque atom by its
                    // shared identity, as a quotient is.
                    IntegerTerm::If { .. } => IntegerAffineAtom::Nonlinear(node.id()),
                    // A quotient or remainder is keyed by its reading through
                    // its observations' value relations (rule W), so its two
                    // spellings are one atom.
                    IntegerTerm::TruncatingQuotient(_, _)
                    | IntegerTerm::TruncatingRemainder(_, _) => {
                        IntegerAffineAtom::Nonlinear(node.read_through().id())
                    }
                    IntegerTerm::PureFunctionApplication(application) => {
                        IntegerAffineAtom::Application(application.id())
                    }
                    _ => unreachable!(),
                };
                add_atom_weight(terms, atom, weight)?;
            }
            IntegerTerm::RangeFold { .. } => {
                let atom = IntegerAffineAtom::Fold(fold_atom_for_claim(context, &node)?);
                add_atom_weight(terms, atom, weight)?;
            }
            IntegerTerm::Negate(child) => {
                if !add_weight(&mut weights, child.id(), -weight) {
                    return None;
                }
            }
            IntegerTerm::Add(left, right) => {
                if !add_weight(&mut weights, left.id(), weight.clone())
                    || !add_weight(&mut weights, right.id(), weight)
                {
                    return None;
                }
            }
            IntegerTerm::Subtract(left, right) => {
                if !add_weight(&mut weights, left.id(), weight.clone())
                    || !add_weight(&mut weights, right.id(), -weight)
                {
                    return None;
                }
            }
            IntegerTerm::Multiply(left, right) => {
                let (child, factor) = if let Some(value) =
                    context.constants.get(&left.id()).and_then(Option::as_ref)
                {
                    (right, value)
                } else if let Some(value) =
                    context.constants.get(&right.id()).and_then(Option::as_ref)
                {
                    (left, value)
                } else {
                    // A symbolic product is keyed by its reading (rule W).
                    add_atom_weight(
                        terms,
                        IntegerAffineAtom::Nonlinear(node.read_through().id()),
                        weight,
                    )?;
                    continue;
                };
                if !charge_integer_product(&weight, factor) {
                    return None;
                }
                if !add_weight(&mut weights, child.id(), weight * factor) {
                    return None;
                }
            }
        }
    }
    Some(())
}

fn add_atom_weight(
    terms: &mut BTreeMap<IntegerAffineAtom, BigInt>,
    atom: IntegerAffineAtom,
    weight: BigInt,
) -> Option<()> {
    let existing = terms.get(&atom).map_or(0, |value| value.bits() as usize);
    if crate::instrumentation::deadline_exceeded_with_work(existing + weight.bits() as usize + 1) {
        return None;
    }
    let merged = terms.remove(&atom).unwrap_or_else(BigInt::zero) + weight;
    if !merged.is_zero() {
        terms.insert(atom, merged);
    }
    Some(())
}

fn add_weight(weights: &mut HashMap<u64, BigInt>, id: u64, weight: BigInt) -> bool {
    let existing = weights.get(&id).map_or(0, |value| value.bits() as usize);
    if crate::instrumentation::deadline_exceeded_with_work(existing + weight.bits() as usize + 1) {
        return false;
    }
    let merged = weights.remove(&id).unwrap_or_else(BigInt::zero) + weight;
    if !merged.is_zero() {
        weights.insert(id, merged);
    }
    true
}

#[cfg(test)]
mod tests {
    use crate::kernel::MachineBinaryOp;
    use crate::kernel::Variable;

    use super::*;

    #[test]
    fn truncating_integer_nodes_are_not_affine_division_laws() {
        let x: crate::kernel::SharedIntegerTerm = IntegerTerm::var(Variable(91003)).into();
        for term in [
            IntegerTerm::TruncatingQuotient(x.clone(), x.clone()),
            IntegerTerm::TruncatingRemainder(x.clone(), x),
        ] {
            let proposition = Proposition::ConditionIs(
                ConditionTerm::IntegerEqual(term.into(), IntegerTerm::constant_i64(1).into()),
                true,
            );
            let claim = integer_affine_claim(&proposition).unwrap();
            assert_eq!(claim.terms.len(), 1);
            let certificate = IntegerArithmeticCertificate {
                nodes: vec![IntegerArithmeticNode::Trivial { result: claim }],
                conclusion: 0,
            };
            assert!(certificate.check(&proposition, &[]).is_err());
        }
    }

    #[test]
    fn integer_affine_graph_collection_stops_at_the_active_budget() {
        use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};
        let mut expression = IntegerTerm::var(Variable(30_000));
        for _ in 0..64 {
            expression = IntegerTerm::add(expression.clone(), expression.clone());
        }
        let goal = proposition(ConditionTerm::integer_less_equal(
            expression,
            IntegerTerm::constant_i64(0),
        ));
        instrumentation::with_tactic_work_limits(
            TacticWorkLimits {
                simple: 16,
                smart: 16,
                control: 16,
            },
            || {
                let tactic = TacticEvent {
                    source_tactic_path: None,
                    claim: "integer budget".into(),
                    tactic_index: 0,
                    tactic_name: "arithmetic_certificate".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                assert!(integer_affine_claim(&goal).is_none());
                instrumentation::emit(VerificationEvent::TacticFailed(tactic));
            },
        );
    }

    fn variable(id: u64) -> IntegerTerm {
        IntegerTerm::Variable(Variable(id))
    }

    fn proposition(condition: ConditionTerm) -> Proposition {
        Proposition::ConditionIs(condition, true)
    }

    fn claim(proposition: &Proposition) -> IntegerAffineClaim {
        integer_affine_claim(proposition).expect("integer proposition should be affine")
    }

    fn premise(index: usize, proposition: &Proposition) -> IntegerArithmeticNode {
        IntegerArithmeticNode::Premise {
            index,
            result: claim(proposition),
        }
    }

    #[test]
    fn machine_observations_are_sorted_opaque_affine_atoms() {
        use crate::kernel::{MachineIntegerType, MachineTerm};
        let observe = |ty, bits| IntegerTerm::from_machine(ty, bits).unwrap();
        let bits = MachineTerm::Variable(Variable(490));
        let x = observe(MachineIntegerType::Int32, bits.clone());
        let same = observe(MachineIntegerType::Int32, bits.clone());
        let unsigned = observe(MachineIntegerType::UInt32, bits.clone());
        let goal = proposition(ConditionTerm::integer_equal(
            IntegerTerm::subtract(IntegerTerm::add(x.clone(), variable(491)), same),
            variable(491),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial {
                result: claim(&goal),
            }],
            conclusion: 0,
        };
        assert!(certificate.check(&goal, &[]).is_ok());
        let wrong_signedness = proposition(ConditionTerm::integer_equal(x.clone(), unsigned));
        assert!(certificate.check(&wrong_signedness, &[]).is_err());

        let y_bits = MachineTerm::Variable(Variable(492));
        let y = observe(MachineIntegerType::Int32, y_bits.clone());
        let machine_sum = observe(
            MachineIntegerType::Int32,
            binary_node!(Int32, Add, Box::new(bits), Box::new(y_bits)),
        );
        let unchecked_distribution = proposition(ConditionTerm::integer_equal(
            machine_sum,
            IntegerTerm::add(x, y),
        ));
        let forged = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial {
                result: claim(&unchecked_distribution),
            }],
            conclusion: 0,
        };
        assert!(forged.check(&unchecked_distribution, &[]).is_err());
    }

    fn int32_fold(
        start: u32,
        end: u32,
        accumulator: u64,
        item: u64,
        body: IntegerTerm,
    ) -> IntegerTerm {
        use crate::kernel::{IntegerRangeFoldIndex, SharedIntegerRangeEndpoint};
        IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Int32 {
                start: SharedIntegerRangeEndpoint::intern(crate::kernel::MachineTerm::constant(
                    start,
                )),
                end: SharedIntegerRangeEndpoint::intern(crate::kernel::MachineTerm::constant(end)),
            },
            IntegerTerm::constant_i64(0),
            Variable(accumulator),
            Variable(item),
            body,
        )
    }

    fn integer_fold(
        start: i64,
        end: i64,
        accumulator: u64,
        item: u64,
        body: IntegerTerm,
    ) -> IntegerTerm {
        use crate::kernel::IntegerRangeFoldIndex;
        IntegerTerm::range_fold(
            IntegerRangeFoldIndex::Integer {
                start: IntegerTerm::constant_i64(start).into(),
                end: IntegerTerm::constant_i64(end).into(),
            },
            IntegerTerm::constant_i64(0),
            Variable(accumulator),
            Variable(item),
            body,
        )
    }

    fn fold_body(accumulator: u64, item: u64) -> IntegerTerm {
        IntegerTerm::add(
            IntegerTerm::var(Variable(accumulator)),
            IntegerTerm::var(Variable(item)),
        )
    }

    fn machine_item(item: u64) -> IntegerTerm {
        IntegerTerm::from_machine(
            crate::kernel::MachineIntegerType::Int32,
            crate::kernel::MachineTerm::Variable(Variable(item)),
        )
        .expect("a symbolic Int32 item should be a machine observation")
    }

    fn machine_fold_body(accumulator: u64, item: u64) -> IntegerTerm {
        IntegerTerm::add(IntegerTerm::var(Variable(accumulator)), machine_item(item))
    }

    #[test]
    fn alpha_renamed_folds_cancel_as_one_checked_affine_atom() {
        let left = int32_fold(0, 8, 100, 101, machine_fold_body(100, 101));
        let right = int32_fold(0, 8, 200, 201, machine_fold_body(200, 201));
        let goal = proposition(ConditionTerm::IntegerEqual(left.into(), right.into()));
        let normalized = claim(&goal);
        assert!(normalized.terms.is_empty());
        assert!(normalized.constant.is_zero());

        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial { result: normalized }],
            conclusion: 0,
        };
        certificate.check(&goal, &[]).unwrap();
    }

    #[test]
    fn fold_atom_identity_keeps_endpoints_body_and_carrier_distinct() {
        let baseline = int32_fold(0, 8, 300, 301, machine_fold_body(300, 301));
        let changed_end = int32_fold(0, 9, 300, 301, machine_fold_body(300, 301));
        let changed_body = int32_fold(
            0,
            8,
            300,
            301,
            IntegerTerm::subtract(IntegerTerm::var(Variable(300)), machine_item(301)),
        );
        let changed_carrier = integer_fold(0, 8, 300, 301, fold_body(300, 301));

        for other in [changed_end, changed_body, changed_carrier] {
            let goal = proposition(ConditionTerm::IntegerEqual(
                baseline.clone().into(),
                other.into(),
            ));
            assert_eq!(claim(&goal).terms.len(), 2);
        }
    }

    #[test]
    fn fold_atom_tampering_is_rejected_at_the_certificate_boundary() {
        let source_fold = int32_fold(0, 8, 400, 401, machine_fold_body(400, 401));
        let changed_fold = int32_fold(0, 9, 400, 401, machine_fold_body(400, 401));
        let source = proposition(ConditionTerm::IntegerLessEqual(
            source_fold.into(),
            IntegerTerm::constant_i64(0).into(),
        ));
        let forged = proposition(ConditionTerm::IntegerLessEqual(
            changed_fold.into(),
            IntegerTerm::constant_i64(0).into(),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Premise {
                index: 0,
                result: claim(&forged),
            }],
            conclusion: 0,
        };
        assert_eq!(
            certificate.check(&source, std::slice::from_ref(&source)),
            Err(IntegerArithmeticCheckError::NodeResultMismatch(0))
        );
    }

    #[test]
    fn fold_atom_identity_retains_the_exact_memory_state() {
        use crate::kernel::{
            IntegerRangeFoldIndex, MachineIntegerType, MachineTerm, Memory, Pointer,
            PointerOffsetTerm, ProgramValue, SharedIntegerRangeEndpoint, SharedMachineIntegerTerm,
        };
        let pointer = Pointer {
            block: "affine-fold-retained_state".into(),
            offset: PointerOffsetTerm::Constant(0),
        };
        let before =
            crate::kernel::intern_memory(Memory::new().with_block("affine-fold-retained_state", 8));
        let after = crate::kernel::intern_memory(before.as_ref().clone().store(
            pointer.clone(),
            ProgramValue::Int32(MachineTerm::constant(7)),
        ));
        let load_fold =
            |memory: &crate::kernel::SharedMemory, accumulator: u64, item: u64| -> IntegerTerm {
                IntegerTerm::range_fold(
                    IntegerRangeFoldIndex::Int32 {
                        start: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(0)),
                        end: SharedIntegerRangeEndpoint::intern(MachineTerm::constant(2)),
                    },
                    IntegerTerm::constant_i64(0),
                    Variable(accumulator),
                    Variable(item),
                    IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
                        MachineIntegerType::Int32,
                        MachineTerm::MemoryLoad(
                            memory.clone(),
                            Box::new(pointer.clone()),
                            crate::kernel::LoadKind::Int32,
                        ),
                    )),
                )
            };
        let before_fold = load_fold(&before, 700, 701);
        let renamed_before_fold = load_fold(&before, 800, 801);
        let after_fold = load_fold(&after, 800, 801);

        let renamed_goal = proposition(ConditionTerm::IntegerEqual(
            before_fold.clone().into(),
            renamed_before_fold.into(),
        ));
        assert!(claim(&renamed_goal).terms.is_empty());

        let changed_state_goal = proposition(ConditionTerm::IntegerEqual(
            before_fold.into(),
            after_fold.into(),
        ));
        assert_eq!(claim(&changed_state_goal).terms.len(), 2);
    }

    #[test]
    fn context_free_trivial_integer_claims_check() {
        let x = variable(1);
        let successor = IntegerTerm::Add(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
        );
        let increasing = proposition(ConditionTerm::IntegerGreaterThan(
            crate::kernel::SharedIntegerTerm::from(successor),
            crate::kernel::SharedIntegerTerm::from(x.clone()),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial {
                result: claim(&increasing),
            }],
            conclusion: 0,
        };
        certificate.check(&increasing, &[]).unwrap();

        let zero = IntegerTerm::Subtract(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(x),
        );
        let identity = proposition(ConditionTerm::IntegerEqual(
            crate::kernel::SharedIntegerTerm::from(zero),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial {
                result: claim(&identity),
            }],
            conclusion: 0,
        };
        certificate.check(&identity, &[]).unwrap();
    }

    #[test]
    fn scaled_bounds_can_close_an_integer_equality() {
        let x = variable(2);
        let lower = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
            crate::kernel::SharedIntegerTerm::from(x.clone()),
        ));
        let upper = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let goal = proposition(ConditionTerm::IntegerEqual(
            crate::kernel::SharedIntegerTerm::from(x),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let lower_node = premise(0, &lower);
        let upper_node = premise(1, &upper);
        let equality = IntegerAffineClaim {
            relation: IntegerAffineRelation::Equal,
            terms: BTreeMap::from([(IntegerAffineAtom::Variable(Variable(2)), BigInt::one())]),
            constant: BigInt::zero(),
        };
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                lower_node,
                upper_node,
                IntegerArithmeticNode::EqualityFromBounds {
                    lower: 1,
                    upper: 0,
                    result: equality,
                },
            ],
            conclusion: 2,
        };
        certificate.check(&goal, &[lower, upper]).unwrap();
    }

    #[test]
    fn equality_can_supply_one_order_direction_and_be_added() {
        let x = IntegerTerm::Variable(Variable(4));
        let y = IntegerTerm::Variable(Variable(5));
        let equality = proposition(ConditionTerm::IntegerEqual(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(y.clone()),
        ));
        let goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::Add(
                crate::kernel::SharedIntegerTerm::from(x),
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
            )),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::Add(
                crate::kernel::SharedIntegerTerm::from(y),
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
            )),
        ));
        let equality_node = premise(0, &equality);
        let direction = IntegerAffineClaim {
            relation: IntegerAffineRelation::LessEqual,
            terms: BTreeMap::from([
                (IntegerAffineAtom::Variable(Variable(4)), BigInt::one()),
                (IntegerAffineAtom::Variable(Variable(5)), BigInt::from(-1)),
            ]),
            constant: BigInt::zero(),
        };
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                equality_node,
                IntegerArithmeticNode::EqualityToLessEqual {
                    source: 0,
                    reverse: false,
                    result: direction.clone(),
                },
                IntegerArithmeticNode::Trivial {
                    result: IntegerAffineClaim {
                        relation: IntegerAffineRelation::LessEqual,
                        terms: BTreeMap::new(),
                        constant: BigInt::zero(),
                    },
                },
                IntegerArithmeticNode::Add {
                    left: 1,
                    right: 2,
                    result: direction,
                },
            ],
            conclusion: 3,
        };
        certificate.check(&goal, &[equality]).unwrap();
    }

    #[test]
    fn tampering_with_premise_result_or_inequality_scale_is_rejected() {
        let x = variable(3);
        let premise_proposition = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(5)),
        ));
        let goal = premise_proposition.clone();
        let mut bad_claim = claim(&premise_proposition);
        bad_claim.constant += BigInt::one();
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Premise {
                index: 0,
                result: bad_claim,
            }],
            conclusion: 0,
        };
        assert_eq!(
            certificate.check(&goal, std::slice::from_ref(&premise_proposition)),
            Err(IntegerArithmeticCheckError::NodeResultMismatch(0))
        );

        let source = premise(0, &premise_proposition);
        let scaled_result = IntegerAffineClaim {
            relation: IntegerAffineRelation::LessEqual,
            terms: BTreeMap::from([(IntegerAffineAtom::Variable(Variable(3)), BigInt::from(2))]),
            constant: BigInt::from(-10),
        };
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                source,
                IntegerArithmeticNode::Scale {
                    source: 0,
                    coefficient: BigInt::from(-2),
                    result: scaled_result,
                },
            ],
            conclusion: 1,
        };
        assert_eq!(
            certificate.check(&goal, &[premise_proposition]),
            Err(IntegerArithmeticCheckError::InvalidCoefficient(1))
        );
    }

    #[test]
    fn negated_integer_disequality_keeps_its_affine_equality() {
        let left = crate::kernel::SharedIntegerTerm::from(variable(995480));
        let right = crate::kernel::SharedIntegerTerm::from(variable(995481));
        let equality = Proposition::ConditionIs(
            ConditionTerm::IntegerEqual(left.clone(), right.clone()),
            true,
        );
        let unequal = ConditionTerm::IntegerNotEqual(left, right);
        let expected = integer_affine_claim(&equality).unwrap();
        for premise in [
            Proposition::ConditionIs(unequal.clone(), false),
            Proposition::Not(Box::new(Proposition::ConditionIs(unequal.clone(), true))),
        ] {
            assert_eq!(integer_affine_claim(&premise), Some(expected.clone()));
        }
        assert!(integer_affine_claim(&Proposition::ConditionIs(unequal, true)).is_none());
    }

    #[test]
    fn deep_integer_terms_are_collected_iteratively() {
        let x = variable(8);
        let mut expression = x.clone();
        for _ in 0..2_048 {
            expression = IntegerTerm::Add(
                crate::kernel::SharedIntegerTerm::from(expression),
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(1)),
            );
        }
        let goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(expression),
            crate::kernel::SharedIntegerTerm::from(x),
        ));
        let result = claim(&goal);
        assert!(result.terms.is_empty());
        assert_eq!(result.constant, BigInt::from(2_048));
    }

    #[test]
    fn nonlinear_integer_terms_are_opaque_and_not_zero() {
        let left = variable(10);
        let right = variable(11);
        let goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::Multiply(
                crate::kernel::SharedIntegerTerm::from(left),
                crate::kernel::SharedIntegerTerm::from(right),
            )),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        assert_eq!(
            IntegerArithmeticCertificate {
                nodes: vec![IntegerArithmeticNode::Trivial {
                    result: claim(&goal)
                }],
                conclusion: 0,
            }
            .check(&goal, &[]),
            Err(IntegerArithmeticCheckError::NodeResultMismatch(0))
        );
    }

    #[test]
    fn large_integer_scale_accounts_for_product_bit_work() {
        let x = IntegerTerm::Variable(Variable(12));
        let premise_proposition = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let narrow_goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(x.clone()),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let wide: BigInt = BigInt::one() << 1_024usize;
        let wide_goal = proposition(ConditionTerm::IntegerLessEqual(
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::Multiply(
                crate::kernel::SharedIntegerTerm::from(IntegerTerm::Constant(wide.clone())),
                crate::kernel::SharedIntegerTerm::from(x),
            )),
            crate::kernel::SharedIntegerTerm::from(IntegerTerm::constant_i64(0)),
        ));
        let narrow_claim = claim(&narrow_goal);
        let wide_claim = claim(&wide_goal);
        let narrow_certificate = IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &premise_proposition),
                IntegerArithmeticNode::Scale {
                    source: 0,
                    coefficient: BigInt::one(),
                    result: narrow_claim,
                },
            ],
            conclusion: 1,
        };
        let wide_certificate = IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &premise_proposition),
                IntegerArithmeticNode::Scale {
                    source: 0,
                    coefficient: wide.clone(),
                    result: wide_claim,
                },
            ],
            conclusion: 1,
        };
        let (_, narrow_work) = crate::instrumentation::measure_deterministic_work(|| {
            narrow_certificate.check(&narrow_goal, std::slice::from_ref(&premise_proposition))
        });
        let (_, wide_work) = crate::instrumentation::measure_deterministic_work(|| {
            wide_certificate.check(&wide_goal, std::slice::from_ref(&premise_proposition))
        });
        assert!(wide_work > narrow_work);
    }

    fn less_equal(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        proposition(ConditionTerm::integer_less_equal(left, right))
    }

    fn scaled(id: u64, coefficient: i64) -> IntegerTerm {
        IntegerTerm::multiply(IntegerTerm::constant_i64(coefficient), variable(id))
    }

    fn constant_claim(relation: IntegerAffineRelation, constant: i64) -> IntegerAffineClaim {
        IntegerAffineClaim {
            relation,
            terms: BTreeMap::new(),
            constant: BigInt::from(constant),
        }
    }

    fn negated_goal_claim(goal: &Proposition) -> IntegerAffineClaim {
        let mut negated = negate_claim(&claim(goal), IntegerAffineRelation::LessEqual);
        negated.constant += BigInt::one();
        negated
    }

    #[test]
    fn operation_bounds_hold_only_for_operations_by_positive_constants() {
        use crate::kernel::{MachineIntegerType, MachineTerm, SharedMachineIntegerTerm};
        let x = || Box::new(MachineTerm::Variable(Variable(97201)));
        let operand = IntegerTerm::Machine(SharedMachineIntegerTerm::intern(
            MachineIntegerType::UInt64,
            *x(),
        ));
        let machine = |ty, value| SharedMachineIntegerTerm::intern(ty, value);
        let quotient = machine(
            MachineIntegerType::UInt64,
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Divide,
                left: x(),
                right: Box::new(MachineTerm::uint64_constant(1000)),
            },
        );
        let observed = IntegerTerm::Machine(quotient.clone());
        let thousand = |term: IntegerTerm| {
            IntegerTerm::Multiply(IntegerTerm::constant_i64(1000).into(), term.into())
        };
        // `1000 * (x / 1000) <= x` and `x <= 1000 * (x / 1000) + 999`.
        assert_eq!(
            operation_bound(&quotient, false),
            Some(less_equal(thousand(observed.clone()), operand.clone()))
        );
        assert_eq!(
            operation_bound(&quotient, true),
            Some(less_equal(
                operand.clone(),
                IntegerTerm::Add(
                    thousand(observed.clone()).into(),
                    IntegerTerm::constant_i64(999).into()
                )
            ))
        );
        // `x >> 32` is `x / 2^32`.
        let shifted = machine(
            MachineIntegerType::UInt64,
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::ShiftRight,
                left: x(),
                right: Box::new(MachineTerm::int64_constant(32)),
            },
        );
        let two_to_32 = IntegerTerm::Multiply(
            IntegerTerm::constant_i64(4_294_967_296).into(),
            IntegerTerm::Machine(shifted.clone()).into(),
        );
        assert_eq!(
            operation_bound(&shifted, false),
            Some(less_equal(two_to_32, operand.clone()))
        );
        // A remainder has only its upper bound; the type range is its lower.
        let remainder = machine(
            MachineIntegerType::UInt64,
            MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Remainder,
                left: x(),
                right: Box::new(MachineTerm::uint64_constant(10)),
            },
        );
        assert_eq!(
            operation_bound(&remainder, true),
            Some(less_equal(
                IntegerTerm::Machine(remainder.clone()),
                IntegerTerm::constant_i64(9)
            ))
        );
        assert_eq!(operation_bound(&remainder, false), None);
        // No bound for a zero divisor, a shift by the width or more, a
        // symbolic divisor, a signed quotient by a negative divisor (the
        // word `0xfffffc18` is `-1000`), or a quotient read at the other
        // signedness.
        for value in [
            machine(
                MachineIntegerType::UInt64,
                MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Divide,
                    left: x(),
                    right: Box::new(MachineTerm::uint64_constant(0)),
                },
            ),
            machine(
                MachineIntegerType::UInt64,
                MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::ShiftRight,
                    left: x(),
                    right: Box::new(MachineTerm::int64_constant(64)),
                },
            ),
            machine(
                MachineIntegerType::UInt64,
                MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Divide,
                    left: x(),
                    right: Box::new(MachineTerm::Variable(Variable(97202))),
                },
            ),
            machine(
                MachineIntegerType::Int32,
                binary_node!(
                    Int32,
                    Divide,
                    x(),
                    Box::new(MachineTerm::constant(-1000i32 as u32))
                ),
            ),
            machine(
                MachineIntegerType::UInt32,
                binary_node!(Int32, Divide, x(), Box::new(MachineTerm::constant(1000))),
            ),
        ] {
            assert_eq!(operation_bound(&value, false), None);
            assert_eq!(operation_bound(&value, true), None);
        }
        // The checker recomputes the bound: a tighter claim is refused.
        let goal = less_equal(operand.clone(), IntegerTerm::constant_i64(0));
        let forged = claim(&less_equal(
            operand.clone(),
            IntegerTerm::Add(
                thousand(observed.clone()).into(),
                IntegerTerm::constant_i64(998).into(),
            ),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::OperationBound {
                value: observed,
                upper: true,
                result: forged,
            }],
            conclusion: 0,
        };
        assert_eq!(
            certificate.check(&goal, &[]),
            Err(IntegerArithmeticCheckError::NodeResultMismatch(0))
        );
    }

    #[test]
    fn a_disequality_bounds_only_at_a_type_endpoint() {
        use crate::kernel::{MachineIntegerType, MachineTerm, SharedMachineIntegerTerm};
        let value =
            |ty| SharedMachineIntegerTerm::intern(ty, MachineTerm::Variable(Variable(97301)));
        let differs = |ty, constant: i64| {
            Proposition::ConditionIs(
                ConditionTerm::integer_equal(
                    IntegerTerm::Machine(value(ty)),
                    IntegerTerm::constant_i64(constant),
                ),
                false,
            )
        };
        let observed = |ty| IntegerTerm::Machine(value(ty));
        assert_eq!(
            excluded_type_bound(&differs(MachineIntegerType::UInt64, 0)),
            Some(less_equal(
                IntegerTerm::constant_i64(1),
                observed(MachineIntegerType::UInt64)
            ))
        );
        assert_eq!(
            excluded_type_bound(&differs(MachineIntegerType::Int32, 2_147_483_647)),
            Some(less_equal(
                observed(MachineIntegerType::Int32),
                IntegerTerm::constant_i64(2_147_483_646)
            ))
        );
        assert_eq!(
            excluded_type_bound(&differs(MachineIntegerType::UInt64, 5)),
            None
        );
        assert_eq!(
            excluded_type_bound(&differs(MachineIntegerType::Int32, 0)),
            None
        );
        let minimum = IntegerTerm::Subtract(
            IntegerTerm::constant_i64(-2147483647).into(),
            IntegerTerm::constant_i64(1).into(),
        );
        for reversed in [false, true] {
            let mut sides = [observed(MachineIntegerType::Int32), minimum.clone()];
            if reversed {
                sides.swap(0, 1);
            }
            let [left, right] = sides;
            let premise = Proposition::ConditionIs(
                ConditionTerm::IntegerNotEqual(left.into(), right.into()),
                true,
            );
            assert_eq!(
                excluded_type_bound(&premise),
                Some(less_equal(
                    IntegerTerm::constant_i64(-2147483647),
                    observed(MachineIntegerType::Int32),
                ))
            );
        }
        // An equality is no disequality.
        let equal = Proposition::ConditionIs(
            ConditionTerm::integer_equal(
                observed(MachineIntegerType::UInt64),
                IntegerTerm::constant_i64(0),
            ),
            true,
        );
        assert_eq!(excluded_type_bound(&equal), None);
    }

    fn strict_from_disequal(
        bound: Proposition,
        disequal: Proposition,
        goal: &Proposition,
    ) -> Result<(), IntegerArithmeticCheckError> {
        let mut strict = claim(&bound);
        strict.constant += BigInt::one();
        IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &bound),
                IntegerArithmeticNode::StrictFromDisequal {
                    bound: 0,
                    disequal: 1,
                    result: strict,
                },
            ],
            conclusion: 1,
        }
        .check(goal, &[bound, disequal])
    }

    fn not_equal(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::IntegerNotEqual(left.into(), right.into()),
            true,
        )
    }

    #[test]
    fn a_disequality_makes_a_bound_of_its_difference_strict() {
        use crate::kernel::{CompareRelation, MachineIntegerType, MachineTerm};
        let (a, b) = (variable(97401), variable(97402));
        let strict = proposition(ConditionTerm::IntegerLessThan(
            a.clone().into(),
            b.clone().into(),
        ));
        // Either side of the disequality first, and as `not (a == b)`.
        for disequal in [
            not_equal(a.clone(), b.clone()),
            not_equal(b.clone(), a.clone()),
            Proposition::ConditionIs(ConditionTerm::integer_equal(a.clone(), b.clone()), false),
        ] {
            assert_eq!(
                strict_from_disequal(less_equal(a.clone(), b.clone()), disequal, &strict),
                Ok(())
            );
        }
        // A constant side: `x <= 5`, `x != 5` gives `x < 5`.
        assert_eq!(
            strict_from_disequal(
                less_equal(a.clone(), IntegerTerm::constant_i64(5)),
                not_equal(IntegerTerm::constant_i64(5), a.clone()),
                &proposition(ConditionTerm::IntegerLessThan(
                    a.clone().into(),
                    IntegerTerm::constant_i64(5).into(),
                )),
            ),
            Ok(())
        );
        // A native `int64` disequality is read as its Integer reading.
        let word = |id| MachineTerm::Variable(Variable(id));
        let observe = |id| IntegerTerm::from_machine(MachineIntegerType::Int64, word(id)).unwrap();
        let native = Proposition::ConditionIs(
            ConditionTerm::machine_compare(
                MachineIntegerType::Int64,
                CompareRelation::Equal,
                word(97403),
                word(97404),
            ),
            false,
        );
        assert_eq!(
            strict_from_disequal(
                less_equal(observe(97403), observe(97404)),
                native,
                &proposition(ConditionTerm::IntegerLessThan(
                    observe(97403).into(),
                    observe(97404).into(),
                )),
            ),
            Ok(())
        );
    }

    #[test]
    fn a_strict_bound_needs_the_disequality_of_its_own_difference() {
        let (a, b, c) = (variable(97411), variable(97412), variable(97413));
        let strict = proposition(ConditionTerm::IntegerLessThan(
            a.clone().into(),
            b.clone().into(),
        ));
        // Another difference, a shifted one, an equality and a bound in
        // place of the disequality are refused.
        for disequal in [
            not_equal(a.clone(), c.clone()),
            not_equal(
                a.clone(),
                IntegerTerm::add(b.clone(), IntegerTerm::constant_i64(1)),
            ),
            proposition(ConditionTerm::integer_equal(a.clone(), b.clone())),
            less_equal(a.clone(), b.clone()),
        ] {
            assert!(
                strict_from_disequal(less_equal(a.clone(), b.clone()), disequal.clone(), &strict)
                    .is_err(),
                "{disequal:?}"
            );
        }
        // The result is exactly one stronger than the bound.
        let bound = less_equal(a.clone(), b.clone());
        let mut twice = claim(&bound);
        twice.constant += BigInt::from(2);
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &bound),
                IntegerArithmeticNode::StrictFromDisequal {
                    bound: 0,
                    disequal: 1,
                    result: twice,
                },
            ],
            conclusion: 1,
        };
        assert_eq!(
            certificate.check(&strict, &[bound.clone(), not_equal(a.clone(), b.clone())]),
            Err(IntegerArithmeticCheckError::NodeResultMismatch(1))
        );
        // An equality bound is no non-strict bound.
        let equality = proposition(ConditionTerm::integer_equal(a.clone(), b.clone()));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &equality),
                IntegerArithmeticNode::StrictFromDisequal {
                    bound: 0,
                    disequal: 1,
                    result: claim(&strict),
                },
            ],
            conclusion: 1,
        };
        assert_eq!(
            certificate.check(&strict, &[equality, not_equal(a, b)]),
            Err(IntegerArithmeticCheckError::InvalidRelation(1))
        );
    }

    #[test]
    fn type_range_nodes_state_exactly_the_machine_type_bounds() {
        use crate::kernel::{MachineIntegerType, MachineTerm, SharedMachineIntegerTerm};
        let word = SharedMachineIntegerTerm::intern(
            MachineIntegerType::UInt32,
            MachineTerm::Variable(Variable(97101)),
        );
        let observed = IntegerTerm::Machine(word.clone());
        // `x <= 4294967295` and `0 <= x` give `x - 4294967295 <= 0` from the
        // negated goal `x >= 4294967296`.
        let goal = less_equal(observed.clone(), IntegerTerm::constant_i64(4_294_967_295));
        let upper = machine_type_range_claim(&word, true).unwrap();
        let certificate = |value: IntegerTerm, upper_bound: bool, result: IntegerAffineClaim| {
            IntegerArithmeticCertificate {
                nodes: vec![IntegerArithmeticNode::TypeRange {
                    value,
                    upper: upper_bound,
                    result,
                }],
                conclusion: 0,
            }
        };
        assert_eq!(
            certificate(observed.clone(), true, upper.clone()).check(&goal, &[]),
            Ok(())
        );
        // A tighter bound than the type gives is not a type range.
        let tighter = less_equal(observed.clone(), IntegerTerm::constant_i64(4_294_967_294));
        assert!(
            certificate(observed.clone(), true, claim(&tighter))
                .check(&tighter, &[])
                .is_err()
        );
        // The lower bound does not stand for the upper one, and a term that
        // is not a machine observation has no type range.
        assert!(
            certificate(observed.clone(), false, upper.clone())
                .check(&goal, &[])
                .is_err()
        );
        assert!(
            certificate(variable(97102), true, upper)
                .check(&goal, &[])
                .is_err()
        );
        // A signed observation of the same carrier has its own range.
        let signed = SharedMachineIntegerTerm::intern(
            MachineIntegerType::Int32,
            MachineTerm::Variable(Variable(97101)),
        );
        let signed_goal = less_equal(
            IntegerTerm::constant_i64(-2_147_483_648),
            IntegerTerm::Machine(signed.clone()),
        );
        assert_eq!(
            certificate(
                IntegerTerm::Machine(signed.clone()),
                false,
                machine_type_range_claim(&signed, false).unwrap(),
            )
            .check(&signed_goal, &[]),
            Ok(())
        );
    }

    #[test]
    fn negated_goal_refutation_proves_the_goal() {
        // 2x <= 10 proves x <= 5: assume x >= 6, double it, and add.
        let goal = less_equal(variable(97001), IntegerTerm::constant_i64(5));
        let premise_proposition = less_equal(scaled(97001, 2), IntegerTerm::constant_i64(10));
        let negated = negated_goal_claim(&goal);
        let doubled = scale_claim(&negated, &BigInt::from(2)).unwrap();
        let premise_claim = claim(&premise_proposition);
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &premise_proposition),
                IntegerArithmeticNode::NegatedGoal { result: negated },
                IntegerArithmeticNode::Scale {
                    source: 1,
                    coefficient: BigInt::from(2),
                    result: doubled.clone(),
                },
                IntegerArithmeticNode::Add {
                    left: 0,
                    right: 2,
                    result: add_claim(&premise_claim, &doubled),
                },
            ],
            conclusion: 3,
        };
        assert_eq!(
            certificate.nodes.last().map(|node| match node {
                IntegerArithmeticNode::Add { result, .. } => result.clone(),
                _ => unreachable!(),
            }),
            Some(constant_claim(IntegerAffineRelation::LessEqual, 2))
        );
        assert_eq!(
            certificate.check(&goal, std::slice::from_ref(&premise_proposition)),
            Ok(())
        );
        // The same refutation does not prove a stronger goal.
        let stronger = less_equal(variable(97001), IntegerTerm::constant_i64(4));
        assert!(
            certificate
                .check(&stronger, std::slice::from_ref(&premise_proposition))
                .is_err()
        );
    }

    #[test]
    fn negated_goal_must_state_the_exact_integer_negation() {
        let goal = less_equal(variable(97002), IntegerTerm::constant_i64(5));
        // `x >= 5` is the rational negation, not the integer one (`x >= 6`).
        let weak = negate_claim(&claim(&goal), IntegerAffineRelation::LessEqual);
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::NegatedGoal { result: weak }],
            conclusion: 0,
        };
        assert_eq!(
            certificate.check(&goal, &[]),
            Err(IntegerArithmeticCheckError::NodeResultMismatch(0))
        );
    }

    #[test]
    fn negated_goal_refuses_an_equality_goal() {
        let goal = proposition(ConditionTerm::integer_equal(
            variable(97003),
            IntegerTerm::constant_i64(5),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::NegatedGoal {
                result: constant_claim(IntegerAffineRelation::LessEqual, 0),
            }],
            conclusion: 0,
        };
        assert_eq!(
            certificate.check(&goal, &[]),
            Err(IntegerArithmeticCheckError::NegatedGoalUnsupported(0))
        );
    }

    #[test]
    fn contradictory_premises_prove_any_supported_goal() {
        let x = || variable(97004);
        let low = less_equal(x(), IntegerTerm::constant_i64(0));
        let high = less_equal(IntegerTerm::constant_i64(1), x());
        let goal = less_equal(variable(97005), IntegerTerm::constant_i64(-7));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &low),
                premise(1, &high),
                IntegerArithmeticNode::Add {
                    left: 0,
                    right: 1,
                    result: constant_claim(IntegerAffineRelation::LessEqual, 1),
                },
            ],
            conclusion: 2,
        };
        assert_eq!(
            certificate.check(&goal, &[low.clone(), high.clone()]),
            Ok(())
        );
        // A consistent non-goal conclusion still does not follow.
        let consistent = IntegerArithmeticCertificate {
            nodes: vec![premise(0, &low)],
            conclusion: 0,
        };
        assert_eq!(
            consistent.check(&goal, &[low, high]),
            Err(IntegerArithmeticCheckError::DoesNotFollow)
        );
    }

    #[test]
    fn divide_rounds_the_constant_toward_the_integer_bound() {
        // 2x <= 5 gives x <= 2 over the integers.
        let premise_proposition = less_equal(scaled(97006, 2), IntegerTerm::constant_i64(5));
        let goal = less_equal(variable(97006), IntegerTerm::constant_i64(2));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &premise_proposition),
                IntegerArithmeticNode::Divide {
                    source: 0,
                    divisor: BigInt::from(2),
                    result: claim(&goal),
                },
            ],
            conclusion: 1,
        };
        assert_eq!(
            certificate.check(&goal, std::slice::from_ref(&premise_proposition)),
            Ok(())
        );
        // Claiming the unrounded x <= 3 is a different result and is refused,
        // as is a stronger x <= 1.
        for wrong in [3, 1] {
            let wrong_goal = less_equal(variable(97006), IntegerTerm::constant_i64(wrong));
            let certificate = IntegerArithmeticCertificate {
                nodes: vec![
                    premise(0, &premise_proposition),
                    IntegerArithmeticNode::Divide {
                        source: 0,
                        divisor: BigInt::from(2),
                        result: claim(&wrong_goal),
                    },
                ],
                conclusion: 1,
            };
            assert_eq!(
                certificate.check(&wrong_goal, std::slice::from_ref(&premise_proposition)),
                Err(IntegerArithmeticCheckError::NodeResultMismatch(1))
            );
        }
    }

    #[test]
    fn divide_requires_a_positive_exact_common_factor() {
        let premise_proposition = less_equal(scaled(97007, 3), IntegerTerm::constant_i64(5));
        for divisor in [2, 0, -3] {
            let certificate = IntegerArithmeticCertificate {
                nodes: vec![
                    premise(0, &premise_proposition),
                    IntegerArithmeticNode::Divide {
                        source: 0,
                        divisor: BigInt::from(divisor),
                        result: claim(&premise_proposition),
                    },
                ],
                conclusion: 1,
            };
            assert_eq!(
                certificate.check(
                    &premise_proposition,
                    std::slice::from_ref(&premise_proposition)
                ),
                Err(IntegerArithmeticCheckError::InvalidDivisor(1)),
                "divisor {divisor}"
            );
        }
        let equality = proposition(ConditionTerm::integer_equal(
            scaled(97007, 2),
            IntegerTerm::constant_i64(4),
        ));
        let certificate = IntegerArithmeticCertificate {
            nodes: vec![
                premise(0, &equality),
                IntegerArithmeticNode::Divide {
                    source: 0,
                    divisor: BigInt::from(2),
                    result: claim(&equality),
                },
            ],
            conclusion: 1,
        };
        assert_eq!(
            certificate.check(&equality, std::slice::from_ref(&equality)),
            Err(IntegerArithmeticCheckError::InvalidRelation(1))
        );
    }

    #[test]
    fn divide_preserves_every_small_integer_model() {
        // For c*x + k <= 0 and every x in a window, the divided claim holds
        // whenever its source does, and is no weaker than the integer bound.
        let atom = IntegerAffineAtom::Variable(Variable(97008));
        for coefficient in [-6i64, -4, -3, -2, 2, 3, 4, 6] {
            for divisor in [2i64, 3] {
                if coefficient % divisor != 0 {
                    continue;
                }
                for constant in -13i64..=13 {
                    let source = IntegerAffineClaim {
                        relation: IntegerAffineRelation::LessEqual,
                        terms: BTreeMap::from([(atom.clone(), BigInt::from(coefficient))]),
                        constant: BigInt::from(constant),
                    };
                    let divided = divide_claim(&source, &BigInt::from(divisor)).unwrap();
                    let reduced = coefficient / divisor;
                    let rounded: i64 = divided.constant.clone().try_into().unwrap();
                    assert_eq!(divided.terms.get(&atom), Some(&BigInt::from(reduced)));
                    for x in -40i64..=40 {
                        let source_holds = coefficient * x + constant <= 0;
                        let result_holds = reduced * x + rounded <= 0;
                        // Sound: the source implies the result. Tight: over
                        // the integers they are equivalent.
                        assert_eq!(
                            source_holds, result_holds,
                            "{coefficient}x + {constant} <= 0 divided by {divisor}, x = {x}"
                        );
                    }
                }
            }
        }
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/integer_arithmetic/tests.rs");
    }
}
