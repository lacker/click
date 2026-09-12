//! Bounded planning for the checked signed-int32 arithmetic certificate.
//!
//! This module is deliberately a planner, not a validation oracle.  It reads
//! only the goal and the exact premise slice supplied by its caller, chooses a
//! finite local derivation, and leaves all semantic validation to the kernel
//! certificate checker.

#![allow(dead_code)]

use crate::kernel::proof::signed_arithmetic::{
    SignedArithmeticAtom, SignedArithmeticCarrier, SignedArithmeticCertificate,
    SignedArithmeticClaim, SignedArithmeticComparison, SignedArithmeticInterval,
    SignedArithmeticNode, SignedArithmeticRelation,
};
use crate::kernel::{Bitvector32Term, ConditionTerm, Proposition};
use num_bigint::BigInt;
use num_traits::{One, ToPrimitive, Zero};
use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};

const MAX_SELECTED_PREMISES: usize = 64;
const MAX_NODES: usize = 4096;
const SIGNED_MIN: i64 = i32::MIN as i64;
const SIGNED_MAX: i64 = i32::MAX as i64;

pub(in crate::surface) fn plan_signed_arithmetic_certificate(
    goal: &Proposition,
    premises: &[Proposition],
) -> Option<SignedArithmeticCertificate> {
    if premises.len() > MAX_SELECTED_PREMISES {
        return None;
    }
    let expected = signed_claim(goal)?;
    if is_trivial(&expected) {
        return Some(certificate(
            vec![SignedArithmeticNode::Trivial { result: expected }],
            0,
        ));
    }
    charge_claim_comparison(&expected)?;

    let claims = premises
        .iter()
        .enumerate()
        .filter_map(|(index, proposition)| {
            charge_work(1)?;
            signed_claim(proposition).map(|claim| (index, claim))
        })
        .collect::<Vec<_>>();

    for (index, claim) in &claims {
        charge_claim_comparison(claim)?;
        if claim == &expected {
            return Some(certificate(
                vec![SignedArithmeticNode::Premise {
                    index: *index,
                    result: claim.clone(),
                }],
                0,
            ));
        }
    }
    if comparison_terms(goal).is_some_and(|(left, right, _)| {
        !contains_machine_operation(left) && !contains_machine_operation(right)
    }) && let Some(plan) = plan_affine_from_selected_claims(premises, &claims, &expected)
    {
        return Some(plan);
    }
    if let Some(plan) = plan_affine_one_premise(&claims, &expected) {
        return Some(plan);
    }
    if let Some(plan) = plan_machine_affine_goal(goal, premises, &claims) {
        return Some(plan);
    }
    if let Some(plan) = plan_interval_goal(goal, premises, &claims) {
        return Some(plan);
    }
    None
}

fn plan_affine_from_selected_claims(
    premises: &[Proposition],
    claims: &[(usize, SignedArithmeticClaim)],
    expected: &SignedArithmeticClaim,
) -> Option<SignedArithmeticCertificate> {
    let mut planner = Planner::new(premises, claims);
    let conclusion = planner.affine_claim(expected)?;
    Some(certificate(planner.nodes, conclusion))
}

/// Classifies one explicitly named premise without trying to prove a goal.
///
/// Callers that assemble an exact premise slice must not invoke the planner
/// with a fabricated goal: a context-free/trivial goal can succeed while the
/// cited premise is completely unrelated.  Keep this predicate bounded and
/// syntactic; the actual certificate remains the kernel's authority.
pub(in crate::surface) fn signed_arithmetic_premise_supported(proposition: &Proposition) -> bool {
    signed_claim(proposition).is_some_and(|claim| charge_claim_comparison(&claim).is_some())
}

fn certificate(nodes: Vec<SignedArithmeticNode>, conclusion: usize) -> SignedArithmeticCertificate {
    SignedArithmeticCertificate { nodes, conclusion }
}

fn charge_work(units: usize) -> Option<()> {
    (!crate::instrumentation::deadline_exceeded_with_work(units.max(1))).then_some(())
}

fn signed_claim(proposition: &Proposition) -> Option<SignedArithmeticClaim> {
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
        constant += 1;
    }
    Some(SignedArithmeticClaim {
        carrier: SignedArithmeticCarrier::SignedInt32,
        relation,
        terms,
        constant,
    })
}

fn decomposed_signed_claim(proposition: &Proposition) -> Option<SignedArithmeticClaim> {
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
            let (terms, constant) = decomposed_affine_difference(left, right)?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Equal,
                terms,
                constant,
            });
        }
        (ConditionTerm::Bitvector32Equal(left, right), false) => {
            let (terms, constant) = decomposed_affine_difference(left, right)?;
            return Some(SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::Disequal,
                terms,
                constant,
            });
        }
        _ => return None,
    };
    let (terms, mut constant) = decomposed_affine_difference(left, right)?;
    if strict {
        constant += 1;
    }
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
) -> Option<(BTreeMap<SignedArithmeticAtom, BigInt>, BigInt)> {
    let mut terms: BTreeMap<SignedArithmeticAtom, BigInt> = BTreeMap::new();
    let mut constant = BigInt::zero();
    let mut pending = vec![(left, BigInt::one()), (right, -BigInt::one())];
    while let Some((term, coefficient)) = pending.pop() {
        charge_work(coefficient.bits() as usize + 1)?;
        if let Bitvector32Term::Constant(value) = term {
            let value = BigInt::from(*value as i32);
            charge_bigint_binary_work(&coefficient, &value)?;
            let product = &coefficient * &value;
            charge_bigint_binary_work(&constant, &product)?;
            constant += product;
        } else {
            let atom = SignedArithmeticAtom::from_term(term)?;
            charge_map_update_work(terms.len(), &atom, &coefficient)?;
            let previous = terms.get(&atom).cloned().unwrap_or_default();
            charge_bigint_binary_work(&previous, &coefficient)?;
            let updated = previous + coefficient;
            if updated.is_zero() {
                terms.remove(&atom);
            } else {
                terms.insert(atom, updated);
            }
        }
    }
    Some((terms, constant))
}

fn decomposed_affine_difference(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(BTreeMap<SignedArithmeticAtom, BigInt>, BigInt)> {
    let mut terms: BTreeMap<SignedArithmeticAtom, BigInt> = BTreeMap::new();
    let mut constant = BigInt::zero();
    let mut pending = vec![(left, BigInt::one()), (right, -BigInt::one())];
    while let Some((term, coefficient)) = pending.pop() {
        charge_work(coefficient.bits() as usize + 1)?;
        match term {
            Bitvector32Term::Constant(value) => {
                let value = BigInt::from(*value as i32);
                charge_bigint_binary_work(&coefficient, &value)?;
                let product = &coefficient * &value;
                charge_bigint_binary_work(&constant, &product)?;
                constant += product;
            }
            Bitvector32Term::Add(left, right) => {
                pending.push((right, coefficient.clone()));
                pending.push((left, coefficient));
            }
            Bitvector32Term::Subtract(left, right) => {
                pending.push((right, -coefficient.clone()));
                pending.push((left, coefficient));
            }
            Bitvector32Term::Multiply(left, right) => {
                if let Some(value) = left.as_const() {
                    let value = BigInt::from(value as i32);
                    let scaled = coefficient.clone() * &value;
                    charge_bigint_binary_work(&coefficient, &value)?;
                    pending.push((right, scaled));
                } else if let Some(value) = right.as_const() {
                    let value = BigInt::from(value as i32);
                    let scaled = coefficient.clone() * &value;
                    charge_bigint_binary_work(&coefficient, &value)?;
                    pending.push((left, scaled));
                } else {
                    let atom = SignedArithmeticAtom::from_term(term)?;
                    charge_map_update_work(terms.len(), &atom, &coefficient)?;
                    let previous = terms.get(&atom).cloned().unwrap_or_default();
                    let updated = previous + coefficient;
                    if updated.is_zero() {
                        terms.remove(&atom);
                    } else {
                        terms.insert(atom, updated);
                    }
                }
            }
            _ => {
                let atom = SignedArithmeticAtom::from_term(term)?;
                charge_map_update_work(terms.len(), &atom, &coefficient)?;
                let previous = terms.get(&atom).cloned().unwrap_or_default();
                charge_bigint_binary_work(&previous, &coefficient)?;
                let updated = previous + coefficient;
                if updated.is_zero() {
                    terms.remove(&atom);
                } else {
                    terms.insert(atom, updated);
                }
            }
        }
    }
    Some((terms, constant))
}

fn is_trivial(claim: &SignedArithmeticClaim) -> bool {
    claim.terms.is_empty()
        && match claim.relation {
            SignedArithmeticRelation::LessEqual => claim.constant <= BigInt::zero(),
            SignedArithmeticRelation::Equal => claim.constant.is_zero(),
            SignedArithmeticRelation::Disequal => !claim.constant.is_zero(),
        }
}

fn plan_affine_one_premise(
    claims: &[(usize, SignedArithmeticClaim)],
    expected: &SignedArithmeticClaim,
) -> Option<SignedArithmeticCertificate> {
    for (index, source) in claims {
        charge_work(1)?;
        charge_claim_comparison(source)?;
        if source.relation == expected.relation
            && let Some(coefficient) = scale_factor(source, expected)
            && (source.relation == SignedArithmeticRelation::Equal
                || (coefficient > BigInt::zero()
                    && (source.relation != SignedArithmeticRelation::Disequal
                        || !coefficient.is_zero())))
        {
            let mut nodes = vec![SignedArithmeticNode::Premise {
                index: *index,
                result: source.clone(),
            }];
            if coefficient != BigInt::one() {
                nodes.push(SignedArithmeticNode::Scale {
                    source: 0,
                    coefficient,
                    result: expected.clone(),
                });
                return Some(certificate(nodes, 1));
            }
            return Some(certificate(nodes, 0));
        }
        if source.relation == SignedArithmeticRelation::LessEqual
            && expected.relation == SignedArithmeticRelation::LessEqual
            && source.terms == expected.terms
            && source.constant >= expected.constant
        {
            let weakening = &expected.constant - &source.constant;
            let mut nodes = vec![SignedArithmeticNode::Premise {
                index: *index,
                result: source.clone(),
            }];
            if !weakening.is_zero() {
                nodes.push(SignedArithmeticNode::Trivial {
                    result: SignedArithmeticClaim {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        relation: SignedArithmeticRelation::LessEqual,
                        terms: BTreeMap::new(),
                        constant: weakening,
                    },
                });
                nodes.push(SignedArithmeticNode::Add {
                    left: 0,
                    right: 1,
                    result: expected.clone(),
                });
                return Some(certificate(nodes, 2));
            }
            return Some(certificate(nodes, 0));
        }
        if expected.relation == SignedArithmeticRelation::LessEqual
            && source.relation == SignedArithmeticRelation::Equal
        {
            for reverse in [false, true] {
                let direction = equality_direction(source, reverse);
                if direction == *expected {
                    return Some(certificate(
                        vec![
                            SignedArithmeticNode::Premise {
                                index: *index,
                                result: source.clone(),
                            },
                            SignedArithmeticNode::EqualityToLessEqual {
                                source: 0,
                                reverse,
                                result: direction,
                            },
                        ],
                        1,
                    ));
                }
                if direction.terms == expected.terms && direction.constant >= expected.constant {
                    let weakening = &expected.constant - &direction.constant;
                    let mut nodes = vec![
                        SignedArithmeticNode::Premise {
                            index: *index,
                            result: source.clone(),
                        },
                        SignedArithmeticNode::EqualityToLessEqual {
                            source: 0,
                            reverse,
                            result: direction.clone(),
                        },
                    ];
                    if !weakening.is_zero() {
                        nodes.push(SignedArithmeticNode::Trivial {
                            result: SignedArithmeticClaim {
                                carrier: SignedArithmeticCarrier::SignedInt32,
                                relation: SignedArithmeticRelation::LessEqual,
                                terms: BTreeMap::new(),
                                constant: weakening,
                            },
                        });
                        nodes.push(SignedArithmeticNode::Add {
                            left: 1,
                            right: 2,
                            result: expected.clone(),
                        });
                        return Some(certificate(nodes, 3));
                    }
                    return Some(certificate(nodes, 1));
                }
            }
        }
    }
    None
}

fn plan_machine_affine_goal(
    goal: &Proposition,
    premises: &[Proposition],
    claims: &[(usize, SignedArithmeticClaim)],
) -> Option<SignedArithmeticCertificate> {
    let (left_operation, right_operation) = affine_operation_terms(goal)?;
    let expected = decomposed_signed_claim(goal)?;
    let mut planner = Planner::new(premises, claims);
    let left_evidence = match left_operation {
        Some(term) => {
            // Affine conclusions decompose their operation roots using the
            // interval evidence.  A direct interval bound treats its root as
            // an opaque atom, so it cannot be used here without changing the
            // algebra represented by the conclusion.  Keep direct compound
            // bounds available to ordinary interval comparisons, but require
            // recursive operation evidence for this path.
            let value = planner.build_interval_for_affine(term);
            Some(value?)
        }
        None => None,
    };
    let right_evidence = match right_operation {
        Some(term) => Some(planner.build_interval_for_affine(term)?),
        None => None,
    };
    let source = planner.affine_claim(&expected).or_else(|| {
        is_trivial(&expected).then(|| {
            planner.push(SignedArithmeticNode::Trivial {
                result: expected.clone(),
            })
        })?
    });
    let source = source?;
    let conclusion = match (left_evidence, right_evidence) {
        (Some(left_evidence), Some(right_evidence)) => {
            planner.push(SignedArithmeticNode::AffineConclusionWithEvidence {
                source,
                left_evidence,
                right_evidence,
                result: goal.clone(),
            })?
        }
        (Some(evidence), None) | (None, Some(evidence)) => {
            planner.push(SignedArithmeticNode::AffineConclusion {
                source,
                evidence,
                result: goal.clone(),
            })?
        }
        (None, None) => return None,
    };
    Some(certificate(planner.nodes, conclusion))
}

fn affine_operation_terms(
    proposition: &Proposition,
) -> Option<(Option<&Bitvector32Term>, Option<&Bitvector32Term>)> {
    let (left, right, _) = comparison_terms(proposition)?;
    let is_affine_operation = |term: &Bitvector32Term| {
        matches!(
            term,
            Bitvector32Term::Add(_, _)
                | Bitvector32Term::Subtract(_, _)
                | Bitvector32Term::Multiply(_, _)
        )
    };
    let left_operation = is_affine_operation(left).then_some(left);
    let right_operation = is_affine_operation(right).then_some(right);
    (left_operation.is_some() || right_operation.is_some())
        .then_some((left_operation, right_operation))
}

fn contains_machine_operation(root: &Bitvector32Term) -> bool {
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        match term {
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
            | Bitvector32Term::BitwiseXor(_, _) => {
                return true;
            }
            Bitvector32Term::BitwiseNot(_) => return true,
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments.iter());
            }
            _ => {}
        }
    }
    false
}

fn scale_factor(source: &SignedArithmeticClaim, target: &SignedArithmeticClaim) -> Option<BigInt> {
    charge_claim_comparison(source)?;
    charge_claim_comparison(target)?;
    if source.terms.is_empty() {
        if !target.terms.is_empty() {
            return None;
        }
        return (source.constant != BigInt::zero())
            .then(|| {
                charge_bigint_binary_work(&target.constant, &source.constant)?;
                let coefficient = target.constant.clone() / &source.constant;
                charge_bigint_binary_work(&source.constant, &coefficient)?;
                let product = source.constant.clone() * &coefficient;
                charge_bigint_binary_work(&product, &target.constant)?;
                (product == target.constant).then_some(coefficient)
            })
            .flatten();
    }
    let mut factor = None;
    for (atom, coefficient) in &source.terms {
        charge_work(coefficient.bits() as usize + 1)?;
        charge_work(
            atom.work()
                .saturating_mul(
                    (usize::BITS - source.terms.len().saturating_add(1).leading_zeros()) as usize,
                )
                .max(1),
        )?;
        charge_map_lookup_work(target.terms.len(), atom)?;
        let target_coefficient = target.terms.get(atom).cloned().unwrap_or_default();
        charge_work(target_coefficient.bits() as usize + 1)?;
        if coefficient.is_zero() {
            continue;
        }
        let quotient = &target_coefficient / coefficient;
        charge_bigint_binary_work(&target_coefficient, coefficient)?;
        let product = coefficient * &quotient;
        charge_bigint_binary_work(coefficient, &quotient)?;
        if product != target_coefficient {
            return None;
        }
        if let Some(existing) = &factor {
            charge_bigint_binary_work(existing, &quotient)?;
            if existing != &quotient {
                return None;
            }
        } else {
            factor = Some(quotient);
        }
    }
    let factor = factor?;
    charge_work(source.constant.bits() as usize + factor.bits() as usize + 2)?;
    charge_bigint_binary_work(&source.constant, &factor)?;
    let product = source.constant.clone() * &factor;
    charge_bigint_binary_work(&product, &target.constant)?;
    if product != target.constant {
        return None;
    }
    for atom in target.terms.keys() {
        charge_map_lookup_work(source.terms.len(), atom)?;
        if !source.terms.contains_key(atom) {
            return None;
        }
    }
    Some(factor)
}

fn add_affine_claims(
    left: &SignedArithmeticClaim,
    right: &SignedArithmeticClaim,
) -> Option<SignedArithmeticClaim> {
    if left.carrier != right.carrier
        || left.relation != SignedArithmeticRelation::LessEqual
        || right.relation != SignedArithmeticRelation::LessEqual
    {
        return None;
    }
    charge_claim_comparison(left)?;
    charge_claim_comparison(right)?;
    let mut terms = left.terms.clone();
    for (atom, coefficient) in &right.terms {
        charge_map_update_work(terms.len(), atom, coefficient)?;
        let previous = terms.get(atom).cloned().unwrap_or_default();
        charge_bigint_binary_work(&previous, coefficient)?;
        let updated = previous + coefficient;
        if updated.is_zero() {
            terms.remove(atom);
        } else {
            terms.insert(atom.clone(), updated);
        }
    }
    charge_bigint_binary_work(&left.constant, &right.constant)?;
    Some(SignedArithmeticClaim {
        carrier: left.carrier,
        relation: SignedArithmeticRelation::LessEqual,
        terms,
        constant: &left.constant + &right.constant,
    })
}

fn subtract_affine_claims(
    target: &SignedArithmeticClaim,
    left: &SignedArithmeticClaim,
) -> Option<SignedArithmeticClaim> {
    if target.carrier != left.carrier
        || target.relation != SignedArithmeticRelation::LessEqual
        || left.relation != SignedArithmeticRelation::LessEqual
    {
        return None;
    }
    charge_claim_comparison(target)?;
    charge_claim_comparison(left)?;
    let mut terms = target.terms.clone();
    for (atom, coefficient) in &left.terms {
        charge_map_update_work(terms.len(), atom, coefficient)?;
        let previous = terms.get(atom).cloned().unwrap_or_default();
        let updated = previous - coefficient;
        if updated.is_zero() {
            terms.remove(atom);
        } else {
            terms.insert(atom.clone(), updated);
        }
    }
    charge_bigint_binary_work(&target.constant, &left.constant)?;
    Some(SignedArithmeticClaim {
        carrier: target.carrier,
        relation: SignedArithmeticRelation::LessEqual,
        terms,
        constant: &target.constant - &left.constant,
    })
}

fn claim_fingerprint(claim: &SignedArithmeticClaim) -> u64 {
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    std::mem::discriminant(&claim.carrier).hash(&mut hasher);
    std::mem::discriminant(&claim.relation).hash(&mut hasher);
    for (atom, coefficient) in &claim.terms {
        atom.hash(&mut hasher);
        coefficient.hash(&mut hasher);
    }
    claim.constant.hash(&mut hasher);
    hasher.finish()
}

fn charge_claim_comparison(claim: &SignedArithmeticClaim) -> Option<()> {
    let logarithmic = (usize::BITS - claim.terms.len().saturating_add(1).leading_zeros()) as usize;
    let mut units = claim.terms.len().saturating_add(1);
    units = units.saturating_add(claim.constant.bits() as usize + 1);
    for (atom, coefficient) in &claim.terms {
        units = units.saturating_add(
            atom.work()
                .saturating_add(coefficient.bits() as usize + 1)
                .saturating_mul(logarithmic.max(1)),
        );
    }
    charge_work(units)
}

fn charge_map_update_work(
    map_len: usize,
    atom: &SignedArithmeticAtom,
    coefficient: &BigInt,
) -> Option<()> {
    let logarithmic = (usize::BITS - map_len.saturating_add(1).leading_zeros()) as usize;
    charge_work(
        atom.work()
            .saturating_add(coefficient.bits() as usize + 1)
            .saturating_mul(logarithmic.max(1))
            .saturating_mul(3),
    )
}

fn charge_bigint_binary_work(left: &BigInt, right: &BigInt) -> Option<()> {
    charge_work((left.bits() as usize + 1).saturating_mul(right.bits() as usize + 1))
}

fn charge_map_lookup_work(map_len: usize, atom: &SignedArithmeticAtom) -> Option<()> {
    let logarithmic = (usize::BITS - map_len.saturating_add(1).leading_zeros()) as usize;
    charge_work(atom.work().saturating_mul(logarithmic.max(1)))
}

fn equality_direction(source: &SignedArithmeticClaim, reverse: bool) -> SignedArithmeticClaim {
    if reverse {
        SignedArithmeticClaim {
            carrier: source.carrier,
            relation: SignedArithmeticRelation::LessEqual,
            terms: source.terms.iter().map(|(a, c)| (a.clone(), -c)).collect(),
            constant: -&source.constant,
        }
    } else {
        SignedArithmeticClaim {
            carrier: source.carrier,
            relation: SignedArithmeticRelation::LessEqual,
            terms: source.terms.clone(),
            constant: source.constant.clone(),
        }
    }
}

#[derive(Clone, Debug, Eq, Hash, PartialEq)]
struct DefinednessKey {
    operator: u8,
    left: u64,
    right: u64,
}

fn definedness_parts_from_term(
    term: &Bitvector32Term,
) -> Option<(u8, &Bitvector32Term, &Bitvector32Term)> {
    Some(match term {
        Bitvector32Term::Add(left, right) => (0, left, right),
        Bitvector32Term::Subtract(left, right) => (1, left, right),
        Bitvector32Term::Multiply(left, right) => (2, left, right),
        Bitvector32Term::ShiftLeft(left, right) => (3, left, right),
        Bitvector32Term::Remainder(left, right) => (4, left, right),
        _ => return None,
    })
}

fn definedness_parts_from_proposition(
    proposition: &Proposition,
) -> Option<(u8, &Bitvector32Term, &Bitvector32Term)> {
    let Proposition::ConditionIs(condition, false) = proposition else {
        return None;
    };
    Some(match condition {
        ConditionTerm::Bitvector32SignedAddOverflows(left, right) => (0, left, right),
        ConditionTerm::Bitvector32SignedSubtractOverflows(left, right) => (1, left, right),
        ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right) => (2, left, right),
        ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => (3, left, right),
        ConditionTerm::Bitvector32SignedDivideOverflows(left, right) => (4, left, right),
        _ => return None,
    })
}

#[derive(Clone, Copy)]
struct BoundCandidate {
    position: usize,
    premise: usize,
    bound: i64,
}

#[derive(Default)]
struct BoundCandidates {
    lower: Option<BoundCandidate>,
    upper: Option<BoundCandidate>,
}

struct Planner<'a> {
    premises: &'a [Proposition],
    claims: &'a [(usize, SignedArithmeticClaim)],
    nodes: Vec<SignedArithmeticNode>,
    intervals: Vec<Option<SignedArithmeticInterval>>,
    interval_cache: HashMap<SignedArithmeticAtom, usize>,
    defined_cache: HashMap<DefinednessKey, Option<usize>>,
    definedness_index: Option<HashMap<DefinednessKey, Vec<usize>>>,
    bound_index: Option<HashMap<SignedArithmeticAtom, BoundCandidates>>,
    term_hash_cache: HashMap<usize, u64>,
    premise_cache: HashMap<usize, usize>,
}

impl<'a> Planner<'a> {
    fn new(premises: &'a [Proposition], claims: &'a [(usize, SignedArithmeticClaim)]) -> Self {
        Self {
            premises,
            claims,
            nodes: Vec::new(),
            intervals: Vec::new(),
            interval_cache: HashMap::new(),
            defined_cache: HashMap::new(),
            definedness_index: None,
            bound_index: None,
            term_hash_cache: HashMap::new(),
            premise_cache: HashMap::new(),
        }
    }

    fn push(&mut self, node: SignedArithmeticNode) -> Option<usize> {
        if self.nodes.len() >= MAX_NODES {
            return None;
        }
        let index = self.nodes.len();
        self.nodes.push(node);
        self.intervals.push(None);
        Some(index)
    }

    fn push_interval(
        &mut self,
        node: SignedArithmeticNode,
        interval: SignedArithmeticInterval,
    ) -> Option<usize> {
        let index = self.push(node)?;
        self.intervals[index] = Some(interval);
        Some(index)
    }

    fn interval_at(&self, index: usize) -> Option<SignedArithmeticInterval> {
        self.intervals.get(index)?.clone()
    }

    fn premise(&mut self, index: usize, claim: &SignedArithmeticClaim) -> Option<usize> {
        if let Some(node) = self.premise_cache.get(&index) {
            return Some(*node);
        }
        let node = self.push(SignedArithmeticNode::Premise {
            index,
            result: claim.clone(),
        })?;
        self.premise_cache.insert(index, node);
        Some(node)
    }

    fn affine_claim(&mut self, target: &SignedArithmeticClaim) -> Option<usize> {
        for (index, claim) in self.claims {
            charge_work(1)?;
            charge_claim_comparison(claim)?;
            if claim == target {
                return self.premise(*index, claim);
            }
            if claim.relation == target.relation
                && let Some(coefficient) = scale_factor(claim, target)
                && (claim.relation == SignedArithmeticRelation::Equal
                    || (coefficient > BigInt::zero()
                        && (claim.relation != SignedArithmeticRelation::Disequal
                            || !coefficient.is_zero())))
            {
                let source = self.premise(*index, claim)?;
                if coefficient == BigInt::one() {
                    return Some(source);
                }
                return self.push(SignedArithmeticNode::Scale {
                    source,
                    coefficient,
                    result: target.clone(),
                });
            }
            if claim.relation == SignedArithmeticRelation::LessEqual
                && target.relation == SignedArithmeticRelation::LessEqual
                && claim.terms == target.terms
                && claim.constant >= target.constant
            {
                let source = self.premise(*index, claim)?;
                let weakening = &target.constant - &claim.constant;
                if weakening.is_zero() {
                    return Some(source);
                }
                let trivial = self.push(SignedArithmeticNode::Trivial {
                    result: SignedArithmeticClaim {
                        carrier: SignedArithmeticCarrier::SignedInt32,
                        relation: SignedArithmeticRelation::LessEqual,
                        terms: BTreeMap::new(),
                        constant: weakening,
                    },
                })?;
                return self.push(SignedArithmeticNode::Add {
                    left: source,
                    right: trivial,
                    result: target.clone(),
                });
            }
        }
        // Index claims by a bounded structural fingerprint, then verify only
        // hash-collision candidates with the exact affine operation.  This
        // preserves the useful five-premise bound case without a quadratic
        // pair scan over unrelated facts.
        let mut index: HashMap<u64, Vec<usize>> = HashMap::new();
        for (position, (_, claim)) in self.claims.iter().enumerate() {
            charge_work(1)?;
            index
                .entry(claim_fingerprint(claim))
                .or_default()
                .push(position);
        }
        for (left_index, left) in self.claims.iter() {
            if left.relation != SignedArithmeticRelation::LessEqual {
                continue;
            }
            let complement = subtract_affine_claims(target, left)?;
            let Some(right_positions) = index.get(&claim_fingerprint(&complement)) else {
                continue;
            };
            for right_position in right_positions {
                charge_work(1)?;
                let (right_index, right) = &self.claims[*right_position];
                if *right_index == *left_index || add_affine_claims(left, right)? != *target {
                    continue;
                }
                let left_node = self.premise(*left_index, left)?;
                let right_node = self.premise(*right_index, right)?;
                return self.push(SignedArithmeticNode::Add {
                    left: left_node,
                    right: right_node,
                    result: target.clone(),
                });
            }
        }
        None
    }

    fn defined(&mut self, term: &Bitvector32Term) -> Option<usize> {
        let cache_key = self.definedness_key_from_term(term)?;
        if let Some(index) = self.defined_cache.get(&cache_key) {
            return index.and_then(|index| {
                self.push(SignedArithmeticNode::DefinedPremise {
                    index,
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: term.clone(),
                })
            });
        }
        self.ensure_definedness_index()?;
        let index = self
            .definedness_index
            .as_ref()?
            .get(&cache_key)
            .and_then(|candidates| {
                candidates.iter().copied().find(|candidate| {
                    charge_work(1).is_some() && exact_definedness(&self.premises[*candidate], term)
                })
            });
        self.defined_cache.insert(cache_key, index);
        let index = index?;
        self.push(SignedArithmeticNode::DefinedPremise {
            index,
            carrier: SignedArithmeticCarrier::SignedInt32,
            term: term.clone(),
        })
    }

    fn definedness_key_from_term(&mut self, term: &Bitvector32Term) -> Option<DefinednessKey> {
        let (operator, left, right) = definedness_parts_from_term(term)?;
        Some(DefinednessKey {
            operator,
            left: self.term_hash(left)?,
            right: self.term_hash(right)?,
        })
    }

    fn term_hash(&mut self, root: &Bitvector32Term) -> Option<u64> {
        let root_key = root as *const Bitvector32Term as usize;
        if let Some(hash) = self.term_hash_cache.get(&root_key) {
            return Some(*hash);
        }
        enum Task<'a> {
            Visit(&'a Bitvector32Term),
            Finish(&'a Bitvector32Term),
        }
        let mut tasks = vec![Task::Visit(root)];
        while let Some(task) = tasks.pop() {
            charge_work(1)?;
            match task {
                Task::Visit(term) => {
                    let key = term as *const Bitvector32Term as usize;
                    if self.term_hash_cache.contains_key(&key) {
                        continue;
                    }
                    match term {
                        Bitvector32Term::Constant(_)
                        | Bitvector32Term::Int64Constant(_)
                        | Bitvector32Term::UInt64Constant(_)
                        | Bitvector32Term::Variable(_) => {
                            let mut hasher = std::collections::hash_map::DefaultHasher::new();
                            std::mem::discriminant(term).hash(&mut hasher);
                            term.hash(&mut hasher);
                            self.term_hash_cache.insert(key, hasher.finish());
                        }
                        Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                            tasks.push(Task::Finish(term));
                            tasks.extend(arguments.iter().rev().map(Task::Visit));
                        }
                        Bitvector32Term::Add(left, right)
                        | Bitvector32Term::Subtract(left, right)
                        | Bitvector32Term::Multiply(left, right)
                        | Bitvector32Term::Divide(left, right)
                        | Bitvector32Term::UnsignedDivide(left, right)
                        | Bitvector32Term::Remainder(left, right)
                        | Bitvector32Term::UnsignedRemainder(left, right)
                        | Bitvector32Term::ShiftLeft(left, right)
                        | Bitvector32Term::ArithmeticShiftRight(left, right)
                        | Bitvector32Term::LogicalShiftRight(left, right)
                        | Bitvector32Term::BitwiseAnd(left, right)
                        | Bitvector32Term::BitwiseOr(left, right)
                        | Bitvector32Term::BitwiseXor(left, right) => {
                            tasks.push(Task::Finish(term));
                            tasks.push(Task::Visit(right));
                            tasks.push(Task::Visit(left));
                        }
                        Bitvector32Term::BitwiseNot(operand)
                        | Bitvector32Term::Int64From32(operand)
                        | Bitvector32Term::UInt64From32(operand)
                        | Bitvector32Term::UInt32From64(operand)
                        | Bitvector32Term::Int64FromUInt32(operand)
                        | Bitvector32Term::UInt64FromInt32(operand)
                        | Bitvector32Term::UInt64FromInt64(operand) => {
                            tasks.push(Task::Finish(term));
                            tasks.push(Task::Visit(operand));
                        }
                        _ => return None,
                    }
                }
                Task::Finish(term) => {
                    let key = term as *const Bitvector32Term as usize;
                    if self.term_hash_cache.contains_key(&key) {
                        continue;
                    }
                    let mut hasher = std::collections::hash_map::DefaultHasher::new();
                    std::mem::discriminant(term).hash(&mut hasher);
                    match term {
                        Bitvector32Term::PureFunctionApplication { name, arguments } => {
                            name.hash(&mut hasher);
                            arguments.len().hash(&mut hasher);
                            for argument in arguments {
                                self.term_hash_cache
                                    .get(&(argument as *const Bitvector32Term as usize))?
                                    .hash(&mut hasher);
                            }
                        }
                        Bitvector32Term::Add(left, right)
                        | Bitvector32Term::Subtract(left, right)
                        | Bitvector32Term::Multiply(left, right)
                        | Bitvector32Term::Divide(left, right)
                        | Bitvector32Term::UnsignedDivide(left, right)
                        | Bitvector32Term::Remainder(left, right)
                        | Bitvector32Term::UnsignedRemainder(left, right)
                        | Bitvector32Term::ShiftLeft(left, right)
                        | Bitvector32Term::ArithmeticShiftRight(left, right)
                        | Bitvector32Term::LogicalShiftRight(left, right)
                        | Bitvector32Term::BitwiseAnd(left, right)
                        | Bitvector32Term::BitwiseOr(left, right)
                        | Bitvector32Term::BitwiseXor(left, right) => {
                            self.term_hash_cache
                                .get(&(left.as_ref() as *const Bitvector32Term as usize))?
                                .hash(&mut hasher);
                            self.term_hash_cache
                                .get(&(right.as_ref() as *const Bitvector32Term as usize))?
                                .hash(&mut hasher);
                        }
                        Bitvector32Term::BitwiseNot(operand)
                        | Bitvector32Term::Int64From32(operand)
                        | Bitvector32Term::UInt64From32(operand)
                        | Bitvector32Term::UInt32From64(operand)
                        | Bitvector32Term::Int64FromUInt32(operand)
                        | Bitvector32Term::UInt64FromInt32(operand)
                        | Bitvector32Term::UInt64FromInt64(operand) => {
                            self.term_hash_cache
                                .get(&(operand.as_ref() as *const Bitvector32Term as usize))?
                                .hash(&mut hasher);
                        }
                        _ => return None,
                    }
                    self.term_hash_cache.insert(key, hasher.finish());
                }
            }
        }
        self.term_hash_cache.get(&root_key).copied()
    }

    fn ensure_definedness_index(&mut self) -> Option<()> {
        if self.definedness_index.is_some() {
            return Some(());
        }
        let mut index: HashMap<DefinednessKey, Vec<usize>> = HashMap::new();
        for (candidate, proposition) in self.premises.iter().enumerate() {
            charge_work(1)?;
            let Some((operator, left, right)) = definedness_parts_from_proposition(proposition)
            else {
                continue;
            };
            let key = DefinednessKey {
                operator,
                left: self.term_hash(left)?,
                right: self.term_hash(right)?,
            };
            index.entry(key).or_default().push(candidate);
        }
        self.definedness_index = Some(index);
        Some(())
    }

    fn ensure_bound_index(&mut self) -> Option<()> {
        if self.bound_index.is_some() {
            return Some(());
        }
        let mut index: HashMap<SignedArithmeticAtom, BoundCandidates> = HashMap::new();
        for (position, (premise, claim)) in self.claims.iter().enumerate() {
            charge_work(1)?;
            if claim.relation != SignedArithmeticRelation::LessEqual || claim.terms.len() != 1 {
                continue;
            }
            let (atom, coefficient) = claim.terms.iter().next()?;
            charge_work(atom.work().saturating_add(coefficient.bits() as usize + 1))?;
            let Some(bound) = (if coefficient == &BigInt::from(-1) {
                claim.constant.to_i64().map(|value| value.max(SIGNED_MIN))
            } else if coefficient == &BigInt::one() {
                (-&claim.constant)
                    .to_i64()
                    .map(|value| value.min(SIGNED_MAX))
            } else {
                None
            }) else {
                continue;
            };
            let entry = index.entry(atom.clone()).or_default();
            if coefficient == &BigInt::from(-1)
                && entry.lower.is_none_or(|candidate| bound > candidate.bound)
            {
                entry.lower = Some(BoundCandidate {
                    position,
                    premise: *premise,
                    bound,
                });
            } else if coefficient == &BigInt::one()
                && entry.upper.is_none_or(|candidate| bound < candidate.bound)
            {
                entry.upper = Some(BoundCandidate {
                    position,
                    premise: *premise,
                    bound,
                });
            }
        }
        self.bound_index = Some(index);
        Some(())
    }

    fn interval_atom(&mut self, term: &Bitvector32Term) -> Option<usize> {
        let cache_key = SignedArithmeticAtom::from_term(term)?;
        if let Some(index) = self.interval_cache.get(&cache_key) {
            return Some(*index);
        }
        if let Some(value) = term.as_const().map(|value| i64::from(value as i32)) {
            let index = self.push_interval(
                SignedArithmeticNode::IntervalAtom {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: term.clone(),
                    lower: value,
                    upper: value,
                },
                SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: value,
                    upper: value,
                },
            )?;
            self.interval_cache.insert(cache_key, index);
            return Some(index);
        }
        let safe_atom = Self::is_safe_interval_atom(term);
        let atom = SignedArithmeticAtom::from_term(term)?;
        self.ensure_bound_index()?;
        let candidates = self.bound_index.as_ref()?.get(&atom);
        let lower = candidates
            .and_then(|candidates| candidates.lower)
            .and_then(|candidate| {
                self.claims
                    .get(candidate.position)
                    .map(|(_, claim)| (candidate.premise, claim.clone(), candidate.bound))
            });
        let upper = candidates
            .and_then(|candidates| candidates.upper)
            .and_then(|candidate| {
                self.claims
                    .get(candidate.position)
                    .map(|(_, claim)| (candidate.premise, claim.clone(), candidate.bound))
            });
        if lower.is_none() && upper.is_none() {
            if !safe_atom {
                return None;
            }
            let index = self.push_interval(
                SignedArithmeticNode::IntervalAtom {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    term: term.clone(),
                    lower: SIGNED_MIN,
                    upper: SIGNED_MAX,
                },
                SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: SIGNED_MIN,
                    upper: SIGNED_MAX,
                },
            )?;
            self.interval_cache.insert(cache_key, index);
            return Some(index);
        }
        let affine_interval_node = |source, lower, upper| {
            if safe_atom {
                SignedArithmeticNode::IntervalFromAffine {
                    source,
                    term: term.clone(),
                    lower,
                    upper,
                }
            } else {
                SignedArithmeticNode::IntervalFromAffineDirect {
                    source,
                    term: term.clone(),
                    lower,
                    upper,
                }
            }
        };
        let Some((lower_index, lower_claim, lower_bound)) = lower else {
            let (upper_index, upper_claim, upper_bound) = upper?;
            let upper_node = self.premise(upper_index, &upper_claim)?;
            let index = self.push_interval(
                affine_interval_node(upper_node, SIGNED_MIN, upper_bound),
                SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: SIGNED_MIN,
                    upper: upper_bound,
                },
            )?;
            self.interval_cache.insert(cache_key, index);
            return Some(index);
        };
        let lower_node = self.premise(lower_index, &lower_claim)?;
        let lower_node_index = self.push_interval(
            affine_interval_node(lower_node, lower_bound, SIGNED_MAX),
            SignedArithmeticInterval {
                carrier: SignedArithmeticCarrier::SignedInt32,
                lower: lower_bound,
                upper: SIGNED_MAX,
            },
        )?;
        if let Some((upper_index, upper_claim, upper_bound)) = upper {
            let upper_node = self.premise(upper_index, &upper_claim)?;
            let upper_interval = self.push_interval(
                affine_interval_node(upper_node, SIGNED_MIN, upper_bound),
                SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: SIGNED_MIN,
                    upper: upper_bound,
                },
            )?;
            let result = SignedArithmeticInterval {
                carrier: SignedArithmeticCarrier::SignedInt32,
                lower: lower_bound,
                upper: upper_bound,
            };
            let index = self.push_interval(
                SignedArithmeticNode::IntervalIntersect {
                    left: lower_node_index,
                    right: upper_interval,
                    result,
                },
                SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: lower_bound,
                    upper: upper_bound,
                },
            )?;
            self.interval_cache.insert(cache_key, index);
            return Some(index);
        }
        self.interval_cache.insert(cache_key, lower_node_index);
        Some(lower_node_index)
    }

    fn is_safe_interval_atom(term: &Bitvector32Term) -> bool {
        let mut pending = vec![term];
        while let Some(term) = pending.pop() {
            match term {
                Bitvector32Term::Variable(_) | Bitvector32Term::Constant(_) => {}
                Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                    pending.extend(arguments.iter());
                }
                _ => return false,
            }
        }
        true
    }

    fn build_interval(&mut self, root: &Bitvector32Term) -> Option<usize> {
        self.build_interval_with_direct(root, true)
    }

    fn build_interval_for_affine(&mut self, root: &Bitvector32Term) -> Option<usize> {
        self.build_interval_with_direct(root, false)
    }

    fn build_interval_with_direct(
        &mut self,
        root: &Bitvector32Term,
        allow_direct: bool,
    ) -> Option<usize> {
        enum Task<'a> {
            Visit(&'a Bitvector32Term, bool),
            Build(&'a Bitvector32Term),
        }
        let mut tasks = vec![Task::Visit(root, allow_direct)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            charge_work(1)?;
            match task {
                Task::Visit(term, allow_direct) => match term {
                    Bitvector32Term::Constant(_) => results.push(self.interval_atom(term)?),
                    Bitvector32Term::Add(left, right)
                    | Bitvector32Term::Subtract(left, right)
                    | Bitvector32Term::Multiply(left, right) => {
                        if allow_direct && let Some(index) = self.interval_atom(term) {
                            results.push(index);
                            continue;
                        }
                        tasks.push(Task::Build(term));
                        // A direct bound may be the only evidence for a child
                        // operation in an interval comparison.  It stops the
                        // traversal at that child, so direct payloads are
                        // disjoint rather than repeated along one path.
                        tasks.push(Task::Visit(right, allow_direct));
                        tasks.push(Task::Visit(left, allow_direct));
                    }
                    Bitvector32Term::Remainder(operand, divisor)
                    | Bitvector32Term::ShiftLeft(operand, divisor)
                    | Bitvector32Term::ArithmeticShiftRight(operand, divisor) => {
                        divisor.as_const()?;
                        tasks.push(Task::Build(term));
                        tasks.push(Task::Visit(operand, allow_direct));
                    }
                    Bitvector32Term::BitwiseAnd(left, right)
                    | Bitvector32Term::BitwiseXor(left, right) => {
                        let (operand, _) = if right.as_const().is_some() {
                            (left, right)
                        } else if left.as_const().is_some() {
                            (right, left)
                        } else {
                            return None;
                        };
                        tasks.push(Task::Build(term));
                        tasks.push(Task::Visit(operand, allow_direct));
                    }
                    _ => results.push(self.interval_atom(term)?),
                },
                Task::Build(term) => {
                    let operand = results.pop()?;
                    let (left, right) = match term {
                        Bitvector32Term::Add(_, _)
                        | Bitvector32Term::Subtract(_, _)
                        | Bitvector32Term::Multiply(_, _) => (Some(results.pop()?), Some(operand)),
                        _ => (None, Some(operand)),
                    };
                    let result = self.build_operation(term, left, right)?;
                    results.push(result);
                }
            }
        }
        results.pop()
    }

    fn build_operation(
        &mut self,
        term: &Bitvector32Term,
        left_index: Option<usize>,
        right_index: Option<usize>,
    ) -> Option<usize> {
        match term {
            Bitvector32Term::Add(_, _) => {
                let left = left_index?;
                let right = right_index?;
                let l = self.interval_at(left)?;
                let r = self.interval_at(right)?;
                let lower = l.lower.checked_add(r.lower)?;
                let upper = l.upper.checked_add(r.upper)?;
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: lower.max(SIGNED_MIN),
                    upper: upper.min(SIGNED_MAX),
                };
                if let Some(defined) = self.defined(term) {
                    return self.push_interval(
                        SignedArithmeticNode::IntervalAdd {
                            left,
                            right,
                            defined,
                            result: interval.clone(),
                        },
                        interval,
                    );
                }
                if lower >= SIGNED_MIN && upper <= SIGNED_MAX {
                    return self.push_interval(
                        SignedArithmeticNode::IntervalAddBounded {
                            left,
                            right,
                            result: interval.clone(),
                        },
                        interval,
                    );
                }
                None
            }
            Bitvector32Term::Subtract(_, _) => {
                let left = left_index?;
                let right = right_index?;
                let l = self.interval_at(left)?;
                let r = self.interval_at(right)?;
                let lower = l.lower.checked_sub(r.upper)?;
                let upper = l.upper.checked_sub(r.lower)?;
                (lower >= SIGNED_MIN && upper <= SIGNED_MAX).then_some(())?;
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower,
                    upper,
                };
                let defined = self.defined(term).unwrap_or(left);
                self.push_interval(
                    SignedArithmeticNode::IntervalSubtract {
                        left,
                        right,
                        defined,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::Multiply(_, _) => {
                let left = left_index?;
                let right = right_index?;
                let l = self.interval_at(left)?;
                let r = self.interval_at(right)?;
                let values = [
                    l.lower as i128 * r.lower as i128,
                    l.lower as i128 * r.upper as i128,
                    l.upper as i128 * r.lower as i128,
                    l.upper as i128 * r.upper as i128,
                ];
                let lower = *values.iter().min()?;
                let upper = *values.iter().max()?;
                (lower >= SIGNED_MIN as i128 && upper <= SIGNED_MAX as i128).then_some(())?;
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: lower as i64,
                    upper: upper as i64,
                };
                let defined = self.defined(term).unwrap_or(left);
                self.push_interval(
                    SignedArithmeticNode::IntervalMultiply {
                        left,
                        right,
                        defined,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::Remainder(_, divisor) => {
                let operand = right_index?;
                let divisor = divisor.as_const()?.to_i32()?;
                if divisor == 0 {
                    return None;
                }
                let op = self.interval_at(operand)?;
                let bounded = divisor != -1 || !(op.lower <= SIGNED_MIN && op.upper >= SIGNED_MIN);
                let defined = self.defined(term).or_else(|| bounded.then_some(operand))?;
                let magnitude = i64::from(divisor).abs().saturating_sub(1);
                let (lower, upper) = if op.lower >= 0 {
                    (0, magnitude)
                } else if op.upper < 0 {
                    (-magnitude, 0)
                } else {
                    (-magnitude, magnitude)
                };
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower,
                    upper,
                };
                self.push_interval(
                    SignedArithmeticNode::IntervalRemainder {
                        operand,
                        divisor,
                        defined,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::ShiftLeft(_, shift) => {
                let operand = right_index?;
                let shift = shift.as_const()?.to_i32()?;
                if !(0..32).contains(&shift) {
                    return None;
                }
                let op = self.interval_at(operand)?;
                if op.lower < 0 {
                    return None;
                }
                let factor = 1_i128 << shift;
                let lower = op.lower as i128 * factor;
                let upper = op.upper as i128 * factor;
                (lower >= SIGNED_MIN as i128 && upper <= SIGNED_MAX as i128).then_some(())?;
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: lower as i64,
                    upper: upper as i64,
                };
                let defined = self.defined(term).unwrap_or(operand);
                self.push_interval(
                    SignedArithmeticNode::IntervalShiftLeft {
                        operand,
                        shift,
                        defined,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::ArithmeticShiftRight(_, shift) => {
                let operand = right_index?;
                let shift = shift.as_const()?.to_i32()?;
                if !(0..32).contains(&shift) {
                    return None;
                }
                let op = self.interval_at(operand)?;
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: i64::from((op.lower as i32) >> shift),
                    upper: i64::from((op.upper as i32) >> shift),
                };
                self.push_interval(
                    SignedArithmeticNode::IntervalArithmeticShiftRight {
                        operand,
                        shift,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::BitwiseAnd(left, right) => {
                let operand = right_index?;
                let mask = left.as_const().or_else(|| right.as_const())?;
                if mask > i32::MAX as u32 {
                    return None;
                }
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower: 0,
                    upper: i64::from(mask as i32),
                };
                self.push_interval(
                    SignedArithmeticNode::IntervalBitwiseAnd {
                        operand,
                        mask,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            Bitvector32Term::BitwiseXor(left, right) => {
                let operand = right_index?;
                let (_operand_term, sign_bit) = if left.as_const() == Some(0x8000_0000) {
                    (right, left)
                } else if right.as_const() == Some(0x8000_0000) {
                    (left, right)
                } else {
                    return None;
                };
                if sign_bit.as_const()? != 0x8000_0000 {
                    return None;
                }
                let op = self.interval_at(operand)?;
                let (lower, upper) = if op.lower >= 0 {
                    (op.lower + SIGNED_MIN, op.upper + SIGNED_MIN)
                } else if op.upper < 0 {
                    (op.lower - SIGNED_MIN, op.upper - SIGNED_MIN)
                } else {
                    (SIGNED_MIN, SIGNED_MAX)
                };
                let interval = SignedArithmeticInterval {
                    carrier: SignedArithmeticCarrier::SignedInt32,
                    lower,
                    upper,
                };
                self.push_interval(
                    SignedArithmeticNode::IntervalSignBitFlip {
                        operand,
                        result: interval.clone(),
                    },
                    interval,
                )
            }
            _ => None,
        }
    }
}

fn exact_definedness(proposition: &Proposition, term: &Bitvector32Term) -> bool {
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
        )
        | (
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right),
            Bitvector32Term::ShiftLeft(a, b),
        )
        | (
            ConditionTerm::Bitvector32SignedDivideOverflows(left, right),
            Bitvector32Term::Remainder(a, b),
        ) => terms_equal(left, a) && terms_equal(right, b),
        _ => false,
    }
}

fn terms_equal(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    let (Some(left), Some(right)) = (
        SignedArithmeticAtom::from_term(left),
        SignedArithmeticAtom::from_term(right),
    ) else {
        return false;
    };
    charge_work(left.work().saturating_add(right.work()).saturating_add(1)).is_some()
        && left == right
}

fn plan_interval_goal(
    goal: &Proposition,
    premises: &[Proposition],
    claims: &[(usize, SignedArithmeticClaim)],
) -> Option<SignedArithmeticCertificate> {
    let (left, right, comparison) = comparison_terms(goal)?;
    let mut planner = Planner::new(premises, claims);
    let left_node = planner.build_interval(left)?;
    let right_node = planner.build_interval(right)?;
    let result = SignedArithmeticComparison::from_comparison(comparison);
    let left_interval = planner.interval_at(left_node)?;
    let right_interval = planner.interval_at(right_node)?;
    if !interval_proves(&left_interval, &right_interval, comparison)
        && !term_interval_proves(left, right, comparison, &left_interval)
    {
        return None;
    }
    let conclusion = planner.push(SignedArithmeticNode::IntervalCompare {
        left: left_node,
        right: right_node,
        comparison: result,
        result: goal.clone(),
    })?;
    Some(certificate(planner.nodes, conclusion))
}

fn term_interval_proves(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
    comparison: Comparison,
    left_interval: &SignedArithmeticInterval,
) -> bool {
    if !matches!(comparison, Comparison::LessEqual) || left_interval.lower < 0 {
        return false;
    }
    let Bitvector32Term::ArithmeticShiftRight(operand, shift) = left else {
        return false;
    };
    terms_equal(operand, right) && shift.as_const().is_some_and(|value| value <= 31)
}

fn comparison_terms(
    proposition: &Proposition,
) -> Option<(&Bitvector32Term, &Bitvector32Term, Comparison)> {
    let (condition, value) = match proposition {
        Proposition::ConditionIs(condition, value) => (condition, *value),
        _ => return None,
    };
    match (condition, value) {
        (ConditionTerm::Bitvector32SignedLessThan(left, right), true) => {
            Some((left.as_ref(), right.as_ref(), Comparison::LessThan))
        }
        (ConditionTerm::Bitvector32SignedLessEqual(left, right), true) => {
            Some((left.as_ref(), right.as_ref(), Comparison::LessEqual))
        }
        (ConditionTerm::Bitvector32Equal(left, right), true) => {
            Some((left.as_ref(), right.as_ref(), Comparison::Equal))
        }
        (ConditionTerm::Bitvector32Equal(left, right), false) => {
            Some((left.as_ref(), right.as_ref(), Comparison::Disequal))
        }
        _ => None,
    }
}

#[derive(Clone, Copy)]
enum Comparison {
    LessThan,
    LessEqual,
    Equal,
    Disequal,
}

impl SignedArithmeticComparison {
    fn from_comparison(comparison: Comparison) -> Self {
        match comparison {
            Comparison::LessThan => Self::LessThan,
            Comparison::LessEqual => Self::LessEqual,
            Comparison::Equal => Self::Equal,
            Comparison::Disequal => Self::Disequal,
        }
    }
}

fn interval_proves(
    left: &SignedArithmeticInterval,
    right: &SignedArithmeticInterval,
    comparison: Comparison,
) -> bool {
    match comparison {
        Comparison::LessThan => left.upper < right.lower,
        Comparison::LessEqual => left.upper <= right.lower,
        Comparison::Equal => {
            left.lower == left.upper && left.lower == right.lower && right.lower == right.upper
        }
        Comparison::Disequal => left.upper < right.lower || right.upper < left.lower,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::Variable;

    fn var(index: u64) -> Bitvector32Term {
        Bitvector32Term::Variable(Variable(index))
    }

    fn constant(value: i32) -> Bitvector32Term {
        Bitvector32Term::Constant(value as u32)
    }

    fn proposition(condition: ConditionTerm, value: bool) -> Proposition {
        Proposition::ConditionIs(condition, value)
    }

    fn le(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        proposition(
            ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right)),
            true,
        )
    }

    fn lt(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        proposition(
            ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
            true,
        )
    }

    fn defined_add(left: Bitvector32Term, right: Bitvector32Term) -> Proposition {
        proposition(
            ConditionTerm::Bitvector32SignedAddOverflows(Box::new(left), Box::new(right)),
            false,
        )
    }

    fn check_plan(goal: &Proposition, premises: &[Proposition]) -> SignedArithmeticCertificate {
        let plan =
            plan_signed_arithmetic_certificate(goal, premises).expect("planner should find proof");
        plan.check(goal, premises)
            .expect("independent checker should accept planner output");
        plan
    }

    #[test]
    fn two_sided_compound_affine_evidence_scales_with_shared_depth() {
        let mut work = Vec::new();
        for depth in [2usize, 4, 8, 16] {
            let mut left_base = var(1);
            let mut right_base = var(2);
            for _ in 0..depth {
                left_base = Bitvector32Term::Add(Box::new(left_base), Box::new(constant(0)));
                right_base = Bitvector32Term::Add(Box::new(right_base), Box::new(constant(0)));
            }
            let left = Bitvector32Term::Add(Box::new(left_base), Box::new(constant(1)));
            let right = Bitvector32Term::Add(Box::new(right_base), Box::new(constant(1)));
            let goal = le(left, right);
            let premises = vec![
                le(var(1), var(2)),
                le(constant(0), var(1)),
                le(var(1), constant(100)),
                le(constant(0), var(2)),
                le(var(2), constant(100)),
            ];
            let (plan, measured) = crate::instrumentation::measure_deterministic_work(|| {
                let plan = check_plan(&goal, &premises);
                assert!(plan.nodes.iter().any(|node| matches!(
                    node,
                    SignedArithmeticNode::AffineConclusionWithEvidence { .. }
                )));
                plan
            });
            assert!(!plan.nodes.is_empty());
            work.push(measured);
        }
        assert!(work.windows(2).all(|pair| pair[1] > pair[0]), "{work:?}");
        assert!(
            work.windows(2).all(|pair| pair[1] <= 4 * pair[0] + 64),
            "two-sided evidence should have bounded scaling: {work:?}"
        );
    }

    #[test]
    fn predecessor_is_less_than_nonnegative_operand() {
        let n = var(90);
        let goal = lt(
            Bitvector32Term::Subtract(Box::new(n.clone()), Box::new(constant(1))),
            n.clone(),
        );
        let plan = check_plan(&goal, &[le(constant(0), n)]);
        assert!(plan.nodes.iter().any(|node| matches!(
            node,
            SignedArithmeticNode::AffineConclusion { .. }
                | SignedArithmeticNode::AffineConclusionWithEvidence { .. }
        )));
    }

    #[test]
    fn predecessor_with_derived_leaf_and_extra_bounds() {
        let n = var(90);
        let predecessor = Bitvector32Term::Subtract(Box::new(n.clone()), Box::new(constant(1)));
        let goal = lt(predecessor.clone(), n.clone());
        let premises = vec![
            le(constant(0), predecessor),
            le(constant(0), n.clone()),
            lt(constant(0), n),
        ];
        let plan = plan_signed_arithmetic_certificate(&goal, &premises);
        assert!(plan.is_some(), "{plan:?}");
        plan.expect("plan").check(&goal, &premises).expect("check");
    }

    #[test]
    fn predecessor_with_greater_equal_bound() {
        let n = var(90);
        let predecessor = Bitvector32Term::Subtract(Box::new(n.clone()), Box::new(constant(1)));
        let goal = lt(predecessor.clone(), n.clone());
        let ge = proposition(
            ConditionTerm::Bitvector32SignedGreaterEqual(
                Box::new(n.clone()),
                Box::new(constant(0)),
            ),
            true,
        );
        let premises = vec![le(constant(0), predecessor), ge];
        let plan = plan_signed_arithmetic_certificate(&goal, &premises);
        assert!(plan.is_some(), "{plan:?}");
        plan.expect("plan").check(&goal, &premises).expect("check");
    }

    #[test]
    fn affine_equality_to_strict_bound_is_explicit() {
        let x = var(1);
        let equality = proposition(
            ConditionTerm::Bitvector32Equal(Box::new(x.clone()), Box::new(constant(1))),
            true,
        );
        let goal = lt(x, constant(1000));
        let plan = check_plan(&goal, std::slice::from_ref(&equality));
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::EqualityToLessEqual { .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::Add { .. }))
        );
    }

    #[test]
    fn bounded_addition_uses_exact_definedness_and_no_duplicate_premise() {
        let a = var(1);
        let b = var(2);
        let lower_a = le(constant(0), a.clone());
        let upper_a = le(a.clone(), constant(10));
        let lower_b = le(constant(0), b.clone());
        let upper_b = le(b.clone(), constant(20));
        let defined = defined_add(a.clone(), b.clone());
        let sum = Bitvector32Term::Add(Box::new(a), Box::new(b));
        let goal = le(sum, constant(30));
        let premises = vec![lower_a, upper_a, lower_b, upper_b, defined];
        let plan = check_plan(&goal, &premises);
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::DefinedPremise { index: 4, .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalAdd { .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::Add { .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::AffineConclusion { .. }))
        );
    }

    #[test]
    fn defined_addition_can_prove_a_lower_bound_without_upper_bounds() {
        let a = var(11);
        let b = var(12);
        let lower_a = le(constant(0), a.clone());
        let lower_b = le(constant(0), b.clone());
        let defined = defined_add(a.clone(), b.clone());
        let sum = Bitvector32Term::Add(Box::new(a), Box::new(b));
        let goal = le(constant(0), sum);
        let premises = vec![lower_a, lower_b, defined];
        let plan = check_plan(&goal, &premises);
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::DefinedPremise { index: 2, .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalAdd { .. }))
        );
        assert!(
            plan.nodes
                .iter()
                .filter(|node| matches!(node, SignedArithmeticNode::Premise { .. }))
                .count()
                >= 2
        );

        let without_definedness = vec![premises[0].clone(), premises[1].clone()];
        assert!(plan_signed_arithmetic_certificate(&goal, &without_definedness).is_none());

        let mut tampered_definedness = plan.clone();
        let node = tampered_definedness
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::DefinedPremise { .. }))
            .expect("definedness node");
        if let SignedArithmeticNode::DefinedPremise { term, .. } = node {
            *term = Bitvector32Term::Add(Box::new(var(11)), Box::new(var(99)));
        }
        assert!(tampered_definedness.check(&goal, &premises).is_err());
    }

    #[test]
    fn bounded_doubling_reuses_bounds_without_definedness_or_duplicate_premises() {
        let n = var(13);
        let lower = le(constant(0), n.clone());
        let upper = le(n.clone(), constant(100));
        let doubled = Bitvector32Term::Add(Box::new(n.clone()), Box::new(n.clone()));
        let goal = le(doubled, constant(200));
        let plan = check_plan(&goal, &[lower, upper]);
        assert!(plan.nodes.iter().any(|node| matches!(
            node,
            SignedArithmeticNode::IntervalAddBounded { left, right, .. } if left == right
        )));
        assert!(plan.nodes.iter().any(|node| matches!(
            node,
            SignedArithmeticNode::Scale { coefficient, .. } if coefficient == &BigInt::from(2)
        )));
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::AffineConclusion { .. }))
        );
        assert!(
            !plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::DefinedPremise { .. }))
        );
        assert_eq!(
            plan.nodes
                .iter()
                .filter(|node| matches!(node, SignedArithmeticNode::Premise { .. }))
                .count(),
            2
        );

        let wide_upper = le(n.clone(), constant(i32::MAX));
        assert!(
            plan_signed_arithmetic_certificate(&goal, &[le(constant(0), n.clone()), wide_upper])
                .is_none()
        );

        let mut tampered = plan.clone();
        let node = tampered
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::IntervalAddBounded { .. }))
            .expect("bounded addition node");
        if let SignedArithmeticNode::IntervalAddBounded { result, .. } = node {
            result.upper += 1;
        }
        assert!(
            tampered
                .check(
                    &goal,
                    &[le(constant(0), var(13)), le(var(13), constant(100))]
                )
                .is_err()
        );

        let mut tampered_scale = plan.clone();
        let node = tampered_scale
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::Scale { .. }))
            .expect("scale node");
        if let SignedArithmeticNode::Scale { coefficient, .. } = node {
            *coefficient = BigInt::from(3);
        }
        assert!(
            tampered_scale
                .check(
                    &goal,
                    &[le(constant(0), var(13)), le(var(13), constant(100))]
                )
                .is_err()
        );

        let premises = [le(constant(0), var(13)), le(var(13), constant(100))];
        let mut wrong_evidence_root = plan.clone();
        let node = wrong_evidence_root
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::AffineConclusion { .. }))
            .expect("affine conclusion node");
        if let SignedArithmeticNode::AffineConclusion { evidence, .. } = node {
            *evidence = 0;
        }
        assert!(wrong_evidence_root.check(&goal, &premises).is_err());

        let mut wrong_child = plan.clone();
        let node = wrong_child
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::IntervalAddBounded { .. }))
            .expect("bounded addition node");
        if let SignedArithmeticNode::IntervalAddBounded { left, .. } = node {
            *left = usize::MAX;
        }
        assert!(wrong_child.check(&goal, &premises).is_err());

        let mut wrong_operator = plan.clone();
        let node = wrong_operator
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::IntervalAddBounded { .. }))
            .expect("bounded addition node");
        if let SignedArithmeticNode::IntervalAddBounded {
            left,
            right,
            result,
        } = node
        {
            let left = *left;
            let right = *right;
            let result = result.clone();
            *node = SignedArithmeticNode::IntervalSubtract {
                left,
                right,
                defined: 0,
                result,
            };
        }
        assert!(wrong_operator.check(&goal, &premises).is_err());

        let mut wrong_expression = plan.clone();
        let node = wrong_expression
            .nodes
            .iter_mut()
            .find(|node| matches!(node, SignedArithmeticNode::AffineConclusion { .. }))
            .expect("affine conclusion node");
        if let SignedArithmeticNode::AffineConclusion { result, .. } = node {
            *result = le(
                Bitvector32Term::Add(Box::new(var(13)), Box::new(var(14))),
                constant(200),
            );
        }
        assert!(wrong_expression.check(&goal, &premises).is_err());
    }

    #[test]
    fn scale_factor_work_charges_large_coefficients_and_key_lookups() {
        let atom = SignedArithmeticAtom::from_term(&var(31)).unwrap();
        let source = SignedArithmeticClaim {
            carrier: SignedArithmeticCarrier::SignedInt32,
            relation: SignedArithmeticRelation::LessEqual,
            terms: BTreeMap::from([(atom.clone(), BigInt::one())]),
            constant: BigInt::zero(),
        };
        let mut measurements = Vec::new();
        for bits in [8usize, 16, 32, 64] {
            let target = SignedArithmeticClaim {
                carrier: SignedArithmeticCarrier::SignedInt32,
                relation: SignedArithmeticRelation::LessEqual,
                terms: BTreeMap::from([(atom.clone(), BigInt::one() << bits)]),
                constant: BigInt::zero(),
            };
            let (result, work) = crate::instrumentation::measure_deterministic_work(|| {
                scale_factor(&source, &target)
            });
            assert_eq!(result, Some(BigInt::one() << bits));
            measurements.push(work);
        }
        assert!(
            measurements.windows(2).all(|pair| pair[1] > pair[0]),
            "scale-factor BigInt work must scale: {measurements:?}"
        );
        assert!(
            measurements
                .windows(2)
                .all(|pair| pair[1] <= 8 * pair[0] + 64),
            "scale-factor work should have bounded scaling: {measurements:?}"
        );
    }

    #[test]
    fn bounded_remainder_shift_mask_product_and_sign_flip_are_planned() {
        let x = var(3);
        let lower = le(constant(0), x.clone());
        let upper = le(x.clone(), constant(10));

        let remainder = Bitvector32Term::Remainder(Box::new(x.clone()), Box::new(constant(7)));
        let remainder_goal = le(remainder.clone(), constant(6));
        let remainder_defined = proposition(
            ConditionTerm::Bitvector32SignedDivideOverflows(
                Box::new(x.clone()),
                Box::new(constant(7)),
            ),
            false,
        );
        let remainder_plan = check_plan(
            &remainder_goal,
            &[lower.clone(), upper.clone(), remainder_defined],
        );
        assert!(
            remainder_plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalRemainder { .. }))
        );

        let shift = Bitvector32Term::ShiftLeft(Box::new(x.clone()), Box::new(constant(2)));
        let shift_goal = le(shift.clone(), constant(40));
        let shift_defined = proposition(
            ConditionTerm::Bitvector32SignedShiftLeftOverflows(
                Box::new(x.clone()),
                Box::new(constant(2)),
            ),
            false,
        );
        let shift_plan = check_plan(&shift_goal, &[lower.clone(), upper.clone(), shift_defined]);
        assert!(
            shift_plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalShiftLeft { .. }))
        );

        let mask = Bitvector32Term::BitwiseAnd(Box::new(x.clone()), Box::new(constant(255)));
        let mask_goal = le(mask, constant(255));
        let mask_plan = check_plan(&mask_goal, &[]);
        assert!(
            mask_plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalBitwiseAnd { .. }))
        );

        let product = Bitvector32Term::Multiply(Box::new(x.clone()), Box::new(x.clone()));
        let product_goal = le(product.clone(), constant(100));
        let product_defined = proposition(
            ConditionTerm::Bitvector32SignedMultiplyOverflows(
                Box::new(x.clone()),
                Box::new(x.clone()),
            ),
            false,
        );
        let product_plan = check_plan(
            &product_goal,
            &[lower.clone(), upper.clone(), product_defined],
        );
        assert!(
            product_plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalMultiply { .. }))
        );

        let flipped =
            Bitvector32Term::BitwiseXor(Box::new(x.clone()), Box::new(constant(i32::MIN)));
        let flip_goal = le(flipped, constant(-2_147_483_638));
        let flip_plan = check_plan(&flip_goal, &[lower, upper]);
        assert!(
            flip_plan
                .nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalSignBitFlip { .. }))
        );
    }

    #[test]
    fn deep_supported_addition_builds_iterative_interval_affine_evidence() {
        let x = var(9);
        let lower = le(constant(0), x.clone());
        let upper = le(x.clone(), constant(1));
        let mut term = x.clone();
        for _ in 0..127 {
            term = Bitvector32Term::Add(Box::new(term), Box::new(x.clone()));
        }
        let goal = le(term, constant(128));
        let plan = check_plan(&goal, &[lower, upper]);
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::IntervalAddBounded { .. }))
        );
        assert!(plan
            .nodes
            .iter()
            .any(|node| matches!(node, SignedArithmeticNode::Scale { coefficient, .. } if coefficient == &BigInt::from(128))));
        assert!(
            plan.nodes
                .iter()
                .any(|node| matches!(node, SignedArithmeticNode::AffineConclusion { .. }))
        );

        let overflowing_inner = Bitvector32Term::Add(Box::new(x.clone()), Box::new(constant(1)));
        let final_in_range =
            Bitvector32Term::Subtract(Box::new(overflowing_inner), Box::new(constant(1)));
        let final_goal = le(final_in_range, constant(i32::MAX));
        let bounds = [le(constant(0), x.clone()), le(x, constant(i32::MAX))];
        assert!(plan_signed_arithmetic_certificate(&final_goal, &bounds).is_none());
    }

    #[test]
    fn deep_affine_plans_have_bounded_work_and_node_growth() {
        let mut measurements = Vec::new();
        for depth in [4usize, 8, 16, 32] {
            let x = var(71);
            let mut term = x.clone();
            for _ in 0..depth {
                term = Bitvector32Term::Add(Box::new(term), Box::new(x.clone()));
            }
            let goal = le(term, constant(depth as i32 + 1));
            let premises = [le(constant(0), x.clone()), le(x, constant(1))];
            let (plan, work) =
                crate::instrumentation::measure_deterministic_work(|| check_plan(&goal, &premises));
            assert!(
                plan.nodes.len() <= 12 * depth + 32,
                "certificate node count grew beyond the expression: {} at depth {depth}",
                plan.nodes.len()
            );
            measurements.push(work);
        }
        assert!(
            measurements
                .windows(2)
                .all(|pair| pair[1] <= 4 * pair[0] + 128),
            "deep affine planning should have bounded scaling: {measurements:?}"
        );
    }

    #[test]
    fn indexed_operation_lookup_scales_with_deep_terms_and_unrelated_facts() {
        let mut measurements = Vec::new();
        for (depth, unrelated) in [(8usize, 4usize), (16, 8), (32, 16), (64, 32)] {
            let x = var(72);
            let mut term = x.clone();
            for _ in 0..depth {
                term = Bitvector32Term::Add(Box::new(term), Box::new(x.clone()));
            }
            let goal = le(term, constant(depth as i32 + 1));
            let mut premises = vec![le(constant(0), x.clone()), le(x, constant(1))];
            premises
                .extend((0..unrelated).map(|index| le(var(10_000 + index as u64), constant(0))));
            let (plan, work) =
                crate::instrumentation::measure_deterministic_work(|| check_plan(&goal, &premises));
            assert!(plan.nodes.len() <= 12 * depth + 32);
            measurements.push(work);
        }
        assert!(
            measurements
                .windows(2)
                .all(|pair| pair[1] <= 3 * pair[0] + 256),
            "indexed operation lookup should avoid depth-by-fact rescans: {measurements:?}"
        );
    }

    #[test]
    fn nested_affine_bounds_have_linear_certificate_size() {
        for depth in [4usize, 8, 16, 32] {
            let x = var(73);
            let mut term = x.clone();
            let mut premises = vec![le(constant(0), x.clone()), le(x, constant(1))];
            for index in 0..depth {
                term = Bitvector32Term::Add(Box::new(term), Box::new(constant(1)));
                if index + 1 < depth {
                    premises.push(le(term.clone(), constant(index as i32 + 2)));
                }
            }
            let goal_term = Bitvector32Term::BitwiseAnd(Box::new(term), Box::new(constant(255)));
            let goal = le(goal_term, constant(255));
            let plan = plan_signed_arithmetic_certificate(&goal, &premises)
                .unwrap_or_else(|| panic!("no plan at depth {depth}"));
            plan.check(&goal, &premises)
                .expect("compact plan must check");
            let direct_nodes = plan
                .nodes
                .iter()
                .filter(|node| {
                    matches!(node, SignedArithmeticNode::IntervalFromAffineDirect { .. })
                })
                .count();
            assert!(
                direct_nodes <= 1,
                "a nested chain needs one direct root at most"
            );
            assert!(plan.nodes.len() <= 12 * depth + 32);
        }
    }

    #[test]
    fn planner_rejects_node_count_above_the_certificate_bound() {
        let mut planner = Planner::new(&[], &[]);
        let result = SignedArithmeticClaim {
            carrier: SignedArithmeticCarrier::SignedInt32,
            relation: SignedArithmeticRelation::LessEqual,
            terms: BTreeMap::new(),
            constant: BigInt::zero(),
        };
        for _ in 0..MAX_NODES {
            assert!(
                planner
                    .push(SignedArithmeticNode::Trivial {
                        result: result.clone(),
                    })
                    .is_some()
            );
        }
        assert!(
            planner
                .push(SignedArithmeticNode::Trivial { result })
                .is_none()
        );
    }
}
