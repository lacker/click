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

    let claims = premises
        .iter()
        .enumerate()
        .filter_map(|(index, proposition)| {
            charge_work(1)?;
            signed_claim(proposition).map(|claim| (index, claim))
        })
        .collect::<Vec<_>>();

    if let Some((index, claim)) = claims.iter().find(|(_, claim)| *claim == expected) {
        return Some(certificate(
            vec![SignedArithmeticNode::Premise {
                index: *index,
                result: claim.clone(),
            }],
            0,
        ));
    }
    if let Some(plan) = plan_affine_one_premise(&claims, &expected) {
        return Some(plan);
    }
    if let Some(plan) = plan_interval_goal(goal, premises, &claims) {
        return Some(plan);
    }
    None
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

fn affine_difference(
    left: &Bitvector32Term,
    right: &Bitvector32Term,
) -> Option<(BTreeMap<SignedArithmeticAtom, BigInt>, BigInt)> {
    let mut terms: BTreeMap<SignedArithmeticAtom, BigInt> = BTreeMap::new();
    let mut constant = BigInt::zero();
    let mut pending = vec![(left, BigInt::one()), (right, -BigInt::one())];
    while let Some((term, coefficient)) = pending.pop() {
        charge_work(1)?;
        if let Bitvector32Term::Constant(value) = term {
            constant += coefficient * BigInt::from(*value as i32);
        } else {
            let atom = SignedArithmeticAtom::from_term(term)?;
            let updated = terms.entry(atom.clone()).or_default().clone() + coefficient;
            if updated.is_zero() {
                terms.remove(&atom);
            } else {
                terms.insert(atom, updated);
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
        if source.relation == expected.relation
            && let Some(coefficient) = scale_factor(source, expected)
            && (source.relation == SignedArithmeticRelation::Equal
                || (coefficient >= BigInt::zero()
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

fn scale_factor(source: &SignedArithmeticClaim, target: &SignedArithmeticClaim) -> Option<BigInt> {
    if source.terms.is_empty() {
        if !target.terms.is_empty() {
            return None;
        }
        return (source.constant != BigInt::zero())
            .then(|| target.constant.clone() / &source.constant)
            .filter(|coefficient| source.constant.clone() * coefficient == target.constant);
    }
    let mut factor = None;
    for (atom, coefficient) in &source.terms {
        let target_coefficient = target.terms.get(atom).cloned().unwrap_or_default();
        if coefficient.is_zero() {
            continue;
        }
        let quotient = &target_coefficient / coefficient;
        if coefficient * &quotient != target_coefficient {
            return None;
        }
        if let Some(existing) = &factor {
            if existing != &quotient {
                return None;
            }
        } else {
            factor = Some(quotient);
        }
    }
    let factor = factor?;
    if source.constant.clone() * &factor != target.constant {
        return None;
    }
    if target
        .terms
        .keys()
        .any(|atom| !source.terms.contains_key(atom))
    {
        return None;
    }
    Some(factor)
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

struct Planner<'a> {
    premises: &'a [Proposition],
    claims: &'a [(usize, SignedArithmeticClaim)],
    nodes: Vec<SignedArithmeticNode>,
    intervals: Vec<Option<SignedArithmeticInterval>>,
    interval_cache: HashMap<SignedArithmeticAtom, usize>,
}

impl<'a> Planner<'a> {
    fn new(premises: &'a [Proposition], claims: &'a [(usize, SignedArithmeticClaim)]) -> Self {
        Self {
            premises,
            claims,
            nodes: Vec::new(),
            intervals: Vec::new(),
            interval_cache: HashMap::new(),
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
        self.push(SignedArithmeticNode::Premise {
            index,
            result: claim.clone(),
        })
    }

    fn defined(&mut self, term: &Bitvector32Term) -> Option<usize> {
        let index = self
            .premises
            .iter()
            .enumerate()
            .find_map(|(index, proposition)| {
                exact_definedness(proposition, term).then_some(index)
            })?;
        self.push(SignedArithmeticNode::DefinedPremise {
            index,
            carrier: SignedArithmeticCarrier::SignedInt32,
            term: term.clone(),
        })
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
        if !Self::is_safe_interval_atom(term) {
            return None;
        }
        let atom = SignedArithmeticAtom::from_term(term)?;
        let mut lower: Option<(usize, SignedArithmeticClaim, i64)> = None;
        let mut upper: Option<(usize, SignedArithmeticClaim, i64)> = None;
        for (index, claim) in self.claims {
            if claim.relation != SignedArithmeticRelation::LessEqual || claim.terms.len() != 1 {
                continue;
            }
            let (claim_atom, coefficient) = claim.terms.iter().next()?;
            if claim_atom != &atom {
                continue;
            }
            if coefficient == &BigInt::from(-1) {
                let bound = claim.constant.to_i64()?.max(SIGNED_MIN);
                if lower.as_ref().is_none_or(|(_, _, old)| bound > *old) {
                    lower = Some((*index, claim.clone(), bound));
                }
            } else if coefficient == &BigInt::one() {
                let bound = (-&claim.constant).to_i64()?.min(SIGNED_MAX);
                if upper.as_ref().is_none_or(|(_, _, old)| bound < *old) {
                    upper = Some((*index, claim.clone(), bound));
                }
            }
        }
        if lower.is_none() && upper.is_none() {
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
        let Some((lower_index, lower_claim, lower_bound)) = lower else {
            let (upper_index, upper_claim, upper_bound) = upper?;
            let upper_node = self.premise(upper_index, &upper_claim)?;
            let index = self.push_interval(
                SignedArithmeticNode::IntervalFromAffine {
                    source: upper_node,
                    term: term.clone(),
                    lower: SIGNED_MIN,
                    upper: upper_bound,
                },
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
            SignedArithmeticNode::IntervalFromAffine {
                source: lower_node,
                term: term.clone(),
                lower: lower_bound,
                upper: SIGNED_MAX,
            },
            SignedArithmeticInterval {
                carrier: SignedArithmeticCarrier::SignedInt32,
                lower: lower_bound,
                upper: SIGNED_MAX,
            },
        )?;
        if let Some((upper_index, upper_claim, upper_bound)) = upper {
            let upper_node = self.premise(upper_index, &upper_claim)?;
            let upper_interval = self.push_interval(
                SignedArithmeticNode::IntervalFromAffine {
                    source: upper_node,
                    term: term.clone(),
                    lower: SIGNED_MIN,
                    upper: upper_bound,
                },
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
        enum Task<'a> {
            Visit(&'a Bitvector32Term),
            Build(&'a Bitvector32Term),
        }
        let mut tasks = vec![Task::Visit(root)];
        let mut results = Vec::new();
        while let Some(task) = tasks.pop() {
            charge_work(1)?;
            match task {
                Task::Visit(term) => match term {
                    Bitvector32Term::Constant(_) => results.push(self.interval_atom(term)?),
                    Bitvector32Term::Add(left, right)
                    | Bitvector32Term::Subtract(left, right)
                    | Bitvector32Term::Multiply(left, right) => {
                        tasks.push(Task::Build(term));
                        tasks.push(Task::Visit(right));
                        tasks.push(Task::Visit(left));
                    }
                    Bitvector32Term::Remainder(operand, divisor)
                    | Bitvector32Term::ShiftLeft(operand, divisor)
                    | Bitvector32Term::ArithmeticShiftRight(operand, divisor)
                    | Bitvector32Term::BitwiseAnd(operand, divisor)
                    | Bitvector32Term::BitwiseXor(operand, divisor) => {
                        divisor.as_const()?;
                        tasks.push(Task::Build(term));
                        tasks.push(Task::Visit(operand));
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
        left: Option<usize>,
        right: Option<usize>,
    ) -> Option<usize> {
        match term {
            Bitvector32Term::Add(_, _) => {
                let left = left?;
                let right = right?;
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
                let left = left?;
                let right = right?;
                let defined = self.defined(term)?;
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
                let left = left?;
                let right = right?;
                let defined = self.defined(term)?;
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
                let operand = right?;
                let divisor = divisor.as_const()?.to_i32()?;
                if divisor == 0 {
                    return None;
                }
                let defined = self.defined(term)?;
                let op = self.interval_at(operand)?;
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
                let operand = right?;
                let shift = shift.as_const()?.to_i32()?;
                if !(0..32).contains(&shift) {
                    return None;
                }
                let defined = self.defined(term)?;
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
                let operand = right?;
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
            Bitvector32Term::BitwiseAnd(_, mask) => {
                let operand = right?;
                let mask = mask.as_const()?;
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
            Bitvector32Term::BitwiseXor(_, sign_bit) => {
                let operand = right?;
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
        ) => {
            SignedArithmeticAtom::from_term(left) == SignedArithmeticAtom::from_term(a)
                && SignedArithmeticAtom::from_term(right) == SignedArithmeticAtom::from_term(b)
        }
        _ => false,
    }
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
    if !interval_proves(&left_interval, &right_interval, comparison) {
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
    fn deep_affine_atom_plans_iteratively() {
        let mut term = var(9);
        for _ in 0..128 {
            term = Bitvector32Term::Add(Box::new(term), Box::new(constant(0)));
        }
        let premise = le(term.clone(), constant(100));
        let goal = le(term, constant(100));
        let plan = check_plan(&goal, std::slice::from_ref(&premise));
        assert!(matches!(
            plan.nodes.first(),
            Some(SignedArithmeticNode::Premise { .. })
        ));
    }
}
