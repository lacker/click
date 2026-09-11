//! Bounded planning for the checked mathematical-Integer affine fragment.
//!
//! This module only chooses a small certificate made from the kernel's
//! existing arithmetic nodes.  It never searches the ambient proof state: the
//! caller supplies the exact premise slice.  In particular, two-premise
//! combinations are solved by a bounded two-dimensional integer calculation,
//! rather than by an LP solver or a growing coefficient search.

use crate::kernel::Proposition;
use crate::kernel::proof::integer_arithmetic::{
    IntegerAffineAtom, IntegerAffineClaim, IntegerAffineRelation, IntegerArithmeticCertificate,
    IntegerArithmeticNode, integer_affine_claim,
};
use num_bigint::BigInt;
use num_traits::{One, Signed, Zero};
use std::collections::{BTreeMap, BTreeSet};

/// Keep planner work proportional to the explicitly selected premise slice.
/// A larger slice is left to the ordinary simple-proof routes instead of
/// turning this bounded planner into an ambient scan.
const MAX_SELECTED_PREMISES: usize = 64;
const MAX_PAIR_ATTEMPTS: usize = 4_096;

pub(in crate::surface) fn plan_integer_affine_certificate(
    goal: &Proposition,
    premises: &[Proposition],
) -> Option<IntegerArithmeticCertificate> {
    if premises.len() > MAX_SELECTED_PREMISES {
        return None;
    }
    let expected = integer_affine_claim(goal)?;
    if claim_is_integer_trivial(&expected) {
        return Some(IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Trivial { result: expected }],
            conclusion: 0,
        });
    }

    // Normalize each selected proposition once.  The kernel recomputes the
    // same checked fold atom key when it validates the certificate; matching
    // these claims is therefore alpha/snapshot aware rather than a raw source
    // proposition comparison.
    // Unrelated machine/logical premises are allowed in the selected slice;
    // skip them while retaining the caller's original premise index.  A
    // deadline is distinct from an unsupported proposition and is propagated.
    let mut claims = Vec::new();
    for (index, premise) in premises.iter().enumerate() {
        charge_planner_work(1)?;
        if let Some(claim) = integer_affine_claim(premise) {
            claims.push((index, claim));
        }
    }

    if let Some((index, _)) = claims.iter().find(|(_, claim)| claim.eq(&expected)) {
        return Some(IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Premise {
                index: *index,
                result: expected.clone(),
            }],
            conclusion: 0,
        });
    }

    if let Some(certificate) = plan_equality_from_opposite_bounds(&claims, &expected) {
        return Some(certificate);
    }

    // A one-premise certificate covers equality directions, nonnegative
    // scaling, and weakening an order constant with a context-free trivial
    // claim.  This is also the fast path for the common `x == y` -> `x <= y`
    // and `2*x <= 2*y` cases.
    for (index, source) in &claims {
        charge_planner_work(1)?;
        if let Some(certificate) = plan_from_one_premise(*index, source, &expected) {
            return Some(certificate);
        }
    }

    // At most two selected premises may participate in a combination.  The
    // pair solver uses two non-collinear affine coordinates (terms, with the
    // constant as a final coordinate) and Cramer's rule.  If no such pair
    // exists, a direct one-premise derivation would already cover the
    // proportional case; there is no unbounded Diophantine search here.
    let mut attempts = 0usize;
    for left in 0..claims.len() {
        for right in (left + 1)..claims.len() {
            if attempts == MAX_PAIR_ATTEMPTS {
                return None;
            }
            attempts += 1;
            charge_planner_work(1)?;
            if let Some(certificate) =
                plan_from_two_premises(&claims[left], &claims[right], &expected)
            {
                return Some(certificate);
            }
        }
    }
    None
}

fn plan_equality_from_opposite_bounds(
    claims: &[(usize, IntegerAffineClaim)],
    expected: &IntegerAffineClaim,
) -> Option<IntegerArithmeticCertificate> {
    if expected.relation != IntegerAffineRelation::Equal {
        return None;
    }
    for (lower_position, (lower_index, lower)) in claims.iter().enumerate() {
        charge_planner_work(1)?;
        if lower.relation != IntegerAffineRelation::LessEqual
            || lower.terms != expected.terms
            || lower.constant != expected.constant
        {
            continue;
        }
        let mut opposite_terms = BTreeMap::new();
        for (atom, coefficient) in &expected.terms {
            opposite_terms.insert(atom.clone(), -coefficient);
        }
        for (upper_position, (upper_index, upper)) in claims.iter().enumerate() {
            charge_planner_work(1)?;
            if upper_position != lower_position
                && upper.relation == IntegerAffineRelation::LessEqual
                && upper.terms == opposite_terms
                && upper.constant == -&expected.constant
            {
                return Some(IntegerArithmeticCertificate {
                    nodes: vec![
                        IntegerArithmeticNode::Premise {
                            index: *lower_index,
                            result: lower.clone(),
                        },
                        IntegerArithmeticNode::Premise {
                            index: *upper_index,
                            result: upper.clone(),
                        },
                        IntegerArithmeticNode::EqualityFromBounds {
                            lower: 0,
                            upper: 1,
                            result: expected.clone(),
                        },
                    ],
                    conclusion: 2,
                });
            }
        }
    }
    None
}

fn plan_from_one_premise(
    index: usize,
    source: &IntegerAffineClaim,
    expected: &IntegerAffineClaim,
) -> Option<IntegerArithmeticCertificate> {
    if source.relation == expected.relation
        && let Some(coefficient) = scale_factor(source, expected)
        && (source.relation == IntegerAffineRelation::Equal || coefficient >= BigInt::zero())
    {
        return scaled_certificate(index, source, coefficient, expected);
    }

    // For `sum + constant <= 0`, a larger source constant is a stronger
    // upper bound.  Weaken it using a checked context-free nonpositive
    // constant and the existing Add node.
    if source.relation == IntegerAffineRelation::LessEqual
        && expected.relation == IntegerAffineRelation::LessEqual
        && source.terms == expected.terms
        && source.constant >= expected.constant
    {
        return weakened_order_certificate(index, source, expected);
    }

    if expected.relation != IntegerAffineRelation::LessEqual
        || source.relation != IntegerAffineRelation::Equal
    {
        return None;
    }

    for reverse in [false, true] {
        let direction = equality_direction(source, reverse);
        if direction == *expected {
            return Some(IntegerArithmeticCertificate {
                nodes: vec![
                    IntegerArithmeticNode::Premise {
                        index,
                        result: source.clone(),
                    },
                    IntegerArithmeticNode::EqualityToLessEqual {
                        source: 0,
                        reverse,
                        result: direction,
                    },
                ],
                conclusion: 1,
            });
        }
        if let Some(coefficient) = scale_factor(&direction, expected)
            && coefficient >= BigInt::zero()
            && let Some(certificate) =
                scaled_direction_certificate(index, source, reverse, coefficient, expected)
        {
            return Some(certificate);
        }
        if let Some(certificate) = weakened_direction_certificate(index, source, reverse, expected)
        {
            return Some(certificate);
        }
    }
    None
}

fn scaled_certificate(
    index: usize,
    source: &IntegerAffineClaim,
    coefficient: BigInt,
    expected: &IntegerAffineClaim,
) -> Option<IntegerArithmeticCertificate> {
    if coefficient == BigInt::one() {
        return Some(IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Premise {
                index,
                result: source.clone(),
            }],
            conclusion: 0,
        });
    }
    Some(IntegerArithmeticCertificate {
        nodes: vec![
            IntegerArithmeticNode::Premise {
                index,
                result: source.clone(),
            },
            IntegerArithmeticNode::Scale {
                source: 0,
                coefficient,
                result: expected.clone(),
            },
        ],
        conclusion: 1,
    })
}

fn scaled_direction_certificate(
    index: usize,
    source: &IntegerAffineClaim,
    reverse: bool,
    coefficient: BigInt,
    expected: &IntegerAffineClaim,
) -> Option<IntegerArithmeticCertificate> {
    if coefficient.is_zero() {
        return None;
    }
    Some(IntegerArithmeticCertificate {
        nodes: vec![
            IntegerArithmeticNode::Premise {
                index,
                result: source.clone(),
            },
            IntegerArithmeticNode::EqualityToLessEqual {
                source: 0,
                reverse,
                result: equality_direction(source, reverse),
            },
            IntegerArithmeticNode::Scale {
                source: 1,
                coefficient,
                result: expected.clone(),
            },
        ],
        conclusion: 2,
    })
}

fn weakened_direction_certificate(
    index: usize,
    source: &IntegerAffineClaim,
    reverse: bool,
    expected: &IntegerAffineClaim,
) -> Option<IntegerArithmeticCertificate> {
    let direction = equality_direction(source, reverse);
    if direction.terms != expected.terms || expected.constant > direction.constant {
        return None;
    }
    let weakening = &expected.constant - &direction.constant;
    if weakening.is_zero() {
        return Some(IntegerArithmeticCertificate {
            nodes: vec![
                IntegerArithmeticNode::Premise {
                    index,
                    result: source.clone(),
                },
                IntegerArithmeticNode::EqualityToLessEqual {
                    source: 0,
                    reverse,
                    result: expected.clone(),
                },
            ],
            conclusion: 1,
        });
    }
    Some(IntegerArithmeticCertificate {
        nodes: vec![
            IntegerArithmeticNode::Premise {
                index,
                result: source.clone(),
            },
            IntegerArithmeticNode::EqualityToLessEqual {
                source: 0,
                reverse,
                result: direction.clone(),
            },
            IntegerArithmeticNode::Trivial {
                result: IntegerAffineClaim {
                    relation: IntegerAffineRelation::LessEqual,
                    terms: BTreeMap::new(),
                    constant: weakening,
                },
            },
            IntegerArithmeticNode::Add {
                left: 1,
                right: 2,
                result: expected.clone(),
            },
        ],
        conclusion: 3,
    })
}

fn weakened_order_certificate(
    index: usize,
    source: &IntegerAffineClaim,
    expected: &IntegerAffineClaim,
) -> Option<IntegerArithmeticCertificate> {
    let weakening = &expected.constant - &source.constant;
    if weakening.is_positive() {
        return None;
    }
    if weakening.is_zero() {
        return Some(IntegerArithmeticCertificate {
            nodes: vec![IntegerArithmeticNode::Premise {
                index,
                result: source.clone(),
            }],
            conclusion: 0,
        });
    }
    Some(IntegerArithmeticCertificate {
        nodes: vec![
            IntegerArithmeticNode::Premise {
                index,
                result: source.clone(),
            },
            IntegerArithmeticNode::Trivial {
                result: IntegerAffineClaim {
                    relation: IntegerAffineRelation::LessEqual,
                    terms: BTreeMap::new(),
                    constant: weakening,
                },
            },
            IntegerArithmeticNode::Add {
                left: 0,
                right: 1,
                result: expected.clone(),
            },
        ],
        conclusion: 2,
    })
}

fn plan_from_two_premises(
    left: &(usize, IntegerAffineClaim),
    right: &(usize, IntegerAffineClaim),
    expected: &IntegerAffineClaim,
) -> Option<IntegerArithmeticCertificate> {
    if expected.relation == IntegerAffineRelation::Equal {
        if left.1.relation != IntegerAffineRelation::Equal
            || right.1.relation != IntegerAffineRelation::Equal
        {
            return None;
        }
        let (left_coefficient, right_coefficient) =
            solve_coefficients(&left.1, &right.1, expected, false)?;
        return combination_certificate(
            left,
            right,
            expected,
            false,
            false,
            left_coefficient,
            right_coefficient,
            left.1.clone(),
            right.1.clone(),
            false,
        );
    }

    // Equality premises may contribute either checked order direction.  The
    // direction is selected before nonnegative scaling, so a negative Scale
    // node can never smuggle an invalid inequality through the planner.
    let left_directions = order_directions(&left.1);
    let right_directions = order_directions(&right.1);
    for (left_reverse, left_direction) in &left_directions {
        for (right_reverse, right_direction) in &right_directions {
            let Some((left_coefficient, right_coefficient)) =
                solve_coefficients(left_direction, right_direction, expected, true)
            else {
                continue;
            };
            if left_coefficient.is_negative() || right_coefficient.is_negative() {
                continue;
            }
            if let Some(certificate) = combination_certificate(
                left,
                right,
                expected,
                *left_reverse,
                *right_reverse,
                left_coefficient,
                right_coefficient,
                left_direction.clone(),
                right_direction.clone(),
                true,
            ) {
                return Some(certificate);
            }
        }
    }
    None
}

fn combination_certificate(
    left: &(usize, IntegerAffineClaim),
    right: &(usize, IntegerAffineClaim),
    expected: &IntegerAffineClaim,
    left_reverse: bool,
    right_reverse: bool,
    left_coefficient: BigInt,
    right_coefficient: BigInt,
    left_direction: IntegerAffineClaim,
    right_direction: IntegerAffineClaim,
    inequality: bool,
) -> Option<IntegerArithmeticCertificate> {
    if left_coefficient.is_zero() || right_coefficient.is_zero() {
        return None;
    }
    let mut nodes = Vec::new();
    nodes.push(IntegerArithmeticNode::Premise {
        index: left.0,
        result: left.1.clone(),
    });
    let left_source = if left.1.relation == IntegerAffineRelation::Equal && inequality {
        let index = nodes.len();
        nodes.push(IntegerArithmeticNode::EqualityToLessEqual {
            source: 0,
            reverse: left_reverse,
            result: left_direction.clone(),
        });
        index
    } else {
        0
    };
    let left_scaled = append_scale_node(
        &mut nodes,
        left_source,
        left_direction.clone(),
        left_coefficient.clone(),
    )?;
    nodes.push(IntegerArithmeticNode::Premise {
        index: right.0,
        result: right.1.clone(),
    });
    let right_source = nodes.len() - 1;
    let right_source = if right.1.relation == IntegerAffineRelation::Equal && inequality {
        let index = nodes.len();
        nodes.push(IntegerArithmeticNode::EqualityToLessEqual {
            source: right_source,
            reverse: right_reverse,
            result: right_direction.clone(),
        });
        index
    } else {
        right_source
    };
    let right_scaled = append_scale_node(
        &mut nodes,
        right_source,
        right_direction.clone(),
        right_coefficient.clone(),
    )?;
    let left_contribution = scale_claim(&left_direction, &left_coefficient)?;
    let right_contribution = scale_claim(&right_direction, &right_coefficient)?;
    let combined = add_claim(&left_contribution, &right_contribution)?;
    if inequality {
        if combined.terms != expected.terms || combined.constant < expected.constant {
            return None;
        }
        let weakening = &expected.constant - &combined.constant;
        let combined_index = nodes.len();
        nodes.push(IntegerArithmeticNode::Add {
            left: left_scaled,
            right: right_scaled,
            result: combined.clone(),
        });
        if !weakening.is_zero() {
            let trivial_index = nodes.len();
            nodes.push(IntegerArithmeticNode::Trivial {
                result: IntegerAffineClaim {
                    relation: IntegerAffineRelation::LessEqual,
                    terms: BTreeMap::new(),
                    constant: weakening,
                },
            });
            nodes.push(IntegerArithmeticNode::Add {
                left: combined_index,
                right: trivial_index,
                result: expected.clone(),
            });
        } else {
            // The exact combination already is the requested conclusion.
            return Some(IntegerArithmeticCertificate {
                conclusion: combined_index,
                nodes,
            });
        }
        return Some(IntegerArithmeticCertificate {
            conclusion: nodes.len() - 1,
            nodes,
        });
    }
    if combined != *expected {
        return None;
    }
    nodes.push(IntegerArithmeticNode::Add {
        left: left_scaled,
        right: right_scaled,
        result: expected.clone(),
    });
    Some(IntegerArithmeticCertificate {
        conclusion: nodes.len() - 1,
        nodes,
    })
}

fn append_scale_node(
    nodes: &mut Vec<IntegerArithmeticNode>,
    source: usize,
    source_claim: IntegerAffineClaim,
    coefficient: BigInt,
) -> Option<usize> {
    if coefficient == BigInt::one() {
        return Some(source);
    }
    let result = scale_claim(&source_claim, &coefficient)?;
    let index = nodes.len();
    nodes.push(IntegerArithmeticNode::Scale {
        source,
        coefficient,
        result,
    });
    Some(index)
}

fn order_directions(source: &IntegerAffineClaim) -> Vec<(bool, IntegerAffineClaim)> {
    match source.relation {
        IntegerAffineRelation::LessEqual => vec![(false, source.clone())],
        IntegerAffineRelation::Equal => vec![
            (false, equality_direction(source, false)),
            (true, equality_direction(source, true)),
        ],
    }
}

fn equality_direction(source: &IntegerAffineClaim, reverse: bool) -> IntegerAffineClaim {
    if reverse {
        negate_claim(source, IntegerAffineRelation::LessEqual)
    } else {
        IntegerAffineClaim {
            relation: IntegerAffineRelation::LessEqual,
            terms: source.terms.clone(),
            constant: source.constant.clone(),
        }
    }
}

/// Solve `left_coefficient * left + right_coefficient * right == target`
/// over the affine coordinates. For inequalities, the constant is deliberately
/// solved exactly first; a separate weakening node handles a smaller target
/// constant after the terms are fixed.
fn solve_coefficients(
    left: &IntegerAffineClaim,
    right: &IntegerAffineClaim,
    target: &IntegerAffineClaim,
    inequality: bool,
) -> Option<(BigInt, BigInt)> {
    let atoms = affine_atoms(left, right, target);
    charge_planner_work(atoms.len().saturating_add(1))?;
    let mut coordinates = atoms
        .iter()
        .map(|atom| {
            (
                left.terms.get(atom).cloned().unwrap_or_else(BigInt::zero),
                right.terms.get(atom).cloned().unwrap_or_else(BigInt::zero),
                target.terms.get(atom).cloned().unwrap_or_else(BigInt::zero),
            )
        })
        .collect::<Vec<_>>();
    // The constant coordinate is useful when two term vectors are collinear
    // but have distinct offsets. It is ignored for the final target constant
    // check in the inequality case, where weakening is explicit.
    coordinates.push((
        left.constant.clone(),
        right.constant.clone(),
        target.constant.clone(),
    ));
    let (pivot_index, (a1, b1, t1)) = coordinates
        .iter()
        .enumerate()
        .find(|(_, (left, right, _))| !left.is_zero() || !right.is_zero())?;
    // Once a nonzero row is selected, one independent row determines the two
    // coefficients uniquely.  Scanning later rows is linear in the explicit
    // affine coordinate set; trying every coordinate pair would make nested
    // fold bodies quadratic for no additional proof power.
    for (right_index, (a2, b2, t2)) in coordinates.iter().enumerate() {
        if right_index == pivot_index {
            continue;
        }
        let numeric_work = (a1.bits().saturating_add(1))
            .saturating_mul(b2.bits().saturating_add(1))
            .saturating_add(
                (a2.bits().saturating_add(1)).saturating_mul(b1.bits().saturating_add(1)),
            )
            .saturating_add(
                (t1.bits().saturating_add(1)).saturating_mul(b2.bits().saturating_add(1)),
            )
            .saturating_add(
                (t2.bits().saturating_add(1)).saturating_mul(b1.bits().saturating_add(1)),
            )
            .saturating_add(1);
        charge_planner_work(usize::try_from(numeric_work).unwrap_or(usize::MAX))?;
        let determinant = a1 * b2 - a2 * b1;
        if determinant.is_zero() {
            continue;
        }
        let numerator_left = t1 * b2 - t2 * b1;
        let numerator_right = a1 * t2 - a2 * t1;
        if !is_divisible(&numerator_left, &determinant)
            || !is_divisible(&numerator_right, &determinant)
        {
            return None;
        }
        let candidate = (
            &numerator_left / &determinant,
            &numerator_right / &determinant,
        );
        if coefficients_match(left, right, target, &candidate.0, &candidate.1, inequality)? {
            return Some(candidate);
        }
        // The first independent row fixes both coefficients uniquely.  If
        // the candidate does not reproduce every affine coordinate, no later
        // row can yield a different valid combination; stop instead of
        // rescanning all atoms for every coordinate pair.
        return None;
    }
    None
}

fn coefficients_match(
    left: &IntegerAffineClaim,
    right: &IntegerAffineClaim,
    target: &IntegerAffineClaim,
    left_coefficient: &BigInt,
    right_coefficient: &BigInt,
    inequality: bool,
) -> Option<bool> {
    let atoms = affine_atoms(left, right, target);
    charge_planner_work(atoms.len().saturating_add(1))?;
    for atom in atoms {
        let left_value = left.terms.get(&atom).cloned().unwrap_or_else(BigInt::zero);
        let right_value = right.terms.get(&atom).cloned().unwrap_or_else(BigInt::zero);
        let numeric_work = (left_value.bits().saturating_add(1))
            .saturating_mul(left_coefficient.bits().saturating_add(1))
            .saturating_add(
                (right_value.bits().saturating_add(1))
                    .saturating_mul(right_coefficient.bits().saturating_add(1)),
            )
            .saturating_add(1);
        charge_planner_work(usize::try_from(numeric_work).unwrap_or(usize::MAX))?;
        let actual = left_value * left_coefficient + right_value * right_coefficient;
        if actual
            != target
                .terms
                .get(&atom)
                .cloned()
                .unwrap_or_else(BigInt::zero)
        {
            return Some(false);
        }
    }
    if !inequality {
        Some(
            left.constant.clone() * left_coefficient + right.constant.clone() * right_coefficient
                == target.constant,
        )
    } else {
        let actual =
            left.constant.clone() * left_coefficient + right.constant.clone() * right_coefficient;
        Some(actual >= target.constant)
    }
}

fn affine_atoms(
    left: &IntegerAffineClaim,
    right: &IntegerAffineClaim,
    target: &IntegerAffineClaim,
) -> BTreeSet<IntegerAffineAtom> {
    left.terms
        .keys()
        .chain(right.terms.keys())
        .chain(target.terms.keys())
        .cloned()
        .collect()
}

fn scale_factor(source: &IntegerAffineClaim, target: &IntegerAffineClaim) -> Option<BigInt> {
    if source.relation != target.relation {
        return None;
    }
    let mut coefficient = None;
    for atom in source.terms.keys().chain(target.terms.keys()) {
        charge_planner_work(1)?;
        let source_value = source.terms.get(atom).cloned().unwrap_or_else(BigInt::zero);
        let target_value = target.terms.get(atom).cloned().unwrap_or_else(BigInt::zero);
        if source_value.is_zero() {
            if !target_value.is_zero() {
                return None;
            }
            continue;
        }
        charge_planner_work(
            usize::try_from(
                source_value
                    .bits()
                    .saturating_add(target_value.bits())
                    .saturating_add(1),
            )
            .unwrap_or(usize::MAX),
        )?;
        if coefficient.is_none() {
            if !is_divisible(&target_value, &source_value) {
                return None;
            }
            coefficient = Some(&target_value / &source_value);
        }
    }
    let coefficient = coefficient.unwrap_or_else(|| {
        if source.constant.is_zero() {
            BigInt::zero()
        } else if is_divisible(&target.constant, &source.constant) {
            &target.constant / &source.constant
        } else {
            BigInt::from(-1)
        }
    });
    for (atom, value) in &source.terms {
        let target_value = target.terms.get(atom).cloned().unwrap_or_else(BigInt::zero);
        let numeric_work = (value.bits().saturating_add(1))
            .saturating_mul(coefficient.bits().saturating_add(1))
            .saturating_add(target_value.bits().saturating_add(1));
        charge_planner_work(usize::try_from(numeric_work).unwrap_or(usize::MAX))?;
        if target_value != value * &coefficient {
            return None;
        }
    }
    let constant_work = (source.constant.bits().saturating_add(1))
        .saturating_mul(coefficient.bits().saturating_add(1))
        .saturating_add(target.constant.bits().saturating_add(1));
    charge_planner_work(usize::try_from(constant_work).unwrap_or(usize::MAX))?;
    if source.constant.clone() * &coefficient != target.constant {
        return None;
    }
    Some(coefficient)
}

fn scale_claim(source: &IntegerAffineClaim, coefficient: &BigInt) -> Option<IntegerAffineClaim> {
    charge_planner_work(source.terms.len().saturating_add(1))?;
    let mut terms = BTreeMap::new();
    for (atom, value) in &source.terms {
        let numeric_work = (value.bits().saturating_add(1))
            .saturating_mul(coefficient.bits().saturating_add(1))
            .saturating_add(1);
        charge_planner_work(usize::try_from(numeric_work).unwrap_or(usize::MAX))?;
        let value = value * coefficient;
        if !value.is_zero() {
            terms.insert(atom.clone(), value);
        }
    }
    charge_planner_work(
        usize::try_from(
            (source.constant.bits().saturating_add(1))
                .saturating_mul(coefficient.bits().saturating_add(1))
                .saturating_add(1),
        )
        .unwrap_or(usize::MAX),
    )?;
    Some(IntegerAffineClaim {
        relation: source.relation.clone(),
        terms,
        constant: &source.constant * coefficient,
    })
}

fn add_claim(left: &IntegerAffineClaim, right: &IntegerAffineClaim) -> Option<IntegerAffineClaim> {
    charge_planner_work(
        left.terms
            .len()
            .saturating_add(right.terms.len())
            .saturating_add(1),
    )?;
    let mut terms = left.terms.clone();
    for (atom, coefficient) in &right.terms {
        let existing = terms.get(atom).cloned().unwrap_or_else(BigInt::zero);
        charge_planner_work(
            usize::try_from(
                existing
                    .bits()
                    .saturating_add(coefficient.bits())
                    .saturating_add(2),
            )
            .unwrap_or(usize::MAX),
        )?;
        let value = existing + coefficient;
        if value.is_zero() {
            terms.remove(atom);
        } else {
            terms.insert(atom.clone(), value);
        }
    }
    charge_planner_work(
        usize::try_from(
            left.constant
                .bits()
                .saturating_add(right.constant.bits())
                .saturating_add(2),
        )
        .unwrap_or(usize::MAX),
    )?;
    Some(IntegerAffineClaim {
        relation: left.relation.clone(),
        terms,
        constant: &left.constant + &right.constant,
    })
}

fn negate_claim(
    source: &IntegerAffineClaim,
    relation: IntegerAffineRelation,
) -> IntegerAffineClaim {
    IntegerAffineClaim {
        relation,
        terms: source
            .terms
            .iter()
            .map(|(atom, coefficient)| (atom.clone(), -coefficient))
            .filter(|(_, coefficient)| !coefficient.is_zero())
            .collect(),
        constant: -&source.constant,
    }
}

fn is_divisible(numerator: &BigInt, denominator: &BigInt) -> bool {
    !denominator.is_zero() && numerator % denominator == BigInt::zero()
}

fn charge_planner_work(units: usize) -> Option<()> {
    (!crate::instrumentation::deadline_exceeded_with_work(units)).then_some(())
}

fn claim_is_integer_trivial(claim: &IntegerAffineClaim) -> bool {
    claim.terms.is_empty()
        && match claim.relation {
            IntegerAffineRelation::LessEqual => claim.constant <= BigInt::zero(),
            IntegerAffineRelation::Equal => claim.constant.is_zero(),
        }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{ConditionTerm, IntegerTerm, Variable};

    fn proposition(condition: ConditionTerm) -> Proposition {
        Proposition::ConditionIs(condition, true)
    }

    fn less_equal(left: IntegerTerm, right: IntegerTerm) -> Proposition {
        proposition(ConditionTerm::IntegerLessEqual(left.into(), right.into()))
    }

    #[test]
    fn planner_matches_normalized_equality_and_order_direction() {
        let x = IntegerTerm::var(Variable(81));
        let y = IntegerTerm::var(Variable(82));
        let equality = proposition(ConditionTerm::IntegerEqual(
            x.clone().into(),
            y.clone().into(),
        ));
        let goal = less_equal(x, y);
        let certificate = plan_integer_affine_certificate(&goal, std::slice::from_ref(&equality))
            .expect("an equality should supply one checked order direction");
        certificate
            .check(&goal, &[equality])
            .expect("the equality-direction certificate should verify");
    }

    #[test]
    fn planner_scales_one_order_premise() {
        let x = IntegerTerm::var(Variable(83));
        let y = IntegerTerm::var(Variable(84));
        let premise = less_equal(x.clone(), y.clone());
        let goal = less_equal(
            IntegerTerm::multiply(IntegerTerm::constant_i64(2), x),
            IntegerTerm::multiply(IntegerTerm::constant_i64(2), y),
        );
        let certificate = plan_integer_affine_certificate(&goal, std::slice::from_ref(&premise))
            .expect("a nonnegative scale should be planned");
        certificate
            .check(&goal, &[premise])
            .expect("the scaled certificate should verify");
    }

    #[test]
    fn planner_rejects_negative_scaling_of_an_order_premise() {
        let x = IntegerTerm::var(Variable(841));
        let y = IntegerTerm::var(Variable(842));
        let premise = less_equal(x.clone(), y.clone());
        let goal = less_equal(
            IntegerTerm::multiply(IntegerTerm::constant_i64(-2), x),
            IntegerTerm::multiply(IntegerTerm::constant_i64(-2), y),
        );
        assert!(
            plan_integer_affine_certificate(&goal, &[premise]).is_none(),
            "a negative scale cannot preserve an order premise"
        );
    }

    #[test]
    fn planner_applies_one_premise_order_constant_weakening() {
        let x = IntegerTerm::var(Variable(843));
        let source = less_equal(
            IntegerTerm::add(x.clone(), IntegerTerm::constant_i64(4)),
            IntegerTerm::constant_i64(0),
        );
        let goal = less_equal(
            IntegerTerm::add(x, IntegerTerm::constant_i64(1)),
            IntegerTerm::constant_i64(0),
        );
        let certificate = plan_integer_affine_certificate(&goal, std::slice::from_ref(&source))
            .expect("a stronger order premise should admit constant weakening");
        certificate
            .check(&goal, &[source])
            .expect("the weakened order certificate should verify");
    }

    #[test]
    fn planner_adds_two_premises_and_weakens_a_constant() {
        let x = IntegerTerm::var(Variable(85));
        let y = IntegerTerm::var(Variable(86));
        let a = IntegerTerm::var(Variable(87));
        let b = IntegerTerm::var(Variable(88));
        let first = less_equal(x.clone(), y.clone());
        let second = less_equal(a.clone(), b.clone());
        let goal = less_equal(
            IntegerTerm::add(x, a),
            IntegerTerm::add(IntegerTerm::add(y, b), IntegerTerm::constant_i64(1)),
        );
        let premises = [first, second];
        let certificate = plan_integer_affine_certificate(&goal, &premises)
            .expect("two selected bounds should support a constant weakening");
        certificate
            .check(&goal, &premises)
            .expect("the two-premise certificate should verify");
    }

    #[test]
    fn planner_combines_an_equality_direction_with_an_order_premise() {
        let total = IntegerTerm::var(Variable(89));
        let prefix = IntegerTerm::var(Variable(90));
        let index = IntegerTerm::var(Variable(91));
        let equality = proposition(ConditionTerm::IntegerEqual(
            total.clone().into(),
            prefix.clone().into(),
        ));
        let lower = less_equal(
            IntegerTerm::multiply(IntegerTerm::constant_i64(-1000), index),
            prefix,
        );
        let goal = less_equal(
            IntegerTerm::multiply(
                IntegerTerm::constant_i64(-1000),
                IntegerTerm::var(Variable(91)),
            ),
            total,
        );
        let premises = [equality, lower];
        let certificate = plan_integer_affine_certificate(&goal, &premises)
            .expect("the reverse equality direction should cancel the prefix atom");
        certificate
            .check(&goal, &premises)
            .expect("the equality-plus-order certificate should verify");
    }

    #[test]
    fn planner_stops_when_the_selected_slice_exhausts_its_budget() {
        use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};

        let x = IntegerTerm::var(Variable(92));
        let y = IntegerTerm::var(Variable(93));
        let goal = less_equal(
            IntegerTerm::multiply(IntegerTerm::constant_i64(2), x.clone()),
            IntegerTerm::multiply(IntegerTerm::constant_i64(2), y.clone()),
        );
        let premise = less_equal(x, y);
        let unrelated = (0..16)
            .map(|offset| {
                less_equal(
                    IntegerTerm::var(Variable(1_000 + offset)),
                    IntegerTerm::var(Variable(2_000 + offset)),
                )
            })
            .collect::<Vec<_>>();
        let mut premises = unrelated;
        premises.push(premise);
        instrumentation::with_tactic_work_limits(
            TacticWorkLimits {
                simple: 8,
                smart: 8,
                control: 8,
            },
            || {
                let tactic = TacticEvent {
                    claim: "bounded integer affine planner".into(),
                    tactic_index: 0,
                    tactic_name: "integer_affine_planner".into(),
                    class: "simple".into(),
                    statement_index: 0,
                    source_index: 0,
                };
                instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                assert!(plan_integer_affine_certificate(&goal, &premises).is_none());
                instrumentation::emit(VerificationEvent::TacticFailed(tactic));
            },
        );
    }

    #[test]
    fn planner_charges_affine_map_construction_before_scaling() {
        use crate::instrumentation::{self, TacticEvent, TacticWorkLimits, VerificationEvent};

        let terms = (0..8)
            .map(|index| {
                (
                    IntegerAffineAtom::Variable(Variable(4_000 + index)),
                    BigInt::one(),
                )
            })
            .collect();
        let claim = IntegerAffineClaim {
            relation: IntegerAffineRelation::LessEqual,
            terms,
            constant: BigInt::zero(),
        };
        let tactic = TacticEvent {
            claim: "affine map construction budget".into(),
            tactic_index: 0,
            tactic_name: "integer_affine_planner".into(),
            class: "smart".into(),
            statement_index: 0,
            source_index: 0,
        };
        instrumentation::with_tactic_work_limits(
            TacticWorkLimits {
                simple: 1_000,
                smart: 32,
                control: 1_000,
            },
            || {
                instrumentation::emit(VerificationEvent::TacticStarted(tactic.clone()));
                assert!(scale_claim(&claim, &BigInt::from(3)).is_none());
                instrumentation::emit(VerificationEvent::TacticFailed(tactic));
            },
        );
    }
}
