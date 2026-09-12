//! Locally checkable certificates for the non-machine-integer arithmetic
//! fragments which are currently routed through `arithmetic`.
//!
//! This module intentionally has no planner and does not call the legacy
//! arithmetic decision procedure.  Every node names the exact premise
//! positions it consumes and carries the proposition it claims to establish.
//! The surface migration can construct these nodes later without changing the
//! kernel boundary.

#![allow(dead_code)]

use super::super::{
    Bitvector32Term, CComparisonOperator, CFloatClassification, CFloatCondition, ConditionTerm,
    Pointer, PointerBlock, PointerOffsetTerm, Proposition,
};
use std::collections::BTreeMap;

const SIGNED_MIN: i64 = i32::MIN as i64;
const SIGNED_MAX: i64 = i32::MAX as i64;

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SpecialArithmeticNode {
    /// Translate one exact pointer equality using explicitly listed scalar
    /// bounds.  The relation premise is one of `premises`; every bound index
    /// must name a scalar signed comparison in that same premise slice.
    PointerTranslation {
        relation: usize,
        bounds: Vec<usize>,
        result: Proposition,
    },
    /// Establish one alignment proposition from one exact alignment premise.
    /// `None` is reserved for intrinsic allocator/static alignment and is
    /// checked structurally, never by searching a context.
    PointerAlignment {
        premise: Option<usize>,
        result: Proposition,
    },
    /// Establish a tagged pointer-word equality from one exact recorded word
    /// equality and any exact alignment premises needed by tag operations.
    PointerWordEquality {
        relation: usize,
        alignments: Vec<usize>,
        result: Proposition,
    },
    /// Prove a reflexive IEEE comparison from one exact finite classification.
    FloatReflexive { finite: usize, result: Proposition },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SpecialArithmeticCertificate {
    pub(crate) nodes: Vec<SpecialArithmeticNode>,
    pub(crate) conclusion: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
#[allow(dead_code)]
pub(crate) enum SpecialArithmeticCheckError {
    InvalidPremise(usize),
    InvalidNodeReference(usize),
    InvalidRelation(usize),
    InvalidAlignment(usize),
    InvalidDefinedness(usize),
    InvalidOperator(usize),
    NodeResultMismatch(usize),
    DoesNotFollow,
}

impl SpecialArithmeticCertificate {
    pub(crate) fn check(
        &self,
        goal: &Proposition,
        premises: &[Proposition],
    ) -> Result<(), SpecialArithmeticCheckError> {
        if self.conclusion >= self.nodes.len() {
            return Err(SpecialArithmeticCheckError::InvalidNodeReference(
                self.conclusion,
            ));
        }
        let mut checked = Vec::with_capacity(self.nodes.len());
        for (index, node) in self.nodes.iter().enumerate() {
            let result = match node {
                SpecialArithmeticNode::PointerTranslation {
                    relation,
                    bounds,
                    result,
                } => {
                    let relation_proposition = premises
                        .get(*relation)
                        .ok_or(SpecialArithmeticCheckError::InvalidPremise(*relation))?;
                    let bound_propositions = bounds
                        .iter()
                        .map(|bound| {
                            premises
                                .get(*bound)
                                .ok_or(SpecialArithmeticCheckError::InvalidPremise(*bound))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    if !pointer_translation(relation_proposition, &bound_propositions, result) {
                        return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                    }
                    result.clone()
                }
                SpecialArithmeticNode::PointerAlignment { premise, result } => {
                    let premise = premise
                        .map(|index| {
                            premises
                                .get(index)
                                .ok_or(SpecialArithmeticCheckError::InvalidPremise(index))
                        })
                        .transpose()?;
                    if !pointer_alignment(premise, result) {
                        return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                    }
                    result.clone()
                }
                SpecialArithmeticNode::PointerWordEquality {
                    relation,
                    alignments,
                    result,
                } => {
                    let relation = premises
                        .get(*relation)
                        .ok_or(SpecialArithmeticCheckError::InvalidPremise(*relation))?;
                    let alignments = alignments
                        .iter()
                        .map(|index| {
                            premises
                                .get(*index)
                                .ok_or(SpecialArithmeticCheckError::InvalidPremise(*index))
                        })
                        .collect::<Result<Vec<_>, _>>()?;
                    if !pointer_word_equality(relation, &alignments, result) {
                        return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                    }
                    result.clone()
                }
                SpecialArithmeticNode::FloatReflexive { finite, result } => {
                    let finite = premises
                        .get(*finite)
                        .ok_or(SpecialArithmeticCheckError::InvalidPremise(*finite))?;
                    if !float_reflexive(finite, result) {
                        return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                    }
                    result.clone()
                }
            };
            checked.push(result);
        }
        if checked[self.conclusion] == *goal {
            Ok(())
        } else {
            Err(SpecialArithmeticCheckError::DoesNotFollow)
        }
    }
}

fn pointer_sides(
    proposition: &Proposition,
) -> Option<(
    &PointerOffsetTerm,
    &PointerOffsetTerm,
    Option<(&PointerBlock, &PointerBlock)>,
)> {
    match proposition {
        Proposition::ConditionIs(ConditionTerm::PointerEqual(left, right), true) => Some((
            &left.offset,
            &right.offset,
            Some((&left.block, &right.block)),
        )),
        Proposition::ConditionIs(ConditionTerm::PointerOffsetEqual(left, right), true) => {
            Some((left, right, None))
        }
        _ => None,
    }
}

fn scalar(value: &Bitvector32Term) -> Option<i64> {
    value.as_const().map(|value| i64::from(value as i32))
}

fn scalar_bounds(premises: &[&Proposition]) -> Option<BTreeMap<Bitvector32Term, (i64, i64)>> {
    let mut bounds = BTreeMap::new();
    for premise in premises {
        let Proposition::ConditionIs(condition, true) = premise else {
            return None;
        };
        let (left, right, strict) = match condition {
            ConditionTerm::Bitvector32SignedLessThan(left, right) => {
                (left.as_ref(), right.as_ref(), true)
            }
            ConditionTerm::Bitvector32SignedLessEqual(left, right) => {
                (left.as_ref(), right.as_ref(), false)
            }
            ConditionTerm::Bitvector32SignedGreaterThan(left, right) => {
                (right.as_ref(), left.as_ref(), true)
            }
            ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                (right.as_ref(), left.as_ref(), false)
            }
            _ => return None,
        };
        if !matches!(
            left,
            Bitvector32Term::Variable(_) | Bitvector32Term::Constant(_)
        ) || !matches!(
            right,
            Bitvector32Term::Variable(_) | Bitvector32Term::Constant(_)
        ) {
            return None;
        }
        let left_constant = scalar(left);
        let right_constant = scalar(right);
        match (left_constant, right_constant) {
            (None, Some(right)) => {
                let entry = bounds
                    .entry(left.clone())
                    .or_insert((SIGNED_MIN, SIGNED_MAX));
                entry.1 = entry.1.min(right - i64::from(strict));
            }
            (Some(left), None) => {
                let entry = bounds
                    .entry(right.clone())
                    .or_insert((SIGNED_MIN, SIGNED_MAX));
                entry.0 = entry.0.max(left + i64::from(strict));
            }
            (None, None) if strict => {
                let entry = bounds
                    .entry(left.clone())
                    .or_insert((SIGNED_MIN, SIGNED_MAX));
                entry.1 = entry.1.min(SIGNED_MAX - 1);
            }
            _ => {}
        }
    }
    Some(bounds)
}

enum OffsetPart<'a> {
    Offset(&'a PointerOffsetTerm),
    Scaled(&'a Bitvector32Term, i64),
}

fn pointer_translation(
    relation: &Proposition,
    bound_propositions: &[&Proposition],
    goal: &Proposition,
) -> bool {
    let Some((goal_left, goal_right, goal_blocks)) = pointer_sides(goal) else {
        return false;
    };
    let Some((premise_left, premise_right, premise_blocks)) = pointer_sides(relation) else {
        return false;
    };
    let (left, right) = match (goal_blocks, premise_blocks) {
        (None, None) => (goal_left, goal_right),
        (Some((goal_l, goal_r)), Some((premise_l, premise_r)))
            if goal_l == premise_l && goal_r == premise_r =>
        {
            (goal_left, goal_right)
        }
        (Some((goal_l, goal_r)), Some((premise_l, premise_r)))
            if goal_l == premise_r && goal_r == premise_l =>
        {
            (goal_right, goal_left)
        }
        _ => return false,
    };
    let Some(bounds) = scalar_bounds(bound_propositions) else {
        return false;
    };
    let atom_range = |value: &Bitvector32Term| match value {
        Bitvector32Term::Constant(value) => {
            let value = i64::from(*value as i32);
            Some((value, value))
        }
        Bitvector32Term::Variable(_) => Some(
            bounds
                .get(value)
                .copied()
                .unwrap_or((SIGNED_MIN, SIGNED_MAX)),
        ),
        _ => None,
    };
    let sum_is_defined = |x: &Bitvector32Term, y: &Bitvector32Term| {
        let (Some((xmin, xmax)), Some((ymin, ymax))) = (atom_range(x), atom_range(y)) else {
            return false;
        };
        xmin + ymin >= SIGNED_MIN && xmax + ymax <= SIGNED_MAX
    };
    let mut terms = BTreeMap::<PointerOffsetTerm, i128>::new();
    let mut constant = 0i128;
    for (offset, sign) in [
        (left, 1i128),
        (premise_left, -1),
        (right, -1),
        (premise_right, 1),
    ] {
        let mut pending = vec![OffsetPart::Offset(offset)];
        while let Some(part) = pending.pop() {
            let atom = match part {
                OffsetPart::Offset(PointerOffsetTerm::Constant(value)) => {
                    let Some(next) = constant.checked_add(sign * i128::from(*value)) else {
                        return false;
                    };
                    constant = next;
                    continue;
                }
                OffsetPart::Offset(PointerOffsetTerm::Add(left, right)) => {
                    pending.push(OffsetPart::Offset(left));
                    pending.push(OffsetPart::Offset(right));
                    continue;
                }
                OffsetPart::Offset(PointerOffsetTerm::Int32Scaled { value, byte_width }) => {
                    pending.push(OffsetPart::Scaled(value, *byte_width));
                    continue;
                }
                OffsetPart::Scaled(Bitvector32Term::Constant(value), width) => {
                    let value = i128::from(*value as i32) * i128::from(width);
                    let Some(next) = constant.checked_add(sign * value) else {
                        return false;
                    };
                    constant = next;
                    continue;
                }
                OffsetPart::Scaled(Bitvector32Term::Add(left, right), width)
                    if sum_is_defined(left, right) =>
                {
                    pending.push(OffsetPart::Scaled(left, width));
                    pending.push(OffsetPart::Scaled(right, width));
                    continue;
                }
                OffsetPart::Scaled(value, width) => PointerOffsetTerm::Int32Scaled {
                    value: Box::new(value.clone()),
                    byte_width: width,
                },
                OffsetPart::Offset(value) => value.clone(),
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

fn offset_difference(goal: &PointerOffsetTerm, premise: &PointerOffsetTerm) -> Option<i128> {
    let mut terms = BTreeMap::<PointerOffsetTerm, i128>::new();
    let mut constant = 0i128;
    for (offset, sign) in [(goal, 1i128), (premise, -1)] {
        let mut pending = vec![offset];
        while let Some(offset) = pending.pop() {
            match offset {
                PointerOffsetTerm::Constant(value) => constant += sign * i128::from(*value),
                PointerOffsetTerm::Add(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                other => {
                    *terms.entry(other.clone()).or_default() += sign;
                }
            }
        }
    }
    terms.retain(|_, coefficient| *coefficient != 0);
    terms.is_empty().then_some(constant)
}

fn pointer_alignment(premise: Option<&Proposition>, result: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, true) = result else {
        return false;
    };
    let Some((goal_pointer, goal_alignment)) = condition.as_pointer_alignment() else {
        return false;
    };
    let premise_alignment = premise.and_then(|proposition| {
        let Proposition::ConditionIs(condition, true) = proposition else {
            return None;
        };
        condition.as_pointer_alignment()
    });
    if premise.is_some() && premise_alignment.is_none() {
        return false;
    }
    if !goal_alignment.is_power_of_two() {
        return false;
    }
    if let Some((base, alignment)) = premise_alignment {
        if base.block != goal_pointer.block
            || alignment % goal_alignment != 0
            || offset_difference(&goal_pointer.offset, &base.offset)
                .is_none_or(|delta| delta.rem_euclid(goal_alignment as i128) != 0)
        {
            return false;
        }
        return true;
    }
    matches!(goal_pointer.block, PointerBlock::Heap(_))
        && offset_difference(&goal_pointer.offset, &PointerOffsetTerm::Constant(0))
            .is_some_and(|delta| delta.rem_euclid(goal_alignment as i128) == 0)
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TaggedAddress {
    pointer: Pointer,
    tag: Bitvector32Term,
}

fn add_tag(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    if left.uint64_as_const() == Some(0) {
        right
    } else if right.uint64_as_const() == Some(0) {
        left
    } else {
        Bitvector32Term::uint64_add(left, right)
    }
}

fn tagged_form(
    term: &Bitvector32Term,
    relation: (&Bitvector32Term, &Bitvector32Term),
    alignments: &[(&Pointer, u64)],
) -> Option<TaggedAddress> {
    let direct = match term {
        Bitvector32Term::PointerAddress(pointer) => Some(TaggedAddress {
            pointer: pointer.as_ref().clone(),
            tag: Bitvector32Term::UInt64Constant(0),
        }),
        Bitvector32Term::UInt64Add(left, right) => tagged_form(left, relation, alignments)
            .map(|form| TaggedAddress {
                pointer: form.pointer,
                tag: add_tag(form.tag, right.as_ref().clone()),
            })
            .or_else(|| {
                tagged_form(right, relation, alignments).map(|form| TaggedAddress {
                    pointer: form.pointer,
                    tag: add_tag(left.as_ref().clone(), form.tag),
                })
            }),
        Bitvector32Term::UInt64Subtract(left, right) => tagged_form(left, relation, alignments)
            .map(|form| TaggedAddress {
                pointer: form.pointer,
                tag: Bitvector32Term::uint64_subtract(form.tag, right.as_ref().clone()),
            }),
        Bitvector32Term::UInt64BitwiseAnd(left, right) => {
            let (inner, mask) = match (left.uint64_as_const(), right.uint64_as_const()) {
                (None, Some(mask)) => (left.as_ref(), mask),
                (Some(mask), None) => (right.as_ref(), mask),
                _ => return None,
            };
            let alignment = (!mask).checked_add(1)?.max(1);
            if !alignment.is_power_of_two() {
                return None;
            }
            let form = tagged_form(inner, relation, alignments)?;
            if !alignments
                .iter()
                .any(|(pointer, candidate)| *pointer == &form.pointer && *candidate >= alignment)
            {
                return None;
            }
            Some(TaggedAddress {
                pointer: form.pointer,
                tag: Bitvector32Term::uint64_bitwise_and(
                    form.tag,
                    Bitvector32Term::UInt64Constant(mask),
                ),
            })
        }
        Bitvector32Term::UInt64BitwiseOr(left, right) => {
            let (inner, constant) = match (left.uint64_as_const(), right.uint64_as_const()) {
                (None, Some(constant)) => (left.as_ref(), constant),
                (Some(constant), None) => (right.as_ref(), constant),
                _ => return None,
            };
            let alignment = constant.checked_add(1)?.next_power_of_two();
            let form = tagged_form(inner, relation, alignments)?;
            if constant != 0
                && !alignments.iter().any(|(pointer, candidate)| {
                    *pointer == &form.pointer && *candidate >= alignment
                })
            {
                return None;
            }
            Some(TaggedAddress {
                pointer: form.pointer,
                tag: Bitvector32Term::uint64_bitwise_or(
                    form.tag,
                    Bitvector32Term::UInt64Constant(constant),
                ),
            })
        }
        _ => None,
    };
    if direct.is_some() {
        return direct;
    }
    if term == relation.0 {
        return tagged_form(relation.1, relation, alignments);
    }
    if term == relation.1 {
        return tagged_form(relation.0, relation, alignments);
    }
    None
}

fn pointer_word_equality(
    relation: &Proposition,
    alignment_premises: &[&Proposition],
    result: &Proposition,
) -> bool {
    let Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(left, right), true) = relation
    else {
        return false;
    };
    let Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(goal_left, goal_right), true) =
        result
    else {
        return false;
    };
    let mut alignments = Vec::new();
    for premise in alignment_premises {
        let Proposition::ConditionIs(condition, true) = premise else {
            return false;
        };
        let Some((pointer, alignment)) = condition.as_pointer_alignment() else {
            return false;
        };
        alignments.push((pointer, alignment));
    }
    if tagged_form(left, (left, right), &alignments).is_none()
        || tagged_form(right, (left, right), &alignments).is_none()
    {
        return false;
    }
    let goal_left_form = tagged_form(goal_left, (left, right), &alignments);
    let goal_right_form = tagged_form(goal_right, (left, right), &alignments);
    match (goal_left_form, goal_right_form) {
        (Some(goal_left), Some(goal_right)) => {
            goal_left.pointer == goal_right.pointer && goal_left.tag == goal_right.tag
        }
        _ => false,
    }
}

fn float_reflexive(finite: &Proposition, result: &Proposition) -> bool {
    let Proposition::ConditionIs(finite_condition, true) = finite else {
        return false;
    };
    let (finite_expression, finite_width) = match finite_condition {
        ConditionTerm::Float32(CFloatCondition::Classification {
            value: expression,
            classification: CFloatClassification::Finite,
        }) => (expression.as_ref(), 32),
        ConditionTerm::Float64(CFloatCondition::Classification {
            value: expression,
            classification: CFloatClassification::Finite,
        }) => (expression.as_ref(), 64),
        _ => return false,
    };
    let Proposition::ConditionIs(condition, expected) = result else {
        return false;
    };
    let (operator, left, right, width) = match condition {
        ConditionTerm::Float32(CFloatCondition::Comparison {
            operator,
            left,
            right,
        }) => (*operator, left.as_ref(), right.as_ref(), 32),
        ConditionTerm::Float64(CFloatCondition::Comparison {
            operator,
            left,
            right,
        }) => (*operator, left.as_ref(), right.as_ref(), 64),
        _ => return false,
    };
    if width != finite_width || left != right || left != finite_expression {
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

#[cfg(test)]
mod tests {
    use super::*;

    fn pointer(offset: PointerOffsetTerm) -> Pointer {
        Pointer {
            block: PointerBlock::ExternalArgument,
            offset,
        }
    }

    fn pointer_eq(left: PointerOffsetTerm, right: PointerOffsetTerm) -> Proposition {
        Proposition::ConditionIs(
            ConditionTerm::PointerEqual(Box::new(pointer(left)), Box::new(pointer(right))),
            true,
        )
    }

    fn add(left: PointerOffsetTerm, right: PointerOffsetTerm) -> PointerOffsetTerm {
        PointerOffsetTerm::Add(Box::new(left), Box::new(right))
    }

    fn scaled(value: Bitvector32Term) -> PointerOffsetTerm {
        PointerOffsetTerm::Int32Scaled {
            value: Box::new(value),
            byte_width: 4,
        }
    }

    #[test]
    fn translation_certificate_checks_named_relation_and_bounds() {
        let p = PointerOffsetTerm::Variable(crate::kernel::Variable(100));
        let arr = PointerOffsetTerm::Variable(crate::kernel::Variable(101));
        let i = Bitvector32Term::Variable(crate::kernel::Variable(1));
        let n = Bitvector32Term::Variable(crate::kernel::Variable(2));
        let relation = pointer_eq(p.clone(), add(arr.clone(), scaled(i.clone())));
        let bound = Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(Box::new(i.clone()), Box::new(n.clone())),
            true,
        );
        let goal = pointer_eq(
            add(p, PointerOffsetTerm::Constant(4)),
            add(
                arr,
                scaled(Bitvector32Term::Add(
                    Box::new(i),
                    Box::new(Bitvector32Term::Constant(1)),
                )),
            ),
        );
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerTranslation {
                relation: 0,
                bounds: vec![1],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        certificate
            .check(&goal, &[relation.clone(), bound.clone()])
            .unwrap();
        let tampered = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerTranslation {
                relation: 1,
                bounds: vec![0],
                result: goal,
            }],
            conclusion: 0,
        };
        assert!(matches!(
            tampered.check(
                &pointer_eq(
                    PointerOffsetTerm::Constant(0),
                    PointerOffsetTerm::Constant(0)
                ),
                &[relation, bound]
            ),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
                | Err(SpecialArithmeticCheckError::InvalidPremise(_))
        ));
    }

    #[test]
    fn alignment_certificate_is_exact_and_rejects_wrong_displacement() {
        let base = pointer(PointerOffsetTerm::Constant(0));
        let aligned_base =
            Proposition::ConditionIs(ConditionTerm::pointer_aligned(base.clone(), 16), true);
        let goal_pointer = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Constant(24),
        };
        let goal = Proposition::ConditionIs(ConditionTerm::pointer_aligned(goal_pointer, 8), true);
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerAlignment {
                premise: Some(0),
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        certificate
            .check(&goal, std::slice::from_ref(&aligned_base))
            .unwrap();
        let wrong = Proposition::ConditionIs(
            ConditionTerm::pointer_aligned(
                Pointer {
                    block: base.block,
                    offset: PointerOffsetTerm::Constant(25),
                },
                8,
            ),
            true,
        );
        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerAlignment {
                    premise: Some(0),
                    result: wrong,
                }],
                conclusion: 0,
            }
            .check(&goal, &[aligned_base]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));
    }

    #[test]
    fn tagged_word_certificate_requires_exact_alignment() {
        let next = pointer(PointerOffsetTerm::Constant(0));
        let address = Bitvector32Term::PointerAddress(Box::new(next.clone()));
        let relation = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                Bitvector32Term::Variable(crate::kernel::Variable(10)),
                Bitvector32Term::uint64_add(address.clone(), Bitvector32Term::UInt64Constant(1)),
            ),
            true,
        );
        let alignment = Proposition::ConditionIs(ConditionTerm::pointer_aligned(next, 8), true);
        let goal = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                Bitvector32Term::uint64_bitwise_or(
                    Bitvector32Term::Variable(crate::kernel::Variable(10)),
                    Bitvector32Term::UInt64Constant(2),
                ),
                Bitvector32Term::uint64_add(address, Bitvector32Term::UInt64Constant(3)),
            ),
            true,
        );
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                relation: 0,
                alignments: vec![1],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        certificate.check(&goal, &[relation, alignment]).unwrap();
    }

    #[test]
    fn finite_float_certificate_rejects_wrong_width_expression_and_operator() {
        let value = Bitvector32Term::Variable(crate::kernel::Variable(22));
        let finite = Proposition::ConditionIs(
            ConditionTerm::float32_classification(value.clone(), CFloatClassification::Finite),
            true,
        );
        let good = Proposition::ConditionIs(
            ConditionTerm::float32_compare(
                value.clone(),
                value.clone(),
                CComparisonOperator::Equal,
            ),
            true,
        );
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::FloatReflexive {
                finite: 0,
                result: good.clone(),
            }],
            conclusion: 0,
        }
        .check(&good, std::slice::from_ref(&finite))
        .unwrap();
        let bad = Proposition::ConditionIs(
            ConditionTerm::float32_compare(value.clone(), value, CComparisonOperator::LessThan),
            true,
        );
        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::FloatReflexive {
                    finite: 0,
                    result: bad,
                }],
                conclusion: 0,
            }
            .check(&good, &[finite]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));
    }
}
