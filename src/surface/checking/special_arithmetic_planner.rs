//! Bounded selection of typed certificates for pointer and finite-float facts.
//! The kernel checker, not this selector, is authoritative.

use super::*;
use crate::kernel::proof::arithmetic_special::{
    SpecialArithmeticCertificate as KernelCertificate, SpecialArithmeticNode as KernelNode,
};
use crate::kernel::{CFloatClassification, CFloatCondition, ConditionTerm, Proposition};
use crate::surface::{ArithmeticCertificate, SpecialArithmeticCertificate, SpecialArithmeticNode};

pub(in crate::surface) fn plan_special_arithmetic_certificate(
    goal: &Proposition,
    premises: &[Proposition],
) -> Option<KernelCertificate> {
    if !charge_proposition(goal) {
        return None;
    }
    if let Some(finite) = float_finite_premise(goal, premises) {
        return Some(KernelCertificate {
            nodes: vec![KernelNode::FloatReflexive {
                finite,
                result: goal.clone(),
            }],
            conclusion: 0,
        });
    }
    if is_alignment_goal(goal) {
        return Some(KernelCertificate {
            nodes: vec![KernelNode::PointerAlignment {
                premise: premises
                    .iter()
                    .position(|p| charge_proposition(p) && is_positive_alignment(p)),
                result: goal.clone(),
            }],
            conclusion: 0,
        });
    }
    if is_pointer_relation(goal)
        && let Some(relation) = premises
            .iter()
            .position(|p| charge_proposition(p) && is_pointer_relation(p))
    {
        let bounds = premises
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                (i != relation && charge_proposition(p) && is_signed_scalar_bound(p)).then_some(i)
            })
            .collect();
        return Some(KernelCertificate {
            nodes: vec![KernelNode::PointerTranslation {
                relation,
                bounds,
                result: goal.clone(),
            }],
            conclusion: 0,
        });
    }
    if is_bitvector64_equality(goal)
        && let Some(relation) = premises
            .iter()
            .position(|p| charge_proposition(p) && is_word_equality(p))
    {
        let alignments: Vec<usize> = premises
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                (i != relation
                    && charge_proposition(p)
                    && is_positive_alignment(p)
                    && alignment_is_relevant(p, &premises[relation], goal))
                .then_some(i)
            })
            .collect();
        if !alignments.is_empty() {
            return Some(KernelCertificate {
                nodes: vec![KernelNode::PointerWordEquality {
                    relation,
                    alignments,
                    result: goal.clone(),
                }],
                conclusion: 0,
            });
        }
    }
    if is_bitvector64_goal(goal) {
        let alignments = premises
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                (charge_proposition(p)
                    && is_positive_alignment(p)
                    && alignment_is_relevant(p, goal, goal))
                .then_some(i)
            })
            .collect::<Vec<_>>();
        if !alignments.is_empty() {
            return Some(KernelCertificate {
                nodes: vec![KernelNode::PointerWordFromAlignment {
                    alignments,
                    result: goal.clone(),
                }],
                conclusion: 0,
            });
        }
    }
    None
}

pub(in crate::surface) fn special_plan_to_surface_certificate(
    plan: &KernelCertificate,
    premises: &[ClickProposition],
    goal: &ClickProposition,
) -> ArithmeticCertificate {
    let nodes = plan
        .nodes
        .iter()
        .map(|node| match node {
            KernelNode::PointerTranslation {
                relation, bounds, ..
            } => SpecialArithmeticNode::PointerTranslation {
                relation: *relation,
                bounds: bounds.clone(),
                result: goal.clone(),
            },
            KernelNode::PointerAlignment { premise, .. } => {
                SpecialArithmeticNode::PointerAlignment {
                    premise: *premise,
                    result: goal.clone(),
                }
            }
            KernelNode::PointerWordEquality {
                relation,
                alignments,
                ..
            } => SpecialArithmeticNode::PointerWordEquality {
                relation: *relation,
                alignments: alignments.clone(),
                result: goal.clone(),
            },
            KernelNode::PointerWordFromAlignment { alignments, .. } => {
                SpecialArithmeticNode::PointerWordFromAlignment {
                    alignments: alignments.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::FloatReflexive { finite, .. } => SpecialArithmeticNode::FloatReflexive {
                finite: *finite,
                result: goal.clone(),
            },
        })
        .collect();
    ArithmeticCertificate::special(SpecialArithmeticCertificate {
        premises: premises.to_vec(),
        nodes,
        conclusion: plan.conclusion,
    })
}

fn is_positive_alignment(p: &Proposition) -> bool {
    matches!(p, Proposition::ConditionIs(condition, true) if alignment_shape(condition).is_some())
}

fn alignment_is_relevant(
    alignment: &Proposition,
    relation: &Proposition,
    goal: &Proposition,
) -> bool {
    let Proposition::ConditionIs(condition, true) = alignment else {
        return false;
    };
    let Some((pointer, _)) = alignment_shape(condition) else {
        return false;
    };
    proposition_mentions_pointer(relation, pointer) || proposition_mentions_pointer(goal, pointer)
}

fn proposition_mentions_pointer(
    proposition: &Proposition,
    target: &crate::kernel::Pointer,
) -> bool {
    let mut pending = vec![proposition];
    while let Some(current) = pending.pop() {
        match current {
            Proposition::ConditionIs(condition, _) => {
                let mut terms = Vec::new();
                match condition {
                    ConditionTerm::Bitvector32Equal(left, right)
                    | ConditionTerm::Bitvector64Equal(left, right)
                    | ConditionTerm::Bitvector32SignedLessThan(left, right)
                    | ConditionTerm::Bitvector32SignedLessEqual(left, right)
                    | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
                    | ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
                        terms.push(left.as_ref());
                        terms.push(right.as_ref());
                    }
                    _ => {}
                }
                for term in terms {
                    if term_mentions_pointer(term, target) {
                        return true;
                    }
                }
            }
            Proposition::And(left, right)
            | Proposition::Or(left, right)
            | Proposition::Implies(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Proposition::Not(body) => pending.push(body),
            _ => {}
        }
    }
    false
}

fn term_mentions_pointer(term: &Bitvector32Term, target: &crate::kernel::Pointer) -> bool {
    let mut pending = vec![term];
    while let Some(current) = pending.pop() {
        match current {
            Bitvector32Term::PointerAddress(pointer) => {
                if bounded_pointer_equal(pointer, target) {
                    return true;
                }
            }
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::UInt64Add(left, right)
            | Bitvector32Term::UInt64Subtract(left, right)
            | Bitvector32Term::UInt64Multiply(left, right)
            | Bitvector32Term::UInt64BitwiseAnd(left, right)
            | Bitvector32Term::UInt64BitwiseOr(left, right)
            | Bitvector32Term::Float32Binary { left, right, .. }
            | Bitvector32Term::Float64Binary { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            Bitvector32Term::PureFunctionApplication { arguments, .. } => {
                pending.extend(arguments.iter());
            }
            _ => {}
        }
    }
    false
}

fn bounded_pointer_equal(left: &crate::kernel::Pointer, right: &crate::kernel::Pointer) -> bool {
    if !bounded_pointer_work(left) || !bounded_pointer_work(right) || left.block != right.block {
        return false;
    }
    let mut pending = vec![(&left.offset, &right.offset)];
    while let Some((left, right)) = pending.pop() {
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match (left, right) {
            (
                crate::kernel::PointerOffsetTerm::Constant(a),
                crate::kernel::PointerOffsetTerm::Constant(b),
            ) => {
                if a != b {
                    return false;
                }
            }
            (
                crate::kernel::PointerOffsetTerm::Variable(a),
                crate::kernel::PointerOffsetTerm::Variable(b),
            ) => {
                if a != b {
                    return false;
                }
            }
            (
                crate::kernel::PointerOffsetTerm::Add(a, b),
                crate::kernel::PointerOffsetTerm::Add(c, d),
            ) => {
                pending.push((a, c));
                pending.push((b, d));
            }
            (
                crate::kernel::PointerOffsetTerm::Int32Scaled {
                    value: a,
                    byte_width: aw,
                },
                crate::kernel::PointerOffsetTerm::Int32Scaled {
                    value: b,
                    byte_width: bw,
                },
            ) => {
                if aw != bw || !bounded_term_equal(a, b) {
                    return false;
                }
            }
            (
                crate::kernel::PointerOffsetTerm::Int64Scaled {
                    value: a,
                    byte_width: aw,
                    ..
                },
                crate::kernel::PointerOffsetTerm::Int64Scaled {
                    value: b,
                    byte_width: bw,
                    ..
                },
            ) => {
                if aw != bw || !bounded_term_equal(a, b) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}
fn is_alignment_goal(p: &Proposition) -> bool {
    matches!(p, Proposition::ConditionIs(condition, _) if alignment_shape(condition).is_some())
}
fn is_pointer_relation(p: &Proposition) -> bool {
    matches!(
        p,
        Proposition::ConditionIs(
            ConditionTerm::PointerEqual(_, _) | ConditionTerm::PointerOffsetEqual(_, _),
            true
        )
    )
}
fn is_signed_scalar_bound(p: &Proposition) -> bool {
    matches!(
        p,
        Proposition::ConditionIs(
            ConditionTerm::Bitvector32SignedLessThan(_, _)
                | ConditionTerm::Bitvector32SignedLessEqual(_, _)
                | ConditionTerm::Bitvector32SignedGreaterThan(_, _)
                | ConditionTerm::Bitvector32SignedGreaterEqual(_, _),
            true
        )
    )
}
fn is_bitvector64_equality(p: &Proposition) -> bool {
    matches!(
        p,
        Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(_, _), true)
    )
}

fn is_bitvector64_goal(p: &Proposition) -> bool {
    matches!(
        p,
        Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(_, _), _)
    )
}

/// Alignment facts are also encoded as 64-bit equalities.  They are evidence
/// for the tagged-word rule, never the recorded word relation consumed by
/// `PointerWordEquality`.
fn is_word_equality(p: &Proposition) -> bool {
    let Proposition::ConditionIs(condition @ ConditionTerm::Bitvector64Equal(_, _), true) = p
    else {
        return false;
    };
    alignment_shape(condition).is_none()
}
fn float_finite_premise(goal: &Proposition, premises: &[Proposition]) -> Option<usize> {
    let Proposition::ConditionIs(condition, _) = goal else {
        return None;
    };
    let (width, expression) = match condition {
        ConditionTerm::Float32(CFloatCondition::Comparison { left, right, .. })
            if bounded_term_equal(left, right) =>
        {
            (32, left.as_ref())
        }
        ConditionTerm::Float64(CFloatCondition::Comparison { left, right, .. })
            if bounded_term_equal(left, right) =>
        {
            (64, left.as_ref())
        }
        _ => return None,
    };
    premises.iter().position(|p| {
        if !charge_proposition(p) {
            return false;
        }
        match (width, p) {
            (
                32,
                Proposition::ConditionIs(
                    ConditionTerm::Float32(CFloatCondition::Classification {
                        classification: CFloatClassification::Finite,
                        value,
                    }),
                    true,
                ),
            )
            | (
                64,
                Proposition::ConditionIs(
                    ConditionTerm::Float64(CFloatCondition::Classification {
                        classification: CFloatClassification::Finite,
                        value,
                    }),
                    true,
                ),
            ) => bounded_term_equal(value, expression),
            _ => false,
        }
    })
}

fn charge_proposition(proposition: &Proposition) -> bool {
    if crate::instrumentation::deadline_exceeded_with_work(1) {
        return false;
    }
    let Proposition::ConditionIs(condition, _) = proposition else {
        return true;
    };
    match condition {
        ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector64Equal(left, right)
        | ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right) => {
            bounded_term_work(left) && bounded_term_work(right)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            bounded_offset_work(left) && bounded_offset_work(right)
        }
        ConditionTerm::PointerEqual(left, right) => {
            bounded_pointer_work(left) && bounded_pointer_work(right)
        }
        ConditionTerm::Float32(float) | ConditionTerm::Float64(float) => match float {
            CFloatCondition::Comparison { left, right, .. } => {
                bounded_term_work(left) && bounded_term_work(right)
            }
            CFloatCondition::Classification { value, .. } => bounded_term_work(value),
        },
        _ => true,
    }
}

fn bounded_offset_work(root: &crate::kernel::PointerOffsetTerm) -> bool {
    let mut pending = vec![root];
    let mut count = 0usize;
    while let Some(offset) = pending.pop() {
        count = count.saturating_add(1);
        if count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match offset {
            crate::kernel::PointerOffsetTerm::Add(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            crate::kernel::PointerOffsetTerm::Int32Scaled { value, .. }
            | crate::kernel::PointerOffsetTerm::Int64Scaled { value, .. }
                if !bounded_term_work(value) =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
}

fn bounded_term_work(root: &Bitvector32Term) -> bool {
    let mut pending = vec![root];
    let mut count = 0usize;
    while let Some(term) = pending.pop() {
        count = count.saturating_add(1);
        if count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match term {
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::Multiply(left, right)
            | Bitvector32Term::UInt64Add(left, right)
            | Bitvector32Term::UInt64Subtract(left, right)
            | Bitvector32Term::UInt64Multiply(left, right)
            | Bitvector32Term::UInt64BitwiseAnd(left, right)
            | Bitvector32Term::UInt64BitwiseOr(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Bitvector32Term::PointerAddress(pointer) if !bounded_offset_work(&pointer.offset) => {
                return false;
            }
            Bitvector32Term::PointerAddress(pointer)
                if !bounded_pointer_block_work(&pointer.block) =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
}

fn bounded_pointer_work(pointer: &crate::kernel::Pointer) -> bool {
    bounded_pointer_block_work(&pointer.block) && bounded_offset_work(&pointer.offset)
}

fn bounded_pointer_block_work(block: &crate::kernel::PointerBlock) -> bool {
    let size = match block {
        crate::kernel::PointerBlock::Concrete(name)
        | crate::kernel::PointerBlock::Function(name) => name.len(),
        crate::kernel::PointerBlock::StringLiteral { identity, bytes } => {
            identity.len().saturating_add(bytes.len())
        }
        _ => 1,
    };
    size <= 256 && !crate::instrumentation::deadline_exceeded_with_work(size.max(1))
}

fn bounded_term_equal(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    let mut pending = vec![(left, right)];
    let mut count = 0usize;
    while let Some((left, right)) = pending.pop() {
        count = count.saturating_add(1);
        if count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match (left, right) {
            (Bitvector32Term::Constant(a), Bitvector32Term::Constant(b)) if a == b => {}
            (Bitvector32Term::Int64Constant(a), Bitvector32Term::Int64Constant(b)) if a == b => {}
            (Bitvector32Term::UInt64Constant(a), Bitvector32Term::UInt64Constant(b)) if a == b => {}
            (Bitvector32Term::Variable(a), Bitvector32Term::Variable(b)) if a == b => {}
            (Bitvector32Term::PointerAddress(_), Bitvector32Term::PointerAddress(_)) => {
                return false;
            }
            (Bitvector32Term::Add(a, b), Bitvector32Term::Add(c, d))
            | (Bitvector32Term::Subtract(a, b), Bitvector32Term::Subtract(c, d))
            | (Bitvector32Term::Multiply(a, b), Bitvector32Term::Multiply(c, d))
            | (Bitvector32Term::UInt64Add(a, b), Bitvector32Term::UInt64Add(c, d))
            | (Bitvector32Term::UInt64Subtract(a, b), Bitvector32Term::UInt64Subtract(c, d))
            | (Bitvector32Term::UInt64Multiply(a, b), Bitvector32Term::UInt64Multiply(c, d))
            | (Bitvector32Term::UInt64BitwiseAnd(a, b), Bitvector32Term::UInt64BitwiseAnd(c, d))
            | (Bitvector32Term::UInt64BitwiseOr(a, b), Bitvector32Term::UInt64BitwiseOr(c, d)) => {
                pending.push((a, c));
                pending.push((b, d));
            }
            (
                Bitvector32Term::Float32Binary {
                    operator: left_operator,
                    left: a,
                    right: b,
                },
                Bitvector32Term::Float32Binary {
                    operator: right_operator,
                    left: c,
                    right: d,
                },
            )
            | (
                Bitvector32Term::Float64Binary {
                    operator: left_operator,
                    left: a,
                    right: b,
                },
                Bitvector32Term::Float64Binary {
                    operator: right_operator,
                    left: c,
                    right: d,
                },
            ) if left_operator == right_operator => {
                pending.push((a, c));
                pending.push((b, d));
            }
            (
                Bitvector32Term::PureFunctionApplication {
                    name: left_name,
                    arguments: left_arguments,
                },
                Bitvector32Term::PureFunctionApplication {
                    name: right_name,
                    arguments: right_arguments,
                },
            ) if left_name == right_name && left_arguments.len() == right_arguments.len() => {
                pending.extend(left_arguments.iter().zip(right_arguments.iter()));
            }
            _ => return false,
        }
    }
    true
}

fn bounded_u64_constant(term: &Bitvector32Term) -> Option<u64> {
    match term {
        Bitvector32Term::UInt64Constant(value) => Some(*value),
        Bitvector32Term::Constant(value) => Some(u64::from(*value)),
        Bitvector32Term::Int64Constant(value) if *value >= 0 => Some(*value as u64),
        _ => None,
    }
}

fn alignment_shape(condition: &ConditionTerm) -> Option<(&crate::kernel::Pointer, u64)> {
    let ConditionTerm::Bitvector64Equal(left, right) = condition else {
        return None;
    };
    let masked = if bounded_u64_constant(right) == Some(0) {
        left.as_ref()
    } else if bounded_u64_constant(left) == Some(0) {
        right.as_ref()
    } else {
        return None;
    };
    let Bitvector32Term::UInt64BitwiseAnd(left, right) = masked else {
        return None;
    };
    let (pointer, mask) = match (left.as_ref(), right.as_ref()) {
        (Bitvector32Term::PointerAddress(pointer), mask)
        | (mask, Bitvector32Term::PointerAddress(pointer)) => {
            (pointer, bounded_u64_constant(mask)?)
        }
        _ => return None,
    };
    let alignment = mask.checked_add(1)?;
    alignment
        .is_power_of_two()
        .then_some((pointer.as_ref(), alignment))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{Bitvector32Term, CComparisonOperator, Variable};

    #[test]
    fn deep_float_candidate_is_rejected_before_recursive_helpers() {
        let mut term = Bitvector32Term::Variable(Variable(1));
        for _ in 0..300 {
            term = Bitvector32Term::Add(Box::new(term), Box::new(Bitvector32Term::Constant(1)));
        }
        let goal = Proposition::ConditionIs(
            ConditionTerm::Float32(CFloatCondition::Comparison {
                operator: CComparisonOperator::Equal,
                left: Box::new(term.clone()),
                right: Box::new(term.clone()),
            }),
            true,
        );
        let finite = Proposition::ConditionIs(
            ConditionTerm::Float32(CFloatCondition::Classification {
                classification: CFloatClassification::Finite,
                value: Box::new(term),
            }),
            true,
        );
        assert!(plan_special_arithmetic_certificate(&goal, &[finite]).is_none());
    }

    #[test]
    fn finite_candidate_scan_charges_unrelated_premises() {
        let value = Bitvector32Term::Variable(Variable(2));
        let goal = Proposition::ConditionIs(
            ConditionTerm::Float32(CFloatCondition::Comparison {
                operator: CComparisonOperator::Equal,
                left: Box::new(value.clone()),
                right: Box::new(value.clone()),
            }),
            true,
        );
        let mut premises = (0..64)
            .map(|i| {
                Proposition::ConditionIs(
                    ConditionTerm::Bitvector32Equal(
                        Box::new(Bitvector32Term::Variable(Variable(100 + i))),
                        Box::new(Bitvector32Term::Constant(i as u32)),
                    ),
                    true,
                )
            })
            .collect::<Vec<_>>();
        premises.push(Proposition::ConditionIs(
            ConditionTerm::Float32(CFloatCondition::Classification {
                classification: CFloatClassification::Finite,
                value: Box::new(value),
            }),
            true,
        ));
        let plan = plan_special_arithmetic_certificate(&goal, &premises).expect("finite plan");
        assert!(matches!(
            plan.nodes[0],
            KernelNode::FloatReflexive { finite: 64, .. }
        ));
    }
}
