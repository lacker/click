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
                premise: premises.iter().position(is_positive_alignment),
                result: goal.clone(),
            }],
            conclusion: 0,
        });
    }
    if is_pointer_relation(goal)
        && let Some(relation) = premises.iter().position(is_pointer_relation)
    {
        let bounds = premises
            .iter()
            .enumerate()
            .filter_map(|(i, p)| (i != relation && is_signed_scalar_bound(p)).then_some(i))
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
        && let Some(relation) = premises.iter().position(is_bitvector64_equality)
    {
        let alignments = premises
            .iter()
            .enumerate()
            .filter_map(|(i, p)| (i != relation && is_positive_alignment(p)).then_some(i))
            .collect();
        return Some(KernelCertificate {
            nodes: vec![KernelNode::PointerWordEquality {
                relation,
                alignments,
                result: goal.clone(),
            }],
            conclusion: 0,
        });
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
    matches!(p, Proposition::ConditionIs(condition, true) if condition.as_pointer_alignment().is_some())
}
fn is_alignment_goal(p: &Proposition) -> bool {
    matches!(p, Proposition::ConditionIs(condition, _) if condition.as_pointer_alignment().is_some())
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
fn float_finite_premise(goal: &Proposition, premises: &[Proposition]) -> Option<usize> {
    let Proposition::ConditionIs(condition, _) = goal else {
        return None;
    };
    let width = match condition {
        ConditionTerm::Float32(CFloatCondition::Comparison { left, right, .. })
            if left == right =>
        {
            32
        }
        ConditionTerm::Float64(CFloatCondition::Comparison { left, right, .. })
            if left == right =>
        {
            64
        }
        _ => return None,
    };
    premises.iter().position(|p| {
        matches!(
            (width, p),
            (
                32,
                Proposition::ConditionIs(
                    ConditionTerm::Float32(CFloatCondition::Classification {
                        classification: CFloatClassification::Finite,
                        ..
                    }),
                    true,
                ),
            ) | (
                64,
                Proposition::ConditionIs(
                    ConditionTerm::Float64(CFloatCondition::Classification {
                        classification: CFloatClassification::Finite,
                        ..
                    }),
                    true,
                ),
            )
        )
    })
}
