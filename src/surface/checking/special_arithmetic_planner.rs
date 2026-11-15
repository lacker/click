//! Bounded selection of typed certificates for pointer and finite-float facts.
//! The kernel checker, not this selector, is authoritative.

use super::*;
use crate::kernel::MachineBinaryOp;
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::cast_term;
use crate::kernel::proof::arithmetic_special::{
    SpecialArithmeticCertificate as KernelCertificate, SpecialArithmeticNode as KernelNode,
    signed_constant_bound_on_view, signed_definedness_query,
};
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{ConditionTerm, FloatClassification, FloatCondition, Proposition};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int64_constant, uint64_constant,
};
use crate::surface::{ArithmeticCertificate, SpecialArithmeticCertificate, SpecialArithmeticNode};

pub(super) fn plan_special_arithmetic_certificate(
    goal: &Proposition,
    premises: &[Proposition],
) -> Option<KernelCertificate> {
    if !charge_proposition(goal) {
        return None;
    }
    if let Proposition::ConditionIs(condition, value) = goal
        && crate::kernel::PureFactContext::new()
            .widened_unsigned_sum_bound_premises(condition)
            .is_some()
    {
        let context = premises
            .iter()
            .fold(crate::kernel::PureFactContext::new(), |context, premise| {
                context.assume_proposition(premise.clone())
            });
        if context.decide_widened_sum_bound(condition) == Some(*value) {
            return Some(KernelCertificate {
                nodes: vec![KernelNode::UnsignedSumBound {
                    bounds: (0..premises.len()).collect(),
                    result: goal.clone(),
                }],
                conclusion: 0,
            });
        }
    }
    // `defined(a + b)` or `defined(a - b)` over `int32` or `int64`: cite
    // exactly the listed premises that bound an operand by a constant of
    // the goal's width. The kernel recomputes the operand ranges and
    // refuses a result that can leave that width.
    if let Some((width, operands, _)) = signed_definedness_query(goal) {
        let bounds = premises
            .iter()
            .enumerate()
            .filter_map(|(i, p)| {
                (charge_proposition(p)
                    && (signed_constant_bound_on_view(width, p, operands[0].operand_view())
                        .is_some()
                        || signed_constant_bound_on_view(width, p, operands[1].operand_view())
                            .is_some()))
                .then_some(i)
            })
            .collect();
        return Some(KernelCertificate {
            nodes: vec![KernelNode::SignedDefined {
                width,
                bounds,
                result: goal.clone(),
            }],
            conclusion: 0,
        });
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
                (i != relation && charge_proposition(p) && is_pointer_translation_bound(p))
                    .then_some(i)
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
    if let Some(bounds) = cast_identity_bounds(goal, premises) {
        return Some(KernelCertificate {
            nodes: vec![KernelNode::IntegerCastIdentity {
                bounds,
                result: goal.clone(),
            }],
            conclusion: 0,
        });
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
            KernelNode::UnsignedSumBound { bounds, .. } => {
                SpecialArithmeticNode::UnsignedSumBound {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerCastIdentity { bounds, .. } => {
                SpecialArithmeticNode::IntegerCastIdentity {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerOperationIdentity { bounds, .. } => {
                SpecialArithmeticNode::IntegerOperationIdentity {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerProductBounds { bounds, .. } => {
                SpecialArithmeticNode::IntegerProductBounds {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerDivisionBounds { bounds, .. } => {
                SpecialArithmeticNode::IntegerDivisionBounds {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerMultiplyOrder { bounds, .. } => {
                SpecialArithmeticNode::IntegerMultiplyOrder {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerQuotientBound { bounds, .. } => {
                SpecialArithmeticNode::IntegerQuotientBound {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerBoundExclusion { bounds, .. } => {
                SpecialArithmeticNode::IntegerBoundExclusion {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerRelationTransport { bounds, .. } => {
                SpecialArithmeticNode::IntegerRelationTransport {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerPolynomialIdentity { bounds, .. } => {
                SpecialArithmeticNode::IntegerPolynomialIdentity {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::IntegerQuotientShift { bounds, .. } => {
                SpecialArithmeticNode::IntegerQuotientShift {
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
            KernelNode::SignedDefined { width, bounds, .. } => {
                SpecialArithmeticNode::SignedDefined {
                    width: *width,
                    bounds: bounds.clone(),
                    result: goal.clone(),
                }
            }
        })
        .collect();
    let (premises, nodes) = cited_premises_only(premises, nodes);
    ArithmeticCertificate::special(SpecialArithmeticCertificate {
        premises,
        nodes,
        conclusion: plan.conclusion,
    })
}

/// The premise indices a node cites, for renumbering.
fn cited_premise_indices(node: &mut SpecialArithmeticNode) -> Vec<&mut usize> {
    match node {
        SpecialArithmeticNode::IntegerProductBounds { bounds, .. }
        | SpecialArithmeticNode::IntegerDivisionBounds { bounds, .. }
        | SpecialArithmeticNode::IntegerMultiplyOrder { bounds, .. }
        | SpecialArithmeticNode::IntegerQuotientBound { bounds, .. }
        | SpecialArithmeticNode::IntegerBoundExclusion { bounds, .. }
        | SpecialArithmeticNode::IntegerRelationTransport { bounds, .. }
        | SpecialArithmeticNode::IntegerPolynomialIdentity { bounds, .. }
        | SpecialArithmeticNode::IntegerQuotientShift { bounds, .. }
        | SpecialArithmeticNode::IntegerCastIdentity { bounds, .. }
        | SpecialArithmeticNode::IntegerOperationIdentity { bounds, .. }
        | SpecialArithmeticNode::UnsignedSumBound { bounds, .. }
        | SpecialArithmeticNode::SignedDefined { bounds, .. } => bounds.iter_mut().collect(),
        SpecialArithmeticNode::PointerTranslation {
            relation, bounds, ..
        } => std::iter::once(relation).chain(bounds.iter_mut()).collect(),
        SpecialArithmeticNode::PointerAlignment { premise, .. } => premise.iter_mut().collect(),
        SpecialArithmeticNode::PointerWordEquality {
            relation,
            alignments,
            ..
        } => std::iter::once(relation)
            .chain(alignments.iter_mut())
            .collect(),
        SpecialArithmeticNode::PointerWordFromAlignment { alignments, .. } => {
            alignments.iter_mut().collect()
        }
        SpecialArithmeticNode::FloatReflexive { finite, .. } => vec![finite],
    }
}

/// The certificate's premises narrowed to those its nodes cite, in their
/// original order, with the nodes renumbered to match. The planner offers
/// every candidate fact; a certificate that listed the unused ones would
/// require each to be exactly available again when it is rechecked, though
/// the proof never depends on them.
fn cited_premises_only(
    premises: &[ClickProposition],
    mut nodes: Vec<SpecialArithmeticNode>,
) -> (Vec<ClickProposition>, Vec<SpecialArithmeticNode>) {
    let mut cited = vec![false; premises.len()];
    for node in &mut nodes {
        for index in cited_premise_indices(node) {
            if let Some(flag) = cited.get_mut(*index) {
                *flag = true;
            }
        }
    }
    let mut renumbered = vec![None; premises.len()];
    let mut kept = Vec::new();
    for (index, premise) in premises.iter().enumerate() {
        if cited[index] {
            renumbered[index] = Some(kept.len());
            kept.push(premise.clone());
        }
    }
    for node in &mut nodes {
        for index in cited_premise_indices(node) {
            if let Some(Some(new)) = renumbered.get(*index) {
                *index = *new;
            }
        }
    }
    (kept, nodes)
}

/// For a goal `to_integer((T)x) == to_integer(x)`, either side first, the
/// first premises `lo <= to_integer(x)` and `to_integer(x) <= hi`, as written
/// or as a native comparison's Integer reading, with constant endpoints
/// inside `T`'s range. A widening of a narrow binder `x` instead cites the
/// range facts `x`'s introduction filed, matched exactly as filed.
fn cast_identity_bounds(goal: &Proposition, premises: &[Proposition]) -> Option<Vec<usize>> {
    use crate::kernel::IntegerTerm;
    use crate::kernel::machine_integer::conversion::{cast_operands, narrow_widening};
    let Proposition::ConditionIs(ConditionTerm::IntegerEqual(a, b), true) = goal else {
        return None;
    };
    let (observed, original): (&IntegerTerm, &IntegerTerm) = [(a, b), (b, a)]
        .into_iter()
        .map(|(observed, original)| (observed.as_ref(), original.as_ref()))
        .find(|(observed, original)| {
            narrow_widening(observed, original) || cast_operands(observed).contains(original)
        })?;
    // The identity's destination is the format of the observation's value
    // reading (rule W), as `integer_cast_identity` checks it.
    let IntegerTerm::Machine(machine) = observed.value_read() else {
        return None;
    };
    let (min, max) = machine.ty().format().bounds();
    let bound = |lower: bool| {
        premises.iter().position(|premise| {
            // A bound with an exact native spelling is filed natively, as
            // `x <= 4294967295u64`; its Integer reading is the bound.
            let readings =
                crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(premise);
            std::iter::once(premise).chain(&readings).any(|reading| {
                let Proposition::ConditionIs(ConditionTerm::IntegerLessEqual(left, right), true) =
                    reading
                else {
                    return false;
                };
                let (endpoint, operand) = if lower { (left, right) } else { (right, left) };
                operand.as_ref() == original
                    && endpoint.as_const().is_some_and(|endpoint| {
                        if lower {
                            endpoint >= &min
                        } else {
                            endpoint <= &max
                        }
                    })
            })
        })
    };
    Some(vec![bound(true)?, bound(false)?])
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
    let mut shared_seen = std::collections::HashSet::new();
    while let Some(current) = pending.pop() {
        match current {
            Proposition::ConditionIs(condition, _) => {
                if let Some(view) =
                    crate::kernel::machine_integer::comparison::structural_comparison_view(
                        condition,
                    )
                {
                    for operand in &view.operands {
                        let mut pending = vec![operand.operand_view()];
                        while let Some(term) = pending.pop() {
                            if let crate::kernel::MachineOperandView::Shared(root) = term
                                && !shared_seen.insert(root.id())
                            {
                                continue;
                            }
                            if crate::instrumentation::deadline_exceeded_with_work(1) {
                                return false;
                            }
                            if let Some((_, _, children)) = term.binary() {
                                pending.extend(children);
                            } else if let Some(leaf) = term.read_source()
                                && term_mentions_pointer(&leaf, target)
                            {
                                return true;
                            }
                        }
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

fn term_mentions_pointer(term: &MachineTerm, target: &crate::kernel::Pointer) -> bool {
    let mut pending = vec![term];
    while let Some(current) = pending.pop() {
        match current {
            MachineTerm::PointerAddress(pointer, _) => {
                if bounded_pointer_equal(pointer, target) {
                    return true;
                }
            }
            binary_term!(Bits32, Add, left, right)
            | binary_term!(Bits32, Subtract, left, right)
            | binary_term!(Bits32, Multiply, left, right)
            | MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op:
                    MachineBinaryOp::Add
                    | MachineBinaryOp::Subtract
                    | MachineBinaryOp::Multiply
                    | MachineBinaryOp::Divide
                    | MachineBinaryOp::Remainder
                    | MachineBinaryOp::BitwiseAnd
                    | MachineBinaryOp::BitwiseOr,
                left,
                right,
            }
            | MachineTerm::Float32Binary { left, right, .. }
            | MachineTerm::Float64Binary { left, right, .. } => {
                pending.push(left);
                pending.push(right);
            }
            MachineTerm::PureFunctionApplication { arguments, .. } => {
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
                if aw != bw || !bounded_index_equal(a, b) {
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
                if aw != bw || !bounded_index_equal(a, b) {
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
            ConditionTerm::PointerValueEqual(..)
                | ConditionTerm::PointerEqual(_, _)
                | ConditionTerm::PointerOffsetEqual(_, _),
            true
        )
    )
}
fn is_signed_scalar_bound(p: &Proposition) -> bool {
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: _,
            right: _,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: _,
            right: _,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left: _,
            right: _,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: _,
            right: _,
        },
        true,
    ) = p
    else {
        return false;
    };
    true
}
/// A scalar bound a pointer translation may cite.
fn is_pointer_translation_bound(p: &Proposition) -> bool {
    is_signed_scalar_bound(p) || is_unsigned64_bound(p)
}
/// An unsigned 64-bit order, which bounds a `uint64` index.
fn is_unsigned64_bound(p: &Proposition) -> bool {
    matches!(
        p,
        Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessThan,
                left: _,
                right: _
            } | ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::LessEqual,
                left: _,
                right: _
            } | ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterThan,
                left: _,
                right: _
            } | ConditionTerm::Compare {
                format: MachineIntegerType::UInt64,
                relation: CompareRelation::GreaterEqual,
                left: _,
                right: _
            },
            true,
        )
    )
}
fn is_bitvector64_equality(p: &Proposition) -> bool {
    word_comparison_truth(p) == Some(true)
}
fn is_bitvector64_goal(p: &Proposition) -> bool {
    word_comparison_truth(p).is_some()
}
fn word_comparison_truth(p: &Proposition) -> Option<bool> {
    let Proposition::ConditionIs(condition, truth) = p else {
        return None;
    };
    let view = crate::kernel::machine_integer::comparison::structural_comparison_view(condition)?;
    (matches!(
        view.format,
        MachineIntegerType::Int64 | MachineIntegerType::UInt64
    ) && view.relation == CompareRelation::Equal)
        .then_some(*truth != view.negated)
}
/// Alignment equalities are evidence, not the recorded tagged-word relation.
fn is_word_equality(p: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, _) = p else {
        return false;
    };
    word_comparison_truth(p) == Some(true) && alignment_shape(condition).is_none()
}
fn float_finite_premise(goal: &Proposition, premises: &[Proposition]) -> Option<usize> {
    let Proposition::ConditionIs(condition, _) = goal else {
        return None;
    };
    let (width, expression) = match condition {
        ConditionTerm::Float32(FloatCondition::Comparison { left, right, .. })
            if bounded_term_equal(left, right) =>
        {
            (32, left.as_ref())
        }
        ConditionTerm::Float64(FloatCondition::Comparison { left, right, .. })
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
                    ConditionTerm::Float32(FloatCondition::Classification {
                        classification: FloatClassification::Finite,
                        value,
                    }),
                    true,
                ),
            )
            | (
                64,
                Proposition::ConditionIs(
                    ConditionTerm::Float64(FloatCondition::Classification {
                        classification: FloatClassification::Finite,
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
        ConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        }
        | ConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => bounded_term_work(left) && bounded_term_work(right),
        ConditionTerm::PointerOffsetEqual(left, right) => {
            bounded_offset_work(left) && bounded_offset_work(right)
        }
        ConditionTerm::PointerEqual(left, right) => {
            bounded_pointer_work(left) && bounded_pointer_work(right)
        }
        ConditionTerm::Float32(float) | ConditionTerm::Float64(float) => match float {
            FloatCondition::Comparison { left, right, .. } => {
                bounded_term_work(left) && bounded_term_work(right)
            }
            FloatCondition::Classification { value, .. } => bounded_term_work(value),
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
                if !bounded_index_work(value) =>
            {
                return false;
            }
            _ => {}
        }
    }
    true
}

fn bounded_term_work(root: &MachineTerm) -> bool {
    bounded_term_work_count(root, &mut 0)
}

fn bounded_term_work_count(root: &MachineTerm, count: &mut usize) -> bool {
    let mut pending = vec![root];
    while let Some(term) = pending.pop() {
        *count = count.saturating_add(1);
        if *count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match term {
            binary_term!(Bits32, Add, left, right)
            | binary_term!(Bits32, Subtract, left, right)
            | binary_term!(Bits32, Multiply, left, right)
            | MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op:
                    MachineBinaryOp::Add
                    | MachineBinaryOp::Subtract
                    | MachineBinaryOp::Multiply
                    | MachineBinaryOp::Divide
                    | MachineBinaryOp::Remainder
                    | MachineBinaryOp::BitwiseAnd
                    | MachineBinaryOp::BitwiseOr,
                left,
                right,
            } => {
                pending.push(left);
                pending.push(right);
            }
            cast_term!(UInt32From64, value) => pending.push(value),
            MachineTerm::MemoryLoad(_, pointer, _) if !bounded_pointer_work(pointer) => {
                return false;
            }
            MachineTerm::PointerAddress(pointer, _) if !bounded_offset_work(&pointer.offset) => {
                return false;
            }
            MachineTerm::PointerAddress(pointer, _)
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

fn bounded_index_work(root: &crate::kernel::SharedMachineIntegerTerm) -> bool {
    let mut pending = vec![root.operand_view()];
    let mut count = 0usize;
    while let Some(view) = pending.pop() {
        if let Some(leaf) = view
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| view.read_source())
        {
            if !bounded_term_work_count(&leaf, &mut count) {
                return false;
            }
            continue;
        }
        count += 1;
        if count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        if let Some((format, op, operands)) = view.binary() {
            use MachineBinaryOp::*;
            if matches!(
                (format, op),
                (
                    MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                    Add | Subtract | Multiply
                ) | (
                    MachineIntegerType::UInt64,
                    Add | Subtract | Multiply | Divide | Remainder | BitwiseAnd | BitwiseOr
                )
            ) {
                pending.extend(operands);
            }
        } else if let Some((crate::kernel::MachineCastSpelling::UInt32From64, _, _, operand)) =
            view.cast()
        {
            pending.push(operand);
        }
    }
    true
}

fn bounded_index_equal(
    left: &crate::kernel::SharedMachineIntegerTerm,
    right: &crate::kernel::SharedMachineIntegerTerm,
) -> bool {
    let mut pending = vec![(left.operand_view(), right.operand_view())];
    let mut count = 0usize;
    while let Some((left, right)) = pending.pop() {
        let a = left
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| left.read_source());
        let b = right
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| right.read_source());
        if let (Some(a), Some(b)) = (a, b) {
            if !bounded_term_equal_count(&a, &b, &mut count) {
                return false;
            }
            continue;
        }
        count += 1;
        if count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        if let (
            Some((crate::kernel::MachineCastSpelling::UInt32From64, _, _, a)),
            Some((crate::kernel::MachineCastSpelling::UInt32From64, _, _, b)),
        ) = (left.cast(), right.cast())
        {
            pending.push((a, b));
            continue;
        }
        if let (Some((af, ao, [al, ar])), Some((bf, bo, [bl, br]))) =
            (left.binary(), right.binary())
        {
            use MachineBinaryOp::*;
            if (af, ao) != (bf, bo)
                || !matches!(
                    (af, ao),
                    (MachineIntegerType::Int32, Add | Subtract | Multiply)
                        | (
                            MachineIntegerType::UInt64,
                            Add | Subtract | Multiply | BitwiseAnd | BitwiseOr
                        )
                )
            {
                return false;
            }
            pending.push((al, bl));
            pending.push((ar, br));
        } else {
            return false;
        }
    }
    true
}

fn bounded_term_equal(left: &MachineTerm, right: &MachineTerm) -> bool {
    bounded_term_equal_count(left, right, &mut 0)
}

fn bounded_term_equal_count(left: &MachineTerm, right: &MachineTerm, count: &mut usize) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        *count = count.saturating_add(1);
        if *count > 256 || crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match (left, right) {
            (cast_term!(UInt32From64, left), cast_term!(UInt32From64, right)) => {
                pending.push((left, right))
            }
            (bits32_constant!(a), bits32_constant!(b)) if constant_u32(*a) == constant_u32(*b) => {}
            (int64_constant!(a), int64_constant!(b)) if constant_i64(*a) == constant_i64(*b) => {}
            (uint64_constant!(a), uint64_constant!(b)) if constant_u64(*a) == constant_u64(*b) => {}
            (MachineTerm::Variable(a), MachineTerm::Variable(b)) if a == b => {}
            (MachineTerm::MemoryLoad(lm, lp, lk), MachineTerm::MemoryLoad(rm, rp, rk)) => {
                if lm != rm || lk != rk || !bounded_pointer_equal(lp, rp) {
                    return false;
                }
            }
            (MachineTerm::PointerAddress(_, _), MachineTerm::PointerAddress(_, _)) => {
                return false;
            }
            (
                MachineTerm::PureFunctionApplication {
                    name: left_name,
                    arguments: left_arguments,
                },
                MachineTerm::PureFunctionApplication {
                    name: right_name,
                    arguments: right_arguments,
                },
            ) if left_name == right_name && left_arguments.len() == right_arguments.len() => {
                pending.extend(left_arguments.iter().zip(right_arguments.iter()));
            }
            _ => {
                use crate::kernel::BitvectorBinaryOp as Op;
                let (Some((operator, a, b)), Some((other, c, d))) =
                    (left.as_binary(), right.as_binary())
                else {
                    return false;
                };
                let compared = matches!(
                    operator,
                    Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::Add
                    ) | Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::Subtract
                    ) | Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::Multiply
                    ) | Op::Machine(
                        MachineIntegerType::UInt64,
                        MachineBinaryOp::Add
                            | MachineBinaryOp::Subtract
                            | MachineBinaryOp::Multiply
                            | MachineBinaryOp::BitwiseAnd
                            | MachineBinaryOp::BitwiseOr
                    ) | Op::Float32(_)
                        | Op::Float64(_)
                );
                if operator != other || !compared {
                    return false;
                }
                pending.push((a, c));
                pending.push((b, d));
            }
        }
    }
    true
}

fn alignment_shape(condition: &ConditionTerm) -> Option<(&crate::kernel::Pointer, u64)> {
    crate::kernel::proof::arithmetic_special::checked_pointer_alignment(condition)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kernel::{ComparisonOperator as KernelComparisonOperator, MachineTerm, Variable};

    fn bound(value: usize) -> ClickProposition {
        ClickProposition::Comparison {
            left: ContractExpression::IntegerLiteral("0".to_string()),
            operator: ComparisonOperator::LessEqual,
            right: ContractExpression::IntegerLiteral(value.to_string()),
        }
    }

    #[test]
    fn certificates_keep_only_the_premises_their_nodes_cite() {
        let premises = (0..6).map(bound).collect::<Vec<_>>();
        let goal = bound(99);
        let nodes = vec![
            SpecialArithmeticNode::PointerTranslation {
                relation: 4,
                bounds: vec![1, 4],
                result: goal.clone(),
            },
            SpecialArithmeticNode::SignedDefined {
                width: crate::kernel::SignedDefinedWidth::Int32,
                bounds: vec![1],
                result: goal.clone(),
            },
            SpecialArithmeticNode::PointerAlignment {
                premise: None,
                result: goal.clone(),
            },
        ];
        let (kept, nodes) = cited_premises_only(&premises, nodes);
        assert_eq!(kept, vec![bound(1), bound(4)]);
        assert_eq!(
            nodes,
            vec![
                SpecialArithmeticNode::PointerTranslation {
                    relation: 1,
                    bounds: vec![0, 1],
                    result: goal.clone(),
                },
                SpecialArithmeticNode::SignedDefined {
                    width: crate::kernel::SignedDefinedWidth::Int32,
                    bounds: vec![0],
                    result: goal.clone(),
                },
                SpecialArithmeticNode::PointerAlignment {
                    premise: None,
                    result: goal,
                },
            ]
        );
    }

    #[test]
    fn deep_float_candidate_is_rejected_before_recursive_helpers() {
        let mut term = MachineTerm::Variable(Variable(1));
        for _ in 0..300 {
            term = binary_node!(
                Int32,
                Add,
                Box::new(term),
                Box::new(MachineTerm::constant(1))
            );
        }
        let goal = Proposition::ConditionIs(
            ConditionTerm::Float32(FloatCondition::Comparison {
                operator: KernelComparisonOperator::Equal,
                left: Box::new(term.clone()),
                right: Box::new(term.clone()),
            }),
            true,
        );
        let finite = Proposition::ConditionIs(
            ConditionTerm::Float32(FloatCondition::Classification {
                classification: FloatClassification::Finite,
                value: Box::new(term),
            }),
            true,
        );
        assert!(plan_special_arithmetic_certificate(&goal, &[finite]).is_none());
    }

    #[test]
    fn finite_read_certificate_preserves_state_address_and_kind() {
        let _session = crate::kernel::VerificationSession::enter();
        let memory = crate::kernel::intern_memory(crate::kernel::Memory::new());
        let pointer = crate::kernel::Pointer::symbolic(Variable(22_104));
        let read = |memory, pointer, kind| MachineTerm::MemoryLoad(memory, Box::new(pointer), kind);
        let value = read(
            memory.clone(),
            pointer.clone(),
            crate::kernel::LoadKind::Float64,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::float64_compare(
                value.clone(),
                value.clone(),
                crate::kernel::ComparisonOperator::Equal,
            ),
            true,
        );
        for (value, valid) in [
            (value, true),
            (
                read(
                    memory.clone(),
                    pointer.offset_by_bytes(8),
                    crate::kernel::LoadKind::Float64,
                ),
                false,
            ),
            (
                read(
                    memory.clone(),
                    pointer.clone(),
                    crate::kernel::LoadKind::Bits64,
                ),
                false,
            ),
            (
                read(
                    crate::kernel::intern_memory(
                        crate::kernel::Memory::new().with_block("other", 8),
                    ),
                    pointer,
                    crate::kernel::LoadKind::Float64,
                ),
                false,
            ),
        ] {
            let premise = Proposition::ConditionIs(
                ConditionTerm::float64_classification(value, FloatClassification::Finite),
                true,
            );
            let plan = plan_special_arithmetic_certificate(&goal, std::slice::from_ref(&premise));
            assert_eq!(plan.is_some(), valid);
            if let Some(plan) = plan {
                plan.check(&goal, &[premise]).unwrap();
            }
        }
    }

    #[test]
    fn finite_candidate_scan_charges_unrelated_premises() {
        let value = MachineTerm::Variable(Variable(2));
        let goal = Proposition::ConditionIs(
            ConditionTerm::Float32(FloatCondition::Comparison {
                operator: KernelComparisonOperator::Equal,
                left: Box::new(value.clone()),
                right: Box::new(value.clone()),
            }),
            true,
        );
        let mut premises = (0..64)
            .map(|i| {
                Proposition::ConditionIs(
                    ConditionTerm::Compare {
                        format: MachineIntegerType::Int32,
                        relation: CompareRelation::Equal,
                        left: Box::new(MachineTerm::Variable(Variable(100 + i))),
                        right: Box::new(MachineTerm::constant(i as u32)),
                    },
                    true,
                )
            })
            .collect::<Vec<_>>();
        premises.push(Proposition::ConditionIs(
            ConditionTerm::Float32(FloatCondition::Classification {
                classification: FloatClassification::Finite,
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

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/checking/special_arithmetic_planner/tests.rs");
}
