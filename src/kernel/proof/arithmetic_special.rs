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
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{Hash, Hasher};

const SIGNED_MIN: i64 = i32::MIN as i64;
const SIGNED_MAX: i64 = i32::MAX as i64;
const MAX_TERM_PAYLOAD: usize = 256;

fn charge_payload(payload: usize) -> bool {
    payload <= MAX_TERM_PAYLOAD
        && !crate::instrumentation::deadline_exceeded_with_work(payload.max(1))
}

fn pointer_block_payload(block: &PointerBlock) -> Option<usize> {
    let payload = match block {
        PointerBlock::Concrete(name) | PointerBlock::Function(name) => {
            1usize.checked_add(name.len())?
        }
        PointerBlock::StringLiteral { identity, bytes } => 1usize
            .checked_add(identity.len())?
            .checked_add(bytes.len())?,
        PointerBlock::FunctionSymbolic(_)
        | PointerBlock::ExternalArgument
        | PointerBlock::Symbolic(_)
        | PointerBlock::Heap(_) => 1,
    };
    (payload <= MAX_TERM_PAYLOAD).then_some(payload)
}

fn pointer_payload(pointer: &Pointer) -> Option<usize> {
    pointer_block_payload(&pointer.block)?.checked_add(pointer_offset_payload(&pointer.offset)?)
}

fn pointer_offset_payload(root: &PointerOffsetTerm) -> Option<usize> {
    let mut pending = vec![root];
    let mut payload = 0usize;
    while let Some(offset) = pending.pop() {
        payload = payload.checked_add(1)?;
        if payload > MAX_TERM_PAYLOAD {
            return None;
        }
        match offset {
            PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => {}
            PointerOffsetTerm::Add(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            PointerOffsetTerm::Int32Scaled { value, .. } => {
                payload = payload.checked_add(bitvector_payload(value)?)?;
            }
            PointerOffsetTerm::Int64Scaled { .. } => return None,
        }
        if payload > MAX_TERM_PAYLOAD {
            return None;
        }
    }
    Some(payload)
}

fn bitvector_payload(root: &Bitvector32Term) -> Option<usize> {
    let mut pending = vec![root];
    let mut payload = 0usize;
    while let Some(term) = pending.pop() {
        payload = payload.checked_add(1)?;
        if payload > MAX_TERM_PAYLOAD {
            return None;
        }
        match term {
            Bitvector32Term::Constant(_)
            | Bitvector32Term::Int64Constant(_)
            | Bitvector32Term::UInt64Constant(_)
            | Bitvector32Term::Variable(_) => {}
            Bitvector32Term::Add(left, right)
            | Bitvector32Term::Subtract(left, right)
            | Bitvector32Term::UInt64Add(left, right)
            | Bitvector32Term::UInt64Subtract(left, right)
            | Bitvector32Term::UInt64BitwiseAnd(left, right)
            | Bitvector32Term::UInt64BitwiseOr(left, right)
            | Bitvector32Term::BitwiseAnd(left, right)
            | Bitvector32Term::BitwiseOr(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            Bitvector32Term::PointerAddress(pointer) => {
                payload = payload.checked_add(pointer_payload(pointer)?)?;
            }
            _ => return None,
        }
        if payload > MAX_TERM_PAYLOAD {
            return None;
        }
    }
    Some(payload)
}

fn charge_pointer_offset(offset: &PointerOffsetTerm) -> bool {
    pointer_offset_payload(offset).is_some_and(charge_payload)
}

fn charge_pointer(pointer: &Pointer) -> bool {
    pointer_payload(pointer).is_some_and(charge_payload)
}

fn charge_pointer_block(block: &PointerBlock) -> bool {
    pointer_block_payload(block).is_some_and(charge_payload)
}

fn charge_bitvector(term: &Bitvector32Term) -> bool {
    bitvector_payload(term).is_some_and(charge_payload)
}

fn charge_map_insert(offset: &PointerOffsetTerm, map_len: usize) -> bool {
    let comparisons = (usize::BITS - map_len.max(1).leading_zeros()) as usize;
    pointer_offset_payload(offset).is_some_and(|payload| {
        !crate::instrumentation::deadline_exceeded_with_work(
            payload.saturating_mul(comparisons).max(1),
        )
    })
}

fn charge_signed_bound(proposition: &Proposition) -> bool {
    let Proposition::ConditionIs(
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right),
        true,
    ) = proposition
    else {
        return false;
    };
    charge_bitvector(left) && charge_bitvector(right)
}

fn pointer_block_equal(left: &PointerBlock, right: &PointerBlock) -> bool {
    match (left, right) {
        (PointerBlock::Concrete(left), PointerBlock::Concrete(right))
        | (PointerBlock::Function(left), PointerBlock::Function(right)) => left == right,
        (
            PointerBlock::StringLiteral {
                identity: left_identity,
                bytes: left_bytes,
            },
            PointerBlock::StringLiteral {
                identity: right_identity,
                bytes: right_bytes,
            },
        ) => left_identity == right_identity && left_bytes == right_bytes,
        (PointerBlock::FunctionSymbolic(left), PointerBlock::FunctionSymbolic(right))
        | (PointerBlock::Symbolic(left), PointerBlock::Symbolic(right)) => left == right,
        (PointerBlock::ExternalArgument, PointerBlock::ExternalArgument)
        | (PointerBlock::Heap(_), PointerBlock::Heap(_)) => left == right,
        _ => false,
    }
}

fn pointer_offset_equal(left: &PointerOffsetTerm, right: &PointerOffsetTerm) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => {
                if left != right {
                    return false;
                }
            }
            (PointerOffsetTerm::Variable(left), PointerOffsetTerm::Variable(right)) => {
                if left != right {
                    return false;
                }
            }
            (
                PointerOffsetTerm::Add(left_first, left_second),
                PointerOffsetTerm::Add(right_first, right_second),
            ) => {
                pending.push((left_first, right_first));
                pending.push((left_second, right_second));
            }
            (
                PointerOffsetTerm::Int32Scaled {
                    value: left,
                    byte_width: left_width,
                },
                PointerOffsetTerm::Int32Scaled {
                    value: right,
                    byte_width: right_width,
                },
            ) if left_width == right_width => {
                if !bitvector_equal(left, right) {
                    return false;
                }
            }
            (
                PointerOffsetTerm::Int64Scaled {
                    value: left,
                    byte_width: left_width,
                    unsigned: left_unsigned,
                },
                PointerOffsetTerm::Int64Scaled {
                    value: right,
                    byte_width: right_width,
                    unsigned: right_unsigned,
                },
            ) if left_width == right_width && left_unsigned == right_unsigned => {
                if !bitvector_equal(left, right) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

fn pointer_equal(left: &Pointer, right: &Pointer) -> bool {
    charge_pointer(left)
        && charge_pointer(right)
        && pointer_block_equal(&left.block, &right.block)
        && pointer_offset_equal(&left.offset, &right.offset)
}

/// Compare only the bounded structural fragment accepted by `bitvector_payload`.
/// This avoids recursive equality on attacker-controlled expression depth after
/// the payload has already been charged.
fn bitvector_equal(left: &Bitvector32Term, right: &Bitvector32Term) -> bool {
    if !charge_bitvector(left) || !charge_bitvector(right) {
        return false;
    }
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
                if left != right {
                    return false;
                }
            }
            (Bitvector32Term::Int64Constant(left), Bitvector32Term::Int64Constant(right)) => {
                if left != right {
                    return false;
                }
            }
            (Bitvector32Term::UInt64Constant(left), Bitvector32Term::UInt64Constant(right)) => {
                if left != right {
                    return false;
                }
            }
            (Bitvector32Term::Variable(left), Bitvector32Term::Variable(right)) => {
                if left != right {
                    return false;
                }
            }
            (
                Bitvector32Term::Add(left_first, left_second),
                Bitvector32Term::Add(right_first, right_second),
            )
            | (
                Bitvector32Term::Subtract(left_first, left_second),
                Bitvector32Term::Subtract(right_first, right_second),
            )
            | (
                Bitvector32Term::UInt64Add(left_first, left_second),
                Bitvector32Term::UInt64Add(right_first, right_second),
            )
            | (
                Bitvector32Term::UInt64Subtract(left_first, left_second),
                Bitvector32Term::UInt64Subtract(right_first, right_second),
            )
            | (
                Bitvector32Term::UInt64BitwiseAnd(left_first, left_second),
                Bitvector32Term::UInt64BitwiseAnd(right_first, right_second),
            )
            | (
                Bitvector32Term::UInt64BitwiseOr(left_first, left_second),
                Bitvector32Term::UInt64BitwiseOr(right_first, right_second),
            )
            | (
                Bitvector32Term::BitwiseAnd(left_first, left_second),
                Bitvector32Term::BitwiseAnd(right_first, right_second),
            )
            | (
                Bitvector32Term::BitwiseOr(left_first, left_second),
                Bitvector32Term::BitwiseOr(right_first, right_second),
            ) => {
                pending.push((left_first, right_first));
                pending.push((left_second, right_second));
            }
            (Bitvector32Term::PointerAddress(left), Bitvector32Term::PointerAddress(right)) => {
                if !pointer_equal(left, right) {
                    return false;
                }
            }
            _ => return false,
        }
    }
    true
}

/// Recognize the kernel's alignment proposition only after its complete
/// bitvector payload has been walked and charged.  `as_pointer_alignment`
/// uses the convenience `uint64_as_const` recognizer, whose implementation is
/// recursive for constant expressions; keeping it behind this bounded walk
/// makes attacker-controlled depth fail before that helper is reached.
fn checked_pointer_alignment(condition: &ConditionTerm) -> Option<(&Pointer, u64)> {
    let ConditionTerm::Bitvector64Equal(left, right) = condition else {
        return None;
    };
    if !charge_bitvector(left) || !charge_bitvector(right) {
        return None;
    }
    condition.as_pointer_alignment()
}

fn condition_identity(left: &ConditionTerm, right: &ConditionTerm) -> bool {
    match (left, right) {
        (ConditionTerm::Constant(left), ConditionTerm::Constant(right)) => left == right,
        (
            ConditionTerm::PointerEqual(left_first, left_second),
            ConditionTerm::PointerEqual(right_first, right_second),
        ) => {
            charge_pointer(left_first)
                && charge_pointer(left_second)
                && charge_pointer(right_first)
                && charge_pointer(right_second)
                && pointer_equal(left_first, right_first)
                && pointer_equal(left_second, right_second)
        }
        (
            ConditionTerm::PointerOffsetEqual(left_first, left_second),
            ConditionTerm::PointerOffsetEqual(right_first, right_second),
        ) => {
            charge_pointer_offset(left_first)
                && charge_pointer_offset(left_second)
                && charge_pointer_offset(right_first)
                && charge_pointer_offset(right_second)
                && pointer_offset_equal(left_first, right_first)
                && pointer_offset_equal(left_second, right_second)
        }
        (
            ConditionTerm::Bitvector32Equal(left_first, left_second),
            ConditionTerm::Bitvector32Equal(right_first, right_second),
        )
        | (
            ConditionTerm::Bitvector64Equal(left_first, left_second),
            ConditionTerm::Bitvector64Equal(right_first, right_second),
        )
        | (
            ConditionTerm::Bitvector32SignedLessThan(left_first, left_second),
            ConditionTerm::Bitvector32SignedLessThan(right_first, right_second),
        )
        | (
            ConditionTerm::Bitvector32SignedLessEqual(left_first, left_second),
            ConditionTerm::Bitvector32SignedLessEqual(right_first, right_second),
        )
        | (
            ConditionTerm::Bitvector32SignedGreaterThan(left_first, left_second),
            ConditionTerm::Bitvector32SignedGreaterThan(right_first, right_second),
        )
        | (
            ConditionTerm::Bitvector32SignedGreaterEqual(left_first, left_second),
            ConditionTerm::Bitvector32SignedGreaterEqual(right_first, right_second),
        ) => {
            charge_bitvector(left_first)
                && charge_bitvector(left_second)
                && charge_bitvector(right_first)
                && charge_bitvector(right_second)
                && bitvector_equal(left_first, right_first)
                && bitvector_equal(left_second, right_second)
        }
        (ConditionTerm::Float32(left), ConditionTerm::Float32(right))
        | (ConditionTerm::Float64(left), ConditionTerm::Float64(right)) => {
            float_condition_identity(left, right)
        }
        _ => false,
    }
}

fn float_condition_identity(left: &CFloatCondition, right: &CFloatCondition) -> bool {
    match (left, right) {
        (
            CFloatCondition::Comparison {
                operator: left_operator,
                left: left_first,
                right: left_second,
            },
            CFloatCondition::Comparison {
                operator: right_operator,
                left: right_first,
                right: right_second,
            },
        ) => {
            left_operator == right_operator
                && charge_bitvector(left_first)
                && charge_bitvector(left_second)
                && charge_bitvector(right_first)
                && charge_bitvector(right_second)
                && bitvector_equal(left_first, right_first)
                && bitvector_equal(left_second, right_second)
        }
        (
            CFloatCondition::Classification {
                classification: left_classification,
                value: left_value,
            },
            CFloatCondition::Classification {
                classification: right_classification,
                value: right_value,
            },
        ) => {
            left_classification == right_classification
                && charge_bitvector(left_value)
                && charge_bitvector(right_value)
                && bitvector_equal(left_value, right_value)
        }
        _ => false,
    }
}

/// Compare the selected certificate result with the requested goal without
/// invoking recursive `Proposition`/`ConditionTerm` equality.
fn proposition_identity(left: &Proposition, right: &Proposition) -> bool {
    let Proposition::ConditionIs(left_condition, left_expected) = left else {
        return false;
    };
    let Proposition::ConditionIs(right_condition, right_expected) = right else {
        return false;
    };
    left_expected == right_expected && condition_identity(left_condition, right_condition)
}

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
    WorkLimitExceeded,
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
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return Err(SpecialArithmeticCheckError::WorkLimitExceeded);
        }
        for (index, node) in self.nodes.iter().enumerate() {
            Self::check_node(index, node, premises)?;
        }
        let node = &self.nodes[self.conclusion];
        proposition_identity(node.result(), goal)
            .then_some(())
            .ok_or(SpecialArithmeticCheckError::DoesNotFollow)
    }

    fn check_node(
        index: usize,
        node: &SpecialArithmeticNode,
        premises: &[Proposition],
    ) -> Result<(), SpecialArithmeticCheckError> {
        match node {
            SpecialArithmeticNode::PointerTranslation {
                relation,
                bounds,
                result,
            } => {
                if crate::instrumentation::deadline_exceeded_with_work(
                    bounds.len().saturating_add(1),
                ) {
                    return Err(SpecialArithmeticCheckError::WorkLimitExceeded);
                }
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
                Ok(())
            }
            SpecialArithmeticNode::PointerAlignment { premise, result } => {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    return Err(SpecialArithmeticCheckError::WorkLimitExceeded);
                }
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
                Ok(())
            }
            SpecialArithmeticNode::PointerWordEquality {
                relation,
                alignments,
                result,
            } => {
                if crate::instrumentation::deadline_exceeded_with_work(
                    alignments.len().saturating_add(1),
                ) {
                    return Err(SpecialArithmeticCheckError::WorkLimitExceeded);
                }
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
                Ok(())
            }
            SpecialArithmeticNode::FloatReflexive { finite, result } => {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    return Err(SpecialArithmeticCheckError::WorkLimitExceeded);
                }
                let finite = premises
                    .get(*finite)
                    .ok_or(SpecialArithmeticCheckError::InvalidPremise(*finite))?;
                if !float_reflexive(finite, result) {
                    return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                }
                Ok(())
            }
        }
    }
}

impl SpecialArithmeticNode {
    fn result(&self) -> &Proposition {
        match self {
            Self::PointerTranslation { result, .. }
            | Self::PointerAlignment { result, .. }
            | Self::PointerWordEquality { result, .. }
            | Self::FloatReflexive { result, .. } => result,
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
        if !charge_signed_bound(premise) {
            return None;
        }
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
        let key_payload = bitvector_payload(left)?.max(bitvector_payload(right)?);
        let comparisons = (usize::BITS - bounds.len().max(1).leading_zeros()) as usize;
        if crate::instrumentation::deadline_exceeded_with_work(
            key_payload.saturating_mul(comparisons).max(1),
        ) {
            return None;
        }
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
    if !charge_pointer_offset(goal_left)
        || !charge_pointer_offset(goal_right)
        || !charge_pointer_offset(premise_left)
        || !charge_pointer_offset(premise_right)
    {
        return false;
    }
    if let Some((goal_l, goal_r)) = goal_blocks
        && (!charge_pointer_block(goal_l) || !charge_pointer_block(goal_r))
    {
        return false;
    }
    if let Some((premise_l, premise_r)) = premise_blocks
        && (!charge_pointer_block(premise_l) || !charge_pointer_block(premise_r))
    {
        return false;
    }
    let (left, right) = match (goal_blocks, premise_blocks) {
        (None, None) => (goal_left, goal_right),
        (Some((goal_l, goal_r)), Some((premise_l, premise_r)))
            if pointer_block_equal(goal_l, premise_l) && pointer_block_equal(goal_r, premise_r) =>
        {
            (goal_left, goal_right)
        }
        (Some((goal_l, goal_r)), Some((premise_l, premise_r)))
            if pointer_block_equal(goal_l, premise_r) && pointer_block_equal(goal_r, premise_l) =>
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
            if !charge_map_insert(&atom, terms.len()) {
                return false;
            }
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
    if !charge_pointer_offset(goal) || !charge_pointer_offset(premise) {
        return None;
    }
    let mut terms = BTreeMap::<PointerOffsetTerm, i128>::new();
    let mut constant = 0i128;
    for (offset, sign) in [(goal, 1i128), (premise, -1)] {
        let mut pending = vec![offset];
        while let Some(offset) = pending.pop() {
            match offset {
                PointerOffsetTerm::Constant(value) => {
                    constant = constant.checked_add(sign * i128::from(*value))?
                }
                PointerOffsetTerm::Add(left, right) => {
                    pending.push(left);
                    pending.push(right);
                }
                other => {
                    if !charge_map_insert(other, terms.len()) {
                        return None;
                    }
                    let coefficient = terms.entry(other.clone()).or_default();
                    *coefficient = coefficient.checked_add(sign)?;
                }
            }
        }
    }
    terms.retain(|_, coefficient| *coefficient != 0);
    terms.is_empty().then_some(constant)
}

fn pointer_alignment(premise: Option<&Proposition>, result: &Proposition) -> bool {
    let Proposition::ConditionIs(condition, expected) = result else {
        return false;
    };
    let Some((goal_pointer, goal_alignment)) = checked_pointer_alignment(condition) else {
        return false;
    };
    if !charge_pointer(goal_pointer) {
        return false;
    }
    let premise_alignment = premise.and_then(|proposition| {
        let Proposition::ConditionIs(condition, true) = proposition else {
            return None;
        };
        checked_pointer_alignment(condition)
    });
    if premise.is_some() && premise_alignment.is_none() {
        return false;
    }
    if !goal_alignment.is_power_of_two() {
        return false;
    }
    let aligned = if let Some((base, alignment)) = premise_alignment {
        if !charge_pointer(base) {
            return false;
        }
        if !pointer_block_equal(&base.block, &goal_pointer.block) || alignment % goal_alignment != 0
        {
            return false;
        }
        let Some(delta) = offset_difference(&goal_pointer.offset, &base.offset) else {
            return false;
        };
        delta.rem_euclid(goal_alignment as i128) == 0
    } else {
        let intrinsic_alignment = if pointer_equal(goal_pointer, &Pointer::null()) {
            // The null address is zero, so every valid power-of-two alignment
            // divides it; use the largest possible bound as an intrinsic
            // alignment sentinel.
            Some(u64::MAX)
        } else {
            match &goal_pointer.block {
                PointerBlock::Heap(_) => Some(crate::kernel::primitives::HEAP_ALLOCATION_ALIGNMENT),
                block => {
                    let Some(payload) = pointer_block_payload(block) else {
                        return false;
                    };
                    crate::kernel::primitives::registered_block_alignment_charged(block, payload)
                }
            }
        };
        let Some(intrinsic) = intrinsic_alignment else {
            return false;
        };
        if goal_alignment > intrinsic {
            return false;
        }
        let Some(delta) = offset_difference(&goal_pointer.offset, &PointerOffsetTerm::Constant(0))
        else {
            return false;
        };
        delta.rem_euclid(goal_alignment as i128) == 0
    };
    *expected == aligned
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct TaggedAddress {
    pointer: Pointer,
    tag: Bitvector32Term,
    /// The tag's constant value, when it is known.  Keeping this alongside
    /// the term is important: a symbolic tag chain must not be recursively
    /// re-evaluated every time another address operation extends it.
    tag_constant: Option<u64>,
}

fn bounded_uint64_constants(roots: &[&Bitvector32Term]) -> HashMap<usize, Option<u64>> {
    let mut pending = roots.iter().map(|root| (*root, false)).collect::<Vec<_>>();
    let mut values: HashMap<usize, Option<u64>> = HashMap::new();
    while let Some((term, expanded)) = pending.pop() {
        let identity = term as *const Bitvector32Term as usize;
        if values.contains_key(&identity) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return HashMap::new();
        }
        if expanded {
            let value = match term {
                Bitvector32Term::UInt64Constant(value) => Some(*value),
                Bitvector32Term::UInt64Add(_, _)
                | Bitvector32Term::UInt64Subtract(_, _)
                | Bitvector32Term::UInt64Multiply(_, _)
                | Bitvector32Term::UInt64Divide(_, _)
                | Bitvector32Term::UInt64Remainder(_, _)
                | Bitvector32Term::UInt64ShiftLeft(_, _)
                | Bitvector32Term::UInt64LogicalShiftRight(_, _)
                | Bitvector32Term::UInt64BitwiseAnd(_, _)
                | Bitvector32Term::UInt64BitwiseOr(_, _)
                | Bitvector32Term::UInt64BitwiseXor(_, _) => {
                    let (left, right) = match term {
                        Bitvector32Term::UInt64Add(left, right)
                        | Bitvector32Term::UInt64Subtract(left, right)
                        | Bitvector32Term::UInt64Multiply(left, right)
                        | Bitvector32Term::UInt64Divide(left, right)
                        | Bitvector32Term::UInt64Remainder(left, right)
                        | Bitvector32Term::UInt64ShiftLeft(left, right)
                        | Bitvector32Term::UInt64LogicalShiftRight(left, right)
                        | Bitvector32Term::UInt64BitwiseAnd(left, right)
                        | Bitvector32Term::UInt64BitwiseOr(left, right)
                        | Bitvector32Term::UInt64BitwiseXor(left, right) => (
                            values
                                .get(&(left.as_ref() as *const _ as usize))
                                .copied()
                                .flatten(),
                            values
                                .get(&(right.as_ref() as *const _ as usize))
                                .copied()
                                .flatten(),
                        ),
                        _ => (None, None),
                    };
                    match (term, left, right) {
                        (Bitvector32Term::UInt64Add(_, _), Some(left), Some(right)) => {
                            Some(left.wrapping_add(right))
                        }
                        (Bitvector32Term::UInt64Subtract(_, _), Some(left), Some(right)) => {
                            Some(left.wrapping_sub(right))
                        }
                        (Bitvector32Term::UInt64Multiply(_, _), Some(left), Some(right)) => {
                            Some(left.wrapping_mul(right))
                        }
                        (Bitvector32Term::UInt64Divide(_, _), Some(left), Some(right))
                            if right != 0 =>
                        {
                            Some(left / right)
                        }
                        (Bitvector32Term::UInt64Remainder(_, _), Some(left), Some(right))
                            if right != 0 =>
                        {
                            Some(left % right)
                        }
                        (Bitvector32Term::UInt64ShiftLeft(_, _), Some(left), Some(right))
                            if right < 64 =>
                        {
                            Some(left.wrapping_shl(right as u32))
                        }
                        (
                            Bitvector32Term::UInt64LogicalShiftRight(_, _),
                            Some(left),
                            Some(right),
                        ) if right < 64 => Some(left >> right),
                        (Bitvector32Term::UInt64BitwiseAnd(_, _), Some(left), Some(right)) => {
                            Some(left & right)
                        }
                        (Bitvector32Term::UInt64BitwiseOr(_, _), Some(left), Some(right)) => {
                            Some(left | right)
                        }
                        (Bitvector32Term::UInt64BitwiseXor(_, _), Some(left), Some(right)) => {
                            Some(left ^ right)
                        }
                        _ => None,
                    }
                }
                Bitvector32Term::UInt64BitwiseNot(value) => values
                    .get(&(value.as_ref() as *const _ as usize))
                    .copied()
                    .flatten()
                    .map(|value| !value),
                Bitvector32Term::UInt64From32(value) => match value.as_ref() {
                    Bitvector32Term::Constant(value) => Some(u64::from(*value)),
                    _ => values
                        .get(&(value.as_ref() as *const _ as usize))
                        .copied()
                        .flatten(),
                },
                Bitvector32Term::UInt64FromInt32(value) => match value.as_ref() {
                    Bitvector32Term::Constant(value) => Some((*value as i32 as i64) as u64),
                    _ => values
                        .get(&(value.as_ref() as *const _ as usize))
                        .copied()
                        .flatten(),
                },
                Bitvector32Term::UInt64FromInt64(value) => match value.as_ref() {
                    Bitvector32Term::Int64Constant(value) => Some(*value as u64),
                    _ => values
                        .get(&(value.as_ref() as *const _ as usize))
                        .copied()
                        .flatten(),
                },
                _ => None,
            };
            values.insert(identity, value);
            continue;
        }
        match term {
            Bitvector32Term::UInt64Constant(_) => pending.push((term, true)),
            Bitvector32Term::UInt64BitwiseNot(value)
            | Bitvector32Term::UInt64From32(value)
            | Bitvector32Term::UInt64FromInt32(value)
            | Bitvector32Term::UInt64FromInt64(value) => {
                pending.push((term, true));
                let direct = matches!(
                    (term, value.as_ref()),
                    (
                        Bitvector32Term::UInt64From32(_),
                        Bitvector32Term::Constant(_)
                    ) | (
                        Bitvector32Term::UInt64FromInt32(_),
                        Bitvector32Term::Constant(_)
                    ) | (
                        Bitvector32Term::UInt64FromInt64(_),
                        Bitvector32Term::Int64Constant(_)
                    )
                );
                if !direct {
                    pending.push((value, false));
                }
            }
            Bitvector32Term::UInt64Add(left, right)
            | Bitvector32Term::UInt64Subtract(left, right)
            | Bitvector32Term::UInt64Multiply(left, right)
            | Bitvector32Term::UInt64Divide(left, right)
            | Bitvector32Term::UInt64Remainder(left, right)
            | Bitvector32Term::UInt64ShiftLeft(left, right)
            | Bitvector32Term::UInt64LogicalShiftRight(left, right)
            | Bitvector32Term::UInt64BitwiseAnd(left, right)
            | Bitvector32Term::UInt64BitwiseOr(left, right)
            | Bitvector32Term::UInt64BitwiseXor(left, right) => {
                pending.push((term, true));
                pending.push((right, false));
                pending.push((left, false));
            }
            _ => {
                values.insert(identity, None);
            }
        }
    }
    values
}

fn pointer_identity_hash(pointer: &Pointer) -> Option<u64> {
    let payload = pointer_payload(pointer)?;
    if crate::instrumentation::deadline_exceeded_with_work(payload.max(1)) {
        return None;
    }
    let mut hasher = DefaultHasher::new();
    pointer.block.hash(&mut hasher);
    let mut pending = vec![&pointer.offset];
    while let Some(offset) = pending.pop() {
        match offset {
            PointerOffsetTerm::Constant(value) => {
                0u8.hash(&mut hasher);
                value.hash(&mut hasher);
            }
            PointerOffsetTerm::Variable(value) => {
                1u8.hash(&mut hasher);
                value.hash(&mut hasher);
            }
            PointerOffsetTerm::Add(left, right) => {
                2u8.hash(&mut hasher);
                pending.push(right);
                pending.push(left);
            }
            PointerOffsetTerm::Int32Scaled { value, byte_width } => {
                3u8.hash(&mut hasher);
                byte_width.hash(&mut hasher);
                bounded_term_hash(value)?.hash(&mut hasher);
            }
            PointerOffsetTerm::Int64Scaled { .. } => return None,
        }
    }
    Some(hasher.finish())
}

/// An indexed view of the alignment evidence for one certificate node.  The
/// hash is only an index: a collision still goes through the bounded,
/// iterative pointer comparison before evidence is accepted.
struct AlignmentIndex<'a> {
    by_hash: HashMap<u64, Vec<(&'a Pointer, u64)>>,
}

impl<'a> AlignmentIndex<'a> {
    fn new(alignments: &'a [(&'a Pointer, u64)]) -> Option<Self> {
        let mut by_hash: HashMap<u64, Vec<(&'a Pointer, u64)>> = HashMap::new();
        for (pointer, alignment) in alignments {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            by_hash
                .entry(pointer_identity_hash(pointer)?)
                .or_default()
                .push((*pointer, *alignment));
        }
        Some(Self { by_hash })
    }

    fn supports(&self, pointer: &Pointer, required: u64) -> bool {
        let Some(hash) = pointer_identity_hash(pointer) else {
            return false;
        };
        self.by_hash.get(&hash).is_some_and(|candidates| {
            candidates.iter().any(|(candidate, alignment)| {
                *alignment >= required && pointer_equal(pointer, candidate)
            })
        })
    }
}

fn bounded_term_hashes(roots: &[&Bitvector32Term]) -> Option<HashMap<usize, u64>> {
    let mut pending = roots.iter().map(|root| (*root, false)).collect::<Vec<_>>();
    let mut hashes: HashMap<usize, u64> = HashMap::new();
    while let Some((term, expanded)) = pending.pop() {
        let identity = term as *const Bitvector32Term as usize;
        if hashes.contains_key(&identity) {
            continue;
        }
        if expanded {
            let mut hasher = DefaultHasher::new();
            std::mem::discriminant(term).hash(&mut hasher);
            match term {
                Bitvector32Term::Constant(value) => value.hash(&mut hasher),
                Bitvector32Term::Int64Constant(value) => value.hash(&mut hasher),
                Bitvector32Term::UInt64Constant(value) => value.hash(&mut hasher),
                Bitvector32Term::Variable(value) => value.hash(&mut hasher),
                Bitvector32Term::PointerAddress(pointer) => {
                    pointer_identity_hash(pointer)?.hash(&mut hasher)
                }
                Bitvector32Term::Add(left, right)
                | Bitvector32Term::Subtract(left, right)
                | Bitvector32Term::UInt64Add(left, right)
                | Bitvector32Term::UInt64Subtract(left, right)
                | Bitvector32Term::UInt64BitwiseAnd(left, right)
                | Bitvector32Term::UInt64BitwiseOr(left, right)
                | Bitvector32Term::BitwiseAnd(left, right)
                | Bitvector32Term::BitwiseOr(left, right) => {
                    hashes
                        .get(&(left.as_ref() as *const _ as usize))?
                        .hash(&mut hasher);
                    hashes
                        .get(&(right.as_ref() as *const _ as usize))?
                        .hash(&mut hasher);
                }
                _ => return None,
            }
            hashes.insert(identity, hasher.finish());
        } else {
            pending.push((term, true));
            match term {
                Bitvector32Term::Add(left, right)
                | Bitvector32Term::Subtract(left, right)
                | Bitvector32Term::UInt64Add(left, right)
                | Bitvector32Term::UInt64Subtract(left, right)
                | Bitvector32Term::UInt64BitwiseAnd(left, right)
                | Bitvector32Term::UInt64BitwiseOr(left, right)
                | Bitvector32Term::BitwiseAnd(left, right)
                | Bitvector32Term::BitwiseOr(left, right) => {
                    pending.push((right, false));
                    pending.push((left, false));
                }
                _ => {}
            }
        }
    }
    Some(hashes)
}

fn bounded_term_hash(root: &Bitvector32Term) -> Option<u64> {
    bounded_term_hashes(&[root])?
        .get(&(root as *const Bitvector32Term as usize))
        .copied()
}

fn constant_value(term: &Bitvector32Term, constants: &HashMap<usize, Option<u64>>) -> Option<u64> {
    constants
        .get(&(term as *const Bitvector32Term as usize))
        .copied()
        .flatten()
}

fn add_tag(
    form: TaggedAddress,
    right: Bitvector32Term,
    right_constant: Option<u64>,
) -> TaggedAddress {
    if form.tag_constant == Some(0) {
        TaggedAddress {
            pointer: form.pointer,
            tag: right,
            tag_constant: right_constant,
        }
    } else if right_constant == Some(0) {
        form
    } else {
        TaggedAddress {
            pointer: form.pointer,
            tag: Bitvector32Term::uint64_add(form.tag, right),
            tag_constant: form
                .tag_constant
                .zip(right_constant)
                .map(|(left, right)| left.wrapping_add(right)),
        }
    }
}

fn tagged_form(
    term: &Bitvector32Term,
    relation: (&Bitvector32Term, &Bitvector32Term),
    alignments: &AlignmentIndex<'_>,
) -> Option<TaggedAddress> {
    let identities = bounded_term_hashes(&[term, relation.0, relation.1])?;
    let constants = bounded_uint64_constants(&[term, relation.0, relation.1]);
    if constants.is_empty() {
        return None;
    }
    let relation_keys = (
        *identities.get(&(relation.0 as *const _ as usize))?,
        *identities.get(&(relation.1 as *const _ as usize))?,
    );
    enum Task<'a> {
        Visit(&'a Bitvector32Term),
        FinishAdd {
            term: &'a Bitvector32Term,
            left: &'a Bitvector32Term,
            right: &'a Bitvector32Term,
        },
        FinishAddRight {
            term: &'a Bitvector32Term,
            left: &'a Bitvector32Term,
            right: &'a Bitvector32Term,
        },
        FinishSubtract {
            term: &'a Bitvector32Term,
            right: &'a Bitvector32Term,
        },
        FinishAnd {
            term: &'a Bitvector32Term,
            mask: u64,
            alignment: u64,
        },
        FinishOr {
            term: &'a Bitvector32Term,
            constant: u64,
            alignment: u64,
        },
        FinishRelation {
            term: &'a Bitvector32Term,
        },
    }

    fn store(
        identity: usize,
        result: Option<TaggedAddress>,
        active: &mut HashSet<usize>,
        results: &mut HashMap<usize, Option<TaggedAddress>>,
        values: &mut Vec<Option<TaggedAddress>>,
    ) {
        active.remove(&identity);
        values.push(result.clone());
        results.insert(identity, result);
    }

    let mut tasks = vec![Task::Visit(term)];
    let mut values = Vec::new();
    let mut active = HashSet::new();
    let mut results: HashMap<usize, Option<TaggedAddress>> = HashMap::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(current) => {
                let identity = current as *const _ as usize;
                if let Some(result) = results.get(&identity) {
                    values.push(result.clone());
                    continue;
                }
                if active.contains(&identity) {
                    values.push(None);
                    continue;
                }
                active.insert(identity);
                match current {
                    Bitvector32Term::PointerAddress(pointer) => store(
                        identity,
                        Some(TaggedAddress {
                            pointer: pointer.as_ref().clone(),
                            tag: Bitvector32Term::UInt64Constant(0),
                            tag_constant: Some(0),
                        }),
                        &mut active,
                        &mut results,
                        &mut values,
                    ),
                    Bitvector32Term::UInt64Add(left, right) => {
                        tasks.push(Task::FinishAdd {
                            term: current,
                            left,
                            right,
                        });
                        tasks.push(Task::Visit(left));
                    }
                    Bitvector32Term::UInt64Subtract(left, right) => {
                        tasks.push(Task::FinishSubtract {
                            term: current,
                            right,
                        });
                        tasks.push(Task::Visit(left));
                    }
                    Bitvector32Term::UInt64BitwiseAnd(left, right) => {
                        let (inner, mask) = match (
                            constant_value(left, &constants),
                            constant_value(right, &constants),
                        ) {
                            (None, Some(mask)) => (left.as_ref(), mask),
                            (Some(mask), None) => (right.as_ref(), mask),
                            _ => {
                                store(identity, None, &mut active, &mut results, &mut values);
                                continue;
                            }
                        };
                        let Some(alignment) =
                            (!mask).checked_add(1).filter(|v| v.is_power_of_two())
                        else {
                            store(identity, None, &mut active, &mut results, &mut values);
                            continue;
                        };
                        tasks.push(Task::FinishAnd {
                            term: current,
                            mask,
                            alignment,
                        });
                        tasks.push(Task::Visit(inner));
                    }
                    Bitvector32Term::UInt64BitwiseOr(left, right) => {
                        let (inner, constant) = match (
                            constant_value(left, &constants),
                            constant_value(right, &constants),
                        ) {
                            (None, Some(constant)) => (left.as_ref(), constant),
                            (Some(constant), None) => (right.as_ref(), constant),
                            _ => {
                                store(identity, None, &mut active, &mut results, &mut values);
                                continue;
                            }
                        };
                        let Some(alignment) = constant
                            .checked_add(1)
                            .and_then(|value| value.checked_next_power_of_two())
                        else {
                            store(identity, None, &mut active, &mut results, &mut values);
                            continue;
                        };
                        tasks.push(Task::FinishOr {
                            term: current,
                            constant,
                            alignment,
                        });
                        tasks.push(Task::Visit(inner));
                    }
                    _ if identities.get(&identity) == Some(&relation_keys.0)
                        && bitvector_equal(current, relation.0) =>
                    {
                        tasks.push(Task::FinishRelation { term: current });
                        tasks.push(Task::Visit(relation.1));
                    }
                    _ if identities.get(&identity) == Some(&relation_keys.1)
                        && bitvector_equal(current, relation.1) =>
                    {
                        tasks.push(Task::FinishRelation { term: current });
                        tasks.push(Task::Visit(relation.0));
                    }
                    _ => store(identity, None, &mut active, &mut results, &mut values),
                }
            }
            Task::FinishAdd { term, left, right } => {
                let left_form = values.pop().flatten();
                if let Some(form) = left_form {
                    store(
                        term as *const _ as usize,
                        Some(add_tag(
                            form,
                            right.clone(),
                            constant_value(right, &constants),
                        )),
                        &mut active,
                        &mut results,
                        &mut values,
                    );
                } else {
                    tasks.push(Task::FinishAddRight { term, left, right });
                    tasks.push(Task::Visit(right));
                }
            }
            Task::FinishAddRight {
                term,
                left,
                right: _,
            } => {
                let right_form = values.pop().flatten();
                store(
                    term as *const _ as usize,
                    right_form
                        .map(|form| add_tag(form, left.clone(), constant_value(left, &constants))),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishSubtract { term, right } => {
                let left_form = values.pop().flatten();
                store(
                    term as *const _ as usize,
                    left_form.map(|form| TaggedAddress {
                        pointer: form.pointer,
                        tag: Bitvector32Term::uint64_subtract(form.tag, right.clone()),
                        tag_constant: form
                            .tag_constant
                            .zip(constant_value(right, &constants))
                            .map(|(left, right)| left.wrapping_sub(right)),
                    }),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishAnd {
                term,
                mask,
                alignment,
            } => {
                let form = values.pop().flatten();
                store(
                    term as *const _ as usize,
                    form.and_then(|form| {
                        alignments
                            .supports(&form.pointer, alignment)
                            .then_some(TaggedAddress {
                                pointer: form.pointer,
                                tag: Bitvector32Term::uint64_bitwise_and(
                                    form.tag,
                                    Bitvector32Term::UInt64Constant(mask),
                                ),
                                tag_constant: form.tag_constant.map(|tag| tag & mask),
                            })
                    }),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishOr {
                term,
                constant,
                alignment,
            } => {
                let form = values.pop().flatten();
                store(
                    term as *const _ as usize,
                    form.and_then(|form| {
                        (constant == 0 || alignments.supports(&form.pointer, alignment)).then_some(
                            TaggedAddress {
                                pointer: form.pointer,
                                tag: Bitvector32Term::uint64_bitwise_or(
                                    form.tag,
                                    Bitvector32Term::UInt64Constant(constant),
                                ),
                                tag_constant: form.tag_constant.map(|tag| tag | constant),
                            },
                        )
                    }),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishRelation { term } => {
                let result = values.pop().flatten();
                store(
                    term as *const _ as usize,
                    result,
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
        }
    }
    values.pop().flatten()
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
    let Proposition::ConditionIs(ConditionTerm::Bitvector64Equal(goal_left, goal_right), expected) =
        result
    else {
        return false;
    };
    if !charge_bitvector(left)
        || !charge_bitvector(right)
        || !charge_bitvector(goal_left)
        || !charge_bitvector(goal_right)
    {
        return false;
    }
    let mut alignments = Vec::new();
    for premise in alignment_premises {
        let Proposition::ConditionIs(condition, true) = premise else {
            return false;
        };
        let Some((pointer, alignment)) = checked_pointer_alignment(condition) else {
            return false;
        };
        if !charge_pointer(pointer) {
            return false;
        }
        alignments.push((pointer, alignment));
    }
    let Some(alignment_index) = AlignmentIndex::new(&alignments) else {
        return false;
    };
    if tagged_form(left, (left, right), &alignment_index).is_none()
        || tagged_form(right, (left, right), &alignment_index).is_none()
    {
        return false;
    }
    let goal_left_form = tagged_form(goal_left, (left, right), &alignment_index);
    let goal_right_form = tagged_form(goal_right, (left, right), &alignment_index);
    let equal = match (goal_left_form, goal_right_form) {
        (Some(goal_left), Some(goal_right)) => {
            pointer_equal(&goal_left.pointer, &goal_right.pointer)
                && bitvector_equal(&goal_left.tag, &goal_right.tag)
        }
        _ => false,
    };
    if *expected {
        equal
    } else {
        match (
            tagged_form(goal_left, (left, right), &alignment_index),
            tagged_form(goal_right, (left, right), &alignment_index),
        ) {
            (Some(goal_left), Some(goal_right))
                if pointer_equal(&goal_left.pointer, &goal_right.pointer) =>
            {
                matches!(
                    (goal_left.tag_constant, goal_right.tag_constant),
                    (Some(left), Some(right)) if left != right
                )
            }
            _ => false,
        }
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
    if !charge_bitvector(finite_expression) {
        return false;
    }
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
    if !charge_bitvector(left) || !charge_bitvector(right) {
        return false;
    }
    if width != finite_width
        || !bitvector_equal(left, right)
        || !bitvector_equal(left, finite_expression)
    {
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

    fn heap_pointer(offset: PointerOffsetTerm) -> Pointer {
        Pointer {
            block: PointerBlock::Heap(7),
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
                    block: base.block.clone(),
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
            .check(&goal, std::slice::from_ref(&aligned_base)),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));

        let known_misalignment = Proposition::ConditionIs(
            ConditionTerm::pointer_aligned(
                Pointer {
                    block: base.block.clone(),
                    offset: PointerOffsetTerm::Constant(1),
                },
                8,
            ),
            false,
        );
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerAlignment {
                premise: Some(0),
                result: known_misalignment.clone(),
            }],
            conclusion: 0,
        }
        .check(&known_misalignment, std::slice::from_ref(&aligned_base))
        .unwrap();

        let unknown_offset = Proposition::ConditionIs(
            ConditionTerm::pointer_aligned(
                pointer(PointerOffsetTerm::Variable(crate::kernel::Variable(77))),
                8,
            ),
            false,
        );
        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerAlignment {
                    premise: None,
                    result: unknown_offset.clone(),
                }],
                conclusion: 0,
            }
            .check(&unknown_offset, &[]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));

        let unknown_from_base = Proposition::ConditionIs(
            ConditionTerm::pointer_aligned(
                Pointer {
                    block: base.block.clone(),
                    offset: PointerOffsetTerm::Add(
                        Box::new(PointerOffsetTerm::Constant(0)),
                        Box::new(PointerOffsetTerm::Variable(crate::kernel::Variable(78))),
                    ),
                },
                8,
            ),
            false,
        );
        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerAlignment {
                    premise: Some(0),
                    result: unknown_from_base.clone(),
                }],
                conclusion: 0,
            }
            .check(&unknown_from_base, std::slice::from_ref(&aligned_base)),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));

        for alignment in [2, 4, 8, 16] {
            let goal = Proposition::ConditionIs(
                ConditionTerm::pointer_aligned(
                    heap_pointer(PointerOffsetTerm::Constant(0)),
                    alignment,
                ),
                true,
            );
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerAlignment {
                    premise: None,
                    result: goal.clone(),
                }],
                conclusion: 0,
            }
            .check(&goal, &[])
            .unwrap();
        }
        for alignment in [32, 4096] {
            let goal = Proposition::ConditionIs(
                ConditionTerm::pointer_aligned(
                    heap_pointer(PointerOffsetTerm::Constant(0)),
                    alignment,
                ),
                true,
            );
            assert!(matches!(
                SpecialArithmeticCertificate {
                    nodes: vec![SpecialArithmeticNode::PointerAlignment {
                        premise: None,
                        result: goal.clone(),
                    }],
                    conclusion: 0,
                }
                .check(&goal, &[]),
                Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
            ));

            let unknown_negative = Proposition::ConditionIs(
                ConditionTerm::pointer_aligned(
                    heap_pointer(PointerOffsetTerm::Constant(0)),
                    alignment,
                ),
                false,
            );
            assert!(matches!(
                SpecialArithmeticCertificate {
                    nodes: vec![SpecialArithmeticNode::PointerAlignment {
                        premise: None,
                        result: unknown_negative.clone(),
                    }],
                    conclusion: 0,
                }
                .check(&unknown_negative, &[]),
                Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
            ));
        }

        crate::kernel::primitives::clear_block_alignment_registry();
        let registered_block = PointerBlock::Concrete("registered-static".to_string());
        crate::kernel::primitives::register_block_alignment(&registered_block, 32);
        let registered = Proposition::ConditionIs(
            ConditionTerm::pointer_aligned(
                Pointer {
                    block: registered_block,
                    offset: PointerOffsetTerm::Constant(0),
                },
                32,
            ),
            true,
        );
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerAlignment {
                premise: None,
                result: registered.clone(),
            }],
            conclusion: 0,
        }
        .check(&registered, &[])
        .unwrap();
        crate::kernel::primitives::clear_block_alignment_registry();

        for alignment in [1, 2, 4, 8, 16, 32, 64, 1u64 << 63] {
            let null_condition = ConditionTerm::Bitvector64Equal(
                Box::new(Bitvector32Term::UInt64BitwiseAnd(
                    Box::new(Bitvector32Term::PointerAddress(Box::new(Pointer::null()))),
                    Box::new(Bitvector32Term::UInt64Constant(alignment - 1)),
                )),
                Box::new(Bitvector32Term::UInt64Constant(0)),
            );
            let null = Proposition::ConditionIs(null_condition.clone(), true);
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerAlignment {
                    premise: None,
                    result: null.clone(),
                }],
                conclusion: 0,
            }
            .check(&null, &[])
            .unwrap_or_else(|error| panic!("null alignment {alignment}: {error:?}"));
            let negative = Proposition::ConditionIs(null_condition, false);
            assert!(matches!(
                SpecialArithmeticCertificate {
                    nodes: vec![SpecialArithmeticNode::PointerAlignment {
                        premise: None,
                        result: negative.clone(),
                    }],
                    conclusion: 0,
                }
                .check(&negative, &[]),
                Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
            ));
        }

        for expected in [true, false] {
            let displaced_null = Proposition::ConditionIs(
                ConditionTerm::pointer_aligned(
                    Pointer {
                        block: PointerBlock::Concrete("null".to_string()),
                        offset: PointerOffsetTerm::Constant(1),
                    },
                    2,
                ),
                expected,
            );
            assert!(matches!(
                SpecialArithmeticCertificate {
                    nodes: vec![SpecialArithmeticNode::PointerAlignment {
                        premise: None,
                        result: displaced_null.clone(),
                    }],
                    conclusion: 0,
                }
                .check(&displaced_null, &[]),
                Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
            ));
        }
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
        certificate
            .check(&goal, &[relation.clone(), alignment.clone()])
            .unwrap();

        assert!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                    relation: 0,
                    alignments: vec![],
                    result: goal.clone(),
                }],
                conclusion: 0,
            }
            .check(&goal, std::slice::from_ref(&relation))
            .is_err(),
            "a tag mask must not be used without alignment evidence"
        );
        assert!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                    relation: 1,
                    alignments: vec![0],
                    result: goal.clone(),
                }],
                conclusion: 0,
            }
            .check(&goal, &[relation.clone(), alignment.clone()])
            .is_err(),
            "the relation reference must name the exact word equality"
        );

        // Keep the source form used by tagged-pointer resources: the word is
        // related directly to address(p) plus its low tag bit.
        let word = Bitvector32Term::Variable(crate::kernel::Variable(11));
        let direct_address =
            Bitvector32Term::PointerAddress(Box::new(pointer(PointerOffsetTerm::Constant(0))));
        let direct_tag =
            Bitvector32Term::uint64_bitwise_and(word.clone(), Bitvector32Term::UInt64Constant(1));
        let direct = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                word.clone(),
                Bitvector32Term::uint64_add(direct_address.clone(), direct_tag.clone()),
            ),
            true,
        );
        let direct_alignment = Proposition::ConditionIs(
            ConditionTerm::pointer_aligned(pointer(PointerOffsetTerm::Constant(0)), 2),
            true,
        );
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                relation: 0,
                alignments: vec![1],
                result: direct.clone(),
            }],
            conclusion: 0,
        }
        .check(&direct, &[direct.clone(), direct_alignment.clone()])
        .unwrap();

        let wrong_mask = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                word.clone(),
                Bitvector32Term::uint64_add(
                    direct_address.clone(),
                    Bitvector32Term::uint64_bitwise_and(
                        word.clone(),
                        Bitvector32Term::UInt64Constant(3),
                    ),
                ),
            ),
            true,
        );
        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                    relation: 0,
                    alignments: vec![1],
                    result: wrong_mask.clone(),
                }],
                conclusion: 0,
            }
            .check(&wrong_mask, &[direct, direct_alignment]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));

        let wrong_polarity = Proposition::ConditionIs(
            match goal {
                Proposition::ConditionIs(condition, _) => condition,
                _ => unreachable!(),
            },
            false,
        );
        assert!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                    relation: 0,
                    alignments: vec![1],
                    result: wrong_polarity.clone(),
                }],
                conclusion: 0,
            }
            .check(&wrong_polarity, &[relation, alignment])
            .is_err()
        );
    }

    #[test]
    fn tagged_word_alignment_index_scales_with_alignment_count() {
        let pointer = pointer(PointerOffsetTerm::Constant(0));
        let address = Bitvector32Term::PointerAddress(Box::new(pointer.clone()));
        let word = Bitvector32Term::Variable(crate::kernel::Variable(12));
        let relation = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                word.clone(),
                Bitvector32Term::uint64_add(address.clone(), Bitvector32Term::UInt64Constant(1)),
            ),
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                Bitvector32Term::uint64_bitwise_or(word, Bitvector32Term::UInt64Constant(2)),
                Bitvector32Term::uint64_add(address, Bitvector32Term::UInt64Constant(3)),
            ),
            true,
        );
        let alignment = Proposition::ConditionIs(ConditionTerm::pointer_aligned(pointer, 8), true);
        let mut previous = None;
        for size in [1, 4, 16, 64, 256, 1024] {
            let mut premises = vec![relation.clone()];
            premises.extend((0..size).map(|_| alignment.clone()));
            let certificate = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                    relation: 0,
                    alignments: (1..=size).collect(),
                    result: goal.clone(),
                }],
                conclusion: 0,
            };
            let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
                certificate.check(&goal, &premises).is_ok()
            });
            assert!(valid);
            if let Some(previous) = previous {
                assert!(work <= previous * 4);
            }
            previous = Some(work);
        }
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

    #[test]
    fn deep_pointer_terms_are_rejected_before_recursive_key_comparison() {
        let mut offset = PointerOffsetTerm::Constant(0);
        for _ in 0..=MAX_TERM_PAYLOAD {
            offset = add(offset, PointerOffsetTerm::Constant(0));
        }
        let relation = pointer_eq(offset.clone(), PointerOffsetTerm::Constant(0));
        let goal = pointer_eq(offset, PointerOffsetTerm::Constant(0));
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerTranslation {
                relation: 0,
                bounds: vec![],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        assert!(matches!(
            certificate.check(&goal, &[relation]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));
    }

    #[test]
    fn translation_work_scales_with_explicit_payload() {
        let mut previous = None;
        for size in [4, 8, 16, 32, 64] {
            let p = PointerOffsetTerm::Variable(crate::kernel::Variable(100));
            let arr = PointerOffsetTerm::Variable(crate::kernel::Variable(101));
            let i = Bitvector32Term::Variable(crate::kernel::Variable(1));
            let n = Bitvector32Term::Variable(crate::kernel::Variable(2));
            let mut left = p.clone();
            let mut right = add(arr.clone(), scaled(i.clone()));
            let mut premises = vec![Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(Box::new(i.clone()), Box::new(n.clone())),
                true,
            )];
            for index in 0..size {
                let delta = PointerOffsetTerm::Variable(crate::kernel::Variable(1000 + index));
                left = add(left, delta.clone());
                right = add(right, delta);
                premises.push(Proposition::ConditionIs(
                    ConditionTerm::Bitvector32SignedLessThan(
                        Box::new(Bitvector32Term::Variable(crate::kernel::Variable(
                            2000 + index,
                        ))),
                        Box::new(Bitvector32Term::Constant(100)),
                    ),
                    true,
                ));
            }
            let relation = pointer_eq(p, add(arr, scaled(i)));
            let goal = pointer_eq(left, right);
            premises.insert(0, relation);
            let certificate = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerTranslation {
                    relation: 0,
                    bounds: (1..premises.len()).collect(),
                    result: goal.clone(),
                }],
                conclusion: 0,
            };
            let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
                certificate.check(&goal, &premises).is_ok()
            });
            assert!(valid);
            if let Some(previous) = previous {
                assert!(work <= previous * 4);
            }
            previous = Some(work);
        }
    }

    #[test]
    fn tagged_word_negative_result_needs_distinct_constant_tags() {
        let pointer = pointer(PointerOffsetTerm::Constant(0));
        let address = Bitvector32Term::PointerAddress(Box::new(pointer));
        let word = Bitvector32Term::Variable(crate::kernel::Variable(30));
        let relation = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                word,
                Bitvector32Term::uint64_add(address.clone(), Bitvector32Term::UInt64Constant(1)),
            ),
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                Bitvector32Term::uint64_add(address.clone(), Bitvector32Term::UInt64Constant(1)),
                Bitvector32Term::uint64_add(address, Bitvector32Term::UInt64Constant(2)),
            ),
            false,
        );
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                relation: 0,
                alignments: vec![],
                result: goal.clone(),
            }],
            conclusion: 0,
        }
        .check(&goal, &[relation])
        .unwrap();
    }

    #[test]
    fn tagged_word_rejects_cyclic_raw_variable_relation() {
        let left = Bitvector32Term::Variable(crate::kernel::Variable(80));
        let right = Bitvector32Term::Variable(crate::kernel::Variable(81));
        let relation = Proposition::ConditionIs(
            ConditionTerm::Bitvector64Equal(Box::new(left.clone()), Box::new(right.clone())),
            true,
        );
        let goal = relation.clone();
        let certificate = SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                relation: 0,
                alignments: vec![],
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        assert!(matches!(
            certificate.check(&goal, &[relation]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));
    }

    #[test]
    fn tagged_word_traversal_scales_with_tagged_depth() {
        let mut previous = None;
        for depth in [4, 8, 16, 32, 64] {
            let address =
                Bitvector32Term::PointerAddress(Box::new(pointer(PointerOffsetTerm::Constant(0))));
            let variable = Bitvector32Term::Variable(crate::kernel::Variable(94));
            let mut tagged = address;
            for _ in 0..depth {
                tagged = Bitvector32Term::UInt64Add(
                    Box::new(tagged),
                    Box::new(Bitvector32Term::UInt64Constant(1)),
                );
            }
            let relation = Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(Box::new(variable.clone()), Box::new(tagged)),
                true,
            );
            let goal = Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(Box::new(variable.clone()), Box::new(variable)),
                true,
            );
            let certificate = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                    relation: 0,
                    alignments: vec![],
                    result: goal.clone(),
                }],
                conclusion: 0,
            };
            let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
                certificate
                    .check(&goal, std::slice::from_ref(&relation))
                    .is_ok()
            });
            assert!(valid);
            if let Some(previous) = previous {
                assert!(work <= previous * 4);
            }
            previous = Some(work);
        }
    }

    #[test]
    fn tagged_word_symbolic_tag_chains_scale_without_rewalking_tags() {
        let mut previous = None;
        for depth in [4, 8, 16, 32, 64] {
            let address =
                Bitvector32Term::PointerAddress(Box::new(pointer(PointerOffsetTerm::Constant(0))));
            let variable = Bitvector32Term::Variable(crate::kernel::Variable(194));
            let mut tagged = address;
            for index in 0..depth {
                tagged = Bitvector32Term::UInt64Add(
                    Box::new(tagged),
                    Box::new(Bitvector32Term::Variable(crate::kernel::Variable(
                        200 + index,
                    ))),
                );
            }
            let relation = Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(Box::new(variable.clone()), Box::new(tagged)),
                true,
            );
            let goal = Proposition::ConditionIs(
                ConditionTerm::Bitvector64Equal(Box::new(variable.clone()), Box::new(variable)),
                true,
            );
            let certificate = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                    relation: 0,
                    alignments: vec![],
                    result: goal.clone(),
                }],
                conclusion: 0,
            };
            let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
                certificate
                    .check(&goal, std::slice::from_ref(&relation))
                    .is_ok()
            });
            assert!(valid);
            if let Some(previous) = previous {
                assert!(work <= previous * 4);
            }
            previous = Some(work);
        }
    }

    #[test]
    fn pointer_block_payload_is_bounded_before_block_comparison() {
        let blocks = [
            PointerBlock::Concrete("c".repeat(MAX_TERM_PAYLOAD + 1)),
            PointerBlock::StringLiteral {
                identity: "s".repeat(MAX_TERM_PAYLOAD / 2 + 1),
                bytes: vec![b'x'; MAX_TERM_PAYLOAD / 2 + 1],
            },
        ];
        for block in blocks {
            let left = Pointer {
                block: block.clone(),
                offset: PointerOffsetTerm::Constant(0),
            };
            let right = Pointer {
                block,
                offset: PointerOffsetTerm::Constant(0),
            };
            let relation = Proposition::ConditionIs(
                ConditionTerm::PointerEqual(Box::new(left.clone()), Box::new(right.clone())),
                true,
            );
            let certificate = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerTranslation {
                    relation: 0,
                    bounds: vec![],
                    result: relation.clone(),
                }],
                conclusion: 0,
            };
            assert!(matches!(
                certificate.check(&relation, std::slice::from_ref(&relation)),
                Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
            ));
        }
    }

    #[test]
    fn alignment_premise_charges_concrete_and_string_literal_blocks() {
        let normal_pointer = pointer(PointerOffsetTerm::Constant(0));
        let address = Bitvector32Term::PointerAddress(Box::new(normal_pointer.clone()));
        let word = Bitvector32Term::Variable(crate::kernel::Variable(92));
        let relation = Proposition::ConditionIs(
            ConditionTerm::Bitvector64Equal(
                Box::new(word.clone()),
                Box::new(Bitvector32Term::uint64_add(
                    address.clone(),
                    Bitvector32Term::UInt64Constant(1),
                )),
            ),
            true,
        );
        let blocks = [
            PointerBlock::Concrete("c".repeat(MAX_TERM_PAYLOAD + 1)),
            PointerBlock::StringLiteral {
                identity: "s".repeat(MAX_TERM_PAYLOAD / 2 + 1),
                bytes: vec![b'x'; MAX_TERM_PAYLOAD / 2 + 1],
            },
        ];
        for block in blocks {
            let alignment = Proposition::ConditionIs(
                ConditionTerm::pointer_aligned(
                    Pointer {
                        block,
                        offset: PointerOffsetTerm::Constant(0),
                    },
                    8,
                ),
                true,
            );
            let certificate = SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                    relation: 0,
                    alignments: vec![1],
                    result: relation.clone(),
                }],
                conclusion: 0,
            };
            assert!(matches!(
                certificate.check(&relation, &[relation.clone(), alignment]),
                Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
            ));
        }
    }

    #[test]
    fn float_payload_is_bounded_before_structural_identity() {
        let mut value = Bitvector32Term::Variable(crate::kernel::Variable(90));
        for _ in 0..=MAX_TERM_PAYLOAD {
            value = Bitvector32Term::Add(Box::new(value), Box::new(Bitvector32Term::Constant(1)));
        }
        let finite = Proposition::ConditionIs(
            ConditionTerm::float32_classification(value.clone(), CFloatClassification::Finite),
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::float32_compare(value.clone(), value, CComparisonOperator::Equal),
            true,
        );
        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::FloatReflexive {
                    finite: 0,
                    result: goal.clone(),
                }],
                conclusion: 0,
            }
            .check(&goal, &[finite]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));
    }

    #[test]
    fn alignment_masks_are_bounded_before_constant_recognition() {
        let mut mask = Bitvector32Term::UInt64Constant(7);
        for _ in 0..=MAX_TERM_PAYLOAD {
            mask = Bitvector32Term::UInt64BitwiseOr(
                Box::new(mask),
                Box::new(Bitvector32Term::UInt64Constant(0)),
            );
        }
        let deep_alignment = Proposition::ConditionIs(
            ConditionTerm::Bitvector64Equal(
                Box::new(Bitvector32Term::UInt64BitwiseAnd(
                    Box::new(Bitvector32Term::PointerAddress(Box::new(heap_pointer(
                        PointerOffsetTerm::Constant(0),
                    )))),
                    Box::new(mask),
                )),
                Box::new(Bitvector32Term::UInt64Constant(0)),
            ),
            true,
        );

        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerAlignment {
                    premise: None,
                    result: deep_alignment.clone(),
                }],
                conclusion: 0,
            }
            .check(&deep_alignment, &[]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));

        let word = Bitvector32Term::Variable(crate::kernel::Variable(93));
        let address =
            Bitvector32Term::PointerAddress(Box::new(pointer(PointerOffsetTerm::Constant(0))));
        let relation = Proposition::ConditionIs(
            ConditionTerm::Bitvector64Equal(
                Box::new(word.clone()),
                Box::new(Bitvector32Term::uint64_add(
                    address.clone(),
                    Bitvector32Term::UInt64Constant(1),
                )),
            ),
            true,
        );
        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                    relation: 0,
                    alignments: vec![1],
                    result: relation.clone(),
                }],
                conclusion: 0,
            }
            .check(&relation, &[relation.clone(), deep_alignment]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));
    }

    #[test]
    fn final_goal_identity_is_bounded_before_structural_equality() {
        let result = Proposition::ConditionIs(
            ConditionTerm::pointer_aligned(heap_pointer(PointerOffsetTerm::Constant(0)), 8),
            true,
        );
        let mut mask = Bitvector32Term::UInt64Constant(7);
        for _ in 0..=MAX_TERM_PAYLOAD {
            mask = Bitvector32Term::UInt64BitwiseOr(
                Box::new(mask),
                Box::new(Bitvector32Term::UInt64Constant(0)),
            );
        }
        let goal = Proposition::ConditionIs(
            ConditionTerm::Bitvector64Equal(
                Box::new(Bitvector32Term::UInt64BitwiseAnd(
                    Box::new(Bitvector32Term::PointerAddress(Box::new(heap_pointer(
                        PointerOffsetTerm::Constant(0),
                    )))),
                    Box::new(mask),
                )),
                Box::new(Bitvector32Term::UInt64Constant(0)),
            ),
            true,
        );
        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerAlignment {
                    premise: None,
                    result,
                }],
                conclusion: 0,
            }
            .check(&goal, &[]),
            Err(SpecialArithmeticCheckError::DoesNotFollow)
        ));
    }

    #[test]
    fn checker_validates_unselected_nodes_and_scales_without_cloning_results() {
        let value = Bitvector32Term::Variable(crate::kernel::Variable(91));
        let finite = Proposition::ConditionIs(
            ConditionTerm::float32_classification(value.clone(), CFloatClassification::Finite),
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::float32_compare(value.clone(), value, CComparisonOperator::Equal),
            true,
        );
        let mut nodes = vec![SpecialArithmeticNode::FloatReflexive {
            finite: 0,
            result: goal.clone(),
        }];
        nodes.extend((0..1024).map(|_| SpecialArithmeticNode::FloatReflexive {
            finite: usize::MAX,
            result: Proposition::ConditionIs(ConditionTerm::Constant(false), true),
        }));
        let invalid = SpecialArithmeticCertificate {
            nodes,
            conclusion: 0,
        };
        assert!(matches!(
            invalid.check(&goal, std::slice::from_ref(&finite)),
            Err(SpecialArithmeticCheckError::InvalidPremise(usize::MAX))
        ));

        let mut previous = None;
        for size in [1, 4, 16, 64, 256, 1024] {
            let nodes = (0..size)
                .map(|_| SpecialArithmeticNode::FloatReflexive {
                    finite: 0,
                    result: goal.clone(),
                })
                .collect();
            let certificate = SpecialArithmeticCertificate {
                nodes,
                conclusion: 0,
            };
            let (valid, work) = crate::instrumentation::measure_deterministic_work(|| {
                certificate
                    .check(&goal, std::slice::from_ref(&finite))
                    .is_ok()
            });
            assert!(valid);
            if let Some(previous) = previous {
                assert!(work <= previous * 4);
            }
            previous = Some(work);
        }
    }
}
