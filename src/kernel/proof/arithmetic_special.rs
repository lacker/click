//! Locally checkable certificates for the non-machine-integer arithmetic
//! fragments which are currently routed through `arithmetic`.
//!
//! This module intentionally has no planner and does not call the legacy
//! arithmetic decision procedure.  Every node names the exact premise
//! positions it consumes and carries the proposition it claims to establish.
//! The surface migration can construct these nodes later without changing the
//! kernel boundary.

use super::super::{
    ComparisonOperator, ConditionTerm, FloatClassification, FloatCondition, MachineTerm, Pointer,
    PointerBlock, PointerOffsetTerm, PointerValue, Proposition, SignedDefinedWidth,
};
#[cfg(test)]
use crate::kernel::binary_node;
use crate::kernel::binary_term;
use crate::kernel::{CompareRelation, OverflowOperation};
use crate::kernel::{IntegerTerm, MachineIntegerType};
use crate::kernel::{MachineBinaryOp, MachineUnaryOp};
use crate::kernel::{MachineCastSpelling, cast_term};
use crate::kernel::{
    bits32_constant, constant_i64, constant_u32, constant_u64, int32_constant, int64_constant,
    native_constant, uint64_constant,
};
use std::collections::hash_map::DefaultHasher;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::hash::{Hash, Hasher};
use std::sync::Arc;

mod word_view;
use word_view::{Key as WordKey, Node as WordNode, Word};

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
        PointerBlock::PureFunctionApplication(_)
        | PointerBlock::FunctionSymbolic(_)
        | PointerBlock::ExternalArgument
        | PointerBlock::ExternalObject(_)
        | PointerBlock::Symbolic(_)
        | PointerBlock::LoadedPointer(_)
        | PointerBlock::Heap(_)
        | PointerBlock::Temporary(_) => 1,
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
            PointerOffsetTerm::Int32Scaled { value, .. }
            | PointerOffsetTerm::Int64Scaled { value, .. } => {
                payload = payload.checked_add(pointer_index_payload(value.operand_view())?)?;
            }
        }
        if payload > MAX_TERM_PAYLOAD {
            return None;
        }
    }
    Some(payload)
}

// Preserve the certificate's occurrence budget and supported native syntax.
// The bounded walk never materializes the potentially much larger native tree.
fn pointer_index_payload(root: crate::kernel::MachineOperandView<'_>) -> Option<usize> {
    use crate::kernel::{MachineCastSpelling as E, MachineOperandView as V};
    let mut pending = vec![root];
    let mut total = 0usize;
    while let Some(view) = pending.pop() {
        if let Some(leaf) = view
            .literal()
            .map(std::borrow::Cow::Owned)
            .or_else(|| view.read_source())
        {
            total = total.checked_add(bitvector_payload(&leaf)?)?;
        } else if let Some((format, op, operands)) = view.binary() {
            if !operand_identity::binary_supported(format, op) {
                return None;
            }
            total = total.checked_add(1)?;
            pending.extend(operands);
        } else if let Some((encoding, _, _, operand)) = view.cast() {
            if !matches!(
                encoding,
                E::Generic | E::Int64FromUInt32 | E::UInt64From32 | E::UInt32From64
            ) {
                return None;
            }
            total = total.checked_add(1)?;
            pending.push(operand);
        } else if let V::Legacy(term) = view {
            total = total.checked_add(bitvector_payload(term)?)?;
        } else {
            return None;
        }
        if total > MAX_TERM_PAYLOAD {
            return None;
        }
    }
    Some(total)
}

fn bitvector_payload(root: &MachineTerm) -> Option<usize> {
    let mut pending = vec![root];
    let mut payload = 0usize;
    while let Some(term) = pending.pop() {
        payload = payload.checked_add(1)?;
        if payload > MAX_TERM_PAYLOAD {
            return None;
        }
        match term {
            MachineTerm::Constant { .. } | MachineTerm::Variable(_) => {}
            // Integer operands are already interned by shallow identity.
            MachineTerm::IntegerToMachine { .. } => {}
            MachineTerm::Binary {
                format: MachineIntegerType::Int64,
                op: MachineBinaryOp::Add,
                left,
                right,
            }
            | binary_term!(Int32, BitwiseXor, left, right)
            | binary_term!(Int32, Add, left, right)
            | binary_term!(Int32, Subtract, left, right)
            | MachineTerm::Float32Binary { left, right, .. }
            | MachineTerm::Float64Binary { left, right, .. }
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
            | binary_term!(Int32, BitwiseAnd, left, right)
            | binary_term!(Int32, BitwiseOr, left, right) => {
                pending.push(left);
                pending.push(right);
            }
            cast_term!(Int64FromUInt32, value)
            | cast_term!(UInt64From32, value)
            | cast_term!(UInt32From64, value)
            | MachineTerm::Float32Negate(value)
            | MachineTerm::Float64Negate(value) => pending.push(value),
            MachineTerm::Cast {
                spelling: MachineCastSpelling::Generic,
                value,
                ..
            } => pending.push(value),
            MachineTerm::PureFunctionApplication { name, arguments } => {
                payload = payload.checked_add(name.len())?;
                pending.extend(arguments.iter());
            }
            MachineTerm::PointerAddress(pointer, _) | MachineTerm::MemoryLoad(_, pointer, _) => {
                // A read owns an interned state; only its written address
                // contributes syntax payload, never the state contents.
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

fn charge_bitvector(term: &MachineTerm) -> bool {
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

/// Charges a 32-bit order premise, signed or `uint32`, and refuses any other
/// premise.
fn charge_signed_bound(proposition: &Proposition) -> bool {
    // A native 8- or 16-bit order is the same fact as the `int32` order of
    // its widenings (rule K8), which the bound context files with it.
    let Proposition::ConditionIs(
        ConditionTerm::Compare {
            format:
                MachineIntegerType::Int32
                | MachineIntegerType::UInt32
                | MachineIntegerType::Int8
                | MachineIntegerType::UInt8
                | MachineIntegerType::Int16
                | MachineIntegerType::UInt16,
            relation:
                CompareRelation::LessThan
                | CompareRelation::LessEqual
                | CompareRelation::GreaterThan
                | CompareRelation::GreaterEqual,
            left,
            right,
        },
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
        | (PointerBlock::Heap(_), PointerBlock::Heap(_))
        | (PointerBlock::Temporary(_), PointerBlock::Temporary(_)) => left == right,
        _ => false,
    }
}

fn pointer_index_equal(
    left: crate::kernel::MachineOperandView<'_>,
    right: crate::kernel::MachineOperandView<'_>,
) -> bool {
    if !pointer_index_payload(left).is_some_and(charge_payload)
        || !pointer_index_payload(right).is_some_and(charge_payload)
    {
        return false;
    }
    let mut pending = vec![(left, right)];
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
            if !legacy_bitvector_equal_after_payload_check(&a, &b) {
                return false;
            }
        } else if let (Some((af, ao, [al, ar])), Some((bf, bo, [bl, br]))) =
            (left.binary(), right.binary())
        {
            if (af, ao) != (bf, bo) || !operand_identity::binary_supported(af, ao) {
                return false;
            }
            pending.push((al, bl));
            pending.push((ar, br));
        } else if let (Some((ae, af, at, av)), Some((be, bf, bt, bv))) = (left.cast(), right.cast())
        {
            if (ae, af, at) != (be, bf, bt) {
                return false;
            }
            pending.push((av, bv));
        } else {
            return false;
        }
    }
    true
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
                if !pointer_index_equal(left.operand_view(), right.operand_view()) {
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
                if !pointer_index_equal(left.operand_view(), right.operand_view()) {
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

mod operand_identity;

/// Compare only the bounded structural fragment accepted by `bitvector_payload`.
/// This avoids recursive equality on attacker-controlled expression depth after
/// the payload has already been charged.
fn bitvector_equal(left: &MachineTerm, right: &MachineTerm) -> bool {
    operand_identity::equal(
        crate::kernel::MachineOperandView::Legacy(left),
        crate::kernel::MachineOperandView::Legacy(right),
    )
}

fn legacy_bitvector_equal(left: &MachineTerm, right: &MachineTerm) -> bool {
    if !charge_bitvector(left) || !charge_bitvector(right) {
        return false;
    }
    legacy_bitvector_equal_after_payload_check(left, right)
}

fn legacy_bitvector_equal_after_payload_check(left: &MachineTerm, right: &MachineTerm) -> bool {
    let mut pending = vec![(left, right)];
    while let Some((left, right)) = pending.pop() {
        match (left, right) {
            (cast_term!(Int64FromUInt32, left), cast_term!(Int64FromUInt32, right))
            | (cast_term!(UInt64From32, left), cast_term!(UInt64From32, right))
            | (cast_term!(UInt32From64, left), cast_term!(UInt32From64, right)) => {
                pending.push((left, right));
            }
            (bits32_constant!(left), bits32_constant!(right)) => {
                if constant_u32(*left) != constant_u32(*right) {
                    return false;
                }
            }
            (int64_constant!(left), int64_constant!(right)) => {
                if constant_i64(*left) != constant_i64(*right) {
                    return false;
                }
            }
            (uint64_constant!(left), uint64_constant!(right)) => {
                if constant_u64(*left) != constant_u64(*right) {
                    return false;
                }
            }
            (MachineTerm::Variable(left), MachineTerm::Variable(right)) => {
                if left != right {
                    return false;
                }
            }
            (MachineTerm::MemoryLoad(lm, lp, lk), MachineTerm::MemoryLoad(rm, rp, rk)) => {
                if lm != rm || lk != rk || !pointer_equal(lp, rp) {
                    return false;
                }
            }
            (native_constant!(left_format, left), native_constant!(right_format, right)) => {
                if (left_format, left) != (right_format, right) {
                    return false;
                }
            }
            (
                MachineTerm::IntegerToMachine {
                    value: left,
                    destination: left_destination,
                },
                MachineTerm::IntegerToMachine {
                    value: right,
                    destination: right_destination,
                },
            ) => {
                if left_destination != right_destination || left != right {
                    return false;
                }
            }
            (
                MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    value: left,
                    from: left_source,
                    to: left_destination,
                },
                MachineTerm::Cast {
                    spelling: MachineCastSpelling::Generic,
                    value: right,
                    from: right_source,
                    to: right_destination,
                },
            ) => {
                if left_source != right_source || left_destination != right_destination {
                    return false;
                }
                pending.push((left, right));
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
            (MachineTerm::PointerAddress(left, _), MachineTerm::PointerAddress(right, _)) => {
                if !pointer_equal(left, right) {
                    return false;
                }
            }
            _ => {
                use crate::kernel::BitvectorBinaryOp as Op;
                let (
                    Some((operator, left_first, left_second)),
                    Some((other, right_first, right_second)),
                ) = (left.as_binary(), right.as_binary())
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
                        crate::kernel::MachineBinaryOp::BitwiseAnd
                    ) | Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::BitwiseOr
                    ) | Op::Machine(
                        crate::kernel::MachineIntegerType::Int32,
                        crate::kernel::MachineBinaryOp::BitwiseXor
                    ) | Op::Machine(MachineIntegerType::Int64, MachineBinaryOp::Add)
                        | Op::Machine(
                            MachineIntegerType::UInt64,
                            MachineBinaryOp::Add
                                | MachineBinaryOp::Subtract
                                | MachineBinaryOp::Multiply
                                | MachineBinaryOp::Divide
                                | MachineBinaryOp::Remainder
                                | MachineBinaryOp::BitwiseAnd
                                | MachineBinaryOp::BitwiseOr
                        )
                        | Op::Float32(_)
                        | Op::Float64(_)
                );
                if operator != other || !compared {
                    return false;
                }
                pending.push((left_first, right_first));
                pending.push((left_second, right_second));
            }
        }
    }
    true
}

/// Recognize the kernel's alignment proposition only after its complete
/// bitvector payload has been walked and charged.  `as_pointer_alignment`
/// uses the convenience `uint64_as_const` recognizer, whose implementation is
/// recursive for constant expressions; keeping it behind this bounded walk
/// makes attacker-controlled depth fail before that helper is reached.
pub(crate) fn checked_pointer_alignment(condition: &ConditionTerm) -> Option<(&Pointer, u64)> {
    match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::Int64,
            relation: CompareRelation::Equal,
            left,
            right,
        } => {
            if !charge_bitvector(left) || !charge_bitvector(right) {
                return None;
            }
        }
        ConditionTerm::IntegerEqual(left, right) => {
            for side in [left, right] {
                match side.as_ref() {
                    IntegerTerm::Machine(word) if word_view::charge(Word(word.operand_view())) => {}
                    IntegerTerm::Constant(_) => {}
                    _ => return None,
                }
            }
        }
        _ => return None,
    }
    condition.as_pointer_alignment()
}

/// [`condition_identity_as_written`] at fact identity. An Integer
/// comparison of exact observations reads as its native comparison
/// (`native_comparison_view`), so a conclusion and a goal
/// that spell one fact in the two sorts match. Two comparisons at an 8- or
/// 16-bit identity compare by [`ConditionTerm::comparison_fact`], which
/// reads a native comparison and the `int32` comparison of its widenings as
/// one fact (rule K8). Root matches and the charged side comparisons.
fn condition_identity(left: &ConditionTerm, right: &ConditionTerm) -> bool {
    operand_identity::condition_equal(left, right)
}

fn condition_identity_native(left: &ConditionTerm, right: &ConditionTerm) -> bool {
    if let (Some(left_fact), Some(right_fact)) = (left.comparison_fact(), right.comparison_fact())
        && (left_fact.0.format().bits() < 32 || right_fact.0.format().bits() < 32)
    {
        let side = |left: crate::kernel::primitives::ComparisonSide<'_>,
                    right: crate::kernel::primitives::ComparisonSide<'_>| {
            use crate::kernel::primitives::ComparisonSide as S;
            match (left, right) {
                (S::Term(left), S::Term(right)) => {
                    charge_bitvector(left)
                        && charge_bitvector(right)
                        && bitvector_equal(left, right)
                }
                (left, right) => left == right,
            }
        };
        return left_fact.0 == right_fact.0
            && left_fact.1 == right_fact.1
            && side(left_fact.2, right_fact.2)
            && side(left_fact.3, right_fact.3);
    }
    condition_identity_as_written(left, right)
}

fn condition_identity_as_written(left: &ConditionTerm, right: &ConditionTerm) -> bool {
    match (left, right) {
        (ConditionTerm::PointerValueEqual(a, b), ConditionTerm::PointerValueEqual(c, d)) => {
            charge_pointer(a.pointer())
                && charge_pointer(b.pointer())
                && charge_pointer(c.pointer())
                && charge_pointer(d.pointer())
                && a == c
                && b == d
        }
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
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                relation: CompareRelation::Equal,
                left: right_first,
                right: right_second,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: right_first,
                right: right_second,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: right_first,
                right: right_second,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: right_first,
                right: right_second,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left: right_first,
                right: right_second,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left: right_first,
                right: right_second,
            },
        )
        | (
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left: right_first,
                right: right_second,
            },
        ) => {
            charge_bitvector(left_first)
                && charge_bitvector(left_second)
                && charge_bitvector(right_first)
                && charge_bitvector(right_second)
                && bitvector_equal(left_first, right_first)
                && bitvector_equal(left_second, right_second)
        }
        (
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation:
                    left_relation @ (crate::kernel::CompareRelation::LessThan
                    | crate::kernel::CompareRelation::LessEqual
                    | crate::kernel::CompareRelation::GreaterThan
                    | crate::kernel::CompareRelation::GreaterEqual),
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation:
                    right_relation @ (crate::kernel::CompareRelation::LessThan
                    | crate::kernel::CompareRelation::LessEqual
                    | crate::kernel::CompareRelation::GreaterThan
                    | crate::kernel::CompareRelation::GreaterEqual),
                left: right_first,
                right: right_second,
            },
        ) if left_relation == right_relation => {
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
        // An `int32` or `int64` definedness claim names arbitrary operand
        // terms (loads, state values, widenings). Both sides were lowered
        // from the certificate's own explicit text and the goal, so the
        // structural comparison is linear in that input.
        (
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: right_first,
                right: right_second,
            },
        )
        | (
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Subtract,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Subtract,
                left: right_first,
                right: right_second,
            },
        )
        | (
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Add,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Add,
                left: right_first,
                right: right_second,
            },
        )
        | (
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Subtract,
                left: left_first,
                right: left_second,
            },
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Subtract,
                left: right_first,
                right: right_second,
            },
        ) => left_first == right_first && left_second == right_second,
        (
            ConditionTerm::IntegerEqual(left_first, left_second),
            ConditionTerm::IntegerEqual(right_first, right_second),
        )
        | (
            ConditionTerm::IntegerNotEqual(left_first, left_second),
            ConditionTerm::IntegerNotEqual(right_first, right_second),
        )
        | (
            ConditionTerm::IntegerLessEqual(left_first, left_second),
            ConditionTerm::IntegerLessEqual(right_first, right_second),
        )
        | (
            ConditionTerm::IntegerGreaterEqual(left_first, left_second),
            ConditionTerm::IntegerGreaterEqual(right_first, right_second),
        ) => left_first == right_first && left_second == right_second,
        _ => false,
    }
}

fn float_condition_identity(left: &FloatCondition, right: &FloatCondition) -> bool {
    match (left, right) {
        (
            FloatCondition::Comparison {
                operator: left_operator,
                left: left_first,
                right: left_second,
            },
            FloatCondition::Comparison {
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
            FloatCondition::Classification {
                classification: left_classification,
                value: left_value,
            },
            FloatCondition::Classification {
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
/// A conjunction, such as a `defined(..)` result that carries its operands'
/// own definedness, compares conjunct by conjunct; a conjunct that is not a
/// condition compares by its exact fact identity key.
fn proposition_identity(left: &Proposition, right: &Proposition) -> bool {
    match (left, right) {
        (
            Proposition::ConditionIs(left_condition, left_expected),
            Proposition::ConditionIs(right_condition, right_expected),
        ) => left_expected == right_expected && condition_identity(left_condition, right_condition),
        (Proposition::And(_, _), Proposition::And(_, _)) => {
            let (left, right) = (conjunct_list(left), conjunct_list(right));
            left.len() == right.len()
                && left
                    .iter()
                    .zip(&right)
                    .all(|(left, right)| match (left, right) {
                        (Proposition::ConditionIs(_, _), _) | (_, Proposition::ConditionIs(_, _)) => {
                            proposition_identity(left, right)
                        }
                        _ => {
                            let key = crate::kernel::proof::fact_keys::proposition_identity_key;
                            matches!((key(left), key(right)), (Some(left), Some(right)) if left == right)
                        }
                    })
        }
        _ => false,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) enum SpecialArithmeticNode {
    /// Bound an exact mathematical product using four explicit constant
    /// endpoint bounds: left lower/upper, then right lower/upper.
    IntegerProductBounds {
        bounds: Vec<usize>,
        result: Proposition,
    },
    IntegerDivisionBounds {
        bounds: Vec<usize>,
        result: Proposition,
    },
    IntegerMultiplyOrder {
        bounds: Vec<usize>,
        result: Proposition,
    },
    IntegerQuotientBound {
        bounds: Vec<usize>,
        result: Proposition,
    },
    IntegerBoundExclusion {
        bounds: Vec<usize>,
        result: Proposition,
    },
    IntegerRelationTransport {
        bounds: Vec<usize>,
        result: Proposition,
    },
    IntegerPolynomialIdentity {
        bounds: Vec<usize>,
        result: Proposition,
    },
    IntegerQuotientShift {
        bounds: Vec<usize>,
        result: Proposition,
    },
    IntegerCastIdentity {
        bounds: Vec<usize>,
        result: Proposition,
    },
    IntegerOperationIdentity {
        bounds: Vec<usize>,
        result: Proposition,
    },
    UnsignedSumBound {
        bounds: Vec<usize>,
        result: Proposition,
    },
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
    /// Establish a tagged pointer-word equality directly from exact
    /// alignment facts.  Unlike `PointerWordEquality`, this rule is for a
    /// word expression produced by the current execution rather than an
    /// explicitly recorded word-equality relation.
    PointerWordFromAlignment {
        alignments: Vec<usize>,
        result: Proposition,
    },
    /// Prove a reflexive IEEE comparison from one exact finite classification.
    FloatReflexive { finite: usize, result: Proposition },
    /// Establish `defined(left + right)` or `defined(left - right)` over
    /// `width` (`int32` or `int64`) from each operand's range: the width
    /// range of its root constructor (a constant, or for `int64` a value
    /// widened from 32 bits), narrowed by the listed premises. Each listed
    /// premise is a constant order or equality fact of that width on one
    /// operand; the checker reads it directly, so its work is one lookup per
    /// listed bound and never a context scan.
    SignedDefined {
        width: SignedDefinedWidth,
        bounds: Vec<usize>,
        result: Proposition,
    },
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(crate) struct SpecialArithmeticCertificate {
    pub(crate) nodes: Vec<SpecialArithmeticNode>,
    pub(crate) conclusion: usize,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum SpecialArithmeticCheckError {
    InvalidIntegerProductBounds(usize),
    InvalidIntegerDivisionBounds(usize),
    InvalidIntegerMultiplyOrder(usize),
    InvalidIntegerQuotientBound(usize),
    InvalidIntegerBoundExclusion(usize),
    InvalidIntegerRelationTransport(usize),
    InvalidIntegerPolynomialIdentity(usize),
    IntegerPolynomialLimitExceeded,
    InvalidIntegerQuotientShift(usize),
    InvalidIntegerCastIdentity(usize),
    InvalidIntegerOperationIdentity(usize),
    InvalidPremise(usize),
    InvalidNodeReference(usize),
    InvalidOperator(usize),
    NodeResultMismatch(usize),
    WorkLimitExceeded,
    DoesNotFollow,
    /// Listed premise `premise` of node `node` is not a constant order or
    /// equality fact of the node's width on an operand of the claimed
    /// operation.
    SignedDefinedBoundUnrelated {
        node: usize,
        width: SignedDefinedWidth,
        premise: usize,
    },
    /// The operand ranges node `node` establishes put the exact result in
    /// `[lower, upper]`, which leaves the node's width.
    SignedDefinedRangeExceeded {
        node: usize,
        width: SignedDefinedWidth,
        lower: i128,
        upper: i128,
    },
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
            SpecialArithmeticNode::IntegerProductBounds { bounds, result } => integer_rule(
                index,
                bounds,
                premises,
                result,
                super::integer_product_bounds::check,
            ),
            SpecialArithmeticNode::IntegerDivisionBounds { bounds, result } => integer_rule(
                index,
                bounds,
                premises,
                result,
                super::integer_division_bounds::check,
            ),
            SpecialArithmeticNode::IntegerMultiplyOrder { bounds, result } => integer_rule(
                index,
                bounds,
                premises,
                result,
                super::integer_multiply_order::check,
            ),
            SpecialArithmeticNode::IntegerQuotientBound { bounds, result } => integer_rule(
                index,
                bounds,
                premises,
                result,
                super::integer_quotient_bound::check,
            ),
            SpecialArithmeticNode::IntegerBoundExclusion { bounds, result } => integer_rule(
                index,
                bounds,
                premises,
                result,
                super::integer_bound_exclusion::check,
            ),
            SpecialArithmeticNode::IntegerRelationTransport { bounds, result } => integer_rule(
                index,
                bounds,
                premises,
                result,
                super::integer_relation_transport::check,
            ),
            SpecialArithmeticNode::IntegerPolynomialIdentity { bounds, result } => integer_rule(
                index,
                bounds,
                premises,
                result,
                super::integer_polynomial_identity::check,
            ),
            SpecialArithmeticNode::IntegerQuotientShift { bounds, result } => integer_rule(
                index,
                bounds,
                premises,
                result,
                super::integer_quotient_shift::check,
            ),
            SpecialArithmeticNode::IntegerCastIdentity { bounds, result } => integer_rule(
                index,
                bounds,
                premises,
                result,
                super::integer_cast_identity::check,
            ),
            SpecialArithmeticNode::IntegerOperationIdentity { bounds, result } => integer_rule(
                index,
                bounds,
                premises,
                result,
                super::integer_operation_identity::check,
            ),
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
                let mut seen_bounds = HashSet::new();
                if bounds.iter().any(|bound| !seen_bounds.insert(*bound)) {
                    return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
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
                let accepted =
                    pointer_translation(relation_proposition, &bound_propositions, result);
                if !accepted {
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
                let mut seen_alignments = HashSet::new();
                if alignments
                    .iter()
                    .any(|alignment| !seen_alignments.insert(*alignment))
                {
                    return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
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
            SpecialArithmeticNode::PointerWordFromAlignment { alignments, result } => {
                if crate::instrumentation::deadline_exceeded_with_work(
                    alignments.len().saturating_add(1),
                ) {
                    return Err(SpecialArithmeticCheckError::WorkLimitExceeded);
                }
                let mut seen = HashSet::new();
                if alignments.is_empty() || alignments.iter().any(|index| !seen.insert(*index)) {
                    return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                }
                let alignment_propositions = alignments
                    .iter()
                    .map(|index| {
                        premises
                            .get(*index)
                            .ok_or(SpecialArithmeticCheckError::InvalidPremise(*index))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if !pointer_word_from_alignment(&alignment_propositions, result) {
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
            SpecialArithmeticNode::UnsignedSumBound { bounds, result } => {
                let Proposition::ConditionIs(condition, value) = result else {
                    return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                };
                let ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::LessEqual,
                    left,
                    right,
                } = condition
                else {
                    return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                };
                if !charge_bitvector(left) || !charge_bitvector(right) {
                    return Err(SpecialArithmeticCheckError::WorkLimitExceeded);
                }
                let mut context = crate::kernel::PureFactContext::new();
                let mut seen = HashSet::new();
                for bound in bounds {
                    if !seen.insert(*bound) {
                        return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                    }
                    let premise = premises
                        .get(*bound)
                        .ok_or(SpecialArithmeticCheckError::InvalidPremise(*bound))?;
                    if !charge_signed_bound(premise) {
                        return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                    }
                    context = context.assume_proposition(premise.clone());
                }
                if context.decide_widened_sum_bound(condition) != Some(*value) {
                    return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                }
                Ok(())
            }
            SpecialArithmeticNode::SignedDefined {
                width,
                bounds,
                result,
            } => {
                if crate::instrumentation::deadline_exceeded_with_work(
                    bounds.len().saturating_add(1),
                ) {
                    return Err(SpecialArithmeticCheckError::WorkLimitExceeded);
                }
                let mut seen = HashSet::new();
                if bounds.iter().any(|bound| !seen.insert(*bound)) {
                    return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
                }
                let bounds = bounds
                    .iter()
                    .map(|bound| {
                        premises
                            .get(*bound)
                            .map(|premise| (*bound, premise))
                            .ok_or(SpecialArithmeticCheckError::InvalidPremise(*bound))
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                signed_defined(index, *width, &bounds, result)
            }
        }
    }
}

/// The operation a `defined` claim over `int32` or `int64` addition or
/// subtraction names: its width, its two operands, and whether it subtracts.
pub(crate) fn signed_definedness_operands(
    proposition: &Proposition,
) -> Option<(SignedDefinedWidth, &MachineTerm, &MachineTerm, bool)> {
    let Proposition::ConditionIs(condition, false) = proposition else {
        return None;
    };
    match condition {
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Add,
            left,
            right,
        } => Some((SignedDefinedWidth::Int32, left, right, false)),
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int32,
            op: OverflowOperation::Subtract,
            left,
            right,
        } => Some((SignedDefinedWidth::Int32, left, right, true)),
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Add,
            left,
            right,
        } => Some((SignedDefinedWidth::Int64, left, right, false)),
        ConditionTerm::Overflows {
            format: MachineIntegerType::Int64,
            op: OverflowOperation::Subtract,
            left,
            right,
        } => Some((SignedDefinedWidth::Int64, left, right, true)),
        _ => None,
    }
}

/// The signed value of `term` when it is a constant of `width`.
pub(crate) fn signed_width_constant(width: SignedDefinedWidth, term: &MachineTerm) -> Option<i64> {
    match width {
        SignedDefinedWidth::Int32 => term.as_const().map(|bits| i64::from(bits as i32)),
        SignedDefinedWidth::Int64 => term.int64_as_const(),
    }
}

/// The range a term of `width` has from its root constructor alone. An
/// `int32` term has no narrower root constructor (`char` and `short` values
/// share the 32-bit term unchanged), so only a constant narrows it.
fn signed_width_interval(
    width: SignedDefinedWidth,
    term: crate::kernel::MachineOperandView<'_>,
) -> (i64, i64) {
    match width {
        SignedDefinedWidth::Int32 => signed_width_constant_view(width, term)
            .map_or_else(|| width.range(), |value| (value, value)),
        SignedDefinedWidth::Int64 => term.int64_width_interval().unwrap_or(width.range()),
    }
}

fn signed_width_constant_view(
    width: SignedDefinedWidth,
    term: crate::kernel::MachineOperandView<'_>,
) -> Option<i64> {
    match width {
        SignedDefinedWidth::Int32 => term.word32_constant().map(|bits| i64::from(bits as i32)),
        SignedDefinedWidth::Int64 => term.int64_constant(),
    }
}

/// What one explicitly supplied constant fact says about an operand.
/// The source fact remains the witness; matching reads only its two endpoints.
pub(crate) fn signed_constant_bound_on_view(
    width: SignedDefinedWidth,
    premise: &Proposition,
    term: crate::kernel::MachineOperandView<'_>,
) -> Option<(Option<i64>, Option<i64>)> {
    let format = match width {
        SignedDefinedWidth::Int32 => MachineIntegerType::Int32,
        SignedDefinedWidth::Int64 => MachineIntegerType::Int64,
    };
    let key = crate::kernel::equality_graph::MachineAtom::from_operand(format, term);
    signed_constant_bound_on_key(width, premise, &key)
}

fn signed_constant_bound_on_key(
    width: SignedDefinedWidth,
    premise: &Proposition,
    key: &crate::kernel::equality_graph::MachineAtom,
) -> Option<(Option<i64>, Option<i64>)> {
    use crate::kernel::equality_graph::MachineAtom;
    use crate::kernel::machine_integer::{Relation, comparison::comparison_view};
    let Proposition::ConditionIs(condition, value) = premise else {
        return None;
    };
    let view = comparison_view(condition, *value)?;
    let format = match width {
        SignedDefinedWidth::Int32 => MachineIntegerType::Int32,
        SignedDefinedWidth::Int64 => MachineIntegerType::Int64,
    };
    if view.format != format
        && !(format == MachineIntegerType::Int32
            && view.format == MachineIntegerType::UInt32
            && view.relation == Relation::Equal)
    {
        return None;
    }
    let [left, right] =
        [&view.operands[0], &view.operands[1]].map(|operand| operand.operand_view());
    let same = |operand| &MachineAtom::from_operand(format, operand) == key;
    if view.relation == Relation::Equal {
        let constant = if same(left) {
            signed_width_constant_view(width, right)?
        } else if same(right) {
            signed_width_constant_view(width, left)?
        } else {
            return None;
        };
        return Some((Some(constant), Some(constant)));
    }
    let strict = match view.relation {
        Relation::Less => true,
        Relation::LessEqual => false,
        _ => return None,
    };
    let step = i64::from(strict);
    let (minimum, maximum) = width.range();
    if same(left)
        && let Some(constant) = signed_width_constant_view(width, right)
    {
        let bound = constant
            .checked_sub(step)
            .filter(|bound| *bound >= minimum)?;
        return Some((None, Some(bound)));
    }
    if same(right)
        && let Some(constant) = signed_width_constant_view(width, left)
    {
        let bound = constant
            .checked_add(step)
            .filter(|bound| *bound <= maximum)?;
        return Some((Some(bound), None));
    }
    None
}

/// The range `term` has from its width and the listed bounds on it.
/// The operation a `defined(a + b)` or `defined(a - b)` result checks. A
/// result whose operands carry definedness of their own, such as a read
/// through a resource view or an inner sum, lowers to a conjunction: its
/// operation is the one overflow conjunct no other conjunct takes as an
/// operand, and every other conjunct must be a conjunct of a cited premise,
/// which marks that premise used.
pub(crate) type SignedDefinedOperation<'a> = (
    SignedDefinedWidth,
    [crate::kernel::machine_integer::comparison::ComparisonOperand<'a>; 2],
    bool,
);

enum IntervalLeaf<'a> {
    Written(&'a Proposition),
    Arithmetic(crate::kernel::machine_integer::definedness::OverflowQueryView),
}

#[derive(Clone, PartialEq, Eq, Hash)]
enum IntervalLeafKey<'a> {
    Written(&'a Proposition),
    Arithmetic(
        MachineIntegerType,
        OverflowOperation,
        [crate::kernel::equality_graph::MachineAtom; 2],
    ),
}

impl<'a> IntervalLeaf<'a> {
    fn key(&self) -> IntervalLeafKey<'a> {
        use crate::kernel::MachineOperandView as V;
        use crate::kernel::equality_graph::MachineAtom;
        match self {
            Self::Arithmetic(query) => IntervalLeafKey::Arithmetic(
                query.format,
                match query.operation {
                    crate::kernel::machine_integer::Operation::Add => OverflowOperation::Add,
                    crate::kernel::machine_integer::Operation::Subtract => {
                        OverflowOperation::Subtract
                    }
                    crate::kernel::machine_integer::Operation::Multiply => {
                        OverflowOperation::Multiply
                    }
                },
                [&query.operands[0], &query.operands[1]]
                    .map(|operand| MachineAtom::from_operand(query.format, operand.operand_view())),
            ),
            Self::Written(Proposition::ConditionIs(
                ConditionTerm::Overflows {
                    format,
                    op,
                    left,
                    right,
                },
                false,
            )) => IntervalLeafKey::Arithmetic(
                *format,
                *op,
                [
                    MachineAtom::from_operand(*format, V::Legacy(left)),
                    MachineAtom::from_operand(*format, V::Legacy(right)),
                ],
            ),
            Self::Written(proposition) => IntervalLeafKey::Written(proposition),
        }
    }

    fn operation(&self) -> Option<SignedDefinedOperation<'a>> {
        use crate::kernel::machine_integer::{Operation, comparison::ComparisonOperand};
        match self {
            Self::Arithmetic(query) => {
                let width = match query.format {
                    MachineIntegerType::Int32 => SignedDefinedWidth::Int32,
                    MachineIntegerType::Int64 => SignedDefinedWidth::Int64,
                    _ => return None,
                };
                let subtract = match query.operation {
                    Operation::Add => false,
                    Operation::Subtract => true,
                    Operation::Multiply => return None,
                };
                Some((width, query.operands.clone(), subtract))
            }
            Self::Written(proposition) => {
                let (width, left, right, subtract) = signed_definedness_operands(proposition)?;
                Some((
                    width,
                    [
                        ComparisonOperand::Written(left),
                        ComparisonOperand::Written(right),
                    ],
                    subtract,
                ))
            }
        }
    }
}

/// Read one complete signed addition/subtraction domain without constructing
/// an overflow proposition or exporting its shared operands. Compound domains
/// remain the responsibility of the certificate's outer-operation selection.
pub(crate) fn signed_definedness_query(
    proposition: &Proposition,
) -> Option<SignedDefinedOperation<'_>> {
    if let Some(query) =
        crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(proposition)
    {
        IntervalLeaf::Arithmetic(query).operation()
    } else {
        IntervalLeaf::Written(proposition).operation()
    }
}

fn interval_leaves(proposition: &Proposition) -> Vec<IntervalLeaf<'_>> {
    let mut result = Vec::new();
    let mut pending = vec![proposition];
    while let Some(next) = pending.pop() {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(query) =
            crate::kernel::machine_integer::definedness::ordinary_arithmetic_guard_view(next)
        {
            result.push(IntervalLeaf::Arithmetic(query));
        } else if let Proposition::And(left, right) = next {
            pending.push(right);
            pending.push(left);
        } else {
            result.push(IntervalLeaf::Written(next));
        }
    }
    result
}

fn signed_defined_operation<'r>(
    result: &'r Proposition,
    bounds: &[(usize, &Proposition)],
    used: &mut [bool],
) -> Option<SignedDefinedOperation<'r>> {
    use crate::kernel::MachineBinaryOp;
    use crate::kernel::equality_graph::MachineAtom;
    let conjuncts = interval_leaves(result);
    if conjuncts.len() == 1 {
        return conjuncts[0].operation();
    }
    let operations = conjuncts
        .iter()
        .map(IntervalLeaf::operation)
        .collect::<Vec<_>>();
    // The established conjunction rule matches an int32 operation root.
    // Index only the two operands explicitly named by each operation; there
    // is no pairwise scan or construction of a boxed candidate expression.
    let mut operand_operations = std::collections::HashSet::new();
    for (_, operands, _) in operations.iter().flatten() {
        for operand in operands {
            if let Some((MachineIntegerType::Int32, op, children)) = operand.operand_view().binary()
            {
                operand_operations.insert((
                    op,
                    children
                        .map(|child| MachineAtom::from_operand(MachineIntegerType::Int32, child)),
                ));
            }
        }
    }
    let mut outermost = operations
        .iter()
        .enumerate()
        .filter_map(|(position, operation)| {
            let (_, operands, subtract) = operation.as_ref()?;
            let key = (
                if *subtract {
                    MachineBinaryOp::Subtract
                } else {
                    MachineBinaryOp::Add
                },
                [&operands[0], &operands[1]].map(|operand| {
                    MachineAtom::from_operand(MachineIntegerType::Int32, operand.operand_view())
                }),
            );
            (!operand_operations.contains(&key)).then_some(position)
        });
    let chosen = outermost.next()?;
    if outermost.next().is_some() {
        return None;
    }
    let mut premise_conjuncts = std::collections::HashMap::<_, Vec<usize>>::new();
    for (position, (_, premise)) in bounds.iter().enumerate() {
        for conjunct in conjunct_list(premise) {
            crate::instrumentation::record_deterministic_work(1);
            premise_conjuncts
                .entry(IntervalLeaf::Written(conjunct).key())
                .or_default()
                .push(position);
        }
    }
    let mut seen = std::collections::HashSet::new();
    for (position, conjunct) in conjuncts.iter().enumerate() {
        if position == chosen {
            continue;
        }
        let key = conjunct.key();
        if !seen.insert(key.clone()) {
            continue;
        }
        for premise in premise_conjuncts.get(&key)? {
            crate::instrumentation::record_deterministic_work(1);
            used[*premise] = true;
        }
    }
    operations[chosen].clone()
}

fn conjunct_list(proposition: &Proposition) -> Vec<&Proposition> {
    let mut conjuncts = Vec::new();
    let mut pending = vec![proposition];
    while let Some(next) = pending.pop() {
        match next {
            Proposition::And(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            other => conjuncts.push(other),
        }
    }
    conjuncts
}

fn signed_operand_range(
    width: SignedDefinedWidth,
    term: crate::kernel::MachineOperandView<'_>,
    bounds: &[(usize, &Proposition)],
    used: &mut [bool],
) -> (i64, i64) {
    let (mut lower, mut upper) = signed_width_interval(width, term);
    let format = match width {
        SignedDefinedWidth::Int32 => MachineIntegerType::Int32,
        SignedDefinedWidth::Int64 => MachineIntegerType::Int64,
    };
    let key = crate::kernel::equality_graph::MachineAtom::from_operand(format, term);
    for (position, (_, premise)) in bounds.iter().enumerate() {
        if let Some((bound_lower, bound_upper)) = signed_constant_bound_on_key(width, premise, &key)
        {
            used[position] = true;
            if let Some(value) = bound_lower {
                lower = lower.max(value);
            }
            if let Some(value) = bound_upper {
                upper = upper.min(value);
            }
        }
    }
    (lower, upper)
}

/// The exact result range of `left + right` or `left - right` over the two
/// operand ranges, computed without overflow.
pub(crate) fn signed_result_range(
    left: (i64, i64),
    right: (i64, i64),
    subtract: bool,
) -> (i128, i128) {
    if subtract {
        (
            i128::from(left.0) - i128::from(right.1),
            i128::from(left.1) - i128::from(right.0),
        )
    } else {
        (
            i128::from(left.0) + i128::from(right.0),
            i128::from(left.1) + i128::from(right.1),
        )
    }
}

fn signed_defined(
    index: usize,
    width: SignedDefinedWidth,
    bounds: &[(usize, &Proposition)],
    result: &Proposition,
) -> Result<(), SpecialArithmeticCheckError> {
    let mut used = vec![false; bounds.len()];
    let (claimed, operands, subtract) = signed_defined_operation(result, bounds, &mut used)
        .ok_or(SpecialArithmeticCheckError::NodeResultMismatch(index))?;
    // The node's spelling names the width; it must be the claim's own.
    if claimed != width {
        return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
    }
    let left_range = signed_operand_range(width, operands[0].operand_view(), bounds, &mut used);
    let right_range = signed_operand_range(width, operands[1].operand_view(), bounds, &mut used);
    if let Some(position) = used.iter().position(|used| !used) {
        return Err(SpecialArithmeticCheckError::SignedDefinedBoundUnrelated {
            node: index,
            width,
            premise: bounds[position].0,
        });
    }
    // Contradictory bounds leave an operand without a value; this rule
    // does not conclude from them.
    if left_range.0 > left_range.1 || right_range.0 > right_range.1 {
        return Err(SpecialArithmeticCheckError::NodeResultMismatch(index));
    }
    let (lower, upper) = signed_result_range(left_range, right_range, subtract);
    let (minimum, maximum) = width.range();
    if lower < i128::from(minimum) || upper > i128::from(maximum) {
        return Err(SpecialArithmeticCheckError::SignedDefinedRangeExceeded {
            node: index,
            width,
            lower,
            upper,
        });
    }
    Ok(())
}

impl SpecialArithmeticNode {
    fn result(&self) -> &Proposition {
        match self {
            Self::UnsignedSumBound { result, .. }
            | Self::IntegerProductBounds { result, .. }
            | Self::IntegerDivisionBounds { result, .. }
            | Self::IntegerMultiplyOrder { result, .. }
            | Self::IntegerQuotientBound { result, .. }
            | Self::IntegerBoundExclusion { result, .. }
            | Self::IntegerRelationTransport { result, .. }
            | Self::IntegerPolynomialIdentity { result, .. }
            | Self::IntegerQuotientShift { result, .. }
            | Self::IntegerCastIdentity { result, .. }
            | Self::IntegerOperationIdentity { result, .. }
            | Self::PointerTranslation { result, .. }
            | Self::PointerAlignment { result, .. }
            | Self::PointerWordEquality { result, .. }
            | Self::PointerWordFromAlignment { result, .. }
            | Self::FloatReflexive { result, .. }
            | Self::SignedDefined { result, .. } => result,
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
        Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) => Some((
            &left.offset,
            &right.offset,
            Some((&left.block, &right.block)),
        )),
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

fn scalar(value: &MachineTerm) -> Option<i64> {
    value.as_const().map(|value| i64::from(value as i32))
}

fn scalar_bounds(premises: &[&Proposition]) -> Option<BTreeMap<MachineTerm, (i64, i64)>> {
    let mut bounds = BTreeMap::new();
    for premise in premises {
        if !charge_signed_bound(premise) {
            return None;
        }
        let Proposition::ConditionIs(condition, true) = premise else {
            return None;
        };
        let (left, right, strict) = match condition {
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left,
                right,
            } => (left.as_ref(), right.as_ref(), true),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left,
                right,
            } => (left.as_ref(), right.as_ref(), false),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterThan,
                left,
                right,
            } => (right.as_ref(), left.as_ref(), true),
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::GreaterEqual,
                left,
                right,
            } => (right.as_ref(), left.as_ref(), false),
            // A `uint32` order bounds no signed word.
            ConditionTerm::Compare {
                format: MachineIntegerType::UInt32,
                relation:
                    CompareRelation::LessThan
                    | CompareRelation::LessEqual
                    | CompareRelation::GreaterThan
                    | CompareRelation::GreaterEqual,
                ..
            } => continue,
            _ => return None,
        };
        // These bounds are over signed words. A native-width or floating
        // operation cannot supply a signed-word interval merely by being
        // embedded in a syntactically signed comparison.
        if super::signed_arithmetic::SignedArithmeticAtom::from_term(left).is_none()
            || super::signed_arithmetic::SignedArithmeticAtom::from_term(right).is_none()
        {
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

/// The two sides of an unsigned 64-bit order premise, lower side first,
/// and whether the order is strict.
fn unsigned64_order(proposition: &Proposition) -> Option<(&MachineTerm, &MachineTerm, bool)> {
    let Proposition::ConditionIs(condition, true) = proposition else {
        return None;
    };
    Some(match condition {
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessThan,
            left,
            right,
        } => (left, right, true),
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } => (left, right, false),
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => (right, left, true),
        ConditionTerm::Compare {
            format: MachineIntegerType::UInt64,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => (right, left, false),
        _ => return None,
    })
}

/// The interval each cited unsigned 64-bit order premise gives its
/// non-constant side. A strict order between two symbolic values keeps the
/// lower one below the type's largest value.
fn unsigned64_bounds(premises: &[&Proposition]) -> Option<BTreeMap<MachineTerm, (u64, u64)>> {
    let mut bounds = BTreeMap::new();
    for premise in premises {
        let (lower, upper, strict) = unsigned64_order(premise)?;
        if !charge_bitvector(lower) || !charge_bitvector(upper) {
            return None;
        }
        let strict = u64::from(strict);
        match (lower.uint64_as_const(), upper.uint64_as_const()) {
            (None, Some(limit)) => {
                let Some(limit) = limit.checked_sub(strict) else {
                    continue;
                };
                let entry = bounds.entry(lower.clone()).or_insert((0, u64::MAX));
                entry.1 = entry.1.min(limit);
            }
            (Some(limit), None) => {
                let Some(limit) = limit.checked_add(strict) else {
                    continue;
                };
                let entry = bounds.entry(upper.clone()).or_insert((0, u64::MAX));
                entry.0 = entry.0.max(limit);
            }
            (None, None) if strict == 1 => {
                let entry = bounds.entry(lower.clone()).or_insert((0, u64::MAX));
                entry.1 = entry.1.min(u64::MAX - 1);
            }
            _ => {}
        }
    }
    Some(bounds)
}

enum OffsetPart<'a> {
    Offset(&'a PointerOffsetTerm),
    Scaled(crate::kernel::MachineOperandView<'a>, i64),
    /// An unsigned 64-bit index scaled by an element width.
    Scaled64(crate::kernel::MachineOperandView<'a>, i64),
}

/// Check Integer rule node `index` against the Integer readings of the
/// premises it cites. The Integer rules read a native comparison premise as
/// the Integer comparison of its exact observations, which holds exactly
/// when it does; only the cited premises are read, so the work follows the
/// certificate rather than the context.
fn integer_rule(
    index: usize,
    bounds: &[usize],
    premises: &[Proposition],
    result: &Proposition,
    check: fn(
        usize,
        &[usize],
        &[Proposition],
        &Proposition,
    ) -> Result<(), SpecialArithmeticCheckError>,
) -> Result<(), SpecialArithmeticCheckError> {
    if bounds.iter().any(|&bound| bound >= premises.len()) {
        return check(index, bounds, premises, result);
    }
    let cited = bounds
        .iter()
        .map(|&bound| {
            crate::kernel::machine_integer::comparison::integer_readings_with_promotions(
                &premises[bound],
            )
            .into_iter()
            .next()
            .unwrap_or_else(|| premises[bound].clone())
        })
        .collect::<Vec<_>>();
    let local = (0..bounds.len()).collect::<Vec<_>>();
    integer_rule_holds(result, |result| check(index, &local, &cited, result))
}

/// An Integer rule's result as the rule derives it: a native comparison
/// result is the Integer comparison of its exact observations, in whichever
/// of its readings the rule's inputs name. The first reading that checks is
/// the node's.
fn integer_rule_holds(
    result: &Proposition,
    check: impl Fn(&Proposition) -> Result<(), SpecialArithmeticCheckError>,
) -> Result<(), SpecialArithmeticCheckError> {
    let negated;
    let native = match result {
        Proposition::Not(inner) => match inner.as_ref() {
            Proposition::ConditionIs(condition, value) => {
                negated = Proposition::ConditionIs(condition.clone(), !value);
                &negated
            }
            _ => result,
        },
        _ => result,
    };
    let readings =
        crate::kernel::machine_integer::comparison::integer_observations_of_native_comparison(
            native,
        );
    if readings.is_empty() {
        return check(result);
    }
    let mut first_error = None;
    for reading in &readings {
        match check(reading) {
            Ok(()) => return Ok(()),
            Err(error) => {
                first_error.get_or_insert(error);
            }
        }
    }
    Err(first_error.expect("a reading was checked"))
}

fn pointer_translation(
    relation: &Proposition,
    bound_propositions: &[&Proposition],
    goal: &Proposition,
) -> bool {
    if let Proposition::ConditionIs(ConditionTerm::PointerValueEqual(left, right), true) = goal {
        let same_domain = |a: &PointerValue, b: &PointerValue| {
            a.designation() == b.designation()
                && a.extent() == b.extent()
                && a.extent_is_known() == b.extent_is_known()
        };
        let linked = match relation {
            Proposition::ConditionIs(ConditionTerm::PointerValueEqual(a, b), true) => {
                (same_domain(left, a) && same_domain(right, b))
                    || (same_domain(left, b) && same_domain(right, a))
            }
            _ => same_domain(left, right),
        };
        if !linked {
            return false;
        }
    }
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
    // The cited bounds are of two kinds: signed 32-bit ones, which keep a
    // 32-bit index sum defined, and unsigned 64-bit ones, which keep a
    // 64-bit index sum from wrapping.
    let (wide_bounds, signed_bounds): (Vec<&Proposition>, Vec<&Proposition>) = bound_propositions
        .iter()
        .copied()
        .partition(|premise| unsigned64_order(premise).is_some());
    let Some(bounds) = scalar_bounds(&signed_bounds) else {
        return false;
    };
    let Some(wide_bounds) = unsigned64_bounds(&wide_bounds) else {
        return false;
    };
    use crate::kernel::MachineOperandView as V;
    // The original maps are sorted by native syntax. Binary search preserves
    // that exact matching rule while retaining the queried shared operand.
    let bounds: Vec<_> = bounds.into_iter().collect();
    let wide_bounds: Vec<_> = wide_bounds.into_iter().collect();
    fn lookup<T: Copy>(bounds: &[(MachineTerm, T)], value: V<'_>) -> Option<T> {
        bounds
            .binary_search_by(|(term, _)| {
                crate::kernel::machine_operand_syntax_cmp(V::Legacy(term), value)
            })
            .ok()
            .map(|index| bounds[index].1)
    }
    let wide_range = |value: V<'_>| match value.uint64_constant() {
        Some(value) => (value, value),
        None => lookup(&wide_bounds, value).unwrap_or((0, u64::MAX)),
    };
    let wide_sum_is_exact = |x: V<'_>, y: V<'_>| {
        if !pointer_index_payload(x).is_some_and(charge_payload)
            || !pointer_index_payload(y).is_some_and(charge_payload)
        {
            return false;
        }
        u128::from(wide_range(x).1) + u128::from(wide_range(y).1) <= u128::from(u64::MAX)
    };
    let atom_range = |value: V<'_>| {
        if let Some(bits) = value.word32_constant() {
            let value = i64::from(bits as i32);
            return Some((value, value));
        }
        if value.variable().is_some() {
            return Some(lookup(&bounds, value).unwrap_or((SIGNED_MIN, SIGNED_MAX)));
        }
        let payload = pointer_index_payload(value)?;
        let comparisons = (usize::BITS - bounds.len().max(1).leading_zeros()) as usize;
        if crate::instrumentation::deadline_exceeded_with_work(
            payload.saturating_mul(comparisons).max(1),
        ) {
            return None;
        }
        lookup(&bounds, value)
    };
    let sum_is_defined = |x: V<'_>, y: V<'_>| {
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
                    pending.push(OffsetPart::Scaled(value.operand_view(), *byte_width));
                    continue;
                }
                OffsetPart::Scaled(value, width) => {
                    if let Some(int32_constant!(bits)) = value.literal() {
                        let value = i128::from(constant_u32(bits) as i32) * i128::from(width);
                        let Some(next) = constant.checked_add(sign * value) else {
                            return false;
                        };
                        constant = next;
                        continue;
                    }
                    if let Some((MachineIntegerType::Int32, MachineBinaryOp::Add, [left, right])) =
                        value.binary()
                    {
                        if sum_is_defined(left, right) {
                            pending.push(OffsetPart::Scaled(left, width));
                            pending.push(OffsetPart::Scaled(right, width));
                            continue;
                        }
                    }
                    PointerOffsetTerm::Int32Scaled {
                        value: value.retain(MachineIntegerType::Int32),
                        byte_width: width,
                    }
                }
                OffsetPart::Offset(PointerOffsetTerm::Int64Scaled {
                    value,
                    byte_width,
                    unsigned: true,
                }) => {
                    pending.push(OffsetPart::Scaled64(value.operand_view(), *byte_width));
                    continue;
                }
                OffsetPart::Scaled64(value, width) => {
                    if let Some(bits) = value.uint64_constant() {
                        let value = i128::from(bits) * i128::from(width);
                        let Some(next) = constant.checked_add(sign * value) else {
                            return false;
                        };
                        constant = next;
                        continue;
                    }
                    if let Some((MachineIntegerType::UInt64, MachineBinaryOp::Add, [left, right])) =
                        value.binary()
                    {
                        if wide_sum_is_exact(left, right) {
                            pending.push(OffsetPart::Scaled64(left, width));
                            pending.push(OffsetPart::Scaled64(right, width));
                            continue;
                        }
                    }
                    PointerOffsetTerm::Int64Scaled {
                        value: value.retain(MachineIntegerType::Int64),
                        byte_width: width,
                        unsigned: true,
                    }
                }
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
        let mut candidates = vec![goal_pointer.offset.clone()];
        if let Some(reduced) = drop_aligned_scaled_addends(&goal_pointer.offset, goal_alignment) {
            candidates.push(reduced);
        }
        let Some(aligned) = candidates.into_iter().find_map(|candidate| {
            offset_difference(&candidate, &base.offset)
                .map(|delta| delta.rem_euclid(goal_alignment as i128) == 0)
        }) else {
            return false;
        };
        aligned
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

/// Remove symbolic scaled addends whose byte scale is divisible by the target
/// alignment.  Such an addend cannot change the pointer's residue.  The
/// traversal is iterative because this helper runs on source-shaped pointer
/// offsets and must not inherit their nesting depth.
fn drop_aligned_scaled_addends(
    offset: &PointerOffsetTerm,
    alignment: u64,
) -> Option<PointerOffsetTerm> {
    if !charge_pointer_offset(offset) {
        return None;
    }
    let alignment = i64::try_from(alignment).ok()?;
    let mut pending = vec![offset];
    let mut parts = Vec::new();
    while let Some(offset) = pending.pop() {
        match offset {
            PointerOffsetTerm::Add(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            other => parts.push(other.clone()),
        }
    }
    fn constant_factor(term: crate::kernel::MachineOperandView<'_>) -> Option<i64> {
        let (MachineIntegerType::Int32, MachineBinaryOp::Multiply, [left, right]) =
            term.binary()?
        else {
            return None;
        };
        left.word32_constant()
            .or_else(|| right.word32_constant())
            .map(|value| i64::from(value as i32))
    }
    let divisible = |part: &PointerOffsetTerm| match part {
        PointerOffsetTerm::Int32Scaled { value, byte_width }
        | PointerOffsetTerm::Int64Scaled {
            value, byte_width, ..
        } => {
            let scale = constant_factor(value.operand_view())
                .and_then(|factor| factor.checked_mul(*byte_width))
                .unwrap_or(*byte_width);
            scale != 0 && scale % alignment == 0
        }
        _ => false,
    };
    if !parts.iter().any(divisible) {
        return None;
    }
    Some(
        parts
            .into_iter()
            .filter(|part| !divisible(part))
            .reduce(PointerOffsetTerm::add)
            .unwrap_or(PointerOffsetTerm::Constant(0)),
    )
}

#[derive(Clone, Debug)]
enum TaggedTag<'a> {
    Constant(u64),
    Source(Word<'a>),
    Add(Arc<TaggedTag<'a>>, Word<'a>),
    Subtract(Arc<TaggedTag<'a>>, Word<'a>),
    BitwiseAnd(Arc<TaggedTag<'a>>, u64),
    BitwiseOr(Arc<TaggedTag<'a>>, u64),
}

#[derive(Clone, Debug)]
struct TaggedAddress<'a> {
    /// Pointer payloads can be large symbolic offset trees.  The iterative
    /// evaluator keeps one of these forms at every visited term, so sharing
    /// the payload is essential: cloning a `Pointer` here would turn a tag
    /// chain over a deep pointer into a payload-depth by tag-depth operation.
    pointer: Arc<Pointer>,
    tag: Arc<TaggedTag<'a>>,
    /// The tag's constant value, when it is known.  Keeping this alongside
    /// the term is important: a symbolic tag chain must not be recursively
    /// re-evaluated every time another address operation extends it.
    tag_constant: Option<u64>,
}

/// Compare compact tag expressions without materializing their nested
/// bitvector syntax.  Shared tag prefixes are discharged by pointer identity;
/// distinct source leaves use the bounded iterative term comparator.
fn tagged_tag_equal<'a>(left: &Arc<TaggedTag<'a>>, right: &Arc<TaggedTag<'a>>) -> bool {
    let mut pending = vec![(Arc::clone(left), Arc::clone(right))];
    while let Some((left, right)) = pending.pop() {
        if Arc::ptr_eq(&left, &right) {
            continue;
        }
        if crate::instrumentation::deadline_exceeded_with_work(1) {
            return false;
        }
        match (&*left, &*right) {
            (TaggedTag::Constant(left), TaggedTag::Constant(right)) => {
                if left != right {
                    return false;
                }
            }
            (TaggedTag::Source(left), TaggedTag::Source(right)) => {
                if !word_view::equal(*left, *right) {
                    return false;
                }
            }
            (TaggedTag::Add(left_tag, left_term), TaggedTag::Add(right_tag, right_term))
            | (
                TaggedTag::Subtract(left_tag, left_term),
                TaggedTag::Subtract(right_tag, right_term),
            ) => {
                if !word_view::equal(*left_term, *right_term) {
                    return false;
                }
                pending.push((Arc::clone(left_tag), Arc::clone(right_tag)));
            }
            (
                TaggedTag::BitwiseAnd(left_tag, left_mask),
                TaggedTag::BitwiseAnd(right_tag, right_mask),
            )
            | (
                TaggedTag::BitwiseOr(left_tag, left_mask),
                TaggedTag::BitwiseOr(right_tag, right_mask),
            ) => {
                if left_mask != right_mask {
                    return false;
                }
                pending.push((Arc::clone(left_tag), Arc::clone(right_tag)));
            }
            _ => return false,
        }
    }
    true
}

fn pointer_index_hash(view: crate::kernel::MachineOperandView<'_>) -> Option<u64> {
    if let Some(leaf) = view
        .literal()
        .map(std::borrow::Cow::Owned)
        .or_else(|| view.read_source())
    {
        return bounded_term_hash(&leaf);
    }
    let (format, op, [left, right]) = view.binary()?;
    use MachineBinaryOp as O;
    use MachineIntegerType as T;
    if !matches!(
        (format, op),
        (
            T::Int32,
            O::Add | O::Subtract | O::BitwiseAnd | O::BitwiseOr
        ) | (
            T::UInt64,
            O::Add | O::Subtract | O::BitwiseAnd | O::BitwiseOr
        )
    ) {
        return None;
    }
    // Called only after the occurrence/depth-bounded pointer payload check.
    let header = MachineTerm::Binary {
        format,
        op,
        left: Box::new(MachineTerm::constant(0)),
        right: Box::new(MachineTerm::constant(0)),
    };
    let mut hash = DefaultHasher::new();
    std::mem::discriminant(&header).hash(&mut hash);
    (format, op).hash(&mut hash);
    pointer_index_hash(left)?.hash(&mut hash);
    pointer_index_hash(right)?.hash(&mut hash);
    Some(hash.finish())
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
                pointer_index_hash(value.operand_view())?.hash(&mut hasher);
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
    by_hash: HashMap<u64, Vec<AlignmentEntry<'a>>>,
}

struct AlignmentEntry<'a> {
    pointer: &'a Pointer,
    max_alignment: u64,
}

impl<'a> AlignmentIndex<'a> {
    fn new(alignments: &'a [(&'a Pointer, u64)]) -> Option<Self> {
        let mut by_hash: HashMap<u64, Vec<AlignmentEntry<'a>>> = HashMap::new();
        for (pointer, alignment) in alignments {
            if crate::instrumentation::deadline_exceeded_with_work(1) {
                return None;
            }
            let candidates = by_hash.entry(pointer_identity_hash(pointer)?).or_default();
            let mut matched = false;
            for candidate in candidates.iter_mut() {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    return None;
                }
                if pointer_equal(pointer, candidate.pointer) {
                    candidate.max_alignment = candidate.max_alignment.max(*alignment);
                    matched = true;
                    break;
                }
            }
            if !matched {
                candidates.push(AlignmentEntry {
                    pointer,
                    max_alignment: *alignment,
                });
            }
        }
        Some(Self { by_hash })
    }

    fn supports(&self, pointer: &Pointer, required: u64) -> bool {
        let Some(hash) = pointer_identity_hash(pointer) else {
            return false;
        };
        self.by_hash.get(&hash).is_some_and(|candidates| {
            candidates.iter().any(|candidate| {
                if crate::instrumentation::deadline_exceeded_with_work(1) {
                    return false;
                }
                candidate.max_alignment >= required && pointer_equal(pointer, candidate.pointer)
            })
        })
    }
}

fn bounded_term_hashes(roots: &[&MachineTerm]) -> Option<HashMap<usize, u64>> {
    let mut pending = roots.iter().map(|root| (*root, false)).collect::<Vec<_>>();
    let mut hashes: HashMap<usize, u64> = HashMap::new();
    while let Some((term, expanded)) = pending.pop() {
        let identity = term as *const MachineTerm as usize;
        if hashes.contains_key(&identity) {
            continue;
        }
        if expanded {
            let mut hasher = DefaultHasher::new();
            std::mem::discriminant(term).hash(&mut hasher);
            // One variant spells every format-carrying operator, so its
            // format and operator are part of the identity.
            if let MachineTerm::Binary { format, op, .. } = term {
                (format, op).hash(&mut hasher);
            }
            // So is a constant's format: one variant spells every constant.
            if let MachineTerm::Constant { format, .. } = term {
                format.hash(&mut hasher);
            }
            match term {
                bits32_constant!(value) => constant_u32(*value).hash(&mut hasher),
                int64_constant!(value) => constant_i64(*value).hash(&mut hasher),
                uint64_constant!(value) => constant_u64(*value).hash(&mut hasher),
                MachineTerm::Variable(value) => value.hash(&mut hasher),
                MachineTerm::MemoryLoad(memory, pointer, kind) => {
                    memory.arena_id().hash(&mut hasher);
                    kind.hash(&mut hasher);
                    pointer_identity_hash(pointer)?.hash(&mut hasher);
                }
                MachineTerm::PointerAddress(pointer, _) => {
                    pointer_identity_hash(pointer)?.hash(&mut hasher)
                }
                binary_term!(Int32, Add, left, right)
                | binary_term!(Int32, Subtract, left, right)
                | MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op:
                        MachineBinaryOp::Add
                        | MachineBinaryOp::Subtract
                        | MachineBinaryOp::BitwiseAnd
                        | MachineBinaryOp::BitwiseOr,
                    left,
                    right,
                }
                | binary_term!(Int32, BitwiseAnd, left, right)
                | binary_term!(Int32, BitwiseOr, left, right) => {
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
                binary_term!(Int32, Add, left, right)
                | binary_term!(Int32, Subtract, left, right)
                | MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op:
                        MachineBinaryOp::Add
                        | MachineBinaryOp::Subtract
                        | MachineBinaryOp::BitwiseAnd
                        | MachineBinaryOp::BitwiseOr,
                    left,
                    right,
                }
                | binary_term!(Int32, BitwiseAnd, left, right)
                | binary_term!(Int32, BitwiseOr, left, right) => {
                    pending.push((right, false));
                    pending.push((left, false));
                }
                _ => {}
            }
        }
    }
    Some(hashes)
}

fn bounded_term_hash(root: &MachineTerm) -> Option<u64> {
    bounded_term_hashes(&[root])?
        .get(&(root as *const MachineTerm as usize))
        .copied()
}

fn constant_value(term: Word<'_>, constants: &HashMap<WordKey, Option<u64>>) -> Option<u64> {
    constants.get(&term.key()).copied().flatten()
}

fn add_tag<'a>(
    form: TaggedAddress<'a>,
    right: Word<'a>,
    right_constant: Option<u64>,
) -> TaggedAddress<'a> {
    if form.tag_constant == Some(0) {
        TaggedAddress {
            pointer: form.pointer,
            tag: right_constant.map_or_else(
                || masked_source_tag(right),
                |value| Arc::new(TaggedTag::Constant(value)),
            ),
            tag_constant: right_constant,
        }
    } else if right_constant == Some(0) {
        form
    } else {
        TaggedAddress {
            pointer: form.pointer,
            tag: form.tag_constant.zip(right_constant).map_or_else(
                || Arc::new(TaggedTag::Add(form.tag, right)),
                |(left, right)| Arc::new(TaggedTag::Constant(left.wrapping_add(right))),
            ),
            tag_constant: form
                .tag_constant
                .zip(right_constant)
                .map(|(left, right)| left.wrapping_add(right)),
        }
    }
}

fn masked_source_tag<'a>(term: Word<'a>) -> Arc<TaggedTag<'a>> {
    if let Some((source, mask)) = masked_source(term) {
        Arc::new(TaggedTag::BitwiseAnd(
            Arc::new(TaggedTag::Source(source)),
            mask,
        ))
    } else {
        Arc::new(TaggedTag::Source(term))
    }
}

fn masked_source(term: Word<'_>) -> Option<(Word<'_>, u64)> {
    let WordNode::Binary {
        format: MachineIntegerType::UInt64,
        op: MachineBinaryOp::BitwiseAnd,
        left,
        right,
    } = term.node()
    else {
        return None;
    };
    match (left.uint64_as_const(), right.uint64_as_const()) {
        (None, Some(mask)) => Some((left, mask)),
        (Some(mask), None) => Some((right, mask)),
        _ => None,
    }
}
fn pointer_or_masked_tag<'a>(
    left: Word<'a>,
    right: Word<'a>,
) -> Option<(&'a Pointer, Word<'a>, u64)> {
    let (pointer, tag) = match (left.node(), right.node()) {
        (WordNode::PointerAddress(pointer), _) => (pointer, right),
        (_, WordNode::PointerAddress(pointer)) => (pointer, left),
        _ => return None,
    };
    let (_, mask) = masked_source(tag)?;
    let alignment = mask.checked_add(1).filter(|v| v.is_power_of_two())?;
    Some((pointer, tag, alignment))
}

fn tagged_form<'a>(
    term: Word<'a>,
    relation: (Word<'a>, Word<'a>),
    alignments: &AlignmentIndex<'_>,
) -> Option<TaggedAddress<'a>> {
    tagged_form_inner(term, Some(relation), alignments)
}

fn tagged_form_from_alignment<'a>(
    term: Word<'a>,
    alignments: &AlignmentIndex<'_>,
) -> Option<TaggedAddress<'a>> {
    tagged_form_inner(term, None, alignments)
}

fn tagged_form_inner<'a>(
    term: Word<'a>,
    relation: Option<(Word<'a>, Word<'a>)>,
    alignments: &AlignmentIndex<'_>,
) -> Option<TaggedAddress<'a>> {
    let identities = if let Some((left, right)) = relation {
        word_view::hashes(&[term, left, right])?
    } else {
        word_view::hashes(&[term])?
    };
    let constants = if let Some((left, right)) = relation {
        word_view::constants(&[term, left, right])
    } else {
        word_view::constants(&[term])
    };
    if constants.is_empty() {
        return None;
    }
    let relation_keys = relation.map(|(left, right)| {
        (
            identities.get(&left.key()).copied(),
            identities.get(&right.key()).copied(),
        )
    });
    enum Task<'a> {
        Visit(Word<'a>),
        FinishAdd {
            term: Word<'a>,
            left: Word<'a>,
            right: Word<'a>,
        },
        FinishAddRight {
            term: Word<'a>,
            left: Word<'a>,
        },
        FinishSubtract {
            term: Word<'a>,
            right: Word<'a>,
        },
        FinishAnd {
            term: Word<'a>,
            mask: u64,
            alignment: u64,
        },
        FinishOr {
            term: Word<'a>,
            constant: u64,
            alignment: u64,
        },
        FinishPointerOr {
            term: Word<'a>,
            pointer: &'a Pointer,
            tag: Word<'a>,
            alignment: u64,
        },
        FinishRelation {
            term: Word<'a>,
        },
    }

    fn store<'a>(
        identity: WordKey,
        result: Option<TaggedAddress<'a>>,
        active: &mut HashSet<WordKey>,
        results: &mut HashMap<WordKey, Option<TaggedAddress<'a>>>,
        values: &mut Vec<Option<TaggedAddress<'a>>>,
    ) {
        active.remove(&identity);
        values.push(result.clone());
        results.insert(identity, result);
    }

    let mut tasks = vec![Task::Visit(term)];
    let mut values = Vec::new();
    let mut active = HashSet::new();
    let mut results: HashMap<WordKey, Option<TaggedAddress<'a>>> = HashMap::new();
    while let Some(task) = tasks.pop() {
        match task {
            Task::Visit(current) => {
                let identity = current.key();
                if let Some(result) = results.get(&identity) {
                    values.push(result.clone());
                    continue;
                }
                if active.contains(&identity) {
                    values.push(None);
                    continue;
                }
                active.insert(identity);
                match current.node() {
                    WordNode::PointerAddress(pointer) => store(
                        identity,
                        Some(TaggedAddress {
                            pointer: Arc::new(pointer.clone()),
                            tag: Arc::new(TaggedTag::Constant(0)),
                            tag_constant: Some(0),
                        }),
                        &mut active,
                        &mut results,
                        &mut values,
                    ),
                    WordNode::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::Add,
                        left,
                        right,
                    } => {
                        tasks.push(Task::FinishAdd {
                            term: current,
                            left,
                            right,
                        });
                        tasks.push(Task::Visit(left));
                    }
                    WordNode::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::Subtract,
                        left,
                        right,
                    } => {
                        tasks.push(Task::FinishSubtract {
                            term: current,
                            right,
                        });
                        tasks.push(Task::Visit(left));
                    }
                    WordNode::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::BitwiseAnd,
                        left,
                        right,
                    } => {
                        let (inner, mask) = match (
                            constant_value(left, &constants),
                            constant_value(right, &constants),
                        ) {
                            (None, Some(mask)) => (left, mask),
                            (Some(mask), None) => (right, mask),
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
                    WordNode::Binary {
                        format: MachineIntegerType::UInt64,
                        op: MachineBinaryOp::BitwiseOr,
                        left,
                        right,
                    } => {
                        if let Some((pointer, tag, alignment)) = pointer_or_masked_tag(left, right)
                        {
                            tasks.push(Task::FinishPointerOr {
                                term: current,
                                pointer,
                                tag,
                                alignment,
                            });
                            continue;
                        }
                        let (inner, constant) = match (
                            constant_value(left, &constants),
                            constant_value(right, &constants),
                        ) {
                            (None, Some(constant)) => (left, constant),
                            (Some(constant), None) => (right, constant),
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
                    _ if relation_keys
                        .is_some_and(|(left, _)| left == identities.get(&identity).copied())
                        && relation.is_some_and(|(left, _)| word_view::equal(current, left)) =>
                    {
                        let (_, right) = relation.expect("relation key is present");
                        tasks.push(Task::FinishRelation { term: current });
                        tasks.push(Task::Visit(right));
                    }
                    _ if relation_keys
                        .is_some_and(|(_, right)| right == identities.get(&identity).copied())
                        && relation.is_some_and(|(_, right)| word_view::equal(current, right)) =>
                    {
                        let (left, _) = relation.expect("relation key is present");
                        tasks.push(Task::FinishRelation { term: current });
                        tasks.push(Task::Visit(left));
                    }
                    _ => store(identity, None, &mut active, &mut results, &mut values),
                }
            }
            Task::FinishAdd { term, left, right } => {
                let left_form = values.pop().flatten();
                if let Some(form) = left_form {
                    store(
                        term.key(),
                        Some(add_tag(form, right, constant_value(right, &constants))),
                        &mut active,
                        &mut results,
                        &mut values,
                    );
                } else {
                    tasks.push(Task::FinishAddRight { term, left });
                    tasks.push(Task::Visit(right));
                }
            }
            Task::FinishAddRight { term, left } => {
                let right_form = values.pop().flatten();
                store(
                    term.key(),
                    right_form.map(|form| add_tag(form, left, constant_value(left, &constants))),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishSubtract { term, right } => {
                let left_form = values.pop().flatten();
                store(
                    term.key(),
                    left_form.map(|form| {
                        let right_constant = constant_value(right, &constants);
                        let tag = form.tag_constant.zip(right_constant).map_or_else(
                            || Arc::new(TaggedTag::Subtract(form.tag, right)),
                            |(left, right)| Arc::new(TaggedTag::Constant(left.wrapping_sub(right))),
                        );
                        TaggedAddress {
                            pointer: form.pointer,
                            tag,
                            tag_constant: form
                                .tag_constant
                                .zip(right_constant)
                                .map(|(left, right)| left.wrapping_sub(right)),
                        }
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
                    term.key(),
                    form.and_then(|form| {
                        // A symbolic tag may itself be an explicitly masked
                        // source term.  Disjoint masks establish a zero tag
                        // locally; this is the bounded normal-form rule used
                        // for the rbtree parent-word shape, not a context
                        // search or alternate derivation.
                        let tag = if let Some(value) = form.tag_constant {
                            Arc::new(TaggedTag::Constant(value & mask))
                        } else if let TaggedTag::BitwiseAnd(_, source_mask) = form.tag.as_ref()
                            && source_mask & mask == 0
                        {
                            Arc::new(TaggedTag::Constant(0))
                        } else if let TaggedTag::Source(source) = form.tag.as_ref()
                            && let WordNode::Binary {
                                format: MachineIntegerType::UInt64,
                                op: MachineBinaryOp::BitwiseAnd,
                                left,
                                right,
                            } = source.node()
                            && let Some(source_mask) = constant_value(left, &constants)
                                .or_else(|| constant_value(right, &constants))
                        {
                            if source_mask & mask == 0 {
                                Arc::new(TaggedTag::Constant(0))
                            } else {
                                Arc::new(TaggedTag::BitwiseAnd(form.tag, mask))
                            }
                        } else {
                            Arc::new(TaggedTag::BitwiseAnd(form.tag, mask))
                        };
                        let tag_constant = match tag.as_ref() {
                            TaggedTag::Constant(value) => Some(*value),
                            _ => None,
                        };
                        alignments
                            .supports(form.pointer.as_ref(), alignment)
                            .then_some(TaggedAddress {
                                pointer: form.pointer,
                                tag,
                                tag_constant,
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
                    term.key(),
                    form.and_then(|form| {
                        let tag = form.tag_constant.map_or_else(
                            || Arc::new(TaggedTag::BitwiseOr(form.tag, constant)),
                            |value| Arc::new(TaggedTag::Constant(value | constant)),
                        );
                        (constant == 0 || alignments.supports(form.pointer.as_ref(), alignment))
                            .then_some(TaggedAddress {
                                pointer: form.pointer,
                                tag,
                                tag_constant: form.tag_constant.map(|tag| tag | constant),
                            })
                    }),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishPointerOr {
                term,
                pointer,
                tag,
                alignment,
            } => {
                store(
                    term.key(),
                    alignments
                        .supports(pointer, alignment)
                        .then(|| TaggedAddress {
                            pointer: Arc::new(pointer.clone()),
                            tag: masked_source_tag(tag),
                            tag_constant: None,
                        }),
                    &mut active,
                    &mut results,
                    &mut values,
                );
            }
            Task::FinishRelation { term } => {
                let result = values.pop().flatten();
                store(term.key(), result, &mut active, &mut results, &mut values);
            }
        }
    }
    values.pop().flatten()
}

/// Reading low tag bits only needs the base aligned to the mask's modulus.
/// The existing bounded word walker supplies the tag; no ambient reasoning or
/// memory history is consulted. Addition is modular, so higher tag bits do not
/// affect this projection.
fn pointer_tag_read_equal<'a>(
    left: Word<'a>,
    right: Word<'a>,
    relation: Option<(Word<'a>, Word<'a>)>,
    alignments: &AlignmentIndex<'_>,
) -> bool {
    let project = |term: Word<'a>| {
        let (word, mask) = masked_source(term)?;
        let alignment = mask
            .checked_add(1)
            .filter(|value| *value > 1 && value.is_power_of_two())?;
        let form = tagged_form_inner(word, relation, alignments)?;
        if !alignments.supports(form.pointer.as_ref(), alignment) {
            return None;
        }
        let tag = match form.tag.as_ref() {
            TaggedTag::Constant(value) => Arc::new(TaggedTag::Constant(value & mask)),
            TaggedTag::BitwiseAnd(inner, inner_mask) => {
                let mask = inner_mask & mask;
                if mask == 0 {
                    Arc::new(TaggedTag::Constant(0))
                } else {
                    Arc::new(TaggedTag::BitwiseAnd(Arc::clone(inner), mask))
                }
            }
            _ => Arc::new(TaggedTag::BitwiseAnd(form.tag, mask)),
        };
        Some(tag)
    };
    let source = |term: Word<'a>| {
        term.uint64_as_const().map_or_else(
            || masked_source_tag(term),
            |value| Arc::new(TaggedTag::Constant(value)),
        )
    };
    project(left).is_some_and(|tag| tagged_tag_equal(&tag, &source(right)))
        || project(right).is_some_and(|tag| tagged_tag_equal(&source(left), &tag))
}

fn word_comparison(
    proposition: &Proposition,
) -> Option<(
    crate::kernel::machine_integer::comparison::StructuralComparisonView<'_>,
    bool,
)> {
    let Proposition::ConditionIs(condition, truth) = proposition else {
        return None;
    };
    let view = crate::kernel::machine_integer::comparison::structural_comparison_view(condition)?;
    if !matches!(
        view.format,
        MachineIntegerType::Int64 | MachineIntegerType::UInt64
    ) || view.relation != CompareRelation::Equal
    {
        return None;
    }
    let expected = *truth != view.negated;
    Some((view, expected))
}

fn pointer_word_equality(
    relation: &Proposition,
    alignment_premises: &[&Proposition],
    result: &Proposition,
) -> bool {
    let Some((relation_view, true)) = word_comparison(relation) else {
        return false;
    };
    let [left, right] = relation_view
        .operands
        .each_ref()
        .map(|operand| Word(operand.operand_view()));
    let Some((goal_view, expected)) = word_comparison(result) else {
        return false;
    };
    let [goal_left, goal_right] = goal_view
        .operands
        .each_ref()
        .map(|operand| Word(operand.operand_view()));
    if ![left, right, goal_left, goal_right]
        .into_iter()
        .all(word_view::charge)
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
    if expected
        && pointer_tag_read_equal(goal_left, goal_right, Some((left, right)), &alignment_index)
    {
        return true;
    }
    let goal_left_form = tagged_form(goal_left, (left, right), &alignment_index);
    let goal_right_form = tagged_form(goal_right, (left, right), &alignment_index);
    let equal = match (goal_left_form, goal_right_form) {
        (Some(goal_left), Some(goal_right)) => {
            pointer_equal(goal_left.pointer.as_ref(), goal_right.pointer.as_ref())
                && tagged_tag_equal(&goal_left.tag, &goal_right.tag)
        }
        _ => false,
    };
    let structural = if expected {
        equal
    } else {
        match (
            tagged_form(goal_left, (left, right), &alignment_index),
            tagged_form(goal_right, (left, right), &alignment_index),
        ) {
            (Some(goal_left), Some(goal_right))
                if pointer_equal(goal_left.pointer.as_ref(), goal_right.pointer.as_ref()) =>
            {
                matches!(
                    (goal_left.tag_constant, goal_right.tag_constant),
                    (Some(left), Some(right)) if left != right
                )
            }
            _ => false,
        }
    };
    if structural {
        return true;
    }
    false
}

fn pointer_word_from_alignment(alignment_premises: &[&Proposition], result: &Proposition) -> bool {
    let Some((view, expected)) = word_comparison(result) else {
        return false;
    };
    let [left, right] = view
        .operands
        .each_ref()
        .map(|operand| Word(operand.operand_view()));
    if !word_view::charge(left) || !word_view::charge(right) {
        return false;
    }
    for premise in alignment_premises {
        let Proposition::ConditionIs(condition, true) = premise else {
            return false;
        };
        if checked_pointer_alignment(condition).is_none() {
            return false;
        }
    }
    let alignments = alignment_premises
        .iter()
        .map(|premise| {
            let Proposition::ConditionIs(condition, true) = premise else {
                unreachable!("alignment premises were checked above");
            };
            checked_pointer_alignment(condition).expect("alignment premises were checked above")
        })
        .collect::<Vec<_>>();
    let alignment_index = AlignmentIndex::new(&alignments);
    let Some(alignment_index) = alignment_index else {
        return false;
    };
    if expected && pointer_tag_read_equal(left, right, None, &alignment_index) {
        return true;
    }
    let left_form = tagged_form_from_alignment(left, &alignment_index);
    let right_form = tagged_form_from_alignment(right, &alignment_index);
    let Some(left_form) = left_form else {
        return false;
    };
    let Some(right_form) = right_form else {
        return false;
    };
    let equal = pointer_equal(left_form.pointer.as_ref(), right_form.pointer.as_ref())
        && tagged_tag_equal(&left_form.tag, &right_form.tag);
    if expected {
        equal
    } else {
        pointer_equal(left_form.pointer.as_ref(), right_form.pointer.as_ref())
            && matches!(
                (left_form.tag_constant, right_form.tag_constant),
                (Some(left), Some(right)) if left != right
            )
    }
}

fn float_reflexive(finite: &Proposition, result: &Proposition) -> bool {
    let Proposition::ConditionIs(finite_condition, true) = finite else {
        return false;
    };
    let (finite_expression, finite_width) = match finite_condition {
        ConditionTerm::Float32(FloatCondition::Classification {
            value: expression,
            classification: FloatClassification::Finite,
        }) => (expression.as_ref(), 32),
        ConditionTerm::Float64(FloatCondition::Classification {
            value: expression,
            classification: FloatClassification::Finite,
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
        ConditionTerm::Float32(FloatCondition::Comparison {
            operator,
            left,
            right,
        }) => (*operator, left.as_ref(), right.as_ref(), 32),
        ConditionTerm::Float64(FloatCondition::Comparison {
            operator,
            left,
            right,
        }) => (*operator, left.as_ref(), right.as_ref(), 64),
        _ => return false,
    };
    if !charge_bitvector(left) || !charge_bitvector(right) {
        return false;
    }
    let same_result = bitvector_equal(left, right);
    let same_finite = bitvector_equal(left, finite_expression);
    if width != finite_width || !same_result || !same_finite {
        return false;
    }
    let reflexive = matches!(
        operator,
        ComparisonOperator::Equal
            | ComparisonOperator::LessEqual
            | ComparisonOperator::GreaterEqual
    );
    *expected == reflexive
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn shared_pointer_certificate_identity_preserves_payload_and_hash() {
        use crate::kernel::{
            KernelTerm, KernelTermExport, MachineOperandView as V, SharedMachineIntegerTerm as S,
            VerificationSession,
        };
        let _session = VerificationSession::enter();
        let x = MachineTerm::Variable(crate::kernel::Variable(1081201));
        let mut native = x.clone();
        let mut root =
            KernelTerm::retained_machine_operand(MachineIntegerType::Int32, V::Legacy(&x));
        for depth in 0..9 {
            let index = S::from_shared(MachineIntegerType::Int32, root.clone()).unwrap();
            let pointer = Pointer {
                block: PointerBlock::ExternalArgument,
                offset: PointerOffsetTerm::Int32Scaled {
                    value: index.clone(),
                    byte_width: 4,
                },
            };
            let exports = KernelTermExport::machine_export_count();
            assert_eq!(
                pointer_index_payload(index.operand_view()),
                bitvector_payload(&native),
                "depth {depth}"
            );
            if bitvector_payload(&native).is_some() {
                assert_eq!(
                    pointer_index_hash(index.operand_view()),
                    bounded_term_hash(&native)
                );
            }
            let equal = pointer_offset_equal(&pointer.offset, &pointer.offset);
            assert_eq!(equal, bitvector_payload(&native).is_some());
            assert_eq!(KernelTermExport::machine_export_count(), exports);
            root = KernelTerm::machine_binary_shared(
                MachineIntegerType::Int32,
                MachineBinaryOp::Add,
                [root.clone(), root],
            );
            native = MachineTerm::Binary {
                format: MachineIntegerType::Int32,
                op: MachineBinaryOp::Add,
                left: Box::new(native.clone()),
                right: Box::new(native),
            };
        }
    }

    #[test]
    fn signed_domain_query_views_match_legacy_interval_shapes() {
        use crate::kernel::machine_integer::definedness::{
            integer_bounds_of_definedness, interval_query_form,
        };
        let _session = crate::kernel::VerificationSession::enter();
        for format in [
            MachineIntegerType::Int8,
            MachineIntegerType::UInt32,
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            MachineIntegerType::UInt64,
        ] {
            for op in [
                OverflowOperation::Add,
                OverflowOperation::Subtract,
                OverflowOperation::Multiply,
                OverflowOperation::Divide,
            ] {
                let legacy = Proposition::ConditionIs(
                    ConditionTerm::Overflows {
                        format,
                        op,
                        left: Box::new(MachineTerm::Variable(crate::kernel::Variable(986302))),
                        right: Box::new(
                            if format == MachineIntegerType::Int64
                                || format == MachineIntegerType::UInt64
                            {
                                MachineTerm::int64_constant(1)
                            } else {
                                MachineTerm::constant(1)
                            },
                        ),
                    },
                    false,
                );
                let mut forms = vec![legacy.clone()];
                let bounds = integer_bounds_of_definedness(&legacy);
                if let [a, b] = bounds.as_slice() {
                    forms.extend([
                        a.clone(),
                        Proposition::And(Box::new(a.clone()), Box::new(b.clone())),
                        Proposition::And(Box::new(b.clone()), Box::new(a.clone())),
                    ]);
                    forms.push(Proposition::And(
                        Box::new(Proposition::And(Box::new(a.clone()), Box::new(b.clone()))),
                        Box::new(legacy.clone()),
                    ));
                }
                for proposition in forms {
                    let adapted = interval_query_form(&proposition);
                    let expected =
                        signed_definedness_operands(adapted.as_ref().unwrap_or(&proposition));
                    let query = signed_definedness_query(&proposition);
                    assert_eq!(query.is_some(), expected.is_some());
                    if let (
                        Some((width, operands, subtract)),
                        Some((expected_width, left, right, expected_subtract)),
                    ) = (query, expected)
                    {
                        assert_eq!(width, expected_width);
                        assert_eq!(subtract, expected_subtract);
                        let ty = match width {
                            SignedDefinedWidth::Int32 => MachineIntegerType::Int32,
                            SignedDefinedWidth::Int64 => MachineIntegerType::Int64,
                        };
                        for (operand, expected) in operands.iter().zip([left, right]) {
                            assert!(
                                operand.operand_view().retain(ty)
                                    == crate::kernel::SharedMachineIntegerTerm::intern(
                                        ty,
                                        expected.clone()
                                    )
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn constant_bound_views_preserve_native_comparison_polarity() {
        use crate::kernel::{MachineOperandView, Variable};
        for (format, width) in [
            (MachineIntegerType::Int32, SignedDefinedWidth::Int32),
            (MachineIntegerType::Int64, SignedDefinedWidth::Int64),
        ] {
            let term = MachineTerm::Variable(Variable(982601));
            for constant in [-5, 0, 7] {
                let literal = if format == MachineIntegerType::Int32 {
                    MachineTerm::constant(constant as u32)
                } else {
                    MachineTerm::int64_constant(constant)
                };
                for relation in [
                    CompareRelation::Equal,
                    CompareRelation::LessThan,
                    CompareRelation::LessEqual,
                    CompareRelation::GreaterThan,
                    CompareRelation::GreaterEqual,
                ] {
                    for reverse in [false, true] {
                        for truth in [false, true] {
                            let (left, right) = if reverse {
                                (literal.clone(), term.clone())
                            } else {
                                (term.clone(), literal.clone())
                            };
                            let premise = Proposition::ConditionIs(
                                ConditionTerm::Compare {
                                    format,
                                    relation,
                                    left: Box::new(left),
                                    right: Box::new(right),
                                },
                                truth,
                            );
                            let expected = if relation == CompareRelation::Equal {
                                truth.then_some((Some(constant), Some(constant)))
                            } else {
                                let greater = matches!(
                                    relation,
                                    CompareRelation::GreaterThan | CompareRelation::GreaterEqual
                                ) ^ reverse
                                    ^ !truth;
                                let strict = matches!(
                                    relation,
                                    CompareRelation::LessThan | CompareRelation::GreaterThan
                                ) ^ !truth;
                                Some(if greater {
                                    (Some(constant + i64::from(strict)), None)
                                } else {
                                    (None, Some(constant - i64::from(strict)))
                                })
                            };
                            assert_eq!(
                                signed_constant_bound_on_view(
                                    width,
                                    &premise,
                                    MachineOperandView::Legacy(&term)
                                ),
                                expected
                            );
                        }
                    }
                }
            }
        }
    }

    #[test]
    fn cast_term_identity_keeps_formats_and_operand_identity() {
        use crate::kernel::{IntegerTerm, MachineIntegerConstant, MachineIntegerType, Variable};
        let native_cast = |source, destination, variable| MachineTerm::Cast {
            spelling: MachineCastSpelling::Generic,
            value: Box::new(MachineTerm::Variable(Variable(variable))),
            from: source,
            to: destination,
        };
        let cast = native_cast(
            MachineIntegerType::Int32,
            MachineIntegerType::Int64,
            891_001,
        );
        assert!(bitvector_equal(&cast, &cast.clone()));
        for other in [
            native_cast(
                MachineIntegerType::UInt32,
                MachineIntegerType::Int64,
                891_001,
            ),
            native_cast(
                MachineIntegerType::Int32,
                MachineIntegerType::UInt64,
                891_001,
            ),
            native_cast(
                MachineIntegerType::Int32,
                MachineIntegerType::Int64,
                891_002,
            ),
        ] {
            assert!(!bitvector_equal(&cast, &other));
        }
        let observed = |destination, variable| MachineTerm::IntegerToMachine {
            value: IntegerTerm::Variable(Variable(variable)).into(),
            destination,
        };
        let cast = observed(MachineIntegerType::Int64, 891_003);
        assert!(bitvector_equal(&cast, &cast.clone()));
        assert!(!bitvector_equal(
            &cast,
            &observed(MachineIntegerType::UInt64, 891_003)
        ));
        assert!(!bitvector_equal(
            &cast,
            &observed(MachineIntegerType::Int64, 891_004)
        ));
        let constant = |value| {
            MachineTerm::machine_constant(
                MachineIntegerConstant::from_integer(MachineIntegerType::Int128.format(), &value)
                    .unwrap(),
            )
        };
        assert!(bitvector_equal(&constant(1.into()), &constant(1.into())));
        assert!(!bitvector_equal(&constant(1.into()), &constant(2.into())));
    }

    fn int64_var(id: u64) -> MachineTerm {
        MachineTerm::Variable(crate::kernel::Variable(id))
    }

    fn int64_fact(condition: ConditionTerm, value: bool) -> Proposition {
        Proposition::ConditionIs(condition, value)
    }

    fn int64_defined_goal(left: MachineTerm, right: MachineTerm, subtract: bool) -> Proposition {
        let condition = if subtract {
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Subtract,
                left: Box::new(left),
                right: Box::new(right),
            }
        } else {
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int64,
                op: OverflowOperation::Add,
                left: Box::new(left),
                right: Box::new(right),
            }
        };
        Proposition::ConditionIs(condition, false)
    }

    fn check_int64_defined(
        goal: &Proposition,
        premises: &[Proposition],
        bounds: Vec<usize>,
    ) -> Result<(), SpecialArithmeticCheckError> {
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::SignedDefined {
                width: SignedDefinedWidth::Int64,
                bounds,
                result: goal.clone(),
            }],
            conclusion: 0,
        }
        .check(goal, premises)
    }

    #[test]
    fn int64_defined_follows_from_constant_bounds_on_both_operands() {
        let (a, b) = (int64_var(1), int64_var(2));
        let c = MachineTerm::int64_constant;
        let premises = vec![
            // `a < 100`, `b == 1`, `-5 <= a` spelled as `not (a < -5)`.
            int64_fact(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::LessThan,
                    left: Box::new(a.clone()),
                    right: Box::new(c(100)),
                },
                true,
            ),
            int64_fact(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::Equal,
                    left: Box::new(b.clone()),
                    right: Box::new(c(1)),
                },
                true,
            ),
            int64_fact(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::LessThan,
                    left: Box::new(a.clone()),
                    right: Box::new(c(-5)),
                },
                false,
            ),
        ];
        // `a + b <= 100`, and `a >= INT64_MIN` keeps the low end in range.
        let add = int64_defined_goal(a.clone(), b.clone(), false);
        assert_eq!(check_int64_defined(&add, &premises, vec![0, 1]), Ok(()));
        // `a - b` needs the lower bound on `a`: `INT64_MIN - 1` overflows.
        let subtract = int64_defined_goal(a.clone(), b.clone(), true);
        assert!(matches!(
            check_int64_defined(&subtract, &premises, vec![0, 1]),
            Err(SpecialArithmeticCheckError::SignedDefinedRangeExceeded { .. })
        ));
        assert_eq!(
            check_int64_defined(&subtract, &premises, vec![0, 1, 2]),
            Ok(())
        );
        // The certificate must conclude the goal it names.
        assert_eq!(
            check_int64_defined(&add, &premises, vec![0, 1]).and_then(|()| {
                SpecialArithmeticCertificate {
                    nodes: vec![SpecialArithmeticNode::SignedDefined {
                        width: SignedDefinedWidth::Int64,
                        bounds: vec![0, 1],
                        result: add.clone(),
                    }],
                    conclusion: 0,
                }
                .check(&subtract, &premises)
            }),
            Err(SpecialArithmeticCheckError::DoesNotFollow)
        );
    }

    #[test]
    fn int64_defined_uses_widening_ranges_and_refuses_unrelated_or_missing_bounds() {
        let tag =
            MachineTerm::legacy_cast(MachineCastSpelling::Int64FromUInt32, Box::new(int64_var(3)));
        let b = int64_var(4);
        let c = MachineTerm::int64_constant;
        let upper = int64_fact(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left: Box::new(b.clone()),
                right: Box::new(c(99)),
            },
            true,
        );
        let unrelated = int64_fact(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::LessEqual,
                left: Box::new(int64_var(5)),
                right: Box::new(c(0)),
            },
            true,
        );
        let premises = vec![upper, unrelated];
        // A widened `unsigned int` is in `[0, 2^32)`; only `b` needs a bound.
        let goal = int64_defined_goal(tag.clone(), b.clone(), false);
        assert_eq!(check_int64_defined(&goal, &premises, vec![0]), Ok(()));
        assert_eq!(
            check_int64_defined(&goal, &premises, vec![0, 1]),
            Err(SpecialArithmeticCheckError::SignedDefinedBoundUnrelated {
                node: 0,
                width: SignedDefinedWidth::Int64,
                premise: 1
            })
        );
        assert_eq!(
            check_int64_defined(&goal, &premises, vec![0, 0]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        );
        // Without the bound, `2^32 - 1 + INT64_MAX` leaves int64.
        assert!(matches!(
            check_int64_defined(&goal, &premises, vec![]),
            Err(SpecialArithmeticCheckError::SignedDefinedRangeExceeded { .. })
        ));
    }

    fn check_int32_defined(
        goal: &Proposition,
        premises: &[Proposition],
        bounds: Vec<usize>,
    ) -> Result<(), SpecialArithmeticCheckError> {
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::SignedDefined {
                width: SignedDefinedWidth::Int32,
                bounds,
                result: goal.clone(),
            }],
            conclusion: 0,
        }
        .check(goal, premises)
    }

    fn int32_defined_goal(left: MachineTerm, right: MachineTerm, subtract: bool) -> Proposition {
        let condition = if subtract {
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Subtract,
                left: Box::new(left),
                right: Box::new(right),
            }
        } else {
            ConditionTerm::Overflows {
                format: MachineIntegerType::Int32,
                op: OverflowOperation::Add,
                left: Box::new(left),
                right: Box::new(right),
            }
        };
        Proposition::ConditionIs(condition, false)
    }

    #[test]
    fn int32_defined_follows_from_constant_bounds_and_refuses_what_leaves_int32() {
        let (a, b) = (int64_var(1), int64_var(2));
        let c = |value: i32| MachineTerm::constant(value as u32);
        let premises = vec![
            // `a < 100`, `b == 1`, `-5 <= a` spelled as `not (a < -5)`.
            int64_fact(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(a.clone()),
                    right: Box::new(c(100)),
                },
                true,
            ),
            int64_fact(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(b.clone()),
                    right: Box::new(c(1)),
                },
                true,
            ),
            int64_fact(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(a.clone()),
                    right: Box::new(c(-5)),
                },
                false,
            ),
            // An `int64` bound on `a` is not an `int32` bound.
            int64_fact(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int64,
                    relation: CompareRelation::LessThan,
                    left: Box::new(a.clone()),
                    right: Box::new(MachineTerm::int64_constant(100)),
                },
                true,
            ),
        ];
        let add = int32_defined_goal(a.clone(), b.clone(), false);
        assert_eq!(check_int32_defined(&add, &premises, vec![0, 1]), Ok(()));
        // `a - b` needs the lower bound on `a`: `INT32_MIN - 1` overflows.
        let subtract = int32_defined_goal(a.clone(), b.clone(), true);
        assert_eq!(
            check_int32_defined(&subtract, &premises, vec![0, 1]),
            Err(SpecialArithmeticCheckError::SignedDefinedRangeExceeded {
                node: 0,
                width: SignedDefinedWidth::Int32,
                lower: i128::from(i32::MIN) - 1,
                upper: 98,
            })
        );
        assert_eq!(
            check_int32_defined(&subtract, &premises, vec![0, 1, 2]),
            Ok(())
        );
        // One bounded operand leaves the other its whole `int32` range.
        assert!(matches!(
            check_int32_defined(&add, &premises, vec![0]),
            Err(SpecialArithmeticCheckError::SignedDefinedRangeExceeded { .. })
        ));
        assert_eq!(
            check_int32_defined(&add, &premises, vec![0, 1, 3]),
            Err(SpecialArithmeticCheckError::SignedDefinedBoundUnrelated {
                node: 0,
                width: SignedDefinedWidth::Int32,
                premise: 3
            })
        );
        // The node's width must be the claim's own.
        assert_eq!(
            check_int64_defined(&add, &premises, vec![0, 1]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        );
        // A constant operand is its own range: `a + 7` needs only `a < 100`
        // and a lower bound on `a`.
        let constant = int32_defined_goal(a.clone(), c(7), false);
        assert!(matches!(
            check_int32_defined(&constant, &premises, vec![2]),
            Err(SpecialArithmeticCheckError::SignedDefinedRangeExceeded { .. })
        ));
        assert_eq!(check_int32_defined(&constant, &premises, vec![0]), Ok(()));
    }

    #[test]
    fn int32_defined_accepts_an_operands_own_definedness_only_from_a_cited_premise() {
        let (a, b) = (int64_var(1), int64_var(2));
        let c = |value: i32| MachineTerm::constant(value as u32);
        let sum = binary_node!(Int32, Add, Box::new(a.clone()), Box::new(b.clone()));
        // `defined((a + b) - 1)` lowers with the inner sum's own definedness.
        let inner = int32_defined_goal(a.clone(), b.clone(), false);
        let goal = Proposition::And(
            Box::new(int32_defined_goal(sum.clone(), c(1), true)),
            Box::new(inner.clone()),
        );
        let premises = vec![
            int64_fact(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::Equal,
                    left: Box::new(sum.clone()),
                    right: Box::new(c(5)),
                },
                true,
            ),
            inner.clone(),
        ];
        assert_eq!(check_int32_defined(&goal, &premises, vec![0, 1]), Ok(()));
        let Proposition::And(outer, inner) = &goal else {
            unreachable!()
        };
        let bounds =
            crate::kernel::machine_integer::definedness::integer_bounds_of_definedness(outer);
        let ordinary = Proposition::And(
            Box::new(Proposition::And(
                Box::new(bounds[0].clone()),
                Box::new(bounds[1].clone()),
            )),
            inner.clone(),
        );
        assert_eq!(
            check_int32_defined(&ordinary, &premises, vec![0, 1]),
            Ok(())
        );
        assert_eq!(
            check_int32_defined(&ordinary, &premises, vec![0]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        );
        // The inner conjunct is not the operation's overflow; without the
        // premise that states it, nothing establishes it.
        assert_eq!(
            check_int32_defined(&goal, &premises, vec![0]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        );
        // Two unrelated operations leave no single outermost one.
        let unrelated = Proposition::And(
            Box::new(int32_defined_goal(a.clone(), c(1), false)),
            Box::new(int32_defined_goal(b.clone(), c(1), false)),
        );
        assert_eq!(
            check_int32_defined(&unrelated, &premises, vec![0, 1]),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        );
    }

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

    fn tagged_tag_nodes(root: &Arc<TaggedTag<'_>>) -> usize {
        let mut pending = vec![Arc::clone(root)];
        let mut seen = HashSet::new();
        while let Some(tag) = pending.pop() {
            let identity = Arc::as_ptr(&tag) as usize;
            if !seen.insert(identity) {
                continue;
            }
            match &*tag {
                TaggedTag::Add(child, _)
                | TaggedTag::Subtract(child, _)
                | TaggedTag::BitwiseAnd(child, _)
                | TaggedTag::BitwiseOr(child, _) => pending.push(Arc::clone(child)),
                TaggedTag::Constant(_) | TaggedTag::Source(_) => {}
            }
        }
        seen.len()
    }

    fn deep_pointer(depth: usize) -> Pointer {
        let mut offset = PointerOffsetTerm::Constant(0);
        for _ in 0..depth {
            offset = add(offset, PointerOffsetTerm::Constant(1));
        }
        pointer(offset)
    }

    fn measured_tagged_form(pointer_depth: usize, tag_depth: usize) -> (bool, usize, usize) {
        let address = MachineTerm::PointerAddress(
            Box::new(deep_pointer(pointer_depth)),
            crate::kernel::AddressObjectClass::NONE,
        );
        let variable = MachineTerm::Variable(crate::kernel::Variable(394));
        let mut tagged = address;
        for index in 0..tag_depth {
            tagged = MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::Add,
                left: Box::new(tagged),
                right: Box::new(MachineTerm::Variable(crate::kernel::Variable(
                    (400 + index) as u64,
                ))),
            };
        }
        let alignments = AlignmentIndex::new(&[]).expect("empty alignment index");
        let (form, work) = crate::instrumentation::measure_deterministic_work(|| {
            tagged_form(
                (&variable).into(),
                ((&variable).into(), (&tagged).into()),
                &alignments,
            )
        });
        let nodes = form
            .as_ref()
            .map(|form| tagged_tag_nodes(&form.tag))
            .unwrap_or(0);
        (form.is_some(), work, nodes)
    }

    fn scaled(value: MachineTerm) -> PointerOffsetTerm {
        PointerOffsetTerm::scaled_int32_node(value, 4)
    }

    #[test]
    fn translation_certificate_checks_named_relation_and_bounds() {
        let p = PointerOffsetTerm::Variable(crate::kernel::Variable(100));
        let arr = PointerOffsetTerm::Variable(crate::kernel::Variable(101));
        let i = MachineTerm::Variable(crate::kernel::Variable(1));
        let n = MachineTerm::Variable(crate::kernel::Variable(2));
        let relation = pointer_eq(p.clone(), add(arr.clone(), scaled(i.clone())));
        let bound = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(i.clone()),
                right: Box::new(n.clone()),
            },
            true,
        );
        let goal = pointer_eq(
            add(p, PointerOffsetTerm::Constant(4)),
            add(
                arr,
                scaled(binary_node!(
                    Int32,
                    Add,
                    Box::new(i),
                    Box::new(MachineTerm::constant(1)),
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
    fn pointer_scalar_bounds_do_not_admit_native_width_operations() {
        let wide = MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Add,
            left: Box::new(MachineTerm::Variable(crate::kernel::Variable(1))),
            right: Box::new(MachineTerm::uint64_constant(1)),
        };
        let bound = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessThan,
                left: Box::new(wide),
                right: Box::new(MachineTerm::constant(i32::MAX as u32)),
            },
            true,
        );
        assert!(scalar_bounds(&[&bound]).is_none());
    }

    #[test]
    fn narrowed_chunk_offset_translation_requires_the_named_bound() {
        let n = MachineTerm::Variable(crate::kernel::Variable(1));
        let index = MachineTerm::uint32_from_64(MachineTerm::uint64_subtract(
            n.clone(),
            MachineTerm::uint64_remainder(n, MachineTerm::uint64_constant(4)),
        ));
        let p = PointerOffsetTerm::Variable(crate::kernel::Variable(100));
        let arr = PointerOffsetTerm::Variable(crate::kernel::Variable(101));
        let relation = pointer_eq(p.clone(), add(arr.clone(), scaled(index.clone())));
        let goal = pointer_eq(
            add(p, PointerOffsetTerm::Constant(4)),
            add(
                arr,
                scaled(MachineTerm::add(index.clone(), MachineTerm::constant(1))),
            ),
        );
        let bound = Proposition::ConditionIs(
            ConditionTerm::signed_less_than(index, MachineTerm::constant(i32::MAX as u32)),
            true,
        );
        let certificate = |bounds| SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerTranslation {
                relation: 0,
                bounds,
                result: goal.clone(),
            }],
            conclusion: 0,
        };
        assert!(
            certificate(vec![1])
                .check(&goal, &[relation.clone(), bound])
                .is_ok()
        );
        assert!(certificate(vec![]).check(&goal, &[relation]).is_err());
    }

    #[test]
    fn special_certificate_rejects_duplicate_reference_lists() {
        let relation = pointer_eq(
            PointerOffsetTerm::Constant(0),
            PointerOffsetTerm::Constant(0),
        );
        let bound = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int32,
                relation: CompareRelation::LessEqual,
                left: Box::new(MachineTerm::constant(0)),
                right: Box::new(MachineTerm::constant(1)),
            },
            true,
        );
        assert!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerTranslation {
                    relation: 0,
                    bounds: vec![1, 1],
                    result: relation.clone(),
                }],
                conclusion: 0,
            }
            .check(&relation, &[relation.clone(), bound])
            .is_err(),
            "translation bounds must not repeat a premise"
        );

        let pointer = pointer(PointerOffsetTerm::Constant(0));
        let address = MachineTerm::PointerAddress(
            Box::new(pointer.clone()),
            crate::kernel::AddressObjectClass::NONE,
        );
        let word_relation = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::Variable(crate::kernel::Variable(901)),
                MachineTerm::uint64_add(address.clone(), MachineTerm::uint64_constant(1)),
            ),
            true,
        );
        let alignment = Proposition::ConditionIs(ConditionTerm::pointer_aligned(pointer, 8), true);
        let goal = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_or(
                    MachineTerm::Variable(crate::kernel::Variable(901)),
                    MachineTerm::uint64_constant(2),
                ),
                MachineTerm::uint64_add(address, MachineTerm::uint64_constant(3)),
            ),
            true,
        );
        assert!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                    relation: 0,
                    alignments: vec![1, 1],
                    result: goal.clone(),
                }],
                conclusion: 0,
            }
            .check(&goal, &[word_relation, alignment])
            .is_err(),
            "tagged-word alignment evidence must not repeat a premise"
        );
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
            let null_condition = ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::BitwiseAnd,
                    left: Box::new(MachineTerm::PointerAddress(
                        Box::new(Pointer::null()),
                        crate::kernel::AddressObjectClass::NONE,
                    )),
                    right: Box::new(MachineTerm::uint64_constant(alignment - 1)),
                }),
                right: Box::new(MachineTerm::uint64_constant(0)),
            };
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
    fn alignment_certificate_drops_aligned_symbolic_scaled_displacement() {
        let base = pointer(PointerOffsetTerm::Variable(crate::kernel::Variable(710)));
        let aligned_base =
            Proposition::ConditionIs(ConditionTerm::pointer_aligned(base.clone(), 8), true);
        let scaled = PointerOffsetTerm::scaled_int32_node(
            MachineTerm::Variable(crate::kernel::Variable(711)),
            8,
        );
        let goal_pointer = Pointer {
            block: base.block.clone(),
            offset: PointerOffsetTerm::Add(Box::new(base.offset.clone()), Box::new(scaled)),
        };
        let goal = Proposition::ConditionIs(ConditionTerm::pointer_aligned(goal_pointer, 8), true);
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerAlignment {
                premise: Some(0),
                result: goal.clone(),
            }],
            conclusion: 0,
        }
        .check(&goal, std::slice::from_ref(&aligned_base))
        .unwrap();

        let unaligned_scaled = PointerOffsetTerm::scaled_int32_node(
            MachineTerm::Variable(crate::kernel::Variable(712)),
            4,
        );
        let negative_pointer = Pointer {
            block: base.block,
            offset: PointerOffsetTerm::Add(Box::new(base.offset), Box::new(unaligned_scaled)),
        };
        let negative =
            Proposition::ConditionIs(ConditionTerm::pointer_aligned(negative_pointer, 8), false);
        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerAlignment {
                    premise: Some(0),
                    result: negative.clone(),
                }],
                conclusion: 0,
            }
            .check(&negative, std::slice::from_ref(&aligned_base)),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));
    }

    #[test]
    fn retained_masked_read_equation_checks_native_pointer_goal() {
        use crate::kernel::MachineOperandView;
        let _session = crate::kernel::VerificationSession::enter();
        let next = pointer(PointerOffsetTerm::Constant(0));
        let address = MachineTerm::pointer_address(next.clone());
        let raw = MachineTerm::MemoryLoad(
            crate::kernel::intern_memory(crate::kernel::Memory::new()),
            Box::new(next.clone()),
            crate::kernel::LoadKind::Bits64,
        );
        let tagged = MachineTerm::uint64_add(
            address.clone(),
            MachineTerm::uint64_bitwise_and(raw.clone(), MachineTerm::uint64_constant(1)),
        );
        let roots = [&raw, &tagged].map(|word| {
            crate::kernel::KernelTerm::retained_machine_operand(
                MachineIntegerType::UInt64,
                MachineOperandView::Legacy(word),
            )
        });
        let relation = Proposition::ConditionIs(
            crate::kernel::machine_integer::comparison::condition_for_operand_views(
                MachineIntegerType::UInt64,
                CompareRelation::Equal,
                roots.each_ref().map(MachineOperandView::Shared),
            ),
            true,
        );
        let alignment = Proposition::ConditionIs(ConditionTerm::pointer_aligned(next, 8), true);
        let goal = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                address,
                MachineTerm::uint64_bitwise_and(raw, MachineTerm::uint64_constant(!1)),
            ),
            true,
        );
        let exports = crate::kernel::KernelTermExport::machine_export_count();
        assert!(pointer_word_equality(&relation, &[&alignment], &goal));
        assert_eq!(
            crate::kernel::KernelTermExport::machine_export_count(),
            exports
        );
    }

    #[test]
    fn tagged_word_certificate_requires_exact_alignment() {
        let next = pointer(PointerOffsetTerm::Constant(0));
        let address = MachineTerm::PointerAddress(
            Box::new(next.clone()),
            crate::kernel::AddressObjectClass::NONE,
        );
        let relation = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::Variable(crate::kernel::Variable(10)),
                MachineTerm::uint64_add(address.clone(), MachineTerm::uint64_constant(1)),
            ),
            true,
        );
        let alignment = Proposition::ConditionIs(ConditionTerm::pointer_aligned(next, 8), true);
        let goal = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_or(
                    MachineTerm::Variable(crate::kernel::Variable(10)),
                    MachineTerm::uint64_constant(2),
                ),
                MachineTerm::uint64_add(address, MachineTerm::uint64_constant(3)),
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
        let word = MachineTerm::Variable(crate::kernel::Variable(11));
        let direct_address = MachineTerm::PointerAddress(
            Box::new(pointer(PointerOffsetTerm::Constant(0))),
            crate::kernel::AddressObjectClass::NONE,
        );
        let direct_tag =
            MachineTerm::uint64_bitwise_and(word.clone(), MachineTerm::uint64_constant(1));
        let direct = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                word.clone(),
                MachineTerm::uint64_add(direct_address.clone(), direct_tag.clone()),
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

        // The parent-word consumer masks off the low two tag bits.  The
        // masked symbolic tag is discharged by the local disjoint-mask rule;
        // no ambient pointer-word decision procedure is needed.
        let masked_parent_word = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_and(word.clone(), MachineTerm::uint64_constant(!3)),
                direct_address.clone(),
            ),
            true,
        );
        let parent_alignment = Proposition::ConditionIs(
            ConditionTerm::pointer_aligned(pointer(PointerOffsetTerm::Constant(0)), 4),
            true,
        );
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordEquality {
                relation: 0,
                alignments: vec![1],
                result: masked_parent_word.clone(),
            }],
            conclusion: 0,
        }
        .check(
            &masked_parent_word,
            &[direct.clone(), parent_alignment.clone()],
        )
        .unwrap();

        let set_parent_word = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_or(
                    MachineTerm::uint64_bitwise_and(word.clone(), MachineTerm::uint64_constant(1)),
                    direct_address.clone(),
                ),
                MachineTerm::uint64_add(
                    direct_address.clone(),
                    MachineTerm::uint64_bitwise_and(word.clone(), MachineTerm::uint64_constant(1)),
                ),
            ),
            true,
        );
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordFromAlignment {
                alignments: vec![0],
                result: set_parent_word.clone(),
            }],
            conclusion: 0,
        }
        .check(&set_parent_word, std::slice::from_ref(&parent_alignment))
        .unwrap();

        let wrong_mask = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                word.clone(),
                MachineTerm::uint64_add(
                    direct_address.clone(),
                    MachineTerm::uint64_bitwise_and(word.clone(), MachineTerm::uint64_constant(3)),
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
    fn direct_tagged_word_certificate_uses_only_alignment_evidence() {
        let next = pointer(PointerOffsetTerm::Constant(0));
        let address = MachineTerm::PointerAddress(
            Box::new(next.clone()),
            crate::kernel::AddressObjectClass::NONE,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_or(
                    MachineTerm::uint64_add(address.clone(), MachineTerm::uint64_constant(1)),
                    MachineTerm::uint64_constant(2),
                ),
                MachineTerm::uint64_add(address, MachineTerm::uint64_constant(3)),
            ),
            true,
        );
        let alignment = Proposition::ConditionIs(ConditionTerm::pointer_aligned(next, 8), true);
        SpecialArithmeticCertificate {
            nodes: vec![SpecialArithmeticNode::PointerWordFromAlignment {
                alignments: vec![0],
                result: goal.clone(),
            }],
            conclusion: 0,
        }
        .check(&goal, std::slice::from_ref(&alignment))
        .unwrap();

        let unrelated = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::Variable(crate::kernel::Variable(901)),
                MachineTerm::PointerAddress(
                    Box::new(pointer(PointerOffsetTerm::Constant(0))),
                    crate::kernel::AddressObjectClass::NONE,
                ),
            ),
            true,
        );
        assert!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordFromAlignment {
                    alignments: vec![0],
                    result: unrelated.clone(),
                }],
                conclusion: 0,
            }
            .check(&unrelated, std::slice::from_ref(&alignment))
            .is_err(),
            "alignment evidence cannot establish an unrelated symbolic word"
        );

        for alignments in [vec![], vec![0, 0], vec![1], vec![2]] {
            assert!(
                SpecialArithmeticCertificate {
                    nodes: vec![SpecialArithmeticNode::PointerWordFromAlignment {
                        alignments,
                        result: goal.clone(),
                    }],
                    conclusion: 0,
                }
                .check(&goal, std::slice::from_ref(&alignment))
                .is_err(),
                "malformed alignment references must be rejected"
            );
        }
        assert!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordFromAlignment {
                    alignments: vec![1],
                    result: goal.clone(),
                }],
                conclusion: 0,
            }
            .check(&goal, &[alignment.clone(), goal.clone()])
            .is_err(),
            "a word equality is not alignment evidence"
        );

        let tampered = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_bitwise_or(
                    MachineTerm::uint64_add(
                        MachineTerm::PointerAddress(
                            Box::new(pointer(PointerOffsetTerm::Constant(0))),
                            crate::kernel::AddressObjectClass::NONE,
                        ),
                        MachineTerm::uint64_constant(1),
                    ),
                    MachineTerm::uint64_constant(4),
                ),
                MachineTerm::uint64_add(
                    MachineTerm::PointerAddress(
                        Box::new(pointer(PointerOffsetTerm::Constant(0))),
                        crate::kernel::AddressObjectClass::NONE,
                    ),
                    MachineTerm::uint64_constant(4),
                ),
            ),
            true,
        );
        assert!(matches!(
            SpecialArithmeticCertificate {
                nodes: vec![SpecialArithmeticNode::PointerWordFromAlignment {
                    alignments: vec![0],
                    result: tampered.clone(),
                }],
                conclusion: 0,
            }
            .check(&tampered, std::slice::from_ref(&alignment)),
            Err(SpecialArithmeticCheckError::NodeResultMismatch(0))
        ));
    }

    #[test]
    fn finite_float_certificate_rejects_wrong_width_expression_and_operator() {
        let value = MachineTerm::Variable(crate::kernel::Variable(22));
        let finite = Proposition::ConditionIs(
            ConditionTerm::float32_classification(value.clone(), FloatClassification::Finite),
            true,
        );
        let good = Proposition::ConditionIs(
            ConditionTerm::float32_compare(value.clone(), value.clone(), ComparisonOperator::Equal),
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
            ConditionTerm::float32_compare(value.clone(), value, ComparisonOperator::LessThan),
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
    fn tagged_word_negative_result_needs_distinct_constant_tags() {
        let pointer = pointer(PointerOffsetTerm::Constant(0));
        let address =
            MachineTerm::PointerAddress(Box::new(pointer), crate::kernel::AddressObjectClass::NONE);
        let word = MachineTerm::Variable(crate::kernel::Variable(30));
        let relation = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                word,
                MachineTerm::uint64_add(address.clone(), MachineTerm::uint64_constant(1)),
            ),
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::uint64_equal(
                MachineTerm::uint64_add(address.clone(), MachineTerm::uint64_constant(1)),
                MachineTerm::uint64_add(address, MachineTerm::uint64_constant(2)),
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
        let left = MachineTerm::Variable(crate::kernel::Variable(80));
        let right = MachineTerm::Variable(crate::kernel::Variable(81));
        let relation = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(left.clone()),
                right: Box::new(right.clone()),
            },
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
    fn tagged_word_tag_arena_stays_linear_for_deep_symbolic_chains() {
        let alignments = AlignmentIndex::new(&[]).expect("empty alignment index");
        let mut previous = 0;
        for depth in [4, 16, 64, 256, 1024] {
            let address = MachineTerm::PointerAddress(
                Box::new(pointer(PointerOffsetTerm::Constant(0))),
                crate::kernel::AddressObjectClass::NONE,
            );
            let variable = MachineTerm::Variable(crate::kernel::Variable(294));
            let mut tagged = address;
            for index in 0..depth {
                tagged = MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::Add,
                    left: Box::new(tagged),
                    right: Box::new(MachineTerm::Variable(crate::kernel::Variable(300 + index))),
                };
            }
            let form = tagged_form(
                (&variable).into(),
                ((&variable).into(), (&tagged).into()),
                &alignments,
            )
            .expect("the relation should provide a tagged form");
            let nodes = tagged_tag_nodes(&form.tag);
            assert_eq!(nodes, depth as usize);
            assert!(nodes >= previous);
            previous = nodes;
        }
    }

    #[test]
    fn tagged_form_shares_deep_pointer_payload_across_tag_depth() {
        let (small_valid, small_work, small_nodes) = measured_tagged_form(4, 4);
        let (deep_pointer_valid, deep_pointer_work, deep_pointer_nodes) =
            measured_tagged_form(64, 4);
        let (deep_tags_valid, deep_tags_work, deep_tags_nodes) = measured_tagged_form(4, 64);
        let (cross_valid, cross_work, cross_nodes) = measured_tagged_form(64, 64);

        assert!(small_valid && deep_pointer_valid && deep_tags_valid && cross_valid);
        assert_eq!(small_nodes, 4);
        assert_eq!(deep_pointer_nodes, 4);
        assert_eq!(deep_tags_nodes, 64);
        assert_eq!(cross_nodes, 64);

        // Sharing the pointer payload makes the two dimensions additive.  A
        // pointer clone at every tag node would make the cross case grow like
        // pointer_depth * tag_depth and violate this bound by a wide margin.
        let additive_bound = small_work
            .saturating_add(deep_pointer_work)
            .saturating_add(deep_tags_work)
            .saturating_add(64);
        assert!(
            cross_work <= additive_bound,
            "cross-product work was not additive: small={small_work}, pointer={deep_pointer_work}, tags={deep_tags_work}, cross={cross_work}"
        );
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
        let address = MachineTerm::PointerAddress(
            Box::new(normal_pointer.clone()),
            crate::kernel::AddressObjectClass::NONE,
        );
        let word = MachineTerm::Variable(crate::kernel::Variable(92));
        let relation = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(word.clone()),
                right: Box::new(MachineTerm::uint64_add(
                    address.clone(),
                    MachineTerm::uint64_constant(1),
                )),
            },
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
        let mut value = MachineTerm::Variable(crate::kernel::Variable(90));
        for _ in 0..=MAX_TERM_PAYLOAD {
            value = binary_node!(
                Int32,
                Add,
                Box::new(value),
                Box::new(MachineTerm::constant(1))
            );
        }
        let finite = Proposition::ConditionIs(
            ConditionTerm::float32_classification(value.clone(), FloatClassification::Finite),
            true,
        );
        let goal = Proposition::ConditionIs(
            ConditionTerm::float32_compare(value.clone(), value, ComparisonOperator::Equal),
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
        let mut mask = MachineTerm::uint64_constant(7);
        for _ in 0..=MAX_TERM_PAYLOAD {
            mask = MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseOr,
                left: Box::new(mask),
                right: Box::new(MachineTerm::uint64_constant(0)),
            };
        }
        let deep_alignment = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::BitwiseAnd,
                    left: Box::new(MachineTerm::PointerAddress(
                        Box::new(heap_pointer(PointerOffsetTerm::Constant(0))),
                        crate::kernel::AddressObjectClass::NONE,
                    )),
                    right: Box::new(mask),
                }),
                right: Box::new(MachineTerm::uint64_constant(0)),
            },
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

        let word = MachineTerm::Variable(crate::kernel::Variable(93));
        let address = MachineTerm::PointerAddress(
            Box::new(pointer(PointerOffsetTerm::Constant(0))),
            crate::kernel::AddressObjectClass::NONE,
        );
        let relation = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(word.clone()),
                right: Box::new(MachineTerm::uint64_add(
                    address.clone(),
                    MachineTerm::uint64_constant(1),
                )),
            },
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
        let mut mask = MachineTerm::uint64_constant(7);
        for _ in 0..=MAX_TERM_PAYLOAD {
            mask = MachineTerm::Binary {
                format: MachineIntegerType::UInt64,
                op: MachineBinaryOp::BitwiseOr,
                left: Box::new(mask),
                right: Box::new(MachineTerm::uint64_constant(0)),
            };
        }
        let goal = Proposition::ConditionIs(
            ConditionTerm::Compare {
                format: MachineIntegerType::Int64,
                relation: CompareRelation::Equal,
                left: Box::new(MachineTerm::Binary {
                    format: MachineIntegerType::UInt64,
                    op: MachineBinaryOp::BitwiseAnd,
                    left: Box::new(MachineTerm::PointerAddress(
                        Box::new(heap_pointer(PointerOffsetTerm::Constant(0))),
                        crate::kernel::AddressObjectClass::NONE,
                    )),
                    right: Box::new(mask),
                }),
                right: Box::new(MachineTerm::uint64_constant(0)),
            },
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

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/kernel/proof/arithmetic_special/tests.rs");
    }
}

#[cfg(test)]
mod unsigned_widening_tests {
    use super::*;
    use crate::kernel::Variable;

    #[test]
    fn widened_operand_identity_preserves_leaf_and_conversion_identity() {
        let value = MachineTerm::Variable(Variable(994_101));
        let widened =
            MachineTerm::legacy_cast(MachineCastSpelling::UInt64From32, Box::new(value.clone()));
        assert!(bitvector_equal(&widened, &widened));
        assert!(!bitvector_equal(
            &widened,
            &MachineTerm::legacy_cast(
                MachineCastSpelling::UInt64From32,
                Box::new(MachineTerm::Variable(Variable(994_102)))
            )
        ));
        assert!(!bitvector_equal(
            &widened,
            &MachineTerm::legacy_cast(
                MachineCastSpelling::Int64FromUInt32,
                Box::new(value.clone())
            )
        ));
        assert!(!bitvector_equal(&widened, &value));
        let mut deep = value;
        for _ in 0..MAX_TERM_PAYLOAD {
            deep = MachineTerm::legacy_cast(MachineCastSpelling::UInt64From32, Box::new(deep));
        }
        assert!(!bitvector_equal(&deep, &deep));
    }
}
