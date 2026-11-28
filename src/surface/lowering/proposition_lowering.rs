use super::*;
use crate::kernel::{CompareRelation, MachineIntegerType, StoredConditionTerm};
use crate::kernel::{binary_node, unary_node};
use crate::kernel::{binary_term, unary_term};
use crate::kernel::{bits32_constant, constant_u32, int32_constant};

/// Two lowered operands whose C types have no common comparison, named by
/// value and type rather than as kernel term dumps.
fn incomparable_values(left: &ProgramValue, right: &ProgramValue) -> ClickError {
    let describe = |value: &ProgramValue| {
        format!(
            "`{}` of type `{}`",
            crate::surface::diagnostics::describe_program_value(value, ParameterBinding::default()),
            crate::kernel::program_type_spelling(value.program_type())
        )
    };
    ClickError::new(format!(
        "cannot compare {} with {} in a proposition",
        describe(left),
        describe(right)
    ))
}

pub(in crate::surface) fn comparison_proposition(
    left: ProgramValue,
    operator: ComparisonOperator,
    right: ProgramValue,
) -> Result<Proposition, ClickError> {
    let left = left.numeric_value().clone();
    let right = right.numeric_value().clone();
    let pointer_and_null = match (&left, &right) {
        (ProgramValue::Pointer(pointer), ProgramValue::Int32(bits32_constant!(0))) => {
            Some((pointer.address().clone(), Address::null()))
        }
        (ProgramValue::Int32(int32_constant!(0)), ProgramValue::Pointer(pointer)) => {
            Some((Address::null(), pointer.address().clone()))
        }
        _ => None,
    };
    if let Some((left, right)) = pointer_and_null {
        let value = match operator {
            ComparisonOperator::Equal => true,
            ComparisonOperator::NotEqual => false,
            _ => {
                return Err(ClickError::new(
                    "pointer propositions support only `==` and `!=`",
                ));
            }
        };
        return Ok(Proposition::condition_is(
            StoredConditionTerm::address_equal(&left, &right),
            value,
        ));
    }
    // A slice is one value, not its data pointer: comparing it with a thin
    // pointer is written on `s.as_ptr()` (`design/rust-slice-values.md`,
    // "Source compatibility").
    if let (ProgramValue::Pointer(left_pointer), ProgramValue::Pointer(right_pointer)) =
        (&left, &right)
        && left_pointer.is_wide() != right_pointer.is_wide()
        && !left_pointer.is_null()
        && !right_pointer.is_null()
    {
        let slice = if left_pointer.is_wide() {
            &left
        } else {
            &right
        };
        let written =
            crate::surface::diagnostics::describe_program_value(slice, ParameterBinding::default());
        return Err(ClickError::new(format!(
            "`{written}` is a slice, not a pointer: a pointer comparison is written on its data pointer, `.as_ptr()`, as in `{written}.as_ptr() == p`"
        ))
        .with_kind(ClickErrorKind::Type));
    }
    if let (ProgramValue::Pointer(left), ProgramValue::Pointer(right)) = (&left, &right)
        && (left
            .program_type()
            .pointer_types_compatible(right.program_type())
            || left.is_null()
            || right.is_null())
    {
        let value = match operator {
            ComparisonOperator::Equal => true,
            ComparisonOperator::NotEqual => false,
            _ => {
                return Err(ClickError::new(
                    "pointer propositions support only `==` and `!=`",
                ));
            }
        };
        if !left.is_null() && !right.is_null() {
            return Ok(Proposition::condition_is(
                StoredConditionTerm::pointer_equal(left, right),
                value,
            ));
        }
        return Ok(Proposition::condition_is(
            StoredConditionTerm::address_equal(left.address(), right.address()),
            value,
        ));
    }
    if matches!(left, ProgramValue::UInt64(_)) || matches!(right, ProgramValue::UInt64(_)) {
        let (Some(left), Some(right)) = (promoted_uint64_term(&left), promoted_uint64_term(&right))
        else {
            return Err(incomparable_values(&left, &right));
        };
        let condition = match operator {
            ComparisonOperator::Equal | ComparisonOperator::NotEqual => {
                OldConditionTerm::uint64_equal(left, right)
            }
            ComparisonOperator::LessThan => OldConditionTerm::uint64_less_than(left, right),
            ComparisonOperator::LessEqual => OldConditionTerm::uint64_less_equal(left, right),
            ComparisonOperator::GreaterThan => OldConditionTerm::uint64_greater_than(left, right),
            ComparisonOperator::GreaterEqual => OldConditionTerm::uint64_greater_equal(left, right),
            ComparisonOperator::In => {
                return Err(ClickError::new("membership is not a scalar comparison"));
            }
        };
        return Ok(Proposition::condition_is(
            condition,
            !matches!(operator, ComparisonOperator::NotEqual),
        ));
    }
    if matches!(left, ProgramValue::Int64(_)) || matches!(right, ProgramValue::Int64(_)) {
        let (Some(left), Some(right)) = (promoted_int64_term(&left), promoted_int64_term(&right))
        else {
            return Err(incomparable_values(&left, &right));
        };
        let condition = match operator {
            ComparisonOperator::Equal | ComparisonOperator::NotEqual => {
                OldConditionTerm::int64_equal(left, right)
            }
            ComparisonOperator::LessThan => OldConditionTerm::int64_signed_less_than(left, right),
            ComparisonOperator::LessEqual => OldConditionTerm::int64_signed_less_equal(left, right),
            ComparisonOperator::GreaterThan => {
                OldConditionTerm::int64_signed_greater_than(left, right)
            }
            ComparisonOperator::GreaterEqual => {
                OldConditionTerm::int64_signed_greater_equal(left, right)
            }
            ComparisonOperator::In => {
                return Err(ClickError::new("membership is not a scalar comparison"));
            }
        };
        return Ok(Proposition::condition_is(
            condition,
            !matches!(operator, ComparisonOperator::NotEqual),
        ));
    }
    // A 32-bit comparison reads its operands at its own format, as the
    // kernel's specification comparisons do (`program_value_word32_term`).
    let unsigned = matches!(
        (&left, &right),
        (ProgramValue::UInt32(_), _) | (_, ProgramValue::UInt32(_))
    );
    let format = if unsigned {
        MachineIntegerType::UInt32
    } else {
        MachineIntegerType::Int32
    };
    let word = |value: &ProgramValue| {
        crate::kernel::program_value_word32_term(value, format)
            .map(|term| normalize_bitvector(&term))
    };
    if let (Some(left_term), Some(right_term)) = (word(&left), word(&right)) {
        let Some((condition, value)) =
            comparison_condition(left_term, operator, right_term, unsigned)
        else {
            return Err(ClickError::new("unsupported proposition comparison"));
        };
        Ok(Proposition::condition_is(condition, value))
    } else {
        Err(incomparable_values(&left, &right))
    }
}

pub(in crate::surface) fn spec_range_membership_proposition(
    start: SpecExpression,
    item: SpecExpression,
    end: SpecExpression,
) -> SpecProposition {
    SpecProposition::And(
        Box::new(SpecProposition::Comparison {
            left: start,
            operator: KernelComparisonOperator::LessEqual,
            right: item.clone(),
        }),
        Box::new(SpecProposition::Comparison {
            left: item,
            operator: KernelComparisonOperator::LessThan,
            right: end,
        }),
    )
}

fn promoted_int64_term(value: &ProgramValue) -> Option<OldMachineTerm> {
    match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Int64(bits) => Some(bits.clone()),
        ProgramValue::Bool(bits) => Some(OldMachineTerm::int64_from_32(bits.clone())),
        ProgramValue::Int8(bits) => Some(OldMachineTerm::int64_from_32(bits.clone())),
        ProgramValue::Int16(bits)
        | ProgramValue::Int32(bits)
        | ProgramValue::UInt8(bits)
        | ProgramValue::UInt16(bits) => Some(OldMachineTerm::int64_from_32(bits.clone())),
        ProgramValue::UInt32(bits) => Some(OldMachineTerm::int64_from_uint32(bits.clone())),
        ProgramValue::Int128(_)
        | ProgramValue::UInt128(_)
        | ProgramValue::Void
        | ProgramValue::UInt64(_)
        | ProgramValue::Pointer(_)
        | ProgramValue::Parameter(_)
        | ProgramValue::Float32(_)
        | ProgramValue::Float64(_) => None,
    }
}

fn promoted_uint64_term(value: &ProgramValue) -> Option<OldMachineTerm> {
    match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::UInt64(bits) => Some(bits.clone()),
        ProgramValue::Bool(bits) => Some(OldMachineTerm::uint64_from_32(bits.clone())),
        ProgramValue::Int64(bits) => Some(OldMachineTerm::uint64_from_int64(bits.clone())),
        ProgramValue::Int8(bits) => Some(OldMachineTerm::uint64_from_int32(bits.clone())),
        ProgramValue::Int16(bits)
        | ProgramValue::Int32(bits)
        | ProgramValue::UInt8(bits)
        | ProgramValue::UInt16(bits) => Some(OldMachineTerm::uint64_from_int32(bits.clone())),
        ProgramValue::UInt32(bits) => Some(OldMachineTerm::uint64_from_32(bits.clone())),
        ProgramValue::Int128(_)
        | ProgramValue::UInt128(_)
        | ProgramValue::Void
        | ProgramValue::Pointer(_)
        | ProgramValue::Parameter(_)
        | ProgramValue::Float32(_)
        | ProgramValue::Float64(_) => None,
    }
}

pub(in crate::surface) fn bitvector32_add(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldMachineTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            OldMachineTerm::constant(constant_u32(*left).wrapping_add(constant_u32(*right)))
        }
        (int32_constant!(constant), binary_term!(Int32, Subtract, base, subtrahend))
            if subtrahend.as_ref() == &OldMachineTerm::constant(constant_u32(*constant)) =>
        {
            base.as_ref().clone()
        }
        (binary_term!(Int32, Subtract, base, subtrahend), bits32_constant!(constant))
            if subtrahend.as_ref() == &OldMachineTerm::constant(constant_u32(*constant)) =>
        {
            base.as_ref().clone()
        }
        (
            binary_term!(Int32, Subtract, zero, subtrahend),
            binary_term!(Int32, Add, base, addend),
        ) if zero.as_ref() == &OldMachineTerm::constant(0) && subtrahend == base => {
            addend.as_ref().clone()
        }
        (
            binary_term!(Int32, Subtract, zero, subtrahend),
            binary_term!(Int32, Add, addend, base),
        ) if zero.as_ref() == &OldMachineTerm::constant(0) && subtrahend == base => {
            addend.as_ref().clone()
        }
        (
            binary_term!(Int32, Add, base, addend),
            binary_term!(Int32, Subtract, zero, subtrahend),
        ) if zero.as_ref() == &OldMachineTerm::constant(0) && base == subtrahend => {
            addend.as_ref().clone()
        }
        (
            binary_term!(Int32, Add, addend, base),
            binary_term!(Int32, Subtract, zero, subtrahend),
        ) if zero.as_ref() == &OldMachineTerm::constant(0) && base == subtrahend => {
            addend.as_ref().clone()
        }
        (_, bits32_constant!(0)) => left,
        (int32_constant!(0), _) => right,
        _ => binary_node!(Int32, Add, Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_subtract(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldMachineTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            OldMachineTerm::constant(constant_u32(*left).wrapping_sub(constant_u32(*right)))
        }
        (_, bits32_constant!(0)) => left,
        _ if left == right => OldMachineTerm::constant(0),
        (
            binary_term!(Int32, Add, left_base, left_addend),
            binary_term!(Int32, Add, right_base, right_addend),
        ) if left_base == right_base => {
            bitvector32_subtract(left_addend.as_ref().clone(), right_addend.as_ref().clone())
        }
        (
            binary_term!(Int32, Add, left_base, left_addend),
            binary_term!(Int32, Add, right_base, right_addend),
        ) if left_base == right_addend => {
            bitvector32_subtract(left_addend.as_ref().clone(), right_base.as_ref().clone())
        }
        (
            binary_term!(Int32, Add, left_base, left_addend),
            binary_term!(Int32, Add, right_base, right_addend),
        ) if left_addend == right_base => {
            bitvector32_subtract(left_base.as_ref().clone(), right_addend.as_ref().clone())
        }
        (
            binary_term!(Int32, Add, left_base, left_addend),
            binary_term!(Int32, Add, right_base, right_addend),
        ) if left_addend == right_addend => {
            bitvector32_subtract(left_base.as_ref().clone(), right_base.as_ref().clone())
        }
        (binary_term!(Int32, Add, left_base, left_addend), _) if left_base.as_ref() == &right => {
            left_addend.as_ref().clone()
        }
        (binary_term!(Int32, Add, left_base, left_addend), _) if left_addend.as_ref() == &right => {
            left_base.as_ref().clone()
        }
        (_, binary_term!(Int32, Add, right_base, right_addend)) if &left == right_base.as_ref() => {
            bitvector32_subtract(OldMachineTerm::constant(0), right_addend.as_ref().clone())
        }
        (_, binary_term!(Int32, Add, right_base, right_addend))
            if &left == right_addend.as_ref() =>
        {
            bitvector32_subtract(OldMachineTerm::constant(0), right_base.as_ref().clone())
        }
        _ => binary_node!(Int32, Subtract, Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_multiply(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldMachineTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            OldMachineTerm::constant(constant_u32(*left).wrapping_mul(constant_u32(*right)))
        }
        (_, bits32_constant!(1)) => left,
        (int32_constant!(1), _) => right,
        (_, bits32_constant!(0)) | (int32_constant!(0), _) => OldMachineTerm::constant(0),
        _ => binary_node!(Int32, Multiply, Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_divide(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> Result<OldMachineTerm, String> {
    match (&left, &right) {
        (_, bits32_constant!(0)) => Err("division by zero in proposition".to_string()),
        (bits32_constant!(left), bits32_constant!(right))
            if constant_u32(*left) == i32::MIN as u32 && constant_u32(*right) == (-1i32) as u32 =>
        {
            Err("signed division overflow in proposition".to_string())
        }
        (bits32_constant!(left), bits32_constant!(right)) => Ok(OldMachineTerm::constant(
            ((constant_u32(*left) as i32) / (constant_u32(*right) as i32)) as u32,
        )),
        (_, bits32_constant!(1)) => Ok(left),
        _ => Ok(binary_node!(Int32, Divide, Box::new(left), Box::new(right))),
    }
}

pub(in crate::surface) fn bitvector32_remainder(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> Result<OldMachineTerm, String> {
    match (&left, &right) {
        (_, bits32_constant!(0)) => Err("division by zero in proposition".to_string()),
        (bits32_constant!(left), bits32_constant!(right))
            if constant_u32(*left) == i32::MIN as u32 && constant_u32(*right) == (-1i32) as u32 =>
        {
            Err("signed division overflow in proposition".to_string())
        }
        (bits32_constant!(left), bits32_constant!(right)) => Ok(OldMachineTerm::constant(
            ((constant_u32(*left) as i32) % (constant_u32(*right) as i32)) as u32,
        )),
        (_, bits32_constant!(1)) => Ok(OldMachineTerm::constant(0)),
        _ => Ok(binary_node!(
            Int32,
            Remainder,
            Box::new(left),
            Box::new(right)
        )),
    }
}

pub(in crate::surface) fn bitvector32_shift_count(right: u32) -> Option<u32> {
    let right = right as i32;
    (0..32).contains(&right).then_some(right as u32)
}

pub(in crate::surface) fn bitvector32_shift_left(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> Result<OldMachineTerm, String> {
    match (&left, &right) {
        (_, bits32_constant!(right)) if bitvector32_shift_count(constant_u32(*right)).is_none() => {
            Err("invalid shift count in proposition".to_string())
        }
        (int32_constant!(left), _) if (constant_u32(*left) as i32) < 0 => {
            Err("left shift of negative value in proposition".to_string())
        }
        (bits32_constant!(left), bits32_constant!(right)) => {
            let count = bitvector32_shift_count(constant_u32(*right))
                .expect("constant shift count was checked above");
            let shifted = ((constant_u32(*left) as i32) as i64) << count;
            if shifted > i64::from(i32::MAX) {
                Err("signed left shift overflow in proposition".to_string())
            } else {
                Ok(OldMachineTerm::constant((shifted as i32) as u32))
            }
        }
        _ => Ok(binary_node!(
            Int32,
            ShiftLeft,
            Box::new(left),
            Box::new(right)
        )),
    }
}

pub(in crate::surface) fn bitvector32_shift_right(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> Result<OldMachineTerm, String> {
    match (&left, &right) {
        (_, bits32_constant!(right)) if bitvector32_shift_count(constant_u32(*right)).is_none() => {
            Err("invalid shift count in proposition".to_string())
        }
        (bits32_constant!(left), bits32_constant!(right)) => {
            let count = bitvector32_shift_count(constant_u32(*right))
                .expect("constant shift count was checked above");
            Ok(OldMachineTerm::constant(
                ((constant_u32(*left) as i32) >> count) as u32,
            ))
        }
        (_, bits32_constant!(0)) => Ok(left),
        _ => Ok(binary_node!(
            Int32,
            ShiftRight,
            Box::new(left),
            Box::new(right),
        )),
    }
}

pub(in crate::surface) fn bitvector32_and(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldMachineTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            OldMachineTerm::constant(constant_u32(*left) & constant_u32(*right))
        }
        (_, bits32_constant!(0xFFFF_FFFF)) => left,
        (int32_constant!(0xFFFF_FFFF), _) => right,
        (_, bits32_constant!(0)) | (int32_constant!(0), _) => OldMachineTerm::constant(0),
        _ if left == right => left,
        _ => binary_node!(Int32, BitwiseAnd, Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_or(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldMachineTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            OldMachineTerm::constant(constant_u32(*left) | constant_u32(*right))
        }
        (_, bits32_constant!(0)) => left,
        (int32_constant!(0), _) => right,
        (_, bits32_constant!(0xFFFF_FFFF)) | (int32_constant!(0xFFFF_FFFF), _) => {
            OldMachineTerm::constant(u32::MAX)
        }
        _ if left == right => left,
        _ => binary_node!(Int32, BitwiseOr, Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_xor(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldMachineTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            OldMachineTerm::constant(constant_u32(*left) ^ constant_u32(*right))
        }
        (_, bits32_constant!(0)) => left,
        (int32_constant!(0), _) => right,
        _ if left == right => OldMachineTerm::constant(0),
        _ => binary_node!(Int32, BitwiseXor, Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_not(value: OldMachineTerm) -> OldMachineTerm {
    match value {
        bits32_constant!(value) => OldMachineTerm::constant(!constant_u32(value)),
        unary_term!(Int32, BitwiseNot, inner) => *inner,
        value => unary_node!(Int32, BitwiseNot, Box::new(value)),
    }
}

pub(in crate::surface) fn signed_less_than(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldConditionTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            OldConditionTerm::Constant((constant_u32(*left) as i32) < (constant_u32(*right) as i32))
        }
        _ => OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left: Box::new(left),
            right: Box::new(right),
        },
    }
}

pub(in crate::surface) fn signed_less_equal(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldConditionTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => OldConditionTerm::Constant(
            (constant_u32(*left) as i32) <= (constant_u32(*right) as i32),
        ),
        _ => OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left: Box::new(left),
            right: Box::new(right),
        },
    }
}

pub(in crate::surface) fn signed_greater_than(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldConditionTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            OldConditionTerm::Constant((constant_u32(*left) as i32) > (constant_u32(*right) as i32))
        }
        _ => OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left: Box::new(left),
            right: Box::new(right),
        },
    }
}

pub(in crate::surface) fn signed_greater_equal(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldConditionTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => OldConditionTerm::Constant(
            (constant_u32(*left) as i32) >= (constant_u32(*right) as i32),
        ),
        _ => OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left: Box::new(left),
            right: Box::new(right),
        },
    }
}

pub(in crate::surface) fn bitvector32_equal(
    left: OldMachineTerm,
    right: OldMachineTerm,
) -> OldConditionTerm {
    match (&left, &right) {
        (bits32_constant!(left), bits32_constant!(right)) => {
            OldConditionTerm::Constant(constant_u32(*left) == constant_u32(*right))
        }
        _ => OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::Equal,
            left: Box::new(left),
            right: Box::new(right),
        },
    }
}
