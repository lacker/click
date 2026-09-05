use super::*;

pub(in crate::surface) fn comparison_proposition(
    left: CValue,
    operator: ComparisonOperator,
    right: CValue,
) -> Result<Proposition, ClickError> {
    let pointer_and_null = match (&left, &right) {
        (CValue::Pointer(pointer), CValue::Int32(Bitvector32Term::Constant(0))) => {
            Some((pointer.pointer().clone(), Pointer::null()))
        }
        (CValue::Int32(Bitvector32Term::Constant(0)), CValue::Pointer(pointer)) => {
            Some((Pointer::null(), pointer.pointer().clone()))
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
        return Ok(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(left, right),
            value,
        ));
    }
    if let (CValue::Pointer(left), CValue::Pointer(right)) = (&left, &right)
        && (left.c_type().pointer_types_compatible(right.c_type())
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
        return Ok(Proposition::ConditionIs(
            ConditionTerm::pointer_equal(left.pointer().clone(), right.pointer().clone()),
            value,
        ));
    }
    if matches!(left, CValue::UInt64(_)) || matches!(right, CValue::UInt64(_)) {
        let left = promoted_uint64_term(&left).ok_or_else(|| {
            ClickError::new(format!(
                "cannot compare `{left:?}` and `{right:?}` in proposition"
            ))
        })?;
        let right = promoted_uint64_term(&right).ok_or_else(|| {
            ClickError::new(format!(
                "cannot compare `{left:?}` and `{right:?}` in proposition"
            ))
        })?;
        let condition = match operator {
            ComparisonOperator::Equal | ComparisonOperator::NotEqual => {
                ConditionTerm::uint64_equal(left, right)
            }
            ComparisonOperator::LessThan => ConditionTerm::uint64_less_than(left, right),
            ComparisonOperator::LessEqual => ConditionTerm::uint64_less_equal(left, right),
            ComparisonOperator::GreaterThan => ConditionTerm::uint64_greater_than(left, right),
            ComparisonOperator::GreaterEqual => ConditionTerm::uint64_greater_equal(left, right),
        };
        return Ok(Proposition::ConditionIs(
            condition,
            !matches!(operator, ComparisonOperator::NotEqual),
        ));
    }
    if matches!(left, CValue::Int64(_)) || matches!(right, CValue::Int64(_)) {
        let left = promoted_int64_term(&left).ok_or_else(|| {
            ClickError::new(format!(
                "cannot compare `{left:?}` and `{right:?}` in proposition"
            ))
        })?;
        let right = promoted_int64_term(&right).ok_or_else(|| {
            ClickError::new(format!(
                "cannot compare `{left:?}` and `{right:?}` in proposition"
            ))
        })?;
        let condition = match operator {
            ComparisonOperator::Equal | ComparisonOperator::NotEqual => {
                ConditionTerm::int64_equal(left, right)
            }
            ComparisonOperator::LessThan => ConditionTerm::int64_signed_less_than(left, right),
            ComparisonOperator::LessEqual => ConditionTerm::int64_signed_less_equal(left, right),
            ComparisonOperator::GreaterThan => {
                ConditionTerm::int64_signed_greater_than(left, right)
            }
            ComparisonOperator::GreaterEqual => {
                ConditionTerm::int64_signed_greater_equal(left, right)
            }
        };
        return Ok(Proposition::ConditionIs(
            condition,
            !matches!(operator, ComparisonOperator::NotEqual),
        ));
    }
    let unsigned = matches!(
        (&left, &right),
        (CValue::UInt32(_), _) | (_, CValue::UInt32(_))
    );
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        let Some((condition, value)) =
            comparison_condition(left_term, operator, right_term, unsigned)
        else {
            return Err(ClickError::new("unsupported proposition comparison"));
        };
        Ok(Proposition::ConditionIs(condition, value))
    } else {
        Err(ClickError::new(format!(
            "cannot compare `{left:?}` and `{right:?}` in proposition"
        )))
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
            operator: CComparisonOperator::LessEqual,
            right: item.clone(),
        }),
        Box::new(SpecProposition::Comparison {
            left: item,
            operator: CComparisonOperator::LessThan,
            right: end,
        }),
    )
}

pub(in crate::surface) fn promoted_int32_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Int16(bits)
        | CValue::Int32(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::UInt32(bits) => Some(simp_bitvector(bits)),
        CValue::Void
        | CValue::Int64(_)
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

fn promoted_int64_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Int64(bits) => Some(bits.clone()),
        CValue::Int16(bits) | CValue::Int32(bits) | CValue::UInt8(bits) | CValue::UInt16(bits) => {
            Some(Bitvector32Term::int64_from_32(bits.clone()))
        }
        CValue::UInt32(bits) => Some(Bitvector32Term::int64_from_uint32(bits.clone())),
        CValue::Void
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

fn promoted_uint64_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::UInt64(bits) => Some(bits.clone()),
        CValue::Int64(bits) => Some(Bitvector32Term::uint64_from_int64(bits.clone())),
        CValue::Int16(bits) | CValue::Int32(bits) | CValue::UInt8(bits) | CValue::UInt16(bits) => {
            Some(Bitvector32Term::uint64_from_int32(bits.clone()))
        }
        CValue::UInt32(bits) => Some(Bitvector32Term::uint64_from_32(bits.clone())),
        CValue::Void | CValue::Pointer(_) | CValue::Float32(_) | CValue::Float64(_) => None,
    }
}

pub(in crate::surface) fn bitvector32_add(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_add(*right))
        }
        (Bitvector32Term::Constant(constant), Bitvector32Term::Subtract(base, subtrahend))
            if subtrahend.as_ref() == &Bitvector32Term::Constant(*constant) =>
        {
            base.as_ref().clone()
        }
        (Bitvector32Term::Subtract(base, subtrahend), Bitvector32Term::Constant(constant))
            if subtrahend.as_ref() == &Bitvector32Term::Constant(*constant) =>
        {
            base.as_ref().clone()
        }
        (Bitvector32Term::Subtract(zero, subtrahend), Bitvector32Term::Add(base, addend))
            if zero.as_ref() == &Bitvector32Term::Constant(0) && subtrahend == base =>
        {
            addend.as_ref().clone()
        }
        (Bitvector32Term::Subtract(zero, subtrahend), Bitvector32Term::Add(addend, base))
            if zero.as_ref() == &Bitvector32Term::Constant(0) && subtrahend == base =>
        {
            addend.as_ref().clone()
        }
        (Bitvector32Term::Add(base, addend), Bitvector32Term::Subtract(zero, subtrahend))
            if zero.as_ref() == &Bitvector32Term::Constant(0) && base == subtrahend =>
        {
            addend.as_ref().clone()
        }
        (Bitvector32Term::Add(addend, base), Bitvector32Term::Subtract(zero, subtrahend))
            if zero.as_ref() == &Bitvector32Term::Constant(0) && base == subtrahend =>
        {
            addend.as_ref().clone()
        }
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        _ => Bitvector32Term::Add(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_subtract(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_sub(*right))
        }
        (_, Bitvector32Term::Constant(0)) => left,
        _ if left == right => Bitvector32Term::Constant(0),
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_base => {
            bitvector32_subtract(left_addend.as_ref().clone(), right_addend.as_ref().clone())
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_base == right_addend => {
            bitvector32_subtract(left_addend.as_ref().clone(), right_base.as_ref().clone())
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_addend == right_base => {
            bitvector32_subtract(left_base.as_ref().clone(), right_addend.as_ref().clone())
        }
        (
            Bitvector32Term::Add(left_base, left_addend),
            Bitvector32Term::Add(right_base, right_addend),
        ) if left_addend == right_addend => {
            bitvector32_subtract(left_base.as_ref().clone(), right_base.as_ref().clone())
        }
        (Bitvector32Term::Add(left_base, left_addend), _) if left_base.as_ref() == &right => {
            left_addend.as_ref().clone()
        }
        (Bitvector32Term::Add(left_base, left_addend), _) if left_addend.as_ref() == &right => {
            left_base.as_ref().clone()
        }
        (_, Bitvector32Term::Add(right_base, right_addend)) if &left == right_base.as_ref() => {
            bitvector32_subtract(Bitvector32Term::Constant(0), right_addend.as_ref().clone())
        }
        (_, Bitvector32Term::Add(right_base, right_addend)) if &left == right_addend.as_ref() => {
            bitvector32_subtract(Bitvector32Term::Constant(0), right_base.as_ref().clone())
        }
        _ => Bitvector32Term::Subtract(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_multiply(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(left.wrapping_mul(*right))
        }
        (_, Bitvector32Term::Constant(1)) => left,
        (Bitvector32Term::Constant(1), _) => right,
        (_, Bitvector32Term::Constant(0)) | (Bitvector32Term::Constant(0), _) => {
            Bitvector32Term::Constant(0)
        }
        _ => Bitvector32Term::Multiply(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_divide(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(0)) => Err("division by zero in proposition".to_string()),
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right))
            if *left == i32::MIN as u32 && *right == (-1i32) as u32 =>
        {
            Err("signed division overflow in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => Ok(
            Bitvector32Term::Constant(((*left as i32) / (*right as i32)) as u32),
        ),
        (_, Bitvector32Term::Constant(1)) => Ok(left),
        _ => Ok(Bitvector32Term::Divide(Box::new(left), Box::new(right))),
    }
}

pub(in crate::surface) fn bitvector32_remainder(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(0)) => Err("division by zero in proposition".to_string()),
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right))
            if *left == i32::MIN as u32 && *right == (-1i32) as u32 =>
        {
            Err("signed division overflow in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => Ok(
            Bitvector32Term::Constant(((*left as i32) % (*right as i32)) as u32),
        ),
        (_, Bitvector32Term::Constant(1)) => Ok(Bitvector32Term::Constant(0)),
        _ => Ok(Bitvector32Term::Remainder(Box::new(left), Box::new(right))),
    }
}

pub(in crate::surface) fn bitvector32_shift_count(right: u32) -> Option<u32> {
    let right = right as i32;
    (0..32).contains(&right).then_some(right as u32)
}

pub(in crate::surface) fn bitvector32_shift_left(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(right)) if bitvector32_shift_count(*right).is_none() => {
            Err("invalid shift count in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), _) if (*left as i32) < 0 => {
            Err("left shift of negative value in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            let count =
                bitvector32_shift_count(*right).expect("constant shift count was checked above");
            let shifted = ((*left as i32) as i64) << count;
            if shifted > i64::from(i32::MAX) {
                Err("signed left shift overflow in proposition".to_string())
            } else {
                Ok(Bitvector32Term::Constant((shifted as i32) as u32))
            }
        }
        _ => Ok(Bitvector32Term::ShiftLeft(Box::new(left), Box::new(right))),
    }
}

pub(in crate::surface) fn bitvector32_shift_right(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Result<Bitvector32Term, String> {
    match (&left, &right) {
        (_, Bitvector32Term::Constant(right)) if bitvector32_shift_count(*right).is_none() => {
            Err("invalid shift count in proposition".to_string())
        }
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            let count =
                bitvector32_shift_count(*right).expect("constant shift count was checked above");
            Ok(Bitvector32Term::Constant(((*left as i32) >> count) as u32))
        }
        (_, Bitvector32Term::Constant(0)) => Ok(left),
        _ => Ok(Bitvector32Term::ArithmeticShiftRight(
            Box::new(left),
            Box::new(right),
        )),
    }
}

pub(in crate::surface) fn bitvector32_and(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(*left & *right)
        }
        (_, Bitvector32Term::Constant(u32::MAX)) => left,
        (Bitvector32Term::Constant(u32::MAX), _) => right,
        (_, Bitvector32Term::Constant(0)) | (Bitvector32Term::Constant(0), _) => {
            Bitvector32Term::Constant(0)
        }
        _ if left == right => left,
        _ => Bitvector32Term::BitwiseAnd(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_or(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(*left | *right)
        }
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        (_, Bitvector32Term::Constant(u32::MAX)) | (Bitvector32Term::Constant(u32::MAX), _) => {
            Bitvector32Term::Constant(u32::MAX)
        }
        _ if left == right => left,
        _ => Bitvector32Term::BitwiseOr(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_xor(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> Bitvector32Term {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            Bitvector32Term::Constant(*left ^ *right)
        }
        (_, Bitvector32Term::Constant(0)) => left,
        (Bitvector32Term::Constant(0), _) => right,
        _ if left == right => Bitvector32Term::Constant(0),
        _ => Bitvector32Term::BitwiseXor(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_not(value: Bitvector32Term) -> Bitvector32Term {
    match value {
        Bitvector32Term::Constant(value) => Bitvector32Term::Constant(!value),
        Bitvector32Term::BitwiseNot(inner) => *inner,
        value => Bitvector32Term::BitwiseNot(Box::new(value)),
    }
}

pub(in crate::surface) fn signed_less_than(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) < (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedLessThan(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn signed_less_equal(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) <= (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedLessEqual(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn signed_greater_than(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) > (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedGreaterThan(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn signed_greater_equal(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant((*left as i32) >= (*right as i32))
        }
        _ => ConditionTerm::Bitvector32SignedGreaterEqual(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn bitvector32_equal(
    left: Bitvector32Term,
    right: Bitvector32Term,
) -> ConditionTerm {
    match (&left, &right) {
        (Bitvector32Term::Constant(left), Bitvector32Term::Constant(right)) => {
            ConditionTerm::Constant(left == right)
        }
        _ => ConditionTerm::Bitvector32Equal(Box::new(left), Box::new(right)),
    }
}
