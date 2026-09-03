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
        && (left.c_type() == right.c_type() || left.is_null() || right.is_null())
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
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        let Some((condition, value)) = comparison_condition(left_term, operator, right_term) else {
            return Err(ClickError::new("unsupported proposition comparison"));
        };
        Ok(Proposition::ConditionIs(condition, value))
    } else {
        Err(ClickError::new(format!(
            "cannot compare `{left:?}` and `{right:?}` in proposition"
        )))
    }
}

pub(in crate::surface) fn proposition_as_single_condition(
    proposition: &Proposition,
) -> Option<(ConditionTerm, bool)> {
    match proposition {
        Proposition::ConditionIs(condition, value) => Some((condition.clone(), *value)),
        Proposition::Not(body) => {
            let Proposition::ConditionIs(condition, value) = body.as_ref() else {
                return None;
            };
            Some((condition.clone(), !*value))
        }
        _ => None,
    }
}

pub(in crate::surface) fn assumptions_prove_proposition_false(
    assumptions: &PureFactContext,
    proposition: &Proposition,
) -> bool {
    match proposition {
        Proposition::ConditionIs(condition, value) => {
            assumptions.proves(&Proposition::ConditionIs(condition.clone(), !*value))
        }
        _ => assumptions.proves(&Proposition::Not(Box::new(proposition.clone()))),
    }
}

pub(in crate::surface) fn conditional_contract_value(
    proposition: &Proposition,
    then_value: CValue,
    else_value: CValue,
) -> Result<CValue, String> {
    if then_value == else_value {
        return Ok(then_value);
    }

    let Some((condition, expected)) = proposition_as_single_condition(proposition) else {
        return Err(
            "symbolic `if` expressions currently require a single comparison condition".to_string(),
        );
    };

    let (CValue::Int32(then_term), CValue::Int32(else_term)) = (then_value, else_value) else {
        return Err(
            "symbolic `if` expressions currently support only int32 branch values".to_string(),
        );
    };

    let (then_term, else_term) = if expected {
        (then_term, else_term)
    } else {
        (else_term, then_term)
    };
    Ok(CValue::Int32(Bitvector32Term::if_then_else(
        condition, then_term, else_term,
    )))
}

pub(in crate::surface) fn true_proposition() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(true), true)
}

pub(in crate::surface) fn false_proposition() -> Proposition {
    Proposition::ConditionIs(ConditionTerm::Constant(false), true)
}

pub(in crate::surface) fn conjunction(left: Proposition, right: Proposition) -> Proposition {
    match (&left, &right) {
        (Proposition::ConditionIs(ConditionTerm::Constant(true), true), _) => right,
        (_, Proposition::ConditionIs(ConditionTerm::Constant(true), true)) => left,
        (Proposition::ConditionIs(ConditionTerm::Constant(false), true), _)
        | (_, Proposition::ConditionIs(ConditionTerm::Constant(false), true)) => {
            false_proposition()
        }
        _ => Proposition::And(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn disjunction(left: Proposition, right: Proposition) -> Proposition {
    match (&left, &right) {
        (Proposition::ConditionIs(ConditionTerm::Constant(false), true), _) => right,
        (_, Proposition::ConditionIs(ConditionTerm::Constant(false), true)) => left,
        (Proposition::ConditionIs(ConditionTerm::Constant(true), true), _)
        | (_, Proposition::ConditionIs(ConditionTerm::Constant(true), true)) => true_proposition(),
        _ => Proposition::Or(Box::new(left), Box::new(right)),
    }
}

pub(in crate::surface) fn range_membership_proposition(
    start: Bitvector32Term,
    item: Bitvector32Term,
    end: Bitvector32Term,
) -> Proposition {
    conjunction(
        Proposition::ConditionIs(signed_less_equal(start, item.clone()), true),
        Proposition::ConditionIs(signed_less_than(item, end), true),
    )
}

pub(in crate::surface) fn bounded_forall_int32(
    variable: Variable,
    start: Bitvector32Term,
    item: Bitvector32Term,
    end: Bitvector32Term,
    body: Proposition,
) -> Proposition {
    Proposition::ForAll {
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(Proposition::Implies(
            Box::new(range_membership_proposition(start, item, end)),
            Box::new(body),
        )),
    }
}

pub(in crate::surface) fn bounded_exists_int32(
    name: String,
    variable: Variable,
    start: Bitvector32Term,
    item: Bitvector32Term,
    end: Bitvector32Term,
    body: Proposition,
) -> Proposition {
    Proposition::Exists {
        name,
        var: variable,
        sort: Sort::CInt32,
        body: Box::new(conjunction(
            range_membership_proposition(start, item, end),
            body,
        )),
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

pub(in crate::surface) fn int32_term_value(
    value: CValue,
    label: &str,
) -> Result<Bitvector32Term, String> {
    let CValue::Int32(bits) = value else {
        return Err(format!("`{label}` is not int32"));
    };
    Ok(simp_bitvector(&bits))
}

pub(in crate::surface) fn promoted_int32_term(value: &CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Int32(bits) | CValue::UInt8(bits) => Some(simp_bitvector(bits)),
        CValue::Void | CValue::Pointer(_) => None,
    }
}

pub(in crate::surface) fn concrete_fold_range(
    start: i32,
    end: i32,
) -> Result<std::ops::Range<i32>, String> {
    let length = i64::from(end) - i64::from(start);
    if length <= 0 {
        return Ok(start..start);
    }
    if length > MAX_CONCRETE_RANGE_FOLD_STEPS {
        return Err(format!(
            "`fold` range has {length} iterations; the current concrete unroll limit is {MAX_CONCRETE_RANGE_FOLD_STEPS}"
        ));
    }
    Ok(start..end)
}

pub(in crate::surface) fn concrete_bound_from_term(
    term: &Bitvector32Term,
    construct: &str,
    label: &str,
) -> Result<i32, String> {
    let term = simp_bitvector(term);
    let Bitvector32Term::Constant(value) = term else {
        return Err(format!(
            "symbolic `{construct}` {label} bounds are not supported yet"
        ));
    };
    Ok(value as i32)
}

pub(in crate::surface) fn fold_bound_variable(name: &str, salt: u64) -> Variable {
    let mut hash = 0xcbf2_9ce4_8422_2325_u64 ^ salt;
    for byte in name.bytes() {
        hash ^= u64::from(byte);
        hash = hash.wrapping_mul(0x1000_0000_01b3);
    }
    Variable(3_000_000 + (hash % 1_000_000_000))
}

pub(in crate::surface) fn symbolic_range_fold_value(
    start: Bitvector32Term,
    end: Bitvector32Term,
    initial: CValue,
    accumulator: &str,
    item: &str,
    body_value: CValue,
) -> Result<CValue, String> {
    let initial = int32_term_value(initial, "fold initial value")?;
    let body = int32_term_value(body_value, "fold body value")?;
    Ok(CValue::Int32(Bitvector32Term::range_fold(
        start,
        end,
        initial,
        fold_bound_variable(accumulator, 0),
        fold_bound_variable(item, 1),
        body,
    )))
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
