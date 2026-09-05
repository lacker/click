use super::*;

/// Round a nonnegative integer right shift to nearest, ties to even.
///
/// The floating-point conversions in this slice operate on the exact integer
/// significands of IEEE values. Keeping the rounding here in integer space
/// makes the result independent of the host floating-point environment.
fn round_right_to_even(value: u128, shift: u32) -> u128 {
    if shift == 0 {
        return value;
    }
    if shift >= 128 {
        return 0;
    }
    let truncated = value >> shift;
    let remainder = value & ((1u128 << shift) - 1);
    let halfway = 1u128 << (shift - 1);
    if remainder > halfway || (remainder == halfway && truncated & 1 != 0) {
        truncated + 1
    } else {
        truncated
    }
}

fn integer_to_float_bits(
    negative: bool,
    magnitude: u128,
    fraction_bits: u32,
    exponent_bits: u32,
    bias: i32,
    sign_bit: u64,
) -> u64 {
    let sign = if negative { sign_bit } else { 0 };
    if magnitude == 0 {
        return sign;
    }

    let precision = fraction_bits + 1;
    let highest_bit = 127 - magnitude.leading_zeros();
    let mut exponent = highest_bit as i32;
    let mut significand = if highest_bit < precision - 1 {
        magnitude << (precision - 1 - highest_bit)
    } else {
        round_right_to_even(magnitude, highest_bit - (precision - 1))
    };

    if significand == 1u128 << precision {
        significand >>= 1;
        exponent += 1;
    }

    let exponent_limit = (1u32 << exponent_bits) - 1;
    let encoded_exponent = exponent + bias;
    if encoded_exponent >= exponent_limit as i32 {
        return sign | (u64::from(exponent_limit) << fraction_bits);
    }

    sign | ((encoded_exponent as u64) << fraction_bits)
        | ((significand as u64) & ((1u64 << fraction_bits) - 1))
}

fn integer_to_float32_bits(negative: bool, magnitude: u128) -> u32 {
    integer_to_float_bits(negative, magnitude, 23, 8, 127, 0x8000_0000) as u32
}

fn integer_to_float64_bits(negative: bool, magnitude: u128) -> u64 {
    integer_to_float_bits(negative, magnitude, 52, 11, 1023, 0x8000_0000_0000_0000)
}

fn float32_to_float64_bits(bits: u32) -> u64 {
    let sign = u64::from(bits & 0x8000_0000) << 32;
    let exponent = (bits >> 23) & 0xff;
    let fraction = bits & 0x007f_ffff;
    if exponent == 0xff {
        let payload = if fraction == 0 {
            0
        } else {
            u64::from(fraction) << 29
        };
        return sign | (0x7ffu64 << 52) | if payload == 0 { 1 } else { payload };
    }
    if exponent != 0 {
        return sign | (u64::from(exponent + 1023 - 127) << 52) | (u64::from(fraction) << 29);
    }
    if fraction == 0 {
        return sign;
    }

    let highest_bit = 31 - fraction.leading_zeros();
    let unbiased_exponent = highest_bit as i32 - 149;
    let encoded_exponent = (unbiased_exponent + 1023) as u64;
    let significand = fraction ^ (1u32 << highest_bit);
    sign | (encoded_exponent << 52) | (u64::from(significand) << (52 - highest_bit))
}

fn float64_to_float32_bits(bits: u64) -> u32 {
    let sign = (bits >> 32) as u32 & 0x8000_0000;
    let exponent = ((bits >> 52) & 0x7ff) as u32;
    let fraction = bits & 0x000f_ffff_ffff_ffff;
    if exponent == 0x7ff {
        return sign
            | if fraction == 0 {
                0x7f80_0000
            } else {
                0x7fc0_0000
            };
    }
    if exponent == 0 && fraction == 0 {
        return sign;
    }

    let (significand, base, highest_bit) = if exponent == 0 {
        let highest_bit = 63 - fraction.leading_zeros();
        (u128::from(fraction), -1074i32, highest_bit)
    } else {
        let significand = (1u128 << 52) | u128::from(fraction);
        let highest_bit = 52;
        (significand, exponent as i32 - 1023 - 52, highest_bit)
    };
    let top_exponent = highest_bit as i32 + base;

    if top_exponent >= -126 {
        let shift = (top_exponent - 23 - base) as u32;
        let mut rounded = round_right_to_even(significand, shift);
        let mut exponent = top_exponent;
        if rounded == 1u128 << 24 {
            rounded >>= 1;
            exponent += 1;
        }
        if exponent > 127 {
            return sign | 0x7f80_0000;
        }
        return sign | (((exponent + 127) as u32) << 23) | ((rounded as u32) & 0x007f_ffff);
    }

    let shift = (-149 - base) as u32;
    let rounded = round_right_to_even(significand, shift);
    if rounded >= 1u128 << 23 {
        sign | 0x0080_0000
    } else {
        sign | rounded as u32
    }
}

fn integer_constant_as_sign_magnitude(value: &CValue) -> Option<(bool, u128)> {
    match value {
        CValue::Int16(bits) | CValue::Int32(bits) => {
            let value = bits.as_const()? as i32;
            Some((value < 0, u128::from(value.unsigned_abs())))
        }
        CValue::UInt8(bits) | CValue::UInt16(bits) | CValue::UInt32(bits) => {
            Some((false, u128::from(bits.as_const()?)))
        }
        CValue::Int64(bits) => {
            let value = bits.int64_as_const()?;
            Some((value < 0, u128::from(value.unsigned_abs())))
        }
        CValue::UInt64(bits) => Some((false, u128::from(bits.uint64_as_const()?))),
        CValue::Void | CValue::Float32(_) | CValue::Float64(_) | CValue::Pointer(_) => None,
    }
}

fn float_significand_as_integer(
    negative: bool,
    exponent: u32,
    fraction: u64,
    fraction_bits: u32,
    exponent_bits: u32,
    bias: i32,
) -> Option<(bool, u128)> {
    let exponent_limit = (1u32 << exponent_bits) - 1;
    if exponent == exponent_limit {
        return None;
    }
    let (significand, base) = if exponent == 0 {
        (u128::from(fraction), 1 - bias - fraction_bits as i32)
    } else {
        (
            (1u128 << fraction_bits) | u128::from(fraction),
            exponent as i32 - bias - fraction_bits as i32,
        )
    };
    let magnitude = if base >= 0 {
        significand.checked_shl(base as u32)?
    } else if (-base) >= 128 {
        0
    } else {
        significand >> (-base as u32)
    };
    Some((negative && magnitude != 0, magnitude))
}

fn float_to_integer_value(negative: bool, magnitude: u128, target_type: CType) -> Option<CValue> {
    let signed_limit = |bits: u32| (1i128 << (bits - 1)) - 1;
    let (signed, bits) = match target_type {
        CType::Int16 => (true, 16),
        CType::Int32 => (true, 32),
        CType::Int64 => (true, 64),
        CType::UInt8 => (false, 8),
        CType::UInt16 => (false, 16),
        CType::UInt32 => (false, 32),
        CType::UInt64 => (false, 64),
        _ => return None,
    };
    if signed {
        let limit = signed_limit(bits) as u128;
        let negative_limit = limit + 1;
        if magnitude > if negative { negative_limit } else { limit } {
            return None;
        }
        let value = if negative {
            -(magnitude as i128)
        } else {
            magnitude as i128
        };
        return Some(match target_type {
            CType::Int16 => CValue::Int16(Bitvector32Term::Constant(value as i32 as u32)),
            CType::Int32 => CValue::Int32(Bitvector32Term::Constant(value as i32 as u32)),
            CType::Int64 => CValue::Int64(Bitvector32Term::Int64Constant(value as i64)),
            _ => unreachable!(),
        });
    }
    if negative && magnitude != 0 {
        return None;
    }
    let limit = (1u128 << bits) - 1;
    if magnitude > limit {
        return None;
    }
    let value = magnitude as u64;
    Some(match target_type {
        CType::UInt8 => CValue::UInt8(Bitvector32Term::Constant(value as u32)),
        CType::UInt16 => CValue::UInt16(Bitvector32Term::Constant(value as u32)),
        CType::UInt32 => CValue::UInt32(Bitvector32Term::Constant(value as u32)),
        CType::UInt64 => CValue::UInt64(Bitvector32Term::UInt64Constant(value)),
        _ => unreachable!(),
    })
}

fn float32_to_integer_value(bits: u32, target_type: CType) -> Option<CValue> {
    let negative = bits & 0x8000_0000 != 0;
    let exponent = (bits >> 23) & 0xff;
    let fraction = u64::from(bits & 0x007f_ffff);
    let (negative, magnitude) =
        float_significand_as_integer(negative, exponent, fraction, 23, 8, 127)?;
    float_to_integer_value(negative, magnitude, target_type)
}

fn float64_to_integer_value(bits: u64, target_type: CType) -> Option<CValue> {
    let negative = bits & (1u64 << 63) != 0;
    let exponent = ((bits >> 52) & 0x7ff) as u32;
    let fraction = bits & 0x000f_ffff_ffff_ffff;
    let (negative, magnitude) =
        float_significand_as_integer(negative, exponent, fraction, 52, 11, 1023)?;
    float_to_integer_value(negative, magnitude, target_type)
}

fn integer_to_float_value(value: CValue, target_type: CType) -> Option<CValue> {
    let (source_name, term) = match &value {
        CValue::Int16(term) => ("int16", term),
        CValue::Int32(term) => ("int32", term),
        CValue::UInt8(term) => ("uint8", term),
        CValue::UInt16(term) => ("uint16", term),
        CValue::UInt32(term) => ("uint32", term),
        CValue::Int64(term) => ("int64", term),
        CValue::UInt64(term) => ("uint64", term),
        CValue::Void | CValue::Float32(_) | CValue::Float64(_) | CValue::Pointer(_) => return None,
    };
    let target_name = match target_type {
        CType::Float32 => "float32",
        CType::Float64 => "float64",
        _ => return None,
    };
    if let Some((negative, magnitude)) = integer_constant_as_sign_magnitude(&value) {
        return Some(match target_type {
            CType::Float32 => CValue::Float32(Bitvector32Term::Constant(integer_to_float32_bits(
                negative, magnitude,
            ))),
            CType::Float64 => CValue::Float64(Bitvector32Term::UInt64Constant(
                integer_to_float64_bits(negative, magnitude),
            )),
            _ => unreachable!(),
        });
    }
    let term = Bitvector32Term::opaque_conversion(
        format!("c_{source_name}_to_{target_name}"),
        term.clone(),
    );
    Some(match target_type {
        CType::Float32 => CValue::Float32(term),
        CType::Float64 => CValue::Float64(term),
        _ => unreachable!(),
    })
}

fn float_integer_bound_bits(
    source_type: CType,
    exponent: u32,
    negative: bool,
) -> Option<Bitvector32Term> {
    let magnitude = 1u128.checked_shl(exponent)?;
    Some(match source_type {
        CType::Float32 => Bitvector32Term::Constant(integer_to_float32_bits(negative, magnitude)),
        CType::Float64 => {
            Bitvector32Term::UInt64Constant(integer_to_float64_bits(negative, magnitude))
        }
        _ => return None,
    })
}

fn add_float_to_integer_obligations(
    value: &Bitvector32Term,
    source_type: CType,
    target_type: CType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<()> {
    let (signed, bits) = match target_type {
        CType::Int16 => (true, 16),
        CType::Int32 => (true, 32),
        CType::Int64 => (true, 64),
        CType::UInt8 => (false, 8),
        CType::UInt16 => (false, 16),
        CType::UInt32 => (false, 32),
        CType::UInt64 => (false, 64),
        _ => return None,
    };
    let finite = match source_type {
        CType::Float32 => {
            ConditionTerm::float32_classification(value.clone(), CFloatClassification::Finite)
        }
        CType::Float64 => {
            ConditionTerm::float64_classification(value.clone(), CFloatClassification::Finite)
        }
        _ => return None,
    };
    add_proof_obligation(
        obligations,
        assumptions,
        Proposition::ConditionIs(finite, true),
    )?;

    if signed {
        let lower = float_integer_bound_bits(source_type, bits - 1, true)?;
        let upper = float_integer_bound_bits(source_type, bits - 1, false)?;
        let lower = match source_type {
            CType::Float32 => ConditionTerm::float32_compare(
                value.clone(),
                lower,
                CComparisonOperator::GreaterEqual,
            ),
            CType::Float64 => ConditionTerm::float64_compare(
                value.clone(),
                lower,
                CComparisonOperator::GreaterEqual,
            ),
            _ => unreachable!(),
        };
        let upper = match source_type {
            CType::Float32 => {
                ConditionTerm::float32_compare(value.clone(), upper, CComparisonOperator::LessThan)
            }
            CType::Float64 => {
                ConditionTerm::float64_compare(value.clone(), upper, CComparisonOperator::LessThan)
            }
            _ => unreachable!(),
        };
        add_proof_obligation(
            obligations,
            assumptions,
            Proposition::ConditionIs(lower, true),
        )?;
        add_proof_obligation(
            obligations,
            assumptions,
            Proposition::ConditionIs(upper, true),
        )?;
    } else {
        let lower = match source_type {
            CType::Float32 => ConditionTerm::float32_compare(
                value.clone(),
                Bitvector32Term::Constant(0),
                CComparisonOperator::GreaterEqual,
            ),
            CType::Float64 => ConditionTerm::float64_compare(
                value.clone(),
                Bitvector32Term::UInt64Constant(0),
                CComparisonOperator::GreaterEqual,
            ),
            _ => unreachable!(),
        };
        let upper_bits = float_integer_bound_bits(source_type, bits, false)?;
        let upper = match source_type {
            CType::Float32 => ConditionTerm::float32_compare(
                value.clone(),
                upper_bits,
                CComparisonOperator::LessThan,
            ),
            CType::Float64 => ConditionTerm::float64_compare(
                value.clone(),
                upper_bits,
                CComparisonOperator::LessThan,
            ),
            _ => unreachable!(),
        };
        add_proof_obligation(
            obligations,
            assumptions,
            Proposition::ConditionIs(lower, true),
        )?;
        add_proof_obligation(
            obligations,
            assumptions,
            Proposition::ConditionIs(upper, true),
        )?;
    }
    Some(())
}

fn float_to_integer_conversion_value(
    value: Bitvector32Term,
    source_type: CType,
    target_type: CType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    add_float_to_integer_obligations(&value, source_type, target_type, obligations, assumptions)?;
    let source_name = match source_type {
        CType::Float32 => "float32",
        CType::Float64 => "float64",
        _ => return None,
    };
    let target_name = match target_type {
        CType::Int16 => "int16",
        CType::Int32 => "int32",
        CType::UInt8 => "uint8",
        CType::UInt16 => "uint16",
        CType::UInt32 => "uint32",
        CType::Int64 => "int64",
        CType::UInt64 => "uint64",
        _ => return None,
    };
    let term =
        Bitvector32Term::opaque_conversion(format!("c_{source_name}_to_{target_name}"), value);
    Some(match target_type {
        CType::Int16 => CValue::Int16(term),
        CType::Int32 => CValue::Int32(term),
        CType::UInt8 => CValue::UInt8(term),
        CType::UInt16 => CValue::UInt16(term),
        CType::UInt32 => CValue::UInt32(term),
        CType::Int64 => CValue::Int64(term),
        CType::UInt64 => CValue::UInt64(term),
        _ => unreachable!(),
    })
}

pub(in crate::kernel) fn evaluate_c_expression(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Option<CExpressionOutcome> {
    let paths = evaluate_c_expression_paths(state, expression, assumptions, budget).ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() || !path.obligations.is_empty() {
        return None;
    }
    Some(path.outcome)
}

pub(in crate::kernel) fn add_uint8_range_execution_pure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    value: &Bitvector32Term,
) -> Option<()> {
    add_c_integer_range_execution_pure_facts(facts, assumptions, value, 0, 255)
}

pub(in crate::kernel) fn add_int16_range_execution_pure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    value: &Bitvector32Term,
) -> Option<()> {
    add_c_integer_range_execution_pure_facts(
        facts,
        assumptions,
        value,
        i32::from(i16::MIN),
        i32::from(i16::MAX),
    )
}

pub(in crate::kernel) fn add_uint16_range_execution_pure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    value: &Bitvector32Term,
) -> Option<()> {
    add_c_integer_range_execution_pure_facts(facts, assumptions, value, 0, i32::from(u16::MAX))
}

fn add_c_integer_range_execution_pure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
    value: &Bitvector32Term,
    lower: i32,
    upper: i32,
) -> Option<()> {
    add_internal_condition_path_fact(
        facts,
        assumptions,
        ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(lower as u32)),
        true,
    )?;
    add_internal_condition_path_fact(
        facts,
        assumptions,
        ConditionTerm::signed_less_equal(value.clone(), Bitvector32Term::Constant(upper as u32)),
        true,
    )
}

pub(in crate::kernel) fn promote_c_int32_path_value(
    value: CValue,
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
) -> Option<Bitvector32Term> {
    match value {
        CValue::Void => None,
        CValue::Int32(value) => Some(value),
        CValue::Int16(value) => {
            add_int16_range_execution_pure_facts(facts, assumptions, &value)?;
            Some(value)
        }
        CValue::UInt8(value) => {
            add_uint8_range_execution_pure_facts(facts, assumptions, &value)?;
            Some(value)
        }
        CValue::UInt16(value) => {
            add_uint16_range_execution_pure_facts(facts, assumptions, &value)?;
            Some(value)
        }
        CValue::UInt32(_) | CValue::Int64(_) | CValue::UInt64(_) => None,
        CValue::Pointer(_) | CValue::Float32(_) | CValue::Float64(_) => None,
    }
}

pub(in crate::kernel) fn promote_c_uint32_path_value(
    value: CValue,
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
) -> Option<Bitvector32Term> {
    match value {
        CValue::Int32(value) | CValue::UInt32(value) => Some(value),
        CValue::Int16(value) => {
            add_int16_range_execution_pure_facts(facts, assumptions, &value)?;
            Some(value)
        }
        CValue::UInt8(value) => {
            add_uint8_range_execution_pure_facts(facts, assumptions, &value)?;
            Some(value)
        }
        CValue::UInt16(value) => {
            add_uint16_range_execution_pure_facts(facts, assumptions, &value)?;
            Some(value)
        }
        CValue::Void
        | CValue::Int64(_)
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

pub(in crate::kernel) fn promote_c_int64_path_value(value: CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::Int64(value) => Some(value),
        CValue::Int16(value)
        | CValue::Int32(value)
        | CValue::UInt8(value)
        | CValue::UInt16(value) => Some(Bitvector32Term::int64_from_32(value)),
        CValue::UInt32(value) => Some(Bitvector32Term::int64_from_uint32(value)),
        CValue::Void
        | CValue::UInt64(_)
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

pub(in crate::kernel) fn promote_c_uint64_path_value(value: CValue) -> Option<Bitvector32Term> {
    match value {
        CValue::UInt64(value) => Some(value),
        CValue::UInt8(value) | CValue::UInt16(value) | CValue::UInt32(value) => {
            Some(Bitvector32Term::uint64_from_32(value))
        }
        CValue::Int16(value) | CValue::Int32(value) => {
            Some(Bitvector32Term::uint64_from_int32(value))
        }
        CValue::Int64(value) => Some(Bitvector32Term::uint64_from_int64(value)),
        CValue::Void | CValue::Pointer(_) | CValue::Float32(_) | CValue::Float64(_) => None,
    }
}

pub(in crate::kernel) fn coerce_c_value_to_type(
    value: CValue,
    target_type: CType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    if let Some(value) = coerce_c_null_pointer_constant(value.clone(), target_type) {
        return Some(value);
    }

    match (target_type, value) {
        (CType::Int32, CValue::Int16(value) | CValue::UInt8(value) | CValue::UInt16(value)) => {
            Some(CValue::Int32(value))
        }
        (CType::Int32, CValue::UInt32(value)) => Some(CValue::Int32(value)),
        (CType::Int32, CValue::Int64(value)) => {
            let value = value.int64_as_const()?;
            let value = i32::try_from(value).ok()?;
            Some(CValue::Int32(Bitvector32Term::Constant(value as u32)))
        }
        (CType::Int32, CValue::UInt64(value)) => {
            let value = value.uint64_as_const()?;
            let value = u32::try_from(value).ok()?;
            if value > i32::MAX as u32 {
                return None;
            }
            Some(CValue::Int32(Bitvector32Term::Constant(value)))
        }
        (
            CType::UInt32,
            CValue::Int16(value)
            | CValue::Int32(value)
            | CValue::UInt8(value)
            | CValue::UInt16(value),
        ) => Some(CValue::UInt32(value)),
        (CType::Int16, CValue::Int32(value)) => {
            add_signed_narrowing_obligations(
                obligations,
                assumptions,
                &value,
                i32::from(i16::MIN),
                i32::from(i16::MAX),
                "int16",
            )?;
            Some(CValue::Int16(value))
        }
        (CType::Int16, CValue::UInt8(value)) => Some(CValue::Int16(value)),
        (CType::Int16, CValue::UInt16(value)) => {
            add_signed_narrowing_obligations(
                obligations,
                assumptions,
                &value,
                i32::from(i16::MIN),
                i32::from(i16::MAX),
                "int16",
            )?;
            Some(CValue::Int16(value))
        }
        (CType::UInt16, CValue::Int32(value)) => {
            add_signed_narrowing_obligations(
                obligations,
                assumptions,
                &value,
                0,
                i32::from(u16::MAX),
                "uint16",
            )?;
            Some(CValue::UInt16(value))
        }
        (CType::UInt16, CValue::Int16(value)) => {
            add_signed_narrowing_obligations(
                obligations,
                assumptions,
                &value,
                0,
                i32::from(u16::MAX),
                "uint16",
            )?;
            Some(CValue::UInt16(value))
        }
        (CType::UInt16, CValue::UInt8(value)) => Some(CValue::UInt16(value)),
        (CType::UInt8, CValue::Int32(value)) => {
            add_signed_narrowing_obligations(obligations, assumptions, &value, 0, 255, "uint8")?;
            Some(CValue::UInt8(value))
        }
        (CType::Int64, CValue::Int64(value)) => Some(CValue::Int64(value)),
        (
            CType::Int64,
            CValue::Int16(value)
            | CValue::Int32(value)
            | CValue::UInt8(value)
            | CValue::UInt16(value),
        ) => Some(CValue::Int64(Bitvector32Term::int64_from_32(value))),
        (CType::Int64, CValue::UInt32(value)) => {
            Some(CValue::Int64(Bitvector32Term::int64_from_uint32(value)))
        }
        (CType::UInt64, CValue::UInt64(value)) => Some(CValue::UInt64(value)),
        (CType::UInt64, CValue::Int64(value)) => {
            Some(CValue::UInt64(Bitvector32Term::uint64_from_int64(value)))
        }
        (
            CType::UInt64,
            CValue::Int16(value)
            | CValue::Int32(value)
            | CValue::UInt8(value)
            | CValue::UInt16(value),
        ) => Some(CValue::UInt64(Bitvector32Term::uint64_from_int32(value))),
        (CType::UInt64, CValue::UInt32(value)) => {
            Some(CValue::UInt64(Bitvector32Term::uint64_from_32(value)))
        }
        (CType::Float32, CValue::Float32(value)) => Some(CValue::Float32(value)),
        (CType::Float32, CValue::Float64(value)) => {
            let converted = value
                .float64_as_const()
                .map(|value| Bitvector32Term::Constant(float64_to_float32_bits(value)))
                .unwrap_or_else(|| {
                    Bitvector32Term::opaque_conversion("c_float64_to_float32", value)
                });
            Some(CValue::Float32(converted))
        }
        (CType::Float64, CValue::Float64(value)) => Some(CValue::Float64(value)),
        (CType::Float64, CValue::Float32(value)) => {
            let converted = value
                .float32_as_const()
                .map(|value| Bitvector32Term::UInt64Constant(float32_to_float64_bits(value)))
                .unwrap_or_else(|| {
                    Bitvector32Term::opaque_conversion("c_float32_to_float64", value)
                });
            Some(CValue::Float64(converted))
        }
        (
            target @ (CType::Float32 | CType::Float64),
            value @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)
            | CValue::Int64(_)
            | CValue::UInt64(_)),
        ) => integer_to_float_value(value, target),
        (
            target @ (CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
            | CType::UInt64),
            CValue::Float32(value),
        ) => {
            if let Some(bits) = value.float32_as_const() {
                float32_to_integer_value(bits, target)
            } else {
                float_to_integer_conversion_value(
                    value,
                    CType::Float32,
                    target,
                    obligations,
                    assumptions,
                )
            }
        }
        (
            target @ (CType::Int16
            | CType::Int32
            | CType::UInt8
            | CType::UInt16
            | CType::UInt32
            | CType::Int64
            | CType::UInt64),
            CValue::Float64(value),
        ) => {
            if let Some(bits) = value.float64_as_const() {
                float64_to_integer_value(bits, target)
            } else {
                float_to_integer_conversion_value(
                    value,
                    CType::Float64,
                    target,
                    obligations,
                    assumptions,
                )
            }
        }
        _ => None,
    }
}

fn add_signed_narrowing_obligations(
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
    value: &Bitvector32Term,
    lower: i32,
    upper: i32,
    type_name: &str,
) -> Option<()> {
    add_proof_obligation_with_context(
        obligations,
        assumptions,
        Proposition::ConditionIs(
            ConditionTerm::signed_greater_equal(
                value.clone(),
                Bitvector32Term::Constant(lower as u32),
            ),
            true,
        ),
        Some(narrowing_context(type_name, true)),
    )?;
    add_proof_obligation_with_context(
        obligations,
        assumptions,
        Proposition::ConditionIs(
            ConditionTerm::signed_less_equal(
                value.clone(),
                Bitvector32Term::Constant(upper as u32),
            ),
            true,
        ),
        Some(narrowing_context(type_name, false)),
    )
}

fn narrowing_context(type_name: &str, lower: bool) -> &'static str {
    match (type_name, lower) {
        ("uint8", true) => "uint8 narrowing lower bound",
        ("uint8", false) => "uint8 narrowing upper bound",
        ("int16", true) => "int16 narrowing lower bound",
        ("int16", false) => "int16 narrowing upper bound",
        ("uint16", true) => "uint16 narrowing lower bound",
        ("uint16", false) => "uint16 narrowing upper bound",
        _ => "integer narrowing bound",
    }
}

fn cast_c_value_to_type(
    value: CValue,
    target_type: CType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Result<CValue, CRuntimeError> {
    if target_type.is_pointer() {
        match value {
            CValue::Pointer(pointer) => {
                return Ok(CValue::typed_pointer(pointer.into_pointer(), target_type));
            }
            // Integer-to-pointer conversion is accepted only for a 64-bit
            // value that is exactly the recorded address of an object
            // pointer, or the constant zero. Provenance comes from the term,
            // never from integer coincidence.
            CValue::UInt64(term) | CValue::Int64(term)
                if !matches!(target_type, CType::FunctionPointer(_)) =>
            {
                return match term {
                    Bitvector32Term::PointerAddress(pointer) => {
                        Ok(CValue::typed_pointer(*pointer, target_type))
                    }
                    term if term.uint64_as_const() == Some(0) => {
                        Ok(CValue::typed_pointer(Pointer::null(), target_type))
                    }
                    _ => Err(CRuntimeError::PointerConversion(
                        "integer-to-pointer cast requires a value that is a recorded pointer \
                         address or zero; an integer without pointer origin cannot become a \
                         pointer"
                            .to_string(),
                    )),
                };
            }
            value => {
                return coerce_c_value_to_type(value, target_type, obligations, assumptions)
                    .ok_or(CRuntimeError::TypeMismatch);
            }
        }
    }
    if let CValue::Pointer(pointer) = &value {
        // Pointer-to-integer conversion under LP64: the integer is the
        // pointer's address term, which keeps the exact source pointer. Null
        // is the integer zero; function addresses are not modeled.
        if !matches!(target_type, CType::UInt64 | CType::Int64) {
            return Err(CRuntimeError::PointerConversion(
                "pointer-to-integer cast requires a 64-bit integer type under the LP64 \
                 profile; a narrower integer cannot hold a pointer"
                    .to_string(),
            ));
        }
        if pointer.block.is_function() || matches!(pointer.c_type(), CType::FunctionPointer(_)) {
            return Err(CRuntimeError::PointerConversion(
                "function addresses do not convert to integers".to_string(),
            ));
        }
        let address = if pointer.is_null() {
            Bitvector32Term::UInt64Constant(0)
        } else {
            Bitvector32Term::PointerAddress(Box::new(pointer.pointer().clone()))
        };
        return Ok(match target_type {
            CType::UInt64 => CValue::UInt64(address),
            _ => CValue::Int64(address),
        });
    }
    coerce_c_value_to_type(value, target_type, obligations, assumptions)
        .ok_or(CRuntimeError::TypeMismatch)
}

pub(in crate::kernel) fn coerce_c_null_pointer_constant(
    value: CValue,
    target_type: CType,
) -> Option<CValue> {
    if target_type.accepts(&value) {
        return Some(match value {
            CValue::Pointer(pointer) if pointer.is_null() => {
                CValue::typed_pointer(pointer.into_pointer(), target_type)
            }
            value => value,
        });
    }
    match (target_type, value) {
        (target_type, CValue::Int32(Bitvector32Term::Constant(0))) if target_type.is_pointer() => {
            Some(CValue::typed_pointer(Pointer::null(), target_type))
        }
        _ => None,
    }
}

pub(in crate::kernel) fn evaluate_c_expression_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    budget.consume_expression_step()?;
    let paths = match expression {
        CExpression::Value(CValue::Void) => vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CExpression::Value(value) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value.clone()),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CExpression::Variable(name)
            if state.locals.is_array_object(name) || state.locals.is_aggregate_object(name) =>
        {
            let pointer = state
                .locals
                .slot(name)
                .expect("array binding must carry a stack slot")
                .clone();
            vec![CExpressionPath {
                outcome: if state.memory.has_block(&pointer.block) {
                    CExpressionOutcome::Value(CValue::typed_pointer(
                        pointer,
                        if state.locals.is_aggregate_object(name) {
                            CType::UInt8Pointer
                        } else {
                            state
                                .locals
                                .object_type(name)
                                .and_then(CType::pointer_to)
                                .unwrap_or(CType::Int32Pointer)
                        },
                    ))
                } else {
                    CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone()))
                },
                facts: Vec::new(),
                obligations: Vec::new(),
            }]
        }
        CExpression::Variable(_) => {
            read_c_lvalue_expression_paths(state, expression, assumptions, budget)?
        }
        CExpression::FunctionAddress(name) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(CValue::typed_pointer(
                Pointer::function(name.clone()),
                CType::FunctionPointer(0),
            )),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CExpression::Cast {
            expression,
            target_type,
        } => evaluate_c_cast_paths(state, expression, *target_type, assumptions, budget)?,
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => evaluate_c_conditional_paths(
            state,
            condition,
            then_branch,
            else_branch,
            assumptions,
            budget,
        )?,
        CExpression::FloatNegate(expression) => {
            evaluate_c_float_negate_paths(state, expression, assumptions, budget)?
        }
        CExpression::FloatClassification {
            expression,
            classification,
        } => evaluate_c_float_classification_paths(
            state,
            expression,
            *classification,
            assumptions,
            budget,
        )?,
        CExpression::AddressOf(target) => {
            address_of_lvalue_paths(state, target, assumptions, budget)?
        }
        CExpression::PointerOffsetBytes { pointer, bytes } => {
            evaluate_c_expression_paths(state, pointer, assumptions, budget)?
                .into_iter()
                .flat_map(|path| match path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => {
                        pointer_offset_by_bytes_paths(
                            state,
                            pointer,
                            *bytes,
                            path.facts,
                            path.obligations,
                            assumptions,
                        )
                    }
                    CExpressionOutcome::Value(_) => vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                    CExpressionOutcome::UndefinedBehavior(error) => vec![CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(error),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                    CExpressionOutcome::RuntimeError(error) => vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(error),
                        facts: path.facts,
                        obligations: path.obligations,
                    }],
                })
                .collect()
        }
        CExpression::LessThan(left, right) => evaluate_c_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            CComparisonOperator::LessThan,
        )?,
        CExpression::LessEqual(left, right) => evaluate_c_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            CComparisonOperator::LessEqual,
        )?,
        CExpression::GreaterThan(left, right) => evaluate_c_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            CComparisonOperator::GreaterThan,
        )?,
        CExpression::GreaterEqual(left, right) => evaluate_c_comparison_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            CComparisonOperator::GreaterEqual,
        )?,
        CExpression::Equal(left, right) => {
            evaluate_c_equal_paths(state, left, right, assumptions, budget)?
        }
        CExpression::NotEqual(left, right) => {
            evaluate_c_not_equal_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Not(expression) => {
            evaluate_c_not_paths(state, expression, assumptions, budget)?
        }
        CExpression::And(left, right) => {
            evaluate_c_logical_and_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Or(left, right) => {
            evaluate_c_logical_or_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Add(left, right) => {
            evaluate_c_add_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Subtract(left, right) => {
            evaluate_c_subtract_paths(state, left, right, assumptions, budget)?
        }
        CExpression::Multiply(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_multiply(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::Divide(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_divide(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::Remainder(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_remainder(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::ShiftLeft(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_shift_left(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::ShiftRight(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_shift_right(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::BitwiseAnd(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::And,
                )
            },
        )?,
        CExpression::BitwiseOr(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::Or,
                )
            },
        )?,
        CExpression::BitwiseXor(left, right) => evaluate_c_value_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_bitwise_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    assumptions,
                    CBitwiseOperation::Xor,
                )
            },
        )?,
        CExpression::BitwiseNot(expression) => {
            let mut paths = Vec::new();
            for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
                match path.outcome {
                    CExpressionOutcome::Value(value) => paths.extend(apply_c_bitwise_not(
                        value,
                        path.facts,
                        path.obligations,
                        assumptions,
                    )),
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(CExpressionPath {
                            outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                            facts: path.facts,
                            obligations: path.obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(error),
                        facts: path.facts,
                        obligations: path.obligations,
                    }),
                }
            }
            paths
        }
        // An inline array field is an lvalue whose value is not represented by
        // CValue. In an expression context it undergoes C's array-to-pointer
        // conversion, so evaluate the field's address rather than attempting
        // to load an aggregate value.
        CExpression::TypedLoad {
            pointer,
            value_type:
                CType::Int32Array(_)
                | CType::UInt8Array(_)
                | CType::Int16Array(_)
                | CType::UInt16Array(_)
                | CType::UInt32Array(_)
                | CType::Int64Array(_)
                | CType::UInt64Array(_),
        } => evaluate_c_expression_paths(state, pointer, assumptions, budget)?,
        CExpression::Load(_) | CExpression::TypedLoad { .. } | CExpression::Index(_, _) => {
            read_c_lvalue_expression_paths(state, expression, assumptions, budget)?
        }
    };
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_c_cast_paths(
    state: &CState,
    expression: &CExpression,
    target_type: CType,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            mut facts,
            mut obligations,
        } = path;
        let outcome = match outcome {
            CExpressionOutcome::Value(value) => {
                let effective_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                let coerced = if target_type == CType::Int32 {
                    match value {
                        value @ (CValue::Int16(_) | CValue::UInt8(_) | CValue::UInt16(_)) => {
                            promote_c_int32_path_value(value, &mut facts, &effective_assumptions)
                                .map(CValue::Int32)
                                .ok_or(CRuntimeError::TypeMismatch)
                        }
                        value => cast_c_value_to_type(
                            value,
                            target_type,
                            &mut obligations,
                            &effective_assumptions,
                        ),
                    }
                } else {
                    cast_c_value_to_type(
                        value,
                        target_type,
                        &mut obligations,
                        &effective_assumptions,
                    )
                };
                match coerced {
                    Ok(value) => CExpressionOutcome::Value(value),
                    Err(error) => CExpressionOutcome::RuntimeError(error),
                }
            }
            CExpressionOutcome::UndefinedBehavior(error) => {
                CExpressionOutcome::UndefinedBehavior(error)
            }
            CExpressionOutcome::RuntimeError(error) => CExpressionOutcome::RuntimeError(error),
        };
        paths.push(CExpressionPath {
            outcome,
            facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_c_float_classification_paths(
    state: &CState,
    expression: &CExpression,
    classification: CFloatClassification,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        match path.outcome {
            CExpressionOutcome::Value(CValue::Float32(value)) => {
                paths.extend(condition_as_c_int32_paths(
                    ConditionTerm::float32_classification(value, classification),
                    path.facts,
                    path.obligations,
                    assumptions,
                ));
            }
            CExpressionOutcome::Value(CValue::Float64(value)) => {
                paths.extend(condition_as_c_int32_paths(
                    ConditionTerm::float64_classification(value, classification),
                    path.facts,
                    path.obligations,
                    assumptions,
                ));
            }
            CExpressionOutcome::Value(_) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts: path.facts,
                obligations: path.obligations,
            }),
            CExpressionOutcome::UndefinedBehavior(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(error),
                facts: path.facts,
                obligations: path.obligations,
            }),
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: path.facts,
                obligations: path.obligations,
            }),
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_c_float_negate_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = path;
        let outcome = match outcome {
            CExpressionOutcome::Value(CValue::Float32(value)) => {
                CExpressionOutcome::Value(CValue::Float32(Bitvector32Term::float32_negate(value)))
            }
            CExpressionOutcome::Value(CValue::Float64(value)) => {
                CExpressionOutcome::Value(CValue::Float64(Bitvector32Term::float64_negate(value)))
            }
            CExpressionOutcome::Value(_) => {
                CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
            }
            CExpressionOutcome::UndefinedBehavior(error) => {
                CExpressionOutcome::UndefinedBehavior(error)
            }
            CExpressionOutcome::RuntimeError(error) => CExpressionOutcome::RuntimeError(error),
        };
        paths.push(CExpressionPath {
            outcome,
            facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn evaluate_c_conditional_paths(
    state: &CState,
    condition: &CExpression,
    then_branch: &CExpression,
    else_branch: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for condition_path in evaluate_c_expression_paths(state, condition, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = condition_path;
        let CExpressionOutcome::Value(value) = outcome else {
            paths.push(CExpressionPath {
                outcome,
                facts,
                obligations,
            });
            continue;
        };

        for truthiness in c_truthiness_paths(value, facts, obligations, assumptions) {
            let branch = if truthiness.is_true {
                then_branch
            } else {
                else_branch
            };
            let branch_assumptions = assumptions_with_path_context(
                assumptions,
                &truthiness.facts,
                &truthiness.obligations,
            );
            for branch_path in
                evaluate_c_expression_paths(state, branch, &branch_assumptions, budget)?
            {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &truthiness.facts,
                    &truthiness.obligations,
                    &branch_path.facts,
                    &branch_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                paths.push(CExpressionPath {
                    outcome: branch_path.outcome,
                    facts,
                    obligations,
                });
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn evaluate_c_lvalue_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CLValuePath>> {
    budget.consume_expression_step()?;
    let paths = match expression {
        CExpression::Variable(name) => vec![CLValuePath {
            outcome: match state.locals.binding(name) {
                Some(CLocalBinding::Object {
                    c_type,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                    ..
                })
                | Some(CLocalBinding::UninitializedObject {
                    c_type,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                    ..
                }) => {
                    let lvalue = CLValue::local_with_qualifiers(
                        name.clone(),
                        *c_type,
                        *volatile,
                        *pointee_volatile,
                    )
                    .with_constant(*constant)
                    .with_pointee_constant(*pointee_constant);
                    CLValueOutcome::LValue(lvalue)
                }
                Some(CLocalBinding::GlobalObject {
                    c_type,
                    slot,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                }) => CLValueOutcome::LValue(
                    CLValue::memory_with_qualifiers(
                        slot.clone(),
                        *c_type,
                        *volatile,
                        *pointee_volatile,
                    )
                    .with_constant(*constant)
                    .with_pointee_constant(*pointee_constant),
                ),
                Some(CLocalBinding::ArrayObject { .. }) => {
                    CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                }
                Some(CLocalBinding::AggregateObject { .. }) => {
                    CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                }
                None => CLValueOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone())),
            },
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CExpression::Load(pointer_expression) => {
            let Some(value_type) = c_expression_pointee_type(state, pointer_expression) else {
                return Ok(vec![CLValuePath {
                    outcome: CLValueOutcome::RuntimeError(CRuntimeError::IndeterminatePointeeType),
                    facts: Vec::new(),
                    obligations: Vec::new(),
                }]);
            };
            let mut paths = Vec::new();
            for pointer_path in
                evaluate_c_expression_paths(state, pointer_expression, assumptions, budget)?
            {
                paths.push(match pointer_path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => CLValuePath {
                        outcome: CLValueOutcome::LValue(
                            CLValue::memory_with_volatile(
                                pointer.pointer().clone(),
                                value_type,
                                pointer.pointee_volatile(),
                            )
                            .with_pointee_constant(pointer.pointee_constant()),
                        ),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::Value(_) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => CLValuePath {
                        outcome: CLValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::RuntimeError(error) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        CExpression::TypedLoad {
            pointer: pointer_expression,
            value_type,
        } => {
            let mut paths = Vec::new();
            for pointer_path in
                evaluate_c_expression_paths(state, pointer_expression, assumptions, budget)?
            {
                paths.push(match pointer_path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => CLValuePath {
                        outcome: CLValueOutcome::LValue(
                            CLValue::memory_with_volatile(
                                pointer.pointer().clone(),
                                *value_type,
                                pointer.pointee_volatile(),
                            )
                            .with_pointee_constant(pointer.pointee_constant()),
                        ),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::Value(_) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => CLValuePath {
                        outcome: CLValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::RuntimeError(error) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        CExpression::Index(base, index) => {
            let Some(value_type) = c_expression_pointee_type(state, base) else {
                return Ok(vec![CLValuePath {
                    outcome: CLValueOutcome::RuntimeError(CRuntimeError::IndeterminatePointeeType),
                    facts: Vec::new(),
                    obligations: Vec::new(),
                }]);
            };
            let mut paths = Vec::new();
            for pointer_path in evaluate_c_add_paths(state, base, index, assumptions, budget)? {
                paths.push(match pointer_path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => CLValuePath {
                        outcome: CLValueOutcome::LValue(
                            CLValue::memory_with_volatile(
                                pointer.pointer().clone(),
                                value_type,
                                pointer.pointee_volatile(),
                            )
                            .with_pointee_constant(pointer.pointee_constant()),
                        ),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::Value(_) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => CLValuePath {
                        outcome: CLValueOutcome::UndefinedBehavior(undefined_behavior),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                    CExpressionOutcome::RuntimeError(error) => CLValuePath {
                        outcome: CLValueOutcome::RuntimeError(error),
                        facts: pointer_path.facts,
                        obligations: pointer_path.obligations,
                    },
                });
            }
            paths
        }
        _ => vec![CLValuePath {
            outcome: CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
    };
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn read_c_lvalue_expression_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for lvalue_path in evaluate_c_lvalue_paths(state, expression, assumptions, budget)? {
        paths.extend(read_c_lvalue_paths(
            state,
            lvalue_path.outcome,
            lvalue_path.facts,
            lvalue_path.obligations,
            assumptions,
            &mut budget.next_kernel_variable,
        ));
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn read_c_lvalue_paths(
    state: &CState,
    outcome: CLValueOutcome,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    next_kernel_variable: &mut u64,
) -> Vec<CExpressionPath> {
    match outcome {
        CLValueOutcome::LValue(lvalue) => match &lvalue.storage {
            CLValueStorage::Local { name } => {
                let outcome = match state.locals.get(name) {
                    Some(value) if lvalue.value_type.accepts(value) => CExpressionOutcome::Value(
                        value
                            .clone()
                            .with_pointer_pointee_volatile(lvalue.pointee_is_volatile())
                            .with_pointer_pointee_constant(lvalue.pointee_is_constant()),
                    ),
                    Some(_) => CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    None if matches!(
                        state.locals.binding(name),
                        Some(CLocalBinding::UninitializedObject { .. })
                    ) =>
                    {
                        CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::UninitializedRead)
                    }
                    None => CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(
                        name.clone(),
                    )),
                };
                let mut facts = facts;
                if lvalue.is_volatile()
                    && let CExpressionOutcome::Value(value) = &outcome
                    && let Some(pointer) = lvalue.pointer(state)
                {
                    facts.push(volatile_access_fact(
                        next_kernel_variable,
                        false,
                        pointer,
                        lvalue.value_type,
                        value.clone(),
                    ));
                }
                vec![CExpressionPath {
                    outcome,
                    facts,
                    obligations,
                }]
            }
            CLValueStorage::Memory { pointer } => {
                if state
                    .memory
                    .heap
                    .pending_reallocations
                    .values()
                    .any(|pending| pending.old_pointer.block == pointer.block)
                {
                    return vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(
                            CRuntimeError::UnresolvedAllocationOutcome,
                        ),
                        facts,
                        obligations,
                    }];
                }
                if state.memory.is_deallocated_heap_address(pointer) {
                    return vec![CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(
                            CUndefinedBehavior::InvalidMemory,
                        ),
                        facts,
                        obligations,
                    }];
                }
                let effective_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                let is_external = is_external_memory_pointer(pointer);
                let has_external_read_resource = is_external
                    && (assumptions.should_allow_symbolic_contract_loads()
                        || resource_context_has_read(
                            state.resources(),
                            pointer,
                            lvalue.value_type.byte_width(),
                            &effective_assumptions,
                        ));
                if is_external && !has_external_read_resource {
                    return vec![CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::MissingResource {
                            resource: CResourceFact::view_memory(CMemoryRange::new(
                                pointer.clone(),
                                Bitvector32Term::Constant(0),
                                Bitvector32Term::Constant(1),
                            )),
                        }),
                        facts,
                        obligations,
                    }];
                }
                let paths = evaluate_c_memory_load_paths(
                    &state.memory,
                    pointer.clone(),
                    lvalue.value_type,
                    facts,
                    obligations,
                    assumptions,
                    has_external_read_resource,
                    next_kernel_variable,
                );
                if !lvalue.is_volatile() {
                    return paths;
                }
                paths
                    .into_iter()
                    .map(|mut path| {
                        if let CExpressionOutcome::Value(value) = &path.outcome {
                            path.facts.push(volatile_access_fact(
                                next_kernel_variable,
                                false,
                                pointer.clone(),
                                lvalue.value_type,
                                value.clone(),
                            ));
                        }
                        path
                    })
                    .collect()
            }
        },
        CLValueOutcome::UndefinedBehavior(undefined_behavior) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
            facts,
            obligations,
        }],
        CLValueOutcome::RuntimeError(error) => vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(error),
            facts,
            obligations,
        }],
    }
}

pub(in crate::kernel) fn address_of_lvalue_paths(
    state: &CState,
    target: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for lvalue_path in evaluate_c_lvalue_paths(state, target, assumptions, budget)? {
        paths.push(match lvalue_path.outcome {
            CLValueOutcome::LValue(lvalue) => match lvalue.pointer(state) {
                Some(pointer) => match lvalue.value_type().pointer_to() {
                    Some(pointer_type) => CExpressionPath {
                        outcome: CExpressionOutcome::Value(
                            CValue::typed_pointer_with_pointee_volatile(
                                pointer,
                                pointer_type,
                                lvalue.is_volatile(),
                            )
                            .with_pointer_pointee_constant(lvalue.is_constant()),
                        ),
                        facts: lvalue_path.facts,
                        obligations: lvalue_path.obligations,
                    },
                    None => CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: lvalue_path.facts,
                        obligations: lvalue_path.obligations,
                    },
                },
                None => CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(
                        format!("{target:?}"),
                    )),
                    facts: lvalue_path.facts,
                    obligations: lvalue_path.obligations,
                },
            },
            CLValueOutcome::UndefinedBehavior(undefined_behavior) => CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                facts: lvalue_path.facts,
                obligations: lvalue_path.obligations,
            },
            CLValueOutcome::RuntimeError(error) => CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: lvalue_path.facts,
                obligations: lvalue_path.obligations,
            },
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn is_external_memory_pointer(pointer: &Pointer) -> bool {
    !pointer.block.starts_with("local:")
        && !pointer.block.starts_with("global:")
        && !pointer.block.starts_with("static:")
        && !pointer.block.starts_with("string:")
        && !pointer.block.starts_with("havoc:")
}

pub(in crate::kernel) fn c_expression_pointee_type(
    state: &CState,
    expression: &CExpression,
) -> Option<CType> {
    match expression {
        CExpression::Variable(name) => match state.locals.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => c_type.pointee_type(),
            Some(CLocalBinding::UninitializedObject { c_type, .. }) => c_type.pointee_type(),
            Some(CLocalBinding::GlobalObject { c_type, .. }) => c_type.pointee_type(),
            Some(CLocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            Some(CLocalBinding::AggregateObject { .. }) => Some(CType::UInt8),
            None => None,
        },
        CExpression::Cast { target_type, .. } => target_type.pointee_type(),
        CExpression::AddressOf(target) => c_expression_lvalue_type(state, target),
        CExpression::PointerOffsetBytes { pointer, .. } => {
            c_expression_pointee_type(state, pointer)
        }
        CExpression::TypedLoad { value_type, .. } => match value_type {
            CType::Int32Array(_) => Some(CType::Int32),
            CType::UInt8Array(_) => Some(CType::UInt8),
            CType::Int16Array(_) => Some(CType::Int16),
            CType::UInt16Array(_) => Some(CType::UInt16),
            CType::UInt32Array(_) => Some(CType::UInt32),
            CType::Int64Array(_) => Some(CType::Int64),
            CType::UInt64Array(_) => Some(CType::UInt64),
            value_type => value_type.pointee_type(),
        },
        CExpression::Add(left, right) => c_expression_pointee_type(state, left)
            .or_else(|| c_expression_pointee_type(state, right)),
        CExpression::Subtract(left, _) => c_expression_pointee_type(state, left),
        // An indexed pointer expression is itself the value stored in the
        // selected cell. For `slots[0]` where `slots` is `int32**`, the
        // lvalue type is `int32*`, so its pointee type is `int32`.
        CExpression::Index(base, _) => {
            c_expression_pointee_type(state, base).and_then(CType::pointee_type)
        }
        _ => None,
    }
}

pub(in crate::kernel) fn c_expression_lvalue_type(
    state: &CState,
    expression: &CExpression,
) -> Option<CType> {
    match expression {
        CExpression::Variable(name) => state.locals.object_type(name),
        CExpression::Load(pointer) => c_expression_pointee_type(state, pointer),
        CExpression::TypedLoad { value_type, .. } => Some(*value_type),
        CExpression::Index(base, _) => c_expression_pointee_type(state, base),
        _ => None,
    }
}

pub(in crate::kernel) fn c_expression_pointer_step_width(
    state: &CState,
    expression: &CExpression,
) -> Option<u32> {
    c_expression_pointee_type(state, expression).map(CType::byte_width)
}

pub(in crate::kernel) fn condition_as_c_int32_paths(
    condition: ConditionTerm,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    match decide_with_facts(assumptions, &facts, &condition) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(1)),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(0)),
            facts,
            obligations,
        }],
        None => {
            let mut true_facts = facts.clone();
            add_condition_path_fact(&mut true_facts, assumptions, condition.clone(), true)
                .expect("unknown comparison fact should be consistent");

            let mut false_facts = facts;
            add_condition_path_fact(&mut false_facts, assumptions, condition, false)
                .expect("unknown comparison fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(1)),
                    facts: true_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(0)),
                    facts: false_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn condition_as_c_int32_not_paths(
    condition: ConditionTerm,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    match decide_with_facts(assumptions, &facts, &condition) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(0)),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(1)),
            facts,
            obligations,
        }],
        None => {
            let mut true_facts = facts.clone();
            add_condition_path_fact(&mut true_facts, assumptions, condition.clone(), true)
                .expect("unknown comparison fact should be consistent");

            let mut false_facts = facts;
            add_condition_path_fact(&mut false_facts, assumptions, condition, false)
                .expect("unknown comparison fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(0)),
                    facts: true_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(1)),
                    facts: false_facts,
                    obligations,
                },
            ]
        }
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct CTruthinessPath {
    pub(in crate::kernel) is_true: bool,
    pub(in crate::kernel) facts: Vec<ExecutionPureFact>,
    pub(in crate::kernel) obligations: Vec<ProofObligation>,
}

pub(in crate::kernel) fn c_truthiness_paths(
    value: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CTruthinessPath> {
    match value {
        CValue::Void => unreachable!("void truthiness must be rejected by the caller"),
        CValue::Int16(bits)
        | CValue::Int32(bits)
        | CValue::UInt8(bits)
        | CValue::UInt16(bits)
        | CValue::UInt32(bits) => {
            let is_zero = ConditionTerm::equal(bits, Bitvector32Term::Constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(true) => vec![CTruthinessPath {
                    is_true: false,
                    facts,
                    obligations,
                }],
                Some(false) => vec![CTruthinessPath {
                    is_true: true,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown truthiness fact should be consistent");

                    let mut false_facts = facts;
                    add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown truthiness fact should be consistent");

                    vec![
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        CValue::Int64(bits) => {
            let is_zero = ConditionTerm::int64_equal(bits, Bitvector32Term::Int64Constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(is_zero) => vec![CTruthinessPath {
                    is_true: !is_zero,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown truthiness fact should be consistent");
                    let mut false_facts = facts;
                    add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown truthiness fact should be consistent");
                    vec![
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        CValue::UInt64(bits) => {
            let is_zero = ConditionTerm::uint64_equal(bits, Bitvector32Term::UInt64Constant(0));
            match decide_with_facts(assumptions, &facts, &is_zero) {
                Some(is_zero) => vec![CTruthinessPath {
                    is_true: !is_zero,
                    facts,
                    obligations,
                }],
                None => {
                    let mut true_facts = facts.clone();
                    add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                        .expect("unknown truthiness fact should be consistent");
                    let mut false_facts = facts;
                    add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                        .expect("unknown truthiness fact should be consistent");
                    vec![
                        CTruthinessPath {
                            is_true: true,
                            facts: true_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: false_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
        CValue::Float32(bits) => c_float_truthiness_paths(
            ConditionTerm::float32_classification(bits, CFloatClassification::Zero),
            facts,
            obligations,
            assumptions,
        ),
        CValue::Float64(bits) => c_float_truthiness_paths(
            ConditionTerm::float64_classification(bits, CFloatClassification::Zero),
            facts,
            obligations,
            assumptions,
        ),
        CValue::Pointer(pointer) => {
            let is_null = pointer_is_null_condition(pointer.pointer().clone());
            match decide_with_facts(assumptions, &facts, &is_null) {
                Some(true) => vec![CTruthinessPath {
                    is_true: false,
                    facts,
                    obligations,
                }],
                Some(false) => vec![CTruthinessPath {
                    is_true: true,
                    facts,
                    obligations,
                }],
                None => {
                    let mut nonnull_facts = facts.clone();
                    add_condition_path_fact(
                        &mut nonnull_facts,
                        assumptions,
                        is_null.clone(),
                        false,
                    )
                    .expect("unknown pointer truthiness fact should be consistent");

                    let mut null_facts = facts;
                    add_condition_path_fact(&mut null_facts, assumptions, is_null, true)
                        .expect("unknown pointer truthiness fact should be consistent");

                    vec![
                        CTruthinessPath {
                            is_true: true,
                            facts: nonnull_facts,
                            obligations: obligations.clone(),
                        },
                        CTruthinessPath {
                            is_true: false,
                            facts: null_facts,
                            obligations,
                        },
                    ]
                }
            }
        }
    }
}

fn c_float_truthiness_paths(
    is_zero: ConditionTerm,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CTruthinessPath> {
    match decide_with_facts(assumptions, &facts, &is_zero) {
        Some(is_zero) => vec![CTruthinessPath {
            is_true: !is_zero,
            facts,
            obligations,
        }],
        None => {
            let mut true_facts = facts.clone();
            add_condition_path_fact(&mut true_facts, assumptions, is_zero.clone(), false)
                .expect("unknown floating truthiness fact should be consistent");
            let mut false_facts = facts;
            add_condition_path_fact(&mut false_facts, assumptions, is_zero, true)
                .expect("unknown floating truthiness fact should be consistent");
            vec![
                CTruthinessPath {
                    is_true: true,
                    facts: true_facts,
                    obligations: obligations.clone(),
                },
                CTruthinessPath {
                    is_true: false,
                    facts: false_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn c_truthiness_as_c_int32_paths(
    value: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    c_truthiness_paths(value, facts, obligations, assumptions)
        .into_iter()
        .map(|path| CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(if path.is_true { 1 } else { 0 })),
            facts: path.facts,
            obligations: path.obligations,
        })
        .collect()
}
