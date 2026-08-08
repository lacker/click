use super::*;

pub(in crate::lang::click) fn evaluate_c_contract_expression(
    parameter_values: &BTreeMap<String, CValue>,
    state: &CState,
    result: Option<&CValue>,
    assumptions: &Assumptions,
    expression: &CExpression,
) -> Result<CValue, String> {
    match expression {
        CExpression::Value(value) => Ok(value.clone()),
        CExpression::Variable(name) if name == "result" => result
            .cloned()
            .ok_or_else(|| "`result` is not available inside `old(...)`".to_string()),
        CExpression::Variable(name) => parameter_values
            .get(name)
            .cloned()
            .ok_or_else(|| format!("unknown contract variable `{name}`")),
        CExpression::PointerOffsetBytes { pointer, bytes } => {
            let pointer = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                pointer,
            )?;
            let CValue::Pointer(pointer) = pointer else {
                return Err("byte-offset base is not a pointer".to_string());
            };
            Ok(CValue::Pointer(pointer.offset_by_bytes(*bytes)))
        }
        CExpression::Add(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_add(left, right)
        }
        CExpression::Subtract(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_sub(left, right)
        }
        CExpression::Multiply(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_multiply(left, right)
        }
        CExpression::Divide(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_divide(left, right)
        }
        CExpression::Remainder(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_remainder(left, right)
        }
        CExpression::ShiftLeft(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_shift_left(left, right)
        }
        CExpression::ShiftRight(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_shift_right(left, right)
        }
        CExpression::BitwiseAnd(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "&", bitvector32_and)
        }
        CExpression::BitwiseOr(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "|", bitvector32_or)
        }
        CExpression::BitwiseXor(left, right) => {
            let left =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, left)?;
            let right = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                right,
            )?;
            evaluate_postcondition_bitwise_binary(left, right, "^", bitvector32_xor)
        }
        CExpression::BitwiseNot(expression) => {
            let value = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                expression,
            )?;
            evaluate_postcondition_bitwise_not(value)
        }
        CExpression::Load(pointer) => {
            let surface_pointer = pointer.as_ref().clone();
            let pointer = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                pointer,
            )?;
            let CValue::Pointer(pointer) = pointer else {
                return Err("field load base is not a pointer".to_string());
            };
            let value =
                evaluate_contract_memory_load(state, pointer.clone(), CType::Int32, assumptions)?;
            record_surface_loadability_segment(
                state.memory(),
                &pointer,
                CType::Int32,
                surface_pointer,
                CExpression::Value(int32(0)),
                CExpression::Value(int32(1)),
            );
            Ok(value)
        }
        CExpression::TypedLoad {
            pointer,
            value_type,
        } => {
            let surface_pointer = pointer.as_ref().clone();
            let pointer = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                pointer,
            )?;
            let CValue::Pointer(pointer) = pointer else {
                return Err("field load base is not a pointer".to_string());
            };
            let value =
                evaluate_contract_memory_load(state, pointer.clone(), *value_type, assumptions)?;
            if value_type.byte_width() == 4 {
                record_surface_loadability_segment(
                    state.memory(),
                    &pointer,
                    *value_type,
                    surface_pointer,
                    CExpression::Value(int32(0)),
                    CExpression::Value(int32(1)),
                );
            }
            Ok(value)
        }
        CExpression::Index(base, index) => {
            let surface_base = base.as_ref().clone();
            let surface_index = index.as_ref().clone();
            let base =
                evaluate_c_contract_expression(parameter_values, state, result, assumptions, base)?;
            let index = evaluate_c_contract_expression(
                parameter_values,
                state,
                result,
                assumptions,
                index,
            )?;
            let pointer = evaluate_postcondition_pointer_add(base, index)?;
            let value =
                evaluate_contract_memory_load(state, pointer.clone(), CType::Int32, assumptions)?;
            record_surface_loadability_segment(
                state.memory(),
                &pointer,
                CType::Int32,
                CExpression::Add(Box::new(surface_base), Box::new(surface_index)),
                CExpression::Value(int32(0)),
                CExpression::Value(int32(1)),
            );
            Ok(value)
        }
        _ => Err(format!(
            "unsupported postcondition expression `{expression:?}`"
        )),
    }
}

pub(in crate::lang::click) fn evaluate_contract_memory_load(
    state: &CState,
    pointer: Pointer,
    value_type: CType,
    assumptions: &Assumptions,
) -> Result<CValue, String> {
    evaluate_contract_memory_load_from_memory(state.memory(), pointer, value_type, assumptions)
}

pub(in crate::lang::click) fn evaluate_contract_memory_load_from_memory(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    assumptions: &Assumptions,
) -> Result<CValue, String> {
    let required = Proposition::CMemoryLoadable {
        memory: memory.clone(),
        base: pointer.clone(),
        bytes: Bitvector32Term::Constant(value_type.byte_width()),
    };
    let outcome = memory.load(&pointer);
    if assumptions.should_allow_symbolic_contract_loads()
        && matches!(outcome, crate::kernel::CExpressionOutcome::Value(_))
        && !assumptions.proves(&required)
    {
        record_surface_loadability_obligation(&required);
    }
    match outcome {
        crate::kernel::CExpressionOutcome::Value(value)
            if c_value_matches_kernel_type(&value, value_type) =>
        {
            Ok(value)
        }
        crate::kernel::CExpressionOutcome::Value(CValue::Int32(
            bits @ Bitvector32Term::MemoryLoad(_, _),
        )) if matches!(value_type, CType::Int32Pointer | CType::UInt8Pointer) => {
            symbolic_pointer_contract_memory_load(pointer, bits, value_type)
        }
        crate::kernel::CExpressionOutcome::Value(value) => Err(format!(
            "load from {pointer:?} produced {value:?}, not {value_type:?}"
        )),
        outcome => {
            if assumptions.should_allow_symbolic_contract_loads() {
                if !assumptions.proves(&required) {
                    record_surface_loadability_obligation(&required);
                }
                return symbolic_contract_memory_load(memory, pointer, value_type);
            }
            if value_type == CType::Int32
                && assumptions
                    .pure_facts()
                    .iter()
                    .any(|fact| proposition_certifies_contract_load(fact, memory, &pointer))
            {
                return symbolic_contract_memory_load(memory, pointer, value_type);
            }
            let is_loadable = if assumptions.should_defer_non_exact_loadability_obligations() {
                assumptions.proves_memory_loadable_for_memory_resolution(
                    memory,
                    &pointer,
                    &Bitvector32Term::Constant(value_type.byte_width()),
                )
            } else {
                assumptions.proves(&required)
            };
            if is_loadable {
                return symbolic_contract_memory_load(memory, pointer, value_type);
            }
            let pure_facts = assumptions.pure_facts();
            Err(format!(
                "{}\n  load from {pointer:?} as {value_type:?} produced {outcome:?}",
                describe_missing_pure_fact(&required, &pure_facts, &[], &[], &[], &[])
            ))
        }
    }
}

fn proposition_certifies_contract_load(
    proposition: &Proposition,
    memory: &CMemory,
    pointer: &Pointer,
) -> bool {
    let Proposition::ConditionIs(condition, _) = proposition else {
        return false;
    };
    condition_contains_contract_load(condition, memory, pointer)
}

fn condition_contains_contract_load(
    condition: &ConditionTerm,
    memory: &CMemory,
    pointer: &Pointer,
) -> bool {
    match condition {
        ConditionTerm::Bitvector32SignedLessThan(left, right)
        | ConditionTerm::Bitvector32SignedLessEqual(left, right)
        | ConditionTerm::Bitvector32SignedGreaterThan(left, right)
        | ConditionTerm::Bitvector32SignedGreaterEqual(left, right)
        | ConditionTerm::Bitvector32Equal(left, right)
        | ConditionTerm::Bitvector32SignedAddOverflows(left, right)
        | ConditionTerm::Bitvector32SignedSubtractOverflows(left, right)
        | ConditionTerm::Bitvector32SignedMultiplyOverflows(left, right)
        | ConditionTerm::Bitvector32SignedDivideOverflows(left, right)
        | ConditionTerm::Bitvector32SignedShiftLeftOverflows(left, right) => {
            bitvector_contains_contract_load(left, memory, pointer)
                || bitvector_contains_contract_load(right, memory, pointer)
        }
        ConditionTerm::PointerOffsetEqual(left, right) => {
            pointer_offset_contains_contract_load(left, memory, pointer)
                || pointer_offset_contains_contract_load(right, memory, pointer)
        }
        ConditionTerm::PointerEqual(left, right) => {
            pointer_offset_contains_contract_load(&left.offset, memory, pointer)
                || pointer_offset_contains_contract_load(&right.offset, memory, pointer)
        }
        ConditionTerm::Constant(_) | ConditionTerm::Variable(_) => false,
    }
}

fn pointer_offset_contains_contract_load(
    term: &PointerOffsetTerm,
    memory: &CMemory,
    pointer: &Pointer,
) -> bool {
    match term {
        PointerOffsetTerm::Constant(_) | PointerOffsetTerm::Variable(_) => false,
        PointerOffsetTerm::Add(left, right) => {
            pointer_offset_contains_contract_load(left, memory, pointer)
                || pointer_offset_contains_contract_load(right, memory, pointer)
        }
        PointerOffsetTerm::Int32Scaled { value, .. } => {
            bitvector_contains_contract_load(value, memory, pointer)
        }
    }
}

fn bitvector_contains_contract_load(
    term: &Bitvector32Term,
    memory: &CMemory,
    pointer: &Pointer,
) -> bool {
    match term {
        Bitvector32Term::Constant(_) | Bitvector32Term::Variable(_) => false,
        Bitvector32Term::MemoryLoad(load_memory, load_pointer) => {
            load_memory.has_same_snapshot_markers(memory)
                && load_pointer.block == pointer.block
                && normalize_direct_atomic_pointer_offset_loads(&load_pointer.offset)
                    == normalize_direct_atomic_pointer_offset_loads(&pointer.offset)
                || pointer_offset_contains_contract_load(&load_pointer.offset, memory, pointer)
        }
        Bitvector32Term::Add(left, right)
        | Bitvector32Term::Subtract(left, right)
        | Bitvector32Term::Multiply(left, right)
        | Bitvector32Term::Divide(left, right)
        | Bitvector32Term::Remainder(left, right)
        | Bitvector32Term::ShiftLeft(left, right)
        | Bitvector32Term::ArithmeticShiftRight(left, right)
        | Bitvector32Term::BitwiseAnd(left, right)
        | Bitvector32Term::BitwiseOr(left, right)
        | Bitvector32Term::BitwiseXor(left, right) => {
            bitvector_contains_contract_load(left, memory, pointer)
                || bitvector_contains_contract_load(right, memory, pointer)
        }
        Bitvector32Term::BitwiseNot(value) => {
            bitvector_contains_contract_load(value, memory, pointer)
        }
        Bitvector32Term::If {
            condition,
            then_term,
            else_term,
        } => {
            condition_contains_contract_load(condition, memory, pointer)
                || bitvector_contains_contract_load(then_term, memory, pointer)
                || bitvector_contains_contract_load(else_term, memory, pointer)
        }
        Bitvector32Term::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            bitvector_contains_contract_load(start, memory, pointer)
                || bitvector_contains_contract_load(end, memory, pointer)
                || bitvector_contains_contract_load(initial, memory, pointer)
                || bitvector_contains_contract_load(body, memory, pointer)
        }
        Bitvector32Term::PureFunctionApplication { arguments, .. } => arguments
            .iter()
            .any(|argument| bitvector_contains_contract_load(argument, memory, pointer)),
    }
}

pub(in crate::lang::click) fn c_value_matches_kernel_type(value: &CValue, c_type: CType) -> bool {
    matches!(
        (value, c_type),
        (CValue::Int32(_), CType::Int32)
            | (CValue::UInt8(_), CType::UInt8)
            | (
                CValue::Pointer(_),
                CType::Int32Pointer | CType::UInt8Pointer
            )
    )
}

pub(in crate::lang::click) fn symbolic_contract_memory_load(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
) -> Result<CValue, String> {
    let load = Bitvector32Term::MemoryLoad(
        crate::kernel::intern_c_memory(memory.clone()),
        Box::new(pointer.clone()),
    );
    match value_type {
        CType::Void => Err("cannot symbolically load void".to_string()),
        CType::Int32 => Ok(CValue::Int32(load)),
        CType::UInt8 => Ok(CValue::UInt8(load)),
        CType::Int32Pointer | CType::UInt8Pointer => {
            symbolic_pointer_contract_memory_load(pointer, load, value_type)
        }
        CType::Int32Array(_) | CType::UInt8Array(_) => {
            Err(format!("cannot symbolically load {value_type:?}"))
        }
    }
}

fn symbolic_pointer_contract_memory_load(
    pointer: Pointer,
    bits: Bitvector32Term,
    value_type: CType,
) -> Result<CValue, String> {
    let pointee_byte_width = match value_type {
        CType::Int32Pointer => 4,
        CType::UInt8Pointer => 1,
        _ => {
            return Err(format!(
                "cannot symbolically load {value_type:?} as pointer"
            ));
        }
    };
    Ok(CValue::Pointer(Pointer {
        block: pointer.block,
        offset: scale_int32_offset(bits, i64::from(pointee_byte_width)),
    }))
}

pub(in crate::lang::click) fn evaluate_postcondition_add(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_add(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| format!("cannot add pointer and `{offset:?}`")),
        (offset, CValue::Pointer(pointer)) => promoted_int32_term(&offset)
            .map(|index| CValue::Pointer(offset_pointer_by_int32_elements(pointer, index)))
            .ok_or_else(|| format!("cannot add `{offset:?}` and pointer")),
        (left, right) => Err(format!("cannot add `{left:?}` and `{right:?}`")),
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_sub(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        return Ok(CValue::Int32(bitvector32_subtract(left_term, right_term)));
    }

    match (left, right) {
        (CValue::Pointer(pointer), offset) => {
            let Some(index) = promoted_int32_term(&offset) else {
                return Err(format!("cannot subtract `{offset:?}` from pointer"));
            };
            Ok(CValue::Pointer(offset_pointer_by_int32_elements(
                pointer,
                bitvector32_subtract(Bitvector32Term::Constant(0), index),
            )))
        }
        (left, right) => Err(format!("cannot subtract `{right:?}` from `{left:?}`")),
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_multiply(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(bitvector32_multiply(left_term, right_term)))
    } else {
        Err(format!("cannot multiply `{left:?}` and `{right:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_divide(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_divide(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot divide `{left:?}` by `{right:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_remainder(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_remainder(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot compute `{left:?}` % `{right:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_shift_left(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_left(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot apply `<<` to `{left:?}` and `{right:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_shift_right(
    left: CValue,
    right: CValue,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        bitvector32_shift_right(left_term, right_term).map(CValue::Int32)
    } else {
        Err(format!("cannot apply `>>` to `{left:?}` and `{right:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_bitwise_binary(
    left: CValue,
    right: CValue,
    operator: &str,
    apply: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Result<CValue, String> {
    if let (Some(left_term), Some(right_term)) =
        (promoted_int32_term(&left), promoted_int32_term(&right))
    {
        Ok(CValue::Int32(apply(left_term, right_term)))
    } else {
        Err(format!(
            "cannot apply `{operator}` to `{left:?}` and `{right:?}`"
        ))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_bitwise_not(
    value: CValue,
) -> Result<CValue, String> {
    if let Some(term) = promoted_int32_term(&value) {
        Ok(CValue::Int32(bitvector32_not(term)))
    } else {
        Err(format!("cannot apply `~` to `{value:?}`"))
    }
}

pub(in crate::lang::click) fn evaluate_postcondition_pointer_add(
    left: CValue,
    right: CValue,
) -> Result<Pointer, String> {
    match evaluate_postcondition_add(left, right)? {
        CValue::Pointer(pointer) => Ok(pointer),
        value => Err(format!(
            "index base did not evaluate to a pointer: `{value:?}`"
        )),
    }
}

pub(in crate::lang::click) fn offset_pointer_by_int32_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
) -> Pointer {
    offset_pointer_by_elements(pointer, elements, 4)
}

pub(in crate::lang::click) fn offset_pointer_by_elements(
    pointer: Pointer,
    elements: Bitvector32Term,
    element_width: u32,
) -> Pointer {
    Pointer {
        block: pointer.block,
        offset: add_pointer_offset(
            pointer.offset,
            scale_int32_offset(elements, i64::from(element_width)),
        ),
    }
}

pub(in crate::lang::click) fn add_pointer_offset(
    left: PointerOffsetTerm,
    right: PointerOffsetTerm,
) -> PointerOffsetTerm {
    match (&left, &right) {
        (PointerOffsetTerm::Constant(left), PointerOffsetTerm::Constant(right)) => {
            PointerOffsetTerm::Constant(left + right)
        }
        (PointerOffsetTerm::Constant(0), _) => right,
        (_, PointerOffsetTerm::Constant(0)) => left,
        _ => PointerOffsetTerm::Add(Box::new(left), Box::new(right)),
    }
}

pub(in crate::lang::click) fn scale_int32_offset(
    value: Bitvector32Term,
    byte_width: i64,
) -> PointerOffsetTerm {
    match value {
        Bitvector32Term::Constant(value) => {
            PointerOffsetTerm::Constant((value as i32 as i64) * byte_width)
        }
        value => PointerOffsetTerm::Int32Scaled {
            value: Box::new(value),
            byte_width,
        },
    }
}
