use super::*;

type ValidShiftCountEvaluator = fn(
    Bitvector32Term,
    Bitvector32Term,
    Vec<ExecutionPureFact>,
    Vec<ProofObligation>,
    &PureFactContext,
) -> Vec<CExpressionPath>;

type ValidInt64ShiftCountEvaluator = fn(
    Bitvector32Term,
    Bitvector32Term,
    Vec<ExecutionPureFact>,
    Vec<ProofObligation>,
    &PureFactContext,
) -> Vec<CExpressionPath>;

fn c_type_mismatch_expression_path(
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
) -> CExpressionPath {
    CExpressionPath {
        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
        facts,
        obligations,
    }
}

fn pointer_types_compatible(left: &CPointerValue, right: &CPointerValue) -> bool {
    left.c_type() == right.c_type() || left.is_null() || right.is_null()
}

fn scalar_uses_uint32(left: &CValue, right: &CValue) -> bool {
    matches!(left, CValue::UInt32(_)) || matches!(right, CValue::UInt32(_))
}

#[derive(Clone, Copy)]
enum ScalarWidth {
    Int32,
    UInt32,
    Int64,
    UInt64,
}

#[derive(Clone, Copy)]
pub(in crate::kernel) enum CBitwiseOperation {
    And,
    Or,
    Xor,
}

fn scalar_width(left: &CValue, right: &CValue) -> Option<ScalarWidth> {
    let is_scalar = |value: &CValue| {
        matches!(
            value,
            CValue::Int16(_)
                | CValue::Int32(_)
                | CValue::UInt8(_)
                | CValue::UInt16(_)
                | CValue::UInt32(_)
                | CValue::Int64(_)
                | CValue::UInt64(_)
        )
    };
    if !is_scalar(left) || !is_scalar(right) {
        return None;
    }
    if matches!(left, CValue::UInt64(_)) || matches!(right, CValue::UInt64(_)) {
        Some(ScalarWidth::UInt64)
    } else if matches!(left, CValue::Int64(_)) || matches!(right, CValue::Int64(_)) {
        Some(ScalarWidth::Int64)
    } else if scalar_uses_uint32(left, right) {
        Some(ScalarWidth::UInt32)
    } else {
        Some(ScalarWidth::Int32)
    }
}

pub(in crate::kernel) fn evaluate_c_add_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    let left_step_width = c_expression_pointer_step_width(state, left);
    let right_step_width = c_expression_pointer_step_width(state, right);
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExpressionOutcome::Value(value) => value,
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            let right = match right_path.outcome {
                CExpressionOutcome::Value(value) => value,
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    });
                    continue;
                }
                CExpressionOutcome::RuntimeError(error) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    });
                    continue;
                }
            };

            paths.extend(apply_c_add(
                state,
                left.clone(),
                right,
                left_step_width,
                right_step_width,
                facts,
                obligations,
                assumptions,
            ));
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn apply_c_add(
    state: &CState,
    left: CValue,
    right: CValue,
    left_step_width: Option<u32>,
    right_step_width: Option<u32>,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return apply_c_wide_add(left, right, width, facts, obligations, assumptions);
    }
    match (left, right) {
        (
            left @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)),
            right @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)),
        ) if scalar_uses_uint32(&left, &right) => {
            let mut facts = facts;
            let Some(left) = promote_c_uint32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_uint32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(uint32(Bitvector32Term::add(left, right))),
                facts,
                obligations,
            }]
        }
        (
            left @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
            right @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
        ) => {
            let mut facts = facts;
            let Some(left) = promote_c_int32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            apply_c_int32_add(left, right, facts, obligations, assumptions)
        }
        (
            CValue::Pointer(pointer),
            offset @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
        ) => {
            let mut facts = facts;
            let Some(offset) = promote_c_int32_path_value(offset, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(byte_width) = left_step_width else {
                return vec![CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(
                        CRuntimeError::IndeterminatePointeeType,
                    ),
                    facts,
                    obligations,
                }];
            };
            let offset = canonicalized_offset_index_term(offset, &mut facts);
            pointer_offset_by_elements_paths(
                state,
                pointer,
                offset,
                byte_width,
                facts,
                obligations,
                assumptions,
            )
        }
        (
            offset @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
            CValue::Pointer(pointer),
        ) => {
            let mut facts = facts;
            let Some(offset) = promote_c_int32_path_value(offset, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(byte_width) = right_step_width else {
                return vec![CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(
                        CRuntimeError::IndeterminatePointeeType,
                    ),
                    facts,
                    obligations,
                }];
            };
            let offset = canonicalized_offset_index_term(offset, &mut facts);
            pointer_offset_by_elements_paths(
                state,
                pointer,
                offset,
                byte_width,
                facts,
                obligations,
                assumptions,
            )
        }
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

pub(in crate::kernel) fn evaluate_c_comparison_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    operator: CComparisonOperator,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let left_step_width = c_expression_pointer_step_width(state, left);
    let right_step_width = c_expression_pointer_step_width(state, right);
    evaluate_c_value_binary_paths(
        state,
        left,
        right,
        assumptions,
        budget,
        |left, right, facts, obligations| {
            apply_c_comparison(
                operator,
                left,
                right,
                left_step_width,
                right_step_width,
                facts,
                obligations,
                assumptions,
            )
        },
    )
}

pub(in crate::kernel) fn evaluate_c_subtract_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let left_step_width = c_expression_pointer_step_width(state, left);
    let right_step_width = c_expression_pointer_step_width(state, right);
    evaluate_c_value_binary_paths(
        state,
        left,
        right,
        assumptions,
        budget,
        |left, right, facts, obligations| {
            apply_c_subtract(
                state,
                left,
                right,
                left_step_width,
                right_step_width,
                facts,
                obligations,
                assumptions,
            )
        },
    )
}

pub(in crate::kernel) fn evaluate_c_value_binary_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    apply: impl Fn(CValue, CValue, Vec<ExecutionPureFact>, Vec<ProofObligation>) -> Vec<CExpressionPath>,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;
        let left = match left_outcome {
            CExpressionOutcome::Value(value) => value,
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match right_path.outcome {
                CExpressionOutcome::Value(value) => {
                    paths.extend(apply(left.clone(), value, facts, obligations));
                }
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    });
                }
                CExpressionOutcome::RuntimeError(error) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    });
                }
            }
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn apply_c_scalar_terms(
    left: CValue,
    right: CValue,
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
) -> Option<(Bitvector32Term, Bitvector32Term, ScalarWidth)> {
    let width = scalar_width(&left, &right)?;
    let left_term = match width {
        ScalarWidth::Int32 => promote_c_int32_path_value(left, facts, assumptions)?,
        ScalarWidth::UInt32 => promote_c_uint32_path_value(left, facts, assumptions)?,
        ScalarWidth::Int64 => promote_c_int64_path_value(left)?,
        ScalarWidth::UInt64 => promote_c_uint64_path_value(left)?,
    };
    let right_term = match width {
        ScalarWidth::Int32 => promote_c_int32_path_value(right, facts, assumptions)?,
        ScalarWidth::UInt32 => promote_c_uint32_path_value(right, facts, assumptions)?,
        ScalarWidth::Int64 => promote_c_int64_path_value(right)?,
        ScalarWidth::UInt64 => promote_c_uint64_path_value(right)?,
    };
    Some((left_term, right_term, width))
}

fn apply_c_wide_add(
    left: CValue,
    right: CValue,
    width: ScalarWidth,
    mut facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let Some((left, right, _)) = apply_c_scalar_terms(left, right, &mut facts, assumptions) else {
        return Vec::new();
    };
    match width {
        ScalarWidth::Int64 => apply_c_int64_add(left, right, facts, obligations, assumptions),
        ScalarWidth::UInt64 => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(CValue::UInt64(Bitvector32Term::uint64_add(
                left, right,
            ))),
            facts,
            obligations,
        }],
        ScalarWidth::Int32 | ScalarWidth::UInt32 => unreachable!(),
    }
}

fn apply_c_wide_subtract(
    left: CValue,
    right: CValue,
    width: ScalarWidth,
    mut facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let Some((left, right, _)) = apply_c_scalar_terms(left, right, &mut facts, assumptions) else {
        return Vec::new();
    };
    match width {
        ScalarWidth::Int64 => apply_c_int64_subtract(left, right, facts, obligations, assumptions),
        ScalarWidth::UInt64 => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(CValue::UInt64(Bitvector32Term::uint64_subtract(
                left, right,
            ))),
            facts,
            obligations,
        }],
        ScalarWidth::Int32 | ScalarWidth::UInt32 => unreachable!(),
    }
}

fn apply_c_wide_multiply(
    left: CValue,
    right: CValue,
    width: ScalarWidth,
    mut facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let Some((left, right, _)) = apply_c_scalar_terms(left, right, &mut facts, assumptions) else {
        return Vec::new();
    };
    match width {
        ScalarWidth::Int64 => apply_c_int64_multiply(left, right, facts, obligations, assumptions),
        ScalarWidth::UInt64 => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(CValue::UInt64(Bitvector32Term::uint64_multiply(
                left, right,
            ))),
            facts,
            obligations,
        }],
        ScalarWidth::Int32 | ScalarWidth::UInt32 => unreachable!(),
    }
}

fn apply_c_wide_divide(
    left: CValue,
    right: CValue,
    width: ScalarWidth,
    mut facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let Some((left, right, _)) = apply_c_scalar_terms(left, right, &mut facts, assumptions) else {
        return Vec::new();
    };
    match width {
        ScalarWidth::Int64 => apply_c_int64_divide(left, right, facts, obligations, assumptions),
        ScalarWidth::UInt64 => apply_c_uint64_division_like(
            left,
            right,
            facts,
            obligations,
            assumptions,
            Bitvector32Term::uint64_divide,
        ),
        ScalarWidth::Int32 | ScalarWidth::UInt32 => unreachable!(),
    }
}

fn apply_c_wide_remainder(
    left: CValue,
    right: CValue,
    width: ScalarWidth,
    mut facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let Some((left, right, _)) = apply_c_scalar_terms(left, right, &mut facts, assumptions) else {
        return Vec::new();
    };
    match width {
        ScalarWidth::Int64 => apply_c_int64_remainder(left, right, facts, obligations, assumptions),
        ScalarWidth::UInt64 => apply_c_uint64_division_like(
            left,
            right,
            facts,
            obligations,
            assumptions,
            Bitvector32Term::uint64_remainder,
        ),
        ScalarWidth::Int32 | ScalarWidth::UInt32 => unreachable!(),
    }
}

fn apply_c_wide_comparison(
    operator: CComparisonOperator,
    left: CValue,
    right: CValue,
    width: ScalarWidth,
    mut facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let Some((left, right, _)) = apply_c_scalar_terms(left, right, &mut facts, assumptions) else {
        return Vec::new();
    };
    let condition = match (width, operator) {
        (ScalarWidth::Int64, CComparisonOperator::LessThan) => {
            ConditionTerm::int64_signed_less_than(left, right)
        }
        (ScalarWidth::Int64, CComparisonOperator::LessEqual) => {
            ConditionTerm::int64_signed_less_equal(left, right)
        }
        (ScalarWidth::Int64, CComparisonOperator::GreaterThan) => {
            ConditionTerm::int64_signed_greater_than(left, right)
        }
        (ScalarWidth::Int64, CComparisonOperator::GreaterEqual) => {
            ConditionTerm::int64_signed_greater_equal(left, right)
        }
        (ScalarWidth::UInt64, CComparisonOperator::LessThan) => {
            ConditionTerm::uint64_less_than(left, right)
        }
        (ScalarWidth::UInt64, CComparisonOperator::LessEqual) => {
            ConditionTerm::uint64_less_equal(left, right)
        }
        (ScalarWidth::UInt64, CComparisonOperator::GreaterThan) => {
            ConditionTerm::uint64_greater_than(left, right)
        }
        (ScalarWidth::UInt64, CComparisonOperator::GreaterEqual) => {
            ConditionTerm::uint64_greater_equal(left, right)
        }
        (ScalarWidth::Int64 | ScalarWidth::UInt64, CComparisonOperator::Equal) => {
            if matches!(width, ScalarWidth::Int64) {
                ConditionTerm::int64_equal(left, right)
            } else {
                ConditionTerm::uint64_equal(left, right)
            }
        }
        (ScalarWidth::Int64 | ScalarWidth::UInt64, CComparisonOperator::NotEqual) => {
            let equal = if matches!(width, ScalarWidth::Int64) {
                ConditionTerm::int64_equal(left, right)
            } else {
                ConditionTerm::uint64_equal(left, right)
            };
            return condition_as_c_int32_not_paths(equal, facts, obligations, assumptions);
        }
        (ScalarWidth::Int32 | ScalarWidth::UInt32, _) => unreachable!(),
    };
    condition_as_c_int32_paths(condition, facts, obligations, assumptions)
}

pub(in crate::kernel) fn apply_c_scalar_subtract(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let Some(width) = scalar_width(&left, &right) else {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    };
    if matches!(width, ScalarWidth::Int64 | ScalarWidth::UInt64) {
        return apply_c_wide_subtract(left, right, width, facts, obligations, assumptions);
    }
    let mut facts = facts;
    let Some((left, right, width)) = apply_c_scalar_terms(left, right, &mut facts, assumptions)
    else {
        return Vec::new();
    };
    if matches!(width, ScalarWidth::UInt32) {
        vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(uint32(Bitvector32Term::subtract(left, right))),
            facts,
            obligations,
        }]
    } else {
        apply_c_int32_subtract(left, right, facts, obligations, assumptions)
    }
}

pub(in crate::kernel) fn apply_c_multiply(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return apply_c_wide_multiply(left, right, width, facts, obligations, assumptions);
    }
    let scalar_left = matches!(
        left,
        CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)
    );
    let scalar_right = matches!(
        right,
        CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)
    );
    if !scalar_left || !scalar_right {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    }
    let mut facts = facts;
    let Some((left, right, width)) = apply_c_scalar_terms(left, right, &mut facts, assumptions)
    else {
        return Vec::new();
    };
    if matches!(width, ScalarWidth::UInt32) {
        vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(uint32(Bitvector32Term::multiply(left, right))),
            facts,
            obligations,
        }]
    } else {
        apply_c_int32_multiply(left, right, facts, obligations, assumptions)
    }
}

pub(in crate::kernel) fn apply_c_divide(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return apply_c_wide_divide(left, right, width, facts, obligations, assumptions);
    }
    let scalar_left = matches!(
        left,
        CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)
    );
    let scalar_right = matches!(
        right,
        CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)
    );
    if !scalar_left || !scalar_right {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    }
    let mut facts = facts;
    let Some((left, right, width)) = apply_c_scalar_terms(left, right, &mut facts, assumptions)
    else {
        return Vec::new();
    };
    if matches!(width, ScalarWidth::UInt32) {
        apply_c_uint32_division_like(
            left,
            right,
            facts,
            obligations,
            assumptions,
            Bitvector32Term::unsigned_divide,
        )
    } else {
        apply_c_int32_divide(left, right, facts, obligations, assumptions)
    }
}

pub(in crate::kernel) fn apply_c_remainder(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return apply_c_wide_remainder(left, right, width, facts, obligations, assumptions);
    }
    let scalar_left = matches!(
        left,
        CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)
    );
    let scalar_right = matches!(
        right,
        CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)
    );
    if !scalar_left || !scalar_right {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    }
    let mut facts = facts;
    let Some((left, right, width)) = apply_c_scalar_terms(left, right, &mut facts, assumptions)
    else {
        return Vec::new();
    };
    if matches!(width, ScalarWidth::UInt32) {
        apply_c_uint32_division_like(
            left,
            right,
            facts,
            obligations,
            assumptions,
            Bitvector32Term::unsigned_remainder,
        )
    } else {
        apply_c_int32_remainder(left, right, facts, obligations, assumptions)
    }
}

pub(in crate::kernel) fn apply_c_bitwise_binary(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    operation: CBitwiseOperation,
) -> Vec<CExpressionPath> {
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        let mut facts = facts;
        let Some((left, right, _)) = apply_c_scalar_terms(left, right, &mut facts, assumptions)
        else {
            return Vec::new();
        };
        let value = match (width, operation) {
            (ScalarWidth::Int64, CBitwiseOperation::And) => {
                Bitvector32Term::int64_bitwise_and(left, right)
            }
            (ScalarWidth::Int64, CBitwiseOperation::Or) => {
                Bitvector32Term::int64_bitwise_or(left, right)
            }
            (ScalarWidth::Int64, CBitwiseOperation::Xor) => {
                Bitvector32Term::int64_bitwise_xor(left, right)
            }
            (ScalarWidth::UInt64, CBitwiseOperation::And) => {
                Bitvector32Term::uint64_bitwise_and(left, right)
            }
            (ScalarWidth::UInt64, CBitwiseOperation::Or) => {
                Bitvector32Term::uint64_bitwise_or(left, right)
            }
            (ScalarWidth::UInt64, CBitwiseOperation::Xor) => {
                Bitvector32Term::uint64_bitwise_xor(left, right)
            }
            (ScalarWidth::Int32 | ScalarWidth::UInt32, _) => unreachable!(),
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(match width {
                ScalarWidth::Int64 => CValue::Int64(value),
                ScalarWidth::UInt64 => CValue::UInt64(value),
                ScalarWidth::Int32 | ScalarWidth::UInt32 => unreachable!(),
            }),
            facts,
            obligations,
        }];
    }
    let scalar_left = matches!(
        left,
        CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)
    );
    let scalar_right = matches!(
        right,
        CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)
    );
    if !scalar_left || !scalar_right {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    }
    let mut facts = facts;
    let Some((left, right, width)) = apply_c_scalar_terms(left, right, &mut facts, assumptions)
    else {
        return Vec::new();
    };
    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(if matches!(width, ScalarWidth::UInt32) {
            uint32(match operation {
                CBitwiseOperation::And => Bitvector32Term::bitwise_and(left, right),
                CBitwiseOperation::Or => Bitvector32Term::bitwise_or(left, right),
                CBitwiseOperation::Xor => Bitvector32Term::bitwise_xor(left, right),
            })
        } else {
            int32(match operation {
                CBitwiseOperation::And => Bitvector32Term::bitwise_and(left, right),
                CBitwiseOperation::Or => Bitvector32Term::bitwise_or(left, right),
                CBitwiseOperation::Xor => Bitvector32Term::bitwise_xor(left, right),
            })
        }),
        facts,
        obligations,
    }]
}

pub(in crate::kernel) fn apply_c_bitwise_not(
    value: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    match value {
        CValue::UInt32(value) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(uint32(Bitvector32Term::bitwise_not(value))),
            facts,
            obligations,
        }],
        CValue::Int32(value) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::bitwise_not(value))),
            facts,
            obligations,
        }],
        CValue::Int16(value) => {
            let mut facts = facts;
            if add_int16_range_execution_pure_facts(&mut facts, assumptions, &value).is_none() {
                return Vec::new();
            }
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::bitwise_not(value))),
                facts,
                obligations,
            }]
        }
        CValue::UInt8(value) => {
            let mut facts = facts;
            if add_uint8_range_execution_pure_facts(&mut facts, assumptions, &value).is_none() {
                return Vec::new();
            }
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::bitwise_not(value))),
                facts,
                obligations,
            }]
        }
        CValue::UInt16(value) => {
            let mut facts = facts;
            if add_uint16_range_execution_pure_facts(&mut facts, assumptions, &value).is_none() {
                return Vec::new();
            }
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::bitwise_not(value))),
                facts,
                obligations,
            }]
        }
        CValue::Int64(value) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(CValue::Int64(Bitvector32Term::int64_bitwise_not(
                value,
            ))),
            facts,
            obligations,
        }],
        CValue::UInt64(value) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(CValue::UInt64(
                Bitvector32Term::uint64_bitwise_not(value),
            )),
            facts,
            obligations,
        }],
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

fn pointer_operation_step_width(
    left_step_width: Option<u32>,
    right_step_width: Option<u32>,
) -> Option<u32> {
    match (left_step_width, right_step_width) {
        (Some(left), Some(right)) if left != right => None,
        (Some(width), _) | (_, Some(width)) => Some(width),
        (None, None) => Some(4),
    }
}

fn pointer_element_index(pointer: &Pointer, byte_width: u32) -> Option<Bitvector32Term> {
    pointer_index_from_offset_term(&pointer.offset, byte_width)
}

fn pointer_element_indices(
    left: &Pointer,
    right: &Pointer,
    byte_width: u32,
) -> Option<(Bitvector32Term, Bitvector32Term)> {
    let zero = Bitvector32Term::Constant(0);
    let relative = match (&left.offset, &right.offset) {
        (left, right) if left == right => Some((zero.clone(), zero.clone())),
        (
            PointerOffsetTerm::Add(left_base, left_addend),
            PointerOffsetTerm::Add(right_base, right_addend),
        ) if left_base == right_base => Some((
            pointer_index_from_offset_term(left_addend, byte_width)?,
            pointer_index_from_offset_term(right_addend, byte_width)?,
        )),
        (PointerOffsetTerm::Add(base, addend), right) if base.as_ref() == right => Some((
            pointer_index_from_offset_term(addend, byte_width)?,
            zero.clone(),
        )),
        (left, PointerOffsetTerm::Add(base, addend)) if base.as_ref() == left => Some((
            zero.clone(),
            pointer_index_from_offset_term(addend, byte_width)?,
        )),
        _ => None,
    };
    relative.or_else(|| {
        Some((
            pointer_element_index(left, byte_width)?,
            pointer_element_index(right, byte_width)?,
        ))
    })
}

pub(in crate::kernel) fn pointer_order_condition(
    left: Bitvector32Term,
    right: Bitvector32Term,
    operator: CComparisonOperator,
) -> ConditionTerm {
    match operator {
        CComparisonOperator::LessThan => ConditionTerm::signed_less_than(left, right),
        CComparisonOperator::LessEqual => ConditionTerm::signed_less_equal(left, right),
        CComparisonOperator::GreaterThan => ConditionTerm::signed_greater_than(left, right),
        CComparisonOperator::GreaterEqual => ConditionTerm::signed_greater_equal(left, right),
        CComparisonOperator::Equal | CComparisonOperator::NotEqual => {
            unreachable!("pointer order condition received equality operator")
        }
    }
}

fn uint32_order_condition(
    left: Bitvector32Term,
    right: Bitvector32Term,
    operator: CComparisonOperator,
) -> ConditionTerm {
    match operator {
        CComparisonOperator::LessThan => ConditionTerm::unsigned_less_than(left, right),
        CComparisonOperator::LessEqual => ConditionTerm::unsigned_less_equal(left, right),
        CComparisonOperator::GreaterThan => ConditionTerm::unsigned_greater_than(left, right),
        CComparisonOperator::GreaterEqual => ConditionTerm::unsigned_greater_equal(left, right),
        CComparisonOperator::Equal | CComparisonOperator::NotEqual => {
            unreachable!("uint32 order condition received equality operator")
        }
    }
}

fn apply_same_block_pointer_operation(
    left: Pointer,
    right: Pointer,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    apply: impl FnOnce(
        Pointer,
        Pointer,
        Vec<ExecutionPureFact>,
        Vec<ProofObligation>,
    ) -> Vec<CExpressionPath>,
) -> Vec<CExpressionPath> {
    let left_base = Pointer {
        block: left.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let right_base = Pointer {
        block: right.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let same_block = ConditionTerm::pointer_equal(left_base, right_base);
    match decide_with_facts(assumptions, &facts, &same_block) {
        Some(true) => apply(left, right, facts, obligations),
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic),
            facts,
            obligations,
        }],
        None => {
            let mut same_block_facts = facts.clone();
            add_condition_path_fact(&mut same_block_facts, assumptions, same_block.clone(), true)
                .expect("same-block pointer guard should be consistent");
            let mut paths = apply(left, right, same_block_facts, obligations.clone());

            let mut different_block_facts = facts;
            add_condition_path_fact(&mut different_block_facts, assumptions, same_block, false)
                .expect("different-block pointer guard should be consistent");
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(
                    CUndefinedBehavior::PointerArithmetic,
                ),
                facts: different_block_facts,
                obligations,
            });
            paths
        }
    }
}

fn apply_c_comparison(
    operator: CComparisonOperator,
    left: CValue,
    right: CValue,
    left_step_width: Option<u32>,
    right_step_width: Option<u32>,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return apply_c_wide_comparison(
            operator,
            left,
            right,
            width,
            facts,
            obligations,
            assumptions,
        );
    }
    match (left, right) {
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            if !pointer_types_compatible(&left, &right) {
                return vec![c_type_mismatch_expression_path(facts, obligations)];
            }
            let Some(byte_width) = pointer_operation_step_width(left_step_width, right_step_width)
            else {
                return vec![c_type_mismatch_expression_path(facts, obligations)];
            };
            apply_same_block_pointer_operation(
                left.into_pointer(),
                right.into_pointer(),
                facts,
                obligations,
                assumptions,
                move |left, right, facts, obligations| {
                    let Some((left, right)) = pointer_element_indices(&left, &right, byte_width)
                    else {
                        return vec![CExpressionPath {
                            outcome: CExpressionOutcome::RuntimeError(
                                CRuntimeError::IndeterminatePointeeType,
                            ),
                            facts,
                            obligations,
                        }];
                    };
                    condition_as_c_int32_paths(
                        pointer_order_condition(left, right, operator),
                        facts,
                        obligations,
                        assumptions,
                    )
                },
            )
        }
        (
            left @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)),
            right @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)),
        ) if scalar_uses_uint32(&left, &right) => {
            let mut facts = facts;
            let Some(left) = promote_c_uint32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_uint32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            condition_as_c_int32_paths(
                uint32_order_condition(left, right, operator),
                facts,
                obligations,
                assumptions,
            )
        }
        (
            left @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
            right @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
        ) => {
            let mut facts = facts;
            let Some(left) = promote_c_int32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            condition_as_c_int32_paths(
                pointer_order_condition(left, right, operator),
                facts,
                obligations,
                assumptions,
            )
        }
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

pub(in crate::kernel) fn apply_c_subtract(
    state: &CState,
    left: CValue,
    right: CValue,
    left_step_width: Option<u32>,
    right_step_width: Option<u32>,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return apply_c_wide_subtract(left, right, width, facts, obligations, assumptions);
    }
    match (left, right) {
        (
            left @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
            right @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
        ) => {
            let mut facts = facts;
            let Some(left) = promote_c_int32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            apply_c_int32_subtract(left, right, facts, obligations, assumptions)
        }
        (
            left @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)),
            right @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)),
        ) if scalar_uses_uint32(&left, &right) => {
            let mut facts = facts;
            let Some(left) = promote_c_uint32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_uint32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(uint32(Bitvector32Term::subtract(left, right))),
                facts,
                obligations,
            }]
        }
        (
            CValue::Pointer(pointer),
            right @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
        ) => {
            let mut facts = facts;
            let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(byte_width) = pointer_operation_step_width(left_step_width, None) else {
                return vec![c_type_mismatch_expression_path(facts, obligations)];
            };
            pointer_offset_by_elements_paths(
                state,
                pointer,
                Bitvector32Term::subtract(Bitvector32Term::Constant(0), right),
                byte_width,
                facts,
                obligations,
                assumptions,
            )
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            if left.c_type() != right.c_type() {
                return vec![c_type_mismatch_expression_path(facts, obligations)];
            }
            let Some(byte_width) = pointer_operation_step_width(left_step_width, right_step_width)
            else {
                return vec![c_type_mismatch_expression_path(facts, obligations)];
            };
            apply_same_block_pointer_operation(
                left.into_pointer(),
                right.into_pointer(),
                facts,
                obligations,
                assumptions,
                move |left, right, facts, obligations| {
                    let Some((left, right)) = pointer_element_indices(&left, &right, byte_width)
                    else {
                        return vec![CExpressionPath {
                            outcome: CExpressionOutcome::RuntimeError(
                                CRuntimeError::IndeterminatePointeeType,
                            ),
                            facts,
                            obligations,
                        }];
                    };
                    apply_c_int32_subtract(left, right, facts, obligations, assumptions)
                },
            )
        }
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

#[derive(Clone)]
struct PointerFormationGuard {
    condition: ConditionTerm,
    value: bool,
}

fn pointer_offset_by_elements_paths(
    state: &CState,
    pointer: CPointerValue,
    offset: Bitvector32Term,
    byte_width: u32,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let pointer_type = pointer.c_type();
    let pointer = pointer.into_pointer();
    let result = pointer.offset_by_elements(offset.clone(), byte_width);
    let mut guards = Vec::new();

    // Pointer offsets are exact i64 terms, but the source index is a signed
    // int32. Once a pointer has a known element index, the next addition must
    // stay in that signed domain. This catches the cumulative case
    // `data + INT_MAX + 1`, even though each individual source operand is a
    // valid int32.
    if let Some(index) = pointer_index_from_offset(&pointer, byte_width)
        && index != Bitvector32Term::Constant(0)
        && offset != Bitvector32Term::Constant(0)
    {
        guards.push(PointerFormationGuard {
            condition: ConditionTerm::signed_add_overflows(index, offset),
            value: false,
        });
    }

    // A resource-backed read may legitimately refer to storage that has not
    // been materialized in the byte map yet. Let that explicit memory range
    // extend the concrete materialization bound; it is still only consulted
    // when the result (including a range endpoint) is provably in the range.
    let resource_backed =
        pointer_is_in_memory_resource(state.resources(), assumptions, &facts, &result, byte_width);
    if !resource_backed {
        guards.extend(pointer_block_bounds(state, &result, byte_width));
    }

    apply_pointer_formation_guards(
        result,
        pointer_type,
        guards,
        facts,
        obligations,
        assumptions,
    )
}

pub(in crate::kernel) fn pointer_offset_by_bytes_paths(
    state: &CState,
    pointer: CPointerValue,
    bytes: u32,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let pointer_type = pointer.c_type();
    let pointer = pointer.into_pointer();
    if pointer.block.is_function() && bytes != 0 {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::IndeterminatePointeeType),
            facts,
            obligations,
        }];
    }
    let result = pointer.offset_by_bytes(bytes);
    let guards = pointer_block_bounds(state, &result, 1);
    apply_pointer_formation_guards(
        result,
        pointer_type,
        guards,
        facts,
        obligations,
        assumptions,
    )
}

fn pointer_index_from_offset(pointer: &Pointer, byte_width: u32) -> Option<Bitvector32Term> {
    if pointer.block != PointerBlock::ExternalArgument {
        return pointer_index_from_offset_term(&pointer.offset, byte_width);
    }

    // External argument pointers carry a symbolic shared-memory offset, not
    // an element index from the beginning of an object. Only the additions
    // structurally introduced after that opaque base participate in the
    // cumulative-index check. Concrete zero-based test pointers retain the
    // direct fallback so their first large addition is checked on the next
    // operation as well.
    pointer
        .offset
        .as_const()
        .and_then(|offset| pointer_index_from_concrete_offset(offset, byte_width))
        .or_else(|| pointer_arithmetic_index(&pointer.offset, byte_width))
}

fn pointer_index_from_offset_term(
    offset: &PointerOffsetTerm,
    byte_width: u32,
) -> Option<Bitvector32Term> {
    if byte_width == 1 {
        byte_offset_from_pointer_offset(offset)
    } else {
        element_index_from_offset(offset, byte_width)
    }
}

fn pointer_index_from_concrete_offset(offset: i64, byte_width: u32) -> Option<Bitvector32Term> {
    if byte_width == 0 || offset % i64::from(byte_width) != 0 {
        return None;
    }
    let index = offset / i64::from(byte_width);
    (i32::MIN as i64..=i32::MAX as i64)
        .contains(&index)
        .then_some(Bitvector32Term::Constant((index as i32) as u32))
}

fn pointer_arithmetic_index(
    offset: &PointerOffsetTerm,
    byte_width: u32,
) -> Option<Bitvector32Term> {
    let PointerOffsetTerm::Add(left, right) = offset else {
        return None;
    };
    let right = pointer_index_from_offset_term(right, byte_width)?;
    let left = match left.as_ref() {
        PointerOffsetTerm::Add(..) => pointer_arithmetic_index(left, byte_width)?,
        // The first addend is the pointer's opaque base. It is not an
        // element displacement, even if its byte representation happens to
        // be aligned.
        _ => Bitvector32Term::Constant(0),
    };
    Some(Bitvector32Term::add(left, right))
}

fn pointer_block_bounds(
    state: &CState,
    pointer: &Pointer,
    byte_width: u32,
) -> Vec<PointerFormationGuard> {
    let Some(block_size) = state.memory().block_size(&pointer.block).cloned() else {
        return Vec::new();
    };

    // Concrete offsets can exceed the signed bitvector representation. Check
    // those directly against the byte-sized block instead of silently
    // rebuilding them through a wrapping int32 term.
    if let (Some(offset), Some(size)) = (pointer.offset.as_const(), block_size.as_const()) {
        if offset < 0 || offset > i64::from(size) {
            return vec![PointerFormationGuard {
                condition: ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(1),
                    Bitvector32Term::Constant(0),
                ),
                value: true,
            }];
        }
        return Vec::new();
    }

    let (offset, size) = if byte_width == 1 {
        let Some(offset) = byte_offset_from_pointer_offset(&pointer.offset) else {
            return Vec::new();
        };
        (offset, block_size)
    } else {
        let Some(offset) = element_index_from_offset(&pointer.offset, byte_width) else {
            return Vec::new();
        };
        let Some(size) = element_count_from_bytes(&block_size, byte_width) else {
            return Vec::new();
        };
        (offset, size)
    };

    vec![
        PointerFormationGuard {
            condition: ConditionTerm::signed_greater_equal(
                offset.clone(),
                Bitvector32Term::Constant(0),
            ),
            value: true,
        },
        PointerFormationGuard {
            condition: ConditionTerm::signed_less_equal(offset, size),
            value: true,
        },
    ]
}

fn pointer_is_in_memory_resource(
    resources: &ResourceContext,
    assumptions: &PureFactContext,
    facts: &[ExecutionPureFact],
    pointer: &Pointer,
    byte_width: u32,
) -> bool {
    let decide =
        |condition: ConditionTerm| decide_with_facts(assumptions, facts, &condition) == Some(true);
    // This is intentionally a small, structural query. It recognizes the
    // range shape produced by pointer arithmetic without asking the resource
    // algebra to search unrelated resources.
    let contains_range = |resources: &ResourceContext| {
        resources.facts().iter().any(|fact| {
            let Some(range) = fact.memory_range() else {
                return false;
            };
            if range.element_width() != byte_width {
                return false;
            }
            let Some(index) = pointer_index_from_base(pointer, range.base(), byte_width) else {
                return false;
            };
            decide(ConditionTerm::signed_less_equal(
                range.start().clone(),
                index.clone(),
            )) && decide(ConditionTerm::signed_less_equal(index, range.end().clone()))
        })
    };
    contains_range(resources) || assumptions.resource_compositions.iter().any(contains_range)
}

fn pointer_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    byte_width: u32,
) -> Option<Bitvector32Term> {
    match byte_width {
        4 => pointer.element_index_from_base(base),
        1 => pointer_byte_offset_from_base(pointer, base),
        _ => None,
    }
}

fn apply_pointer_formation_guards(
    pointer: Pointer,
    pointer_type: CType,
    guards: Vec<PointerFormationGuard>,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let mut normal = vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(CValue::typed_pointer(pointer, pointer_type)),
        facts,
        obligations,
    }];
    let mut paths = Vec::new();

    for guard in guards {
        let mut next = Vec::new();
        for path in normal {
            match decide_with_facts(assumptions, &path.facts, &guard.condition) {
                Some(known) if known == guard.value => next.push(path),
                Some(_) => paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::PointerArithmetic,
                    ),
                    facts: path.facts,
                    obligations: path.obligations,
                }),
                None => {
                    let mut valid_facts = path.facts.clone();
                    add_condition_path_fact(
                        &mut valid_facts,
                        assumptions,
                        guard.condition.clone(),
                        guard.value,
                    )
                    .expect("pointer formation guard should be consistent");
                    next.push(CExpressionPath {
                        outcome: path.outcome.clone(),
                        facts: valid_facts,
                        obligations: path.obligations.clone(),
                    });

                    let invalid_value = !guard.value;
                    let mut invalid_facts = path.facts;
                    add_condition_path_fact(
                        &mut invalid_facts,
                        assumptions,
                        guard.condition.clone(),
                        invalid_value,
                    )
                    .expect("pointer formation guard should be consistent");
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(
                            CUndefinedBehavior::PointerArithmetic,
                        ),
                        facts: invalid_facts,
                        obligations: path.obligations,
                    });
                }
            }
        }
        normal = next;
    }

    paths.extend(normal);
    paths
}

pub(in crate::kernel) fn apply_c_int32_add(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_add_overflows(left.clone(), right.clone());
    match crate::instrumentation::measure_operation(
        "kernel",
        "independent kernel execution",
        "int32 add overflow decision",
        || decide_with_facts(assumptions, &facts, &overflow),
    ) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::add(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(Bitvector32Term::add(left, right))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn apply_c_int32_subtract(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_subtract_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::subtract(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(Bitvector32Term::subtract(
                        left, right,
                    ))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn apply_c_int32_multiply(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_multiply_overflows(
        normalize_exact_memory_loads_in_bitvector(&left, assumptions),
        normalize_exact_memory_loads_in_bitvector(&right, assumptions),
    );
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::multiply(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(Bitvector32Term::multiply(
                        left, right,
                    ))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn apply_c_int32_divide(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    apply_c_int32_division_like(
        left,
        right,
        facts,
        obligations,
        assumptions,
        Bitvector32Term::divide,
    )
}

pub(in crate::kernel) fn apply_c_int32_remainder(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    apply_c_int32_division_like(
        left,
        right,
        facts,
        obligations,
        assumptions,
        Bitvector32Term::remainder,
    )
}

fn apply_c_int32_division_like(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let zero = Bitvector32Term::Constant(0);
    let divides_by_zero = ConditionTerm::equal(right.clone(), zero);
    match decide_with_facts(assumptions, &facts, &divides_by_zero) {
        Some(true) => {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero),
                facts,
                obligations,
            }];
        }
        Some(false) => {
            return apply_c_int32_division_nonzero(
                left,
                right,
                facts,
                obligations,
                assumptions,
                result,
            );
        }
        None => {}
    }

    let mut normal_facts = facts.clone();
    add_condition_path_fact(
        &mut normal_facts,
        assumptions,
        divides_by_zero.clone(),
        false,
    )
    .expect("unknown zero-divisor fact should be consistent");

    let mut zero_facts = facts;
    add_condition_path_fact(&mut zero_facts, assumptions, divides_by_zero, true)
        .expect("unknown zero-divisor fact should be consistent");

    let mut paths = apply_c_int32_division_nonzero(
        left,
        right,
        normal_facts,
        obligations.clone(),
        assumptions,
        result,
    );
    paths.push(CExpressionPath {
        outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero),
        facts: zero_facts,
        obligations,
    });
    paths
}

fn apply_c_int32_division_nonzero(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_divide_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(result(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown divide-overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown divide-overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(result(left, right))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

fn apply_c_int64_overflowing(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    overflow: ConditionTerm,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(CValue::Int64(result(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown int64 overflow fact should be consistent");
            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown int64 overflow fact should be consistent");
            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(CValue::Int64(result(
                        left.clone(),
                        right.clone(),
                    ))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

fn apply_c_int64_add(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::int64_signed_add_overflows(left.clone(), right.clone());
    apply_c_int64_overflowing(
        left,
        right,
        facts,
        obligations,
        assumptions,
        overflow,
        Bitvector32Term::int64_add,
    )
}

fn apply_c_int64_subtract(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::int64_signed_subtract_overflows(left.clone(), right.clone());
    apply_c_int64_overflowing(
        left,
        right,
        facts,
        obligations,
        assumptions,
        overflow,
        Bitvector32Term::int64_subtract,
    )
}

fn apply_c_int64_multiply(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::int64_signed_multiply_overflows(left.clone(), right.clone());
    apply_c_int64_overflowing(
        left,
        right,
        facts,
        obligations,
        assumptions,
        overflow,
        Bitvector32Term::int64_multiply,
    )
}

fn apply_c_int64_divide(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    apply_c_int64_division_like(
        left,
        right,
        facts,
        obligations,
        assumptions,
        Bitvector32Term::int64_divide,
    )
}

fn apply_c_int64_remainder(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    apply_c_int64_division_like(
        left,
        right,
        facts,
        obligations,
        assumptions,
        Bitvector32Term::int64_remainder,
    )
}

fn apply_c_int64_division_like(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let zero = ConditionTerm::int64_equal(right.clone(), Bitvector32Term::Int64Constant(0));
    match decide_with_facts(assumptions, &facts, &zero) {
        Some(true) => {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero),
                facts,
                obligations,
            }];
        }
        Some(false) => {}
        None => {
            let mut nonzero_facts = facts.clone();
            add_condition_path_fact(&mut nonzero_facts, assumptions, zero.clone(), false)
                .expect("unknown int64 divisor fact should be consistent");
            let mut zero_facts = facts;
            add_condition_path_fact(&mut zero_facts, assumptions, zero, true)
                .expect("unknown int64 divisor fact should be consistent");
            let mut paths = apply_c_int64_division_nonzero(
                left,
                right,
                nonzero_facts,
                obligations.clone(),
                assumptions,
                result,
            );
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero),
                facts: zero_facts,
                obligations,
            });
            return paths;
        }
    }
    apply_c_int64_division_nonzero(left, right, facts, obligations, assumptions, result)
}

fn apply_c_int64_division_nonzero(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::int64_signed_divide_overflows(left.clone(), right.clone());
    apply_c_int64_overflowing(
        left,
        right,
        facts,
        obligations,
        assumptions,
        overflow,
        result,
    )
}

fn apply_c_uint64_division_like(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let zero = ConditionTerm::uint64_equal(right.clone(), Bitvector32Term::UInt64Constant(0));
    match decide_with_facts(assumptions, &facts, &zero) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(CValue::UInt64(result(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut nonzero_facts = facts.clone();
            add_condition_path_fact(&mut nonzero_facts, assumptions, zero.clone(), false)
                .expect("unknown uint64 divisor fact should be consistent");
            let mut zero_facts = facts;
            add_condition_path_fact(&mut zero_facts, assumptions, zero, true)
                .expect("unknown uint64 divisor fact should be consistent");
            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(CValue::UInt64(result(left, right))),
                    facts: nonzero_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::DivisionByZero,
                    ),
                    facts: zero_facts,
                    obligations,
                },
            ]
        }
    }
}

fn apply_c_uint32_division_like(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let divides_by_zero = ConditionTerm::equal(right.clone(), Bitvector32Term::Constant(0));
    match decide_with_facts(assumptions, &facts, &divides_by_zero) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(uint32(result(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(
                &mut normal_facts,
                assumptions,
                divides_by_zero.clone(),
                false,
            )
            .expect("unknown zero-divisor fact should be consistent");
            let mut zero_facts = facts;
            add_condition_path_fact(&mut zero_facts, assumptions, divides_by_zero, true)
                .expect("unknown zero-divisor fact should be consistent");
            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(uint32(result(left, right))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::DivisionByZero,
                    ),
                    facts: zero_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn apply_c_int32_shift_left(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    apply_c_int32_with_valid_shift_count(
        left,
        right,
        facts,
        obligations,
        assumptions,
        false,
        apply_c_int32_shift_left_valid_count,
    )
}

pub(in crate::kernel) fn apply_c_int32_shift_right(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    apply_c_int32_with_valid_shift_count(
        left,
        right,
        facts,
        obligations,
        assumptions,
        false,
        |left, right, facts, obligations, _| {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::arithmetic_shift_right(
                    left, right,
                ))),
                facts,
                obligations,
            }]
        },
    )
}

fn promote_c_shift_count(
    value: CValue,
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
) -> Option<(Bitvector32Term, bool)> {
    match value {
        CValue::UInt32(value) => Some((value, true)),
        CValue::Int32(value) => Some((value, false)),
        CValue::UInt8(value) => {
            add_uint8_range_execution_pure_facts(facts, assumptions, &value)?;
            Some((value, false))
        }
        CValue::Int16(value) => {
            add_int16_range_execution_pure_facts(facts, assumptions, &value)?;
            Some((value, false))
        }
        CValue::UInt16(value) => {
            add_uint16_range_execution_pure_facts(facts, assumptions, &value)?;
            Some((value, false))
        }
        CValue::Int64(value) => Some((value, false)),
        CValue::UInt64(value) => Some((value, true)),
        CValue::Void | CValue::Pointer(_) => None,
    }
}

pub(in crate::kernel) fn apply_c_shift_left(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let mut facts = facts;
    let Some((right, unsigned_count)) = promote_c_shift_count(right, &mut facts, assumptions)
    else {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    };
    match left {
        CValue::Int64(left) => apply_c_int64_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            apply_c_int64_shift_left_valid_count,
        ),
        CValue::UInt64(left) => apply_c_int64_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            apply_c_uint64_shift_left_valid_count,
        ),
        CValue::UInt32(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            |left, right, facts, obligations, _| {
                vec![CExpressionPath {
                    outcome: CExpressionOutcome::Value(uint32(
                        Bitvector32Term::unsigned_shift_left(left, right),
                    )),
                    facts,
                    obligations,
                }]
            },
        ),
        CValue::Int32(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            apply_c_int32_shift_left_valid_count,
        ),
        CValue::Int16(left) => {
            if add_int16_range_execution_pure_facts(&mut facts, assumptions, &left).is_none() {
                return Vec::new();
            }
            apply_c_int32_with_valid_shift_count(
                left,
                right,
                facts,
                obligations,
                assumptions,
                unsigned_count,
                apply_c_int32_shift_left_valid_count,
            )
        }
        CValue::UInt8(left) => {
            if add_uint8_range_execution_pure_facts(&mut facts, assumptions, &left).is_none() {
                return Vec::new();
            }
            apply_c_int32_with_valid_shift_count(
                left,
                right,
                facts,
                obligations,
                assumptions,
                unsigned_count,
                apply_c_int32_shift_left_valid_count,
            )
        }
        CValue::UInt16(left) => {
            if add_uint16_range_execution_pure_facts(&mut facts, assumptions, &left).is_none() {
                return Vec::new();
            }
            apply_c_int32_with_valid_shift_count(
                left,
                right,
                facts,
                obligations,
                assumptions,
                unsigned_count,
                apply_c_int32_shift_left_valid_count,
            )
        }
        CValue::Void | CValue::Pointer(_) => {
            vec![c_type_mismatch_expression_path(facts, obligations)]
        }
    }
}

pub(in crate::kernel) fn apply_c_shift_right(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let mut facts = facts;
    let Some((right, unsigned_count)) = promote_c_shift_count(right, &mut facts, assumptions)
    else {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    };
    match left {
        CValue::Int64(left) => apply_c_int64_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            apply_c_int64_shift_right_valid_count,
        ),
        CValue::UInt64(left) => apply_c_int64_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            apply_c_uint64_shift_right_valid_count,
        ),
        CValue::UInt32(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            |left, right, facts, obligations, _| {
                vec![CExpressionPath {
                    outcome: CExpressionOutcome::Value(uint32(
                        Bitvector32Term::logical_shift_right(left, right),
                    )),
                    facts,
                    obligations,
                }]
            },
        ),
        CValue::Int32(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            |left, right, facts, obligations, _| {
                vec![CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(
                        Bitvector32Term::arithmetic_shift_right(left, right),
                    )),
                    facts,
                    obligations,
                }]
            },
        ),
        CValue::Int16(left) => {
            if add_int16_range_execution_pure_facts(&mut facts, assumptions, &left).is_none() {
                return Vec::new();
            }
            apply_c_int32_with_valid_shift_count(
                left,
                right,
                facts,
                obligations,
                assumptions,
                unsigned_count,
                |left, right, facts, obligations, _| {
                    vec![CExpressionPath {
                        outcome: CExpressionOutcome::Value(int32(
                            Bitvector32Term::arithmetic_shift_right(left, right),
                        )),
                        facts,
                        obligations,
                    }]
                },
            )
        }
        CValue::UInt8(left) => {
            if add_uint8_range_execution_pure_facts(&mut facts, assumptions, &left).is_none() {
                return Vec::new();
            }
            apply_c_int32_with_valid_shift_count(
                left,
                right,
                facts,
                obligations,
                assumptions,
                unsigned_count,
                |left, right, facts, obligations, _| {
                    vec![CExpressionPath {
                        outcome: CExpressionOutcome::Value(int32(
                            Bitvector32Term::arithmetic_shift_right(left, right),
                        )),
                        facts,
                        obligations,
                    }]
                },
            )
        }
        CValue::UInt16(left) => {
            if add_uint16_range_execution_pure_facts(&mut facts, assumptions, &left).is_none() {
                return Vec::new();
            }
            apply_c_int32_with_valid_shift_count(
                left,
                right,
                facts,
                obligations,
                assumptions,
                unsigned_count,
                |left, right, facts, obligations, _| {
                    vec![CExpressionPath {
                        outcome: CExpressionOutcome::Value(int32(
                            Bitvector32Term::arithmetic_shift_right(left, right),
                        )),
                        facts,
                        obligations,
                    }]
                },
            )
        }
        CValue::Void | CValue::Pointer(_) => {
            vec![c_type_mismatch_expression_path(facts, obligations)]
        }
    }
}

fn apply_c_int64_with_valid_shift_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    unsigned_count: bool,
    apply_valid_count: ValidInt64ShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    let (count, invalid_count) = if unsigned_count {
        let count = Bitvector32Term::uint64_from_32(right);
        let invalid =
            ConditionTerm::uint64_greater_equal(count.clone(), Bitvector32Term::UInt64Constant(64));
        (count, invalid)
    } else {
        let count = Bitvector32Term::int64_from_32(right);
        let invalid =
            ConditionTerm::int64_signed_less_than(count.clone(), Bitvector32Term::Int64Constant(0));
        (count, invalid)
    };
    match decide_with_facts(assumptions, &facts, &invalid_count) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
            facts,
            obligations,
        }],
        Some(false) if !unsigned_count => {
            let too_large = ConditionTerm::int64_signed_greater_equal(
                count.clone(),
                Bitvector32Term::Int64Constant(64),
            );
            apply_c_int64_shift_count_upper_bound(
                left,
                count,
                too_large,
                facts,
                obligations,
                assumptions,
                apply_valid_count,
            )
        }
        Some(false) => apply_c_int64_shift_count_upper_bound(
            left,
            count.clone(),
            invalid_count,
            facts,
            obligations,
            assumptions,
            apply_valid_count,
        ),
        None => {
            let mut valid_facts = facts.clone();
            add_condition_path_fact(&mut valid_facts, assumptions, invalid_count.clone(), false)
                .expect("unknown shift-count fact should be consistent");
            let mut invalid_facts = facts;
            add_condition_path_fact(&mut invalid_facts, assumptions, invalid_count, true)
                .expect("unknown shift-count fact should be consistent");
            let mut paths = if unsigned_count {
                apply_c_int64_shift_count_upper_bound(
                    left,
                    count,
                    ConditionTerm::Constant(false),
                    valid_facts,
                    obligations.clone(),
                    assumptions,
                    apply_valid_count,
                )
            } else {
                let too_large = ConditionTerm::int64_signed_greater_equal(
                    count.clone(),
                    Bitvector32Term::Int64Constant(64),
                );
                apply_c_int64_shift_count_upper_bound(
                    left,
                    count,
                    too_large,
                    valid_facts,
                    obligations.clone(),
                    assumptions,
                    apply_valid_count,
                )
            };
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
                facts: invalid_facts,
                obligations,
            });
            paths
        }
    }
}

fn apply_c_int64_shift_count_upper_bound(
    left: Bitvector32Term,
    count: Bitvector32Term,
    too_large: ConditionTerm,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    apply_valid_count: ValidInt64ShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    match decide_with_facts(assumptions, &facts, &too_large) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
            facts,
            obligations,
        }],
        Some(false) => apply_valid_count(left, count, facts, obligations, assumptions),
        None => {
            let mut valid_facts = facts.clone();
            add_condition_path_fact(&mut valid_facts, assumptions, too_large.clone(), false)
                .expect("unknown shift-count fact should be consistent");
            let mut invalid_facts = facts;
            add_condition_path_fact(&mut invalid_facts, assumptions, too_large, true)
                .expect("unknown shift-count fact should be consistent");
            let mut paths =
                apply_valid_count(left, count, valid_facts, obligations.clone(), assumptions);
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
                facts: invalid_facts,
                obligations,
            });
            paths
        }
    }
}

fn apply_c_int64_shift_left_valid_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let negative_left =
        ConditionTerm::int64_signed_less_than(left.clone(), Bitvector32Term::Int64Constant(0));
    match decide_with_facts(assumptions, &facts, &negative_left) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
            facts,
            obligations,
        }],
        Some(false) => {
            apply_c_int64_shift_left_nonnegative(left, right, facts, obligations, assumptions)
        }
        None => {
            let mut valid_facts = facts.clone();
            add_condition_path_fact(&mut valid_facts, assumptions, negative_left.clone(), false)
                .expect("unknown shift operand fact should be consistent");
            let mut invalid_facts = facts;
            add_condition_path_fact(&mut invalid_facts, assumptions, negative_left, true)
                .expect("unknown shift operand fact should be consistent");
            let mut paths = apply_c_int64_shift_left_nonnegative(
                left,
                right,
                valid_facts,
                obligations.clone(),
                assumptions,
            );
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
                facts: invalid_facts,
                obligations,
            });
            paths
        }
    }
}

fn apply_c_int64_shift_left_nonnegative(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::int64_signed_shift_left_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(CValue::Int64(Bitvector32Term::int64_shift_left(
                left, right,
            ))),
            facts,
            obligations,
        }],
        None => {
            let mut valid_facts = facts.clone();
            add_condition_path_fact(&mut valid_facts, assumptions, overflow.clone(), false)
                .expect("unknown shift-overflow fact should be consistent");
            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown shift-overflow fact should be consistent");
            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(CValue::Int64(
                        Bitvector32Term::int64_shift_left(left, right),
                    )),
                    facts: valid_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

fn apply_c_uint64_shift_left_valid_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    _assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(CValue::UInt64(Bitvector32Term::uint64_shift_left(
            left, right,
        ))),
        facts,
        obligations,
    }]
}

fn apply_c_int64_shift_right_valid_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    _assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(CValue::Int64(
            Bitvector32Term::int64_arithmetic_shift_right(left, right),
        )),
        facts,
        obligations,
    }]
}

fn apply_c_uint64_shift_right_valid_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    _assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(CValue::UInt64(
            Bitvector32Term::uint64_logical_shift_right(left, right),
        )),
        facts,
        obligations,
    }]
}

fn apply_c_int32_with_valid_shift_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    unsigned_count: bool,
    apply_valid_count: ValidShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    if unsigned_count {
        return apply_c_int32_with_nonnegative_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            true,
            apply_valid_count,
        );
    }
    let negative_count =
        ConditionTerm::signed_less_than(right.clone(), Bitvector32Term::Constant(0));
    match decide_with_facts(assumptions, &facts, &negative_count) {
        Some(true) => {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
                facts,
                obligations,
            }];
        }
        Some(false) => {
            return apply_c_int32_with_nonnegative_shift_count(
                left,
                right,
                facts,
                obligations,
                assumptions,
                false,
                apply_valid_count,
            );
        }
        None => {}
    }

    let mut normal_facts = facts.clone();
    add_condition_path_fact(
        &mut normal_facts,
        assumptions,
        negative_count.clone(),
        false,
    )
    .expect("unknown negative shift-count fact should be consistent");

    let mut invalid_facts = facts;
    add_condition_path_fact(&mut invalid_facts, assumptions, negative_count, true)
        .expect("unknown negative shift-count fact should be consistent");

    let mut paths = apply_c_int32_with_nonnegative_shift_count(
        left,
        right,
        normal_facts,
        obligations.clone(),
        assumptions,
        false,
        apply_valid_count,
    );
    paths.push(CExpressionPath {
        outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
        facts: invalid_facts,
        obligations,
    });
    paths
}

fn apply_c_int32_with_nonnegative_shift_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    unsigned_count: bool,
    apply_valid_count: ValidShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    let too_large_count = if unsigned_count {
        ConditionTerm::unsigned_greater_equal(right.clone(), Bitvector32Term::Constant(32))
    } else {
        ConditionTerm::signed_greater_equal(right.clone(), Bitvector32Term::Constant(32))
    };
    match decide_with_facts(assumptions, &facts, &too_large_count) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
            facts,
            obligations,
        }],
        Some(false) => apply_valid_count(left, right, facts, obligations, assumptions),
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(
                &mut normal_facts,
                assumptions,
                too_large_count.clone(),
                false,
            )
            .expect("unknown large shift-count fact should be consistent");

            let mut invalid_facts = facts;
            add_condition_path_fact(&mut invalid_facts, assumptions, too_large_count, true)
                .expect("unknown large shift-count fact should be consistent");

            let mut paths =
                apply_valid_count(left, right, normal_facts, obligations.clone(), assumptions);
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
                facts: invalid_facts,
                obligations,
            });
            paths
        }
    }
}

fn apply_c_int32_shift_left_valid_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let negative_left = ConditionTerm::signed_less_than(left.clone(), Bitvector32Term::Constant(0));
    match decide_with_facts(assumptions, &facts, &negative_left) {
        Some(true) => {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
                facts,
                obligations,
            }];
        }
        Some(false) => {
            return apply_c_int32_shift_left_nonnegative(
                left,
                right,
                facts,
                obligations,
                assumptions,
            );
        }
        None => {}
    }

    let mut normal_facts = facts.clone();
    add_condition_path_fact(&mut normal_facts, assumptions, negative_left.clone(), false)
        .expect("unknown negative left-shift operand fact should be consistent");

    let mut invalid_facts = facts;
    add_condition_path_fact(&mut invalid_facts, assumptions, negative_left, true)
        .expect("unknown negative left-shift operand fact should be consistent");

    let mut paths = apply_c_int32_shift_left_nonnegative(
        left,
        right,
        normal_facts,
        obligations.clone(),
        assumptions,
    );
    paths.push(CExpressionPath {
        outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidShift),
        facts: invalid_facts,
        obligations,
    });
    paths
}

fn apply_c_int32_shift_left_nonnegative(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_shift_left_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::shift_left(left, right))),
            facts,
            obligations,
        }],
        None => {
            let mut normal_facts = facts.clone();
            add_condition_path_fact(&mut normal_facts, assumptions, overflow.clone(), false)
                .expect("unknown left-shift overflow fact should be consistent");

            let mut overflow_facts = facts;
            add_condition_path_fact(&mut overflow_facts, assumptions, overflow, true)
                .expect("unknown left-shift overflow fact should be consistent");

            vec![
                CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(Bitvector32Term::shift_left(
                        left, right,
                    ))),
                    facts: normal_facts,
                    obligations: obligations.clone(),
                },
                CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn evaluate_c_equal_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    evaluate_c_value_binary_paths(
        state,
        left,
        right,
        assumptions,
        budget,
        |left, right, facts, obligations| {
            apply_c_equal(left, right, facts, obligations, assumptions)
        },
    )
}

pub(in crate::kernel) fn apply_c_equal(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        let mut facts = facts;
        let Some((left, right, _)) = apply_c_scalar_terms(left, right, &mut facts, assumptions)
        else {
            return Vec::new();
        };
        let condition = if matches!(width, ScalarWidth::Int64) {
            ConditionTerm::int64_equal(left, right)
        } else {
            ConditionTerm::uint64_equal(left, right)
        };
        return condition_as_c_int32_paths(condition, facts, obligations, assumptions);
    }
    match (left, right) {
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            if !pointer_types_compatible(&left, &right) {
                vec![c_type_mismatch_expression_path(facts, obligations)]
            } else {
                condition_as_c_int32_paths(
                    pointer_equality_condition(left.into_pointer(), right.into_pointer()),
                    facts,
                    obligations,
                    assumptions,
                )
            }
        }
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            condition_as_c_int32_paths(
                pointer_is_null_condition(pointer.into_pointer()),
                facts,
                obligations,
                assumptions,
            )
        }
        (
            left @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)),
            right @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)),
        ) if scalar_uses_uint32(&left, &right) => {
            let mut facts = facts;
            let Some(left) = promote_c_uint32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_uint32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            condition_as_c_int32_paths(
                ConditionTerm::equal(left, right),
                facts,
                obligations,
                assumptions,
            )
        }
        (
            left @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
            right @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
        ) => {
            let mut facts = facts;
            let Some(left) = promote_c_int32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            condition_as_c_int32_paths(
                ConditionTerm::equal(left, right),
                facts,
                obligations,
                assumptions,
            )
        }
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

pub(in crate::kernel) fn evaluate_c_not_equal_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    evaluate_c_value_binary_paths(
        state,
        left,
        right,
        assumptions,
        budget,
        |left, right, facts, obligations| {
            apply_c_not_equal(left, right, facts, obligations, assumptions)
        },
    )
}

pub(in crate::kernel) fn apply_c_not_equal(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        let mut facts = facts;
        let Some((left, right, _)) = apply_c_scalar_terms(left, right, &mut facts, assumptions)
        else {
            return Vec::new();
        };
        let condition = if matches!(width, ScalarWidth::Int64) {
            ConditionTerm::int64_equal(left, right)
        } else {
            ConditionTerm::uint64_equal(left, right)
        };
        return condition_as_c_int32_not_paths(condition, facts, obligations, assumptions);
    }
    match (left, right) {
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            if !pointer_types_compatible(&left, &right) {
                vec![c_type_mismatch_expression_path(facts, obligations)]
            } else {
                condition_as_c_int32_not_paths(
                    pointer_equality_condition(left.into_pointer(), right.into_pointer()),
                    facts,
                    obligations,
                    assumptions,
                )
            }
        }
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            condition_as_c_int32_not_paths(
                pointer_is_null_condition(pointer.into_pointer()),
                facts,
                obligations,
                assumptions,
            )
        }
        (
            left @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)),
            right @ (CValue::Int16(_)
            | CValue::Int32(_)
            | CValue::UInt8(_)
            | CValue::UInt16(_)
            | CValue::UInt32(_)),
        ) if scalar_uses_uint32(&left, &right) => {
            let mut facts = facts;
            let Some(left) = promote_c_uint32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_uint32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            condition_as_c_int32_not_paths(
                ConditionTerm::equal(left, right),
                facts,
                obligations,
                assumptions,
            )
        }
        (
            left @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
            right @ (CValue::Int16(_) | CValue::Int32(_) | CValue::UInt8(_) | CValue::UInt16(_)),
        ) => {
            let mut facts = facts;
            let Some(left) = promote_c_int32_path_value(left, &mut facts, assumptions) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions) else {
                return Vec::new();
            };
            condition_as_c_int32_not_paths(
                ConditionTerm::equal(left, right),
                facts,
                obligations,
                assumptions,
            )
        }
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

pub(in crate::kernel) fn evaluate_c_not_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        match path.outcome {
            CExpressionOutcome::Value(value) => {
                paths.extend(
                    c_truthiness_paths(value, path.facts, path.obligations, assumptions)
                        .into_iter()
                        .map(|truthiness| CExpressionPath {
                            outcome: CExpressionOutcome::Value(int32(if truthiness.is_true {
                                0
                            } else {
                                1
                            })),
                            facts: truthiness.facts,
                            obligations: truthiness.obligations,
                        }),
                );
            }
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

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn evaluate_c_logical_and_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        match left_path.outcome {
            CExpressionOutcome::Value(left_value) => {
                for left_truthiness in c_truthiness_paths(
                    left_value,
                    left_path.facts,
                    left_path.obligations,
                    assumptions,
                ) {
                    if !left_truthiness.is_true {
                        paths.push(CExpressionPath {
                            outcome: CExpressionOutcome::Value(int32(0)),
                            facts: left_truthiness.facts,
                            obligations: left_truthiness.obligations,
                        });
                        continue;
                    }

                    let right_assumptions = assumptions_with_path_context(
                        assumptions,
                        &left_truthiness.facts,
                        &left_truthiness.obligations,
                    );
                    for right_path in
                        evaluate_c_expression_paths(state, right, &right_assumptions, budget)?
                    {
                        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                            &left_truthiness.facts,
                            &left_truthiness.obligations,
                            &right_path.facts,
                            &right_path.obligations,
                            assumptions,
                        ) else {
                            continue;
                        };

                        match right_path.outcome {
                            CExpressionOutcome::Value(value) => {
                                paths.extend(c_truthiness_as_c_int32_paths(
                                    value,
                                    facts,
                                    obligations,
                                    assumptions,
                                ))
                            }
                            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => paths
                                .push(CExpressionPath {
                                    outcome: CExpressionOutcome::UndefinedBehavior(
                                        undefined_behavior,
                                    ),
                                    facts,
                                    obligations,
                                }),
                            CExpressionOutcome::RuntimeError(error) => {
                                paths.push(CExpressionPath {
                                    outcome: CExpressionOutcome::RuntimeError(error),
                                    facts,
                                    obligations,
                                })
                            }
                        }
                    }
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_path.facts,
                    obligations: left_path.obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: left_path.facts,
                obligations: left_path.obligations,
            }),
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn evaluate_c_logical_or_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        match left_path.outcome {
            CExpressionOutcome::Value(left_value) => {
                for left_truthiness in c_truthiness_paths(
                    left_value,
                    left_path.facts,
                    left_path.obligations,
                    assumptions,
                ) {
                    if left_truthiness.is_true {
                        paths.push(CExpressionPath {
                            outcome: CExpressionOutcome::Value(int32(1)),
                            facts: left_truthiness.facts,
                            obligations: left_truthiness.obligations,
                        });
                        continue;
                    }

                    let right_assumptions = assumptions_with_path_context(
                        assumptions,
                        &left_truthiness.facts,
                        &left_truthiness.obligations,
                    );
                    for right_path in
                        evaluate_c_expression_paths(state, right, &right_assumptions, budget)?
                    {
                        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                            &left_truthiness.facts,
                            &left_truthiness.obligations,
                            &right_path.facts,
                            &right_path.obligations,
                            assumptions,
                        ) else {
                            continue;
                        };

                        match right_path.outcome {
                            CExpressionOutcome::Value(value) => {
                                paths.extend(c_truthiness_as_c_int32_paths(
                                    value,
                                    facts,
                                    obligations,
                                    assumptions,
                                ))
                            }
                            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => paths
                                .push(CExpressionPath {
                                    outcome: CExpressionOutcome::UndefinedBehavior(
                                        undefined_behavior,
                                    ),
                                    facts,
                                    obligations,
                                }),
                            CExpressionOutcome::RuntimeError(error) => {
                                paths.push(CExpressionPath {
                                    outcome: CExpressionOutcome::RuntimeError(error),
                                    facts,
                                    obligations,
                                })
                            }
                        }
                    }
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_path.facts,
                    obligations: left_path.obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(error),
                facts: left_path.facts,
                obligations: left_path.obligations,
            }),
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn pointer_equality_condition(
    left: Pointer,
    right: Pointer,
) -> ConditionTerm {
    if left.block == right.block {
        ConditionTerm::pointer_offset_equal(left.offset, right.offset)
    } else {
        ConditionTerm::pointer_equal(left, right)
    }
}

pub(in crate::kernel) fn pointer_is_null_condition(pointer: Pointer) -> ConditionTerm {
    pointer_equality_condition(pointer, Pointer::null())
}

pub(in crate::kernel) fn evaluate_c_int32_binary_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    apply: impl Fn(
        Bitvector32Term,
        Bitvector32Term,
        Vec<ExecutionPureFact>,
        Vec<ProofObligation>,
    ) -> Vec<CExpressionPath>,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let mut left_facts = left_facts;
        let left = match left_outcome {
            CExpressionOutcome::Value(left) => {
                let Some(left) = promote_c_int32_path_value(left, &mut left_facts, assumptions)
                else {
                    paths.push(c_type_mismatch_expression_path(
                        left_facts,
                        left_obligations,
                    ));
                    continue;
                };
                left
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
            CExpressionOutcome::RuntimeError(error) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts: left_facts,
                    obligations: left_obligations,
                });
                continue;
            }
        };

        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in evaluate_c_expression_paths(state, right, &right_assumptions, budget)? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &left_facts,
                &left_obligations,
                &right_path.facts,
                &right_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match right_path.outcome {
                CExpressionOutcome::Value(right) => {
                    let mut facts = facts;
                    let Some(right) = promote_c_int32_path_value(right, &mut facts, assumptions)
                    else {
                        paths.push(c_type_mismatch_expression_path(facts, obligations));
                        continue;
                    };
                    paths.extend(apply(left.clone(), right, facts, obligations));
                }
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    })
                }
                CExpressionOutcome::RuntimeError(error) => paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                }),
            }
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn apply_c_int32_total_binary(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    apply: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(int32(apply(left, right))),
        facts,
        obligations,
    }]
}

pub(in crate::kernel) fn evaluate_c_int32_total_unary_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    apply: fn(Bitvector32Term) -> Bitvector32Term,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        match path.outcome {
            CExpressionOutcome::Value(value) => {
                let mut facts = path.facts;
                let Some(value) = promote_c_int32_path_value(value, &mut facts, assumptions) else {
                    paths.push(c_type_mismatch_expression_path(facts, path.obligations));
                    continue;
                };
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::Value(int32(apply(value))),
                    facts,
                    obligations: path.obligations,
                });
            }
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

    budget.check_path_width(paths.len())?;
    Ok(paths)
}
