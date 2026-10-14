use super::*;

type ValidShiftCountEvaluator = fn(
    Bitvector32Term,
    Bitvector32Term,
    ExecutionFacts,
    Vec<ProofObligation>,
    &PureFactContext,
) -> Vec<CExpressionPath>;

type ValidInt64ShiftCountEvaluator = fn(
    Bitvector32Term,
    Bitvector32Term,
    ExecutionFacts,
    Vec<ProofObligation>,
    &PureFactContext,
) -> Vec<CExpressionPath>;

fn c_type_mismatch_expression_path(
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
) -> CExpressionPath {
    CExpressionPath {
        outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
        facts,
        obligations,
    }
}

/// Splits an operation on `undefined`, the condition under which it has
/// `behavior`. A decided condition keeps one side. An undecided one
/// continues `defined` under the condition's negation, followed by the
/// undefined path under the condition itself.
fn split_on_undefined_behavior(
    undefined: ConditionTerm,
    behavior: CUndefinedBehavior,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    defined: impl FnOnce(ExecutionFacts, Vec<ProofObligation>) -> Vec<CExpressionPath>,
) -> Vec<CExpressionPath> {
    match decide_with_facts(assumptions, &facts, &undefined) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(behavior),
            facts,
            obligations,
        }],
        Some(false) => defined(facts, obligations),
        None => {
            let mut defined_facts = facts.clone();
            add_condition_path_fact(&mut defined_facts, assumptions, undefined.clone(), false)
                .expect("an undecided undefined-behavior condition should be consistent");
            let mut undefined_facts = facts;
            add_condition_path_fact(&mut undefined_facts, assumptions, undefined, true)
                .expect("an undecided undefined-behavior condition should be consistent");
            let mut paths = defined(defined_facts, obligations.clone());
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(behavior),
                facts: undefined_facts,
                obligations,
            });
            paths
        }
    }
}

fn pointer_types_compatible(left: &CPointerValue, right: &CPointerValue) -> bool {
    left.c_type().pointer_types_compatible(right.c_type()) || left.is_null() || right.is_null()
}

fn scalar_uses_uint32(left: &CValue, right: &CValue) -> bool {
    matches!(left, CValue::UInt32(_)) || matches!(right, CValue::UInt32(_))
}

fn numeric_pointer_integer_value(value: CValue) -> CValue {
    match value {
        CValue::PointerInteger(value) => value.numeric_value(),
        value => value,
    }
}

fn single_pointer_integer_origin(
    left: &CValue,
    right: &CValue,
) -> Option<std::sync::Arc<CPointerIntegerValue>> {
    match (left, right) {
        (CValue::PointerInteger(value), right) if !matches!(right, CValue::PointerInteger(_)) => {
            Some(value.clone())
        }
        (left, CValue::PointerInteger(value)) if !matches!(left, CValue::PointerInteger(_)) => {
            Some(value.clone())
        }
        _ => None,
    }
}

fn retain_pointer_integer_origin(
    mut paths: Vec<CExpressionPath>,
    origin: Option<std::sync::Arc<CPointerIntegerValue>>,
) -> Vec<CExpressionPath> {
    if let Some(origin) = origin {
        for path in &mut paths {
            if let CExpressionOutcome::Value(value) = &path.outcome
                && let Some(value) = origin.with_numeric_value(value.clone())
            {
                path.outcome =
                    CExpressionOutcome::Value(CValue::PointerInteger(std::sync::Arc::new(value)));
            }
        }
    }
    paths
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
            CValue::Bool(_)
                | CValue::Int8(_)
                | CValue::Int16(_)
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

// Integer promotions turn a boolean rvalue into int before an ordinary
// scalar operation. Keep pointer cases outside this conversion: a boolean
// variable is not a null pointer constant, and boolean pointer arithmetic is
// outside the supported C0 subset.
fn promote_c_bool_scalar_operands(left: CValue, right: CValue) -> (CValue, CValue) {
    if scalar_width(&left, &right).is_none() {
        return (left, right);
    }
    let promote = |value| match value {
        CValue::Bool(bits) => CValue::Int32(bits),
        value => value,
    };
    (promote(left), promote(right))
}

fn coerce_c_float_operands(
    left: &CValue,
    right: &CValue,
    obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(CValue, CValue, CType, Vec<ProofObligation>)> {
    let target_type = if matches!(left, CValue::Float64(_)) || matches!(right, CValue::Float64(_)) {
        CType::Float64
    } else if matches!(left, CValue::Float32(_)) || matches!(right, CValue::Float32(_)) {
        CType::Float32
    } else {
        return None;
    };
    let mut obligations = obligations.to_vec();
    let left = coerce_c_value_to_type(left.clone(), target_type, &mut obligations, assumptions)?;
    let right = coerce_c_value_to_type(right.clone(), target_type, &mut obligations, assumptions)?;
    Some((left, right, target_type, obligations))
}

fn apply_c_float_binary(
    left: CValue,
    right: CValue,
    target_type: CType,
    operator: CFloatBinaryOperator,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
) -> Vec<CExpressionPath> {
    let outcome = match (target_type, left, right) {
        (CType::Float32, CValue::Float32(left), CValue::Float32(right)) => {
            CExpressionOutcome::Value(CValue::Float32(Bitvector32Term::float32_binary(
                left, right, operator,
            )))
        }
        (CType::Float64, CValue::Float64(left), CValue::Float64(right)) => {
            CExpressionOutcome::Value(CValue::Float64(Bitvector32Term::float64_binary(
                left, right, operator,
            )))
        }
        _ => CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
    };
    vec![CExpressionPath {
        outcome,
        facts,
        obligations,
    }]
}

fn apply_c_float_comparison(
    left: CValue,
    right: CValue,
    target_type: CType,
    operator: CComparisonOperator,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let condition = match (target_type, left, right) {
        (CType::Float32, CValue::Float32(left), CValue::Float32(right)) => {
            ConditionTerm::float32_compare(left, right, operator)
        }
        (CType::Float64, CValue::Float64(left), CValue::Float64(right)) => {
            ConditionTerm::float64_compare(left, right, operator)
        }
        _ => return vec![c_type_mismatch_expression_path(facts, obligations)],
    };
    condition_as_c_int32_paths(condition, facts, obligations, assumptions)
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

        // A binary operator operating on a freed pointer uses its
        // indeterminate value; see `freed_pointer_use`.
        if let Some(undefined_behavior) = freed_pointer_use(state, &left, assumptions) {
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                facts: left_facts,
                obligations: left_obligations,
            });
            continue;
        }
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in refuse_freed_pointer_value_paths(
            state,
            evaluate_c_expression_paths(state, right, &right_assumptions, budget)?,
            assumptions,
        ) {
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

            paths.extend(
                apply_c_add(
                    state,
                    left.clone(),
                    right,
                    left_step_width,
                    right_step_width,
                    facts,
                    obligations,
                    assumptions,
                )
                .into_iter()
                .map(fold_c_int32_constant_increment),
            );
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// A C int32 sum `(x + a) + b` of constants whose signed sum is an int32 is
/// `x + (a + b)`, both as bits and, on a path where the add did not
/// overflow, as integers. Folding keeps a value incremented N times one node
/// deep, where it was an N-deep term each later overflow decision ranged.
/// Only executed C folds: a written proposition is lowered through
/// [`apply_c_add`] directly and keeps the shape its proof names, in which a
/// compound operand can be an opaque affine atom.
fn fold_c_int32_constant_increment(mut path: CExpressionPath) -> CExpressionPath {
    if let CExpressionOutcome::Value(CValue::Int32(Bitvector32Term::Add(base, increment))) =
        &path.outcome
        && let (Bitvector32Term::Add(inner, addend), Bitvector32Term::Constant(increment)) =
            (base.as_ref(), increment.as_ref())
        && let Bitvector32Term::Constant(addend) = addend.as_ref()
        && let Some(sum) = (*addend as i32).checked_add(*increment as i32)
    {
        path.outcome = CExpressionOutcome::Value(CValue::Int32(Bitvector32Term::add(
            inner.as_ref().clone(),
            Bitvector32Term::Constant(sum as u32),
        )));
    }
    path
}

pub(in crate::kernel) fn apply_c_add(
    state: &CState,
    left: CValue,
    right: CValue,
    left_step_width: Option<u32>,
    right_step_width: Option<u32>,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if matches!(&left, CValue::PointerInteger(_)) || matches!(&right, CValue::PointerInteger(_)) {
        let origin = single_pointer_integer_origin(&left, &right);
        let paths = apply_c_add(
            state,
            numeric_pointer_integer_value(left),
            numeric_pointer_integer_value(right),
            left_step_width,
            right_step_width,
            facts,
            obligations,
            assumptions,
        );
        return retain_pointer_integer_origin(paths, origin);
    }
    if let Some((left, right, target_type, obligations)) =
        coerce_c_float_operands(&left, &right, &obligations, assumptions)
    {
        return apply_c_float_binary(
            left,
            right,
            target_type,
            CFloatBinaryOperator::Add,
            facts,
            obligations,
        );
    }
    let (left, right) = promote_c_bool_scalar_operands(left, right);
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return WideArithmetic::Add.apply(left, right, width, facts, obligations, assumptions);
    }
    match (left, right) {
        (
            left @ (crate::kernel::integer32_c_value!(_)),
            right @ (crate::kernel::integer32_c_value!(_)),
        ) if scalar_uses_uint32(&left, &right) => {
            let facts = facts;
            let Some(left) = promote_c_uint32_path_value(left) else {
                return Vec::new();
            };
            let Some(right) = promote_c_uint32_path_value(right) else {
                return Vec::new();
            };
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(uint32(Bitvector32Term::add(left, right))),
                facts,
                obligations,
            }]
        }
        (
            left @ (crate::kernel::int_promoted_c_value!(_)),
            right @ (crate::kernel::int_promoted_c_value!(_)),
        ) => {
            let facts = facts;
            let Some(left) = promote_c_int32_path_value(left) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right) else {
                return Vec::new();
            };
            apply_c_int32_add(left, right, facts, obligations, assumptions)
        }
        (CValue::Pointer(pointer), offset @ (crate::kernel::integer64_c_value!(_))) => {
            let mut facts = facts;
            let Some((offset, unsigned, wide)) = pointer_index_term(offset, &facts, assumptions)
            else {
                return Vec::new();
            };
            let Some(byte_width) = pointer_value_step_width(&pointer, left_step_width) else {
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
                unsigned,
                wide,
                facts,
                obligations,
                assumptions,
            )
        }
        (offset @ (crate::kernel::integer64_c_value!(_)), CValue::Pointer(pointer)) => {
            let mut facts = facts;
            let Some((offset, unsigned, wide)) = pointer_index_term(offset, &facts, assumptions)
            else {
                return Vec::new();
            };
            let Some(byte_width) = pointer_value_step_width(&pointer, right_step_width) else {
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
                unsigned,
                wide,
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
                state,
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
    apply: impl Fn(CValue, CValue, ExecutionFacts, Vec<ProofObligation>) -> Vec<CExpressionPath>,
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

        // A binary operator operating on a freed pointer uses its
        // indeterminate value; see `freed_pointer_use`.
        if let Some(undefined_behavior) = freed_pointer_use(state, &left, assumptions) {
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(undefined_behavior),
                facts: left_facts,
                obligations: left_obligations,
            });
            continue;
        }
        let right_assumptions =
            assumptions_with_path_context(assumptions, &left_facts, &left_obligations);
        for right_path in refuse_freed_pointer_value_paths(
            state,
            evaluate_c_expression_paths(state, right, &right_assumptions, budget)?,
            assumptions,
        ) {
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
) -> Option<(Bitvector32Term, Bitvector32Term, ScalarWidth)> {
    let width = scalar_width(&left, &right)?;
    let left_term = match width {
        ScalarWidth::Int32 => promote_c_int32_path_value(left)?,
        ScalarWidth::UInt32 => promote_c_uint32_path_value(left)?,
        ScalarWidth::Int64 => promote_c_int64_path_value(left)?,
        ScalarWidth::UInt64 => promote_c_uint64_path_value(left)?,
    };
    let right_term = match width {
        ScalarWidth::Int32 => promote_c_int32_path_value(right)?,
        ScalarWidth::UInt32 => promote_c_uint32_path_value(right)?,
        ScalarWidth::Int64 => promote_c_int64_path_value(right)?,
        ScalarWidth::UInt64 => promote_c_uint64_path_value(right)?,
    };
    Some((left_term, right_term, width))
}

/// A 64-bit arithmetic operator, applied by `WideArithmetic::apply`.
#[derive(Clone, Copy)]
enum WideArithmetic {
    Add,
    Subtract,
    Multiply,
    Divide,
    Remainder,
}

type WideTermOperation = fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term;

impl WideArithmetic {
    fn apply(
        self,
        left: CValue,
        right: CValue,
        width: ScalarWidth,
        facts: ExecutionFacts,
        obligations: Vec<ProofObligation>,
        assumptions: &PureFactContext,
    ) -> Vec<CExpressionPath> {
        let Some((left, right, _)) = apply_c_scalar_terms(left, right) else {
            return Vec::new();
        };
        match width {
            ScalarWidth::Int64 => {
                let (overflows, result): (
                    fn(Bitvector32Term, Bitvector32Term) -> ConditionTerm,
                    WideTermOperation,
                ) = match self {
                    WideArithmetic::Add => (
                        ConditionTerm::int64_signed_add_overflows,
                        Bitvector32Term::int64_add,
                    ),
                    WideArithmetic::Subtract => (
                        ConditionTerm::int64_signed_subtract_overflows,
                        Bitvector32Term::int64_subtract,
                    ),
                    WideArithmetic::Multiply => (
                        ConditionTerm::int64_signed_multiply_overflows,
                        Bitvector32Term::int64_multiply,
                    ),
                    WideArithmetic::Divide => {
                        return apply_c_int64_division_like(
                            left,
                            right,
                            facts,
                            obligations,
                            assumptions,
                            Bitvector32Term::int64_divide,
                        );
                    }
                    WideArithmetic::Remainder => {
                        return apply_c_int64_division_like(
                            left,
                            right,
                            facts,
                            obligations,
                            assumptions,
                            Bitvector32Term::int64_remainder,
                        );
                    }
                };
                let overflow = overflows(left.clone(), right.clone());
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
            ScalarWidth::UInt64 => {
                let result: WideTermOperation = match self {
                    WideArithmetic::Add => Bitvector32Term::uint64_add,
                    WideArithmetic::Subtract => Bitvector32Term::uint64_subtract,
                    WideArithmetic::Multiply => Bitvector32Term::uint64_multiply,
                    WideArithmetic::Divide => {
                        return apply_c_uint64_division_like(
                            left,
                            right,
                            facts,
                            obligations,
                            assumptions,
                            Bitvector32Term::uint64_divide,
                        );
                    }
                    WideArithmetic::Remainder => {
                        return apply_c_uint64_division_like(
                            left,
                            right,
                            facts,
                            obligations,
                            assumptions,
                            Bitvector32Term::uint64_remainder,
                        );
                    }
                };
                vec![CExpressionPath {
                    outcome: CExpressionOutcome::Value(CValue::UInt64(result(left, right))),
                    facts,
                    obligations,
                }]
            }
            ScalarWidth::Int32 | ScalarWidth::UInt32 => unreachable!(),
        }
    }
}

fn apply_c_wide_comparison(
    operator: CComparisonOperator,
    left: CValue,
    right: CValue,
    width: ScalarWidth,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let Some((left, right, _)) = apply_c_scalar_terms(left, right) else {
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

pub(in crate::kernel) fn apply_c_multiply(
    left: CValue,
    right: CValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let left = numeric_pointer_integer_value(left);
    let right = numeric_pointer_integer_value(right);
    if matches!(left, CValue::Int128(_)) || matches!(right, CValue::Int128(_)) {
        return apply_c_int128_multiply(left, right, facts, obligations, assumptions);
    }
    if let Some((left, right, target_type, obligations)) =
        coerce_c_float_operands(&left, &right, &obligations, assumptions)
    {
        return apply_c_float_binary(
            left,
            right,
            target_type,
            CFloatBinaryOperator::Multiply,
            facts,
            obligations,
        );
    }
    let (left, right) = promote_c_bool_scalar_operands(left, right);
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return WideArithmetic::Multiply.apply(left, right, width, facts, obligations, assumptions);
    }
    let scalar_left = matches!(left, crate::kernel::integer32_c_value!(_));
    let scalar_right = matches!(right, crate::kernel::integer32_c_value!(_));
    if !scalar_left || !scalar_right {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    }
    let facts = facts;
    let Some((left, right, width)) = apply_c_scalar_terms(left, right) else {
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

/// Signed wide multiplication is exact multiplication followed by the shared
/// checked machine conversion. Range failure is native signed overflow, not
/// a modulo cast or an unbounded Integer result. Other wide operations keep
/// their own admission boundary.
fn apply_c_int128_multiply(
    left: CValue,
    right: CValue,
    mut facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    fn observe(value: CValue, assumptions: &PureFactContext) -> Option<IntegerTerm> {
        let ty = match value.c_type() {
            // Boolean operands are normalized 0/1. The other narrow types
            // retain their actual numeric interpretation before promotion.
            CType::Bool => MachineIntegerType::UInt8,
            CType::UInt128 => return None,
            ty => MachineIntegerType::from_c_type(ty)?,
        };
        let term = match value {
            CValue::Bool(term)
            | CValue::Int8(term)
            | CValue::UInt8(term)
            | CValue::Int16(term)
            | CValue::UInt16(term)
            | CValue::Int32(term)
            | CValue::UInt32(term)
            | CValue::Int64(term)
            | CValue::UInt64(term)
            | CValue::Int128(term) => term,
            _ => return None,
        };
        let observed = IntegerTerm::from_machine(ty, term)?;
        // Numeric widening has already normalized to the original observer.
        // Resolve only its indexed equality component, keeping the original
        // signedness; unknown values retain both product-bound obligations.
        if let IntegerTerm::Machine(machine) = &observed {
            let constant = match machine.ty() {
                MachineIntegerType::Int64 => assumptions
                    .wide_constant_from_equalities(machine.value())
                    .map(|value| IntegerTerm::constant_i64(value as i64)),
                MachineIntegerType::UInt64 => assumptions
                    .wide_constant_from_equalities(machine.value())
                    .map(|value| IntegerTerm::constant(num_bigint::BigInt::from(value))),
                _ => None,
            };
            if let Some(constant) = constant {
                return Some(constant);
            }
        }
        Some(observed)
    }
    let (Some(left), Some(right)) = (observe(left, assumptions), observe(right, assumptions))
    else {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    };
    let product = IntegerTerm::multiply(left, right);
    let destination = MachineIntegerType::Int128;
    let (min, max) = destination.format().bounds();
    let mut paths = Vec::new();
    for (guard, equivalent) in [
        (
            ConditionTerm::integer_greater_equal(
                product.clone(),
                IntegerTerm::constant(min.clone()),
            ),
            ConditionTerm::integer_less_equal(IntegerTerm::constant(min), product.clone()),
        ),
        (
            ConditionTerm::integer_less_equal(product.clone(), IntegerTerm::constant(max.clone())),
            ConditionTerm::integer_greater_equal(IntegerTerm::constant(max), product.clone()),
        ),
    ] {
        // Product-bound certificates use <= for either endpoint. Consult the
        // equivalent orientation directly rather than searching ambient facts.
        match decide_with_facts(assumptions, &facts, &guard)
            .or_else(|| decide_with_facts(assumptions, &facts, &equivalent))
        {
            Some(false) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts,
                    obligations,
                });
                return paths;
            }
            Some(true) => {}
            None => {
                let mut overflow_facts = facts.clone();
                add_condition_path_fact(&mut overflow_facts, assumptions, guard.clone(), false)
                    .expect("unknown wide multiplication bound must have a consistent false path");
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: overflow_facts,
                    obligations: obligations.clone(),
                });
                add_condition_path_fact(&mut facts, assumptions, guard, true)
                    .expect("unknown wide multiplication bound must have a consistent true path");
            }
        }
    }
    let term = if let Some(constant) = product.as_const() {
        destination
            .constant_term(
                MachineIntegerConstant::from_integer(destination.format(), constant)
                    .expect("both signed wide product bounds hold"),
            )
            .expect("exact wide format")
    } else {
        Bitvector32Term::IntegerToMachine {
            value: product.clone().into(),
            destination,
        }
    };
    // Both range guards hold on this normal path, so observation of the
    // representable native product preserves the exact Integer product.
    // Keep this relation explicit, as for guarded quotient/remainder results.
    let observed = IntegerTerm::from_machine(destination, term.clone()).expect("typed wide result");
    let definition = ConditionTerm::integer_equal(observed, product);
    if definition != ConditionTerm::Constant(true) {
        facts.push(ExecutionPureFact::certified(Proposition::ConditionIs(
            definition, true,
        )));
    }
    paths.push(CExpressionPath {
        outcome: CExpressionOutcome::Value(CValue::Int128(term)),
        facts,
        obligations,
    });
    paths
}

/// Compare already-resolved wide operands by their full mathematical values.
/// Signedness belongs to the observer, and promotions remain caller-owned.
fn apply_c_int128_comparison(
    operator: CComparisonOperator,
    left: CValue,
    right: CValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let Some(condition) = wide_integer_comparison_condition(operator, &left, &right) else {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    };
    // Complementary relations have separate Integer nodes. Query the two
    // exact keys without scanning unrelated premises or changing the guard.
    let complement = match operator {
        CComparisonOperator::Equal => CComparisonOperator::NotEqual,
        CComparisonOperator::NotEqual => CComparisonOperator::Equal,
        CComparisonOperator::LessThan => CComparisonOperator::GreaterEqual,
        CComparisonOperator::LessEqual => CComparisonOperator::GreaterThan,
        CComparisonOperator::GreaterThan => CComparisonOperator::LessEqual,
        CComparisonOperator::GreaterEqual => CComparisonOperator::LessThan,
    };
    let known = decide_with_facts(assumptions, &facts, &condition).or_else(|| {
        let opposite = wide_integer_comparison_condition(complement, &left, &right)?;
        decide_with_facts(assumptions, &facts, &opposite).map(|truth| !truth)
    });
    if let Some(truth) = known {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(u32::from(truth))),
            facts,
            obligations,
        }];
    }
    condition_as_c_int32_paths(condition, facts, obligations, assumptions)
}

/// One condition representation for native execution and pure-spec transport.
pub(in crate::kernel) fn wide_integer_comparison_condition(
    operator: CComparisonOperator,
    left: &CValue,
    right: &CValue,
) -> Option<ConditionTerm> {
    let (ty, left, right) = match (left, right) {
        (CValue::Int128(a), CValue::Int128(b)) => (MachineIntegerType::Int128, a, b),
        (CValue::UInt128(a), CValue::UInt128(b)) => (MachineIntegerType::UInt128, a, b),
        _ => return None,
    };
    let left = IntegerTerm::from_machine(ty, left.clone())?;
    let right = IntegerTerm::from_machine(ty, right.clone())?;
    Some(match operator {
        CComparisonOperator::Equal => ConditionTerm::integer_equal(left, right),
        CComparisonOperator::NotEqual => ConditionTerm::integer_not_equal(left, right),
        CComparisonOperator::LessThan => ConditionTerm::integer_less_than(left, right),
        CComparisonOperator::LessEqual => ConditionTerm::integer_less_equal(left, right),
        CComparisonOperator::GreaterThan => ConditionTerm::integer_greater_than(left, right),
        CComparisonOperator::GreaterEqual => ConditionTerm::integer_greater_equal(left, right),
    })
}

/// Integer equality and inequality have separate representation nodes. Both
/// spellings denote the same native guard; query each by exact indexed lookup.
fn decide_wide_integer_equality(
    assumptions: &PureFactContext,
    facts: &(impl ExecutionFactSource + ?Sized),
    left: IntegerTerm,
    right: IntegerTerm,
) -> Option<bool> {
    decide_with_facts(
        assumptions,
        facts,
        &ConditionTerm::integer_equal(left.clone(), right.clone()),
    )
    .or_else(|| {
        decide_with_facts(
            assumptions,
            facts,
            &ConditionTerm::integer_not_equal(left, right),
        )
        .map(|value| !value)
    })
}

/// Division on already-resolved wide formats. Promotions belong to the
/// caller; the native guards precede construction of the mathematical term.
fn apply_c_int128_division_like(
    left: CValue,
    right: CValue,
    mut facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    remainder: bool,
) -> Vec<CExpressionPath> {
    let (destination, left, right) = match (left, right) {
        (CValue::Int128(a), CValue::Int128(b)) => (MachineIntegerType::Int128, a, b),
        (CValue::UInt128(a), CValue::UInt128(b)) => (MachineIntegerType::UInt128, a, b),
        _ => return vec![c_type_mismatch_expression_path(facts, obligations)],
    };
    let (Some(left), Some(right)) = (
        IntegerTerm::from_machine(destination, left),
        IntegerTerm::from_machine(destination, right),
    ) else {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    };
    let mut paths = Vec::new();
    let zero = ConditionTerm::integer_equal(right.clone(), IntegerTerm::constant_i64(0));
    match decide_wide_integer_equality(
        assumptions,
        &facts,
        right.clone(),
        IntegerTerm::constant_i64(0),
    ) {
        Some(true) => {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero),
                facts,
                obligations,
            }];
        }
        Some(false) => {}
        None => {
            let mut bad = facts.clone();
            add_condition_path_fact(&mut bad, assumptions, zero.clone(), true)
                .expect("unknown divisor has a zero path");
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::DivisionByZero),
                facts: bad,
                obligations: obligations.clone(),
            });
            add_condition_path_fact(&mut facts, assumptions, zero, false)
                .expect("unknown divisor has a nonzero path");
        }
    }
    if destination == MachineIntegerType::Int128 {
        let min =
            ConditionTerm::integer_equal(left.clone(), IntegerTerm::constant(i128::MIN.into()));
        let minus_one = ConditionTerm::integer_equal(right.clone(), IntegerTerm::constant_i64(-1));
        let a = decide_wide_integer_equality(
            assumptions,
            &facts,
            left.clone(),
            IntegerTerm::constant(i128::MIN.into()),
        );
        let b = decide_wide_integer_equality(
            assumptions,
            &facts,
            right.clone(),
            IntegerTerm::constant_i64(-1),
        );
        let (safe, overflow, known) = match (a, b) {
            (Some(false), _) | (_, Some(false)) => (None, None, Some(false)),
            (Some(true), Some(true)) => (None, None, Some(true)),
            (Some(true), None) => (
                Some(Proposition::ConditionIs(minus_one.clone(), false)),
                Some(Proposition::ConditionIs(minus_one, true)),
                None,
            ),
            (None, Some(true)) => (
                Some(Proposition::ConditionIs(min.clone(), false)),
                Some(Proposition::ConditionIs(min, true)),
                None,
            ),
            (None, None) => (
                Some(Proposition::Or(
                    Box::new(Proposition::ConditionIs(min.clone(), false)),
                    Box::new(Proposition::ConditionIs(minus_one.clone(), false)),
                )),
                Some(Proposition::And(
                    Box::new(Proposition::ConditionIs(min, true)),
                    Box::new(Proposition::ConditionIs(minus_one, true)),
                )),
                None,
            ),
        };
        let known = known.or_else(|| {
            let safe = safe.as_ref()?;
            // Keep the complete contract guard available even when a known
            // operand simplified the path guard to a single condition.
            let equality_safe = Proposition::Or(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::integer_equal(
                        left.clone(),
                        IntegerTerm::constant(i128::MIN.into()),
                    ),
                    false,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::integer_equal(right.clone(), IntegerTerm::constant_i64(-1)),
                    false,
                )),
            );
            let inequality_safe = Proposition::Or(
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::integer_not_equal(
                        left.clone(),
                        IntegerTerm::constant(i128::MIN.into()),
                    ),
                    true,
                )),
                Box::new(Proposition::ConditionIs(
                    ConditionTerm::integer_not_equal(right.clone(), IntegerTerm::constant_i64(-1)),
                    true,
                )),
            );
            if assumptions.proves_exact(safe)
                || assumptions.proves_exact(&equality_safe)
                || assumptions.proves_exact(&inequality_safe)
                || facts.iter().any(|f| {
                    f.proposition() == safe
                        || f.proposition() == &equality_safe
                        || f.proposition() == &inequality_safe
                })
            {
                Some(false)
            } else {
                None
            }
        });
        match known {
            Some(true) => {
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts,
                    obligations,
                });
                return paths;
            }
            Some(false) => {}
            None => {
                let mut bad = facts.clone();
                add_path_fact(&mut bad, assumptions, overflow.unwrap())
                    .expect("unknown signed overflow has an overflow path");
                paths.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::SignedOverflow,
                    ),
                    facts: bad,
                    obligations: obligations.clone(),
                });
                add_path_fact(&mut facts, assumptions, safe.unwrap())
                    .expect("unknown signed overflow has a normal path");
            }
        }
    }
    let result = if remainder {
        IntegerTerm::truncating_remainder(left, right)
    } else {
        IntegerTerm::truncating_quotient(left, right)
    };
    // Typed operands bound the quotient/remainder. Nonzero excludes division
    // failure; excluding MIN/-1 is sufficient for either signed result to fit.
    let term = if let Some(constant) = result.as_const() {
        destination
            .constant_term(
                MachineIntegerConstant::from_integer(destination.format(), constant)
                    .expect("guarded native quotient/remainder fits its format"),
            )
            .expect("exact wide format")
    } else {
        Bitvector32Term::IntegerToMachine {
            value: result.clone().into(),
            destination,
        }
    };
    let observed = IntegerTerm::from_machine(destination, term.clone()).expect("typed wide result");
    let definition = ConditionTerm::integer_equal(observed, result);
    if definition != ConditionTerm::Constant(true) {
        facts.push(ExecutionPureFact::certified(Proposition::ConditionIs(
            definition, true,
        )));
    }
    paths.push(CExpressionPath {
        outcome: CExpressionOutcome::Value(match destination {
            MachineIntegerType::Int128 => CValue::Int128(term),
            MachineIntegerType::UInt128 => CValue::UInt128(term),
            _ => unreachable!(),
        }),
        facts,
        obligations,
    });
    paths
}

pub(in crate::kernel) fn apply_c_divide(
    left: CValue,
    right: CValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let left = numeric_pointer_integer_value(left);
    let right = numeric_pointer_integer_value(right);
    if matches!(left, CValue::Int128(_) | CValue::UInt128(_))
        || matches!(right, CValue::Int128(_) | CValue::UInt128(_))
    {
        return apply_c_int128_division_like(left, right, facts, obligations, assumptions, false);
    }

    if let Some((left, right, target_type, obligations)) =
        coerce_c_float_operands(&left, &right, &obligations, assumptions)
    {
        return apply_c_float_binary(
            left,
            right,
            target_type,
            CFloatBinaryOperator::Divide,
            facts,
            obligations,
        );
    }
    let (left, right) = promote_c_bool_scalar_operands(left, right);
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return WideArithmetic::Divide.apply(left, right, width, facts, obligations, assumptions);
    }
    let scalar_left = matches!(left, crate::kernel::integer32_c_value!(_));
    let scalar_right = matches!(right, crate::kernel::integer32_c_value!(_));
    if !scalar_left || !scalar_right {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    }
    let facts = facts;
    let Some((left, right, width)) = apply_c_scalar_terms(left, right) else {
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
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let left = numeric_pointer_integer_value(left);
    let right = numeric_pointer_integer_value(right);
    if matches!(left, CValue::Int128(_) | CValue::UInt128(_))
        || matches!(right, CValue::Int128(_) | CValue::UInt128(_))
    {
        return apply_c_int128_division_like(left, right, facts, obligations, assumptions, true);
    }

    let (left, right) = promote_c_bool_scalar_operands(left, right);
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return WideArithmetic::Remainder.apply(
            left,
            right,
            width,
            facts,
            obligations,
            assumptions,
        );
    }
    let scalar_left = matches!(left, crate::kernel::integer32_c_value!(_));
    let scalar_right = matches!(right, crate::kernel::integer32_c_value!(_));
    if !scalar_left || !scalar_right {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    }
    let facts = facts;
    let Some((left, right, width)) = apply_c_scalar_terms(left, right) else {
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
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    _assumptions: &PureFactContext,
    operation: CBitwiseOperation,
) -> Vec<CExpressionPath> {
    if matches!(&left, CValue::PointerInteger(_)) || matches!(&right, CValue::PointerInteger(_)) {
        let mut origin = single_pointer_integer_origin(&left, &right);
        if matches!(operation, CBitwiseOperation::And) {
            let mask = match (&left, &right) {
                (CValue::PointerInteger(_), other) | (other, CValue::PointerInteger(_)) => {
                    promote_c_uint64_path_value(numeric_pointer_integer_value(other.clone()))
                        .and_then(|bits| bits.bitvector64_as_const())
                }
                _ => None,
            };
            // Reading low tag bits destroys the address representation.
            // Only a known high-bit-preserving mask retains this origin.
            if mask.is_none_or(|mask| mask & (1u64 << 63) == 0) {
                origin = None;
            }
        }
        let paths = apply_c_bitwise_binary(
            numeric_pointer_integer_value(left),
            numeric_pointer_integer_value(right),
            facts,
            obligations,
            _assumptions,
            operation,
        );
        return retain_pointer_integer_origin(paths, origin);
    }
    let (left, right) = promote_c_bool_scalar_operands(left, right);
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        let facts = facts;
        let Some((left, right, _)) = apply_c_scalar_terms(left, right) else {
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
    let scalar_left = matches!(left, crate::kernel::integer32_c_value!(_));
    let scalar_right = matches!(right, crate::kernel::integer32_c_value!(_));
    if !scalar_left || !scalar_right {
        return vec![c_type_mismatch_expression_path(facts, obligations)];
    }
    let facts = facts;
    let Some((left, right, width)) = apply_c_scalar_terms(left, right) else {
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
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
) -> Vec<CExpressionPath> {
    let value = numeric_pointer_integer_value(value);
    match value {
        CValue::Bool(value) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(Bitvector32Term::bitwise_not(value))),
            facts,
            obligations,
        }],
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
        CValue::Int8(value) => {
            let facts = facts;
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::bitwise_not(value))),
                facts,
                obligations,
            }]
        }
        CValue::Int16(value) => {
            let facts = facts;
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::bitwise_not(value))),
                facts,
                obligations,
            }]
        }
        CValue::UInt8(value) => {
            let facts = facts;
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::bitwise_not(value))),
                facts,
                obligations,
            }]
        }
        CValue::UInt16(value) => {
            let facts = facts;
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

fn pointer_value_step_width(pointer: &CPointerValue, expression_width: Option<u32>) -> Option<u32> {
    // GNU C treats void-pointer arithmetic as byte arithmetic. Other
    // pointers still require the expression's existing pointee evidence.
    if pointer.c_type() == CType::VoidPointer {
        Some(1)
    } else {
        expression_width
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

fn apply_same_object_pointer_operation(
    state: &CState,
    left: Pointer,
    right: Pointer,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    apply: impl FnOnce(Pointer, Pointer, ExecutionFacts, Vec<ProofObligation>) -> Vec<CExpressionPath>,
) -> Vec<CExpressionPath> {
    let left_is_null = pointer_object_is_null_condition(&left);
    apply_pointer_object_nonnull_guard(
        state,
        &left.clone(),
        left_is_null,
        facts,
        obligations,
        assumptions,
        move |facts, obligations| {
            let right_is_null = pointer_object_is_null_condition(&right);
            apply_pointer_object_nonnull_guard(
                state,
                &right.clone(),
                right_is_null,
                facts,
                obligations,
                assumptions,
                move |facts, obligations| {
                    let same_identity = pointer_object_identity_condition(&left, &right);
                    apply_pointer_provenance_guard(
                        same_identity,
                        true,
                        facts,
                        obligations,
                        assumptions,
                        move |facts, obligations| apply(left, right, facts, obligations),
                    )
                },
            )
        },
    )
}

fn apply_pointer_object_nonnull_guard(
    state: &CState,
    pointer: &Pointer,
    is_null: ConditionTerm,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    apply: impl FnOnce(ExecutionFacts, Vec<ProofObligation>) -> Vec<CExpressionPath>,
) -> Vec<CExpressionPath> {
    if pointer_has_object_provenance_evidence(state, pointer, assumptions, &facts) {
        let mut facts = facts;
        if add_condition_path_fact(&mut facts, assumptions, is_null, false).is_none() {
            return Vec::new();
        }
        return apply(facts, obligations);
    }
    apply_pointer_provenance_guard(is_null, false, facts, obligations, assumptions, apply)
}

fn pointer_has_object_provenance_evidence(
    state: &CState,
    pointer: &Pointer,
    assumptions: &PureFactContext,
    facts: &(impl ExecutionFactSource + ?Sized),
) -> bool {
    let decide =
        |condition: ConditionTerm| decide_with_facts(assumptions, facts, &condition) == Some(true);
    let establishes_object = |fact: &CResourceFact| {
        let Some(range) = fact.memory_range() else {
            return false;
        };
        (!fact.is_own() || fact.has_proven_positive_quantity(assumptions))
            && decide(pointer_object_identity_condition(pointer, range.base()))
            && decide(match range.wide_bounds() {
                Some((start, end)) => ConditionTerm::uint64_less_than(start.clone(), end.clone()),
                None => ConditionTerm::signed_less_than(range.start().clone(), range.end().clone()),
            })
    };
    state
        .resources()
        .memory_object_evidence(pointer, assumptions)
        .is_some_and(establishes_object)
        || assumptions
            .composition_object_resources
            .memory_object_evidence(pointer, assumptions)
            .is_some_and(establishes_object)
        || assumptions
            .memory_loadable_candidates_for_object(pointer)
            .any(|proposition| {
                let Proposition::CMemoryLoadable {
                    memory,
                    base,
                    bytes,
                    wide: false,
                } = proposition
                else {
                    unreachable!("viewability object index contains only viewability facts")
                };
                crate::kernel::reasoning::memory_range_still_available(
                    memory,
                    state.memory(),
                    base,
                    assumptions,
                ) && decide(ConditionTerm::signed_greater_than(
                    bytes.clone(),
                    Bitvector32Term::Constant(0),
                ))
            })
}

fn apply_pointer_provenance_guard(
    condition: ConditionTerm,
    expected: bool,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    apply: impl FnOnce(ExecutionFacts, Vec<ProofObligation>) -> Vec<CExpressionPath>,
) -> Vec<CExpressionPath> {
    match decide_with_facts(assumptions, &facts, &condition) {
        Some(value) if value == expected => apply(facts, obligations),
        Some(_) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic),
            facts,
            obligations,
        }],
        None => {
            let mut valid_facts = facts.clone();
            add_condition_path_fact(&mut valid_facts, assumptions, condition.clone(), expected)
                .expect("valid pointer provenance guard should be consistent");
            let mut paths = apply(valid_facts, obligations.clone());

            let mut invalid_facts = facts;
            add_condition_path_fact(&mut invalid_facts, assumptions, condition, !expected)
                .expect("invalid pointer provenance guard should be consistent");
            paths.push(CExpressionPath {
                outcome: CExpressionOutcome::UndefinedBehavior(
                    CUndefinedBehavior::PointerArithmetic,
                ),
                facts: invalid_facts,
                obligations,
            });
            paths
        }
    }
}

pub(in crate::kernel) fn pointer_object_identity_condition(
    left: &Pointer,
    right: &Pointer,
) -> ConditionTerm {
    ConditionTerm::pointer_equal(left.object_identity(), right.object_identity())
}

pub(in crate::kernel) fn pointer_object_is_null_condition(pointer: &Pointer) -> ConditionTerm {
    pointer_is_null_condition(pointer.object_base())
}

pub(in crate::kernel) fn pointer_same_object_proposition(
    left: &Pointer,
    right: &Pointer,
) -> Proposition {
    Proposition::And(
        Box::new(Proposition::ConditionIs(
            pointer_object_is_null_condition(left),
            false,
        )),
        Box::new(Proposition::And(
            Box::new(Proposition::ConditionIs(
                pointer_object_is_null_condition(right),
                false,
            )),
            Box::new(Proposition::ConditionIs(
                pointer_object_identity_condition(left, right),
                true,
            )),
        )),
    )
}

/// The two owned members of the held resources that hold the compared
/// addresses, as one composition: distinct owned members are separate, so
/// the addresses inside them differ. Each side is looked up under its own
/// spelling and the spellings exact equalities give it, through the base
/// index, as a store's member is; nothing is opened and nothing else is
/// visited. The composition is assumed for the comparison and kept as a path
/// fact, as `functions::store_opened_instance_composition` keeps a store's,
/// so the pointer disequality rule reads the same two members wherever the
/// comparison is re-asked. `None` when either side lies in no owned member,
/// or both lie in one. String literal storage is not a holder: two
/// occurrences with identical bytes may be one object, so their ranges are
/// deliberately never separated.
fn compared_pointer_holders_composition(
    state: &CState,
    left: &Pointer,
    right: &Pointer,
    assumptions: &PureFactContext,
) -> Option<ResourceContext> {
    let resources = state.resources();
    let holder = |pointer: &Pointer| {
        assumptions
            .pointer_equality_component(pointer)
            .into_iter()
            .find_map(|(spelling, _)| {
                crate::instrumentation::record_deterministic_work(1);
                assumptions
                    .owned_member_holding_access(resources, &spelling, 1)
                    .filter(|range| {
                        !matches!(range.base().block, PointerBlock::StringLiteral { .. })
                    })
                    .cloned()
            })
    };
    let left_member = holder(left)?;
    let right_member = holder(right)?;
    if left_member == right_member {
        return None;
    }
    ResourceContext::new()
        .try_compose_with_facts_delaying_normalization(
            [left_member, right_member]
                .into_iter()
                .map(CResourceFact::own_memory),
            assumptions,
        )
        .ok()
}

fn apply_c_comparison(
    state: &CState,
    operator: CComparisonOperator,
    left: CValue,
    right: CValue,
    left_step_width: Option<u32>,
    right_step_width: Option<u32>,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let left = numeric_pointer_integer_value(left);
    let right = numeric_pointer_integer_value(right);
    if matches!(left, CValue::Int128(_) | CValue::UInt128(_))
        || matches!(right, CValue::Int128(_) | CValue::UInt128(_))
    {
        return apply_c_int128_comparison(operator, left, right, facts, obligations, assumptions);
    }

    if let Some((left, right, target_type, obligations)) =
        coerce_c_float_operands(&left, &right, &obligations, assumptions)
    {
        return apply_c_float_comparison(
            left,
            right,
            target_type,
            operator,
            facts,
            obligations,
            assumptions,
        );
    }
    let (left, right) = promote_c_bool_scalar_operands(left, right);
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
            let domain_context = assumptions_with_path_context(assumptions, &facts, &obligations);
            let check = super::pointer_domains::checked_pointer_ordering(
                state,
                &left,
                &right,
                byte_width,
                pointer_domain_view(&left),
                true,
                &domain_context,
            );
            let Some(mut domain_refusals) = pointer_arithmetic_domain_refusal_paths(
                check,
                &facts,
                &obligations,
                assumptions,
                &CUndefinedBehavior::PointerArithmetic,
            ) else {
                return vec![CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::PointerArithmetic,
                    ),
                    facts,
                    obligations,
                }];
            };
            domain_refusals.extend(apply_same_object_pointer_operation(
                state,
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
            ));
            domain_refusals
        }
        (
            left @ (crate::kernel::integer32_c_value!(_)),
            right @ (crate::kernel::integer32_c_value!(_)),
        ) if scalar_uses_uint32(&left, &right) => {
            let facts = facts;
            let Some(left) = promote_c_uint32_path_value(left) else {
                return Vec::new();
            };
            let Some(right) = promote_c_uint32_path_value(right) else {
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
            left @ (crate::kernel::int_promoted_c_value!(_)),
            right @ (crate::kernel::int_promoted_c_value!(_)),
        ) => {
            let facts = facts;
            let Some(left) = promote_c_int32_path_value(left) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right) else {
                return Vec::new();
            };
            condition_as_c_int32_paths(
                pointer_order_condition(left, right, operator),
                facts,
                obligations,
                assumptions,
            )
        }
        (CValue::Float32(left), CValue::Float32(right)) => condition_as_c_int32_paths(
            ConditionTerm::float32_compare(left, right, operator),
            facts,
            obligations,
            assumptions,
        ),
        (CValue::Float64(left), CValue::Float64(right)) => condition_as_c_int32_paths(
            ConditionTerm::float64_compare(left, right, operator),
            facts,
            obligations,
            assumptions,
        ),
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

pub(in crate::kernel) fn apply_c_subtract(
    state: &CState,
    left: CValue,
    right: CValue,
    left_step_width: Option<u32>,
    right_step_width: Option<u32>,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    if matches!(&left, CValue::PointerInteger(_)) || matches!(&right, CValue::PointerInteger(_)) {
        let origin = match (&left, &right) {
            (CValue::PointerInteger(origin), right)
                if !matches!(right, CValue::PointerInteger(_)) =>
            {
                Some(origin.clone())
            }
            _ => None,
        };
        let paths = apply_c_subtract(
            state,
            numeric_pointer_integer_value(left),
            numeric_pointer_integer_value(right),
            left_step_width,
            right_step_width,
            facts,
            obligations,
            assumptions,
        );
        return retain_pointer_integer_origin(paths, origin);
    }
    if let Some((left, right, target_type, obligations)) =
        coerce_c_float_operands(&left, &right, &obligations, assumptions)
    {
        return apply_c_float_binary(
            left,
            right,
            target_type,
            CFloatBinaryOperator::Subtract,
            facts,
            obligations,
        );
    }
    let (left, right) = promote_c_bool_scalar_operands(left, right);
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        return WideArithmetic::Subtract.apply(left, right, width, facts, obligations, assumptions);
    }
    match (left, right) {
        (
            left @ (crate::kernel::int_promoted_c_value!(_)),
            right @ (crate::kernel::int_promoted_c_value!(_)),
        ) => {
            let facts = facts;
            let Some(left) = promote_c_int32_path_value(left) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right) else {
                return Vec::new();
            };
            apply_c_int32_subtract(left, right, facts, obligations, assumptions)
        }
        (
            left @ (crate::kernel::integer32_c_value!(_)),
            right @ (crate::kernel::integer32_c_value!(_)),
        ) if scalar_uses_uint32(&left, &right) => {
            let facts = facts;
            let Some(left) = promote_c_uint32_path_value(left) else {
                return Vec::new();
            };
            let Some(right) = promote_c_uint32_path_value(right) else {
                return Vec::new();
            };
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(uint32(Bitvector32Term::subtract(left, right))),
                facts,
                obligations,
            }]
        }
        (CValue::Pointer(pointer), right @ (crate::kernel::int_promoted_c_value!(_))) => {
            let facts = facts;
            let Some(right) = promote_c_int32_path_value(right) else {
                return Vec::new();
            };
            let Some(byte_width) = pointer_operation_step_width(
                pointer_value_step_width(&pointer, left_step_width),
                None,
            ) else {
                return vec![c_type_mismatch_expression_path(facts, obligations)];
            };
            pointer_offset_by_elements_paths(
                state,
                pointer,
                Bitvector32Term::subtract(Bitvector32Term::Constant(0), right),
                byte_width,
                false,
                false,
                facts,
                obligations,
                assumptions,
            )
        }
        (
            CValue::Pointer(pointer),
            right @ (CValue::UInt32(_) | CValue::Int64(_) | CValue::UInt64(_)),
        ) => {
            let Some(byte_width) = pointer_operation_step_width(
                pointer_value_step_width(&pointer, left_step_width),
                None,
            ) else {
                return vec![c_type_mismatch_expression_path(facts, obligations)];
            };
            let (offset, unsigned) = match right {
                CValue::UInt32(value) => (Bitvector32Term::uint64_from_32(value), true),
                CValue::Int64(value) => (value, false),
                CValue::UInt64(value) => (value, true),
                _ => unreachable!(),
            };
            // Negate the mathematical displacement, not a wrapping unsigned
            // C value. Guard the conversion/negation before reusing addition's
            // pointer formation and object-bound checks.
            let guard = if unsigned {
                PointerFormationGuard {
                    condition: ConditionTerm::uint64_less_equal(
                        offset.clone(),
                        Bitvector32Term::UInt64Constant(i64::MAX as u64),
                    ),
                    value: true,
                }
            } else {
                PointerFormationGuard {
                    condition: ConditionTerm::int64_signed_subtract_overflows(
                        Bitvector32Term::Int64Constant(0),
                        offset.clone(),
                    ),
                    value: false,
                }
            };
            let guarded = apply_pointer_formation_guards(
                pointer,
                vec![guard],
                facts,
                obligations,
                assumptions,
            );
            let offset = if unsigned {
                Bitvector32Term::int64_from_uint64_bits(offset)
            } else {
                offset
            };
            let negated =
                Bitvector32Term::int64_subtract(Bitvector32Term::Int64Constant(0), offset);
            guarded
                .into_iter()
                .flat_map(|path| {
                    let CExpressionOutcome::Value(CValue::Pointer(pointer)) = path.outcome else {
                        return vec![path];
                    };
                    // Keep the existing zero-displacement treatment for null and
                    // otherwise unbounded pointers independent of integer width.
                    let (negated, wide) = if negated.int64_as_const() == Some(0) {
                        (Bitvector32Term::Constant(0), false)
                    } else {
                        (negated.clone(), true)
                    };
                    pointer_offset_by_elements_paths(
                        state,
                        pointer,
                        negated,
                        byte_width,
                        false,
                        wide,
                        path.facts,
                        path.obligations,
                        assumptions,
                    )
                })
                .collect()
        }
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            if left.c_type() != right.c_type() {
                return vec![c_type_mismatch_expression_path(facts, obligations)];
            }
            let Some(byte_width) = pointer_operation_step_width(left_step_width, right_step_width)
            else {
                return vec![c_type_mismatch_expression_path(facts, obligations)];
            };
            let check = super::pointer_domains::checked_pointer_difference(
                state,
                &left,
                &right,
                byte_width,
                pointer_domain_view(&left),
                assumptions,
            );
            let Some(mut domain_refusals) = pointer_arithmetic_domain_refusal_paths(
                check,
                &facts,
                &obligations,
                assumptions,
                &CUndefinedBehavior::PointerArithmetic,
            ) else {
                return vec![CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(
                        CUndefinedBehavior::PointerArithmetic,
                    ),
                    facts,
                    obligations,
                }];
            };
            domain_refusals.extend(apply_same_object_pointer_operation(
                state,
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
            ));
            domain_refusals
        }
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

#[derive(Clone)]
struct PointerFormationGuard {
    condition: ConditionTerm,
    value: bool,
}

/// The shared evaluator's character access mode selects the retained object's
/// representation extent. It does not issue a new object or widen that extent.
/// Native frontends remain responsible for admitting this source operation.
pub(super) fn pointer_domain_view(
    pointer: &CPointerValue,
) -> super::pointer_domains::PointerDomainView {
    if matches!(
        pointer.c_type().pointee_type(),
        Some(CType::Int8 | CType::UInt8)
    ) {
        super::pointer_domains::PointerDomainView::ObjectRepresentationBytes
    } else {
        super::pointer_domains::PointerDomainView::Typed
    }
}

/// Keep domain obligations independent of memory permission. Undecided guards
/// retain their refused paths, so successful verification must discharge them.
pub(super) fn pointer_domain_refusal_paths(
    check: Result<
        super::pointer_domains::PointerDomainCheck,
        super::pointer_domains::PointerDomainRefusal,
    >,
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
    assumptions: &PureFactContext,
    refusal: &CUndefinedBehavior,
) -> Option<Vec<CExpressionPath>> {
    let guards = match check.ok()? {
        super::pointer_domains::PointerDomainCheck::Legacy => return Some(Vec::new()),
        super::pointer_domains::PointerDomainCheck::Checked(conditions) => conditions
            .into_iter()
            .map(|condition| PointerFormationGuard {
                condition,
                value: true,
            })
            .collect(),
    };
    owed_guard_paths(guards, facts, obligations, assumptions, refusal)
}

// Specification lowering observes address expressions without executing
// native arithmetic. It must retain the carrier, but cannot issue a domain
// or use address formation as evidence of a valid native access.
fn pointer_arithmetic_domain_refusal_paths(
    check: Result<
        super::pointer_domains::PointerDomainCheck,
        super::pointer_domains::PointerDomainRefusal,
    >,
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
    assumptions: &PureFactContext,
    refusal: &CUndefinedBehavior,
) -> Option<Vec<CExpressionPath>> {
    if assumptions.should_observe_pointer_addresses() {
        Some(Vec::new())
    } else {
        pointer_domain_refusal_paths(check, facts, obligations, assumptions, refusal)
    }
}

pub(super) fn pointer_index_term(
    value: CValue,
    facts: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> Option<(Bitvector32Term, bool, bool)> {
    match value {
        CValue::PointerInteger(value) => {
            pointer_index_term(value.numeric_value(), facts, assumptions)
        }
        value @ (CValue::Bool(_)
        | CValue::Int8(_)
        | CValue::Int16(_)
        | CValue::Int32(_)
        | CValue::UInt8(_)
        | CValue::UInt16(_)) => Some((promote_c_int32_path_value(value)?, false, false)),
        // An unsigned word whose sign bit the path has cleared (`x < 4u`
        // leaves `0 <= x` beside it) names the same element index read as
        // signed: zero- and sign-extension agree on it. Indexing by the
        // signed word gives the address the shape a signed index has, so
        // the formation guard and the element and footprint rules read its
        // range from the same order facts. Otherwise the index is the exact
        // zero-extended word.
        CValue::UInt32(value)
            if decide_with_facts(
                assumptions,
                facts,
                &ConditionTerm::signed_less_equal(Bitvector32Term::Constant(0), value.clone()),
            ) == Some(true) =>
        {
            Some((value, false, false))
        }
        CValue::UInt32(value) => Some((Bitvector32Term::uint64_from_32(value), true, true)),
        CValue::Int64(value) => Some((value, false, true)),
        // A 64-bit index keeps its own form, so a body's access and a
        // contract's place name one address in one spelling.
        CValue::UInt64(value) => Some((value, true, true)),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

fn pointer_offset_by_elements_paths(
    state: &CState,
    pointer: CPointerValue,
    offset: Bitvector32Term,
    byte_width: u32,
    unsigned: bool,
    wide: bool,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let pointer_value = pointer;
    let pointer = pointer_value.pointer().clone();

    // C11 6.5.6p8 defines additive pointer arithmetic only for a pointer that
    // designates an element of an array object or one past its end. A null
    // pointer designates no object, so the sum has no value to compare or
    // dereference; without this the displaced pointer carried a nonzero
    // offset and compared unequal to null, which decided a branch C leaves
    // undefined. Displacing by zero is left alone: it is the shape real code
    // writes, and C23 defines it.
    if pointer.is_in_null_block() && offset != Bitvector32Term::Constant(0) {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic),
            facts,
            obligations,
        }];
    }

    let result = match byte_stride_index(&offset, byte_width, unsigned, wide, &facts, assumptions) {
        Some((index, stride)) => pointer.offset_by_typed_elements(index, stride, false, false),
        None => pointer.offset_by_typed_elements(offset.clone(), byte_width, unsigned, wide),
    };
    let displaces = offset != Bitvector32Term::Constant(0);
    let mut guards = Vec::new();
    let domain_check = super::pointer_domains::checked_pointer_formation(
        state,
        &pointer_value,
        &result,
        byte_width,
        pointer_domain_view(&pointer_value),
        assumptions,
    );
    let Some(mut owed) = pointer_arithmetic_domain_refusal_paths(
        domain_check,
        &facts,
        &obligations,
        assumptions,
        &CUndefinedBehavior::PointerArithmetic,
    ) else {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic),
            facts,
            obligations,
        }];
    };

    // Pointer offsets are exact i64 terms, but the source index is a signed
    // int32. Once a pointer has a known element index, the next addition must
    // stay in that signed domain when its next operand is also int32. A
    // wide operand needs a wide addition guard instead. This catches the cumulative case
    // `data + INT_MAX + 1`, even though each individual source operand is a
    // valid int32.
    // An unsigned 64-bit operand decided to be at most `INT_MAX` cannot
    // overflow the sum with a signed 32-bit index, so it owes no guard:
    // the guard below reads the operand as signed, which order facts over
    // an unsigned value do not decide.
    let small_unsigned = wide && unsigned && assumptions.uint64_index_fits_int32(&offset);
    if let Some(index) = pointer_index_from_offset(&pointer, byte_width)
        && index != Bitvector32Term::Constant(0)
        && offset != Bitvector32Term::Constant(0)
        && !small_unsigned
    {
        guards.push(PointerFormationGuard {
            condition: if wide {
                ConditionTerm::int64_signed_add_overflows(
                    Bitvector32Term::int64_from_32(index),
                    offset,
                )
            } else {
                ConditionTerm::signed_add_overflows(index, offset)
            },
            value: false,
        });
    }

    // A resource-backed read may legitimately refer to storage that has not
    // been materialized in the byte map yet. Let that explicit memory range
    // extend the concrete materialization bound; it is still only consulted
    // when the result (including a range endpoint) is provably in the range.
    let membership =
        held_range_membership(state, assumptions, &facts, &pointer, &result, byte_width);
    if !matches!(membership, HeldRangeMembership::Inside) {
        let Some(bounds) = pointer_block_bounds(state, &result, byte_width) else {
            return Vec::new();
        };
        guards.extend(bounds);
        // C11 6.5.6p8 defines the sum only for a result inside the array
        // object or one past its end. When the state does not record the
        // block's extent (every pointer parameter, and every symbolic or
        // loaded pointer), the ranges it holds in that block are the only
        // extent it knows, so the result must lie in one of them, one-past
        // end included. A range decided to exclude the result drops out: when
        // the facts exclude it from every range the formation is refused, and
        // when exactly one range is left undecided its bounds are owed, as
        // refused paths carrying their negation. The normal path does not
        // assume them: a specification term `p + i` is evaluated through this
        // same operation and keeps the facts it had, and a proof that
        // verified before the bound existed sees the same facts. A block
        // with no range that resolves the result owes nothing here; the
        // access through the pointer is what is refused then. Displacing by
        // zero is left alone, as for null.
        if displaces && state.memory().block_size(&result.block).is_none() {
            match membership {
                HeldRangeMembership::Inside => {
                    unreachable!("a contained pointer owes no formation guard")
                }
                HeldRangeMembership::Undecided(range_guards) => {
                    let Some(refused) = owed_guard_paths(
                        range_guards,
                        &facts,
                        &obligations,
                        assumptions,
                        &CUndefinedBehavior::PointerArithmetic,
                    ) else {
                        return vec![CExpressionPath {
                            outcome: CExpressionOutcome::UndefinedBehavior(
                                CUndefinedBehavior::PointerArithmetic,
                            ),
                            facts,
                            obligations,
                        }];
                    };
                    owed.extend(refused);
                }
                HeldRangeMembership::Outside => {
                    return vec![CExpressionPath {
                        outcome: CExpressionOutcome::UndefinedBehavior(
                            CUndefinedBehavior::PointerArithmetic,
                        ),
                        facts,
                        obligations,
                    }];
                }
                HeldRangeMembership::Unknown => {}
            }
        }
    }

    owed.extend(apply_pointer_formation_guards(
        pointer_value.with_pointer(result),
        guards,
        facts,
        obligations,
        assumptions,
    ));
    owed
}

/// The element index and stride of a byte displacement `index * stride`.
///
/// The C frontend addresses an element of a struct array through the bytes
/// of the array: `items[i]` is the byte pointer `items + i * sizeof(item)`,
/// with the multiplication evaluated as a C `int`. That spelling is a byte
/// offset whose index is a product, and the element-index rules that bound a
/// scalar store `values[i]` by `0 <= i < n` cannot read it. Forming the
/// address as `i` scaled by the stride gives it the scalar shape, with the
/// struct size as the element width, so the same membership rules apply.
///
/// The two spellings name one address only where the product did not wrap:
/// the scaled form sign-extends `i` before scaling, the product form
/// sign-extends the wrapped product. The multiplication that produced the
/// product refused the overflowing path, so its result path carries that
/// exclusion, and the rewrite is taken only when the path facts decide it.
fn byte_stride_index(
    offset: &Bitvector32Term,
    byte_width: u32,
    unsigned: bool,
    wide: bool,
    facts: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> Option<(Bitvector32Term, u32)> {
    if byte_width != 1 || unsigned || wide {
        return None;
    }
    let Bitvector32Term::Multiply(left, right) = offset else {
        return None;
    };
    let (index, stride) = match (left.as_const(), right.as_const()) {
        (None, Some(stride)) => (left.as_ref(), stride),
        (Some(stride), None) => (right.as_ref(), stride),
        _ => return None,
    };
    // Only a positive stride that is itself an `int32` names an element width.
    if stride < 2 || stride > i32::MAX as u32 {
        return None;
    }
    let overflow = ConditionTerm::signed_multiply_overflows(
        normalize_exact_memory_loads_in_bitvector(left, assumptions),
        normalize_exact_memory_loads_in_bitvector(right, assumptions),
    );
    (decide_with_facts(assumptions, facts, &overflow) == Some(false))
        .then(|| (index.clone(), stride))
}

pub(in crate::kernel) fn pointer_offset_by_bytes_paths(
    state: &CState,
    pointer: CPointerValue,
    bytes: u32,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let pointer_value = pointer;
    let pointer = pointer_value.pointer().clone();
    if pointer.block.is_function() && bytes != 0 {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::IndeterminatePointeeType),
            facts,
            obligations,
        }];
    }
    let result = pointer.offset_by_bytes(bytes);
    let domain_context = assumptions_with_path_context(assumptions, &facts, &obligations);
    let check = super::pointer_domains::checked_pointer_byte_formation(
        state,
        &pointer_value,
        &result,
        &domain_context,
    );
    let Some(mut domain_refusals) = pointer_arithmetic_domain_refusal_paths(
        check,
        &facts,
        &obligations,
        assumptions,
        &CUndefinedBehavior::PointerArithmetic,
    ) else {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::PointerArithmetic),
            facts,
            obligations,
        }];
    };
    let Some(guards) = pointer_block_bounds(state, &result, 1) else {
        return Vec::new();
    };
    domain_refusals.extend(apply_pointer_formation_guards(
        pointer_value.with_pointer(result),
        guards,
        facts,
        obligations,
        assumptions,
    ));
    domain_refusals
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

fn pointer_offset_contains_int64_scaled(offset: &PointerOffsetTerm) -> bool {
    match offset {
        PointerOffsetTerm::Int64Scaled { .. } => true,
        PointerOffsetTerm::Add(left, right) => {
            pointer_offset_contains_int64_scaled(left)
                || pointer_offset_contains_int64_scaled(right)
        }
        PointerOffsetTerm::Constant(_)
        | PointerOffsetTerm::Variable(_)
        | PointerOffsetTerm::Int32Scaled { .. } => false,
    }
}

fn exact_pointer_offset_i64_with_guards(
    offset: &PointerOffsetTerm,
    guards: &mut Vec<PointerFormationGuard>,
) -> Option<Bitvector32Term> {
    match offset {
        PointerOffsetTerm::Constant(value) => Some(Bitvector32Term::Int64Constant(*value)),
        PointerOffsetTerm::Variable(_) => None,
        PointerOffsetTerm::Add(left, right) => {
            let left = exact_pointer_offset_i64_with_guards(left, guards)?;
            let right = exact_pointer_offset_i64_with_guards(right, guards)?;
            guards.push(PointerFormationGuard {
                condition: ConditionTerm::int64_signed_add_overflows(left.clone(), right.clone()),
                value: false,
            });
            Some(Bitvector32Term::int64_add(left, right))
        }
        PointerOffsetTerm::Int32Scaled { value, byte_width } => {
            let left = Bitvector32Term::int64_from_32(value.as_ref().clone());
            let right = Bitvector32Term::Int64Constant(*byte_width);
            guards.push(PointerFormationGuard {
                condition: ConditionTerm::int64_signed_multiply_overflows(
                    left.clone(),
                    right.clone(),
                ),
                value: false,
            });
            Some(Bitvector32Term::int64_multiply(left, right))
        }
        PointerOffsetTerm::Int64Scaled { byte_width: 0, .. } => {
            Some(Bitvector32Term::Int64Constant(0))
        }
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned: false,
        } => {
            let left = value.as_ref().clone();
            let right = Bitvector32Term::Int64Constant(*byte_width);
            guards.push(PointerFormationGuard {
                condition: ConditionTerm::int64_signed_multiply_overflows(
                    left.clone(),
                    right.clone(),
                ),
                value: false,
            });
            Some(Bitvector32Term::int64_multiply(left, right))
        }
        PointerOffsetTerm::Int64Scaled {
            value,
            byte_width,
            unsigned: true,
        } if *byte_width > 0 => {
            let width = u64::try_from(*byte_width).ok()?;
            let maximum_index = (i64::MAX as u64) / width;
            guards.push(PointerFormationGuard {
                condition: ConditionTerm::uint64_less_equal(
                    value.as_ref().clone(),
                    Bitvector32Term::UInt64Constant(maximum_index),
                ),
                value: true,
            });
            let left = value.as_ref().clone();
            let right = Bitvector32Term::Int64Constant(*byte_width);
            guards.push(PointerFormationGuard {
                condition: ConditionTerm::int64_signed_multiply_overflows(
                    left.clone(),
                    right.clone(),
                ),
                value: false,
            });
            Some(Bitvector32Term::int64_multiply(left, right))
        }
        PointerOffsetTerm::Int64Scaled { .. } => None,
    }
}

fn pointer_block_bounds(
    state: &CState,
    pointer: &Pointer,
    byte_width: u32,
) -> Option<Vec<PointerFormationGuard>> {
    let Some(block_size) = state.memory().block_size(&pointer.block).cloned() else {
        return Some(Vec::new());
    };

    // Concrete offsets can exceed the signed bitvector representation. Check
    // those directly against the byte-sized block instead of silently
    // rebuilding them through a wrapping int32 term.
    if let (Some(offset), Some(size)) = (pointer.offset.as_const(), block_size.as_const()) {
        if offset < 0 || offset > i64::from(size) {
            return Some(vec![PointerFormationGuard {
                condition: ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(1),
                    Bitvector32Term::Constant(0),
                ),
                value: true,
            }]);
        }
        return Some(Vec::new());
    }

    if let PointerOffsetTerm::Int64Scaled {
        value,
        byte_width: scale,
        unsigned,
    } = &pointer.offset
        && *scale > 0
    {
        // Compare the original 64-bit element count to the number of elements
        // the block can hold. Rebuilding it as a 32-bit residue can certify an
        // index several GiB past the block as a small in-bounds number.
        let limit = if *unsigned {
            let bytes = Bitvector32Term::uint64_from_32(block_size.clone());
            if *scale == 1 {
                bytes
            } else {
                Bitvector32Term::uint64_divide(
                    bytes,
                    Bitvector32Term::UInt64Constant(*scale as u64),
                )
            }
        } else {
            let bytes = Bitvector32Term::int64_from_uint32(block_size.clone());
            if *scale == 1 {
                bytes
            } else {
                Bitvector32Term::int64_divide(bytes, Bitvector32Term::Int64Constant(*scale))
            }
        };
        let mut guards = Vec::new();
        if !*unsigned {
            guards.push(PointerFormationGuard {
                condition: ConditionTerm::int64_signed_greater_equal(
                    value.as_ref().clone(),
                    Bitvector32Term::Int64Constant(0),
                ),
                value: true,
            });
        }
        guards.push(PointerFormationGuard {
            condition: if *unsigned {
                ConditionTerm::uint64_less_equal(value.as_ref().clone(), limit)
            } else {
                ConditionTerm::int64_signed_less_equal(value.as_ref().clone(), limit)
            },
            value: true,
        });
        return Some(guards);
    }

    if pointer_offset_contains_int64_scaled(&pointer.offset) {
        let mut guards = Vec::new();
        let Some(offset) = exact_pointer_offset_i64_with_guards(&pointer.offset, &mut guards)
        else {
            // An opaque pointer-offset variable cannot be reinterpreted as a
            // 32-bit residue. Refuse to construct an unchecked normal path.
            return None;
        };
        guards.extend([
            PointerFormationGuard {
                condition: ConditionTerm::int64_signed_greater_equal(
                    offset.clone(),
                    Bitvector32Term::Int64Constant(0),
                ),
                value: true,
            },
            PointerFormationGuard {
                condition: ConditionTerm::int64_signed_less_equal(
                    offset,
                    Bitvector32Term::int64_from_uint32(block_size),
                ),
                value: true,
            },
        ]);
        return Some(guards);
    }

    if byte_width == 1
        && let Some(guards) = strided_block_bounds(&pointer.offset, &block_size)
    {
        return Some(guards);
    }

    let (offset, size) = if byte_width == 1 {
        let Some(offset) = byte_offset_from_pointer_offset(&pointer.offset) else {
            return Some(Vec::new());
        };
        (offset, block_size)
    } else {
        let Some(offset) = element_index_from_offset(&pointer.offset, byte_width) else {
            return Some(Vec::new());
        };
        let Some(size) = element_count_from_bytes(&block_size, byte_width) else {
            return Some(Vec::new());
        };
        (offset, size)
    };

    Some(vec![
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
    ])
}

/// The formation bound of a byte pointer into a struct array, stated over its
/// element index.
///
/// `items + i * stride + field` stays inside a block of `count * stride`
/// bytes exactly when `0 <= i` and either `i <= count` (the field is at the
/// start of its element, so one past the last element is a valid address) or
/// `i < count` (any other field inside the element). This is the scalar
/// element bound with the struct size as the element width; the byte
/// spelling `0 <= i * stride + field <= bytes` says the same thing in terms
/// a linear order check cannot read.
fn strided_block_bounds(
    offset: &PointerOffsetTerm,
    block_size: &Bitvector32Term,
) -> Option<Vec<PointerFormationGuard>> {
    let (index, stride, field) = match offset {
        PointerOffsetTerm::Int32Scaled { value, byte_width } => (value, *byte_width, 0),
        PointerOffsetTerm::Add(left, right) => match (left.as_ref(), right.as_ref()) {
            (
                PointerOffsetTerm::Int32Scaled { value, byte_width },
                PointerOffsetTerm::Constant(field),
            )
            | (
                PointerOffsetTerm::Constant(field),
                PointerOffsetTerm::Int32Scaled { value, byte_width },
            ) => (value, *byte_width, *field),
            _ => return None,
        },
        _ => return None,
    };
    if stride < 2 || !(0..stride).contains(&field) {
        return None;
    }
    let count = element_count_from_bytes(block_size, u32::try_from(stride).ok()?)?;
    let upper = if field == 0 {
        ConditionTerm::signed_less_equal(index.as_ref().clone(), count)
    } else {
        ConditionTerm::signed_less_than(index.as_ref().clone(), count)
    };
    Some(vec![
        PointerFormationGuard {
            condition: ConditionTerm::signed_greater_equal(
                index.as_ref().clone(),
                Bitvector32Term::Constant(0),
            ),
            value: true,
        },
        PointerFormationGuard {
            condition: upper,
            value: true,
        },
    ])
}

/// How a formed pointer relates to the memory ranges the state holds in its
/// block: the `owns` and `views` ranges of the current resources and of
/// every admitted composition, and the `viewable` extents the facts hold for
/// its object. A range contains the pointer when `start <= index <= end` in
/// the range's own element coordinates, so the one-past end counts.
///
/// This is intentionally a small, structural query. Every lookup is keyed:
/// the ranges by the pointer's block, the extents by its object identity,
/// and the pointer is resolved against each range's base by exact offset
/// arithmetic, never by searching the resource algebra. `ExternalArgument`
/// is the one block every pointer parameter shares, so a formation there
/// costs one resolution per range the contract holds.
///
/// Only a range based in the pointer's own object judges it. Two parameters
/// `p` and `q` share a block, and the index of `q + i` relative to `p`
/// resolves to the residue `(q + i) - p`, which an alias `p == q` published
/// as an offset equality never decides; a range of `p` therefore neither
/// refutes nor bounds `q + i`, and can only confirm it when both bounds are
/// decided anyway. The store through `q` is still checked against `p`'s
/// range by the resource algebra, which reads the alias.
enum HeldRangeMembership {
    /// Some held range contains the pointer, its one-past end included.
    Inside,
    /// No range is decided to contain the pointer and one range is left
    /// undecided: the guards that place the pointer inside it.
    Undecided(Vec<PointerFormationGuard>),
    /// Every range the pointer resolves in is decided not to contain it.
    Outside,
    /// No held range resolves the pointer, or several are left undecided
    /// and none of them is based at the displaced operand.
    Unknown,
}

#[derive(Default)]
struct HeldRangeSurvey {
    refuted: bool,
    /// The undecided resource ranges: whether the displaced operand is the
    /// range's base, and the guards that place the result inside it.
    undecided: Vec<(bool, Vec<PointerFormationGuard>)>,
    /// A `viewable` extent is undecided. Its byte-scaled bounds are not the
    /// element shape the formation guard rules read, so it is never a guard
    /// source, and it keeps a resource range from standing in for it alone.
    undecided_extent: bool,
}

impl HeldRangeSurvey {
    /// Records how `start <= index <= end` decides, and whether it holds.
    /// A range that does not `judge` the pointer can only confirm it: its
    /// refutation and its open bounds are not recorded.
    fn consider(
        &mut self,
        assumptions: &PureFactContext,
        facts: &(impl ExecutionFactSource + ?Sized),
        start: Bitvector32Term,
        index: Bitvector32Term,
        end: Bitvector32Term,
        judge: bool,
        from_operand: bool,
        guard_source: bool,
        wide: bool,
    ) -> bool {
        // A wide range orders its unsigned 64-bit bounds and index.
        let order = if wide {
            ConditionTerm::uint64_less_equal
        } else {
            ConditionTerm::signed_less_equal
        };
        let lower = order(start, index.clone());
        let upper = order(index, end);
        match (
            decide_with_facts(assumptions, facts, &lower),
            decide_with_facts(assumptions, facts, &upper),
        ) {
            (Some(true), Some(true)) => true,
            _ if !judge => false,
            (Some(false), _) | (_, Some(false)) => {
                self.refuted = true;
                false
            }
            _ => {
                if guard_source {
                    self.undecided.push((
                        from_operand,
                        vec![
                            PointerFormationGuard {
                                condition: lower,
                                value: true,
                            },
                            PointerFormationGuard {
                                condition: upper,
                                value: true,
                            },
                        ],
                    ));
                } else {
                    self.undecided_extent = true;
                }
                false
            }
        }
    }

    fn membership(self) -> HeldRangeMembership {
        let Self {
            refuted,
            mut undecided,
            undecided_extent,
        } = self;
        if undecided_extent {
            return HeldRangeMembership::Unknown;
        }
        match undecided.len() {
            0 if refuted => HeldRangeMembership::Outside,
            0 => HeldRangeMembership::Unknown,
            1 => {
                HeldRangeMembership::Undecided(undecided.pop().expect("one undecided held range").1)
            }
            _ => {
                // Several ranges could hold the result. The one the displaced
                // operand is the base of is the range the arithmetic is
                // relative to; with no such range, or two, the disjunction
                // has no single guard and the formation owes nothing here.
                let mut from_operand = undecided
                    .into_iter()
                    .filter(|(from_operand, _)| *from_operand);
                match (from_operand.next(), from_operand.next()) {
                    (Some((_, guards)), None) => HeldRangeMembership::Undecided(guards),
                    _ => HeldRangeMembership::Unknown,
                }
            }
        }
    }
}

fn held_range_membership(
    state: &CState,
    assumptions: &PureFactContext,
    facts: &(impl ExecutionFactSource + ?Sized),
    operand: &Pointer,
    pointer: &Pointer,
    byte_width: u32,
) -> HeldRangeMembership {
    let mut survey = HeldRangeSurvey::default();
    let object = pointer.object_base();
    for resources in
        std::iter::once(state.resources()).chain(assumptions.resource_compositions.iter())
    {
        for fact in resources.memory_facts_in_block(&pointer.block) {
            let Some(range) = fact.memory_range() else {
                continue;
            };
            if range.element_width() != byte_width {
                continue;
            }
            if let Some((start, end)) = range.wide_bounds() {
                let Some(index) = pointer.wide_element_index_from_base(range.base(), byte_width)
                else {
                    continue;
                };
                if survey.consider(
                    assumptions,
                    facts,
                    start.clone(),
                    index,
                    end.clone(),
                    range.base().object_base() == object,
                    range.base() == operand,
                    true,
                    true,
                ) {
                    return HeldRangeMembership::Inside;
                }
                continue;
            }
            // A 64-bit index keeps its own form in the pointer. Against a
            // range of 32-bit indices it is read as one where it is proved
            // to fit.
            let Some(index) =
                pointer_index_from_base(pointer, range.base(), byte_width).or_else(|| {
                    crate::kernel::reasoning::element_index_from_offset_with_facts(
                        &pointer.offset_from_base(range.base())?,
                        byte_width,
                        assumptions,
                    )
                })
            else {
                continue;
            };
            if survey.consider(
                assumptions,
                facts,
                range.start().clone(),
                index,
                range.end().clone(),
                range.base().object_base() == object,
                range.base() == operand,
                true,
                false,
            ) {
                return HeldRangeMembership::Inside;
            }
        }
    }
    for proposition in assumptions.memory_loadable_candidates_for_object(pointer) {
        let Proposition::CMemoryLoadable {
            memory,
            base,
            bytes,
            wide: false,
        } = proposition
        else {
            continue;
        };
        if !crate::kernel::reasoning::memory_range_still_available(
            memory,
            state.memory(),
            base,
            assumptions,
        ) {
            continue;
        }
        let Some(offset) = pointer_byte_offset_from_base(pointer, base) else {
            continue;
        };
        if survey.consider(
            assumptions,
            facts,
            Bitvector32Term::Constant(0),
            offset,
            bytes.clone(),
            true,
            false,
            false,
            false,
        ) {
            return HeldRangeMembership::Inside;
        }
    }
    survey.membership()
}

fn pointer_index_from_base(
    pointer: &Pointer,
    base: &Pointer,
    byte_width: u32,
) -> Option<Bitvector32Term> {
    match byte_width {
        0 => None,
        1 => pointer_byte_offset_from_base(pointer, base),
        width => pointer.element_index_from_base_with_width(base, width),
    }
}

/// Resolve one recorded equality-class hop before checking signed-add
/// overflow. The normal simplifier handles direct equalities and recursively
/// simplifies a term's children, but it deliberately does not search through
/// a whole equality closure. A returned aggregate can expose a result
/// variable equal to a short expression whose leaves are direct constants;
/// checking that one class is enough to recognize the concrete value without
/// reintroducing an unbounded contextual-lowering search.
fn simplify_c_int32_add_operand(
    assumptions: &PureFactContext,
    term: &Bitvector32Term,
) -> Bitvector32Term {
    let simplified = assumptions.simplify_bitvector_under_assumptions(term);
    if simplified.as_const().is_some() {
        return simplified;
    }
    assumptions
        .recorded_equality_class(term)
        .into_iter()
        .map(|member| assumptions.simplify_bitvector_under_assumptions(&member))
        .find(|member| member.as_const().is_some())
        .unwrap_or(simplified)
}

fn apply_pointer_formation_guards(
    pointer: CPointerValue,
    guards: Vec<PointerFormationGuard>,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let mut normal = vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(CValue::Pointer(pointer)),
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

/// The refused paths `guards` owe on a path with `facts`, without assuming
/// the guards on that path: one path per guard the facts leave open,
/// carrying the guard's negation under `refusal`. A guard the facts decide
/// as required owes nothing. `None` when the facts decide a guard against
/// its required value, so the path itself is refused.
///
/// This differs from a formation guard of a block with a recorded size,
/// which the normal path assumes: the normal path here keeps exactly the
/// facts it had, so a proof that verified before the guard existed sees the
/// same facts, and only the refused path is new.
fn owed_guard_paths(
    guards: Vec<PointerFormationGuard>,
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
    assumptions: &PureFactContext,
    refusal: &CUndefinedBehavior,
) -> Option<Vec<CExpressionPath>> {
    let mut refused = Vec::new();
    for guard in guards {
        match decide_with_facts(assumptions, facts, &guard.condition) {
            Some(known) if known == guard.value => {}
            Some(_) => return None,
            None => {
                let mut refused_facts = facts.persistent_facts();
                add_condition_path_fact(
                    &mut refused_facts,
                    assumptions,
                    guard.condition,
                    !guard.value,
                )
                .expect("an undecided guard's negation should be consistent");
                refused.push(CExpressionPath {
                    outcome: CExpressionOutcome::UndefinedBehavior(refusal.clone()),
                    facts: refused_facts,
                    obligations: obligations.to_vec(),
                });
            }
        }
    }
    Some(refused)
}

/// Keep checked C addition values shallow when adjoining constant offsets.
/// This runs only after the operation's original overflow guard is checked;
/// it does not reassociate the C expression or discard intermediate guards.
/// Keep the combined offset signed-representable for interval reconstruction.
fn c_int32_add_value(left: Bitvector32Term, right: Bitvector32Term) -> Bitvector32Term {
    if let (Bitvector32Term::Add(base, trailing), Bitvector32Term::Constant(right)) =
        (&left, &right)
        && let Bitvector32Term::Constant(trailing) = trailing.as_ref()
        && let Some(offset) = (*trailing as i32).checked_add(*right as i32)
    {
        return Bitvector32Term::add(
            base.as_ref().clone(),
            Bitvector32Term::Constant(offset as u32),
        );
    }
    Bitvector32Term::add(left, right)
}

pub(in crate::kernel) fn apply_c_int32_add(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_add_overflows(
        simplify_c_int32_add_operand(assumptions, &left),
        simplify_c_int32_add_operand(assumptions, &right),
    );
    let decision = crate::instrumentation::measure_operation(
        "kernel",
        "independent kernel execution",
        "int32 add overflow decision",
        || decide_with_facts(assumptions, &facts, &overflow),
    );
    match decision {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(CUndefinedBehavior::SignedOverflow),
            facts,
            obligations,
        }],
        Some(false) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(int32(c_int32_add_value(left, right))),
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
                    outcome: CExpressionOutcome::Value(int32(c_int32_add_value(left, right))),
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
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_subtract_overflows(left.clone(), right.clone());
    split_on_undefined_behavior(
        overflow,
        CUndefinedBehavior::SignedOverflow,
        facts,
        obligations,
        assumptions,
        |facts, obligations| {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::subtract(left, right))),
                facts,
                obligations,
            }]
        },
    )
}

pub(in crate::kernel) fn apply_c_int32_multiply(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_multiply_overflows(
        normalize_exact_memory_loads_in_bitvector(&left, assumptions),
        normalize_exact_memory_loads_in_bitvector(&right, assumptions),
    );
    split_on_undefined_behavior(
        overflow,
        CUndefinedBehavior::SignedOverflow,
        facts,
        obligations,
        assumptions,
        |facts, obligations| {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::multiply(left, right))),
                facts,
                obligations,
            }]
        },
    )
}

pub(in crate::kernel) fn apply_c_int32_divide(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
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
    facts: ExecutionFacts,
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
    facts: ExecutionFacts,
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
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_divide_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
        Some(true) => vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(
                CUndefinedBehavior::SignedDivisionOverflow,
            ),
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
                        CUndefinedBehavior::SignedDivisionOverflow,
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
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    overflow: ConditionTerm,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    split_on_undefined_behavior(
        overflow,
        CUndefinedBehavior::SignedOverflow,
        facts,
        obligations,
        assumptions,
        |facts, obligations| {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(CValue::Int64(result(left, right))),
                facts,
                obligations,
            }]
        },
    )
}

fn apply_c_int64_division_like(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
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
    facts: ExecutionFacts,
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
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let zero = ConditionTerm::uint64_equal(right.clone(), Bitvector32Term::UInt64Constant(0));
    split_on_undefined_behavior(
        zero,
        CUndefinedBehavior::DivisionByZero,
        facts,
        obligations,
        assumptions,
        |facts, obligations| {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(CValue::UInt64(result(left, right))),
                facts,
                obligations,
            }]
        },
    )
}

fn apply_c_uint32_division_like(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    result: fn(Bitvector32Term, Bitvector32Term) -> Bitvector32Term,
) -> Vec<CExpressionPath> {
    let divides_by_zero = ConditionTerm::equal(right.clone(), Bitvector32Term::Constant(0));
    split_on_undefined_behavior(
        divides_by_zero,
        CUndefinedBehavior::DivisionByZero,
        facts,
        obligations,
        assumptions,
        |facts, obligations| {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(uint32(result(left, right))),
                facts,
                obligations,
            }]
        },
    )
}

fn promote_c_shift_count(value: CValue) -> Option<(Bitvector32Term, bool, bool)> {
    match value {
        CValue::PointerInteger(value) => promote_c_shift_count(value.numeric_value()),
        CValue::Bool(value) => Some((value, false, false)),
        CValue::UInt32(value) => Some((value, true, false)),
        CValue::Int32(value) => Some((value, false, false)),
        CValue::UInt8(value) => Some((value, false, false)),
        CValue::Int8(value) => Some((value, false, false)),
        CValue::Int16(value) => Some((value, false, false)),
        CValue::UInt16(value) => Some((value, false, false)),
        CValue::Int64(value) => Some((value, false, true)),
        CValue::UInt64(value) => Some((value, true, true)),
        CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => None,
    }
}

pub(in crate::kernel) fn apply_c_shift_left(
    left: CValue,
    right: CValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let left = numeric_pointer_integer_value(left);
    let right = numeric_pointer_integer_value(right);
    let facts = facts;
    let Some((right, unsigned_count, right_is_64_bit)) = promote_c_shift_count(right) else {
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
            right_is_64_bit,
            apply_c_int64_shift_left_valid_count,
        ),
        CValue::UInt64(left) => apply_c_int64_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
            apply_c_uint64_shift_left_valid_count,
        ),
        CValue::UInt32(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
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
        CValue::Bool(left) | CValue::Int32(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
            apply_c_int32_shift_left_valid_count,
        ),
        CValue::Int8(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
            apply_c_int32_shift_left_valid_count,
        ),
        CValue::Int16(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
            apply_c_int32_shift_left_valid_count,
        ),
        CValue::UInt8(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
            apply_c_int32_shift_left_valid_count,
        ),
        CValue::UInt16(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
            apply_c_int32_shift_left_valid_count,
        ),
        CValue::PointerInteger(_)
        | CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => {
            vec![c_type_mismatch_expression_path(facts, obligations)]
        }
    }
}

pub(in crate::kernel) fn apply_c_shift_right(
    left: CValue,
    right: CValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let left = numeric_pointer_integer_value(left);
    let right = numeric_pointer_integer_value(right);
    let facts = facts;
    let Some((right, unsigned_count, right_is_64_bit)) = promote_c_shift_count(right) else {
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
            right_is_64_bit,
            apply_c_int64_shift_right_valid_count,
        ),
        CValue::UInt64(left) => apply_c_int64_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
            apply_c_uint64_shift_right_valid_count,
        ),
        CValue::UInt32(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
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
        CValue::Bool(left) | CValue::Int32(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
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
        CValue::Int8(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
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
        CValue::Int16(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
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
        CValue::UInt8(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
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
        CValue::UInt16(left) => apply_c_int32_with_valid_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            right_is_64_bit,
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
        CValue::PointerInteger(_)
        | CValue::Int128(_)
        | CValue::UInt128(_)
        | CValue::Void
        | CValue::Pointer(_)
        | CValue::Float32(_)
        | CValue::Float64(_) => {
            vec![c_type_mismatch_expression_path(facts, obligations)]
        }
    }
}

fn apply_c_int64_with_valid_shift_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    unsigned_count: bool,
    right_is_64_bit: bool,
    apply_valid_count: ValidInt64ShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    let count = if right_is_64_bit {
        right
    } else if unsigned_count {
        Bitvector32Term::uint64_from_32(right)
    } else {
        Bitvector32Term::int64_from_32(right)
    };
    let invalid_count = if unsigned_count {
        ConditionTerm::uint64_greater_equal(count.clone(), Bitvector32Term::UInt64Constant(64))
    } else {
        ConditionTerm::int64_signed_less_than(count.clone(), Bitvector32Term::Int64Constant(0))
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
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    apply_valid_count: ValidInt64ShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    split_on_undefined_behavior(
        too_large,
        CUndefinedBehavior::InvalidShift,
        facts,
        obligations,
        assumptions,
        |facts, obligations| apply_valid_count(left, count, facts, obligations, assumptions),
    )
}

fn apply_c_int64_shift_left_valid_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let negative_left =
        ConditionTerm::int64_signed_less_than(left.clone(), Bitvector32Term::Int64Constant(0));
    split_on_undefined_behavior(
        negative_left,
        CUndefinedBehavior::InvalidShift,
        facts,
        obligations,
        assumptions,
        |facts, obligations| {
            apply_c_int64_shift_left_nonnegative(left, right, facts, obligations, assumptions)
        },
    )
}

fn apply_c_int64_shift_left_nonnegative(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::int64_signed_shift_left_overflows(left.clone(), right.clone());
    split_on_undefined_behavior(
        overflow,
        CUndefinedBehavior::SignedOverflow,
        facts,
        obligations,
        assumptions,
        |facts, obligations| {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(CValue::Int64(
                    Bitvector32Term::int64_shift_left(left, right),
                )),
                facts,
                obligations,
            }]
        },
    )
}

fn apply_c_uint64_shift_left_valid_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
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
    facts: ExecutionFacts,
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
    facts: ExecutionFacts,
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
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    unsigned_count: bool,
    right_is_64_bit: bool,
    apply_valid_count: ValidShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    if right_is_64_bit {
        return apply_c_int32_with_valid_wide_shift_count(
            left,
            right,
            facts,
            obligations,
            assumptions,
            unsigned_count,
            apply_valid_count,
        );
    }
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

fn apply_c_int32_with_valid_wide_shift_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    unsigned_count: bool,
    apply_valid_count: ValidShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    if unsigned_count {
        return apply_c_int32_with_nonnegative_wide_shift_count(
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
        ConditionTerm::int64_signed_less_than(right.clone(), Bitvector32Term::Int64Constant(0));
    split_on_undefined_behavior(
        negative_count,
        CUndefinedBehavior::InvalidShift,
        facts,
        obligations,
        assumptions,
        |facts, obligations| {
            apply_c_int32_with_nonnegative_wide_shift_count(
                left,
                right,
                facts,
                obligations,
                assumptions,
                false,
                apply_valid_count,
            )
        },
    )
}

fn apply_c_int32_with_nonnegative_wide_shift_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    unsigned_count: bool,
    apply_valid_count: ValidShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    let too_large_count = if unsigned_count {
        ConditionTerm::uint64_greater_equal(right.clone(), Bitvector32Term::UInt64Constant(32))
    } else {
        ConditionTerm::int64_signed_greater_equal(right.clone(), Bitvector32Term::Int64Constant(32))
    };
    split_on_undefined_behavior(
        too_large_count,
        CUndefinedBehavior::InvalidShift,
        facts,
        obligations,
        assumptions,
        |facts, obligations| {
            apply_valid_count(
                left,
                Bitvector32Term::uint32_from_64(right),
                facts,
                obligations,
                assumptions,
            )
        },
    )
}

fn apply_c_int32_with_nonnegative_shift_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
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
    split_on_undefined_behavior(
        too_large_count,
        CUndefinedBehavior::InvalidShift,
        facts,
        obligations,
        assumptions,
        |facts, obligations| apply_valid_count(left, right, facts, obligations, assumptions),
    )
}

fn apply_c_int32_shift_left_valid_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: ExecutionFacts,
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
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_shift_left_overflows(left.clone(), right.clone());
    split_on_undefined_behavior(
        overflow,
        CUndefinedBehavior::SignedOverflow,
        facts,
        obligations,
        assumptions,
        |facts, obligations| {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(int32(Bitvector32Term::shift_left(left, right))),
                facts,
                obligations,
            }]
        },
    )
}

pub(in crate::kernel) fn evaluate_c_equal_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    evaluate_c_equality_paths(
        state,
        CComparisonOperator::Equal,
        left,
        right,
        assumptions,
        budget,
    )
}

pub(in crate::kernel) fn evaluate_c_not_equal_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    evaluate_c_equality_paths(
        state,
        CComparisonOperator::NotEqual,
        left,
        right,
        assumptions,
        budget,
    )
}

fn evaluate_c_equality_paths(
    state: &CState,
    operator: CComparisonOperator,
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
            apply_c_equality(
                state,
                operator,
                left,
                right,
                facts,
                obligations,
                assumptions,
            )
        },
    )
}

/// `==` or `!=` (`operator` is one of the two) over two C values.
fn apply_c_equality(
    state: &CState,
    operator: CComparisonOperator,
    left: CValue,
    right: CValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CExpressionPath> {
    let left = numeric_pointer_integer_value(left);
    let right = numeric_pointer_integer_value(right);
    let negated = operator == CComparisonOperator::NotEqual;
    if matches!(left, CValue::Int128(_) | CValue::UInt128(_))
        || matches!(right, CValue::Int128(_) | CValue::UInt128(_))
    {
        return apply_c_int128_comparison(operator, left, right, facts, obligations, assumptions);
    }

    if let Some((left, right, target_type, obligations)) =
        coerce_c_float_operands(&left, &right, &obligations, assumptions)
    {
        return apply_c_float_comparison(
            left,
            right,
            target_type,
            operator,
            facts,
            obligations,
            assumptions,
        );
    }
    let (left, right) = promote_c_bool_scalar_operands(left, right);
    if let Some(width @ (ScalarWidth::Int64 | ScalarWidth::UInt64)) = scalar_width(&left, &right) {
        let facts = facts;
        let Some((left, right, _)) = apply_c_scalar_terms(left, right) else {
            return Vec::new();
        };
        let condition = if matches!(width, ScalarWidth::Int64) {
            ConditionTerm::int64_equal(left, right)
        } else {
            ConditionTerm::uint64_equal(left, right)
        };
        return condition_as_c_int32_paths_valued(
            condition,
            facts,
            obligations,
            assumptions,
            negated,
        );
    }
    match (left, right) {
        (CValue::Pointer(left), CValue::Pointer(right)) => {
            if !pointer_types_compatible(&left, &right) {
                vec![c_type_mismatch_expression_path(facts, obligations)]
            } else {
                let (left, right) = (left.into_pointer(), right.into_pointer());
                let mut facts = facts;
                if let Some(holders) =
                    compared_pointer_holders_composition(state, &left, &right, assumptions)
                {
                    facts.push(ExecutionPureFact::new(Proposition::CResourceComposition(
                        holders,
                    )));
                }
                let (compared_left, compared_right) = (left.clone(), right.clone());
                apply_pointer_adjacency_guard(
                    state,
                    &compared_left,
                    &compared_right,
                    facts,
                    obligations,
                    assumptions,
                    move |facts, obligations| {
                        condition_as_c_int32_paths_valued(
                            pointer_equality_condition(left, right),
                            facts,
                            obligations,
                            assumptions,
                            negated,
                        )
                    },
                )
            }
        }
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            condition_as_c_int32_paths_valued(
                pointer_is_null_condition(pointer.into_pointer()),
                facts,
                obligations,
                assumptions,
                negated,
            )
        }
        (
            left @ (crate::kernel::integer32_c_value!(_)),
            right @ (crate::kernel::integer32_c_value!(_)),
        ) if scalar_uses_uint32(&left, &right) => {
            let facts = facts;
            let Some(left) = promote_c_uint32_path_value(left) else {
                return Vec::new();
            };
            let Some(right) = promote_c_uint32_path_value(right) else {
                return Vec::new();
            };
            condition_as_c_int32_paths_valued(
                ConditionTerm::equal(left, right),
                facts,
                obligations,
                assumptions,
                negated,
            )
        }
        (
            left @ (crate::kernel::int_promoted_c_value!(_)),
            right @ (crate::kernel::int_promoted_c_value!(_)),
        ) => {
            let facts = facts;
            let Some(left) = promote_c_int32_path_value(left) else {
                return Vec::new();
            };
            let Some(right) = promote_c_int32_path_value(right) else {
                return Vec::new();
            };
            condition_as_c_int32_paths_valued(
                ConditionTerm::equal(left, right),
                facts,
                obligations,
                assumptions,
                negated,
            )
        }
        (CValue::Float32(left), CValue::Float32(right)) => condition_as_c_int32_paths_valued(
            ConditionTerm::float32_compare(left, right, operator),
            facts,
            obligations,
            assumptions,
            negated,
        ),
        (CValue::Float64(left), CValue::Float64(right)) => condition_as_c_int32_paths_valued(
            ConditionTerm::float64_compare(left, right, operator),
            facts,
            obligations,
            assumptions,
            negated,
        ),
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
    for path in evaluate_c_condition_paths(state, expression, assumptions, budget)? {
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
    for left_path in evaluate_c_condition_paths(state, left, assumptions, budget)? {
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
                        evaluate_c_condition_paths(state, right, &right_assumptions, budget)?
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
    for left_path in evaluate_c_condition_paths(state, left, assumptions, budget)? {
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
                        evaluate_c_condition_paths(state, right, &right_assumptions, budget)?
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

/// Refuses an equality comparison C11 6.5.9p6 leaves to the implementation's
/// object layout. Two pointers into distinct objects compare unequal, except
/// that one past the end of one object may equal the start of another: the
/// two are equal exactly when the objects are adjacent, which the kernel does
/// not model. The decision procedure answers a distinct-block
/// `PointerEqual` false from the blocks alone, so that configuration is
/// excluded here, before the condition is built: when the facts decide it
/// the comparison is refused, and when they leave it open a refused path
/// carrying the configuration is owed beside the comparison, whose own path
/// keeps the facts it had.
///
/// Only a pair whose blocks are proven distinct is examined; any other pair
/// is already an undecided condition. Null comparisons and same-block
/// comparisons are unaffected. A pointer at its object's start is never
/// taken for its one-past end, so two objects' starts stay decided; the
/// kernel's objects are nonempty.
fn apply_pointer_adjacency_guard(
    state: &CState,
    left: &Pointer,
    right: &Pointer,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    apply: impl FnOnce(ExecutionFacts, Vec<ProofObligation>) -> Vec<CExpressionPath>,
) -> Vec<CExpressionPath> {
    if !left.blocks_proven_distinct(right) || left.is_in_null_block() || right.is_in_null_block() {
        return apply(facts, obligations);
    }
    let mut guards = Vec::new();
    let mut one_past_end = false;
    for (end, start) in [(left, right), (right, left)] {
        let Some(at_end) = pointer_at_block_end_condition(state, end) else {
            continue;
        };
        let Some(at_start) = pointer_at_object_start_condition(start) else {
            continue;
        };
        match (
            decide_with_facts(assumptions, &facts, &at_end),
            decide_with_facts(assumptions, &facts, &at_start),
        ) {
            (Some(false), _) | (_, Some(false)) => continue,
            (Some(true), None) => guards.push(PointerFormationGuard {
                condition: at_start,
                value: false,
            }),
            _ => guards.push(PointerFormationGuard {
                condition: at_end,
                value: false,
            }),
        }
        one_past_end = true;
    }
    if !one_past_end {
        return apply(facts, obligations);
    }
    let refusal = CUndefinedBehavior::OnePastEndComparison;
    let Some(mut paths) = owed_guard_paths(guards, &facts, &obligations, assumptions, &refusal)
    else {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::UndefinedBehavior(refusal),
            facts,
            obligations,
        }];
    };
    paths.extend(apply(facts, obligations));
    paths
}

/// The pointer's displacement from its object's base: its offset for a block
/// based at offset zero, and the summands after the parameter's opaque base
/// for argument memory. `None` when the offset does not spell the base.
fn pointer_object_displacement(pointer: &Pointer) -> Option<PointerOffsetTerm> {
    pointer.offset_from_base(&pointer.object_base())
}

/// The condition under which `pointer` is one past the end of its block, or
/// `None` when it cannot be: a pointer at its object's start, or one at a
/// constant offset other than the block's constant size. A displacement the
/// terms do not resolve, and any nonzero displacement into a block whose
/// extent the state does not record, may be the end.
fn pointer_at_block_end_condition(state: &CState, pointer: &Pointer) -> Option<ConditionTerm> {
    let Some(displacement) = pointer_object_displacement(pointer) else {
        return Some(ConditionTerm::Constant(true));
    };
    if displacement.as_const() == Some(0) {
        return None;
    }
    let Some(size) = state.memory().block_size(&pointer.block).cloned() else {
        return Some(ConditionTerm::Constant(true));
    };
    match (displacement.as_const(), size.as_const()) {
        (Some(offset), Some(size)) => {
            (offset == i64::from(size)).then_some(ConditionTerm::Constant(true))
        }
        _ => match byte_offset_from_pointer_offset(&displacement) {
            Some(offset) => Some(ConditionTerm::equal(offset, size)),
            None => Some(ConditionTerm::Constant(true)),
        },
    }
}

/// The condition under which `pointer` is the start of its object, or `None`
/// when a constant displacement says it is not.
fn pointer_at_object_start_condition(pointer: &Pointer) -> Option<ConditionTerm> {
    let Some(displacement) = pointer_object_displacement(pointer) else {
        return Some(ConditionTerm::Constant(true));
    };
    match displacement.as_const() {
        Some(0) => Some(ConditionTerm::Constant(true)),
        Some(_) => None,
        None => match byte_offset_from_pointer_offset(&displacement) {
            Some(offset) => Some(ConditionTerm::equal(offset, Bitvector32Term::Constant(0))),
            None => Some(ConditionTerm::Constant(true)),
        },
    }
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

#[cfg(test)]
mod wide_range_reader_tests {
    use super::*;
    // Object provenance uses native nonemptiness, never the range's low word.
    #[test]
    fn wide_nonempty_owned_range_supplies_object_provenance() {
        let base = Pointer::symbolic(Variable(985_100));
        let wide = CMemoryRange::new_wide(
            base.clone(),
            Bitvector32Term::UInt64Constant(0),
            Bitvector32Term::UInt64Constant(1 << 33),
            4,
        );
        let state = CState::new().with_resource_context(
            ResourceContext::new().unchecked_with_fact(CResourceFact::own_memory(wide)),
        );
        assert!(pointer_has_object_provenance_evidence(
            &state,
            &base,
            &PureFactContext::new(),
            &ExecutionFacts::new()
        ));
    }
}
