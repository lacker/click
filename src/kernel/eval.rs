use super::prelude::*;

type ValidShiftCountEvaluator = fn(
    Bitvector32Term,
    Bitvector32Term,
    Vec<ExecutionPureFact>,
    Vec<ProofObligation>,
    &Assumptions,
) -> Vec<CExpressionPath>;

pub(super) fn evaluate_c_expression(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
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

pub(super) fn add_uint8_range_execution_pure_facts(
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
    value: &Bitvector32Term,
) -> Option<()> {
    add_internal_condition_path_fact(
        facts,
        assumptions,
        ConditionTerm::signed_greater_equal(value.clone(), Bitvector32Term::Constant(0)),
        true,
    )?;
    add_internal_condition_path_fact(
        facts,
        assumptions,
        ConditionTerm::signed_less_equal(value.clone(), Bitvector32Term::Constant(255)),
        true,
    )
}

pub(super) fn promote_c_int32_path_value(
    value: CValue,
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &Assumptions,
) -> Option<Bitvector32Term> {
    match value {
        CValue::Int32(value) => Some(value),
        CValue::UInt8(value) => {
            add_uint8_range_execution_pure_facts(facts, assumptions, &value)?;
            Some(value)
        }
        CValue::Pointer(_) => None,
    }
}

pub(super) fn coerce_c_value_to_type(
    value: CValue,
    target_type: CType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Option<CValue> {
    if target_type.accepts(&value) {
        return Some(value);
    }

    match (target_type, value) {
        (CType::UInt8, CValue::Int32(value)) => {
            add_proof_obligation_with_context(
                obligations,
                assumptions,
                Proposition::ConditionIs(
                    ConditionTerm::signed_greater_equal(
                        value.clone(),
                        Bitvector32Term::Constant(0),
                    ),
                    true,
                ),
                Some("uint8 narrowing lower bound"),
            )?;
            add_proof_obligation_with_context(
                obligations,
                assumptions,
                Proposition::ConditionIs(
                    ConditionTerm::signed_less_equal(value.clone(), Bitvector32Term::Constant(255)),
                    true,
                ),
                Some("uint8 narrowing upper bound"),
            )?;
            Some(CValue::UInt8(value))
        }
        _ => None,
    }
}

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

pub(super) fn evaluate_c_expression_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    budget.consume_expression_step()?;
    let paths = match expression {
        CExpression::Value(value) => vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value.clone()),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CExpression::Variable(name) if state.locals.is_array_object(name) => {
            let pointer = CMemory::local_pointer(name);
            vec![CExpressionPath {
                outcome: if state.memory.has_block(&pointer.block) {
                    CExpressionOutcome::Value(CValue::Pointer(pointer))
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
        CExpression::AddressOf(target) => {
            address_of_lvalue_paths(state, target, assumptions, budget)?
        }
        CExpression::LessThan(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                condition_as_c_int32_paths(
                    ConditionTerm::signed_less_than(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        )?,
        CExpression::LessEqual(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                condition_as_c_int32_paths(
                    ConditionTerm::signed_less_equal(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        )?,
        CExpression::GreaterThan(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                condition_as_c_int32_paths(
                    ConditionTerm::signed_greater_than(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
        )?,
        CExpression::GreaterEqual(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                condition_as_c_int32_paths(
                    ConditionTerm::signed_greater_equal(left, right),
                    facts,
                    obligations,
                    assumptions,
                )
            },
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
        CExpression::Subtract(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_subtract(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::Multiply(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_multiply(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::Divide(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_divide(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::Remainder(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_remainder(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::ShiftLeft(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_shift_left(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::ShiftRight(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_shift_right(left, right, facts, obligations, assumptions)
            },
        )?,
        CExpression::BitwiseAnd(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_total_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    Bitvector32Term::bitwise_and,
                )
            },
        )?,
        CExpression::BitwiseOr(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_total_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    Bitvector32Term::bitwise_or,
                )
            },
        )?,
        CExpression::BitwiseXor(left, right) => evaluate_c_int32_binary_paths(
            state,
            left,
            right,
            assumptions,
            budget,
            |left, right, facts, obligations| {
                apply_c_int32_total_binary(
                    left,
                    right,
                    facts,
                    obligations,
                    Bitvector32Term::bitwise_xor,
                )
            },
        )?,
        CExpression::BitwiseNot(expression) => evaluate_c_int32_total_unary_paths(
            state,
            expression,
            assumptions,
            budget,
            Bitvector32Term::bitwise_not,
        )?,
        CExpression::Load(_) | CExpression::TypedLoad { .. } | CExpression::Index(_, _) => {
            read_c_lvalue_expression_paths(state, expression, assumptions, budget)?
        }
    };
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn evaluate_c_lvalue_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CLValuePath>> {
    budget.consume_expression_step()?;
    let paths = match expression {
        CExpression::Variable(name) => vec![CLValuePath {
            outcome: match state.locals.binding(name) {
                Some(CLocalBinding::Object { c_type, .. }) => {
                    CLValueOutcome::LValue(CLValue::local(name.clone(), *c_type))
                }
                Some(CLocalBinding::ArrayObject { .. }) => {
                    CLValueOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                }
                None => CLValueOutcome::RuntimeError(CRuntimeError::UnboundVariable(name.clone())),
            },
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CExpression::Load(pointer_expression) => {
            let mut paths = Vec::new();
            let value_type =
                c_expression_pointee_type(state, pointer_expression).unwrap_or(CType::Int32);
            for pointer_path in
                evaluate_c_expression_paths(state, pointer_expression, assumptions, budget)?
            {
                paths.push(match pointer_path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => CLValuePath {
                        outcome: CLValueOutcome::LValue(CLValue::memory(pointer, value_type)),
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
                        outcome: CLValueOutcome::LValue(CLValue::memory(pointer, *value_type)),
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
            let mut paths = Vec::new();
            let value_type = c_expression_pointee_type(state, base).unwrap_or(CType::Int32);
            for pointer_path in evaluate_c_add_paths(state, base, index, assumptions, budget)? {
                paths.push(match pointer_path.outcome {
                    CExpressionOutcome::Value(CValue::Pointer(pointer)) => CLValuePath {
                        outcome: CLValueOutcome::LValue(CLValue::memory(pointer, value_type)),
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
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn read_c_lvalue_expression_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
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
        ));
    }
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn read_c_lvalue_paths(
    state: &CState,
    outcome: CLValueOutcome,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    match outcome {
        CLValueOutcome::LValue(lvalue) => match &lvalue.storage {
            CLValueStorage::Local { name } => vec![CExpressionPath {
                outcome: match state.locals.get(name) {
                    Some(value) if lvalue.value_type.accepts(value) => {
                        CExpressionOutcome::Value(value.clone())
                    }
                    Some(_) => CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    None => CExpressionOutcome::RuntimeError(CRuntimeError::UnboundVariable(
                        name.clone(),
                    )),
                },
                facts,
                obligations,
            }],
            CLValueStorage::Memory { pointer } => {
                let effective_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                let has_external_read_resource = is_external_memory_pointer(pointer)
                    && resource_context_has_read(
                        state.resources(),
                        pointer,
                        lvalue.value_type.byte_width(),
                        &effective_assumptions,
                    );
                if is_external_memory_pointer(pointer) && !has_external_read_resource {
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
                evaluate_c_memory_load_paths(
                    &state.memory,
                    pointer.clone(),
                    lvalue.value_type,
                    facts,
                    obligations,
                    assumptions,
                    has_external_read_resource,
                )
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

pub(super) fn address_of_lvalue_paths(
    state: &CState,
    target: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for lvalue_path in evaluate_c_lvalue_paths(state, target, assumptions, budget)? {
        paths.push(match lvalue_path.outcome {
            CLValueOutcome::LValue(lvalue) => match lvalue.pointer(state) {
                Some(pointer) => CExpressionPath {
                    outcome: CExpressionOutcome::Value(CValue::Pointer(pointer)),
                    facts: lvalue_path.facts,
                    obligations: lvalue_path.obligations,
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
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn c_expression_pointee_type(state: &CState, expression: &CExpression) -> Option<CType> {
    match expression {
        CExpression::Variable(name) => match state.locals.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => c_type.pointee_type(),
            Some(CLocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            None => None,
        },
        CExpression::AddressOf(target) => c_expression_lvalue_type(state, target),
        CExpression::TypedLoad { value_type, .. } => value_type.pointee_type(),
        CExpression::Add(left, right) => c_expression_pointee_type(state, left)
            .or_else(|| c_expression_pointee_type(state, right)),
        CExpression::Subtract(left, _) => c_expression_pointee_type(state, left),
        _ => None,
    }
}

pub(super) fn c_expression_lvalue_type(state: &CState, expression: &CExpression) -> Option<CType> {
    match expression {
        CExpression::Variable(name) => state.locals.object_type(name),
        CExpression::Load(pointer) => c_expression_pointee_type(state, pointer),
        CExpression::TypedLoad { value_type, .. } => Some(*value_type),
        CExpression::Index(base, _) => c_expression_pointee_type(state, base),
        _ => None,
    }
}

pub(super) fn c_expression_pointer_step_width(
    state: &CState,
    expression: &CExpression,
) -> Option<u32> {
    c_expression_pointee_type(state, expression).map(CType::byte_width)
}

pub(super) fn condition_as_c_int32_paths(
    condition: ConditionTerm,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
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

pub(super) fn condition_as_c_int32_not_paths(
    condition: ConditionTerm,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
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
pub(super) struct CTruthinessPath {
    pub(super) is_true: bool,
    pub(super) facts: Vec<ExecutionPureFact>,
    pub(super) obligations: Vec<ProofObligation>,
}

pub(super) fn c_truthiness_paths(
    value: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CTruthinessPath> {
    match value {
        CValue::Int32(bits) | CValue::UInt8(bits) => {
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
        CValue::Pointer(pointer) => {
            let is_null = pointer_is_null_condition(pointer);
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

pub(super) fn c_truthiness_as_c_int32_paths(
    value: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
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

pub(super) fn evaluate_c_memory_load_paths(
    memory: &CMemory,
    pointer: Pointer,
    value_type: CType,
    facts: Vec<ExecutionPureFact>,
    mut obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
    has_external_read_resource: bool,
) -> Vec<CExpressionPath> {
    // An exact materialized cell is already the authoritative value for this
    // pointer. Avoid proving every other symbolic cell distinct before the
    // direct map lookup.
    if let Some(value) = memory.known_value(&pointer) {
        if let Some(value) = symbolic_pointer_value_from_int_cell(&pointer, &value, value_type) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if !value_type.accepts(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        }
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if has_external_read_resource && assumptions.should_prefer_symbolic_external_loads() {
        let Some(value) = symbolic_load_value(memory, &pointer, value_type) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    let memory = memory.without_proven_distinct_cells(&pointer, assumptions);

    if let Some(value) = memory.known_value(&pointer) {
        if let Some(value) = symbolic_pointer_value_from_int_cell(&pointer, &value, value_type) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(value),
                facts,
                obligations,
            }];
        }
        if !value_type.accepts(&value) {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        }
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if pointer.has_symbolic_block() && has_external_read_resource {
        let Some(value) = symbolic_load_value(&memory, &pointer, value_type) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if let Some((stored_pointer, stored_value)) =
        memory.first_unresolved_same_block_cell(&pointer, assumptions)
    {
        let mut paths = Vec::new();

        let mut equal_facts = facts.clone();
        if add_pointer_offset_equality_execution_pure_facts(
            &mut equal_facts,
            assumptions,
            pointer.offset.clone(),
            stored_pointer.offset.clone(),
            true,
        )
        .is_some()
        {
            let equal_outcome = if let Some(value) =
                symbolic_pointer_value_from_int_cell(&pointer, &stored_value, value_type)
            {
                CExpressionOutcome::Value(value)
            } else if value_type.accepts(&stored_value) {
                CExpressionOutcome::Value(stored_value)
            } else {
                CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch)
            };
            paths.push(CExpressionPath {
                outcome: equal_outcome,
                facts: equal_facts,
                obligations: obligations.clone(),
            });
        }

        let mut distinct_facts = facts;
        if add_pointer_offset_equality_execution_pure_facts(
            &mut distinct_facts,
            assumptions,
            pointer.offset.clone(),
            stored_pointer.offset.clone(),
            false,
        )
        .is_some()
        {
            paths.extend(evaluate_c_memory_load_paths(
                &memory.without_cell(&stored_pointer),
                pointer,
                value_type,
                distinct_facts,
                obligations,
                assumptions,
                has_external_read_resource,
            ));
        }

        return paths;
    }

    if memory.is_loadable_concretely(&pointer, value_type.byte_width()) {
        let Some(value) = symbolic_load_value(&memory, &pointer, value_type) else {
            return vec![CExpressionPath {
                outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            }];
        };
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::Value(value),
            facts,
            obligations,
        }];
    }

    if !has_external_read_resource {
        let proposition = Proposition::CMemoryLoadable {
            memory: memory.clone(),
            base: pointer.clone(),
            bytes: Bitvector32Term::Constant(value_type.byte_width()),
        };
        if add_proof_obligation(&mut obligations, assumptions, proposition).is_none() {
            return Vec::new();
        }
    }

    let Some(value) = symbolic_load_value(&memory, &pointer, value_type) else {
        return vec![CExpressionPath {
            outcome: CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts,
            obligations,
        }];
    };

    vec![CExpressionPath {
        outcome: CExpressionOutcome::Value(value),
        facts,
        obligations,
    }]
}

fn symbolic_pointer_value_from_int_cell(
    pointer: &Pointer,
    value: &CValue,
    value_type: CType,
) -> Option<CValue> {
    let CValue::Int32(bits @ Bitvector32Term::MemoryLoad(_, _)) = value else {
        return None;
    };
    let pointee_byte_width = match value_type {
        CType::Int32Pointer => 4,
        CType::UInt8Pointer => 1,
        _ => return None,
    };
    Some(CValue::Pointer(Pointer {
        block: pointer.block.clone(),
        offset: PointerOffsetTerm::scale_int32(bits.clone(), i64::from(pointee_byte_width)),
    }))
}

pub(super) fn symbolic_load_value(
    memory: &CMemory,
    pointer: &Pointer,
    value_type: CType,
) -> Option<CValue> {
    match value_type {
        CType::Int32 => Some(memory.symbolic_int32_load(pointer)),
        CType::UInt8 => Some(memory.symbolic_uint8_load(pointer)),
        CType::Int32Pointer => Some(memory.symbolic_pointer_load(pointer, 4)),
        CType::UInt8Pointer => Some(memory.symbolic_pointer_load(pointer, 1)),
        CType::Int32Array(_) | CType::UInt8Array(_) => None,
    }
}

pub(super) fn evaluate_c_add_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
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

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn apply_c_add(
    left: CValue,
    right: CValue,
    left_step_width: Option<u32>,
    right_step_width: Option<u32>,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    match (left, right) {
        (
            left @ (CValue::Int32(_) | CValue::UInt8(_)),
            right @ (CValue::Int32(_) | CValue::UInt8(_)),
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
        (CValue::Pointer(pointer), offset @ (CValue::Int32(_) | CValue::UInt8(_))) => {
            let mut facts = facts;
            let Some(offset) = promote_c_int32_path_value(offset, &mut facts, assumptions) else {
                return Vec::new();
            };
            let byte_width = left_step_width.unwrap_or(4);
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(CValue::Pointer(
                    pointer.offset_by_elements(offset, byte_width),
                )),
                facts,
                obligations,
            }]
        }
        (offset @ (CValue::Int32(_) | CValue::UInt8(_)), CValue::Pointer(pointer)) => {
            let mut facts = facts;
            let Some(offset) = promote_c_int32_path_value(offset, &mut facts, assumptions) else {
                return Vec::new();
            };
            let byte_width = right_step_width.unwrap_or(4);
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(CValue::Pointer(
                    pointer.offset_by_elements(offset, byte_width),
                )),
                facts,
                obligations,
            }]
        }
        _ => vec![c_type_mismatch_expression_path(facts, obligations)],
    }
}

pub(super) fn apply_c_int32_add(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_add_overflows(left.clone(), right.clone());
    match decide_with_facts(assumptions, &facts, &overflow) {
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

pub(super) fn apply_c_int32_subtract(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
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

pub(super) fn apply_c_int32_multiply(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    let overflow = ConditionTerm::signed_multiply_overflows(left.clone(), right.clone());
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

pub(super) fn apply_c_int32_divide(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
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

pub(super) fn apply_c_int32_remainder(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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

pub(super) fn apply_c_int32_shift_left(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    apply_c_int32_with_valid_shift_count(
        left,
        right,
        facts,
        obligations,
        assumptions,
        apply_c_int32_shift_left_valid_count,
    )
}

pub(super) fn apply_c_int32_shift_right(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    apply_c_int32_with_valid_shift_count(
        left,
        right,
        facts,
        obligations,
        assumptions,
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

fn apply_c_int32_with_valid_shift_count(
    left: Bitvector32Term,
    right: Bitvector32Term,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
    apply_valid_count: ValidShiftCountEvaluator,
) -> Vec<CExpressionPath> {
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
    assumptions: &Assumptions,
    apply_valid_count: ValidShiftCountEvaluator,
) -> Vec<CExpressionPath> {
    let too_large_count =
        ConditionTerm::signed_greater_equal(right.clone(), Bitvector32Term::Constant(32));
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
    assumptions: &Assumptions,
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
    assumptions: &Assumptions,
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

pub(super) fn evaluate_c_equal_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExpressionOutcome::Value(left) => left,
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
                    paths.extend(apply_c_equal(
                        left.clone(),
                        right,
                        facts,
                        obligations,
                        assumptions,
                    ));
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

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn apply_c_equal(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    match (left, right) {
        (CValue::Pointer(left), CValue::Pointer(right)) => condition_as_c_int32_paths(
            pointer_equality_condition(left, right),
            facts,
            obligations,
            assumptions,
        ),
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            condition_as_c_int32_paths(
                pointer_is_null_condition(pointer),
                facts,
                obligations,
                assumptions,
            )
        }
        (
            left @ (CValue::Int32(_) | CValue::UInt8(_)),
            right @ (CValue::Int32(_) | CValue::UInt8(_)),
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

pub(super) fn evaluate_c_not_equal_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CExpressionPath>> {
    let mut paths = Vec::new();
    for left_path in evaluate_c_expression_paths(state, left, assumptions, budget)? {
        let CExpressionPath {
            outcome: left_outcome,
            facts: left_facts,
            obligations: left_obligations,
        } = left_path;

        let left = match left_outcome {
            CExpressionOutcome::Value(left) => left,
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
                    paths.extend(apply_c_not_equal(
                        left.clone(),
                        right,
                        facts,
                        obligations,
                        assumptions,
                    ));
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

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn apply_c_not_equal(
    left: CValue,
    right: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CExpressionPath> {
    match (left, right) {
        (CValue::Pointer(left), CValue::Pointer(right)) => condition_as_c_int32_not_paths(
            pointer_equality_condition(left, right),
            facts,
            obligations,
            assumptions,
        ),
        (CValue::Pointer(pointer), CValue::Int32(bits))
        | (CValue::Int32(bits), CValue::Pointer(pointer))
            if bits.as_const() == Some(0) =>
        {
            condition_as_c_int32_not_paths(
                pointer_is_null_condition(pointer),
                facts,
                obligations,
                assumptions,
            )
        }
        (
            left @ (CValue::Int32(_) | CValue::UInt8(_)),
            right @ (CValue::Int32(_) | CValue::UInt8(_)),
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

pub(super) fn evaluate_c_not_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
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

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn evaluate_c_logical_and_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
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

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn evaluate_c_logical_or_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
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

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn pointer_equality_condition(left: Pointer, right: Pointer) -> ConditionTerm {
    if left.block == right.block {
        ConditionTerm::pointer_offset_equal(left.offset, right.offset)
    } else {
        ConditionTerm::pointer_equal(left, right)
    }
}

pub(super) fn pointer_is_null_condition(pointer: Pointer) -> ConditionTerm {
    pointer_equality_condition(
        pointer,
        Pointer {
            block: "null".into(),
            offset: PointerOffsetTerm::Constant(0),
        },
    )
}

pub(super) fn evaluate_c_int32_binary_paths(
    state: &CState,
    left: &CExpression,
    right: &CExpression,
    assumptions: &Assumptions,
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

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn apply_c_int32_total_binary(
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

pub(super) fn evaluate_c_int32_total_unary_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &Assumptions,
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

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_statement(
    state: &CState,
    statement: &CStatement,
    assumptions: &Assumptions,
) -> Option<CStatementOutcome> {
    let paths = execute_c_statement_paths(
        state,
        statement,
        assumptions,
        &CExecutionEnvironment::new(),
        CExecutionSemantics::EXECUTE_BODIES,
        &mut ExecutionBudget::default(),
    )
    .ok()?;
    let mut paths = paths.into_iter();
    let path = paths.next()?;
    if paths.next().is_some() {
        return None;
    }
    Some(path.outcome)
}

pub(super) fn execute_c_lvalue_assignment_paths(
    state: &CState,
    target: &CExpression,
    value: &CExpression,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut paths = Vec::new();
    for target_path in evaluate_c_lvalue_paths(state, target, assumptions, budget)? {
        let CLValuePath {
            outcome: target_outcome,
            facts: target_facts,
            obligations: target_obligations,
        } = target_path;

        let target_lvalue = match target_outcome {
            CLValueOutcome::LValue(lvalue) => lvalue,
            CLValueOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts: target_facts,
                    obligations: target_obligations,
                });
                continue;
            }
            CLValueOutcome::RuntimeError(error) => {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(error),
                    facts: target_facts,
                    obligations: target_obligations,
                });
                continue;
            }
        };

        let value_assumptions =
            assumptions_with_path_context(assumptions, &target_facts, &target_obligations);
        for value_path in evaluate_c_expression_paths(state, value, &value_assumptions, budget)? {
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &target_facts,
                &target_obligations,
                &value_path.facts,
                &value_path.obligations,
                assumptions,
            ) else {
                continue;
            };

            match value_path.outcome {
                CExpressionOutcome::Value(value) => paths.extend(write_c_lvalue_paths(
                    state,
                    target_lvalue.clone(),
                    value,
                    facts,
                    obligations,
                    assumptions,
                )),
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CStatementExecutionPath {
                        outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    })
                }
                CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(error),
                    facts,
                    obligations,
                }),
            }
        }
    }
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn write_c_lvalue_paths(
    state: &CState,
    lvalue: CLValue,
    value: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &Assumptions,
) -> Vec<CStatementExecutionPath> {
    let mut obligations = obligations;
    let effective_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    let Some(value) = coerce_c_value_to_type(
        value,
        lvalue.value_type,
        &mut obligations,
        &effective_assumptions,
    ) else {
        return vec![CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts,
            obligations,
        }];
    };

    match lvalue.storage {
        CLValueStorage::Local { name } => {
            let mut state = state.clone();
            sync_stack_local(&mut state, &name, &value);
            state.locals.set_typed(name, value, lvalue.value_type);
            vec![CStatementExecutionPath {
                outcome: CStatementOutcome::Normal(state),
                facts,
                obligations,
            }]
        }
        CLValueStorage::Memory { pointer } => {
            let has_external_write_resource = is_external_memory_pointer(&pointer)
                && resource_context_has_write(
                    state.resources(),
                    &pointer,
                    value.byte_width(),
                    &effective_assumptions,
                );
            if is_external_memory_pointer(&pointer) && !has_external_write_resource {
                return vec![CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource: CResourceFact::own_memory(CMemoryRange::new(
                            pointer.clone(),
                            Bitvector32Term::Constant(0),
                            Bitvector32Term::Constant(1),
                        )),
                    }),
                    facts,
                    obligations,
                }];
            }
            let obligations = if has_external_write_resource {
                obligations
            } else {
                let Some(obligations) = add_memory_store_obligation(
                    &state.memory,
                    &pointer,
                    &value,
                    obligations,
                    &effective_assumptions,
                ) else {
                    return Vec::new();
                };
                obligations
            };
            let before_memory = state.memory.clone();
            let mut state = state.clone();
            state.memory = state
                .memory
                .without_possible_aliasing_cells(&pointer, &effective_assumptions)
                .store(pointer.clone(), value.clone());
            let mut facts = facts;
            if add_internal_path_fact(
                &mut facts,
                assumptions,
                Proposition::CMemoryMutatesOnly {
                    before: before_memory,
                    after: state.memory.clone(),
                    pointers: vec![pointer.clone()],
                },
            )
            .is_none()
            {
                return Vec::new();
            }
            if let Some(name) = local_name_from_pointer(&pointer)
                && let Some(c_type) = state.locals.scalar_object_type(name)
            {
                state.locals.set_typed(name.to_string(), value, c_type);
            }
            vec![CStatementExecutionPath {
                outcome: CStatementOutcome::Normal(state),
                facts,
                obligations,
            }]
        }
    }
}

fn is_external_memory_pointer(pointer: &Pointer) -> bool {
    !pointer.block.starts_with("local:") && !pointer.block.starts_with("havoc:")
}

pub(super) fn local_name_from_pointer(pointer: &Pointer) -> Option<&str> {
    if pointer.offset != PointerOffsetTerm::Constant(0) {
        return None;
    }
    pointer.block.strip_prefix("local:")
}

pub(super) fn execute_c_statement_paths(
    state: &CState,
    statement: &CStatement,
    assumptions: &Assumptions,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    budget.consume_statement_step()?;
    let paths = match statement {
        CStatement::Declare { name, c_type } => vec![CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(declare_local(state, name, *c_type)),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CStatement::Assign { name, expression } => execute_c_lvalue_assignment_paths(
            state,
            &c_variable(name.clone()),
            expression,
            assumptions,
            budget,
        )?,
        CStatement::CallAssign {
            target,
            function_name,
            arguments,
        } => execute_c_call_assign_paths(
            state,
            target,
            function_name,
            arguments,
            assumptions,
            environment,
            execution_semantics,
            budget,
        )?,
        CStatement::Assert { condition, label } => {
            execute_c_assert_paths(state, condition, label.as_deref(), assumptions, budget)?
        }
        CStatement::Seq(first, second) => {
            let mut paths = Vec::new();
            for first_path in execute_c_statement_paths(
                state,
                first,
                assumptions,
                environment,
                execution_semantics,
                budget,
            )? {
                match first_path.outcome {
                    CStatementOutcome::Normal(state) => {
                        paths.extend(execute_c_statement_paths_with_prefix(
                            &state,
                            second,
                            assumptions,
                            environment,
                            execution_semantics,
                            &first_path.facts,
                            &first_path.obligations,
                            budget,
                        )?);
                    }
                    outcome @ (CStatementOutcome::Return { .. }
                    | CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)) => paths.push(CStatementExecutionPath {
                        outcome,
                        facts: first_path.facts,
                        obligations: first_path.obligations,
                    }),
                }
            }
            paths
        }
        CStatement::Return(expression) => {
            evaluate_c_expression_paths(state, expression, assumptions, budget)?
                .into_iter()
                .map(|path| CStatementExecutionPath {
                    outcome: match path.outcome {
                        CExpressionOutcome::Value(value) => CStatementOutcome::Return {
                            value,
                            state: state.clone(),
                        },
                        CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                            CStatementOutcome::UndefinedBehavior(undefined_behavior)
                        }
                        CExpressionOutcome::RuntimeError(error) => {
                            CStatementOutcome::RuntimeError(error)
                        }
                    },
                    facts: path.facts,
                    obligations: path.obligations,
                })
                .collect()
        }
        CStatement::Store { pointer, value } => execute_c_lvalue_assignment_paths(
            state,
            &CExpression::Load(Box::new(pointer.clone())),
            value,
            assumptions,
            budget,
        )?,
        CStatement::TypedStore {
            pointer,
            value,
            value_type,
        } => execute_c_lvalue_assignment_paths(
            state,
            &CExpression::TypedLoad {
                pointer: Box::new(pointer.clone()),
                value_type: *value_type,
            },
            value,
            assumptions,
            budget,
        )?,
        CStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            let mut paths = Vec::new();
            for condition_path in
                evaluate_c_expression_paths(state, condition, assumptions, budget)?
            {
                let CExpressionPath {
                    outcome,
                    facts,
                    obligations,
                } = condition_path;
                match outcome {
                    CExpressionOutcome::Value(value) => {
                        let truthiness_paths =
                            c_truthiness_paths(value, facts, obligations, assumptions);
                        for truthiness_path in truthiness_paths {
                            let branch = if truthiness_path.is_true {
                                then_branch
                            } else {
                                else_branch
                            };
                            paths.extend(execute_c_statement_paths_with_prefix(
                                state,
                                branch,
                                assumptions,
                                environment,
                                execution_semantics,
                                &truthiness_path.facts,
                                &truthiness_path.obligations,
                                budget,
                            )?);
                        }
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                            facts,
                            obligations,
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(error),
                            facts,
                            obligations,
                        })
                    }
                }
            }
            paths
        }
        CStatement::While {
            condition,
            invariant,
            invariant_checks: _,
            effect_checks: _,
            body,
        } => execute_c_while_paths(
            state,
            condition,
            invariant,
            body,
            assumptions,
            environment,
            execution_semantics,
            budget,
        )?,
    };
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_assert_paths(
    state: &CState,
    condition: &CExpression,
    label: Option<&str>,
    assumptions: &Assumptions,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut paths = Vec::new();
    for condition_path in evaluate_c_expression_paths(state, condition, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = condition_path;
        match outcome {
            CExpressionOutcome::Value(value) => {
                let assertion_obligation = assertion_truthiness_obligation(&value, label);
                for truthiness_path in c_truthiness_paths(value, facts, obligations, assumptions) {
                    let mut obligations = truthiness_path.obligations;
                    if !truthiness_path.is_true {
                        obligations.push(assertion_obligation.clone());
                    }
                    paths.push(CStatementExecutionPath {
                        outcome: CStatementOutcome::Normal(state.clone()),
                        facts: truthiness_path.facts,
                        obligations,
                    });
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts,
                    obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(error),
                facts,
                obligations,
            }),
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn assertion_truthiness_obligation(
    value: &CValue,
    label: Option<&str>,
) -> ProofObligation {
    let obligation = ProofObligation::verification_condition(Proposition::Equal(
        Term::CValue(value.clone()),
        Term::CValue(int32(1)),
    ));
    match label {
        Some(label) => obligation.with_context(label),
        None => obligation,
    }
}

pub(super) fn execute_c_while_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    body: &CStatement,
    assumptions: &Assumptions,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    budget.consume_loop_unroll()?;

    let mut base_obligations = Vec::new();
    for proposition in invariant {
        if add_proof_obligation(&mut base_obligations, assumptions, proposition.clone()).is_none() {
            return Ok(Vec::new());
        }
    }
    let loop_assumptions = assumptions_with_propositions(assumptions, invariant);
    let mut paths = Vec::new();

    for condition_path in evaluate_c_expression_paths(state, condition, &loop_assumptions, budget)?
    {
        let Some((condition_facts, condition_obligations)) =
            merge_execution_pure_facts_and_obligations(
                &[],
                &base_obligations,
                &condition_path.facts,
                &condition_path.obligations,
                assumptions,
            )
        else {
            continue;
        };

        match condition_path.outcome {
            CExpressionOutcome::Value(value) => {
                let truthiness_paths =
                    c_truthiness_paths(value, condition_facts, condition_obligations, assumptions);
                for truthiness_path in truthiness_paths {
                    if truthiness_path.is_true {
                        paths.extend(execute_c_while_body_paths(
                            state,
                            condition,
                            invariant,
                            body,
                            assumptions,
                            environment,
                            execution_semantics,
                            truthiness_path.facts,
                            truthiness_path.obligations,
                            budget,
                        )?);
                    } else {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::Normal(state.clone()),
                            facts: truthiness_path.facts,
                            obligations: truthiness_path.obligations,
                        });
                    }
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts: condition_facts,
                    obligations: condition_obligations,
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(error),
                facts: condition_facts,
                obligations: condition_obligations,
            }),
        }
    }

    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn execute_c_while_body_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    body: &CStatement,
    assumptions: &Assumptions,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let body_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    let mut paths = Vec::new();
    for body_path in execute_c_statement_paths(
        state,
        body,
        &body_assumptions,
        environment,
        execution_semantics,
        budget,
    )? {
        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
            &facts,
            &obligations,
            &body_path.facts,
            &body_path.obligations,
            assumptions,
        ) else {
            continue;
        };

        match body_path.outcome {
            CStatementOutcome::Normal(next_state) => {
                let next_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                for path in execute_c_while_paths(
                    &next_state,
                    condition,
                    invariant,
                    body,
                    &next_assumptions,
                    environment,
                    execution_semantics,
                    budget,
                )? {
                    let (facts, obligations) = merge_execution_pure_facts_and_obligations(
                        &facts,
                        &obligations,
                        &path.facts,
                        &path.obligations,
                        assumptions,
                    )
                    .expect("merged loop execution pure facts should remain consistent");
                    paths.push(CStatementExecutionPath {
                        outcome: path.outcome,
                        facts,
                        obligations,
                    });
                }
            }
            outcome @ (CStatementOutcome::Return { .. }
            | CStatementOutcome::UndefinedBehavior(_)
            | CStatementOutcome::RuntimeError(_)) => paths.push(CStatementExecutionPath {
                outcome,
                facts,
                obligations,
            }),
        }
    }
    budget.consume_paths(paths.len())?;
    Ok(paths)
}

pub(super) fn declare_local(state: &CState, name: &str, c_type: CType) -> CState {
    let mut state = state.clone();
    let (initial_value, byte_width) = match c_type {
        CType::Int32 => (int32(0), 4),
        CType::UInt8 => (uint8(0), 1),
        CType::Int32Pointer => (
            CValue::Pointer(Pointer {
                block: "null".into(),
                offset: PointerOffsetTerm::Constant(0),
            }),
            C_POINTER_BYTE_WIDTH,
        ),
        CType::UInt8Pointer => (
            CValue::Pointer(Pointer {
                block: "null".into(),
                offset: PointerOffsetTerm::Constant(0),
            }),
            C_POINTER_BYTE_WIDTH,
        ),
        CType::Int32Array(length) => {
            let pointer = CMemory::local_pointer(name);
            state.memory = state
                .memory
                .with_block(pointer.block, length.saturating_mul(4));
            state
                .locals
                .set_array_object(name.to_string(), CType::Int32, length);
            return state;
        }
        CType::UInt8Array(length) => {
            let pointer = CMemory::local_pointer(name);
            state.memory = state.memory.with_block(pointer.block, length);
            state
                .locals
                .set_array_object(name.to_string(), CType::UInt8, length);
            return state;
        }
    };
    let pointer = CMemory::local_pointer(name);
    state.memory = state
        .memory
        .with_block(pointer.block.clone(), byte_width)
        .store(pointer, initial_value.clone());
    state
        .locals
        .set_typed(name.to_string(), initial_value, c_type);
    state
}

pub(super) fn sync_stack_local(state: &mut CState, name: &str, value: &CValue) {
    let pointer = CMemory::local_pointer(name);
    if state.memory.has_block(&pointer.block) {
        state.memory = state.memory.clone().store(pointer, value.clone());
    }
}
