use super::*;

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

pub(in crate::kernel) fn promote_c_int32_path_value(
    value: CValue,
    facts: &mut Vec<ExecutionPureFact>,
    assumptions: &PureFactContext,
) -> Option<Bitvector32Term> {
    match value {
        CValue::Void => None,
        CValue::Int32(value) => Some(value),
        CValue::UInt8(value) => {
            add_uint8_range_execution_pure_facts(facts, assumptions, &value)?;
            Some(value)
        }
        CValue::Pointer(_) => None,
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
        (CType::Int32, CValue::UInt8(value)) => Some(CValue::Int32(value)),
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

fn cast_c_value_to_type(
    value: CValue,
    target_type: CType,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<CValue> {
    if target_type.is_pointer() {
        if let CValue::Pointer(pointer) = value {
            return Some(CValue::typed_pointer(pointer.into_pointer(), target_type));
        }
    }
    coerce_c_value_to_type(value, target_type, obligations, assumptions)
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
        // An inline array field is an lvalue whose value is not represented by
        // CValue. In an expression context it undergoes C's array-to-pointer
        // conversion, so evaluate the field's address rather than attempting
        // to load an aggregate value.
        CExpression::TypedLoad {
            pointer,
            value_type: CType::Int32Array(_) | CType::UInt8Array(_),
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
                        CValue::UInt8(value) => promote_c_int32_path_value(
                            CValue::UInt8(value),
                            &mut facts,
                            &effective_assumptions,
                        )
                        .map(CValue::Int32),
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
                    Some(value) => CExpressionOutcome::Value(value),
                    None => CExpressionOutcome::RuntimeError(CRuntimeError::TypeMismatch),
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
                Some(CLocalBinding::Object { c_type, .. })
                | Some(CLocalBinding::UninitializedObject { c_type, .. }) => {
                    CLValueOutcome::LValue(CLValue::local(name.clone(), *c_type))
                }
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
                        outcome: CLValueOutcome::LValue(CLValue::memory(
                            pointer.pointer().clone(),
                            value_type,
                        )),
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
                        outcome: CLValueOutcome::LValue(CLValue::memory(
                            pointer.pointer().clone(),
                            *value_type,
                        )),
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
                        outcome: CLValueOutcome::LValue(CLValue::memory(
                            pointer.pointer().clone(),
                            value_type,
                        )),
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
            CLValueStorage::Local { name } => vec![CExpressionPath {
                outcome: match state.locals.get(name) {
                    Some(value) if lvalue.value_type.accepts(value) => {
                        CExpressionOutcome::Value(value.clone())
                    }
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
                },
                facts,
                obligations,
            }],
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
                evaluate_c_memory_load_paths(
                    &state.memory,
                    pointer.clone(),
                    lvalue.value_type,
                    facts,
                    obligations,
                    assumptions,
                    has_external_read_resource,
                    next_kernel_variable,
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
                Some(pointer) => CExpressionPath {
                    outcome: CExpressionOutcome::Value(CValue::typed_pointer(
                        pointer,
                        lvalue
                            .value_type()
                            .pointer_to()
                            .unwrap_or(CType::Int32Pointer),
                    )),
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
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn is_external_memory_pointer(pointer: &Pointer) -> bool {
    !pointer.block.starts_with("local:") && !pointer.block.starts_with("havoc:")
}

pub(in crate::kernel) fn c_expression_pointee_type(
    state: &CState,
    expression: &CExpression,
) -> Option<CType> {
    match expression {
        CExpression::Variable(name) => match state.locals.binding(name) {
            Some(CLocalBinding::Object { c_type, .. }) => c_type.pointee_type(),
            Some(CLocalBinding::UninitializedObject { c_type, .. }) => c_type.pointee_type(),
            Some(CLocalBinding::ArrayObject { element_type, .. }) => Some(*element_type),
            Some(CLocalBinding::AggregateObject { .. }) => Some(CType::UInt8),
            None => None,
        },
        CExpression::AddressOf(target) => c_expression_lvalue_type(state, target),
        CExpression::PointerOffsetBytes { pointer, .. } => {
            c_expression_pointee_type(state, pointer)
        }
        CExpression::TypedLoad { value_type, .. } => match value_type {
            CType::Int32Array(_) => Some(CType::Int32),
            CType::UInt8Array(_) => Some(CType::UInt8),
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
