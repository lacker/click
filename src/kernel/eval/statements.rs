use super::*;

pub(in crate::kernel) fn execute_c_statement(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
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

pub(in crate::kernel) fn execute_c_lvalue_assignment_paths(
    state: &CState,
    target: &CExpression,
    value: &CExpression,
    assumptions: &PureFactContext,
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
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn execute_c_lvalue_update_paths(
    state: &CState,
    target: &CExpression,
    operator: CUpdateOperator,
    operand: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut paths = Vec::new();
    for target_path in evaluate_c_lvalue_paths(state, target, assumptions, budget)? {
        let CLValuePath {
            outcome,
            facts,
            obligations,
        } = target_path;
        let CLValueOutcome::LValue(lvalue) = outcome else {
            let outcome = match outcome {
                CLValueOutcome::UndefinedBehavior(error) => {
                    CStatementOutcome::UndefinedBehavior(error)
                }
                CLValueOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
                CLValueOutcome::LValue(_) => unreachable!(),
            };
            paths.push(CStatementExecutionPath {
                outcome,
                facts,
                obligations,
            });
            continue;
        };
        if !matches!(lvalue.value_type, CType::Int32 | CType::UInt8) {
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            });
            continue;
        }

        for current_path in read_c_lvalue_paths(
            state,
            CLValueOutcome::LValue(lvalue.clone()),
            facts,
            obligations,
            assumptions,
            &mut budget.next_kernel_variable,
        ) {
            let CExpressionPath {
                outcome: current_outcome,
                facts: current_facts,
                obligations: current_obligations,
            } = current_path;
            let CExpressionOutcome::Value(current) = current_outcome else {
                let outcome = match current_outcome {
                    CExpressionOutcome::UndefinedBehavior(error) => {
                        CStatementOutcome::UndefinedBehavior(error)
                    }
                    CExpressionOutcome::RuntimeError(error) => {
                        CStatementOutcome::RuntimeError(error)
                    }
                    CExpressionOutcome::Value(_) => unreachable!(),
                };
                paths.push(CStatementExecutionPath {
                    outcome,
                    facts: current_facts,
                    obligations: current_obligations,
                });
                continue;
            };

            let operand_assumptions =
                assumptions_with_path_context(assumptions, &current_facts, &current_obligations);
            for operand_path in
                evaluate_c_expression_paths(state, operand, &operand_assumptions, budget)?
            {
                let CExpressionPath {
                    outcome: operand_outcome,
                    facts: operand_facts,
                    obligations: operand_obligations,
                } = operand_path;
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &current_facts,
                    &current_obligations,
                    &operand_facts,
                    &operand_obligations,
                    assumptions,
                ) else {
                    continue;
                };
                let CExpressionOutcome::Value(operand_value) = operand_outcome else {
                    let outcome = match operand_outcome {
                        CExpressionOutcome::UndefinedBehavior(error) => {
                            CStatementOutcome::UndefinedBehavior(error)
                        }
                        CExpressionOutcome::RuntimeError(error) => {
                            CStatementOutcome::RuntimeError(error)
                        }
                        CExpressionOutcome::Value(_) => unreachable!(),
                    };
                    paths.push(CStatementExecutionPath {
                        outcome,
                        facts,
                        obligations,
                    });
                    continue;
                };

                let update_expression = c_update_expression(
                    operator,
                    CExpression::Value(current.clone()),
                    CExpression::Value(operand_value),
                );
                let update_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                for result_path in evaluate_c_expression_paths(
                    state,
                    &update_expression,
                    &update_assumptions,
                    budget,
                )? {
                    let CExpressionPath {
                        outcome,
                        facts: result_facts,
                        obligations: result_obligations,
                    } = result_path;
                    let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                        &facts,
                        &obligations,
                        &result_facts,
                        &result_obligations,
                        assumptions,
                    ) else {
                        continue;
                    };
                    match outcome {
                        CExpressionOutcome::Value(value) => paths.extend(write_c_lvalue_paths(
                            state,
                            lvalue.clone(),
                            value,
                            facts,
                            obligations,
                            assumptions,
                        )),
                        CExpressionOutcome::UndefinedBehavior(error) => {
                            paths.push(CStatementExecutionPath {
                                outcome: CStatementOutcome::UndefinedBehavior(error),
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
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn c_update_expression(
    operator: CUpdateOperator,
    left: CExpression,
    right: CExpression,
) -> CExpression {
    let left = Box::new(left);
    let right = Box::new(right);
    match operator {
        CUpdateOperator::Add => CExpression::Add(left, right),
        CUpdateOperator::Subtract => CExpression::Subtract(left, right),
        CUpdateOperator::Multiply => CExpression::Multiply(left, right),
        CUpdateOperator::Divide => CExpression::Divide(left, right),
        CUpdateOperator::Remainder => CExpression::Remainder(left, right),
        CUpdateOperator::ShiftLeft => CExpression::ShiftLeft(left, right),
        CUpdateOperator::ShiftRight => CExpression::ShiftRight(left, right),
        CUpdateOperator::BitwiseAnd => CExpression::BitwiseAnd(left, right),
        CUpdateOperator::BitwiseOr => CExpression::BitwiseOr(left, right),
        CUpdateOperator::BitwiseXor => CExpression::BitwiseXor(left, right),
    }
}

pub(in crate::kernel) fn write_c_lvalue_paths(
    state: &CState,
    lvalue: CLValue,
    value: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CStatementExecutionPath> {
    let mut obligations = obligations;
    let effective_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    // The current owned resource composition is proof authority for memory
    // separation even when callers retain only surface-synthesizable pure facts.
    // Attach its compact carrier directly while executing a write instead of
    // depending on eagerly materialized pair propositions.
    let resource_facts = state
        .resources()
        .observable_facts_assuming_valid(&effective_assumptions);
    let effective_assumptions = resource_facts
        .into_iter()
        .fold(effective_assumptions, |assumptions, fact| {
            assumptions.assume_proposition(fact)
        });
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
            if state
                .memory
                .heap
                .pending_reallocations
                .values()
                .any(|pending| pending.old_pointer.block == pointer.block)
            {
                return vec![CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(
                        CRuntimeError::UnresolvedAllocationOutcome,
                    ),
                    facts,
                    obligations,
                }];
            }
            if state.memory.is_deallocated_heap_address(&pointer) {
                return vec![CStatementExecutionPath {
                    outcome: CStatementOutcome::UndefinedBehavior(
                        CUndefinedBehavior::InvalidMemory,
                    ),
                    facts,
                    obligations,
                }];
            }
            let is_external = is_external_memory_pointer(&pointer);
            let authorized_range = is_external
                .then(|| {
                    state.resources().memory_write_range(
                        &pointer,
                        value.byte_width(),
                        &effective_assumptions,
                    )
                })
                .flatten()
                .cloned();
            let has_external_write_resource = is_external && authorized_range.is_some();
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
                .store_with_context(pointer.clone(), value.clone(), &effective_assumptions);
            let mut facts = facts;
            facts.push(ExecutionPureFact::certified_store(
                before_memory,
                state.memory.clone(),
                pointer.clone(),
                value.clone(),
                authorized_range,
            ));
            if let Some(name) = state.locals.name_for_slot(&pointer)
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

pub(super) fn execute_c_heap_allocate_paths(
    state: &CState,
    target: &str,
    bytes_expression: &CExpression,
    zeroed: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    if state.local_object_type(target) != Some(CType::Int32Pointer) {
        return Ok(vec![CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }

    let element_count_expression = match bytes_expression {
        CExpression::Multiply(left, right)
            if right.as_ref() == &CExpression::Value(int32(CType::Int32.byte_width())) =>
        {
            Some(left.as_ref())
        }
        CExpression::Multiply(left, right)
            if left.as_ref() == &CExpression::Value(int32(CType::Int32.byte_width())) =>
        {
            Some(right.as_ref())
        }
        _ => None,
    };
    let evaluated_size_expression = element_count_expression.unwrap_or(bytes_expression);
    let mut paths = Vec::new();
    for size_path in
        evaluate_c_expression_paths(state, evaluated_size_expression, assumptions, budget)?
    {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = size_path;
        let CExpressionOutcome::Value(CValue::Int32(size)) = outcome else {
            let outcome = match outcome {
                CExpressionOutcome::UndefinedBehavior(error) => {
                    CStatementOutcome::UndefinedBehavior(error)
                }
                CExpressionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
                CExpressionOutcome::Value(_) => {
                    CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                }
            };
            paths.push(CStatementExecutionPath {
                outcome,
                facts,
                obligations,
            });
            continue;
        };
        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        let (bytes, valid_size) = if element_count_expression.is_some() {
            let positive = effective_assumptions.decide(&ConditionTerm::signed_greater_than(
                size.clone(),
                Bitvector32Term::Constant(0),
            )) == Some(true);
            let fits = effective_assumptions.decide(&ConditionTerm::signed_less_equal(
                size.clone(),
                Bitvector32Term::Constant(i32::MAX as u32 / CType::Int32.byte_width()),
            )) == Some(true);
            (
                Bitvector32Term::multiply(
                    size,
                    Bitvector32Term::Constant(CType::Int32.byte_width()),
                ),
                positive && fits,
            )
        } else {
            let valid = int32_element_count_from_bytes(&size).is_some()
                && effective_assumptions.decide(&ConditionTerm::signed_greater_than(
                    size.clone(),
                    Bitvector32Term::Constant(0),
                )) == Some(true);
            (size, valid)
        };
        if !valid_size {
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            });
            continue;
        }

        while state
            .memory
            .heap_identity_in_use(budget.next_kernel_variable)
        {
            budget.next_kernel_variable += 1;
        }
        let pointer = Pointer::symbolic(Variable(budget.next_kernel_variable));
        budget.next_kernel_variable += 1;
        let success_state =
            state
                .clone()
                .with_memory(state.memory.clone().with_pending_heap_allocation(
                    pointer.clone(),
                    bytes,
                    zeroed,
                ));
        let assigned = execute_c_lvalue_assignment_paths(
            &success_state,
            &c_variable(target.to_string()),
            &CExpression::Value(CValue::Pointer(pointer)),
            &effective_assumptions,
            budget,
        )?;
        for assigned_path in assigned {
            let Some((merged_facts, merged_obligations)) =
                merge_execution_pure_facts_and_obligations(
                    &facts,
                    &obligations,
                    &assigned_path.facts,
                    &assigned_path.obligations,
                    assumptions,
                )
            else {
                continue;
            };
            paths.push(CStatementExecutionPath {
                outcome: assigned_path.outcome,
                facts: merged_facts,
                obligations: merged_obligations,
            });
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(crate) fn execute_c_realloc_assign_paths(
    state: &CState,
    target: &str,
    arguments: &[CExpression],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let [old_expression, size_expression] = arguments else {
        return Ok(vec![CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: 2,
                actual: arguments.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    };
    if state.local_object_type(target) != Some(CType::Int32Pointer) {
        return Ok(vec![CStatementExecutionPath {
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts: Vec::new(),
            obligations: Vec::new(),
        }]);
    }

    let mut paths = Vec::new();
    for old_path in evaluate_c_expression_paths(state, old_expression, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = old_path;
        let CExpressionOutcome::Value(old_value) = outcome else {
            let outcome = match outcome {
                CExpressionOutcome::UndefinedBehavior(error) => {
                    CStatementOutcome::UndefinedBehavior(error)
                }
                CExpressionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
                CExpressionOutcome::Value(_) => unreachable!(),
            };
            paths.push(CStatementExecutionPath {
                outcome,
                facts,
                obligations,
            });
            continue;
        };

        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        let old_pointer = match old_value {
            CValue::Pointer(pointer) => pointer,
            CValue::Int32(bits) if bits.as_const() == Some(0) => Pointer::null(),
            _ => {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts,
                    obligations,
                });
                continue;
            }
        };

        // C specifies realloc(NULL, size) as an allocation. Reuse the
        // existing pending-allocation machinery so a later null check can
        // resolve this branch just like malloc/calloc.
        if old_pointer == Pointer::null() {
            for allocation_path in execute_c_heap_allocate_paths(
                state,
                target,
                size_expression,
                false,
                &effective_assumptions,
                budget,
            )? {
                let Some((merged_facts, merged_obligations)) =
                    merge_execution_pure_facts_and_obligations(
                        &facts,
                        &obligations,
                        &allocation_path.facts,
                        &allocation_path.obligations,
                        assumptions,
                    )
                else {
                    continue;
                };
                paths.push(CStatementExecutionPath {
                    outcome: allocation_path.outcome,
                    facts: merged_facts,
                    obligations: merged_obligations,
                });
            }
            continue;
        }

        let Some(old_bytes) = state.memory.live_heap_block_size(&old_pointer).cloned() else {
            let error = if state.memory.is_deallocated_heap_address(&old_pointer) {
                CInvalidFree::DoubleFree
            } else if state.memory.is_live_heap_address(&old_pointer) {
                CInvalidFree::InteriorPointer
            } else {
                CInvalidFree::NonHeapPointer
            };
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(error)),
                facts,
                obligations,
            });
            continue;
        };
        let Some(old_count) = int32_element_count_from_bytes(&old_bytes) else {
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,
            });
            continue;
        };
        for new_size_path in
            evaluate_c_expression_paths(state, size_expression, &effective_assumptions, budget)?
        {
            let CExpressionPath {
                outcome: new_size_outcome,
                facts: size_facts,
                obligations: size_obligations,
            } = new_size_path;
            let CExpressionOutcome::Value(CValue::Int32(new_bytes)) = new_size_outcome else {
                let outcome = match new_size_outcome {
                    CExpressionOutcome::UndefinedBehavior(error) => {
                        CStatementOutcome::UndefinedBehavior(error)
                    }
                    CExpressionOutcome::RuntimeError(error) => {
                        CStatementOutcome::RuntimeError(error)
                    }
                    CExpressionOutcome::Value(_) => {
                        CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                    }
                };
                let Some((merged_facts, merged_obligations)) =
                    merge_execution_pure_facts_and_obligations(
                        &facts,
                        &obligations,
                        &size_facts,
                        &size_obligations,
                        assumptions,
                    )
                else {
                    continue;
                };
                paths.push(CStatementExecutionPath {
                    outcome,
                    facts: merged_facts,
                    obligations: merged_obligations,
                });
                continue;
            };
            let Some(new_count) = int32_element_count_from_bytes(&new_bytes) else {
                let Some((merged_facts, merged_obligations)) =
                    merge_execution_pure_facts_and_obligations(
                        &facts,
                        &obligations,
                        &size_facts,
                        &size_obligations,
                        assumptions,
                    )
                else {
                    continue;
                };
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts: merged_facts,
                    obligations: merged_obligations,
                });
                continue;
            };
            let all_facts = merge_facts(&facts, &size_facts, assumptions);
            let Some(all_facts) = all_facts else {
                continue;
            };
            let Some(all_obligations) =
                merge_obligations(&obligations, &size_obligations, &effective_assumptions)
            else {
                continue;
            };
            let effective_assumptions =
                assumptions_with_path_context(assumptions, &all_facts, &all_obligations);
            if effective_assumptions.decide(&ConditionTerm::signed_greater_than(
                new_count,
                Bitvector32Term::Constant(0),
            )) != Some(true)
            {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts: all_facts,
                    obligations: all_obligations,
                });
                continue;
            }
            let zeroed_source = if state.memory.heap.zeroed_allocations.contains(&old_pointer) {
                Some(old_bytes.clone())
            } else {
                state
                    .memory
                    .heap
                    .zeroed_prefix_allocations
                    .get(&old_pointer)
                    .cloned()
            };
            let zeroed_prefix = match zeroed_source {
                None => None,
                Some(old_prefix) => {
                    let (Some(old_prefix), Some(new_bytes)) =
                        (old_prefix.as_const(), new_bytes.as_const())
                    else {
                        paths.push(CStatementExecutionPath {
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: all_facts,
                            obligations: all_obligations,
                        });
                        continue;
                    };
                    Some(Bitvector32Term::Constant(old_prefix.min(new_bytes)))
                }
            };

            let allocation = CResourceFact::own_allocation(old_pointer.clone(), old_bytes.clone());
            let Some(resources) = state
                .resources
                .clone()
                .without_fact(&allocation, &effective_assumptions)
            else {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource: allocation,
                    }),
                    facts: all_facts,
                    obligations: all_obligations,
                });
                continue;
            };
            let complete_access = CResourceFact::own_memory(CMemoryRange::new(
                old_pointer.clone(),
                Bitvector32Term::Constant(0),
                old_count.clone(),
            ));
            let Some(resources) = resources.without_fact(&complete_access, &effective_assumptions)
            else {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource: complete_access,
                    }),
                    facts: all_facts,
                    obligations: all_obligations,
                });
                continue;
            };
            let resource_assumptions = state
                .resources()
                .observable_facts_assuming_valid(&effective_assumptions)
                .into_iter()
                .fold(effective_assumptions.clone(), |assumptions, fact| {
                    assumptions.assume_proposition(fact)
                });
            if let Some(stale) = resources.facts().iter().find(|resource| {
                resource.may_refer_to_memory_block(&old_pointer.block)
                    && !resource.is_proven_separate_from_allocation(
                        &old_pointer,
                        &old_bytes,
                        &resource_assumptions,
                    )
            }) {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(
                        CRuntimeError::StaleResourceAfterFree {
                            resource: stale.clone(),
                        },
                    ),
                    facts: all_facts,
                    obligations: all_obligations,
                });
                continue;
            }

            let old_cells = state
                .memory
                .cells
                .iter()
                .filter(|(pointer, _)| pointer.block == old_pointer.block)
                .map(|(pointer, value)| (pointer.offset.clone(), value.clone()))
                .collect::<Vec<_>>();
            let mut copied_cells = Vec::new();
            let mut copy_is_unsupported = false;
            for (offset, value) in old_cells {
                let Some(offset) = offset
                    .as_const()
                    .and_then(|offset| u32::try_from(offset).ok())
                else {
                    copy_is_unsupported = true;
                    break;
                };
                let Some(end) = offset.checked_add(value.byte_width()) else {
                    continue;
                };
                let fits = effective_assumptions.decide(&ConditionTerm::signed_less_equal(
                    Bitvector32Term::Constant(end),
                    new_bytes.clone(),
                ));
                if fits == Some(true) {
                    copied_cells.push((offset, value));
                } else if fits == Some(false)
                    || effective_assumptions.decide(&ConditionTerm::signed_less_than(
                        new_bytes.clone(),
                        Bitvector32Term::Constant(end),
                    )) == Some(true)
                {
                    // The initialized cell lies in the truncated tail and is
                    // intentionally not copied.
                } else {
                    copy_is_unsupported = true;
                    break;
                }
            }
            if copy_is_unsupported {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts: all_facts,
                    obligations: all_obligations,
                });
                continue;
            }

            while state
                .memory
                .heap_identity_in_use(budget.next_kernel_variable)
            {
                budget.next_kernel_variable += 1;
            }
            let pending_pointer = Pointer::symbolic(Variable(budget.next_kernel_variable));
            budget.next_kernel_variable += 1;
            let pending_memory = state
                .memory
                .clone()
                .with_pending_heap_allocation(pending_pointer.clone(), new_bytes.clone(), false)
                .with_pending_heap_reallocation(
                    pending_pointer.clone(),
                    old_pointer.clone(),
                    old_bytes.clone(),
                    zeroed_prefix,
                    copied_cells
                        .into_iter()
                        .map(|(offset, value)| {
                            (PointerOffsetTerm::Constant(i64::from(offset)), value)
                        })
                        .collect(),
                );
            let pending_state = state.clone().with_memory(pending_memory);
            let assigned = execute_c_lvalue_assignment_paths(
                &pending_state,
                &c_variable(target.to_string()),
                &CExpression::Value(CValue::Pointer(pending_pointer)),
                &effective_assumptions,
                budget,
            )?;
            for assigned_path in assigned {
                let Some((merged_facts, merged_obligations)) =
                    merge_execution_pure_facts_and_obligations(
                        &all_facts,
                        &all_obligations,
                        &assigned_path.facts,
                        &assigned_path.obligations,
                        assumptions,
                    )
                else {
                    continue;
                };
                paths.push(CStatementExecutionPath {
                    outcome: assigned_path.outcome,
                    facts: merged_facts,
                    obligations: merged_obligations,
                });
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn execute_c_heap_free_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            mut facts,
            obligations,
        } = path;
        let outcome = match outcome {
            CExpressionOutcome::Value(CValue::Int32(bits)) if bits.as_const() == Some(0) => {
                CExpressionOutcome::Value(CValue::Pointer(Pointer::null()))
            }
            outcome => outcome,
        };
        let CExpressionOutcome::Value(CValue::Pointer(pointer)) = outcome else {
            let outcome = match outcome {
                CExpressionOutcome::UndefinedBehavior(error) => {
                    CStatementOutcome::UndefinedBehavior(error)
                }
                CExpressionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
                CExpressionOutcome::Value(_) => {
                    CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                }
            };
            paths.push(CStatementExecutionPath {
                outcome,
                facts,
                obligations,
            });
            continue;
        };

        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        if pointer == Pointer::null()
            || effective_assumptions.decide(&pointer_is_null_condition(pointer.clone()))
                == Some(true)
        {
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::Normal(state.clone()),
                facts,
                obligations,
            });
            continue;
        }

        if state
            .memory
            .heap
            .pending_reallocations
            .values()
            .any(|pending| pending.old_pointer.block == pointer.block)
        {
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(
                    CRuntimeError::UnresolvedAllocationOutcome,
                ),
                facts,
                obligations,
            });
            continue;
        }

        let declared_allocation = state
            .resources
            .facts()
            .iter()
            .filter_map(|fact| fact.allocation())
            .find(|(base, _)| **base == pointer)
            .map(|(_, bytes)| bytes.clone());
        let before_free = state.memory.clone();
        let mut working_memory = state.memory.clone();
        let bytes = if let Some(bytes) = working_memory.live_heap_block_size(&pointer) {
            bytes.clone()
        } else if working_memory.is_deallocated_heap_address(&pointer) {
            let error = CInvalidFree::DoubleFree;
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(error)),
                facts,
                obligations,
            });
            continue;
        } else if working_memory.is_live_heap_address(&pointer) {
            let error = CInvalidFree::InteriorPointer;
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(error)),
                facts,
                obligations,
            });
            continue;
        } else if let Some(bytes) = declared_allocation {
            let Some(memory) =
                working_memory.with_heap_allocation_claim(pointer.clone(), bytes.clone())
            else {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(
                        CInvalidFree::NonHeapPointer,
                    )),
                    facts,
                    obligations,
                });
                continue;
            };
            working_memory = memory;
            bytes
        } else {
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(
                    CInvalidFree::NonHeapPointer,
                )),
                facts,
                obligations,
            });
            continue;
        };
        let allocation = CResourceFact::own_allocation(pointer.clone(), bytes.clone());
        let Some(resources) = state
            .resources
            .clone()
            .without_fact(&allocation, &effective_assumptions)
        else {
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                    resource: allocation,
                }),
                facts,
                obligations,
            });
            continue;
        };
        let complete_access = CResourceFact::own_memory(CMemoryRange::new(
            pointer.clone(),
            Bitvector32Term::Constant(0),
            int32_element_count_from_bytes(&bytes)
                .expect("supported allocations have an exact int32 element count"),
        ));
        let Some(resources) = resources.without_fact(&complete_access, &effective_assumptions)
        else {
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                    resource: complete_access,
                }),
                facts,
                obligations,
            });
            continue;
        };
        let resource_assumptions = state
            .resources()
            .observable_facts_assuming_valid(&effective_assumptions)
            .into_iter()
            .fold(effective_assumptions.clone(), |assumptions, fact| {
                assumptions.assume_proposition(fact)
            });
        if let Some(stale) = resources.facts().iter().find(|resource| {
            resource.may_refer_to_memory_block(&pointer.block)
                && !resource.is_proven_separate_from_allocation(
                    &pointer,
                    &bytes,
                    &resource_assumptions,
                )
        }) {
            paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::StaleResourceAfterFree {
                    resource: stale.clone(),
                }),
                facts,
                obligations,
            });
            continue;
        }
        let memory = working_memory
            .free_heap_block(&pointer)
            .expect("validated live heap base should free");
        facts.push(ExecutionPureFact::internal(
            Proposition::CHeapAllocationFreed {
                before: before_free,
                after: memory.clone(),
                allocation_base: pointer.clone(),
                bytes: bytes.clone(),
            },
        ));
        paths.push(CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(
                state
                    .clone()
                    .with_memory(memory)
                    .with_resource_context(resources),
            ),
            facts,
            obligations,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(crate) fn resolve_pending_heap_allocations(
    state: &CState,
    assumptions: &PureFactContext,
) -> CState {
    let pending = state
        .memory
        .heap
        .pending_allocations
        .iter()
        .map(|(base, bytes)| (base.clone(), bytes.clone()))
        .collect::<Vec<_>>();
    let mut state = state.clone();
    for (base, _) in pending {
        let Some(is_null) = assumptions.decide(&pointer_is_null_condition(base.clone())) else {
            continue;
        };
        if let Some(pending_reallocation) =
            state.memory.heap.pending_reallocations.get(&base).cloned()
        {
            let (memory, bytes, resolved_base, _) = state
                .memory
                .clone()
                .resolve_pending_heap_reallocation(&base, !is_null)
                .expect("collected pending reallocation should still exist");
            state.memory = memory;
            for binding in std::sync::Arc::make_mut(&mut state.locals.bindings).values_mut() {
                if let CLocalBinding::Object {
                    value: CValue::Pointer(pointer),
                    ..
                } = binding
                    && pointer == &base
                {
                    *pointer = resolved_base.clone();
                }
            }
            if !is_null {
                let old_allocation = CResourceFact::own_allocation(
                    pending_reallocation.old_pointer,
                    pending_reallocation.old_bytes.clone(),
                );
                let old_count = int32_element_count_from_bytes(&pending_reallocation.old_bytes)
                    .expect("supported reallocations have an exact int32 element count");
                let old_memory = CResourceFact::own_memory(CMemoryRange::new(
                    match old_allocation.allocation() {
                        Some((pointer, _)) => pointer.clone(),
                        None => unreachable!("allocation resource was just constructed"),
                    },
                    Bitvector32Term::Constant(0),
                    old_count,
                ));
                state.resources = state
                    .resources
                    .clone()
                    .without_fact(&old_allocation, assumptions)
                    .expect("validated realloc allocation resource should remain available")
                    .without_fact(&old_memory, assumptions)
                    .expect("validated realloc memory resource should remain available")
                    .unchecked_with_fact(CResourceFact::own_allocation(
                        resolved_base.clone(),
                        bytes.clone(),
                    ))
                    .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                        resolved_base,
                        Bitvector32Term::Constant(0),
                        int32_element_count_from_bytes(&bytes)
                            .expect("supported allocations have an exact int32 element count"),
                    )));
            }
            continue;
        }
        let (memory, bytes, resolved_base) = state
            .memory
            .clone()
            .resolve_pending_heap_allocation(&base, !is_null)
            .expect("collected pending allocation should still exist");
        state.memory = memory;
        for binding in std::sync::Arc::make_mut(&mut state.locals.bindings).values_mut() {
            if let CLocalBinding::Object {
                value: CValue::Pointer(pointer),
                ..
            } = binding
                && pointer == &base
            {
                *pointer = resolved_base.clone();
            }
        }
        if !is_null {
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::own_allocation(
                    resolved_base.clone(),
                    bytes.clone(),
                ))
                .unchecked_with_fact(CResourceFact::own_memory(CMemoryRange::new(
                    resolved_base,
                    Bitvector32Term::Constant(0),
                    int32_element_count_from_bytes(&bytes)
                        .expect("supported allocations have an exact int32 element count"),
                )));
        }
    }
    state
}

fn execute_c_return_expression_paths(
    state: &CState,
    expression: &CExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut paths = Vec::new();
    for expression_path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = expression_path;
        match outcome {
            CExpressionOutcome::Value(CValue::Pointer(pointer))
                if state.memory.heap.pending_allocations.contains_key(&pointer) =>
            {
                for truthiness_path in pending_allocation_outcome_paths(
                    pointer.clone(),
                    facts,
                    obligations,
                    assumptions,
                ) {
                    let path_assumptions = assumptions_with_path_context(
                        assumptions,
                        &truthiness_path.facts,
                        &truthiness_path.obligations,
                    );
                    let resolved_state = resolve_pending_heap_allocations(state, &path_assumptions);
                    let resolved_pointer = if truthiness_path.is_true {
                        let PointerBlock::Symbolic(Variable(identity)) = pointer.block else {
                            unreachable!("pending malloc results have symbolic heap identities");
                        };
                        Pointer {
                            block: PointerBlock::Heap(identity),
                            offset: PointerOffsetTerm::Constant(0),
                        }
                    } else {
                        Pointer::null()
                    };
                    let outcome = if resolved_state.memory.has_pending_heap_allocation() {
                        CStatementOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome)
                    } else {
                        CStatementOutcome::Return {
                            value: CValue::Pointer(resolved_pointer),
                            state: resolved_state,
                        }
                    };
                    paths.push(CStatementExecutionPath {
                        outcome,
                        facts: truthiness_path.facts,
                        obligations: truthiness_path.obligations,
                    });
                }
            }
            CExpressionOutcome::Value(value) => {
                let outcome = if state.memory.has_pending_heap_allocation() {
                    CStatementOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome)
                } else {
                    CStatementOutcome::Return {
                        value,
                        state: state.clone(),
                    }
                };
                paths.push(CStatementExecutionPath {
                    outcome,
                    facts,
                    obligations,
                });
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CStatementExecutionPath {
                    outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts,
                    obligations,
                });
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                outcome: CStatementOutcome::RuntimeError(error),
                facts,
                obligations,
            }),
        }
    }
    Ok(paths)
}

fn pending_allocation_outcome_paths(
    pointer: Pointer,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<CTruthinessPath> {
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
            // The pending symbolic pointer is an internal representation of
            // malloc's nondeterministic outcome. Unlike a C `if` condition,
            // this split does not expose a new source-level assumption: each
            // resolved return outcome is valid without making the temporary
            // symbolic identity part of the execution theorem.
            let mut success_facts = facts.clone();
            add_internal_condition_path_fact(
                &mut success_facts,
                assumptions,
                is_null.clone(),
                false,
            )
            .expect("unknown malloc success fact should be consistent");

            let mut failure_facts = facts;
            add_internal_condition_path_fact(&mut failure_facts, assumptions, is_null, true)
                .expect("unknown malloc failure fact should be consistent");

            vec![
                CTruthinessPath {
                    is_true: true,
                    facts: success_facts,
                    obligations: obligations.clone(),
                },
                CTruthinessPath {
                    is_true: false,
                    facts: failure_facts,
                    obligations,
                },
            ]
        }
    }
}

pub(in crate::kernel) fn execute_c_statement_paths(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    // `Seq` is the tree representation of a source block, not an executed C
    // statement. Charging it made the statement budget depend on tree shape
    // and counted every straight-line source statement twice.
    if !matches!(statement, CStatement::Seq(_, _)) {
        budget.consume_statement_step()?;
    }
    let paths = match statement {
        CStatement::Skip => vec![CStatementExecutionPath {
            outcome: CStatementOutcome::Normal(state.clone()),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CStatement::Break => vec![CStatementExecutionPath {
            outcome: CStatementOutcome::Break(state.clone()),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CStatement::Continue => vec![CStatementExecutionPath {
            outcome: CStatementOutcome::Continue(state.clone()),
            facts: Vec::new(),
            obligations: Vec::new(),
        }],
        CStatement::Declare { name, c_type } => {
            let outcome = if *c_type == CType::Void {
                CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
            } else {
                CStatementOutcome::Normal(declare_local(state, name, *c_type))
            };
            vec![CStatementExecutionPath {
                outcome,
                facts: Vec::new(),
                obligations: Vec::new(),
            }]
        }
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
        CStatement::Call {
            function_name,
            arguments,
        } => execute_c_call_paths(
            state,
            function_name,
            arguments,
            assumptions,
            environment,
            execution_semantics,
            budget,
        )?,
        CStatement::HeapAllocate {
            target,
            bytes,
            zeroed,
        } => execute_c_heap_allocate_paths(state, target, bytes, *zeroed, assumptions, budget)?,
        CStatement::HeapFree { pointer } => {
            execute_c_heap_free_paths(state, pointer, assumptions, budget)?
        }
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
                    outcome @ (CStatementOutcome::Break(_)
                    | CStatementOutcome::Continue(_)
                    | CStatementOutcome::Return { .. }
                    | CStatementOutcome::VerificationDiverges
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
        CStatement::Return(CExpression::Value(CValue::Void)) => {
            let outcome = if state.memory.has_pending_heap_allocation() {
                CStatementOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome)
            } else {
                CStatementOutcome::Return {
                    value: CValue::Void,
                    state: state.clone(),
                }
            };
            vec![CStatementExecutionPath {
                outcome,
                facts: Vec::new(),
                obligations: Vec::new(),
            }]
        }
        CStatement::Return(expression) => {
            execute_c_return_expression_paths(state, expression, assumptions, budget)?
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
        CStatement::Update {
            target,
            operator,
            operand,
        } => execute_c_lvalue_update_paths(state, target, *operator, operand, assumptions, budget)?,
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
                            let path_assumptions = assumptions_with_path_context(
                                assumptions,
                                &truthiness_path.facts,
                                &truthiness_path.obligations,
                            );
                            let branch_state =
                                resolve_pending_heap_allocations(state, &path_assumptions);
                            paths.extend(execute_c_statement_paths_with_prefix(
                                &branch_state,
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
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn execute_c_assert_paths(
    state: &CState,
    condition: &CExpression,
    label: Option<&str>,
    assumptions: &PureFactContext,
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

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn assertion_truthiness_obligation(
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

pub(in crate::kernel) fn execute_c_while_paths(
    state: &CState,
    condition: &CExpression,
    invariant: &[Proposition],
    body: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    struct PendingLoopPath {
        state: CState,
        facts: Vec<ExecutionPureFact>,
        obligations: Vec<ProofObligation>,
    }

    let mut pending = vec![PendingLoopPath {
        state: state.clone(),
        facts: Vec::new(),
        obligations: Vec::new(),
    }];
    let mut paths = Vec::new();

    while let Some(PendingLoopPath {
        state: current_state,
        facts: accumulated_facts,
        obligations: accumulated_obligations,
    }) = pending.pop()
    {
        budget.consume_loop_unroll()?;
        let current_assumptions = assumptions_with_path_context(
            assumptions,
            &accumulated_facts,
            &accumulated_obligations,
        );
        let mut base_obligations = Vec::new();
        let mut invariant_is_inconsistent = false;
        for proposition in invariant {
            if add_proof_obligation(
                &mut base_obligations,
                &current_assumptions,
                proposition.clone(),
            )
            .is_none()
            {
                invariant_is_inconsistent = true;
                break;
            }
        }
        if invariant_is_inconsistent {
            continue;
        }
        let loop_assumptions = assumptions_with_propositions(&current_assumptions, invariant);

        for condition_path in
            evaluate_c_expression_paths(&current_state, condition, &loop_assumptions, budget)?
        {
            let Some((condition_facts, condition_obligations)) =
                merge_execution_pure_facts_and_obligations(
                    &[],
                    &base_obligations,
                    &condition_path.facts,
                    &condition_path.obligations,
                    &current_assumptions,
                )
            else {
                continue;
            };

            match condition_path.outcome {
                CExpressionOutcome::Value(value) => {
                    let truthiness_paths = c_truthiness_paths(
                        value,
                        condition_facts,
                        condition_obligations,
                        &current_assumptions,
                    );
                    for truthiness_path in truthiness_paths {
                        if !truthiness_path.is_true {
                            let Some((facts, obligations)) =
                                merge_execution_pure_facts_and_obligations(
                                    &accumulated_facts,
                                    &accumulated_obligations,
                                    &truthiness_path.facts,
                                    &truthiness_path.obligations,
                                    assumptions,
                                )
                            else {
                                continue;
                            };
                            paths.push(CStatementExecutionPath {
                                outcome: CStatementOutcome::Normal(current_state.clone()),
                                facts,
                                obligations,
                            });
                            continue;
                        }

                        let body_assumptions = assumptions_with_path_context(
                            &current_assumptions,
                            &truthiness_path.facts,
                            &truthiness_path.obligations,
                        );
                        for body_path in execute_c_statement_paths(
                            &current_state,
                            body,
                            &body_assumptions,
                            environment,
                            execution_semantics,
                            budget,
                        )? {
                            let Some((step_facts, step_obligations)) =
                                merge_execution_pure_facts_and_obligations(
                                    &truthiness_path.facts,
                                    &truthiness_path.obligations,
                                    &body_path.facts,
                                    &body_path.obligations,
                                    &current_assumptions,
                                )
                            else {
                                continue;
                            };
                            let Some((facts, obligations)) =
                                merge_execution_pure_facts_and_obligations(
                                    &accumulated_facts,
                                    &accumulated_obligations,
                                    &step_facts,
                                    &step_obligations,
                                    assumptions,
                                )
                            else {
                                continue;
                            };
                            match body_path.outcome {
                                CStatementOutcome::Normal(next_state)
                                | CStatementOutcome::Continue(next_state) => {
                                    pending.push(PendingLoopPath {
                                        state: next_state,
                                        facts,
                                        obligations,
                                    });
                                }
                                CStatementOutcome::Break(next_state) => {
                                    paths.push(CStatementExecutionPath {
                                        outcome: CStatementOutcome::Normal(next_state),
                                        facts,
                                        obligations,
                                    });
                                }
                                outcome @ (CStatementOutcome::Return { .. }
                                | CStatementOutcome::VerificationDiverges
                                | CStatementOutcome::UndefinedBehavior(_)
                                | CStatementOutcome::RuntimeError(_)) => {
                                    paths.push(CStatementExecutionPath {
                                        outcome,
                                        facts,
                                        obligations,
                                    });
                                }
                            }
                        }
                    }
                }
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                        &accumulated_facts,
                        &accumulated_obligations,
                        &condition_facts,
                        &condition_obligations,
                        assumptions,
                    ) else {
                        continue;
                    };
                    paths.push(CStatementExecutionPath {
                        outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    });
                }
                CExpressionOutcome::RuntimeError(error) => {
                    let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                        &accumulated_facts,
                        &accumulated_obligations,
                        &condition_facts,
                        &condition_obligations,
                        assumptions,
                    ) else {
                        continue;
                    };
                    paths.push(CStatementExecutionPath {
                        outcome: CStatementOutcome::RuntimeError(error),
                        facts,
                        obligations,
                    });
                }
            }
        }
        budget.check_path_width(paths.len().saturating_add(pending.len()))?;
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn declare_local(state: &CState, name: &str, c_type: CType) -> CState {
    let mut state = state.clone();
    let byte_width = match c_type {
        CType::Void => unreachable!("void local objects are not supported"),
        CType::Int32 => 4,
        CType::UInt8 => 1,
        CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::FunctionPointer(_) => C_POINTER_BYTE_WIDTH,
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
    state.memory = state.memory.with_block(pointer.block, byte_width);
    state.locals.set_uninitialized(name.to_string(), c_type);
    state
}

pub(in crate::kernel) fn sync_stack_local(state: &mut CState, name: &str, value: &CValue) {
    let Some(pointer) = state.locals.slot(name).cloned() else {
        return;
    };
    if state.memory.has_block(&pointer.block) {
        state.memory = state.memory.clone().store(pointer, value.clone());
    }
}
