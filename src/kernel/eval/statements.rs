use super::*;
use crate::kernel::loans::empty_checked_loan_evidence_sequence;

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
        &mut ExecutionBudget::for_new_execution(),
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
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts: target_facts,
                    obligations: target_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
            CLValueOutcome::RuntimeError(error) => {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(error),
                    facts: target_facts,
                    obligations: target_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
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
                    budget,
                )?),
                CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    })
                }
                CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(error),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
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
    let source = match target {
        CExpression::TypedLoad { source, .. } => source.as_ref(),
        _ => None,
    };
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
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };
        let supported_integer_update = matches!(
            lvalue.value_type,
            CType::Int8
                | CType::Int16
                | CType::Int32
                | CType::UInt8
                | CType::UInt16
                | CType::UInt32
                | CType::Int64
                | CType::UInt64
        );
        let supported_float_update = matches!(
            (lvalue.value_type, operator),
            (CType::Float32 | CType::Float64, CUpdateOperator::Add)
                | (CType::Float32 | CType::Float64, CUpdateOperator::Subtract)
                | (CType::Float32 | CType::Float64, CUpdateOperator::Multiply)
                | (CType::Float32 | CType::Float64, CUpdateOperator::Divide)
        );
        if !supported_integer_update && !supported_float_update {
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }

        for current_path in read_c_lvalue_paths(
            state,
            CLValueOutcome::LValue(lvalue.clone()),
            facts,
            obligations,
            source,
            assumptions,
            budget,
        )? {
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
                    loop_invariant_correspondence: Default::default(),
                    outcome,
                    facts: current_facts,
                    obligations: current_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
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
                        loop_invariant_correspondence: Default::default(),
                        outcome,
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
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
                            budget,
                        )?),
                        CExpressionOutcome::UndefinedBehavior(error) => {
                            paths.push(CStatementExecutionPath {
                                loop_invariant_correspondence: Default::default(),
                                outcome: CStatementOutcome::UndefinedBehavior(error),
                                facts,
                                obligations,

                                loan_evidence: empty_checked_loan_evidence_sequence(),
                            })
                        }
                        CExpressionOutcome::RuntimeError(error) => {
                            paths.push(CStatementExecutionPath {
                                loop_invariant_correspondence: Default::default(),
                                outcome: CStatementOutcome::RuntimeError(error),
                                facts,
                                obligations,

                                loan_evidence: empty_checked_loan_evidence_sequence(),
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

pub(in crate::kernel) fn stable_loan_memory_write_outcome(
    state: &CState,
    pointer: &Pointer,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<CStatementOutcome> {
    let range = CMemoryRange::new_with_element_width(
        pointer.clone(),
        Bitvector32Term::Constant(0),
        Bitvector32Term::Constant(1),
        bytes,
    );
    stable_loan_memory_range_outcome(state, &range, assumptions)
}

fn stable_loan_memory_range_outcome(
    state: &CState,
    range: &CMemoryRange,
    assumptions: &PureFactContext,
) -> Option<CStatementOutcome> {
    state
        .stable_loan_memory_access_refusal(
            range,
            assumptions,
            crate::kernel::LoanRefusalOperation::MemoryAccess,
        )
        .map(|diagnostic| CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(diagnostic)))
}

pub(in crate::kernel) fn write_c_lvalue_paths(
    state: &CState,
    lvalue: CLValue,
    value: CValue,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    if lvalue.is_constant() {
        return Ok(vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
            facts,
            obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }
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
    let mut facts = facts;
    let is_volatile = lvalue.is_volatile();
    let value_type = lvalue.value_type;
    let pointee_volatile = lvalue.pointee_is_volatile();
    let pointee_constant = lvalue.pointee_is_constant();
    let value = value.with_pointer_pointee_volatile(pointee_volatile);
    let volatile_pointer = is_volatile.then(|| lvalue.pointer(state)).flatten();
    if lvalue.value_type == CType::Int32 {
        let range_result = match &value {
            CValue::Int8(value) => {
                add_int8_range_execution_pure_facts(&mut facts, &effective_assumptions, value)
            }
            CValue::Int16(value) => {
                add_int16_range_execution_pure_facts(&mut facts, &effective_assumptions, value)
            }
            CValue::UInt8(value) => {
                add_uint8_range_execution_pure_facts(&mut facts, &effective_assumptions, value)
            }
            CValue::UInt16(value) => {
                add_uint16_range_execution_pure_facts(&mut facts, &effective_assumptions, value)
            }
            _ => Some(()),
        };
        if range_result.is_none() {
            return Ok(Vec::new());
        }
    }
    let Some(value) = crate::kernel::functions::coerce_c_value_with_pointee_constant(
        value,
        lvalue.value_type,
        pointee_constant,
        &mut obligations,
        &effective_assumptions,
    ) else {
        return Ok(vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts,
            obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    };

    match lvalue.storage {
        CLValueStorage::Local { name } => {
            if state
                .pending_thread_create
                .as_ref()
                .is_some_and(|pending| pending.protects_local(state, &name))
            {
                return Ok(vec![CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(
                        "pending pthread create permits only external disjoint stores".to_string(),
                    )),
                    facts,
                    obligations,
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }]);
            }
            if let Some(pointer) = state.locals.slot(&name).cloned()
                && let Some(outcome) = stable_loan_memory_write_outcome(
                    state,
                    &pointer,
                    value.byte_width(),
                    &effective_assumptions,
                )
            {
                return Ok(vec![CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome,
                    facts,
                    obligations,
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }]);
            }
            let mut state = state.clone();
            sync_stack_local(&mut state, &name, &value);
            if let Some(pointer) = volatile_pointer {
                facts.push(volatile_access_fact(
                    budget,
                    true,
                    pointer,
                    value_type,
                    value.clone(),
                )?);
            }
            state.locals.set_typed_with_all_qualifiers(
                name,
                value,
                value_type,
                is_volatile,
                pointee_volatile,
                false,
                pointee_constant,
            );
            Ok(vec![CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::Normal(state),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }])
        }
        CLValueStorage::Memory { pointer } => {
            let pointer = resolve_local_pointer_alias(state, &pointer, &effective_assumptions);
            if state.pending_thread_create.is_some() && !is_external_memory_pointer(&pointer) {
                return Ok(vec![CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(
                        "pending pthread create permits only external disjoint stores".to_string(),
                    )),
                    facts,
                    obligations,
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }]);
            }
            if state
                .memory
                .heap
                .pending_reallocations
                .values()
                .any(|pending| pending.old_pointer.block == pointer.block)
            {
                return Ok(vec![CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(
                        CRuntimeError::UnresolvedAllocationOutcome,
                    ),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }]);
            }
            if state.memory.is_ended_local_address(&pointer) {
                return Ok(vec![CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::UndefinedBehavior(
                        CUndefinedBehavior::InvalidMemory,
                    ),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }]);
            }
            if state
                .memory
                .is_deallocated_heap_address(&pointer, assumptions)
            {
                return Ok(vec![CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::UndefinedBehavior(
                        CUndefinedBehavior::InvalidMemory,
                    ),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }]);
            }
            if state.memory.is_read_only_block(&pointer.block) {
                return Ok(vec![CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::UndefinedBehavior(
                        CUndefinedBehavior::InvalidMemory,
                    ),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }]);
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
                return Ok(vec![CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource: CResourceFact::own_memory(CMemoryRange::new(
                            pointer.clone(),
                            Bitvector32Term::Constant(0),
                            Bitvector32Term::Constant(1),
                        )),
                    }),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }]);
            }
            // The write is owner-authorized here, so a refusal below names the
            // stable loan it conflicts with rather than masking the ordinary
            // missing-ownership diagnostic above.
            if let Some(outcome) = stable_loan_memory_write_outcome(
                state,
                &pointer,
                value.byte_width(),
                &effective_assumptions,
            ) {
                return Ok(vec![CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome,
                    facts,
                    obligations,
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }]);
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
                    return Ok(Vec::new());
                };
                obligations
            };
            // A one-byte store inside a wider integer cell updates that cell's
            // little-endian representation in place. The transition is then
            // exactly a store of the updated wider value at the cell's own
            // address: that is what the memory, its derivation edge, the
            // certified store record, and the local refresh below describe.
            // With no byte view the store writes its own cell and forgets the
            // wider one, as before.
            let (written_pointer, written_value) = if value.byte_width() == 1
                && let Some(cell) =
                    containing_integer_cell(&state.memory, &pointer, budget.c_byte_order())
                && let Some(updated) = integer_cell_with_byte(&cell, &value)
            {
                (cell.pointer, updated)
            } else {
                (pointer.clone(), value.clone())
            };
            let before_memory = state.memory.clone();
            let mut state = state.clone();
            let next_memory = state
                .memory
                .clone()
                .without_possible_aliasing_cells(
                    &written_pointer,
                    written_value.byte_width(),
                    &effective_assumptions,
                )
                .store_with_context(
                    written_pointer.clone(),
                    written_value.clone(),
                    &effective_assumptions,
                );
            state.set_memory(next_memory);
            if let Some(pending) = &state.pending_thread_create {
                state.pending_thread_create = Some(pending.with_delta(
                    super::super::threads::PendingThreadMemoryDelta::Store {
                        pointer: written_pointer.clone(),
                        value: written_value.clone(),
                    },
                ));
            }
            let mut facts = facts;
            facts.push(ExecutionPureFact::certified_store(
                before_memory,
                state.memory.clone(),
                written_pointer.clone(),
                written_value.clone(),
                authorized_range,
            ));
            refresh_scalar_local_after_memory_store(
                &mut state,
                &written_pointer,
                &written_value,
                &effective_assumptions,
            );
            if is_volatile {
                facts.push(volatile_access_fact(
                    budget, true, pointer, value_type, value,
                )?);
            }
            Ok(vec![CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::Normal(state),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }])
        }
    }
}

fn execute_c_aggregate_copy_paths(
    state: &CState,
    target: &CExpression,
    source: &CExpression,
    layout: &CAggregateLayout,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut paths = Vec::new();
    for target_path in evaluate_c_expression_paths(state, target, assumptions, budget)? {
        let CExpressionPath {
            outcome: target_outcome,
            facts: target_facts,
            obligations: target_obligations,
        } = target_path;
        let CExpressionOutcome::Value(CValue::Pointer(target_pointer)) = target_outcome else {
            continue;
        };
        if target_pointer.is_null() {
            continue;
        }
        let value_assumptions =
            assumptions_with_path_context(assumptions, &target_facts, &target_obligations);
        for source_path in evaluate_c_expression_paths(state, source, &value_assumptions, budget)? {
            let CExpressionPath {
                outcome: source_outcome,
                facts: source_facts,
                obligations: source_obligations,
            } = source_path;
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &target_facts,
                &target_obligations,
                &source_facts,
                &source_obligations,
                assumptions,
            ) else {
                continue;
            };
            let CExpressionOutcome::Value(CValue::Pointer(source_pointer)) = source_outcome else {
                continue;
            };
            if source_pointer.is_null() {
                continue;
            }
            if let Some(resource) = missing_aggregate_copy_read_resource(
                state,
                source_pointer.pointer(),
                layout,
                &assumptions_with_path_context(assumptions, &facts, &obligations),
            ) {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource,
                    }),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
            if let Some(outcome) = stable_loan_memory_write_outcome(
                state,
                target_pointer.pointer(),
                layout.size_bytes(),
                &assumptions_with_path_context(assumptions, &facts, &obligations),
            ) {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome,
                    facts,
                    obligations,
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
            let mut state = state.clone();
            let next_memory = match crate::kernel::functions::copy_aggregate_fields_checked(
                state.memory.clone(),
                source_pointer.pointer(),
                target_pointer.pointer(),
                layout,
            ) {
                Ok(memory) => memory,
                Err(undefined_behavior) => {
                    paths.push(CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                    continue;
                }
            };
            state.set_memory(next_memory);
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::Normal(state),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn missing_aggregate_copy_read_resource(
    state: &CState,
    source: &Pointer,
    layout: &CAggregateLayout,
    assumptions: &PureFactContext,
) -> Option<CResourceFact> {
    if !crate::kernel::eval::is_external_memory_pointer(source)
        || assumptions.should_allow_symbolic_contract_loads()
    {
        return None;
    }
    for field in layout.fields() {
        if !crate::kernel::reasoning::resource_context_has_read(
            state.resources(),
            &source.offset_by_bytes(field.offset_bytes()),
            field.c_type().byte_width(),
            assumptions,
        ) {
            return Some(CResourceFact::view_memory(CMemoryRange::new(
                source.offset_by_bytes(field.offset_bytes()),
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )));
        }
    }
    for union in layout.unions() {
        let pointer = source.offset_by_bytes(union.offset_bytes());
        if !crate::kernel::reasoning::resource_context_has_read(
            state.resources(),
            &pointer,
            union.size_bytes(),
            assumptions,
        ) {
            return Some(CResourceFact::view_memory(CMemoryRange::new(
                pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(1),
            )));
        }
    }
    None
}

pub(super) fn execute_c_heap_allocate_paths(
    state: &CState,
    target: &str,
    bytes_expression: &CExpression,
    zeroed: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let Some(
        target_type @ (CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::Int16Pointer
        | CType::UInt16Pointer
        | CType::UInt32Pointer
        | CType::Int64Pointer
        | CType::UInt64Pointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::Int16PointerPointer
        | CType::UInt16PointerPointer
        | CType::UInt32PointerPointer
        | CType::Int64PointerPointer
        | CType::UInt64PointerPointer),
    ) = state.local_object_type(target)
    else {
        return Ok(vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    };
    let element_width = target_type
        .pointee_type()
        .expect("heap allocation target has a pointee type")
        .byte_width();

    let element_count_expression = heap_element_count_expression(bytes_expression, element_width);
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
        let CExpressionOutcome::Value(value) = outcome else {
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
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };
        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        let Some(size) = allocation_size_value(value, &effective_assumptions) else {
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };
        let (bytes, valid_size) = if element_count_expression.is_some() {
            let positive = allocation_size_is_positive(&size, &effective_assumptions);
            let fits =
                allocation_size_fits_element_width(&size, element_width, &effective_assumptions);
            (
                Bitvector32Term::multiply(
                    size.term.clone(),
                    Bitvector32Term::Constant(element_width),
                ),
                positive && fits,
            )
        } else {
            // Heap blocks are byte-addressed even when the receiving pointer
            // has a wider logical element type. Typed accesses still carry
            // their own width and must fit in the resulting byte extent.
            let valid = allocation_size_is_positive(&size, &effective_assumptions);
            (size.term, valid)
        };
        if !valid_size {
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }

        // An identity the heap already uses is skipped through the same
        // counter, so it is spent here rather than left for a later
        // allocation to hand to something else.
        let pointer = loop {
            let identity = budget.allocate_kernel_variable()?;
            if !state.memory.heap_identity_in_use(identity.0) {
                break Pointer::symbolic(identity);
            }
        };
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
            &CExpression::Value(CValue::typed_pointer(pointer, target_type)),
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
                loop_invariant_correspondence: Default::default(),
                outcome: assigned_path.outcome,
                facts: merged_facts,
                obligations: merged_obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn heap_allocation_element_width(state: &CState, base: &Pointer) -> u32 {
    state
        .locals
        .bindings
        .values()
        .find_map(|binding| {
            let CLocalBinding::Object {
                value: CValue::Pointer(pointer),
                c_type,
                ..
            } = binding
            else {
                return None;
            };
            (pointer.pointer() == base)
                .then(|| c_type.pointee_type().map(CType::byte_width))
                .flatten()
        })
        .unwrap_or(CType::Int32.byte_width())
}

/// Heap ownership is expressed in the narrowest logical unit that exactly
/// describes the block. Preserve typed ranges for established allocation
/// forms, but use bytes for a raw extent that is not divisible by the pointer's
/// logical element width.
fn heap_range_element_width(bytes: &Bitvector32Term, requested_width: u32) -> u32 {
    crate::kernel::reasoning::element_count_from_bytes(bytes, requested_width)
        .map(|_| requested_width)
        .unwrap_or(CType::UInt8.byte_width())
}

fn heap_range_element_count(
    bytes: &Bitvector32Term,
    requested_width: u32,
) -> (Bitvector32Term, u32) {
    let element_width = heap_range_element_width(bytes, requested_width);
    let element_count = crate::kernel::reasoning::element_count_from_bytes(bytes, element_width)
        .expect("byte width must describe every positive heap extent");
    (element_count, element_width)
}

#[derive(Clone, Debug)]
struct AllocationSize {
    term: Bitvector32Term,
    unsigned: bool,
}

/// C heap blocks currently use the target's checked 32-bit address extent.
/// Preserve symbolic 32-bit sizes, and accept a 64-bit `size_t`/`long` size
/// when its concrete value fits that representation. A symbolic 64-bit size
/// cannot be safely narrowed into a memory block extent yet.
fn allocation_size_value(value: CValue, assumptions: &PureFactContext) -> Option<AllocationSize> {
    match value {
        CValue::Bool(term) => Some(AllocationSize {
            term,
            unsigned: true,
        }),
        CValue::Int8(term) => Some(AllocationSize {
            term,
            unsigned: false,
        }),
        CValue::Int16(term) | CValue::UInt8(term) | CValue::UInt16(term) => Some(AllocationSize {
            term,
            unsigned: false,
        }),
        CValue::Int32(term) => Some(AllocationSize {
            term,
            unsigned: false,
        }),
        CValue::UInt32(term) => Some(AllocationSize {
            term,
            unsigned: true,
        }),
        CValue::Int64(term) => exact_signed_size_value(&term, assumptions).and_then(|value| {
            u32::try_from(value).ok().map(|value| AllocationSize {
                term: Bitvector32Term::Constant(value),
                unsigned: false,
            })
        }),
        CValue::UInt64(term) => exact_unsigned_size_value(&term, assumptions).and_then(|value| {
            u32::try_from(value).ok().map(|value| AllocationSize {
                term: Bitvector32Term::Constant(value),
                unsigned: false,
            })
        }),
        CValue::Void | CValue::Pointer(_) | CValue::Float32(_) | CValue::Float64(_) => None,
    }
}

fn heap_element_count_expression(
    bytes_expression: &CExpression,
    element_width: u32,
) -> Option<&CExpression> {
    let is_element_width_expression = |expression: &CExpression| {
        expression == &CExpression::Value(int32(element_width))
            || expression == &crate::kernel::c_uint64_literal(u64::from(element_width))
    };
    match bytes_expression {
        CExpression::Multiply(left, right) if is_element_width_expression(right) => {
            Some(left.as_ref())
        }
        CExpression::Multiply(left, right) if is_element_width_expression(left) => {
            Some(right.as_ref())
        }
        _ => None,
    }
}

fn exact_signed_size_value(term: &Bitvector32Term, assumptions: &PureFactContext) -> Option<i64> {
    if let Some(value) = term.int64_as_const() {
        return Some(value);
    }
    if let Some(value) = crate::kernel::assumptions::exact_signed_constant(term, assumptions) {
        return Some(value);
    }
    match term {
        Bitvector32Term::Int64Add(left, right) => Some(
            exact_signed_size_value(left, assumptions)?
                .checked_add(exact_signed_size_value(right, assumptions)?)?,
        ),
        Bitvector32Term::Int64Subtract(left, right) => Some(
            exact_signed_size_value(left, assumptions)?
                .checked_sub(exact_signed_size_value(right, assumptions)?)?,
        ),
        Bitvector32Term::Int64Multiply(left, right) => Some(
            exact_signed_size_value(left, assumptions)?
                .checked_mul(exact_signed_size_value(right, assumptions)?)?,
        ),
        _ => None,
    }
}

fn exact_unsigned_size_value(term: &Bitvector32Term, assumptions: &PureFactContext) -> Option<u64> {
    if let Some(value) = term.uint64_as_const() {
        return Some(value);
    }
    if let Some(value) = crate::kernel::assumptions::exact_signed_constant(term, assumptions) {
        return u64::try_from(value).ok();
    }
    match term {
        Bitvector32Term::UInt64Add(left, right) => Some(
            exact_unsigned_size_value(left, assumptions)?
                .wrapping_add(exact_unsigned_size_value(right, assumptions)?),
        ),
        Bitvector32Term::UInt64Subtract(left, right) => Some(
            exact_unsigned_size_value(left, assumptions)?
                .wrapping_sub(exact_unsigned_size_value(right, assumptions)?),
        ),
        Bitvector32Term::UInt64Multiply(left, right) => Some(
            exact_unsigned_size_value(left, assumptions)?
                .wrapping_mul(exact_unsigned_size_value(right, assumptions)?),
        ),
        _ => None,
    }
}

fn allocation_size_is_positive(size: &AllocationSize, assumptions: &PureFactContext) -> bool {
    let condition = if size.unsigned {
        ConditionTerm::unsigned_greater_than(size.term.clone(), Bitvector32Term::Constant(0))
    } else {
        ConditionTerm::signed_greater_than(size.term.clone(), Bitvector32Term::Constant(0))
    };
    assumptions.decide(&condition) == Some(true)
}

fn allocation_size_fits_element_width(
    size: &AllocationSize,
    element_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    let maximum = if size.unsigned {
        u32::MAX / element_width
    } else {
        i32::MAX as u32 / element_width
    };
    let condition = if size.unsigned {
        ConditionTerm::unsigned_less_equal(size.term.clone(), Bitvector32Term::Constant(maximum))
    } else {
        ConditionTerm::signed_less_equal(size.term.clone(), Bitvector32Term::Constant(maximum))
    };
    assumptions.decide(&condition) == Some(true)
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
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::WrongArity {
                expected: 2,
                actual: arguments.len(),
            }),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    };
    let Some(
        target_type @ (CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::Int16Pointer
        | CType::UInt16Pointer
        | CType::UInt32Pointer
        | CType::Int64Pointer
        | CType::UInt64Pointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::Int16PointerPointer
        | CType::UInt16PointerPointer
        | CType::UInt32PointerPointer
        | CType::Int64PointerPointer
        | CType::UInt64PointerPointer),
    ) = state.local_object_type(target)
    else {
        return Ok(vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    };
    let element_width = target_type
        .pointee_type()
        .expect("realloc target has a pointee type")
        .byte_width();
    let element_count_expression = heap_element_count_expression(size_expression, element_width);

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
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };

        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        let old_pointer = match old_value {
            CValue::Pointer(pointer) => pointer.into_pointer(),
            CValue::Int32(bits) if bits.as_const() == Some(0) => Pointer::null(),
            _ => {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
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
                    loop_invariant_correspondence: Default::default(),
                    outcome: allocation_path.outcome,
                    facts: merged_facts,
                    obligations: merged_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
            }
            continue;
        }

        let Some(old_bytes) = state.memory.live_heap_block_size(&old_pointer).cloned() else {
            let error = if state
                .memory
                .is_deallocated_heap_address(&old_pointer, assumptions)
            {
                CInvalidFree::DoubleFree
            } else if state.memory.is_live_heap_address(&old_pointer, assumptions) {
                CInvalidFree::InteriorPointer
            } else {
                CInvalidFree::NonHeapPointer
            };
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(error)),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };
        let (old_count, old_range_width) = heap_range_element_count(&old_bytes, element_width);
        let old_allocation_range = CMemoryRange::new_with_element_width(
            old_pointer.clone(),
            Bitvector32Term::Constant(0),
            old_bytes.clone(),
            1,
        );
        for new_size_path in evaluate_c_expression_paths(
            state,
            element_count_expression.unwrap_or(size_expression),
            &effective_assumptions,
            budget,
        )? {
            let CExpressionPath {
                outcome: new_size_outcome,
                facts: size_facts,
                obligations: size_obligations,
            } = new_size_path;
            let CExpressionOutcome::Value(new_size_value) = new_size_outcome else {
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
                    loop_invariant_correspondence: Default::default(),
                    outcome,
                    facts: merged_facts,
                    obligations: merged_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            };
            let size_assumptions = assumptions_with_path_context(
                &effective_assumptions,
                &size_facts,
                &size_obligations,
            );
            let Some(size) = allocation_size_value(new_size_value, &size_assumptions) else {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts: size_facts,
                    obligations: size_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            };
            let new_bytes = if element_count_expression.is_some() {
                let positive = allocation_size_is_positive(&size, &size_assumptions);
                let fits =
                    allocation_size_fits_element_width(&size, element_width, &size_assumptions);
                if !positive || !fits {
                    paths.push(CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts: size_facts,
                        obligations: size_obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                    continue;
                }
                AllocationSize {
                    term: Bitvector32Term::multiply(
                        size.term.clone(),
                        Bitvector32Term::Constant(element_width),
                    ),
                    unsigned: size.unsigned,
                }
            } else {
                size
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
            if !allocation_size_is_positive(&new_bytes, &effective_assumptions) {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts: all_facts,
                    obligations: all_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
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
                    let (Some(old_prefix), Some(new_size)) =
                        (old_prefix.as_const(), new_bytes.term.as_const())
                    else {
                        paths.push(CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                            facts: all_facts,
                            obligations: all_obligations,

                            loan_evidence: empty_checked_loan_evidence_sequence(),
                        });
                        continue;
                    };
                    Some(Bitvector32Term::Constant(old_prefix.min(new_size)))
                }
            };

            let allocation = CResourceFact::own_allocation(old_pointer.clone(), old_bytes.clone());
            let Some(resources) = state
                .resources
                .clone()
                .without_fact(&allocation, &effective_assumptions)
            else {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource: allocation,
                    }),
                    facts: all_facts,
                    obligations: all_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            };
            let complete_access = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                old_pointer.clone(),
                Bitvector32Term::Constant(0),
                old_count.clone(),
                old_range_width,
            ));
            let Some(resources) = resources.without_fact(&complete_access, &effective_assumptions)
            else {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource: complete_access,
                    }),
                    facts: all_facts,
                    obligations: all_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            };
            // Ownership of the old allocation and its complete access is
            // established, so a refusal here names the live loan that keeps
            // these bytes from being reallocated.
            if let Some(outcome) = stable_loan_memory_range_outcome(
                state,
                &old_allocation_range,
                &effective_assumptions,
            ) {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome,
                    facts: all_facts,
                    obligations: all_obligations,
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }
            let resource_assumptions = state
                .resources()
                .observable_facts_assuming_valid(&effective_assumptions)
                .into_iter()
                .fold(effective_assumptions.clone(), |assumptions, fact| {
                    assumptions.assume_proposition(fact)
                });
            if let Some(stale) = resources.facts().iter().find(|resource| {
                resource.may_refer_to_memory_block(&old_pointer.block)
                    && !resource.is_proven_separate_from_allocation_with_element_width(
                        &old_pointer,
                        &old_bytes,
                        old_range_width,
                        &resource_assumptions,
                    )
            }) {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(
                        CRuntimeError::StaleResourceAfterFree {
                            resource: stale.clone(),
                        },
                    ),
                    facts: all_facts,
                    obligations: all_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }

            let old_cells = state
                .memory
                .clone()
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
                let fits_condition = if new_bytes.unsigned {
                    ConditionTerm::unsigned_less_equal(
                        Bitvector32Term::Constant(end),
                        new_bytes.term.clone(),
                    )
                } else {
                    ConditionTerm::signed_less_equal(
                        Bitvector32Term::Constant(end),
                        new_bytes.term.clone(),
                    )
                };
                let truncated_condition = if new_bytes.unsigned {
                    ConditionTerm::unsigned_less_than(
                        new_bytes.term.clone(),
                        Bitvector32Term::Constant(end),
                    )
                } else {
                    ConditionTerm::signed_less_than(
                        new_bytes.term.clone(),
                        Bitvector32Term::Constant(end),
                    )
                };
                let fits = effective_assumptions.decide(&fits_condition);
                if fits == Some(true) {
                    copied_cells.push((offset, value));
                } else if fits == Some(false)
                    || effective_assumptions.decide(&truncated_condition) == Some(true)
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
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts: all_facts,
                    obligations: all_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            }

            let pending_pointer = loop {
                let identity = budget.allocate_kernel_variable()?;
                if !state.memory.heap_identity_in_use(identity.0) {
                    break Pointer::symbolic(identity);
                }
            };
            let pending_memory = state
                .memory
                .clone()
                .with_pending_heap_allocation(
                    pending_pointer.clone(),
                    new_bytes.term.clone(),
                    false,
                )
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
                &CExpression::Value(CValue::typed_pointer(pending_pointer, target_type)),
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
                    loop_invariant_correspondence: Default::default(),
                    outcome: assigned_path.outcome,
                    facts: merged_facts,
                    obligations: merged_obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
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
                CExpressionOutcome::Value(CValue::typed_pointer(
                    Pointer::null(),
                    CType::Int32Pointer,
                ))
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
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };

        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        if pointer.is_null()
            || effective_assumptions.decide(&pointer_is_null_condition(pointer.pointer().clone()))
                == Some(true)
        {
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::Normal(state.clone()),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
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
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(
                    CRuntimeError::UnresolvedAllocationOutcome,
                ),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }

        let declared_allocation = state
            .resources
            .facts()
            .iter()
            .filter_map(|fact| fact.allocation())
            .find(|(base, _)| **base == *pointer.pointer())
            .map(|(_, bytes)| bytes.clone());
        let element_width = pointer
            .c_type()
            .pointee_type()
            .map(CType::byte_width)
            .unwrap_or(CType::Int32.byte_width());
        let before_free = state.memory.clone();
        let mut working_memory = state.memory.clone();
        let bytes = if let Some(bytes) = working_memory.live_heap_block_size(pointer.pointer()) {
            bytes.clone()
        } else if working_memory
            .is_deallocated_heap_address(pointer.pointer(), &effective_assumptions)
        {
            let error = CInvalidFree::DoubleFree;
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(error)),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        } else if working_memory.is_live_heap_address(pointer.pointer(), &effective_assumptions) {
            let error = CInvalidFree::InteriorPointer;
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(error)),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        } else if let Some(bytes) = declared_allocation {
            let Some(memory) =
                working_memory.with_heap_allocation_claim(pointer.pointer().clone(), bytes.clone())
            else {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(
                        CInvalidFree::NonHeapPointer,
                    )),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
                continue;
            };
            working_memory = memory;
            bytes
        } else {
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::InvalidFree(
                    CInvalidFree::NonHeapPointer,
                )),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };
        let full_allocation_range = CMemoryRange::new_with_element_width(
            pointer.pointer().clone(),
            Bitvector32Term::Constant(0),
            bytes.clone(),
            1,
        );
        let allocation = CResourceFact::own_allocation(pointer.pointer().clone(), bytes.clone());
        let Some(resources) = state
            .resources
            .clone()
            .without_fact(&allocation, &effective_assumptions)
        else {
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                    resource: allocation,
                }),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };
        let (element_count, range_width) = heap_range_element_count(&bytes, element_width);
        let complete_access = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
            pointer.pointer().clone(),
            Bitvector32Term::Constant(0),
            element_count,
            range_width,
        ));
        let Some(resources) = resources.without_fact(&complete_access, &effective_assumptions)
        else {
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                    resource: complete_access,
                }),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        };
        // The free is authorized by the allocation and its complete access, so
        // a refusal here is about a live loan of these bytes, not ownership.
        if let Some(outcome) =
            stable_loan_memory_range_outcome(state, &full_allocation_range, &effective_assumptions)
        {
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts,
                obligations,
                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }
        let resource_assumptions = state
            .resources()
            .observable_facts_assuming_valid(&effective_assumptions)
            .into_iter()
            .fold(effective_assumptions.clone(), |assumptions, fact| {
                assumptions.assume_proposition(fact)
            });
        if let Some(stale) = resources.facts().iter().find(|resource| {
            resource.may_refer_to_memory_block(&pointer.block)
                && !resource.is_proven_separate_from_allocation_with_element_width(
                    &pointer,
                    &bytes,
                    range_width,
                    &resource_assumptions,
                )
        }) {
            paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(CRuntimeError::StaleResourceAfterFree {
                    resource: stale.clone(),
                }),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            });
            continue;
        }
        let memory = working_memory
            .free_heap_block(pointer.pointer(), &effective_assumptions)
            .expect("validated live heap base should free");
        facts.push(ExecutionPureFact::internal(
            Proposition::CHeapAllocationFreed {
                before: before_free,
                after: memory.clone(),
                allocation_base: pointer.pointer().clone(),
                bytes: bytes.clone(),
            },
        ));
        paths.push(CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::Normal(
                state
                    .clone()
                    .with_memory(memory)
                    .with_resource_context(resources),
            ),
            facts,
            obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
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
        // Resolution rewrites the local pointer binding from the pending
        // base to the fresh live base. Capture its logical pointee width
        // before that rewrite so pointer-array and struct-array resources
        // retain their established coordinate system.
        let element_width = heap_allocation_element_width(&state, &base);
        if let Some(pending_reallocation) =
            state.memory.heap.pending_reallocations.get(&base).cloned()
        {
            let (memory, bytes, resolved_base, _) = state
                .memory
                .clone()
                .resolve_pending_heap_reallocation(&base, !is_null, assumptions)
                .expect("collected pending reallocation should still exist");
            state = state.with_memory(memory);
            for binding in std::sync::Arc::make_mut(&mut state.locals.bindings).values_mut() {
                if let CLocalBinding::Object {
                    value: CValue::Pointer(pointer),
                    ..
                } = binding
                    && pointer.pointer() == &base
                {
                    pointer.replace_pointer(resolved_base.clone());
                }
            }
            if !is_null {
                let old_allocation = CResourceFact::own_allocation(
                    pending_reallocation.old_pointer,
                    pending_reallocation.old_bytes.clone(),
                );
                let (old_count, old_range_width) =
                    heap_range_element_count(&pending_reallocation.old_bytes, element_width);
                let old_memory = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                    match old_allocation.allocation() {
                        Some((pointer, _)) => pointer.clone(),
                        None => unreachable!("allocation resource was just constructed"),
                    },
                    Bitvector32Term::Constant(0),
                    old_count,
                    old_range_width,
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
                    .unchecked_with_fact(CResourceFact::own_memory({
                        let (new_count, new_range_width) =
                            heap_range_element_count(&bytes, element_width);
                        CMemoryRange::new_with_element_width(
                            resolved_base,
                            Bitvector32Term::Constant(0),
                            new_count,
                            new_range_width,
                        )
                    }));
            }
            continue;
        }
        let (memory, bytes, resolved_base) = state
            .memory
            .clone()
            .resolve_pending_heap_allocation(&base, !is_null)
            .expect("collected pending allocation should still exist");
        state = state.with_memory(memory);
        for binding in std::sync::Arc::make_mut(&mut state.locals.bindings).values_mut() {
            if let CLocalBinding::Object {
                value: CValue::Pointer(pointer),
                ..
            } = binding
                && pointer.pointer() == &base
            {
                pointer.replace_pointer(resolved_base.clone());
            }
        }
        if !is_null {
            let (element_count, range_width) = heap_range_element_count(&bytes, element_width);
            state.resources = state
                .resources
                .unchecked_with_fact(CResourceFact::own_allocation(
                    resolved_base.clone(),
                    bytes.clone(),
                ))
                .unchecked_with_fact(CResourceFact::own_memory(
                    CMemoryRange::new_with_element_width(
                        resolved_base,
                        Bitvector32Term::Constant(0),
                        element_count,
                        range_width,
                    ),
                ));
        }
    }
    state
}

fn has_live_thread_completion(state: &CState) -> bool {
    state.pending_thread_create.is_some()
        || state
            .thread_ledger
            .as_ref()
            .is_some_and(|ledger| ledger.has_live_rights())
}

fn live_thread_return_refusal() -> CStatementOutcome {
    CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(
        "a function cannot return with a live pthread completion right".to_string(),
    ))
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
                    pointer.pointer().clone(),
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
                    let outcome = if has_live_thread_completion(&resolved_state) {
                        live_thread_return_refusal()
                    } else if resolved_state.memory.has_pending_heap_allocation() {
                        CStatementOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome)
                    } else {
                        CStatementOutcome::Return {
                            value: CValue::typed_pointer(resolved_pointer, pointer.c_type()),
                            state: resolved_state,
                        }
                    };
                    paths.push(CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome,
                        facts: truthiness_path.facts,
                        obligations: truthiness_path.obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                }
            }
            CExpressionOutcome::Value(value) => {
                let outcome = if has_live_thread_completion(state) {
                    live_thread_return_refusal()
                } else if state.memory.has_pending_heap_allocation() {
                    CStatementOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome)
                } else {
                    CStatementOutcome::Return {
                        value,
                        state: state.clone(),
                    }
                };
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome,
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(error),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
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

/// The automatic objects one scope declares for itself.
///
/// C0 lowers a source block to a `Seq` tree, and the kernel has no statement
/// that stands for the block itself, so a scope's own declarations are the
/// ones reachable from its root through that tree. The walk stops at a nested
/// scope — an `if` arm, a loop body, a `switch` body — because control leaving
/// that scope retires what it declared, and stops at every other statement
/// because no other statement declares.
///
/// Bounded by the scope's own spine: the `Seq` nodes above its declarations,
/// which a source block has one of per statement it holds.
fn collect_scope_declared_names(statement: &CStatement, names: &mut Vec<String>) {
    match statement {
        CStatement::Declare { name, .. } | CStatement::DeclareAggregate { name, .. } => {
            names.push(name.clone());
        }
        CStatement::Seq(first, second) => {
            collect_scope_declared_names(first, names);
            collect_scope_declared_names(second, names);
        }
        // Nested scopes retire their own declarations.
        CStatement::If { .. }
        | CStatement::While { .. }
        | CStatement::Switch { .. }
        | CStatement::TryCatchInt32 { .. }
        // Everything else declares nothing.
        | CStatement::Skip
        | CStatement::Break
        | CStatement::Continue
        | CStatement::Goto { .. }
        | CStatement::ForStep { .. }
        | CStatement::CopyAggregate { .. }
        | CStatement::Assign { .. }
        | CStatement::CallAssign { .. }
        | CStatement::Call { .. }
        | CStatement::HeapAllocate { .. }
        | CStatement::HeapFree { .. }
        | CStatement::Assert { .. }
        | CStatement::Return(_)
        | CStatement::Throw(_)
        | CStatement::Store { .. }
        | CStatement::TypedStore { .. }
        | CStatement::Update { .. } => {}
    }
}

/// The names a scope declares, in the order it declares them.
pub(in crate::kernel) fn scope_declared_names(statement: &CStatement) -> Vec<String> {
    let mut names = Vec::new();
    collect_scope_declared_names(statement, &mut names);
    names
}

/// Ends the automatic lifetimes of the objects a scope declared.
///
/// An automatic object's lifetime ends when control leaves the block that
/// declared it, however it leaves — falling off the end, `break`, `continue`,
/// `return`, `goto`, or a thrown outcome. Its storage stops existing, so a
/// pointer into it designates no object and a load through one is undefined
/// behaviour rather than a way to read what the block wrote.
///
/// The name is unbound as well as the storage retired, because the frame no
/// longer holds an object of that name: a later declaration of it is a
/// declaration, not a re-entry, and the mint gives it an identity of its own.
///
/// Bounded by the declarations of the exiting scope; it reads no other local
/// and no other block.
pub(in crate::kernel) fn end_scope_automatic_lifetimes(
    state: &CState,
    declared: &[String],
) -> Result<CState, crate::kernel::LoanRefusalDiagnostic> {
    let mut state = state.clone();
    let mut memory = state.memory.clone();
    let mut retired = false;
    for name in declared {
        crate::instrumentation::record_deterministic_work(1);
        let Some(slot) = state.locals.slot(name).cloned() else {
            continue;
        };
        if slot.block.starts_with("local:") && memory.has_block(&slot.block) {
            let range = CMemoryRange::new_with_element_width(
                slot.clone(),
                0.into(),
                memory
                    .block_size(&slot.block)
                    .expect("live local block")
                    .clone(),
                1,
            );
            if let Some(refusal) = state.stable_loan_memory_access_refusal(
                &range,
                &PureFactContext::default(),
                crate::kernel::LoanRefusalOperation::MemoryAccess,
            ) {
                return Err(refusal);
            }
            memory = memory.without_local_block(&slot.block);
            retired = true;
        }
        state.locals.remove(name);
    }
    if retired {
        state.set_memory(memory);
    }
    Ok(state)
}

/// Applies a scope exit to every outcome a scope's body produced.
///
/// Every outcome leaves the scope, so every outcome retires it. The three
/// outcomes that carry no state — divergence, undefined behaviour, a runtime
/// error — have no successor to retire anything in.
pub(in crate::kernel) fn paths_after_scope_exit(
    paths: Vec<CStatementExecutionPath>,
    declared: &[String],
) -> Vec<CStatementExecutionPath> {
    if declared.is_empty() {
        return paths;
    }
    paths
        .into_iter()
        .map(|path| {
            let outcome = match path.outcome {
                CStatementOutcome::Normal(state) => {
                    end_scope_automatic_lifetimes(&state, declared).map(CStatementOutcome::Normal)
                }
                CStatementOutcome::Break(state) => {
                    end_scope_automatic_lifetimes(&state, declared).map(CStatementOutcome::Break)
                }
                CStatementOutcome::Continue(state) => {
                    end_scope_automatic_lifetimes(&state, declared).map(CStatementOutcome::Continue)
                }
                CStatementOutcome::Jump { target, state } => {
                    end_scope_automatic_lifetimes(&state, declared)
                        .map(|state| CStatementOutcome::Jump { target, state })
                }
                CStatementOutcome::Return { value, state } => {
                    end_scope_automatic_lifetimes(&state, declared)
                        .map(|state| CStatementOutcome::Return { value, state })
                }
                CStatementOutcome::Throw { value, state } => {
                    end_scope_automatic_lifetimes(&state, declared)
                        .map(|state| CStatementOutcome::Throw { value, state })
                }
                outcome @ (CStatementOutcome::VerificationDiverges
                | CStatementOutcome::UndefinedBehavior(_)
                | CStatementOutcome::RuntimeError(_)) => Ok(outcome),
            }
            .unwrap_or_else(|refusal| {
                CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(refusal))
            });
            CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome,
                ..path
            }
        })
        .collect()
}

pub(in crate::kernel) fn execute_c_statement_paths(
    state: &CState,
    statement: &CStatement,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    budget.install_c_byte_order(environment.byte_order());
    if let Some(pending) = &state.pending_thread_create {
        if let Some(resolved) = pending.resolve(state, assumptions) {
            return execute_c_statement_paths(
                &resolved,
                statement,
                assumptions,
                environment,
                execution_semantics,
                budget,
            );
        }
        match statement {
            CStatement::Declare {
                name,
                c_type:
                    CType::Int8
                    | CType::Int16
                    | CType::Int32
                    | CType::Int64
                    | CType::UInt8
                    | CType::UInt16
                    | CType::UInt32
                    | CType::UInt64,
                ..
            } if !pending.protects_local(state, name) => {
                let mut bare = state.clone();
                bare.pending_thread_create = None;
                let mut paths = execute_c_statement_paths(
                    &bare,
                    statement,
                    assumptions,
                    environment,
                    execution_semantics,
                    budget,
                )?;
                for path in &mut paths {
                    if let CStatementOutcome::Normal(next) = &mut path.outcome {
                        if let Some(slot) = next.locals.slot(name)
                            && let Some(bytes) = next
                                .memory
                                .block_size(&slot.block)
                                .and_then(Bitvector32Term::as_const)
                        {
                            next.pending_thread_create = Some(pending.with_delta(
                                super::super::threads::PendingThreadMemoryDelta::Declare {
                                    block: slot.block.clone(),
                                    bytes,
                                },
                            ));
                        } else {
                            path.outcome =
                                CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(
                                    "pending pthread create cannot retain this local declaration"
                                        .to_string(),
                                ));
                        }
                    }
                }
                return Ok(paths);
            }
            CStatement::Assign { name, expression }
                if matches!(expression, CExpression::Value(_) | CExpression::Variable(_))
                    && state.locals.slot(name).is_some()
                    && !pending.protects_local(state, name) =>
            {
                let mut bare = state.clone();
                bare.pending_thread_create = None;
                let mut paths = execute_c_statement_paths(
                    &bare,
                    statement,
                    assumptions,
                    environment,
                    execution_semantics,
                    budget,
                )?;
                for path in &mut paths {
                    if let CStatementOutcome::Normal(next) = &mut path.outcome {
                        if let (Some(slot), Some(value)) =
                            (next.locals.slot(name), next.locals.get(name))
                        {
                            next.pending_thread_create = Some(pending.with_delta(
                                super::super::threads::PendingThreadMemoryDelta::Store {
                                    pointer: slot.clone(),
                                    value: value.clone(),
                                },
                            ));
                        } else {
                            path.outcome =
                                CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(
                                    "pending pthread create cannot retain this local assignment"
                                        .to_string(),
                                ));
                        }
                    }
                }
                return Ok(paths);
            }
            CStatement::TypedStore { .. } if pending.has_local_handle_slot(state) => {}
            CStatement::Skip | CStatement::Seq(_, _) => {}
            CStatement::If { condition, .. }
                if super::super::functions::c_expression_is_state_independent(condition) => {}
            _ => {
                budget.consume_statement_step()?;
                return Ok(vec![CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(
                        "resolve the pending pthread create status before this C operation"
                            .to_string(),
                    )),
                    facts: Vec::new(),
                    obligations: Vec::new(),
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                }]);
            }
        }
    }
    // `Seq` is the tree representation of a source block, not an executed C
    // statement. Charging it made the statement budget depend on tree shape
    // and counted every straight-line source statement twice.
    if !matches!(statement, CStatement::Seq(_, _)) {
        budget.consume_statement_step()?;
    }
    let paths = match statement {
        CStatement::Skip => vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::Normal(state.clone()),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }],
        CStatement::Break => vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::Break(state.clone()),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }],
        CStatement::Continue => vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::Continue(state.clone()),
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }],
        CStatement::Goto { target } => vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::Jump {
                target: *target,
                state: state.clone(),
            },
            facts: Vec::new(),
            obligations: Vec::new(),

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }],
        CStatement::ForStep {
            step,
            exited_locals,
            continue_after,
        } => {
            let retired = match end_scope_automatic_lifetimes(state, exited_locals) {
                Ok(state) => state,
                Err(refusal) => {
                    return Ok(vec![CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(
                            refusal,
                        )),
                        facts: Vec::new(),
                        obligations: Vec::new(),
                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    }]);
                }
            };
            let mut paths = Vec::new();
            for step_path in execute_c_statement_paths(
                &retired,
                step,
                assumptions,
                environment,
                execution_semantics,
                budget,
            )? {
                let outcome = match step_path.outcome {
                    CStatementOutcome::Normal(next_state) if *continue_after => {
                        CStatementOutcome::Continue(next_state)
                    }
                    outcome => outcome,
                };
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome,
                    facts: step_path.facts,
                    obligations: step_path.obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
            }
            paths
        }
        CStatement::Declare {
            name,
            c_type,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
        } => {
            let outcome = if *c_type == CType::Void {
                CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
            } else {
                match declare_local(
                    state,
                    name,
                    *c_type,
                    *volatile,
                    *pointee_volatile,
                    *constant,
                    *pointee_constant,
                ) {
                    Ok(state) => CStatementOutcome::Normal(state),
                    Err(refusal) => {
                        CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(refusal))
                    }
                }
            };
            vec![CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts: Vec::new(),
                obligations: Vec::new(),

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }]
        }
        CStatement::DeclareAggregate {
            name,
            layout,
            construction,
        } => {
            let outcome = match if *construction {
                begin_aggregate_construction(state, name, layout, budget)?
            } else {
                declare_aggregate_local(state, name, layout)
            } {
                Ok(state) => CStatementOutcome::Normal(state),
                Err(refusal) => {
                    CStatementOutcome::RuntimeError(CRuntimeError::LoanRefusal(refusal))
                }
            };
            vec![CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts: Vec::new(),
                obligations: Vec::new(),

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }]
        }
        CStatement::CopyAggregate {
            target,
            source,
            layout,
        } => execute_c_aggregate_copy_paths(state, target, source, layout, assumptions, budget)?,
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
                            &first_path.loan_evidence,
                            budget,
                        )?);
                    }
                    outcome @ (CStatementOutcome::Break(_)
                    | CStatementOutcome::Continue(_)
                    | CStatementOutcome::Jump { .. }
                    | CStatementOutcome::Return { .. }
                    | CStatementOutcome::Throw { .. }
                    | CStatementOutcome::VerificationDiverges
                    | CStatementOutcome::UndefinedBehavior(_)
                    | CStatementOutcome::RuntimeError(_)) => paths.push(CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome,
                        facts: first_path.facts,
                        obligations: first_path.obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    }),
                }
            }
            paths
        }
        CStatement::Return(CExpression::Value(CValue::Void)) => {
            let outcome = if has_live_thread_completion(state) {
                live_thread_return_refusal()
            } else if state.memory.has_pending_heap_allocation() {
                CStatementOutcome::RuntimeError(CRuntimeError::UnresolvedAllocationOutcome)
            } else {
                CStatementOutcome::Return {
                    value: CValue::Void,
                    state: state.clone(),
                }
            };
            vec![CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts: Vec::new(),
                obligations: Vec::new(),

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }]
        }
        CStatement::Return(expression) => {
            execute_c_return_expression_paths(state, expression, assumptions, budget)?
        }
        CStatement::Throw(expression) => {
            let mut paths = Vec::new();
            for path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
                let outcome = match path.outcome {
                    CExpressionOutcome::Value(value @ CValue::Int32(_)) => {
                        if has_live_thread_completion(state) {
                            live_thread_return_refusal()
                        } else {
                            CStatementOutcome::Throw {
                                value,
                                state: state.clone(),
                            }
                        }
                    }
                    CExpressionOutcome::Value(_) => {
                        CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
                    }
                    CExpressionOutcome::UndefinedBehavior(error) => {
                        CStatementOutcome::UndefinedBehavior(error)
                    }
                    CExpressionOutcome::RuntimeError(error) => {
                        CStatementOutcome::RuntimeError(error)
                    }
                };
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome,
                    facts: path.facts,
                    obligations: path.obligations,
                    loan_evidence: empty_checked_loan_evidence_sequence(),
                });
            }
            paths
        }
        CStatement::TryCatchInt32 {
            try_body,
            binding,
            handler,
            ..
        } => {
            let mut paths = Vec::new();
            for try_path in execute_c_statement_paths(
                state,
                try_body,
                assumptions,
                environment,
                execution_semantics,
                budget,
            )? {
                if let CStatementOutcome::Throw {
                    value: value @ CValue::Int32(_),
                    state: thrown_state,
                } = &try_path.outcome
                {
                    if thrown_state.locals.bindings.contains_key(binding) {
                        paths.push(CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::RuntimeError(
                                CRuntimeError::FunctionContract(format!(
                                    "int32 handler binding `{binding}` is not fresh"
                                )),
                            ),
                            facts: try_path.facts,
                            obligations: try_path.obligations,
                            loan_evidence: try_path.loan_evidence,
                        });
                        continue;
                    }
                    let bound_handler = c_seq(
                        c_declare(binding.clone(), CType::Int32),
                        c_seq(
                            c_assign(binding.clone(), CExpression::Value(value.clone())),
                            (**handler).clone(),
                        ),
                    );
                    paths.extend(execute_c_statement_paths_with_prefix(
                        thrown_state,
                        &bound_handler,
                        assumptions,
                        environment,
                        execution_semantics,
                        &try_path.facts,
                        &try_path.obligations,
                        &try_path.loan_evidence,
                        budget,
                    )?);
                } else {
                    paths.push(try_path);
                }
            }
            paths
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
            volatile,
            pointee_constant,
        } => execute_c_lvalue_assignment_paths(
            state,
            &CExpression::TypedLoad {
                pointer: Box::new(pointer.clone()),
                value_type: *value_type,
                volatile: *volatile,
                pointee_constant: *pointee_constant,
                source: Default::default(),
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
                            let branch_state = if let Some(pending) =
                                &branch_state.pending_thread_create
                            {
                                match pending.resolve(&branch_state, &path_assumptions) {
                                    Some(resolved) => resolved,
                                    None => {
                                        paths.push(CStatementExecutionPath {
                                            loop_invariant_correspondence: Default::default(),
                                            outcome: CStatementOutcome::RuntimeError(CRuntimeError::FunctionContract(
                                                "C branch does not decide the pending pthread create status".to_string(),
                                            )),
                                            facts: truthiness_path.facts,
                                            obligations: truthiness_path.obligations,
                                            loan_evidence: empty_checked_loan_evidence_sequence(),
                                        });
                                        continue;
                                    }
                                }
                            } else {
                                branch_state
                            };
                            // The arm is a scope: what it declares stops
                            // existing however control leaves it.
                            let declared = scope_declared_names(branch);
                            paths.extend(paths_after_scope_exit(
                                execute_c_statement_paths_with_prefix(
                                    &branch_state,
                                    branch,
                                    assumptions,
                                    environment,
                                    execution_semantics,
                                    &truthiness_path.facts,
                                    &truthiness_path.obligations,
                                    &empty_checked_loan_evidence_sequence(),
                                    budget,
                                )?,
                                &declared,
                            ));
                        }
                    }
                    CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                            facts,
                            obligations,

                            loan_evidence: empty_checked_loan_evidence_sequence(),
                        })
                    }
                    CExpressionOutcome::RuntimeError(error) => {
                        paths.push(CStatementExecutionPath {
                            loop_invariant_correspondence: Default::default(),
                            outcome: CStatementOutcome::RuntimeError(error),
                            facts,
                            obligations,

                            loan_evidence: empty_checked_loan_evidence_sequence(),
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
            resource_specs: _,
            ranking_measures: _,
            structural_measure: _,
            do_while,
            body,
            ..
        } => execute_c_while_paths(
            state,
            condition,
            invariant,
            *do_while,
            body,
            assumptions,
            environment,
            execution_semantics,
            budget,
        )?,
        CStatement::Switch { expression, cases } => execute_c_switch_paths(
            state,
            expression,
            cases,
            assumptions,
            environment,
            execution_semantics,
            budget,
        )?,
    };
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn execute_c_switch_paths(
    state: &CState,
    expression: &CExpression,
    cases: &[CSwitchCase],
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    // A `switch` body is one scope: cases fall through into each other, so a
    // declaration in one case is in scope in the next and stops existing only
    // where control leaves the switch.
    let mut declared = Vec::new();
    for case in cases {
        collect_scope_declared_names(&case.body, &mut declared);
    }
    let mut paths = Vec::new();
    for selector_path in evaluate_c_expression_paths(state, expression, assumptions, budget)? {
        let CExpressionPath {
            outcome,
            mut facts,
            obligations,
        } = selector_path;
        match outcome {
            CExpressionOutcome::Value(value) => {
                let selector_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                let Some(selector) =
                    promote_c_int32_path_value(value, &mut facts, &selector_assumptions)
                else {
                    paths.push(CStatementExecutionPath {
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                    continue;
                };
                paths.extend(execute_c_switch_dispatch_paths(
                    state,
                    &selector,
                    cases,
                    0,
                    facts,
                    obligations,
                    assumptions,
                    environment,
                    execution_semantics,
                    budget,
                )?);
            }
            CExpressionOutcome::UndefinedBehavior(error) => paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::UndefinedBehavior(error),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }),
            CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(error),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }),
        }
    }
    Ok(paths_after_scope_exit(paths, &declared))
}

fn execute_c_switch_dispatch_paths(
    state: &CState,
    selector: &Bitvector32Term,
    cases: &[CSwitchCase],
    case_index: usize,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    if case_index == cases.len() {
        let default_index = cases.iter().position(|case| case.value.is_none());
        return match default_index {
            Some(default_index) => execute_c_switch_suffix_paths(
                state,
                cases,
                default_index,
                facts,
                obligations,
                assumptions,
                environment,
                execution_semantics,
                budget,
            ),
            None => Ok(vec![CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::Normal(state.clone()),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }]),
        };
    }

    let case = &cases[case_index];
    let Some(value) = case.value else {
        return execute_c_switch_dispatch_paths(
            state,
            selector,
            cases,
            case_index + 1,
            facts,
            obligations,
            assumptions,
            environment,
            execution_semantics,
            budget,
        );
    };
    let condition = ConditionTerm::equal(selector.clone(), Bitvector32Term::Constant(value));
    let mut paths = Vec::new();
    for condition_path in condition_as_c_int32_paths(condition, facts, obligations, assumptions) {
        let CExpressionPath {
            outcome,
            facts,
            obligations,
        } = condition_path;
        let CExpressionOutcome::Value(CValue::Int32(result)) = outcome else {
            unreachable!("switch case conditions produce promoted int32 values");
        };
        if result.as_const() == Some(1) {
            paths.extend(execute_c_switch_suffix_paths(
                state,
                cases,
                case_index,
                facts,
                obligations,
                assumptions,
                environment,
                execution_semantics,
                budget,
            )?);
        } else {
            paths.extend(execute_c_switch_dispatch_paths(
                state,
                selector,
                cases,
                case_index + 1,
                facts,
                obligations,
                assumptions,
                environment,
                execution_semantics,
                budget,
            )?);
        }
    }
    Ok(paths)
}

fn execute_c_switch_suffix_paths(
    state: &CState,
    cases: &[CSwitchCase],
    case_index: usize,
    facts: Vec<ExecutionPureFact>,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    environment: &CExecutionEnvironment,
    execution_semantics: CExecutionSemantics,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    if case_index == cases.len() {
        return Ok(vec![CStatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            outcome: CStatementOutcome::Normal(state.clone()),
            facts,
            obligations,

            loan_evidence: empty_checked_loan_evidence_sequence(),
        }]);
    }
    let case_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    let mut paths = Vec::new();
    for case_path in execute_c_statement_paths(
        state,
        &cases[case_index].body,
        &case_assumptions,
        environment,
        execution_semantics,
        budget,
    )? {
        let Some((case_facts, case_obligations)) = merge_execution_pure_facts_and_obligations(
            &facts,
            &obligations,
            &case_path.facts,
            &case_path.obligations,
            assumptions,
        ) else {
            continue;
        };
        match case_path.outcome {
            CStatementOutcome::Normal(next_state) => paths.extend(execute_c_switch_suffix_paths(
                &next_state,
                cases,
                case_index + 1,
                case_facts,
                case_obligations,
                assumptions,
                environment,
                execution_semantics,
                budget,
            )?),
            CStatementOutcome::Break(next_state) => paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::Normal(next_state),
                facts: case_facts,
                obligations: case_obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }),
            outcome @ (CStatementOutcome::Continue(_)
            | CStatementOutcome::Jump { .. }
            | CStatementOutcome::Return { .. }
            | CStatementOutcome::Throw { .. }
            | CStatementOutcome::VerificationDiverges
            | CStatementOutcome::UndefinedBehavior(_)
            | CStatementOutcome::RuntimeError(_)) => paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome,
                facts: case_facts,
                obligations: case_obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
            }),
        }
    }
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
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::Normal(state.clone()),
                        facts: truthiness_path.facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                }
            }
            CExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(CStatementExecutionPath {
                    loop_invariant_correspondence: Default::default(),
                    outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts,
                    obligations,

                    loan_evidence: empty_checked_loan_evidence_sequence(),
                })
            }
            CExpressionOutcome::RuntimeError(error) => paths.push(CStatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                outcome: CStatementOutcome::RuntimeError(error),
                facts,
                obligations,

                loan_evidence: empty_checked_loan_evidence_sequence(),
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
    do_while: bool,
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
        check_condition: bool,
    }

    let body_declared = scope_declared_names(body);
    let mut pending = vec![PendingLoopPath {
        state: state.clone(),
        facts: Vec::new(),
        obligations: Vec::new(),
        check_condition: !do_while,
    }];
    let mut paths = Vec::new();

    while let Some(PendingLoopPath {
        state: current_state,
        facts: accumulated_facts,
        obligations: accumulated_obligations,
        check_condition,
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

        let condition_paths = if check_condition {
            evaluate_c_expression_paths(&current_state, condition, &loop_assumptions, budget)?
        } else {
            vec![CExpressionPath {
                outcome: CExpressionOutcome::Value(CValue::Int32(Bitvector32Term::Constant(1))),
                facts: Vec::new(),
                obligations: Vec::new(),
            }]
        };
        for condition_path in condition_paths {
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
                                loop_invariant_correspondence: Default::default(),
                                outcome: CStatementOutcome::Normal(current_state.clone()),
                                facts,
                                obligations,

                                loan_evidence: empty_checked_loan_evidence_sequence(),
                            });
                            continue;
                        }

                        let body_assumptions = assumptions_with_path_context(
                            &current_assumptions,
                            &truthiness_path.facts,
                            &truthiness_path.obligations,
                        );
                        // The body is a scope, and every way out of an
                        // iteration leaves it: the back edge, `break`,
                        // `continue`, and every transfer out of the loop.
                        for body_path in paths_after_scope_exit(
                            execute_c_statement_paths(
                                &current_state,
                                body,
                                &body_assumptions,
                                environment,
                                execution_semantics,
                                budget,
                            )?,
                            &body_declared,
                        ) {
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
                                        check_condition: true,
                                    });
                                }
                                CStatementOutcome::Break(next_state) => {
                                    paths.push(CStatementExecutionPath {
                                        loop_invariant_correspondence: Default::default(),
                                        outcome: CStatementOutcome::Normal(next_state),
                                        facts,
                                        obligations,

                                        loan_evidence: empty_checked_loan_evidence_sequence(),
                                    });
                                }
                                outcome @ (CStatementOutcome::Return { .. }
                                | CStatementOutcome::Throw { .. }
                                | CStatementOutcome::Jump { .. }
                                | CStatementOutcome::VerificationDiverges
                                | CStatementOutcome::UndefinedBehavior(_)
                                | CStatementOutcome::RuntimeError(_)) => {
                                    paths.push(CStatementExecutionPath {
                                        loop_invariant_correspondence: Default::default(),
                                        outcome,
                                        facts,
                                        obligations,

                                        loan_evidence: empty_checked_loan_evidence_sequence(),
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
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
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
                        loop_invariant_correspondence: Default::default(),
                        outcome: CStatementOutcome::RuntimeError(error),
                        facts,
                        obligations,

                        loan_evidence: empty_checked_loan_evidence_sequence(),
                    });
                }
            }
        }
        budget.check_path_width(paths.len().saturating_add(pending.len()))?;
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// Mints the block identity for one execution of a local declaration.
///
/// Soundness. Around seventy kernel sites read `a.block == b.block` as "the
/// same object", so each execution of a declaration must get a block that no
/// other automatic object in this memory has, live or ended. Two things can
/// hand out the bare `local:<name>` spelling twice:
///
/// * this frame re-entering the declaration — a loop, or an inner scope that
///   shadows the name — which the locals map sees, and which ends the old
///   object's lifetime before taking the next generation; and
/// * a *called* frame, which executes on the caller's memory with its own
///   locals map and so cannot see the caller's objects at all. Its `buf` and
///   the caller's `buf` would be one block, one extent and one cell map. That
///   is why a called frame is generational unconditionally: the caller's
///   object may not even be visible in memory, as for a value-only parameter
///   whose pseudo-slot borrows the `local:<name>` spelling while owning no
///   block of its own.
///
/// The generation counter is path state threaded through calls and returns,
/// so it hands out each generation once. The mint checks that against memory
/// regardless, because this is the place the uniqueness invariant is
/// established rather than assumed.
fn local_declaration_pointer(
    state: &mut CState,
    name: &str,
) -> Result<Pointer, crate::kernel::LoanRefusalDiagnostic> {
    let previous = state.locals.slot(name).cloned();
    if let Some(previous) = previous
        && previous.block.starts_with("local:")
    {
        let end = state
            .memory
            .block_size(&previous.block)
            .cloned()
            .unwrap_or(Bitvector32Term::Variable(Variable(u64::MAX)));
        let old_range = CMemoryRange::new_with_element_width(
            previous.clone(),
            Bitvector32Term::Constant(0),
            end,
            1,
        );
        if let Some(refusal) = state.stable_loan_memory_access_refusal(
            &old_range,
            &PureFactContext::default(),
            crate::kernel::LoanRefusalOperation::MemoryAccess,
        ) {
            return Err(refusal);
        }
        state.set_memory(state.memory.without_local_block(&previous.block));
        return Ok(fresh_local_object_identity(state, name));
    }
    let unnumbered = CMemory::local_pointer(name);
    if state.enclosing_frame_holds_locals()
        || state.memory.local_block_is_occupied(&unnumbered.block)
    {
        return Ok(fresh_local_object_identity(state, name));
    }
    Ok(unnumbered)
}

/// Takes the next unused generation of `name`'s automatic object.
///
/// Refuses to hand back an identity this memory has already given out. The
/// counter is monotone and every generation it hands out is declared, so the
/// first candidate is free; checking it is what makes the uniqueness
/// invariant enforced at the one place it is created.
fn fresh_local_object_identity(state: &mut CState, name: &str) -> Pointer {
    loop {
        let lifetime = state.next_local_lifetime();
        assert!(
            lifetime != u64::MAX,
            "ran out of automatic-object generations for `{name}`"
        );
        *state = state
            .clone()
            .with_next_local_lifetime(lifetime.saturating_add(1));
        let pointer = CMemory::local_lifetime_pointer(lifetime, name);
        if !state.memory.local_block_is_occupied(&pointer.block) {
            return pointer;
        }
        debug_assert!(
            false,
            "generation {lifetime} of `{name}` was minted twice; \
             an automatic object would share a block with another one"
        );
    }
}

pub(in crate::kernel) fn declare_local(
    state: &CState,
    name: &str,
    c_type: CType,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
) -> Result<CState, crate::kernel::LoanRefusalDiagnostic> {
    let mut state = state.clone();
    let pointer = local_declaration_pointer(&mut state, name)?;
    // A declared local's block is placed at its type's alignment; record it
    // with the block so the alignment decision is intrinsic, as for heap
    // and file-scope blocks, rather than a path fact at each address-of.
    register_block_alignment(&pointer.block, c_type.abi_alignment());
    let byte_width = match c_type {
        CType::Void => unreachable!("void local objects are not supported"),
        CType::Bool => 1,
        CType::VoidPointer | CType::VoidPointerPointer => C_POINTER_BYTE_WIDTH,
        CType::Int8 => 1,
        CType::Int16 | CType::UInt16 => 2,
        CType::Int32 => 4,
        CType::Int64 | CType::UInt64 | CType::Float64 => 8,
        CType::UInt8 => 1,
        CType::UInt32 | CType::Float32 => 4,
        CType::Int8Pointer | CType::Int8PointerPointer => C_POINTER_BYTE_WIDTH,
        CType::Int16Pointer
        | CType::UInt16Pointer
        | CType::Int32Pointer
        | CType::UInt8Pointer
        | CType::UInt32Pointer
        | CType::Int64Pointer
        | CType::UInt64Pointer
        | CType::Int16PointerPointer
        | CType::UInt16PointerPointer
        | CType::Int32PointerPointer
        | CType::UInt8PointerPointer
        | CType::UInt32PointerPointer
        | CType::Int64PointerPointer
        | CType::UInt64PointerPointer
        | CType::Float32Pointer
        | CType::Float64Pointer
        | CType::Float32PointerPointer
        | CType::Float64PointerPointer
        | CType::FunctionPointer(_) => C_POINTER_BYTE_WIDTH,
        CType::Int32Array(length) => {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), length.saturating_mul(4)),
            );
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                CType::Int32,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        CType::UInt8Array(length) => {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), length),
            );
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                CType::UInt8,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        CType::Int8Array(length) => {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), length),
            );
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                CType::Int8,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        CType::Int16Array(length) => {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), length.saturating_mul(2)),
            );
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                CType::Int16,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        CType::UInt16Array(length) => {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), length.saturating_mul(2)),
            );
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                CType::UInt16,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        CType::UInt32Array(length) => {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), length.saturating_mul(4)),
            );
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                CType::UInt32,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        CType::Int64Array(length) => {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), length.saturating_mul(8)),
            );
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                CType::Int64,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        CType::UInt64Array(length) => {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), length.saturating_mul(8)),
            );
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                CType::UInt64,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        CType::Float32Array(length) => {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), length.saturating_mul(4)),
            );
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                CType::Float32,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        CType::Float64Array(length) => {
            state.set_memory(
                state
                    .memory
                    .clone()
                    .with_block(pointer.block.clone(), length.saturating_mul(8)),
            );
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                CType::Float64,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        CType::PointerArray(element, length) => {
            state.set_memory(state.memory.clone().with_block(
                pointer.block.clone(),
                length.saturating_mul(C_POINTER_BYTE_WIDTH),
            ));
            state.locals.set_array_object_at_with_constant(
                name.to_string(),
                element.pointer_type(),
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
    };
    state.set_memory(
        state
            .memory
            .clone()
            .with_block(pointer.block.clone(), byte_width),
    );
    if volatile {
        state.locals.set_uninitialized_with_all_qualifiers(
            name.to_string(),
            c_type,
            pointer,
            true,
            pointee_volatile,
            constant,
            pointee_constant,
        );
    } else {
        state.locals.set_uninitialized_with_all_qualifiers(
            name.to_string(),
            c_type,
            pointer,
            false,
            pointee_volatile,
            constant,
            pointee_constant,
        );
    }
    Ok(state)
}

pub(in crate::kernel) fn declare_aggregate_local(
    state: &CState,
    name: &str,
    layout: &CAggregateLayout,
) -> Result<CState, crate::kernel::LoanRefusalDiagnostic> {
    let mut state = state.clone();
    let pointer = local_declaration_pointer(&mut state, name)?;
    register_block_alignment(&pointer.block, layout.alignment_bytes());
    state.set_memory(
        state
            .memory
            .clone()
            .with_block(pointer.block.clone(), layout.size_bytes()),
    );
    state
        .locals
        .set_aggregate_object_at(name.to_string(), layout.clone(), pointer);
    Ok(state)
}

fn begin_aggregate_construction(
    state: &CState,
    name: &str,
    layout: &CAggregateLayout,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<CState, crate::kernel::LoanRefusalDiagnostic>> {
    let mut state = match declare_aggregate_local(state, name, layout) {
        Ok(state) => state,
        Err(refusal) => return Ok(Err(refusal)),
    };
    let pointer = state
        .locals
        .slot(name)
        .expect("aggregate construction has a declared stack slot")
        .clone();
    for field in layout.fields() {
        let variable = budget.allocate_kernel_variable()?;
        let value = crate::kernel::functions::symbolic_call_result(field.c_type(), variable);
        state.set_memory(
            state
                .memory
                .clone()
                .store(pointer.offset_by_bytes(field.offset_bytes()), value),
        );
    }
    state.resources = state
        .resources
        .clone()
        .unchecked_with_fact(CResourceFact::own_memory(
            CMemoryRange::new_with_element_width(
                pointer,
                Bitvector32Term::Constant(0),
                Bitvector32Term::Constant(layout.size_bytes()),
                1,
            ),
        ));
    Ok(Ok(state))
}

/// Brings a scalar local's binding back in step with the memory a store just
/// produced.
///
/// A scalar local is held twice: as a binding, which is what reading the name
/// returns, and — once its address is taken — as the cell at its stack slot.
/// A store through a pointer only writes the cell, so the binding has to be
/// told. Which addresses count is a question about *bytes*: `&v + 1` is a
/// different address from `&v` by every address test the kernel has, and a
/// one-byte store there still overwrites the second byte of an `int64` `v`.
/// Matching the slot address exactly left that binding holding the whole old
/// value, and the next read of the name returned it as if the store had not
/// happened.
///
/// So the store's byte interval is compared against the object's, and only a
/// store that covers the object completely, at its own address and in its own
/// type, may install its value. Any other store that reaches those bytes —
/// including one whose overlap is undecided — replaces the binding with the
/// read of the slot in the memory this store produced, which is what reading
/// the name now means. A store the bytes separate leaves the binding alone.
///
/// Bounded: one slot lookup keyed by the written block, then the shared byte
/// comparison against that one object. No scan of the frame.
fn refresh_scalar_local_after_memory_store(
    state: &mut CState,
    pointer: &Pointer,
    value: &CValue,
    assumptions: &PureFactContext,
) {
    let slot = Pointer {
        block: pointer.block.clone(),
        offset: PointerOffsetTerm::Constant(0),
    };
    let Some(name) = state.locals.name_for_slot(&slot).map(str::to_string) else {
        return;
    };
    let Some(c_type) = state.locals.scalar_object_type(&name) else {
        return;
    };
    let overlap = crate::kernel::reasoning::memory_resolution::access_byte_overlap(
        pointer,
        value.byte_width(),
        &slot,
        c_type.byte_width(),
        assumptions,
    );
    if overlap == crate::kernel::reasoning::memory_resolution::AccessByteOverlap::Separate {
        return;
    }
    let covers_whole_object = pointer == &slot
        && crate::kernel::reasoning::memory_resolution::StoreByteInterval::of(
            pointer,
            value.byte_width(),
        )
        .is_some_and(|written| written.overwrites_typed_completely(&slot, c_type))
        && c_type.accepts(value);
    let refreshed = if covers_whole_object {
        Some(value.clone())
    } else {
        crate::kernel::eval::symbolic_load_value(&state.memory, &slot, c_type)
    };
    let (object_volatile, object_pointee_volatile, object_pointee_constant) =
        match state.locals.binding(&name) {
            Some(CLocalBinding::Object {
                volatile,
                pointee_volatile,
                pointee_constant,
                ..
            })
            | Some(CLocalBinding::UninitializedObject {
                volatile,
                pointee_volatile,
                pointee_constant,
                ..
            }) => (*volatile, *pointee_volatile, *pointee_constant),
            _ => (false, false, false),
        };
    match refreshed {
        Some(refreshed) => state.locals.set_typed_with_all_qualifiers(
            name,
            refreshed,
            c_type,
            object_volatile,
            object_pointee_volatile,
            false,
            object_pointee_constant,
        ),
        // No symbolic form for this object's type: the binding must not keep
        // saying what it said before the store.
        None => state.locals.set_uninitialized_with_all_qualifiers(
            name,
            c_type,
            slot,
            object_volatile,
            object_pointee_volatile,
            false,
            object_pointee_constant,
        ),
    }
}

pub(in crate::kernel) fn sync_stack_local(state: &mut CState, name: &str, value: &CValue) {
    let Some(pointer) = state.locals.slot(name).cloned() else {
        return;
    };
    if state.memory.has_block(&pointer.block) {
        state.set_memory(state.memory.clone().store(pointer, value.clone()));
    }
}
