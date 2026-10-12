//! Scalar-array initialization and region writes. Storage and retained derivations
//! are compact; authority, source initialization, and coercion remain checked.
use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn execute(
    state: &CState,
    target: &CExpression,
    source: &CExpression,
    element_type: CType,
    count: u32,
    copy: bool,
    fresh: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<CStatementExecutionPath>> {
    let mut paths = Vec::new();
    if !matches!(element_type, CType::Int32 | CType::UInt8 | CType::UInt32) {
        return Ok(vec![path(
            CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            vec![].into(),
            vec![],
        )]);
    }
    let Some(bytes) = count
        .checked_mul(element_type.byte_width())
        .filter(|n| *n <= i32::MAX as u32)
    else {
        return Ok(vec![path(
            CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
            vec![].into(),
            vec![],
        )]);
    };
    for target in evaluate_c_expression_paths(state, target, assumptions, budget)? {
        let target_pointer = match target.outcome {
            CExpressionOutcome::Value(CValue::Pointer(pointer)) => pointer,
            outcome => {
                paths.push(path(
                    expression_error(outcome),
                    target.facts,
                    target.obligations,
                ));
                continue;
            }
        };
        let selected =
            assumptions_with_path_context(assumptions, &target.facts, &target.obligations);
        for source in evaluate_c_expression_paths(state, source, &selected, budget)? {
            let Some((facts, mut obligations)) = merge_execution_pure_facts_and_obligations(
                &target.facts,
                &target.obligations,
                &source.facts,
                &source.obligations,
                assumptions,
            ) else {
                continue;
            };
            let value = match source.outcome {
                CExpressionOutcome::Value(value) => value,
                outcome => {
                    paths.push(path(expression_error(outcome), facts, obligations));
                    continue;
                }
            };
            let selected = assumptions_with_path_context(assumptions, &facts, &obligations);
            let value = if copy {
                Some(value)
            } else {
                crate::kernel::functions::coerce_c_value_with_pointee_constant(
                    value,
                    element_type,
                    false,
                    &mut obligations,
                    &selected,
                )
            };
            let Some(value) = value else {
                paths.push(path(
                    CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                    facts,
                    obligations,
                ));
                continue;
            };
            // Whole declaration initialization stays compact even for nested
            // dimensions. Every partial/row-selected operation remains bounded
            // by its authenticated scalar domain.
            let target_check = state
                .memory()
                .complete_declared_array_storage(&target_pointer, element_type, count, &selected)
                .map(super::super::pointer_domains::PointerDomainCheck::Checked)
                .map(Ok)
                .unwrap_or_else(|| {
                    super::super::pointer_domains::checked_c_typed_pointer_span(
                        state,
                        &target_pointer,
                        IntegerTerm::constant_i64(0),
                        IntegerTerm::constant_i64(i64::from(count)),
                        element_type,
                        &selected,
                    )
                });
            let Some(refused) = super::super::operators::pointer_domain_refusal_paths(
                target_check,
                &facts,
                &obligations,
                assumptions,
                &CUndefinedBehavior::InvalidMemory,
            ) else {
                paths.push(path(
                    CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
                    facts,
                    obligations,
                ));
                continue;
            };
            for refused in refused {
                paths.push(path(
                    expression_error(refused.outcome),
                    refused.facts,
                    refused.obligations,
                ));
            }
            if copy && let CValue::Pointer(source) = &value {
                let source_check = state
                    .memory()
                    .complete_declared_array_storage(source, element_type, count, &selected)
                    .map(super::super::pointer_domains::PointerDomainCheck::Checked)
                    .map(Ok)
                    .unwrap_or_else(|| {
                        super::super::pointer_domains::checked_c_typed_pointer_span(
                            state,
                            source,
                            IntegerTerm::constant_i64(0),
                            IntegerTerm::constant_i64(i64::from(count)),
                            element_type,
                            &selected,
                        )
                    });
                let Some(refused) = super::super::operators::pointer_domain_refusal_paths(
                    source_check,
                    &facts,
                    &obligations,
                    assumptions,
                    &CUndefinedBehavior::InvalidMemory,
                ) else {
                    paths.push(path(
                        CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
                        facts,
                        obligations,
                    ));
                    continue;
                };
                for refused in refused {
                    paths.push(path(
                        expression_error(refused.outcome),
                        refused.facts,
                        refused.obligations,
                    ));
                }
            }
            let target = target_pointer.pointer();
            if bytes != 0
                && (target_pointer.pointee_constant()
                    || state.memory.is_read_only_block(&target.block))
            {
                paths.push(path(
                    CStatementOutcome::UndefinedBehavior(CUndefinedBehavior::InvalidMemory),
                    facts,
                    obligations,
                ));
                continue;
            }
            let required = CResourceFact::own_memory(CMemoryRange::new_with_element_width(
                target.clone(),
                0u32.into(),
                count.into(),
                element_type.byte_width(),
            ));
            if bytes != 0
                && !state
                    .resources()
                    .owns_storage_access(target, bytes, &selected)
            {
                paths.push(path(
                    CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                        resource: Box::new(required),
                    }),
                    facts,
                    obligations,
                ));
                continue;
            }
            if bytes != 0
                && let Some(outcome) =
                    memory_write_permission_outcome(state, target, bytes, &selected)
            {
                paths.push(path(outcome, facts, obligations));
                continue;
            }
            if copy && bytes != 0 {
                let CValue::Pointer(source) = &value else {
                    paths.push(path(
                        CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch),
                        facts,
                        obligations,
                    ));
                    continue;
                };
                if !crate::kernel::api::with_extended_dag_bridging(|| {
                    state
                        .resources()
                        .permits_storage_read(source.pointer(), bytes, &selected)
                }) {
                    let resource =
                        CResourceFact::view_memory(CMemoryRange::new_with_element_width(
                            source.pointer().clone(),
                            0u32.into(),
                            count.into(),
                            element_type.byte_width(),
                        ));
                    paths.push(path(
                        CStatementOutcome::RuntimeError(CRuntimeError::MissingResource {
                            resource: Box::new(resource),
                        }),
                        facts,
                        obligations,
                    ));
                    continue;
                }
            }
            let memory = if fresh {
                state.memory.clone().initialize_scalar_array(
                    target,
                    element_type,
                    count,
                    value,
                    copy,
                )
            } else {
                state.memory.clone().write_scalar_array_region(
                    target,
                    element_type,
                    count,
                    value,
                    copy,
                    false,
                    &selected,
                )
            };
            let outcome = match memory {
                Ok(memory) => {
                    let mut next = state.clone();
                    next.set_memory(memory);
                    if bytes != 0
                        && let CExpressionOutcome::Value(value) = next.memory.load(target)
                    {
                        refresh_scalar_local_after_memory_store(
                            &mut next, target, &value, &selected,
                        );
                    }
                    CStatementOutcome::Normal(Box::new(next))
                }
                Err(error) => CStatementOutcome::RuntimeError(error),
            };
            paths.push(path(outcome, facts, obligations));
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn path(
    outcome: CStatementOutcome,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
) -> CStatementExecutionPath {
    CStatementExecutionPath::new(outcome, facts, obligations)
}
fn expression_error(outcome: CExpressionOutcome) -> CStatementOutcome {
    match outcome {
        CExpressionOutcome::UndefinedBehavior(error) => CStatementOutcome::UndefinedBehavior(error),
        CExpressionOutcome::RuntimeError(error) => CStatementOutcome::RuntimeError(error),
        CExpressionOutcome::Value(_) => {
            CStatementOutcome::RuntimeError(CRuntimeError::TypeMismatch)
        }
    }
}
