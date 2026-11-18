//! Scalar-array initialization and region writes. Storage and retained derivations
//! are compact; authority, source initialization, and coercion remain checked.
use super::*;

#[allow(clippy::too_many_arguments)]
pub(super) fn execute(
    state: &ExecutionState,
    target: &ProgramExpression,
    source: &ProgramExpression,
    element_type: ProgramType,
    count: u32,
    copy: bool,
    fresh: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let mut paths = Vec::new();
    if !element_type.supports_scalar_array_write(copy) {
        return Ok(vec![path(
            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            vec![].into(),
            vec![],
        )]);
    }
    let Some(bytes) = count
        .checked_mul(element_type.byte_width())
        .filter(|n| *n <= i32::MAX as u32)
    else {
        return Ok(vec![path(
            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            vec![].into(),
            vec![],
        )]);
    };
    for target in evaluate_program_expression_paths(state, target, assumptions, budget)? {
        let target_pointer = match target.outcome {
            ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) => pointer,
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
        for source in evaluate_program_expression_paths(state, source, &selected, budget)? {
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
                ExpressionOutcome::Value(value) => value,
                outcome => {
                    paths.push(path(expression_error(outcome), facts, obligations));
                    continue;
                }
            };
            let selected = assumptions_with_path_context(assumptions, &facts, &obligations);
            let value = if copy {
                Some(value)
            } else {
                crate::kernel::functions::coerce_program_value_with_pointee_constant(
                    value,
                    element_type,
                    false,
                    &mut obligations,
                    &selected,
                )
            };
            let Some(value) = value else {
                paths.push(path(
                    StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                    facts,
                    obligations,
                ));
                continue;
            };
            let target = target_pointer.address();
            if bytes != 0
                && let Some(refusal) = subobject_access_refusal(
                    target,
                    &target_pointer,
                    bytes,
                    &facts,
                    &obligations,
                    &selected,
                )
            {
                paths.push(path(
                    StatementOutcome::UndefinedBehavior(refusal),
                    facts,
                    obligations,
                ));
                continue;
            }
            if bytes != 0
                && (target_pointer.pointee_constant()
                    || state.memory.is_read_only_block(&target.base))
            {
                paths.push(path(
                    StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
                    facts,
                    obligations,
                ));
                continue;
            }
            let required = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                target.clone(),
                0u32.into(),
                count.into(),
                element_type.byte_width(),
            ));
            if bytes != 0
                && !state.resources().owns_designated_storage_access(
                    target,
                    target_pointer.access_provenance(),
                    bytes,
                    &selected,
                )
            {
                paths.push(path(
                    StatementOutcome::RuntimeError(RuntimeError::MissingResource {
                        resource: Box::new(required),
                    }),
                    facts,
                    obligations,
                ));
                continue;
            }
            let write_refusal = if bytes == 0 {
                None
            } else if !fresh {
                let destination = MemoryRange::from_pointer_value(
                    &target_pointer,
                    0u32.into(),
                    count.into(),
                    element_type.byte_width(),
                );
                memory_region_write_obligation_outcome(
                    state,
                    target,
                    bytes,
                    &destination,
                    &selected,
                    &mut obligations,
                )
            } else {
                memory_write_permission_outcome(state, target, bytes, &selected)
            };
            if let Some(outcome) = write_refusal {
                paths.push(path(outcome, facts, obligations));
                continue;
            }
            if copy && bytes != 0 {
                let ProgramValue::Pointer(source) = &value else {
                    paths.push(path(
                        StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                        facts,
                        obligations,
                    ));
                    continue;
                };
                if let Some(refusal) = subobject_access_refusal(
                    source.address(),
                    source,
                    bytes,
                    &facts,
                    &obligations,
                    &selected,
                ) {
                    paths.push(path(
                        StatementOutcome::UndefinedBehavior(refusal),
                        facts,
                        obligations,
                    ));
                    continue;
                }
                if !crate::kernel::api::with_extended_dag_bridging(|| {
                    state.resources().permits_designated_storage_read(
                        source.address(),
                        Some(source.access_provenance()),
                        bytes,
                        &selected,
                    )
                }) {
                    let resource = ResourceFact::view_memory(MemoryRange::new_with_element_width(
                        source.address().clone(),
                        0u32.into(),
                        count.into(),
                        element_type.byte_width(),
                    ));
                    paths.push(path(
                        StatementOutcome::RuntimeError(RuntimeError::MissingResource {
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
                        && let ExpressionOutcome::Value(value) = next.memory.load(target)
                    {
                        refresh_scalar_local_after_memory_store(
                            &mut next,
                            target,
                            value.byte_width(),
                            &selected,
                        );
                    }
                    StatementOutcome::Normal(Box::new(next))
                }
                Err(error) => StatementOutcome::RuntimeError(error),
            };
            paths.push(path(outcome, facts, obligations));
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn path(
    outcome: StatementOutcome,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
) -> StatementExecutionPath {
    StatementExecutionPath::new(outcome, facts, obligations)
}
fn expression_error(outcome: ExpressionOutcome) -> StatementOutcome {
    match outcome {
        ExpressionOutcome::UndefinedBehavior(error) => StatementOutcome::UndefinedBehavior(error),
        ExpressionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
        ExpressionOutcome::Value(_) => StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
    }
}

/// Evaluate explicit initializers, then install and seal the complete array in
/// one declaration transition. Zero-filled gaps each take one retained run.
pub(super) fn construct_const(
    declared: &ExecutionState,
    name: &BindingName,
    element_type: ProgramType,
    fill: &ZeroFill,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let slot = declared.locals.slot(name).expect("declared array slot");
    let bytes = fill.count.checked_mul(fill.stride);
    let cells = fill.cells.as_ref();
    let (Some(bytes), [cell]) = (bytes, cells) else {
        return Ok(vec![path(
            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            Vec::new().into(),
            Vec::new(),
        )]);
    };
    if declared
        .memory
        .block_size(&slot.base)
        .and_then(MachineTerm::as_const)
        != Some(bytes)
        || element_type.byte_width() != fill.stride
        || cell.offset != 0
        || cell.value_type != element_type
    {
        return Ok(vec![path(
            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            Vec::new().into(),
            Vec::new(),
        )]);
    }
    let mut zero_obligations = Vec::new();
    let zero = crate::kernel::functions::coerce_program_value_with_pointee_constant(
        cell.zero.clone(),
        element_type,
        cell.pointee_constant,
        &mut zero_obligations,
        &PureFactContext::new(),
    )
    .filter(|_| zero_obligations.is_empty());
    let Some(zero) = zero else {
        return Ok(vec![path(
            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            Vec::new().into(),
            Vec::new(),
        )]);
    };

    let mut paths = Vec::new();
    for evaluation in crate::kernel::functions::evaluate_retained_program_arguments_paths(
        declared,
        fill.expressions(),
        assumptions,
        budget,
        None,
    )? {
        let mut obligations = evaluation.obligations;
        let outcome = match evaluation.outcome {
            Some(FunctionOutcome::UndefinedBehavior(error)) => {
                StatementOutcome::UndefinedBehavior(error)
            }
            Some(FunctionOutcome::RuntimeError(error)) => StatementOutcome::RuntimeError(error),
            Some(_) => unreachable!("expression evaluation returns values or errors"),
            None => {
                let selected =
                    assumptions_with_path_context(assumptions, &evaluation.facts, &obligations);
                let build_runs = || {
                    let mut runs = Vec::new();
                    let mut next = 0;
                    let mut push_run = |start, count, value| {
                        if count != 0 {
                            runs.push(ConstantRun {
                                offset: start * fill.stride,
                                stride: fill.stride,
                                count,
                                value,
                            });
                        }
                    };
                    for ((index, _), value) in fill.written_elements.iter().zip(evaluation.values) {
                        crate::instrumentation::record_deterministic_work(1);
                        if *index < next || *index >= fill.count {
                            return None;
                        }
                        let value =
                            crate::kernel::functions::coerce_program_value_with_pointee_constant(
                                value.into_native(),
                                element_type,
                                cell.pointee_constant,
                                &mut obligations,
                                &selected,
                            )?;
                        push_run(next, *index - next, zero.clone());
                        push_run(*index, 1, value);
                        next = *index + 1;
                    }
                    push_run(next, fill.count - next, zero.clone());
                    Some(runs)
                };
                match build_runs() {
                    Some(runs) => {
                        let memory = declared
                            .memory
                            .clone()
                            .seed_fresh_declared_runs(slot, &runs)
                            .with_initialized_object(slot, bytes)
                            .freeze_declared_object(&slot.base, None);
                        let mut state = declared.clone();
                        state.set_memory(memory);
                        StatementOutcome::Normal(Box::new(note_declared_population_storage(
                            state, name,
                        )))
                    }
                    None => StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                }
            }
        };
        paths.push(path(outcome, evaluation.facts, obligations));
    }
    Ok(paths)
}
