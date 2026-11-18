use super::*;
use crate::kernel::StatementStoreSource;
use crate::kernel::loans::{CheckedLoanCallEvidenceSequence, empty_checked_loan_evidence_sequence};
#[cfg(test)]
mod aggregate_results;
mod scalar_arrays;
#[cfg(test)]
mod unsigned_switch_tests;

#[cfg(test)]
pub(in crate::kernel) fn execute_execution_statement(
    state: &ExecutionState,
    statement: &ProgramStatement,
    assumptions: &PureFactContext,
) -> Option<StatementOutcome> {
    let paths = execute_execution_statement_paths(
        state,
        statement,
        assumptions,
        ExecutionContext::verify_loops(&ExecutionEnvironment::new()),
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

pub(in crate::kernel) fn execute_program_lvalue_assignment_paths(
    state: &ExecutionState,
    target: &ProgramExpression,
    value: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    execute_program_lvalue_assignment_paths_with_source(
        state,
        target,
        value,
        assumptions,
        budget,
        Default::default(),
    )
}

fn execute_program_lvalue_assignment_paths_with_source(
    state: &ExecutionState,
    target: &ProgramExpression,
    value: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    store_source: StatementStoreSource,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let bounds = indexed_store_bounds(state, target, assumptions);
    // Use the bounds only while preparing this statement. The driver gets the
    // original input context and must prove the condition before publishing
    // the prepared successor.
    let conditional_context = bounds.as_ref().map(|[lower, upper]| {
        assumptions
            .clone()
            .assume_proposition(lower.clone())
            .assume_proposition(upper.clone())
    });
    let execution_assumptions = conditional_context.as_ref().unwrap_or(assumptions);
    let mut paths = Vec::new();
    for target_path in evaluate_program_lvalue_paths(state, target, execution_assumptions, budget)?
    {
        let LValuePath {
            outcome: target_outcome,
            facts: target_facts,
            obligations: target_obligations,
        } = target_path;

        let target_lvalue = match target_outcome {
            LValueOutcome::LValue(lvalue) => lvalue,
            LValueOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::UndefinedBehavior(undefined_behavior),
                    target_facts,
                    target_obligations,
                ));
                continue;
            }
            LValueOutcome::RuntimeError(error) => {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(error),
                    target_facts,
                    target_obligations,
                ));
                continue;
            }
        };

        let value_assumptions =
            assumptions_with_path_context(assumptions, &target_facts, &target_obligations);
        for value_path in evaluate_expression_value_paths(state, value, &value_assumptions, budget)?
        {
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
                ExpressionOutcome::Value(value) => {
                    paths.extend(write_program_lvalue_paths_for_initialization(
                        state,
                        target_lvalue.clone(),
                        value,
                        facts,
                        obligations,
                        execution_assumptions,
                        budget,
                        false,
                        store_source.clone(),
                    )?)
                }
                ExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                    paths.push(StatementExecutionPath::new(
                        StatementOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    ))
                }
                ExpressionOutcome::RuntimeError(error) => paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(error),
                    facts,
                    obligations,
                )),
            }
        }
    }
    if let Some([lower, upper]) = bounds {
        let requirement = ProofObligation::verification_condition(Proposition::And(
            Box::new(lower),
            Box::new(upper),
        ))
        .with_context("indexed store requires an in-bounds index");
        for path in &mut paths {
            path.obligations.push(requirement.clone());
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// Bounds for a plain signed index into one directly held external array.
/// The block bucket supplies at most one owner. The original access check
/// still validates the chosen storage, provenance, and write permission.
fn indexed_store_bounds(
    state: &ExecutionState,
    target: &ProgramExpression,
    assumptions: &PureFactContext,
) -> Option<[Proposition; 2]> {
    if !assumptions.retains_required_obligations() {
        return None;
    }
    let (base, index) = match target {
        ProgramExpression::Load(pointer)
        | ProgramExpression::TypedLoad {
            pointer,
            value_type: ProgramType::Int32,
            ..
        } => match pointer.as_ref() {
            ProgramExpression::Add(base, index) => (base, index),
            _ => return None,
        },
        _ => return None,
    };
    let (ProgramExpression::Variable(base), ProgramExpression::Variable(index)) =
        (base.as_ref(), index.as_ref())
    else {
        return None;
    };
    let binding = |name, expected| match state.locals.binding(name) {
        Some(LocalBinding::Object {
            value,
            program_type,
            volatile: false,
            ..
        }) if *program_type == expected => Some(value.native()),
        _ => None,
    };
    let base = binding(base, ProgramType::Int32Pointer)?;
    let index = binding(index, ProgramType::Int32)?;
    let (ProgramValue::Pointer(base), ProgramValue::Int32(index)) = (base.as_ref(), index.as_ref())
    else {
        return None;
    };
    let address = base.address();
    if address.base != AddressBase::ExternalArgument
        || address != &address.object_base()
        || base.provenance() != &address.object_identity()
        || base.bounds().is_some()
        || index.as_const().is_some()
    {
        return None;
    }
    let mut owners = state.resources().owned_memory_facts_in_block(&address.base);
    let range = owners.next()?.memory_own_range()?;
    if owners.next().is_some()
        || range.base() != address
        || range.wide_bounds().is_some()
        || range.element_width() != ProgramType::Int32.byte_width()
        || range.start().as_const() != Some(0)
    {
        return None;
    }
    Some([
        Proposition::condition_is(
            ConditionTerm::signed_less_equal(range.start().clone(), index.clone()),
            true,
        ),
        Proposition::condition_is(
            ConditionTerm::signed_less_than(index.clone(), range.end().clone()),
            true,
        ),
    ])
}

fn execute_program_lvalue_update_paths(
    state: &ExecutionState,
    target: &ProgramExpression,
    operator: UpdateOperator,
    operand: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let source = match target {
        ProgramExpression::TypedLoad { source, .. } => source.as_ref(),
        _ => None,
    };
    let mut paths = Vec::new();
    for target_path in evaluate_program_lvalue_paths(state, target, assumptions, budget)? {
        let LValuePath {
            outcome,
            facts,
            obligations,
        } = target_path;
        let LValueOutcome::LValue(lvalue) = outcome else {
            let outcome = match outcome {
                LValueOutcome::UndefinedBehavior(error) => {
                    StatementOutcome::UndefinedBehavior(error)
                }
                LValueOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
                LValueOutcome::LValue(_) => unreachable!(),
            };
            paths.push(StatementExecutionPath::new(outcome, facts, obligations));
            continue;
        };
        let supported_integer_update = matches!(
            lvalue.value_type,
            ProgramType::Int8
                | ProgramType::Int16
                | ProgramType::Int32
                | ProgramType::UInt8
                | ProgramType::UInt16
                | ProgramType::UInt32
                | ProgramType::Int64
                | ProgramType::UInt64
        );
        let supported_float_update = matches!(
            (lvalue.value_type, operator),
            (
                ProgramType::Float32 | ProgramType::Float64,
                UpdateOperator::Add
            ) | (
                ProgramType::Float32 | ProgramType::Float64,
                UpdateOperator::Subtract
            ) | (
                ProgramType::Float32 | ProgramType::Float64,
                UpdateOperator::Multiply
            ) | (
                ProgramType::Float32 | ProgramType::Float64,
                UpdateOperator::Divide
            )
        );
        if !supported_integer_update && !supported_float_update {
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                facts,
                obligations,
            ));
            continue;
        }

        for current_path in read_program_lvalue_paths(
            state,
            LValueOutcome::LValue(lvalue.clone()),
            facts,
            obligations,
            source,
            assumptions,
            budget,
        )? {
            let ExpressionPath {
                outcome: current_outcome,
                facts: current_facts,
                obligations: current_obligations,
            } = current_path;
            let ExpressionOutcome::Value(current) = current_outcome else {
                let outcome = match current_outcome {
                    ExpressionOutcome::UndefinedBehavior(error) => {
                        StatementOutcome::UndefinedBehavior(error)
                    }
                    ExpressionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
                    ExpressionOutcome::Value(_) => unreachable!(),
                };
                paths.push(StatementExecutionPath::new(
                    outcome,
                    current_facts,
                    current_obligations,
                ));
                continue;
            };

            let operand_assumptions =
                assumptions_with_path_context(assumptions, &current_facts, &current_obligations);
            for operand_path in
                evaluate_program_expression_paths(state, operand, &operand_assumptions, budget)?
            {
                let ExpressionPath {
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
                let ExpressionOutcome::Value(operand_value) = operand_outcome else {
                    let outcome = match operand_outcome {
                        ExpressionOutcome::UndefinedBehavior(error) => {
                            StatementOutcome::UndefinedBehavior(error)
                        }
                        ExpressionOutcome::RuntimeError(error) => {
                            StatementOutcome::RuntimeError(error)
                        }
                        ExpressionOutcome::Value(_) => unreachable!(),
                    };
                    paths.push(StatementExecutionPath::new(outcome, facts, obligations));
                    continue;
                };

                let update_expression = program_update_expression(
                    operator,
                    ProgramExpression::Value(current.clone()),
                    ProgramExpression::Value(operand_value),
                );
                let update_assumptions =
                    assumptions_with_path_context(assumptions, &facts, &obligations);
                for result_path in evaluate_program_expression_paths(
                    state,
                    &update_expression,
                    &update_assumptions,
                    budget,
                )? {
                    let ExpressionPath {
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
                        ExpressionOutcome::Value(value) => {
                            paths.extend(write_program_lvalue_paths(
                                state,
                                lvalue.clone(),
                                value,
                                facts,
                                obligations,
                                assumptions,
                                budget,
                                Default::default(),
                            )?)
                        }
                        ExpressionOutcome::UndefinedBehavior(error) => {
                            paths.push(StatementExecutionPath::new(
                                StatementOutcome::UndefinedBehavior(error),
                                facts,
                                obligations,
                            ))
                        }
                        ExpressionOutcome::RuntimeError(error) => {
                            paths.push(StatementExecutionPath::new(
                                StatementOutcome::RuntimeError(error),
                                facts,
                                obligations,
                            ))
                        }
                    }
                }
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn program_update_expression(
    operator: UpdateOperator,
    left: ProgramExpression,
    right: ProgramExpression,
) -> ProgramExpression {
    let left = Box::new(left);
    let right = Box::new(right);
    match operator {
        UpdateOperator::Add => ProgramExpression::Add(left, right),
        UpdateOperator::Subtract => ProgramExpression::Subtract(left, right),
        UpdateOperator::Multiply => ProgramExpression::Multiply(left, right),
        UpdateOperator::Divide => ProgramExpression::Divide(left, right),
        UpdateOperator::Remainder => ProgramExpression::Remainder(left, right),
        UpdateOperator::ShiftLeft => ProgramExpression::ShiftLeft(left, right),
        UpdateOperator::ShiftRight => ProgramExpression::ShiftRight(left, right),
        UpdateOperator::BitwiseAnd => ProgramExpression::BitwiseAnd(left, right),
        UpdateOperator::BitwiseOr => ProgramExpression::BitwiseOr(left, right),
        UpdateOperator::BitwiseXor => ProgramExpression::BitwiseXor(left, right),
    }
}

pub(in crate::kernel) fn memory_write_permission_outcome(
    state: &ExecutionState,
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) -> Option<StatementOutcome> {
    let range = MemoryRange::new_with_element_width(
        pointer.clone(),
        MachineTerm::constant(0),
        MachineTerm::constant(1),
        bytes,
    );
    if let Some(error) = super::super::mutexes::storage_write_refusal(state, &range, assumptions) {
        return Some(StatementOutcome::RuntimeError(error));
    }
    if let Some(outcome) = stable_loan_memory_range_outcome(state, &range, assumptions) {
        return Some(outcome);
    }
    memory_write_ownership_outcome(state, range, assumptions)
}

/// Scalar writes report loan separation as an obligation. The driver chooses
/// its explicit proof or ordinary solve; this operation never searches loans.
fn memory_write_obligation_outcome(
    state: &ExecutionState,
    range: &MemoryRange,
    storage_pointer: &Address,
    assumptions: &PureFactContext,
    obligations: &mut Vec<ProofObligation>,
) -> Option<StatementOutcome> {
    let storage_range = range.with_base(storage_pointer.clone());
    if let Some(error) =
        super::super::mutexes::storage_write_refusal(state, &storage_range, assumptions)
    {
        return Some(StatementOutcome::RuntimeError(error));
    }
    require_write_loan_separation(state, range, obligations);
    memory_write_ownership_outcome(state, storage_range, assumptions)
}

fn require_write_loan_separation(
    state: &ExecutionState,
    range: &MemoryRange,
    obligations: &mut Vec<ProofObligation>,
) {
    if let Some(requirement) = state
        .loan_ledger()
        .and_then(|ledger| ledger.memory_access_requirement(range))
    {
        obligations.push(ProofObligation::verification_condition(requirement));
    }
}

fn memory_write_ownership_outcome(
    state: &ExecutionState,
    range: MemoryRange,
    assumptions: &PureFactContext,
) -> Option<StatementOutcome> {
    let pointer = range.base();
    let bytes = range.element_width();
    if state.memory.requires_explicit_scalar_ownership(pointer)
        && state
            .resources()
            .memory_write_range(pointer, bytes, assumptions)
            .is_none()
    {
        return Some(StatementOutcome::RuntimeError(
            RuntimeError::MissingResource {
                resource: Box::new(ResourceFact::own_memory(range)),
            },
        ));
    }
    None
}

fn stable_loan_memory_range_outcome(
    state: &ExecutionState,
    range: &MemoryRange,
    assumptions: &PureFactContext,
) -> Option<StatementOutcome> {
    state
        .stable_loan_memory_access_refusal(
            range,
            assumptions,
            crate::kernel::LoanRefusalOperation::MemoryAccess,
        )
        .map(|diagnostic| {
            StatementOutcome::RuntimeError(RuntimeError::LoanRefusal(Box::new(diagnostic)))
        })
}

pub(in crate::kernel) fn write_program_lvalue_paths(
    state: &ExecutionState,
    lvalue: LValue,
    value: ProgramValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    store_source: StatementStoreSource,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    write_program_lvalue_paths_for_initialization(
        state,
        lvalue,
        value.into(),
        facts,
        obligations,
        assumptions,
        budget,
        false,
        store_source,
    )
}

fn write_program_lvalue_paths_for_initialization(
    state: &ExecutionState,
    lvalue: LValue,
    value: ExecutionValue,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    initialization: bool,
    store_source: StatementStoreSource,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    if lvalue.is_constant() && !initialization {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
            facts,
            obligations,
        )]);
    }
    let mut obligations = obligations;
    let effective_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    // The current owned resource composition is proof authority for memory
    // separation even when callers retain only surface-synthesizable pure facts.
    // Attach its compact carrier directly while executing a write instead of
    // depending on eagerly materialized pair propositions.
    // A same-type value copy to a local whose address is never taken
    // cannot use separation evidence from other owned resources. Its backing
    // cell, if any, is private. Copying a pointer does not access its pointee;
    // all qualifier, ownership, and loan checks below still run.
    let direct_local_copy = value.program_type() == lvalue.value_type
        && matches!(&lvalue.storage, LValueStorage::Local { name }
            if state.locals.slot(name).is_none_or(|pointer|
                crate::kernel::block_is_never_address_taken_local(&pointer.base)));
    let effective_assumptions = if direct_local_copy {
        effective_assumptions
    } else {
        // The store is separated by what the writer owns now, not by every
        // composition stated earlier on the path.
        let owner = state
            .resources()
            .observable_facts_assuming_valid(&effective_assumptions)
            .into_iter()
            .find_map(|fact| match fact {
                Proposition::ResourceComposition(owner) => Some(owner),
                _ => None,
            });
        effective_assumptions.with_store_owner(owner)
    };
    let mut facts = facts;
    let constant = lvalue.is_constant();
    let is_volatile = lvalue.is_volatile();
    let value_type = lvalue.value_type;
    let pointee_volatile = lvalue.pointee_is_volatile();
    let pointee_constant = lvalue.pointee_is_constant();

    let volatile_pointer = is_volatile.then(|| lvalue.pointer(state)).flatten();
    // Storing a freed pointer moves it without using it, but an implicit
    // conversion to `_Bool` (or any non-pointer type) tests its value; see
    // `freed_pointer_use`.
    if !lvalue.value_type.is_pointer()
        && let Some(undefined_behavior) =
            retained_expression::freed_expression_value_pointer_use(state, &value, assumptions)
    {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::UndefinedBehavior(undefined_behavior),
            facts,
            obligations,
        )]);
    }
    let value = if value.shared().is_some()
        && value.program_type() == lvalue.value_type
        && matches!(
            value.program_type(),
            ProgramType::Bool
                | ProgramType::Float32
                | ProgramType::Float64
                | ProgramType::Parameter(_)
                | ProgramType::Int8
                | ProgramType::UInt8
                | ProgramType::Int16
                | ProgramType::UInt16
                | ProgramType::Int32
                | ProgramType::UInt32
                | ProgramType::Int64
                | ProgramType::UInt64
        ) {
        value
    } else {
        let Some(converted) = crate::kernel::functions::coerce_program_value_with_pointee_constant(
            value
                .native()
                .into_owned()
                .with_pointer_pointee_volatile(pointee_volatile),
            lvalue.value_type,
            pointee_constant,
            &mut obligations,
            &effective_assumptions,
        ) else {
            return Ok(vec![StatementExecutionPath::new(
                StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                facts,
                obligations,
            )]);
        };
        if converted.program_type().is_pointer() {
            value.retain_checked_pointer(converted)
        } else {
            converted.into()
        }
    };

    let lvalue_access_provenance = lvalue.provenance.as_deref().map(|root| {
        (
            root,
            if lvalue.bounds_known {
                None
            } else {
                lvalue.bounds_owner.as_deref()
            },
        )
    });
    let lvalue_bounds = lvalue.bounds.clone();
    let lvalue_bounds_owner = lvalue.bounds_owner.clone();
    let lvalue_domain_source = crate::kernel::assumptions::PointerDomainSource::Retained {
        bounds: lvalue_bounds.as_deref(),
        known: lvalue.bounds_known,
        opaque: lvalue_bounds_owner.as_deref(),
    };
    let lvalue_value_type = lvalue.value_type;
    let lvalue_classes = (lvalue.access_class(), lvalue.object_class());
    match lvalue.storage {
        // A local of an abstract type holds its value in its binding: its
        // object has no addressable bytes to store to.
        LValueStorage::Local { name } if matches!(lvalue_value_type, ProgramType::Parameter(_)) => {
            let mut state = state.clone();
            state
                .locals
                .set_typed(name, value.into_native(), lvalue_value_type);
            Ok(vec![StatementExecutionPath::new(
                StatementOutcome::Normal(Box::new(state)),
                facts,
                obligations,
            )])
        }
        LValueStorage::Local { name } => {
            if let Some(pointer) = state.locals.slot(&name)
                && let Some(refusal) = subobject_access_refusal(
                    pointer,
                    lvalue_domain_source,
                    lvalue_value_type.byte_width(),
                    &facts,
                    &obligations,
                    &effective_assumptions,
                )
            {
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::UndefinedBehavior(refusal),
                    facts,
                    obligations,
                )]);
            }
            if state
                .pending_thread_create
                .as_ref()
                .is_some_and(|pending| pending.protects_local(state, &name))
            {
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
                        "pending pthread create permits only external disjoint stores".to_string(),
                    )),
                    facts,
                    obligations,
                )]);
            }
            if let Some(pointer) = state.locals.slot(&name)
                && lvalue.provenance.as_deref().is_some_and(|origin| {
                    !effective_assumptions.provenance_equal(origin, &pointer.object_identity())
                        || !lvalue.bounds_known && lvalue.bounds_owner.is_some()
                })
                && state
                    .resources()
                    .designated_memory_write_range(
                        pointer,
                        lvalue_access_provenance,
                        value.program_type().byte_width(),
                        &effective_assumptions,
                    )
                    .is_none()
            {
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::MissingResource {
                        resource: Box::new(ResourceFact::own_memory(
                            MemoryRange::new_with_element_width(
                                pointer.clone(),
                                0u32.into(),
                                1u32.into(),
                                value.program_type().byte_width(),
                            ),
                        )),
                    }),
                    facts,
                    obligations,
                )]);
            }
            if let Some(pointer) = state.locals.slot(&name) {
                let bytes = value.program_type().byte_width();
                let outcome = if initialization
                    || crate::kernel::block_is_never_address_taken_local(&pointer.base)
                    || !state.memory.has_block(&pointer.base)
                {
                    memory_write_permission_outcome(state, pointer, bytes, &effective_assumptions)
                } else {
                    // Name the declared slot with the same carrier as `&name`.
                    let range = MemoryRange::from_pointer_value(
                        &Pointer::new(pointer.clone(), ProgramType::VoidPointer),
                        0u32.into(),
                        1u32.into(),
                        bytes,
                    );
                    memory_write_obligation_outcome(
                        state,
                        &range,
                        pointer,
                        &effective_assumptions,
                        &mut obligations,
                    )
                };
                if let Some(outcome) = outcome {
                    return Ok(vec![StatementExecutionPath::new(
                        outcome,
                        facts,
                        obligations,
                    )]);
                }
            }
            let mut state = state.clone();
            sync_retained_stack_local(&mut state, &name, &value);
            if let Some(pointer) = volatile_pointer {
                facts.push(volatile_access_fact(
                    budget,
                    VolatileAccessKind::Write,
                    pointer,
                    value_type,
                    value.clone(),
                )?);
            }
            state.locals.set_retained_typed_with_all_qualifiers(
                name,
                value,
                value_type,
                is_volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            );
            Ok(vec![StatementExecutionPath::new(
                StatementOutcome::Normal(Box::new(state)),
                facts,
                obligations,
            )])
        }
        LValueStorage::Memory { pointer } => {
            let retained_direct = value
                .shared()
                .filter(|root| {
                    root.ty() == &KernelType::Bool
                        || matches!(root.ty(), KernelType::Algebraic(_))
                        || FloatOperandView::from_shared(root).is_some()
                })
                .cloned();
            let retained_pointer = value
                .shared()
                .filter(|root| root.pointer_payload().is_some())
                .cloned();
            // The bit-field producer computes a different, combined byte below.
            // Ordinary writes keep their already-coerced execution operand.
            let retained_volatile_value = (is_volatile
                && !matches!(
                    &lvalue_classes.0,
                    Some(crate::kernel::effective_type::CAccessClass::BitFieldByte(_))
                ))
            .then(|| value.clone());
            // The loan obligation names the evaluated source lvalue. Keep its
            // address before storage chooses an equivalent owner's coordinates.
            let source_pointer = pointer.clone();
            if let Some(refusal) = subobject_access_refusal(
                &pointer,
                lvalue_domain_source,
                lvalue_value_type.byte_width(),
                &facts,
                &obligations,
                &effective_assumptions,
            )
            .or_else(|| {
                effective_type_refusal_of(
                    &state.memory,
                    &pointer,
                    lvalue_classes.0.clone(),
                    lvalue_classes.1.clone(),
                    AccessKind::Write,
                )
            }) {
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::UndefinedBehavior(refusal),
                    facts,
                    obligations,
                )]);
            }
            let pointer = resolve_local_pointer_alias(state, &pointer, &effective_assumptions);
            if state.pending_thread_create.is_some() && !is_external_memory_pointer(&pointer) {
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
                        "pending pthread create permits only external disjoint stores".to_string(),
                    )),
                    facts,
                    obligations,
                )]);
            }
            if state
                .memory
                .heap
                .pending_reallocations
                .values()
                .any(|pending| pending.old_pointer.base == pointer.base)
            {
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::UnresolvedAllocationOutcome),
                    facts,
                    obligations,
                )]);
            }
            if state.memory.is_ended_local_address(&pointer) {
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
                    facts,
                    obligations,
                )]);
            }
            if state
                .memory
                .is_deallocated_heap_address(&pointer, assumptions)
            {
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
                    facts,
                    obligations,
                )]);
            }
            if state.memory.is_read_only_block(&pointer.base) {
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
                    facts,
                    obligations,
                )]);
            }
            let is_external = is_external_memory_pointer(&pointer)
                || lvalue.provenance.as_deref().is_some_and(|origin| {
                    !effective_assumptions.provenance_equal(origin, &pointer.object_identity())
                        || !lvalue.bounds_known && lvalue.bounds_owner.is_some()
                });
            let authorized_range = is_external
                .then(|| {
                    state.resources().designated_memory_write_range(
                        &pointer,
                        lvalue_access_provenance,
                        value.byte_width(),
                        &effective_assumptions,
                    )
                })
                .flatten()
                .cloned();
            let has_external_write_resource = is_external && authorized_range.is_some();
            // Keep the checked owner's base for a captured external address
            // without an explicit additive spine. Ordinary source addresses
            // retain their typed field/index coordinates, which subsequent
            // loads use to find the stored cell.
            // The graph supplies an equal address, while the owner and exact
            // byte coverage above remain the authorization. This spelling
            // lets subsequent frame checks identify the same backing member.
            // A loaded pointer's displacement is such a spine: the read is
            // its base, as `parent->right` is a field of `parent`.
            let pointer = authorized_range
                .as_ref()
                .filter(|_| {
                    !matches!(pointer.offset, AddressOffset::Add(_, _))
                        && !matches!(pointer.base, AddressBase::LoadedPointer(_))
                })
                .and_then(|range| {
                    effective_assumptions
                        .equality_graph
                        .pointer_at_base(&pointer, range.base())
                })
                .unwrap_or(pointer);

            if is_external && !has_external_write_resource {
                let missing = MemoryRange::new_with_element_width(
                    pointer.clone(),
                    MachineTerm::constant(0),
                    MachineTerm::constant(1),
                    value.byte_width(),
                );
                // A live mutex holds storage its initialization consumed;
                // name it rather than the missing ownership.
                let error = crate::kernel::mutexes::consumed_storage_refusal(
                    state,
                    &missing,
                    &effective_assumptions,
                )
                .unwrap_or_else(|| RuntimeError::MissingResource {
                    resource: Box::new(ResourceFact::own_memory(missing)),
                });
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(error),
                    facts,
                    obligations,
                )]);
            }
            // Ownership was established above. Loan separation is a proof
            // obligation for the driver, not an alias search during the store.
            let mut write_range = MemoryRange::new_with_element_width(
                source_pointer,
                0u32.into(),
                1u32.into(),
                value.byte_width(),
            )
            .with_bounds_owner(lvalue.bounds_owner.clone(), lvalue.bounds_known)
            .with_typed_carrier();
            if let Some(provenance) = &lvalue.provenance {
                write_range = write_range.with_provenance(provenance.clone());
            }
            if let Some(outcome) = memory_write_obligation_outcome(
                state,
                &write_range,
                &pointer,
                &effective_assumptions,
                &mut obligations,
            ) {
                return Ok(vec![StatementExecutionPath::new(
                    outcome,
                    facts,
                    obligations,
                )]);
            }
            // An ordinary word at this external address already has its exact
            // checked width and payload. Byte assembly, worker deltas and
            // guarded iteration keep using their existing native consumers.
            if has_external_write_resource
                && write_range.base().base == AddressBase::ExternalArgument
                && write_range.base().offset.is_shallow()
                && pointer.base == AddressBase::ExternalArgument
                && !is_volatile
                && state.pending_thread_create.is_none()
                && !state.resources().has_iterated_facts()
                && let Some(stored) = value.shared().and_then(StoredMemoryValue::retained_word)
            {
                let bytes = stored.byte_width();
                let mut facts = facts;
                let effective_assumptions = store_composition_context(
                    state,
                    &pointer,
                    bytes,
                    &effective_assumptions,
                    &mut facts,
                );
                let before = state.memory.clone();
                let memory = before.clone().store_retained_classed_with_context(
                    pointer.clone(),
                    stored.clone(),
                    &effective_assumptions,
                    lvalue_classes
                        .0
                        .as_ref()
                        .and_then(|class| class.effective_type_of_store()),
                );
                let mut state = state.clone();
                state.set_memory_with_checked_stores(memory, true);
                let mut fact = ExecutionPureFact::certified_store(
                    before,
                    state.memory.clone(),
                    pointer.clone(),
                    stored,
                    authorized_range,
                );
                let certificate = fact
                    .certified_store
                    .as_mut()
                    .expect("fresh store certificate");
                certificate.source = store_source.clone();
                certificate.source_address = Some(write_range.base().clone());
                facts.push(fact);
                refresh_scalar_local_after_memory_store(
                    &mut state,
                    &pointer,
                    bytes,
                    &effective_assumptions,
                );
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::Normal(Box::new(state)),
                    facts,
                    obligations,
                )]);
            }
            let value = value.into_native();
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
            let value = if let Some(crate::kernel::effective_type::CAccessClass::BitFieldByte(
                mask,
            )) = &lvalue_classes.0
            {
                let ProgramValue::UInt8(incoming) = value else {
                    unreachable!("bit-field byte store has type uint8");
                };
                if !pointer.base.is_local_block() || !state.memory.access_in_bounds(&pointer, 1) {
                    return Ok(vec![StatementExecutionPath::new(
                        StatementOutcome::UndefinedBehavior(UndefinedBehavior::InvalidMemory),
                        facts,
                        obligations,
                    )]);
                }
                let mask = mask.get();
                let initialized = &state.memory.heap.initialized;
                let partial = initialized.partial_byte(&pointer);
                let old_full = super::byte_view::known_integer_byte(
                    &state.memory,
                    &pointer,
                    budget.program_byte_order(),
                );
                let before = if old_full.is_some() {
                    u8::MAX
                } else {
                    initialized.mask_at(&pointer)
                };
                let preserve = before & !mask;
                let written = super::byte_view::mask_byte(incoming, mask);
                let combined = if preserve == 0 {
                    written
                } else if let Some(old) = old_full.or_else(|| {
                    let ProgramValue::UInt8(value) = partial?.value.as_ref()? else {
                        return None;
                    };
                    Some(value.clone())
                }) {
                    super::byte_view::merge_byte_bits(
                        super::byte_view::mask_byte(old, preserve),
                        written,
                    )
                } else {
                    return Ok(vec![StatementExecutionPath::new(
                        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
                            "bit-field update requires the retained value of the other initialized bits in its byte".into(),
                        )),
                        facts,
                        obligations,
                    )]);
                };
                let value = ProgramValue::UInt8(combined);
                if before | mask != u8::MAX {
                    let mut state = state.clone();
                    let memory = state.memory.clone().store_partial_byte(
                        pointer,
                        before | mask,
                        value,
                        &effective_assumptions,
                    );
                    state.set_memory(memory);
                    return Ok(vec![StatementExecutionPath::new(
                        StatementOutcome::Normal(Box::new(state)),
                        facts,
                        obligations,
                    )]);
                }
                value
            } else {
                value
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
                    containing_integer_cell(&state.memory, &pointer, budget.program_byte_order())
                && let Some(updated) = integer_cell_with_byte(&cell, &value)
            {
                (cell.pointer, updated)
            } else if let Some(assembled) = assemble_declared_uint32_after_byte_store(
                &state.memory,
                &pointer,
                &value,
                budget.program_byte_order(),
            ) {
                assembled
            } else {
                (pointer.clone(), value.clone())
            };
            // A store to a guard cell of an iterated ownership fact is
            // permitted only where the fact claims nothing at that index
            // (`crate::kernel::iterated`); the plan respells the fact so the
            // write itself names a hole, and settles the hole afterwards.
            let iterated_plan = match crate::kernel::plan_iterated_guard_store(
                state,
                &written_pointer,
                &written_value,
                &effective_assumptions,
            ) {
                Ok(plan) => plan,
                Err(message) => {
                    return Ok(vec![StatementExecutionPath::new(
                        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message)),
                        facts,
                        obligations,
                    )]);
                }
            };
            let before_memory = state.memory.clone();
            let mut state = state.clone();
            if !iterated_plan.is_empty() {
                match iterated_plan.before_store(state.resources().clone()) {
                    Ok(resources) => state = state.with_resource_context(resources),
                    Err(message) => {
                        return Ok(vec![StatementExecutionPath::new(
                            StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message)),
                            facts,
                            obligations,
                        )]);
                    }
                }
            }
            // Cells a held folded instance owns one body layer down are kept
            // by the same partition law as cells of a flat member; the
            // composition that says so is assumed for this store and kept as
            // a path fact, so every later route that re-asks this store's
            // framing reads the same members
            // (`functions::store_opened_instance_composition`).
            let mut facts = facts;
            let effective_assumptions = store_composition_context(
                &state,
                &written_pointer,
                written_value.byte_width(),
                &effective_assumptions,
                &mut facts,
            );
            let retained_written = if let Some(root) = retained_direct
                && ExecutionValue::Shared(root.clone()).program_type()
                    == written_value.program_type()
            {
                // Byte assembly produces an integer. An unchanged Boolean,
                // algebraic or float type keeps the original selected producer.
                ExecutionValue::Shared(root)
            } else {
                match retained_pointer {
                    Some(root) => {
                        ExecutionValue::Shared(root).retain_checked_pointer(written_value.clone())
                    }
                    None => ExecutionValue::from(written_value.clone()).retain_pointer_result(),
                }
            };
            let next_memory = state.memory.clone().store_retained_classed_with_context(
                written_pointer.clone(),
                retained_written,
                &effective_assumptions,
                lvalue_classes
                    .0
                    .as_ref()
                    .and_then(|class| class.effective_type_of_store()),
            );
            state.set_memory_with_checked_stores(next_memory, true);
            if !iterated_plan.is_empty() {
                match iterated_plan.after_store(state.resources().clone()) {
                    Ok(resources) => state = state.with_resource_context(resources),
                    Err(message) => {
                        return Ok(vec![StatementExecutionPath::new(
                            StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message)),
                            facts,
                            obligations,
                        )]);
                    }
                }
            }
            if let Some(pending) = &state.pending_thread_create {
                state.pending_thread_create = Some(pending.with_delta(
                    super::super::threads::PendingThreadMemoryDelta::Store {
                        pointer: written_pointer.clone(),
                        value: written_value.clone(),
                    },
                ));
            }
            let mut facts = facts;
            let mut store_fact = ExecutionPureFact::certified_store(
                before_memory,
                state.memory.clone(),
                written_pointer.clone(),
                written_value.clone(),
                authorized_range,
            );
            let certificate = store_fact
                .certified_store
                .as_mut()
                .expect("fresh store certificate");
            certificate.source = store_source.clone();
            let source_address = write_range.base();
            if !is_volatile
                && written_value.program_type() == ProgramType::UInt32
                && source_address.base == AddressBase::ExternalArgument
                && source_address.offset.is_shallow()
            {
                certificate.source_address = Some(source_address.clone());
            }
            facts.push(store_fact);
            // The checked store establishes the complete pointer value at
            // this exact state. Retain its read equation so congruence
            // can use a different, proven-equal address spelling without
            // re-running store resolution at the subsequent read.
            if let ProgramValue::Pointer(stored) = &written_value {
                facts.push(ExecutionPureFact::logical_read_equation(
                    stored.clone(),
                    Address::canonical_read(
                        &crate::kernel::intern_memory_ref(state.memory()),
                        &written_pointer,
                    ),
                ));
            }
            refresh_scalar_local_after_memory_store(
                &mut state,
                &written_pointer,
                written_value.byte_width(),
                &effective_assumptions,
            );
            if is_volatile {
                facts.push(volatile_access_fact(
                    budget,
                    VolatileAccessKind::Write,
                    pointer,
                    value_type,
                    retained_volatile_value.unwrap_or_else(|| value.into()),
                )?);
            }
            Ok(vec![StatementExecutionPath::new(
                StatementOutcome::Normal(Box::new(state)),
                facts,
                obligations,
            )])
        }
    }
}

fn store_composition_context(
    state: &ExecutionState,
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
    facts: &mut ExecutionFacts,
) -> PureFactContext {
    if let Some(opened) = crate::kernel::functions::store_opened_instance_composition(
        state,
        pointer,
        bytes,
        assumptions,
    ) {
        facts.push(ExecutionPureFact::new(Proposition::ResourceComposition(
            opened.clone(),
        )));
        assumptions.clone().with_additional_store_owner(opened)
    } else {
        assumptions.clone()
    }
}

/// End only the anonymous objects explicitly selected by this expression boundary.
fn end_aggregate_step_lifetimes(
    state: &ExecutionState,
    steps: &[u32],
) -> Result<ExecutionState, RuntimeError> {
    let mut next = state.clone();
    for step in steps {
        crate::instrumentation::record_deterministic_work(1);
        let Some(pointer) = next.aggregate_step_objects.get(step).cloned() else {
            continue;
        };
        next.aggregate_step_objects.remove(step);
        if let Some(error) = next.population_storage_retirement_refusal(&pointer.base) {
            return Err(error);
        }
        if let Some(error) = crate::kernel::mutexes::automatic_storage_refusal(
            &next,
            "aggregate expression result",
            &pointer.base,
        ) {
            return Err(error);
        }
        let Some(bytes) = next.memory.block_size(&pointer.base).cloned() else {
            continue;
        };
        let range = MemoryRange::new_with_element_width(pointer.clone(), 0.into(), bytes, 1);
        if let Some(error) = next.automatic_storage_loan_refusal(&pointer.base) {
            return Err(error);
        }
        retire_automatic_storage_owner(&mut next, &range);
        next.set_memory(next.memory.without_local_block(&pointer.base));
        next.retire_population_storage(&pointer.base)?;
    }
    next.end_step_results(steps);
    Ok(next)
}

/// Materialize an aggregate step in typed anonymous storage, with no local binding.
fn execute_program_aggregate_step_paths(
    state: &ExecutionState,
    steps: &[u32],
    expression: &ProgramExpression,
    result_layout: &AggregateResultLayout,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let layout = &result_layout.layout;
    let pointer = Address {
        base: AddressBase::Temporary(budget.allocate_kernel_variable()?.0),
        offset: AddressOffset::constant(0),
    };
    register_block_alignment(&pointer.base, layout.alignment_bytes());
    let mut allocated = state.clone();
    allocated.set_memory(allocated.memory.clone().with_classed_block(
        pointer.base.clone(),
        result_layout.declared_class.clone(),
        layout.size_bytes(),
    ));
    allocated.resources =
        allocated
            .resources
            .clone()
            .unchecked_with_fact(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(
                    pointer.clone(),
                    0.into(),
                    layout.size_bytes().into(),
                    1,
                ),
            ));
    let result = ProgramValue::typed_pointer(pointer.clone(), ProgramType::UInt8Pointer);
    let mut paths = execute_program_aggregate_copy_paths(
        &allocated,
        &ProgramExpression::Value(result.clone()),
        expression,
        layout,
        AggregateCopyDestination::ResultTemporary,
        assumptions,
        budget,
    )?;
    for path in &mut paths {
        if let StatementOutcome::Normal(next) = &mut path.outcome {
            next.set_memory(
                next.memory
                    .clone()
                    .freeze_aggregate_result(&pointer.base, None),
            );
            for step in steps {
                next.set_retained_step_result(
                    *step,
                    ExecutionValue::from(result.clone()).retain_pointer_result(),
                );
                next.aggregate_step_objects.insert(*step, pointer.clone());
            }
        }
    }
    Ok(paths)
}

#[derive(Clone, Copy)]
enum AggregateCopyDestination {
    Assignment,
    ResultTemporary,
}

fn memory_region_write_obligation_outcome(
    state: &ExecutionState,
    pointer: &Address,
    bytes: u32,
    destination: &MemoryRange,
    assumptions: &PureFactContext,
    obligations: &mut Vec<ProofObligation>,
) -> Option<StatementOutcome> {
    #[cfg(test)]
    let _fast = crate::kernel::search::FastOperationScope::enter("memory region write loan check");
    let storage =
        MemoryRange::new_with_element_width(pointer.clone(), 0u32.into(), 1u32.into(), bytes);
    if let Some(error) = super::super::mutexes::storage_write_refusal(state, &storage, assumptions)
    {
        return Some(StatementOutcome::RuntimeError(error));
    }
    if let Some(outcome) = memory_write_ownership_outcome(state, storage, assumptions) {
        return Some(outcome);
    }
    require_write_loan_separation(state, destination, obligations);
    None
}

fn execute_program_aggregate_copy_paths(
    state: &ExecutionState,
    target: &ProgramExpression,
    source: &ProgramExpression,
    layout: &AggregateLayout,
    destination: AggregateCopyDestination,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let mut paths = Vec::new();
    for target_path in evaluate_program_expression_paths(state, target, assumptions, budget)? {
        let ExpressionPath {
            outcome: target_outcome,
            facts: target_facts,
            obligations: target_obligations,
        } = target_path;
        let ExpressionOutcome::Value(ProgramValue::Pointer(target_pointer)) = target_outcome else {
            continue;
        };
        if target_pointer.is_null() {
            continue;
        }
        let value_assumptions =
            assumptions_with_path_context(assumptions, &target_facts, &target_obligations);
        for source_path in
            evaluate_program_expression_paths(state, source, &value_assumptions, budget)?
        {
            let ExpressionPath {
                outcome: source_outcome,
                facts: source_facts,
                obligations: source_obligations,
            } = source_path;
            let Some((facts, mut obligations)) = merge_execution_pure_facts_and_obligations(
                &target_facts,
                &target_obligations,
                &source_facts,
                &source_obligations,
                assumptions,
            ) else {
                continue;
            };
            let ExpressionOutcome::Value(ProgramValue::Pointer(source_pointer)) = source_outcome
            else {
                continue;
            };
            if source_pointer.is_null() {
                continue;
            }
            let copy_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
            if let Some(refusal) = subobject_access_refusal(
                source_pointer.address(),
                &source_pointer,
                layout.size_bytes(),
                &facts,
                &obligations,
                &copy_assumptions,
            )
            .or_else(|| {
                subobject_access_refusal(
                    target_pointer.address(),
                    &target_pointer,
                    layout.size_bytes(),
                    &facts,
                    &obligations,
                    &copy_assumptions,
                )
            }) {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::UndefinedBehavior(refusal),
                    facts,
                    obligations,
                ));
                continue;
            }
            if let Some(resource) = missing_aggregate_copy_read_resource(
                state,
                &source_pointer,
                layout,
                &copy_assumptions,
            ) {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::MissingResource {
                        resource: Box::new(resource),
                    }),
                    facts,
                    obligations,
                ));
                continue;
            }
            let write_refusal = match destination {
                AggregateCopyDestination::Assignment => {
                    // The byte slice covers the entire layout, including padding.
                    let bytes = layout.size_bytes();
                    let byte_pointer = super::expression::cast_pointer_value(
                        target_pointer.clone(),
                        ProgramType::UInt8Pointer,
                    );
                    let range = MemoryRange::from_pointer_value(
                        &byte_pointer,
                        0u32.into(),
                        bytes.into(),
                        1,
                    );
                    memory_region_write_obligation_outcome(
                        state,
                        target_pointer.address(),
                        bytes,
                        &range,
                        &copy_assumptions,
                        &mut obligations,
                    )
                }
                AggregateCopyDestination::ResultTemporary => memory_write_permission_outcome(
                    state,
                    target_pointer.address(),
                    layout.size_bytes(),
                    &copy_assumptions,
                ),
            };
            if let Some(outcome) = write_refusal {
                paths.push(StatementExecutionPath::new(outcome, facts, obligations));
                continue;
            }
            if let Some(resource) = missing_aggregate_copy_write_resource(
                state,
                &target_pointer,
                layout,
                &copy_assumptions,
            ) {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::MissingResource {
                        resource: Box::new(resource),
                    }),
                    facts,
                    obligations,
                ));
                continue;
            }
            let mut state = state.clone();
            let next_memory = match crate::kernel::functions::copy_aggregate_fields_checked(
                state.memory.clone(),
                source_pointer.address(),
                target_pointer.address(),
                layout,
            ) {
                Ok(memory) => memory,
                Err(undefined_behavior) => {
                    paths.push(StatementExecutionPath::new(
                        StatementOutcome::UndefinedBehavior(undefined_behavior),
                        facts,
                        obligations,
                    ));
                    continue;
                }
            };
            state.set_memory(next_memory);
            paths.push(StatementExecutionPath::new(
                StatementOutcome::Normal(Box::new(state)),
                facts,
                obligations,
            ));
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn missing_aggregate_copy_write_resource(
    state: &ExecutionState,
    target: &Pointer,
    layout: &AggregateLayout,
    assumptions: &PureFactContext,
) -> Option<ResourceFact> {
    if !is_external_memory_pointer(target)
        && target.bounds_are_known()
        && assumptions.provenance_equal(target.provenance(), &target.address().object_identity())
    {
        return None;
    }
    let ranges = layout
        .fields()
        .iter()
        .map(|field| (field.offset_bytes(), field.program_type().byte_width()))
        .chain(
            layout
                .unions()
                .iter()
                .map(|union| (union.offset_bytes(), union.size_bytes())),
        );
    for (offset, bytes) in ranges {
        let pointer = target.offset_by_bytes(offset);
        if state
            .resources()
            .designated_memory_write_range(
                &pointer,
                Some(target.access_provenance()),
                bytes,
                assumptions,
            )
            .is_none()
        {
            return Some(ResourceFact::own_memory(
                MemoryRange::new_with_element_width(
                    pointer,
                    MachineTerm::constant(0),
                    MachineTerm::constant(1),
                    bytes,
                ),
            ));
        }
    }
    None
}

pub(in crate::kernel) fn missing_aggregate_copy_read_resource(
    state: &ExecutionState,
    source: &Pointer,
    layout: &AggregateLayout,
    assumptions: &PureFactContext,
) -> Option<ResourceFact> {
    // A modular by-value return creates fresh caller storage, just as a
    // body return materializes a local return object. Copying that value
    // does not borrow an external resource. Use the temporary's recorded
    // bounds, not merely its identity, to authorize this selected copy.
    if matches!(source.base, AddressBase::Temporary(_))
        && source.bounds_are_known()
        && assumptions.provenance_equal(source.provenance(), &source.address().object_identity())
        && state.memory.access_in_bounds(source, layout.size_bytes())
    {
        return None;
    }
    if (!crate::kernel::eval::is_external_memory_pointer(source)
        && source.bounds_are_known()
        && assumptions.provenance_equal(source.provenance(), &source.address().object_identity())
        && !state.memory.requires_explicit_scalar_ownership(source)
        && !assumptions.should_require_owned_expression_loads())
        || (assumptions.should_allow_symbolic_contract_loads()
            && !assumptions.should_require_owned_expression_loads())
    {
        return None;
    }
    for field in layout.fields() {
        crate::instrumentation::record_deterministic_work(1);
        if !state.resources().permits_designated_memory_read(
            &source.offset_by_bytes(field.offset_bytes()),
            Some(source.access_provenance()),
            field.program_type().byte_width(),
            assumptions,
        ) {
            return Some(ResourceFact::view_memory(
                MemoryRange::new_with_element_width(
                    source.offset_by_bytes(field.offset_bytes()),
                    MachineTerm::constant(0),
                    MachineTerm::constant(1),
                    crate::kernel::assumptions::read_candidate_byte_width(
                        field.program_type().byte_width(),
                    ),
                ),
            ));
        }
    }
    for union in layout.unions() {
        crate::instrumentation::record_deterministic_work(1);
        let pointer = source.offset_by_bytes(union.offset_bytes());
        if !state.resources().permits_designated_memory_read(
            &pointer,
            Some(source.access_provenance()),
            union.size_bytes(),
            assumptions,
        ) {
            return Some(ResourceFact::view_memory(
                MemoryRange::new_with_element_width(
                    pointer,
                    MachineTerm::constant(0),
                    MachineTerm::constant(1),
                    union.size_bytes(),
                ),
            ));
        }
    }
    None
}

#[derive(Clone, Copy)]
enum AllocationDestination<'a> {
    Local(&'a BindingName),
    Value(ProgramType),
}

impl AllocationDestination<'_> {
    fn program_type(self, state: &ExecutionState) -> Option<ProgramType> {
        match self {
            Self::Local(name) => state.local_object_type(name),
            Self::Value(program_type) => Some(program_type),
        }
    }

    fn finish(
        self,
        state: &ExecutionState,
        value: ProgramValue,
        assumptions: &PureFactContext,
        budget: &mut ExecutionBudget,
    ) -> ExecutionResult<Vec<StatementExecutionPath>> {
        match self {
            Self::Local(name) => execute_program_lvalue_assignment_paths(
                state,
                &crate::kernel::program_expression::variable(name),
                &ProgramExpression::Value(value),
                assumptions,
                budget,
            ),
            Self::Value(_) => Ok(vec![
                StatementExecutionPath::new(
                    StatementOutcome::Normal(Box::new(state.clone())),
                    Vec::new().into(),
                    Vec::new(),
                )
                .with_call_result(Some(value)),
            ]),
        }
    }
}

pub(super) fn execute_program_heap_allocate_paths(
    state: &ExecutionState,
    target: &BindingName,
    bytes_expression: &ProgramExpression,
    zeroed: bool,
    object_type: Option<&(crate::kernel::effective_type::CAccessClass, u32, u32)>,
    ends_program_on_failure: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    execute_program_heap_allocate_to_paths(
        state,
        AllocationDestination::Local(target),
        bytes_expression,
        zeroed,
        object_type,
        ends_program_on_failure,
        assumptions,
        budget,
    )
}

fn execute_program_heap_allocate_to_paths(
    state: &ExecutionState,
    target: AllocationDestination<'_>,
    bytes_expression: &ProgramExpression,
    zeroed: bool,
    object_type: Option<&(crate::kernel::effective_type::CAccessClass, u32, u32)>,
    ends_program_on_failure: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let Some(
        target_type @ (ProgramType::Int32Pointer
        | ProgramType::UInt8Pointer
        | ProgramType::Int16Pointer
        | ProgramType::UInt16Pointer
        | ProgramType::UInt32Pointer
        | ProgramType::Int128Pointer
        | ProgramType::Int64Pointer
        | ProgramType::UInt128Pointer
        | ProgramType::UInt64Pointer
        | ProgramType::Int32PointerPointer
        | ProgramType::UInt8PointerPointer
        | ProgramType::Int16PointerPointer
        | ProgramType::UInt16PointerPointer
        | ProgramType::UInt32PointerPointer
        | ProgramType::Int128PointerPointer
        | ProgramType::Int64PointerPointer
        | ProgramType::UInt128PointerPointer
        | ProgramType::UInt64PointerPointer),
    ) = target.program_type(state)
    else {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            Vec::new().into(),
            Vec::new(),
        )]);
    };
    let element_width = target_type
        .pointee_type()
        .expect("heap allocation target has a pointee type")
        .byte_width();

    // calloc's size is its count of `count_width`-byte elements: the count
    // alone is evaluated, never the product (`design/heap-allocation-sizes.md`,
    // stage 4).
    let (element_count_expression, count_width) =
        match zeroed.then(|| calloc_operands(bytes_expression)).flatten() {
            Some((count, width)) => (Some(count), width),
            None => (
                heap_element_count_expression(bytes_expression, element_width),
                element_width,
            ),
        };
    let evaluated_size_expression = element_count_expression.unwrap_or(bytes_expression);
    let mut paths = Vec::new();
    for size_path in
        evaluate_program_expression_paths(state, evaluated_size_expression, assumptions, budget)?
    {
        let ExpressionPath {
            outcome,
            facts,
            obligations,
        } = size_path;
        let ExpressionOutcome::Value(value) = outcome else {
            let outcome = match outcome {
                ExpressionOutcome::UndefinedBehavior(error) => {
                    StatementOutcome::UndefinedBehavior(error)
                }
                ExpressionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
                ExpressionOutcome::Value(_) => {
                    StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
                }
            };
            paths.push(StatementExecutionPath::new(outcome, facts, obligations));
            continue;
        };
        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        let refusal = allocation_size_refusal(&value);
        let Some(size) = allocation_size_value(value, &effective_assumptions) else {
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(refusal),
                facts,
                obligations,
            ));
            continue;
        };
        // calloc's `n * w` is not a `size_t` product (it returns null when
        // the product is not representable), so it is never evaluated as
        // one: its count must be decided `1 <= n <= PTRDIFF_MAX / w`, and a
        // 64-bit size calloc does not split into its operands is refused.
        let (bytes, size_refusal) = if zeroed
            && element_count_expression.is_none()
            && size.kind == AllocationSizeKind::UInt64
        {
            (
                size.into_allocation_size(),
                Some(RuntimeError::HeapAllocationSize),
            )
        } else if element_count_expression.is_some() {
            let refusal =
                allocation_size_validity_refusal(&size, count_width, true, &effective_assumptions);
            let wrapped = if zeroed {
                None
            } else {
                size.wrapped_product(count_width, &effective_assumptions)
            };
            match (refusal, wrapped) {
                // An inexact `size_t` product is the block `malloc`
                // allocates: its wrapped value, admitted as a raw byte count.
                (Some(_), Some(product)) => {
                    let refusal = allocation_size_validity_refusal(
                        &product,
                        1,
                        false,
                        &effective_assumptions,
                    );
                    (product.into_allocation_size(), refusal)
                }
                (refusal, _) => (size.scaled(count_width).into_allocation_size(), refusal),
            }
        } else {
            // Heap blocks are byte-addressed even when the receiving pointer
            // has a wider logical element type. Typed accesses still carry
            // their own width and must fit in the resulting byte size.
            let refusal = allocation_size_validity_refusal(&size, 1, false, &effective_assumptions);
            (size.into_allocation_size(), refusal)
        };
        if let Some(refusal) = size_refusal {
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(refusal),
                facts,
                obligations,
            ));
            continue;
        }

        // An identity the heap already uses is skipped through the same
        // counter, so it is spent here rather than left for a later
        // allocation to hand to something else.
        let pointer = loop {
            let identity = budget.allocate_kernel_variable()?;
            if !state.memory.heap_identity_in_use(identity.0) {
                break Address::symbolic(identity);
            }
        };
        // A failure that ends the program leaves no execution to continue:
        // the one that does is the success, whose pointer is not null.
        let mut facts = facts;
        if ends_program_on_failure {
            add_internal_condition_path_fact(
                &mut facts,
                &effective_assumptions,
                pointer_is_null_condition(pointer.clone()),
                false,
            )
            .expect("a fresh allocation's success is consistent");
        }
        let object_class = object_type.and_then(|(class, size, alignment)| {
            let enough_space =
                bytes.unsigned_less_equal(bytes.constant(*size), bytes.bytes().clone());
            (*alignment as u64 <= crate::kernel::primitives::HEAP_ALLOCATION_ALIGNMENT
                && effective_assumptions.decide(&enough_space) == Some(true))
            .then(|| class.clone())
        });
        let mut success_state =
            state
                .clone()
                .with_memory(state.memory.clone().with_pending_typed_heap_allocation(
                    pointer.clone(),
                    bytes,
                    zeroed,
                    object_class.clone(),
                ));
        success_state.record_pending_population_storage_creation(pointer.base.clone());
        let assigned = target.finish(
            &success_state,
            ProgramValue::typed_pointer(pointer, target_type)
                .with_pointer_object_class(object_class),
            &effective_assumptions,
            budget,
        )?;
        for assigned_path in assigned {
            let Some((merged_facts, mut merged_obligations)) =
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
            // Its success already known, the allocation is a live block now.
            let outcome = match assigned_path.outcome {
                StatementOutcome::Normal(state) if ends_program_on_failure => {
                    StatementOutcome::Normal(Box::new(resolve_pending_heap_allocations_recording(
                        &state,
                        &assumptions_with_path_context(
                            assumptions,
                            &merged_facts,
                            &merged_obligations,
                        ),
                        &mut merged_obligations,
                    )))
                }
                outcome => outcome,
            };
            paths.push(
                StatementExecutionPath::new(outcome, merged_facts, merged_obligations)
                    .with_call_result(assigned_path.call_result),
            );
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn heap_allocation_element_width(state: &ExecutionState, base: &Address) -> u32 {
    state
        .locals
        .bindings
        .values()
        .find_map(|binding| {
            let LocalBinding::Object {
                value,
                program_type,
                ..
            } = binding
            else {
                return None;
            };
            let pointer = value.pointer()?;
            (pointer.address() == base)
                .then(|| program_type.pointee_type().map(ProgramType::byte_width))
                .flatten()
        })
        .unwrap_or(ProgramType::Int32.byte_width())
}

/// Heap ownership is expressed in the narrowest logical unit that exactly
/// describes the block. Preserve typed ranges for established allocation
/// forms, but use bytes for a raw size that is not divisible by the pointer's
/// logical element width.
fn heap_range_element_width(size: &AllocationSize, requested_width: u32) -> u32 {
    size.element_count(requested_width)
        .map(|_| requested_width)
        .unwrap_or(ProgramType::UInt8.byte_width())
}

/// The owned range of a whole heap block, `base[0..count]` in the size's
/// index kind, and its element width ([`heap_range_element_count`]).
fn heap_block_range(
    base: Address,
    size: &AllocationSize,
    requested_width: u32,
) -> (MemoryRange, u32) {
    let (count, width) = heap_range_element_count(size, requested_width);
    (size.range(base, count, width), width)
}

/// The element count and width of a whole heap block's owned range, in the
/// size's format ([`AllocationSize::element_count`]).
fn heap_range_element_count(size: &AllocationSize, requested_width: u32) -> (MachineTerm, u32) {
    let element_width = heap_range_element_width(size, requested_width);
    let element_count = size
        .element_count(element_width)
        .expect("byte width must describe every positive allocation size");
    (element_count, element_width)
}

#[derive(Clone, Debug)]
struct RequestedAllocationSize {
    term: MachineTerm,
    unsigned: bool,
    /// The size's type admits values above `INT32_MAX` (`uint32`), so the
    /// facts must bound it to the signed 32-bit allocation size.
    needs_size_bound: bool,
    /// The format of the block size this size makes, by its C type
    /// (`design/heap-allocation-sizes.md`, D1): `UInt64` for a symbolic 64-bit size,
    /// `Int32` for every other.
    kind: AllocationSizeKind,
    /// The size is a `size_t` in C, so `size * w` for a `size_t` or `int`
    /// constant `w` is C's wrapping `size_t` product. A `long` times an
    /// `int` constant may instead overflow, which is undefined.
    wraps: bool,
}

impl RequestedAllocationSize {
    /// A 32-bit size of the given signedness.
    fn int32(term: MachineTerm, unsigned: bool, needs_size_bound: bool) -> Self {
        Self {
            term,
            unsigned,
            needs_size_bound,
            kind: AllocationSizeKind::Int32,
            wraps: false,
        }
    }

    /// A symbolic 64-bit size as C's `size_t` argument: a `long` is read as
    /// its conversion, so a negative one is above `PTRDIFF_MAX`.
    fn uint64(term: MachineTerm, wraps: bool) -> Self {
        Self {
            term,
            unsigned: true,
            needs_size_bound: false,
            kind: AllocationSizeKind::UInt64,
            wraps,
        }
    }

    /// The value C computes for `self * element_width` when the facts do not
    /// prove the product exact: the wrapped `size_t` product of a `size_t`
    /// count (`design/heap-allocation-sizes.md`, stage 2), a real block of that many
    /// bytes. `None` for a `long` count, whose product may be undefined.
    fn wrapped_product(&self, element_width: u32, assumptions: &PureFactContext) -> Option<Self> {
        (self.kind == AllocationSizeKind::UInt64 && self.wraps).then(|| {
            let product = MachineTerm::uint64_multiply(
                self.term.clone(),
                MachineTerm::uint64_constant(u64::from(element_width)),
            );
            uint64_size_value(product, true, assumptions)
        })
    }

    /// The bytes of `self` elements of `element_width` bytes, in the size's
    /// format. Formed only once [`allocation_size_validity_refusal`] has
    /// decided the count fits, so the product does not wrap.
    fn scaled(&self, element_width: u32) -> Self {
        let term = match self.kind {
            AllocationSizeKind::Int32 => {
                MachineTerm::multiply(self.term.clone(), MachineTerm::constant(element_width))
            }
            AllocationSizeKind::UInt64 => MachineTerm::uint64_multiply(
                self.term.clone(),
                MachineTerm::uint64_constant(u64::from(element_width)),
            ),
        };
        Self {
            term,
            unsigned: self.unsigned,
            needs_size_bound: false,
            kind: self.kind,
            wraps: self.wraps,
        }
    }

    fn into_allocation_size(self) -> AllocationSize {
        AllocationSize::new(self.term, self.kind)
    }

    /// The size as a constant byte count, in either format.
    fn constant_bytes(&self) -> Option<u64> {
        match self.kind {
            AllocationSizeKind::Int32 => self.term.as_const().map(u64::from),
            AllocationSizeKind::UInt64 => self.term.uint64_as_const(),
        }
    }

    /// `bytes <= self`, compared in the size's format and signedness.
    fn at_least(&self, bytes: u32) -> ConditionTerm {
        match (self.kind, self.unsigned) {
            (AllocationSizeKind::UInt64, _) => uint64_size_at_least(&self.term, u64::from(bytes)),
            (AllocationSizeKind::Int32, true) => {
                ConditionTerm::unsigned_less_equal(MachineTerm::constant(bytes), self.term.clone())
            }
            (AllocationSizeKind::Int32, false) => {
                ConditionTerm::signed_less_equal(MachineTerm::constant(bytes), self.term.clone())
            }
        }
    }

    /// `self < bytes`, compared in the size's format and signedness.
    fn less_than(&self, bytes: u32) -> ConditionTerm {
        match (self.kind, self.unsigned) {
            (AllocationSizeKind::UInt64, _) => {
                let (count, bound) =
                    crate::kernel::reasoning::uint64_size_in_elements(&self.term, u64::from(bytes));
                ConditionTerm::uint64_less_than(count.clone(), bound)
            }
            (AllocationSizeKind::Int32, true) => {
                ConditionTerm::unsigned_less_than(self.term.clone(), MachineTerm::constant(bytes))
            }
            (AllocationSizeKind::Int32, false) => {
                ConditionTerm::signed_less_than(self.term.clone(), MachineTerm::constant(bytes))
            }
        }
    }
}

/// `bytes <= size` for an admitted 64-bit allocation size. A size `n * k`
/// with a constant `k` is exact ([`uint64_allocation_size_bytes_are_exact`]), so
/// the comparison is `ceil(bytes / k) <= n` over its element count, which
/// the facts about `n` decide where the wrapping product would not.
fn uint64_size_at_least(size: &MachineTerm, bytes: u64) -> ConditionTerm {
    let (count, bound) = crate::kernel::reasoning::uint64_size_in_elements(size, bytes);
    ConditionTerm::uint64_less_equal(bound, count.clone())
}

/// The constant zeroed prefix of a reallocated block: the smaller of the old
/// zeroed bytes and the new size, when that is a constant. Both constant, it
/// is their minimum; one constant, it is that one where the facts decide it
/// is the smaller. A prefix that is not a 32-bit constant is not modeled.
fn realloc_zeroed_prefix(
    old_prefix: &AllocationSize,
    new_size: &RequestedAllocationSize,
    assumptions: &PureFactContext,
) -> Option<u32> {
    let old_constant = match old_prefix.kind() {
        AllocationSizeKind::Int32 => old_prefix.bytes().as_const().map(u64::from),
        AllocationSizeKind::UInt64 => old_prefix.bytes().uint64_as_const(),
    };
    let prefix = match (old_constant, new_size.constant_bytes()) {
        (Some(old), Some(new)) => old.min(new),
        (Some(old), None) => {
            let old = u32::try_from(old).ok()?;
            (assumptions.decide(&new_size.at_least(old)) == Some(true)).then_some(u64::from(old))?
        }
        (None, Some(new)) => {
            let new = u32::try_from(new).ok()?;
            let shrinks = match old_prefix.kind() {
                AllocationSizeKind::Int32 => ConditionTerm::unsigned_less_equal(
                    MachineTerm::constant(new),
                    old_prefix.bytes().clone(),
                ),
                AllocationSizeKind::UInt64 => {
                    uint64_size_at_least(old_prefix.bytes(), u64::from(new))
                }
            };
            (assumptions.decide(&shrinks) == Some(true)).then_some(u64::from(new))?
        }
        (None, None) => return None,
    };
    u32::try_from(prefix).ok()
}

/// The refusal for a size [`allocation_size_value`] does not accept, or
/// `realloc` does not resize to: a 64-bit size is named as such, not as a
/// type error.
fn allocation_size_refusal(value: &ProgramValue) -> RuntimeError {
    match value.numeric_value() {
        ProgramValue::Int64(_) | ProgramValue::UInt64(_) => RuntimeError::HeapAllocationSize,
        _ => RuntimeError::TypeMismatch,
    }
}

/// The allocation size a C allocation size makes (`design/heap-allocation-sizes.md`,
/// D1 and D2). A 32-bit or narrower size is a checked 32-bit size, and so
/// is a 64-bit `size_t`/`long` size the facts fix to a constant that fits
/// `uint32`. Any other 64-bit size is a `uint64` size, its value as C's
/// `size_t` argument (a `long` converted). A `uint32` size is admitted here
/// and must still be bounded by `INT32_MAX`, and a 64-bit one by
/// `PTRDIFF_MAX` ([`allocation_size_validity_refusal`]).
fn allocation_size_value(
    value: ProgramValue,
    assumptions: &PureFactContext,
) -> Option<RequestedAllocationSize> {
    match value.numeric_value().clone() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Bool(term) => Some(RequestedAllocationSize::int32(term, true, false)),
        ProgramValue::Int8(term) => Some(RequestedAllocationSize::int32(term, false, false)),
        ProgramValue::Int16(term) | ProgramValue::UInt8(term) | ProgramValue::UInt16(term) => {
            Some(RequestedAllocationSize::int32(term, false, false))
        }
        ProgramValue::Int32(term) => Some(RequestedAllocationSize::int32(term, false, false)),
        ProgramValue::UInt32(term) => Some(RequestedAllocationSize::int32(term, true, true)),
        ProgramValue::Int64(term) => Some(match exact_signed_size_value(&term, assumptions) {
            Some(value) => match u32::try_from(value) {
                Ok(value) => {
                    RequestedAllocationSize::int32(MachineTerm::constant(value), false, false)
                }
                Err(_) => RequestedAllocationSize::uint64(
                    MachineTerm::uint64_constant(value as u64),
                    false,
                ),
            },
            None => RequestedAllocationSize::uint64(MachineTerm::uint64_from_int64(term), false),
        }),
        ProgramValue::UInt64(term) => Some(uint64_size_value(term, true, assumptions)),
        ProgramValue::Int128(_)
        | ProgramValue::UInt128(_)
        | ProgramValue::Void
        | ProgramValue::Pointer(_)
        | ProgramValue::Parameter(_)
        | ProgramValue::Float32(_)
        | ProgramValue::Float64(_) => None,
    }
}

/// A `uint64` size: a 32-bit constant size where the facts fix it to a
/// value that fits `uint32` (D2), else a `uint64` size.
fn uint64_size_value(
    term: MachineTerm,
    wraps: bool,
    assumptions: &PureFactContext,
) -> RequestedAllocationSize {
    match exact_unsigned_size_value(&term, assumptions) {
        Some(value) => match u32::try_from(value) {
            Ok(value) => RequestedAllocationSize::int32(MachineTerm::constant(value), false, false),
            Err(_) => RequestedAllocationSize::uint64(MachineTerm::uint64_constant(value), wraps),
        },
        None => RequestedAllocationSize::uint64(term, wraps),
    }
}

/// `calloc(n, w)`'s count `n` and constant element size `w`: the C front end
/// lowers the call to `n * w` with `w` the target's element or struct size.
fn calloc_operands(bytes_expression: &ProgramExpression) -> Option<(&ProgramExpression, u32)> {
    let ProgramExpression::Multiply(count, width) = bytes_expression else {
        return None;
    };
    let ProgramExpression::Value(width) = width.as_ref() else {
        return None;
    };
    let width = match width {
        ProgramValue::Int32(width) => width.as_const()?,
        ProgramValue::UInt64(width) => u32::try_from(width.uint64_as_const()?).ok()?,
        _ => return None,
    };
    (width > 0).then_some((count.as_ref(), width))
}

fn heap_element_count_expression(
    bytes_expression: &ProgramExpression,
    element_width: u32,
) -> Option<&ProgramExpression> {
    let is_element_width_expression = |expression: &ProgramExpression| {
        expression == &ProgramExpression::Value(int32(element_width))
            || expression
                == &crate::kernel::program_expression::uint64_literal(u64::from(element_width))
    };
    match bytes_expression {
        ProgramExpression::Multiply(left, right) if is_element_width_expression(right) => {
            Some(left.as_ref())
        }
        ProgramExpression::Multiply(left, right) if is_element_width_expression(left) => {
            Some(right.as_ref())
        }
        _ => None,
    }
}

fn exact_signed_size_value(term: &MachineTerm, assumptions: &PureFactContext) -> Option<i64> {
    if let Some(value) = term.int64_as_const() {
        return Some(value);
    }
    if let Some(value) = crate::kernel::assumptions::exact_signed_constant(term, assumptions) {
        return Some(value);
    }
    match term {
        MachineTerm::Binary {
            format: MachineIntegerType::Int64,
            op: MachineBinaryOp::Add,
            left,
            right,
        } => Some(
            exact_signed_size_value(left, assumptions)?
                .checked_add(exact_signed_size_value(right, assumptions)?)?,
        ),
        MachineTerm::Binary {
            format: MachineIntegerType::Int64,
            op: MachineBinaryOp::Subtract,
            left,
            right,
        } => Some(
            exact_signed_size_value(left, assumptions)?
                .checked_sub(exact_signed_size_value(right, assumptions)?)?,
        ),
        MachineTerm::Binary {
            format: MachineIntegerType::Int64,
            op: MachineBinaryOp::Multiply,
            left,
            right,
        } => Some(
            exact_signed_size_value(left, assumptions)?
                .checked_mul(exact_signed_size_value(right, assumptions)?)?,
        ),
        _ => None,
    }
}

fn exact_unsigned_size_value(term: &MachineTerm, assumptions: &PureFactContext) -> Option<u64> {
    if let Some(value) = term.uint64_as_const() {
        return Some(value);
    }
    if let Some(value) = crate::kernel::assumptions::exact_signed_constant(term, assumptions) {
        return u64::try_from(value).ok();
    }
    match term {
        MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Add,
            left,
            right,
        } => Some(
            exact_unsigned_size_value(left, assumptions)?
                .wrapping_add(exact_unsigned_size_value(right, assumptions)?),
        ),
        MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Subtract,
            left,
            right,
        } => Some(
            exact_unsigned_size_value(left, assumptions)?
                .wrapping_sub(exact_unsigned_size_value(right, assumptions)?),
        ),
        MachineTerm::Binary {
            format: MachineIntegerType::UInt64,
            op: MachineBinaryOp::Multiply,
            left,
            right,
        } => Some(
            exact_unsigned_size_value(left, assumptions)?
                .wrapping_mul(exact_unsigned_size_value(right, assumptions)?),
        ),
        _ => None,
    }
}

fn allocation_size_is_positive(
    size: &RequestedAllocationSize,
    assumptions: &PureFactContext,
) -> bool {
    let condition = if size.unsigned {
        ConditionTerm::unsigned_greater_than(size.term.clone(), MachineTerm::constant(0))
    } else {
        ConditionTerm::signed_greater_than(size.term.clone(), MachineTerm::constant(0))
    };
    assumptions.decide(&condition) == Some(true)
}

/// Whether `size` elements of `element_width` bytes fit the checked signed
/// 32-bit allocation size. The block's token and range store the size as an
/// `int32`, so an unsigned size is bounded by `INT32_MAX` too: a `uint32`
/// at or above 2^31 would read there as a negative count.
fn allocation_size_fits_element_width(
    size: &RequestedAllocationSize,
    element_width: u32,
    assumptions: &PureFactContext,
) -> bool {
    let maximum = i32::MAX as u32 / element_width;
    let condition = if size.unsigned {
        ConditionTerm::unsigned_less_equal(size.term.clone(), MachineTerm::constant(maximum))
    } else {
        ConditionTerm::signed_less_equal(size.term.clone(), MachineTerm::constant(maximum))
    };
    assumptions.decide(&condition) == Some(true)
}

/// Whether the facts decide that a 64-bit size is exact: an element count
/// `1 <= n <= PTRDIFF_MAX / element_width` (so `n * element_width` does not
/// wrap), or a byte count `1 <= bytes <= PTRDIFF_MAX` whose top-level
/// product, if it is one, is by a constant `k` with the other factor at most
/// `PTRDIFF_MAX / k` (`design/heap-allocation-sizes.md`, D3).
///
/// The product condition is what lets a reader take `n * k` bytes as `n`
/// elements ([`crate::kernel::reasoning::uint64_element_count_from_bytes`]):
/// a `size_t` product may wrap without undefined behavior, and its wrapped
/// value bounded by `PTRDIFF_MAX` says nothing about `n`. A product of two
/// symbolic factors is not admitted.
fn uint64_allocation_size_is_exact(
    size: &RequestedAllocationSize,
    element_width: u32,
    element_count: bool,
    assumptions: &PureFactContext,
) -> bool {
    let holds = |condition: ConditionTerm| assumptions.decide(&condition) == Some(true);
    let at_most = |term: &MachineTerm, width: u64| {
        holds(ConditionTerm::uint64_less_equal(
            term.clone(),
            MachineTerm::uint64_constant(i64::MAX as u64 / width),
        ))
    };
    let positive = |term: &MachineTerm| {
        holds(ConditionTerm::uint64_greater_than(
            term.clone(),
            MachineTerm::uint64_constant(0),
        ))
    };
    if element_count {
        return positive(&size.term) && at_most(&size.term, u64::from(element_width.max(1)));
    }
    uint64_allocation_size_bytes_are_exact(&size.term, assumptions)
}

/// Whether `bytes`, a `uint64` byte count, is a 64-bit allocation size: positive
/// and at most `PTRDIFF_MAX`, and, when it is a top-level product with a
/// constant factor `k`, with its other factor decided at most
/// `PTRDIFF_MAX / k`, so the product is exact and reads back as its elements
/// ([`crate::kernel::reasoning::uint64_element_count_from_bytes`]). A product
/// of two symbolic factors is not one. `malloc` and a contract's
/// `allocation(p, bytes)` admit a 64-bit size only under this decision.
pub(in crate::kernel) fn uint64_allocation_size_bytes_are_exact(
    bytes: &MachineTerm,
    assumptions: &PureFactContext,
) -> bool {
    let holds = |condition: ConditionTerm| assumptions.decide(&condition) == Some(true);
    let at_most = |term: &MachineTerm, width: u64| {
        holds(ConditionTerm::uint64_less_equal(
            term.clone(),
            MachineTerm::uint64_constant(i64::MAX as u64 / width),
        ))
    };
    let positive = |term: &MachineTerm| {
        holds(ConditionTerm::uint64_greater_than(
            term.clone(),
            MachineTerm::uint64_constant(0),
        ))
    };
    match bytes {
        // `1 <= n <= PTRDIFF_MAX / k` makes `n * k` exact, so it is also
        // positive and at most `PTRDIFF_MAX`.
        binary_term!(UInt64, Multiply, left, right) => {
            match (left.uint64_as_const(), right.uint64_as_const()) {
                (_, Some(width)) if width > 0 => positive(left) && at_most(left, width),
                (Some(width), _) if width > 0 => positive(right) && at_most(right, width),
                _ => false,
            }
        }
        bytes => positive(bytes) && at_most(bytes, 1),
    }
}

/// Why an admitted allocation size cannot be a heap block's size, if it cannot. An
/// element count must be positive and fit with `element_width`; a raw byte
/// count must be positive and, for a `uint32`, at most `INT32_MAX`; a 64-bit
/// size must be exact and at most `PTRDIFF_MAX` bytes
/// ([`uint64_allocation_size_is_exact`]).
fn allocation_size_validity_refusal(
    size: &RequestedAllocationSize,
    element_width: u32,
    element_count: bool,
    assumptions: &PureFactContext,
) -> Option<RuntimeError> {
    if size.kind == AllocationSizeKind::UInt64 {
        return (!uint64_allocation_size_is_exact(size, element_width, element_count, assumptions))
            .then_some(RuntimeError::HeapAllocationSize);
    }
    if !allocation_size_is_positive(size, assumptions) {
        return Some(RuntimeError::TypeMismatch);
    }
    let fits = if element_count || size.needs_size_bound {
        allocation_size_fits_element_width(size, element_width, assumptions)
    } else {
        true
    };
    if fits {
        None
    } else if size.needs_size_bound {
        Some(RuntimeError::HeapAllocationSizeAboveInt32)
    } else {
        Some(RuntimeError::TypeMismatch)
    }
}

fn execute_program_realloc_result_paths(
    state: &ExecutionState,
    result_type: Option<ProgramType>,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let [old_expression, size_expression] = arguments else {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::RuntimeError(RuntimeError::WrongArity {
                expected: 2,
                actual: arguments.len(),
            }),
            Vec::new().into(),
            Vec::new(),
        )]);
    };
    let Some(
        target_type @ (ProgramType::Int32Pointer
        | ProgramType::UInt8Pointer
        | ProgramType::Int16Pointer
        | ProgramType::UInt16Pointer
        | ProgramType::UInt32Pointer
        | ProgramType::Int128Pointer
        | ProgramType::Int64Pointer
        | ProgramType::UInt128Pointer
        | ProgramType::UInt64Pointer
        | ProgramType::Int32PointerPointer
        | ProgramType::UInt8PointerPointer
        | ProgramType::Int16PointerPointer
        | ProgramType::UInt16PointerPointer
        | ProgramType::UInt32PointerPointer
        | ProgramType::Int128PointerPointer
        | ProgramType::Int64PointerPointer
        | ProgramType::UInt128PointerPointer
        | ProgramType::UInt64PointerPointer),
    ) = result_type
    else {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
            Vec::new().into(),
            Vec::new(),
        )]);
    };
    let element_width = target_type
        .pointee_type()
        .expect("realloc target has a pointee type")
        .byte_width();
    let element_count_expression = heap_element_count_expression(size_expression, element_width);

    let mut paths = Vec::new();
    for old_path in evaluate_program_expression_paths(state, old_expression, assumptions, budget)? {
        let ExpressionPath {
            outcome,
            facts,
            obligations,
        } = old_path;
        let ExpressionOutcome::Value(old_value) = outcome else {
            let outcome = match outcome {
                ExpressionOutcome::UndefinedBehavior(error) => {
                    StatementOutcome::UndefinedBehavior(error)
                }
                ExpressionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
                ExpressionOutcome::Value(_) => unreachable!(),
            };
            paths.push(StatementExecutionPath::new(outcome, facts, obligations));
            continue;
        };

        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        let old_argument = match old_value {
            ProgramValue::Pointer(pointer) => pointer,
            ProgramValue::Int32(bits) if bits.as_const() == Some(0) => {
                Pointer::new(Address::null(), target_type)
            }
            _ => {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                    facts,
                    obligations,
                ));
                continue;
            }
        };

        let old_pointer = old_argument.address().clone();
        // C specifies realloc(NULL, size) as an allocation. Reuse the
        // existing pending-allocation machinery so a later null check can
        // resolve this branch just like malloc/calloc.
        if old_pointer == Address::null() {
            for allocation_path in execute_program_heap_allocate_to_paths(
                state,
                AllocationDestination::Value(target_type),
                size_expression,
                false,
                None,
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
                paths.push(
                    StatementExecutionPath::new(
                        allocation_path.outcome,
                        merged_facts,
                        merged_obligations,
                    )
                    .with_call_result(allocation_path.call_result),
                );
            }
            continue;
        }

        let Some(old_bytes) = state.memory.live_heap_block_size(&old_pointer).cloned() else {
            let error = if state
                .memory
                .is_deallocated_heap_address(&old_pointer, assumptions)
            {
                InvalidFree::DoubleFree
            } else if state.memory.is_live_heap_address(&old_pointer, assumptions) {
                InvalidFree::InteriorPointer
            } else {
                InvalidFree::NonHeapPointer
            };
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(RuntimeError::InvalidFree(error)),
                facts,
                obligations,
            ));
            continue;
        };
        let (old_complete_range, old_range_width) =
            heap_block_range(old_pointer.clone(), &old_bytes, element_width);
        let old_allocation_range = old_bytes.byte_range(old_pointer.clone());
        for new_size_path in evaluate_program_expression_paths(
            state,
            element_count_expression.unwrap_or(size_expression),
            &effective_assumptions,
            budget,
        )? {
            let ExpressionPath {
                outcome: new_size_outcome,
                facts: size_facts,
                obligations: size_obligations,
            } = new_size_path;
            let ExpressionOutcome::Value(new_size_value) = new_size_outcome else {
                let outcome = match new_size_outcome {
                    ExpressionOutcome::UndefinedBehavior(error) => {
                        StatementOutcome::UndefinedBehavior(error)
                    }
                    ExpressionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
                    ExpressionOutcome::Value(_) => {
                        StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
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
                paths.push(StatementExecutionPath::new(
                    outcome,
                    merged_facts,
                    merged_obligations,
                ));
                continue;
            };
            let size_assumptions = assumptions_with_path_context(
                &effective_assumptions,
                &size_facts,
                &size_obligations,
            );
            let refusal = allocation_size_refusal(&new_size_value);
            let Some(size) = allocation_size_value(new_size_value, &size_assumptions) else {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(refusal),
                    size_facts,
                    size_obligations,
                ));
                continue;
            };
            let new_bytes = if element_count_expression.is_some() {
                if let Some(refusal) =
                    allocation_size_validity_refusal(&size, element_width, true, &size_assumptions)
                {
                    paths.push(StatementExecutionPath::new(
                        StatementOutcome::RuntimeError(refusal),
                        size_facts,
                        size_obligations,
                    ));
                    continue;
                }
                size.scaled(element_width)
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
            if let Some(refusal) =
                allocation_size_validity_refusal(&new_bytes, 1, false, &effective_assumptions)
            {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(refusal),
                    all_facts,
                    all_obligations,
                ));
                continue;
            }
            // The bytes that stay zero: the whole old block of a calloc, or
            // the constant prefix an earlier realloc kept, in its format.
            let zeroed_source = if state.memory.heap.zeroed_allocations.contains(&old_pointer) {
                Some(old_bytes.clone())
            } else {
                state
                    .memory
                    .heap
                    .zeroed_prefix_allocations
                    .get(&old_pointer)
                    .map(|prefix| AllocationSize::int32(prefix.clone()))
            };
            let zeroed_prefix = match zeroed_source {
                None => None,
                Some(old_prefix) => {
                    let Some(prefix) =
                        realloc_zeroed_prefix(&old_prefix, &new_bytes, &effective_assumptions)
                    else {
                        paths.push(StatementExecutionPath::new(
                            StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                            all_facts,
                            all_obligations,
                        ));
                        continue;
                    };
                    Some(MachineTerm::constant(prefix))
                }
            };

            let allocation = ResourceFact::own_heap_allocation(old_pointer.clone(), &old_bytes);
            let Some(resources) = state
                .resources
                .clone()
                .without_fact_incrementally(&allocation, &effective_assumptions)
            else {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::MissingResource {
                        resource: Box::new(allocation),
                    }),
                    all_facts,
                    all_obligations,
                ));
                continue;
            };
            let complete_access = ResourceFact::own_memory(old_complete_range.clone());
            let Some(resources) =
                resources.without_fact_incrementally(&complete_access, &effective_assumptions)
            else {
                // A live mutex consumed ownership of its storage; name it
                // rather than the bytes it took.
                let error = super::super::mutexes::storage_retirement_refusal(
                    state,
                    &old_allocation_range,
                    &effective_assumptions,
                )
                .unwrap_or(RuntimeError::MissingResource {
                    resource: Box::new(complete_access),
                });
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(error),
                    all_facts,
                    all_obligations,
                ));
                continue;
            };
            if let Some(error) = super::super::mutexes::storage_retirement_refusal(
                state,
                &old_allocation_range,
                &effective_assumptions,
            ) {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(error),
                    all_facts,
                    all_obligations,
                ));
                continue;
            }
            // Reallocation retires the old block under the same conservative
            // reference check as free. Select that block's dependents before
            // projecting resource facts; unrelated holdings cannot become stale.
            {
                let mut candidates =
                    resources.facts_that_may_refer_to_memory_block(&old_pointer.base);
                if let Some(first) = candidates.next() {
                    let resource_assumptions = state
                        .resources()
                        .observable_facts_assuming_valid(&effective_assumptions)
                        .into_iter()
                        .fold(effective_assumptions.clone(), |assumptions, fact| {
                            assumptions.assume_proposition(fact)
                        });
                    if let Some(stale) = std::iter::once(first).chain(candidates).find(|resource| {
                        !resource.is_proven_separate_from_allocation_with_element_width(
                            &old_pointer,
                            &old_bytes,
                            old_range_width,
                            &resource_assumptions,
                        )
                    }) {
                        paths.push(StatementExecutionPath::new(
                            StatementOutcome::RuntimeError(RuntimeError::StaleResourceAfterFree {
                                resource: Box::new(stale.clone()),
                            }),
                            all_facts,
                            all_obligations,
                        ));
                        continue;
                    }
                }
            }

            let old_cells = state
                .memory
                .clone()
                .cells
                .iter()
                .filter(|(pointer, _)| pointer.base == old_pointer.base)
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
                let fits_condition = new_bytes.at_least(end);
                let truncated_condition = new_bytes.less_than(end);
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
            // The old block's initialized bytes the new allocation holds,
            // whether or not a cell above carries their value: each run cut
            // at the new size where that is a constant, and kept whole where
            // the facts place its end inside the new size. A run the facts
            // cannot place is left out, which can only refuse a later read.
            let mut initialized_prefix = Vec::new();
            for (start, length) in state.memory.initialized_runs_in_block(&old_pointer.base) {
                let end = start + i64::from(length);
                let Ok(end_constant) = u32::try_from(end) else {
                    continue;
                };
                if effective_assumptions.decide(&new_bytes.at_least(end_constant)) == Some(true) {
                    initialized_prefix.push((start, length));
                } else if let Some(new_size) = new_bytes
                    .constant_bytes()
                    .and_then(|new_size| i64::try_from(new_size).ok())
                    && new_size > start
                    && start >= 0
                {
                    let kept =
                        u32::try_from(new_size - start).map_or(length, |kept| kept.min(length));
                    initialized_prefix.push((start, kept));
                }
            }
            if copy_is_unsupported {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                    all_facts,
                    all_obligations,
                ));
                continue;
            }

            let pending_pointer = loop {
                let identity = budget.allocate_kernel_variable()?;
                if !state.memory.heap_identity_in_use(identity.0) {
                    break Address::symbolic(identity);
                }
            };
            // Save the call-entry loan footprint. Only success retires the
            // old allocation, and intervening proof steps can change the ledger.
            let retirement_separation = state.loan_ledger().and_then(|ledger| {
                let byte_pointer = super::expression::cast_pointer_value(
                    old_argument.clone(),
                    ProgramType::UInt8Pointer,
                );
                let range = old_allocation_range
                    .clone()
                    .with_pointer_carrier(&byte_pointer);
                ledger
                    .memory_access_requirement(&range)
                    .map(std::sync::Arc::new)
            });
            let pending_memory = state
                .memory
                .clone()
                .with_pending_heap_allocation(
                    pending_pointer.clone(),
                    new_bytes.clone().into_allocation_size(),
                    false,
                )
                .with_pending_heap_reallocation(
                    pending_pointer.clone(),
                    PendingReallocation {
                        old_pointer: old_pointer.clone(),
                        old_bytes: old_bytes.clone(),
                        zeroed_prefix,
                        copied_cells: copied_cells
                            .into_iter()
                            .map(|(offset, value)| {
                                (AddressOffset::Constant(i64::from(offset)), value)
                            })
                            .collect(),
                        initialized_prefix,
                        retirement_separation,
                    },
                );
            let pending_state = state.clone().with_memory(pending_memory);
            let assigned = AllocationDestination::Value(target_type).finish(
                &pending_state,
                ProgramValue::typed_pointer(pending_pointer, target_type),
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
                paths.push(
                    StatementExecutionPath::new(
                        assigned_path.outcome,
                        merged_facts,
                        merged_obligations,
                    )
                    .with_call_result(assigned_path.call_result),
                );
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn execute_program_heap_free_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let mut paths = Vec::new();
    for path in evaluate_program_expression_paths(state, expression, assumptions, budget)? {
        let ExpressionPath {
            outcome,
            mut facts,
            mut obligations,
        } = path;
        let outcome = match outcome {
            ExpressionOutcome::Value(ProgramValue::Int32(bits)) if bits.as_const() == Some(0) => {
                ExpressionOutcome::Value(ProgramValue::typed_pointer(
                    Address::null(),
                    ProgramType::Int32Pointer,
                ))
            }
            outcome => outcome,
        };
        let ExpressionOutcome::Value(ProgramValue::Pointer(pointer)) = outcome else {
            let outcome = match outcome {
                ExpressionOutcome::UndefinedBehavior(error) => {
                    StatementOutcome::UndefinedBehavior(error)
                }
                ExpressionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
                ExpressionOutcome::Value(_) => {
                    StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
                }
            };
            paths.push(StatementExecutionPath::new(outcome, facts, obligations));
            continue;
        };

        let effective_assumptions =
            assumptions_with_path_context(assumptions, &facts, &obligations);
        if pointer.is_null()
            || effective_assumptions.decide(&pointer_is_null_condition(pointer.address().clone()))
                == Some(true)
        {
            paths.push(StatementExecutionPath::new(
                StatementOutcome::Normal(Box::new(state.clone())),
                facts,
                obligations,
            ));
            continue;
        }

        // Retain the argument's spelling for the proof at this program point.
        let argument = pointer.clone();

        // Resolve the allocation's owned base through the same argument
        // equality used to consume its token. A proven alias names that
        // allocation; it must not create a second lifetime under the alias.
        // The query's byte count is a placeholder: candidates match by base.
        let allocation_query =
            ResourceFact::own_designated_allocation(pointer.clone(), &AllocationSize::int32(0));
        let declared_allocation = state
            .resources
            .direct_match_candidates_for(&allocation_query, &effective_assumptions)
            .into_iter()
            .filter_map(ResourceFact::allocation_size)
            .find(|(base, _)| {
                crate::kernel::resource_arguments_proven_equal(
                    &ProgramValue::Pointer((*base).clone().with_type(ProgramType::Int32Pointer))
                        .into(),
                    &ProgramValue::Pointer(pointer.clone().with_type(ProgramType::Int32Pointer))
                        .into(),
                    &effective_assumptions,
                )
            });
        let (mut pointer, declared_allocation) = match declared_allocation {
            Some((base, bytes)) => (base.clone().with_type(pointer.program_type()), Some(bytes)),
            None => (pointer, None),
        };
        // The owned token can itself be spelled by a returned alias. Resolve
        // that address to its indexed storage coordinate before asking whether
        // it is the exact live allocation base. Keep provenance and bounds;
        // this address spelling grants no permission and preserves offsets.
        pointer.replace_pointer(
            effective_assumptions
                .equality_graph
                .storage_address(pointer.address()),
        );
        if state
            .memory
            .heap
            .pending_reallocations
            .values()
            .any(|pending| pending.old_pointer.base == pointer.base)
        {
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(RuntimeError::UnresolvedAllocationOutcome),
                facts,
                obligations,
            ));
            continue;
        }

        let element_width = pointer
            .program_type()
            .pointee_type()
            .map(ProgramType::byte_width)
            .unwrap_or(ProgramType::Int32.byte_width());
        let before_free = state.memory.clone();
        let mut working_memory = state.memory.clone();
        let bytes = if let Some(bytes) = working_memory.live_heap_block_size(pointer.address()) {
            bytes.clone()
        } else if working_memory
            .is_deallocated_heap_address(pointer.address(), &effective_assumptions)
        {
            let error = InvalidFree::DoubleFree;
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(RuntimeError::InvalidFree(error)),
                facts,
                obligations,
            ));
            continue;
        } else if working_memory.is_live_heap_address(pointer.address(), &effective_assumptions) {
            let error = InvalidFree::InteriorPointer;
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(RuntimeError::InvalidFree(error)),
                facts,
                obligations,
            ));
            continue;
        } else if let Some(bytes) = declared_allocation {
            let Some(memory) =
                working_memory.with_heap_allocation_claim(pointer.address().clone(), bytes.clone())
            else {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::InvalidFree(
                        InvalidFree::NonHeapPointer,
                    )),
                    facts,
                    obligations,
                ));
                continue;
            };
            working_memory = memory;
            bytes
        } else {
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(RuntimeError::InvalidFree(
                    InvalidFree::NonHeapPointer,
                )),
                facts,
                obligations,
            ));
            continue;
        };
        if let Some(error) = state.population_storage_retirement_refusal(&pointer.base) {
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(error),
                facts,
                obligations,
            ));
            continue;
        }
        let full_allocation_range = bytes.byte_range(pointer.address().clone());
        let allocation = ResourceFact::own_designated_allocation(pointer.clone(), &bytes);
        let Some(resources) = state
            .resources
            .clone()
            .without_fact_delaying_normalization(&allocation, &effective_assumptions)
        else {
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(RuntimeError::MissingResource {
                    resource: Box::new(allocation),
                }),
                facts,
                obligations,
            ));
            continue;
        };
        let (complete_range, range_width) =
            heap_block_range(pointer.address().clone(), &bytes, element_width);
        let complete_access = ResourceFact::own_memory(complete_range);
        // Single-supplier consumption keeps unrelated holdings untouched.
        // Split and supported owners still need their composition checked.
        let consumed = resources
            .clone()
            .without_fact_delaying_normalization(&complete_access, &effective_assumptions)
            .or_else(|| {
                resources
                    .clone()
                    .without_fact_incrementally(&complete_access, &effective_assumptions)
            })
            .or_else(|| {
                resources
                    .normalized(&effective_assumptions)
                    .without_fact_delaying_normalization(&complete_access, &effective_assumptions)
            });
        let Some(resources) = consumed else {
            // A live mutex consumed ownership of its storage; name it rather
            // than the bytes it took.
            let error = super::super::mutexes::storage_retirement_refusal(
                state,
                &full_allocation_range,
                &effective_assumptions,
            )
            .unwrap_or(RuntimeError::MissingResource {
                resource: Box::new(complete_access),
            });
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(error),
                facts,
                obligations,
            ));
            continue;
        };
        if let Some(error) = super::super::mutexes::storage_retirement_refusal(
            state,
            &full_allocation_range,
            &effective_assumptions,
        ) {
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(error),
                facts,
                obligations,
            ));
            continue;
        }
        if let Some(ledger) = state.loan_ledger() {
            // Check the full allocation at the argument's address, which was
            // resolved to its live base above. Keep the Surface byte carrier
            // so the separation can be stated at the free's entry.
            let byte_pointer =
                super::expression::cast_pointer_value(argument, ProgramType::UInt8Pointer);
            let range = bytes
                .byte_range(byte_pointer.address().clone())
                .with_pointer_carrier(&byte_pointer);
            if let Some(requirement) = ledger.memory_access_requirement(&range) {
                obligations.push(ProofObligation::verification_condition(requirement));
            }
        }
        // A free can invalidate only resources that refer to this block.
        // Most frees leave no such facts after consuming the allocation and
        // its full ownership. Avoid projecting the whole ambient composition
        // in that common case; the indexed candidates preserve the same
        // conservative separation checks when a dependent resource remains.
        {
            let mut candidates = resources.facts_that_may_refer_to_memory_block(&pointer.base);
            if let Some(first) = candidates.next() {
                let resource_assumptions = state
                    .resources()
                    .observable_facts_assuming_valid(&effective_assumptions)
                    .into_iter()
                    .fold(effective_assumptions.clone(), |assumptions, fact| {
                        assumptions.assume_proposition(fact)
                    });
                if let Some(stale) = std::iter::once(first).chain(candidates).find(|resource| {
                    !resource.is_proven_separate_from_allocation_with_element_width(
                        &pointer,
                        &bytes,
                        range_width,
                        &resource_assumptions,
                    )
                }) {
                    paths.push(StatementExecutionPath::new(
                        StatementOutcome::RuntimeError(RuntimeError::StaleResourceAfterFree {
                            resource: Box::new(stale.clone()),
                        }),
                        facts,
                        obligations,
                    ));
                    continue;
                }
            }
        }
        let (memory, pointer_frames) = working_memory
            .free_heap_block_and_owned_pointer_frames(
                pointer.address(),
                &effective_assumptions,
                &resources,
            )
            .expect("validated live heap base should free");
        for (address, value_type) in pointer_frames {
            let ProgramValue::Pointer(before) =
                before_free.symbolic_pointer_version_load(&address, value_type)
            else {
                unreachable!("a pointer version read has pointer type");
            };
            let ProgramValue::Pointer(after) =
                memory.symbolic_pointer_version_load(&address, value_type)
            else {
                unreachable!("a pointer version read has pointer type");
            };
            if before != after {
                facts.push(ExecutionPureFact::certified(Proposition::condition_is(
                    ConditionTerm::pointer_equal(before, after),
                    true,
                )));
            }
        }
        facts.push(ExecutionPureFact::internal(
            Proposition::HeapAllocationFreed {
                before: before_free,
                after: memory.clone(),
                allocation_base: pointer.address().clone(),
                bytes: bytes.clone(),
            },
        ));
        let mut next = state
            .clone()
            .with_memory(memory)
            .with_resource_context(resources);
        if let Err(error) = next.retire_population_storage(&pointer.base) {
            paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(error),
                facts,
                obligations,
            ));
            continue;
        }
        paths.push(StatementExecutionPath::new(
            StatementOutcome::Normal(Box::new(next)),
            facts,
            obligations,
        ));
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// Resolve one path, letting its caller record or discharge any retirement
/// prerequisites before the corresponding old allocation is retired.
pub(crate) fn resolve_pending_heap_allocations_with<E>(
    state: &ExecutionState,
    assumptions: &PureFactContext,
    mut require: impl FnMut(ProofObligation) -> Result<(), E>,
) -> Result<ExecutionState, E> {
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
            if !is_null && let Some(separation) = &pending_reallocation.retirement_separation {
                require(ProofObligation::verification_condition(
                    separation.as_ref().clone(),
                ))?;
            }
            let (memory, bytes, resolved_base, _) = state
                .memory
                .clone()
                .resolve_pending_heap_reallocation(&base, !is_null, assumptions)
                .expect("collected pending reallocation should still exist");
            state = state.with_memory(memory);
            let rebound = state
                .locals
                .bindings
                .iter()
                .filter_map(|(name, binding)| {
                    let mut binding = binding.clone();
                    let LocalBinding::Object { value, .. } = &mut binding else {
                        return None;
                    };
                    if value.pointer()?.address() != &base {
                        return None;
                    }
                    let native = value.native();
                    let ProgramValue::Pointer(pointer) = native.as_ref() else {
                        unreachable!()
                    };
                    *value = ProgramValue::Pointer(rebase_resolved_allocation(
                        pointer,
                        &base,
                        &resolved_base,
                    ))
                    .into();
                    Some((name.clone(), binding))
                })
                .collect::<Vec<_>>();
            for (name, binding) in rebound {
                state.locals.insert_binding(name, binding);
            }
            if !is_null {
                let old_memory = ResourceFact::own_memory(
                    heap_block_range(
                        pending_reallocation.old_pointer.clone(),
                        &pending_reallocation.old_bytes,
                        element_width,
                    )
                    .0,
                );
                let old_allocation = ResourceFact::own_heap_allocation(
                    pending_reallocation.old_pointer,
                    &pending_reallocation.old_bytes,
                );
                state.resources = state
                    .resources
                    .clone()
                    .without_fact(&old_allocation, assumptions)
                    .expect("validated realloc allocation resource should remain available")
                    .without_fact(&old_memory, assumptions)
                    .expect("validated realloc memory resource should remain available")
                    .unchecked_with_fact(ResourceFact::own_heap_allocation(
                        resolved_base.clone(),
                        &bytes,
                    ))
                    .unchecked_with_fact(ResourceFact::own_memory(
                        heap_block_range(resolved_base, &bytes, element_width).0,
                    ));
            }
            continue;
        }
        let (memory, bytes, resolved_base) = state
            .memory
            .clone()
            .resolve_pending_heap_allocation(&base, !is_null)
            .expect("collected pending allocation should still exist");
        state = state.with_memory(memory);
        state.resolve_pending_population_storage_creation(
            &base.base,
            (!is_null).then(|| resolved_base.base.clone()),
        );
        let rebound = state
            .locals
            .bindings
            .iter()
            .filter_map(|(name, binding)| {
                let mut binding = binding.clone();
                let LocalBinding::Object { value, .. } = &mut binding else {
                    return None;
                };
                if value.pointer()?.address() != &base {
                    return None;
                }
                let native = value.native();
                let ProgramValue::Pointer(pointer) = native.as_ref() else {
                    unreachable!()
                };
                *value = ProgramValue::Pointer(rebase_resolved_allocation(
                    pointer,
                    &base,
                    &resolved_base,
                ))
                .into();
                Some((name.clone(), binding))
            })
            .collect::<Vec<_>>();
        for (name, binding) in rebound {
            state.locals.insert_binding(name, binding);
        }
        if !is_null {
            state.resources = state
                .resources
                .unchecked_with_fact(ResourceFact::own_heap_allocation(
                    resolved_base.clone(),
                    &bytes,
                ))
                .unchecked_with_fact(ResourceFact::own_memory(
                    heap_block_range(resolved_base, &bytes, element_width).0,
                ));
        }
    }
    Ok(state)
}

fn resolve_pending_heap_allocations_recording(
    state: &ExecutionState,
    assumptions: &PureFactContext,
    obligations: &mut Vec<ProofObligation>,
) -> ExecutionState {
    match resolve_pending_heap_allocations_with(state, assumptions, |obligation| {
        obligations.push(obligation);
        Ok::<_, std::convert::Infallible>(())
    }) {
        Ok(state) => state,
        Err(never) => match never {},
    }
}

#[cfg(test)]
pub(crate) fn resolve_pending_heap_allocations(
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> ExecutionState {
    resolve_pending_heap_allocations_with(state, assumptions, |obligation| {
        assumptions
            .states_required_goal(obligation.proposition())
            .then_some(())
            .ok_or(obligation)
    })
    .expect("test requires checked allocation retirement")
}

fn has_live_thread_completion(state: &ExecutionState) -> bool {
    state.pending_thread_create.is_some()
        || state
            .thread_ledger
            .as_ref()
            .is_some_and(|ledger| ledger.has_live_rights())
}

fn live_thread_return_refusal() -> StatementOutcome {
    StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
        "a function cannot return with a live pthread completion right".to_string(),
    ))
}

fn has_live_mutex(state: &ExecutionState) -> bool {
    state
        .opaque_mutex_acquisitions
        .as_ref()
        .is_some_and(|held| held.has_local_hold(state.loan_participant))
        && !super::super::mutexes::helper_contracts::permits_return(state)
        || (!state.preserves_mutex_protocols
            && state
                .mutex_ledger
                .as_ref()
                .is_some_and(super::super::mutexes::MutexLedger::has_return_obligation))
}

fn live_mutex_return_refusal() -> StatementOutcome {
    StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
        "a function cannot return with a held mutex or an unpublished guarded resource; unlock or destroy it first".to_string(),
    ))
}

/// The same authority obligations apply to explicit returns and void fallthrough.
pub(in crate::kernel) fn return_authority_refusal(
    state: &ExecutionState,
) -> Option<StatementOutcome> {
    if has_live_thread_completion(state) {
        Some(live_thread_return_refusal())
    } else if has_live_mutex(state) {
        Some(live_mutex_return_refusal())
    } else {
        None
    }
}

fn execute_program_return_expression_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let mut paths = Vec::new();
    for expression_path in evaluate_expression_value_paths(state, expression, assumptions, budget)?
    {
        let ExecutionValuePath {
            outcome,
            facts,
            obligations,
        } = expression_path;
        match outcome {
            ExpressionOutcome::Value(value)
                if value.pointer().is_some_and(|pointer| {
                    state.memory.heap.pending_allocations.contains_key(pointer)
                }) =>
            {
                let pointer = value.pointer().expect("pending pointer result").clone();
                for mut truthiness_path in pending_allocation_outcome_paths(
                    pointer.address().clone(),
                    facts,
                    obligations,
                    assumptions,
                ) {
                    let path_assumptions = assumptions_with_path_context(
                        assumptions,
                        &truthiness_path.facts,
                        &truthiness_path.obligations,
                    );
                    let resolved_state = resolve_pending_heap_allocations_recording(
                        state,
                        &path_assumptions,
                        &mut truthiness_path.obligations,
                    );
                    let resolved_pointer = if truthiness_path.is_true {
                        let AddressBase::Symbolic(variable) = pointer.base else {
                            unreachable!("pending malloc results have symbolic heap identities");
                        };
                        Address {
                            base: AddressBase::Heap(variable.0),
                            offset: AddressOffset::Constant(0),
                        }
                    } else {
                        Address::null()
                    };
                    let outcome = if let Some(refusal) = return_authority_refusal(&resolved_state) {
                        refusal
                    } else if resolved_state.memory.has_pending_heap_allocation() {
                        StatementOutcome::RuntimeError(RuntimeError::UnresolvedAllocationOutcome)
                    } else {
                        StatementOutcome::Return {
                            value: ProgramValue::typed_pointer(
                                resolved_pointer,
                                pointer.program_type(),
                            )
                            .with_pointer_object_type_evidence(
                                pointer.object_type_evidence().cloned(),
                            )
                            .into(),
                            state: Box::new(resolved_state),
                        }
                    };
                    paths.push(StatementExecutionPath::new(
                        outcome,
                        truthiness_path.facts,
                        truthiness_path.obligations,
                    ));
                }
            }
            ExpressionOutcome::Value(value) => {
                let outcome = if let Some(refusal) = return_authority_refusal(state) {
                    refusal
                } else if state.memory.has_pending_heap_allocation() {
                    StatementOutcome::RuntimeError(RuntimeError::UnresolvedAllocationOutcome)
                } else {
                    StatementOutcome::Return {
                        value: value.into(),
                        state: Box::new(state.clone()),
                    }
                };
                paths.push(StatementExecutionPath::new(outcome, facts, obligations));
            }
            ExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts,
                    obligations,
                ));
            }
            ExpressionOutcome::RuntimeError(error) => paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(error),
                facts,
                obligations,
            )),
        }
    }
    Ok(paths)
}

fn pending_allocation_outcome_paths(
    pointer: Address,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Vec<TruthinessPath> {
    let is_null = pointer_is_null_condition(pointer);
    match decide_with_facts(assumptions, &facts, &is_null) {
        Some(true) => vec![TruthinessPath {
            is_true: false,
            facts,
            obligations,
        }],
        Some(false) => vec![TruthinessPath {
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
                TruthinessPath {
                    is_true: true,
                    facts: success_facts,
                    obligations: obligations.clone(),
                },
                TruthinessPath {
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
/// C lowers a source block to a `Seq` tree, and the kernel has no statement
/// that stands for the block itself, so a scope's own declarations are the
/// ones reachable from its root through that tree. The walk stops at a nested
/// scope — an `if` arm, a loop body, a `switch` body — because control leaving
/// that scope retires what it declared, and stops at every other statement
/// because no other statement declares.
///
/// Bounded by the scope's own spine: the `Seq` nodes above its declarations,
/// which a source block has one of per statement it holds.
fn collect_scope_declared_names(statement: &ProgramStatement, names: &mut Vec<BindingName>) {
    match statement {
        ProgramStatement::Declare { name, .. } | ProgramStatement::DeclareAggregate { name, .. } => {
            names.push(name.binding().clone());
        }
        ProgramStatement::Seq(statements) => {
            for statement in statements.iter() {
                collect_scope_declared_names(statement, names);
            }
        }
        // Nested scopes retire their own declarations.
        ProgramStatement::If { .. }
        | ProgramStatement::Loop { .. }
        | ProgramStatement::Switch { .. }
        | ProgramStatement::TryCatchInt32 { .. }
        | ProgramStatement::UnwindCleanup { .. }
        // Everything else declares nothing.
        | ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::Skip
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Assign { .. }
        | ProgramStatement::CallConstruct { .. }
        | ProgramStatement::Call { .. }
        | ProgramStatement::CallResult { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Return(_)
        | ProgramStatement::Throw(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::Update { .. } => {}
    }
}

/// The names a scope declares, in the order it declares them.
pub(in crate::kernel) fn scope_declared_names(statement: &ProgramStatement) -> Vec<BindingName> {
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
    state: &ExecutionState,
    declared: &[BindingName],
) -> Result<ExecutionState, RuntimeError> {
    let mut state = state.clone();
    let mut memory = state.memory.clone();
    let mut retired = false;
    for name in declared {
        crate::instrumentation::record_deterministic_work(1);
        let Some(slot) = state.locals.slot(name).cloned() else {
            continue;
        };
        if slot.base.is_local_block() && memory.has_block(&slot.base) {
            if let Some(error) = state.population_storage_retirement_refusal(&slot.base) {
                return Err(error);
            }
            if let Some(error) =
                super::super::mutexes::automatic_storage_refusal(&state, name, &slot.base)
            {
                return Err(error);
            }
            let range = MemoryRange::new_with_element_width(
                slot.clone(),
                0.into(),
                memory
                    .block_size(&slot.base)
                    .expect("live local block")
                    .clone(),
                1,
            );
            if let Some(error) = state.automatic_storage_loan_refusal(&slot.base) {
                return Err(error);
            }
            retire_automatic_storage_owner(&mut state, &range);
            memory = memory.without_local_block(&slot.base);
            state.retire_population_storage(&slot.base)?;
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
    paths: Vec<StatementExecutionPath>,
    declared: &[BindingName],
) -> Vec<StatementExecutionPath> {
    if declared.is_empty() {
        return paths;
    }
    paths
        .into_iter()
        .map(|path| {
            let outcome = match path.outcome {
                StatementOutcome::Normal(state) => end_scope_automatic_lifetimes(&state, declared)
                    .map(|state| StatementOutcome::Normal(Box::new(state))),
                StatementOutcome::LoopTestFalse(state) => {
                    end_scope_automatic_lifetimes(&state, declared)
                        .map(|state| StatementOutcome::LoopTestFalse(Box::new(state)))
                }
                StatementOutcome::Break(state) => end_scope_automatic_lifetimes(&state, declared)
                    .map(|state| StatementOutcome::Break(Box::new(state))),
                StatementOutcome::Continue(state) => {
                    end_scope_automatic_lifetimes(&state, declared)
                        .map(|state| StatementOutcome::Continue(Box::new(state)))
                }
                StatementOutcome::Jump { target, state } => {
                    end_scope_automatic_lifetimes(&state, declared).map(|state| {
                        StatementOutcome::Jump {
                            target,
                            state: Box::new(state),
                        }
                    })
                }
                StatementOutcome::Return { value, state } => {
                    end_scope_automatic_lifetimes(&state, declared).map(|state| {
                        StatementOutcome::Return {
                            value,
                            state: Box::new(state),
                        }
                    })
                }
                StatementOutcome::Throw { value, state } => {
                    end_scope_automatic_lifetimes(&state, declared).map(|state| {
                        StatementOutcome::Throw {
                            value,
                            state: Box::new(state),
                        }
                    })
                }
                outcome @ (StatementOutcome::VerificationDiverges
                | StatementOutcome::UndefinedBehavior(_)
                | StatementOutcome::RuntimeError(_)) => Ok(outcome),
            }
            .unwrap_or_else(StatementOutcome::RuntimeError);
            StatementExecutionPath {
                loop_invariant_correspondence: Default::default(),
                call_result: None,
                outcome,
                ..path
            }
        })
        .collect()
}

/// The execution judgment a statement is stepped under
/// (`docs/internals/kernel.md`, "Execution semantics"). One driver,
/// [`execute_statement_paths`], serves both; each place they differ is a
/// branch on this value.
pub(in crate::kernel) enum StatementJudgment<'generator, 'scope> {
    /// Concrete operational outcomes. A loop runs by unrolling its
    /// iterations. A contract-less inline helper's body runs under it.
    Executes,
    /// `ProgramStatementVerifies`: an annotated loop is stepped as its checked
    /// abstraction instead, from an environment's verified loop rule or from
    /// its own invariant and effect checks, and may end in
    /// `VerificationDiverges`. The generator names the identities an
    /// abstracted loop head invents.
    Verifies(&'generator mut KernelVariableGenerator<'scope>),
}

/// `statement` stepped under the concrete judgment, which unrolls loops.
pub(in crate::kernel) fn execute_execution_statement_paths(
    state: &ExecutionState,
    statement: &ProgramStatement,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    execute_statement_paths(
        state,
        statement,
        assumptions,
        execution_context,
        budget,
        &mut StatementJudgment::Executes,
    )
}

/// Steps `statement` under `judgment`. Every statement the judgment
/// contains, in a sequence, a branch, a loop body, a switch case or a
/// handler, is stepped under the same judgment.
pub(in crate::kernel) fn execute_statement_paths(
    state: &ExecutionState,
    statement: &ProgramStatement,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    judgment: &mut StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    // Keep a source block's sequence spine out of the large leaf-operation
    // frame. Adding a fact index must not multiply stack use per statement.
    if let ProgramStatement::Seq(statements) = statement {
        let second = statements.rest();
        let mut paths = Vec::new();
        for first_path in execute_statement_paths(
            state,
            statements.first(),
            assumptions,
            execution_context,
            budget,
            judgment,
        )? {
            let StatementExecutionPath {
                call_parameters: _,
                loop_invariant_correspondence: _,
                call_result: _,
                outcome,
                facts,
                obligations,
                loan_evidence,
            } = first_path;
            match outcome {
                StatementOutcome::Normal(state) => {
                    paths.extend(execute_statement_paths_with_prefix(
                        &state,
                        &second,
                        assumptions,
                        execution_context,
                        &facts,
                        &obligations,
                        &loan_evidence,
                        budget,
                        judgment,
                    )?);
                }
                // Control leaves the sequence with everything the first
                // statement's path established, its loan evidence included.
                outcome @ (StatementOutcome::LoopTestFalse(_)
                | StatementOutcome::Break(_)
                | StatementOutcome::Continue(_)
                | StatementOutcome::Jump { .. }
                | StatementOutcome::Return { .. }
                | StatementOutcome::Throw { .. }
                | StatementOutcome::VerificationDiverges
                | StatementOutcome::UndefinedBehavior(_)
                | StatementOutcome::RuntimeError(_)) => paths.push(StatementExecutionPath {
                    call_parameters: None,
                    loop_invariant_correspondence: Default::default(),
                    call_result: None,
                    outcome,
                    facts,
                    obligations,
                    loan_evidence,
                }),
            }
        }
        budget.check_path_width(paths.len())?;
        return Ok(paths);
    }
    match judgment {
        // Profiling attributes a verification run's work to its leaf
        // statements; a branch and an abstracted loop are attributed to the
        // statements they step.
        StatementJudgment::Verifies(_)
            if !matches!(statement, ProgramStatement::If { .. })
                && !is_annotated_loop(statement) =>
        {
            crate::instrumentation::measure_operation(
                "kernel",
                "independent kernel execution",
                verification_operation_name(statement),
                || {
                    execute_execution_statement_leaf_paths(
                        state,
                        statement,
                        assumptions,
                        execution_context,
                        budget,
                        judgment,
                    )
                },
            )
        }
        _ => execute_execution_statement_leaf_paths(
            state,
            statement,
            assumptions,
            execution_context,
            budget,
            judgment,
        ),
    }
}

/// `statement` under `judgment`, after a prefix whose facts, obligations and
/// loan evidence its paths carry first.
pub(in crate::kernel) fn execute_statement_paths_with_prefix(
    state: &ExecutionState,
    statement: &ProgramStatement,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    prefix_facts: &(impl ExecutionFactSource + ?Sized),
    prefix_obligations: &[ProofObligation],
    prefix_loan_evidence: &CheckedLoanCallEvidenceSequence,
    budget: &mut ExecutionBudget,
    judgment: &mut StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let paths = execute_statement_paths(
        state,
        statement,
        &effective_assumptions,
        execution_context,
        budget,
        judgment,
    )?
    .into_iter()
    .filter_map(|path| {
        let (facts, obligations) = merge_execution_pure_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &path.facts,
            &path.obligations,
            assumptions,
        )?;
        Some(StatementExecutionPath {
            call_parameters: None,
            loop_invariant_correspondence: Default::default(),
            call_result: None,
            outcome: path.outcome,
            facts,
            obligations,
            loan_evidence: crate::kernel::loans::concat_checked_loan_evidence(
                prefix_loan_evidence,
                &path.loan_evidence,
            ),
        })
    })
    .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// Run the loop's one update after the body scopes have been exited.
/// Both normal completion and `continue` reach this region; other transfers
/// retain their successor without evaluating the update.
pub(in crate::kernel) fn paths_after_loop_update(
    paths: Vec<StatementExecutionPath>,
    update: Option<&ProgramStatement>,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    judgment: &mut StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let Some(update) = update else {
        return Ok(paths);
    };
    let mut successors = Vec::new();
    for path in paths {
        let (state, continued) = match &path.outcome {
            StatementOutcome::Normal(state) => (state, false),
            StatementOutcome::Continue(state) => (state, true),
            _ => {
                successors.push(path);
                continue;
            }
        };
        for mut successor in execute_statement_paths_with_prefix(
            state,
            update,
            assumptions,
            execution_context,
            &path.facts,
            &path.obligations,
            &path.loan_evidence,
            budget,
            judgment,
        )? {
            if continued && let StatementOutcome::Normal(state) = successor.outcome {
                successor.outcome = StatementOutcome::Continue(state);
            }
            successors.push(successor);
        }
    }
    Ok(successors)
}

/// A loop with invariant, effect or termination checks: the verification
/// judgment steps it as its checked abstraction.
fn is_annotated_loop(statement: &ProgramStatement) -> bool {
    matches!(
        statement,
        ProgramStatement::Loop {
            invariant_checks,
            effect_checks,
            ranking_measures,
            structural_measure,
            ..
        } if !invariant_checks.is_empty()
            || !effect_checks.is_empty()
            || !ranking_measures.is_empty()
            || structural_measure.is_some()
    )
}

fn verification_operation_name(statement: &ProgramStatement) -> &'static str {
    match statement {
        ProgramStatement::Skip => "verification statement: skip",
        ProgramStatement::Break => "verification statement: break",
        ProgramStatement::LoopTest { .. } => "verification statement: loop test",
        ProgramStatement::Continue => "verification statement: continue",
        ProgramStatement::Goto { .. } => "verification statement: goto",

        ProgramStatement::EndAutomaticLifetimes { .. } => {
            "verification statement: automatic lifetime end"
        }
        ProgramStatement::Declare { .. } => "verification statement: declare",
        ProgramStatement::DeclareAggregate { .. } => "verification statement: declare aggregate",
        ProgramStatement::CopyAggregate { .. } => "verification statement: aggregate copy",
        ProgramStatement::InitializeScalarArray { .. } => {
            "verification statement: scalar array initialization"
        }
        ProgramStatement::Assign { .. } => "verification statement: assign",
        ProgramStatement::CallConstruct { .. } => "verification statement: call construct",
        ProgramStatement::Call { .. } | ProgramStatement::CallResult { .. } => {
            "verification statement: call"
        }
        ProgramStatement::HeapAllocate { .. } => "verification statement: heap allocate",
        ProgramStatement::HeapFree { .. } => "verification statement: heap free",
        ProgramStatement::Assert { .. } => "verification statement: assert",
        ProgramStatement::StepValue { .. } => "verification statement: step value",
        ProgramStatement::Return(_) => "verification statement: return",
        ProgramStatement::Throw(_) | ProgramStatement::ThrowOpaque(_) => {
            "verification statement: throw"
        }
        ProgramStatement::TryCatchInt32 { .. } => "verification statement: int32 handler",
        ProgramStatement::UnwindCleanup { .. } => "verification statement: unwind cleanup",
        ProgramStatement::Store { .. } => "verification statement: store",
        ProgramStatement::TypedStore { .. } => "verification statement: typed store",
        ProgramStatement::Update { .. } => "verification statement: update",
        ProgramStatement::Loop { .. } => "verification statement: loop",
        ProgramStatement::Switch { .. } => "verification statement: switch",
        ProgramStatement::If { .. } => "verification statement: if",
        ProgramStatement::Seq(_) => "verification statement: sequence",
    }
}

fn execute_execution_statement_leaf_paths(
    state: &ExecutionState,
    statement: &ProgramStatement,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    judgment: &mut StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    budget.install_program_byte_order(execution_context.environment.byte_order());
    if let Some(pending) = &state.pending_thread_create {
        if let Some(resolved) = pending.resolve(state, assumptions) {
            return execute_statement_paths(
                &resolved,
                statement,
                assumptions,
                execution_context,
                budget,
                judgment,
            );
        }
        match statement {
            ProgramStatement::Declare {
                name,
                initializer: None,
                program_type:
                    ProgramType::Int8
                    | ProgramType::Int16
                    | ProgramType::Int32
                    | ProgramType::Int64
                    | ProgramType::UInt8
                    | ProgramType::UInt16
                    | ProgramType::UInt32
                    | ProgramType::UInt64,
                ..
            } if !pending.protects_local(state, name) => {
                let mut bare = state.clone();
                bare.pending_thread_create = None;
                let mut paths = execute_statement_paths(
                    &bare,
                    statement,
                    assumptions,
                    execution_context,
                    budget,
                    judgment,
                )?;
                for path in &mut paths {
                    if let StatementOutcome::Normal(next) = &mut path.outcome {
                        if let Some(slot) = next.locals.slot(name)
                            && let Some(bytes) = next
                                .memory
                                .block_size(&slot.base)
                                .and_then(MachineTerm::as_const)
                        {
                            next.pending_thread_create = Some(pending.with_delta(
                                super::super::threads::PendingThreadMemoryDelta::Declare {
                                    block: slot.base.clone(),
                                    bytes,
                                },
                            ));
                        } else {
                            path.outcome =
                                StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
                                    "pending pthread create cannot retain this local declaration"
                                        .to_string(),
                                ));
                        }
                    }
                }
                return Ok(paths);
            }
            ProgramStatement::Assign {
                name, expression, ..
            } if matches!(
                expression,
                ProgramExpression::Value(_)
                    | ProgramExpression::Variable(_)
                    | ProgramExpression::StepResult { .. }
            ) && state.locals.slot(name).is_some()
                && !pending.protects_local(state, name) =>
            {
                let mut bare = state.clone();
                bare.pending_thread_create = None;
                let mut paths = execute_statement_paths(
                    &bare,
                    statement,
                    assumptions,
                    execution_context,
                    budget,
                    judgment,
                )?;
                for path in &mut paths {
                    if let StatementOutcome::Normal(next) = &mut path.outcome {
                        if let (Some(slot), Some(value)) =
                            (next.locals.slot(name), next.locals.get(name))
                        {
                            next.pending_thread_create = Some(pending.with_delta(
                                super::super::threads::PendingThreadMemoryDelta::Store {
                                    pointer: slot.clone(),
                                    value: value.clone().into_native(),
                                },
                            ));
                        } else {
                            path.outcome =
                                StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
                                    "pending pthread create cannot retain this local assignment"
                                        .to_string(),
                                ));
                        }
                    }
                }
                return Ok(paths);
            }
            ProgramStatement::TypedStore { .. } if pending.has_local_handle_slot(state) => {}
            ProgramStatement::Skip | ProgramStatement::Seq(_) => {}
            ProgramStatement::If { condition, .. }
                if super::super::functions::program_expression_is_state_independent(condition) => {}
            _ => {
                budget.consume_statement_step()?;
                return Ok(vec![StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
                        "resolve the pending pthread create status before this C operation"
                            .to_string(),
                    )),
                    Vec::new().into(),
                    Vec::new(),
                )]);
            }
        }
    }
    // `Seq` is the tree representation of a source block, not an executed C
    // statement. Charging it made the statement budget depend on tree shape
    // and counted every straight-line source statement twice.
    if !matches!(statement, ProgramStatement::Seq(_)) {
        budget.consume_statement_step()?;
    }
    let paths = match statement {
        ProgramStatement::Skip => vec![StatementExecutionPath::new(
            StatementOutcome::Normal(Box::new(state.clone())),
            Vec::new().into(),
            Vec::new(),
        )],
        ProgramStatement::Break => vec![StatementExecutionPath::new(
            StatementOutcome::Break(Box::new(state.clone())),
            Vec::new().into(),
            Vec::new(),
        )],
        ProgramStatement::Continue => vec![StatementExecutionPath::new(
            StatementOutcome::Continue(Box::new(state.clone())),
            Vec::new().into(),
            Vec::new(),
        )],
        ProgramStatement::Goto { target } => vec![StatementExecutionPath::new(
            StatementOutcome::Jump {
                target: *target,
                state: Box::new(state.clone()),
            },
            Vec::new().into(),
            Vec::new(),
        )],
        ProgramStatement::EndAutomaticLifetimes { names, steps } => {
            vec![StatementExecutionPath::new(
                match end_scope_automatic_lifetimes(state, names)
                    .and_then(|next| end_aggregate_step_lifetimes(&next, steps))
                {
                    Ok(state) => StatementOutcome::Normal(Box::new(state)),
                    Err(refusal) => StatementOutcome::RuntimeError(refusal),
                },
                Vec::new().into(),
                Vec::new(),
            )]
        }

        ProgramStatement::Declare {
            name,
            program_type,
            volatile,
            pointee_volatile,
            constant,
            pointee_constant,
            initializer,
            zero_fill,
            declared_class,
        } => {
            if let Some(fill) = zero_fill
                && *constant
                && let Some(element_type) = program_type.array_element_type()
                && initializer.is_none()
            {
                let declared = declare_local(
                    state,
                    name,
                    *program_type,
                    *volatile,
                    *pointee_volatile,
                    true,
                    *pointee_constant,
                    declared_class.clone(),
                );
                return match declared {
                    Ok(declared) => scalar_arrays::construct_const(
                        &declared,
                        name,
                        element_type,
                        fill,
                        assumptions,
                        budget,
                    ),
                    Err(error) => Ok(vec![StatementExecutionPath::new(
                        StatementOutcome::RuntimeError(error),
                        Vec::new().into(),
                        Vec::new(),
                    )]),
                };
            }
            let outcome = if *program_type == ProgramType::Void {
                StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
            } else {
                match declare_local(
                    state,
                    name,
                    *program_type,
                    *volatile,
                    *pointee_volatile,
                    *constant,
                    *pointee_constant,
                    declared_class.clone(),
                )
                .and_then(|state| match zero_fill {
                    Some(zero_fill) => zero_fill_declared_array(state, name, zero_fill),
                    None => Ok(state),
                }) {
                    Ok(state) => StatementOutcome::Normal(Box::new(
                        note_declared_population_storage(state, name),
                    )),
                    Err(refusal) => StatementOutcome::RuntimeError(refusal),
                }
            };
            if let (Some(expression), StatementOutcome::Normal(declared)) = (initializer, &outcome)
            {
                if zero_fill.is_some()
                    || matches!(
                        program_type,
                        ProgramType::Int8Array(_)
                            | ProgramType::Int16Array(_)
                            | ProgramType::UInt16Array(_)
                            | ProgramType::Int32Array(_)
                            | ProgramType::UInt8Array(_)
                            | ProgramType::UInt32Array(_)
                            | ProgramType::Int64Array(_)
                            | ProgramType::Int128Array(_)
                            | ProgramType::UInt128Array(_)
                            | ProgramType::UInt64Array(_)
                            | ProgramType::Float32Array(_)
                            | ProgramType::Float64Array(_)
                            | ProgramType::PointerArray(_, _)
                    )
                {
                    return Ok(vec![StatementExecutionPath::new(
                        StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                        Vec::new().into(),
                        Vec::new(),
                    )]);
                }
                let mut paths = Vec::new();
                for path in
                    evaluate_expression_value_paths(declared, expression, assumptions, budget)?
                {
                    match path.outcome {
                        ExpressionOutcome::Value(value) => {
                            let lvalue = LValue::local_with_qualifiers(
                                name.clone(),
                                *program_type,
                                *volatile,
                                *pointee_volatile,
                            )
                            .with_constant(*constant)
                            .with_pointee_constant(*pointee_constant);
                            paths.extend(write_program_lvalue_paths_for_initialization(
                                declared,
                                lvalue,
                                value,
                                path.facts,
                                path.obligations,
                                assumptions,
                                budget,
                                true,
                                Default::default(),
                            )?);
                        }
                        ExpressionOutcome::UndefinedBehavior(error) => {
                            paths.push(StatementExecutionPath::new(
                                StatementOutcome::UndefinedBehavior(error),
                                path.facts,
                                path.obligations,
                            ))
                        }
                        ExpressionOutcome::RuntimeError(error) => {
                            paths.push(StatementExecutionPath::new(
                                StatementOutcome::RuntimeError(error),
                                path.facts,
                                path.obligations,
                            ))
                        }
                    }
                }
                if *constant {
                    for path in &mut paths {
                        if let StatementOutcome::Normal(state) = &mut path.outcome {
                            let block = state
                                .locals
                                .slot(name)
                                .expect("initialized scalar slot")
                                .base
                                .clone();
                            state.set_memory(state.memory.clone().freeze_declared_scalar(&block));
                        }
                    }
                }
                paths
            } else {
                let outcome = match outcome {
                    StatementOutcome::Normal(mut state)
                        if *constant
                            && initializer.is_none()
                            && zero_fill.is_none()
                            && (state.locals.is_uninitialized_object(name)
                                || state.locals.is_array_object(name)) =>
                    {
                        let block = state
                            .locals
                            .slot(name)
                            .expect("declared automatic slot")
                            .base
                            .clone();
                        state.set_memory(state.memory.clone().freeze_declared_object(&block, None));
                        StatementOutcome::Normal(state)
                    }
                    outcome => outcome,
                };
                vec![StatementExecutionPath::new(
                    outcome,
                    Vec::new().into(),
                    Vec::new(),
                )]
            }
        }
        ProgramStatement::DeclareAggregate {
            name,
            layout,
            kind,
            declared_class,
        } => {
            let declared = match kind {
                AggregateDeclarationKind::Local
                | AggregateDeclarationKind::ConstructionDestination => {
                    declare_aggregate_local(state, name, layout, declared_class.clone())
                }
                AggregateDeclarationKind::Constructor => {
                    begin_aggregate_construction(state, name, layout, budget)?
                }
            };
            let outcome = match declared {
                Ok(state) => StatementOutcome::Normal(Box::new(note_declared_population_storage(
                    state, name,
                ))),
                Err(refusal) => StatementOutcome::RuntimeError(refusal),
            };
            vec![StatementExecutionPath::new(
                outcome,
                Vec::new().into(),
                Vec::new(),
            )]
        }
        ProgramStatement::CopyAggregate {
            target,
            source,
            layout,
        } => execute_program_aggregate_copy_paths(
            state,
            target,
            source,
            layout,
            AggregateCopyDestination::Assignment,
            assumptions,
            budget,
        )?,
        ProgramStatement::InitializeScalarArray {
            target,
            source,
            element_type,
            count,
            copy,
            fresh,
        } => scalar_arrays::execute(
            state,
            target,
            source,
            *element_type,
            *count,
            *copy,
            *fresh,
            assumptions,
            budget,
        )?,
        ProgramStatement::Assign {
            name,
            expression,
            source,
            prior_result,
        } => {
            // A postfix update keeps the value the assignment replaces as its
            // step's result: one read of the local, as the program reads it.
            let prior = match prior_result {
                Some(step) => {
                    let reads = evaluate_expression_value_paths(
                        state,
                        &crate::kernel::program_expression::variable(name.clone()),
                        assumptions,
                        budget,
                    )?;
                    match reads.as_slice() {
                        [
                            ExpressionPath {
                                outcome: ExpressionOutcome::Value(value),
                                ..
                            },
                        ] => Some((*step, value.clone())),
                        _ => {
                            return Ok(vec![StatementExecutionPath::new(
                                StatementOutcome::RuntimeError(RuntimeError::UnboundVariable(
                                    format!("`{name}` has no single value before its update"),
                                )),
                                Vec::new().into(),
                                Vec::new(),
                            )]);
                        }
                    }
                }
                None => None,
            };
            let mut paths = execute_program_lvalue_assignment_paths(
                state,
                &crate::kernel::program_expression::variable(name.clone()),
                expression,
                assumptions,
                budget,
            )?;
            for path in &mut paths {
                if let StatementOutcome::Normal(after) = &mut path.outcome {
                    if let Some(fact) = source.completed(state, after, name) {
                        path.facts.push(fact);
                    }
                    if let Some((step, value)) = &prior {
                        after.set_retained_step_result(*step, value.clone());
                    }
                }
            }
            paths
        }
        ProgramStatement::CallConstruct {
            target,
            function_name,
            arguments,
        } => execute_program_call_construct_paths(
            state,
            target,
            function_name,
            arguments,
            assumptions,
            execution_context,
            budget,
        )?,
        ProgramStatement::Call {
            function_name,
            arguments,
            callee,
        } => execute_program_call_paths(
            state,
            None,
            function_name,
            callee.as_ref(),
            arguments,
            assumptions,
            execution_context,
            budget,
        )?,
        // A call inside the expression of the statement that follows: the
        // term it returned is that statement's `CallResult { call }`.
        ProgramStatement::CallResult {
            aggregate_layout,
            call,
            function_name,
            arguments,
            result_type,
            result_aggregate_layout,
            result_pointee_constant,
            callee,
            ..
        } => {
            if let Some(expected) = result_aggregate_layout {
                let actual = execution_context
                    .environment
                    .get_function(function_name)
                    .and_then(|function| function.return_aggregate_layout());
                if actual != Some(expected) {
                    return Ok(vec![StatementExecutionPath::new(
                        StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                        Vec::new().into(),
                        Vec::new(),
                    )]);
                }
            }
            let mut paths = if function_name == "realloc" && callee.is_none() {
                if execution_context
                    .environment
                    .selected_call_contract
                    .is_some()
                {
                    return Ok(vec![StatementExecutionPath::new(
                        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
                            "step(Contract) requires a function-pointer call".into(),
                        )),
                        Vec::new().into(),
                        Vec::new(),
                    )]);
                }
                execute_program_realloc_result_paths(
                    state,
                    *result_type,
                    arguments,
                    assumptions,
                    budget,
                )?
            } else {
                execute_program_call_paths(
                    state,
                    Some(*call),
                    function_name,
                    callee.as_ref(),
                    arguments,
                    assumptions,
                    execution_context,
                    budget,
                )?
            };
            for path in &mut paths {
                let Some(retained_value) = path.call_result.as_ref() else {
                    continue;
                };
                // The result has the callee's declared type, as it would
                // assigned to a local of that type.
                let value = match result_type {
                    // The callee already formed a value of this scalar type.
                    // An unchanged type keeps that producer, not an exported
                    // and re-imported arithmetic tree.
                    Some(program_type)
                        if !program_type.is_pointer()
                            && *program_type == retained_value.program_type() =>
                    {
                        retained_value.clone().into()
                    }
                    Some(program_type) => {
                        match crate::kernel::functions::coerce_program_value_with_pointee_constant(
                            retained_value.native().into_owned(),
                            *program_type,
                            *result_pointee_constant,
                            &mut path.obligations,
                            assumptions,
                        ) {
                            Some(value) => retained_value.retain_checked_pointer(value),
                            None => {
                                path.outcome =
                                    StatementOutcome::RuntimeError(RuntimeError::TypeMismatch);
                                continue;
                            }
                        }
                    }
                    None => retained_value.clone().into(),
                };
                if let Some(result_layout) = aggregate_layout {
                    if let StatementOutcome::Normal(state) = &mut path.outcome {
                        let Some(pointer) = value.pointer() else {
                            path.outcome =
                                StatementOutcome::RuntimeError(RuntimeError::TypeMismatch);
                            continue;
                        };
                        let pointer = pointer.address().clone();
                        let size = result_layout.layout.size_bytes();
                        // The call already materialized its by-value result in caller storage.
                        // Keep that object as the step's result, with its C lifetime and type.
                        state.set_memory(state.memory.clone().freeze_aggregate_result(
                            &pointer.base,
                            result_layout.declared_class.clone(),
                        ));
                        let owner = ResourceFact::own_memory(MemoryRange::new_with_element_width(
                            pointer.clone(),
                            0.into(),
                            size.into(),
                            1,
                        ));
                        if state.resources.exact_count(&owner) == 0 {
                            state.resources = state.resources.clone().unchecked_with_fact(owner);
                        }
                        state.aggregate_step_objects.insert(*call, pointer);
                        state.set_retained_step_result(*call, value);
                    }
                    continue;
                }
                if let StatementOutcome::Normal(state) = &mut path.outcome {
                    state.set_retained_step_result(*call, value);
                }
            }
            paths
        }
        ProgramStatement::HeapAllocate {
            target,
            bytes,
            zeroed,
            object_type,
            ends_program_on_failure,
        } => execute_program_heap_allocate_paths(
            state,
            target,
            bytes,
            *zeroed,
            object_type.as_ref(),
            *ends_program_on_failure,
            assumptions,
            budget,
        )?,
        ProgramStatement::HeapFree { pointer } => {
            execute_program_heap_free_paths(state, pointer, assumptions, budget)?
        }
        ProgramStatement::Assert { condition, label } => {
            execute_program_assert_paths(state, condition, label.as_deref(), assumptions, budget)?
        }
        // The operator's value on this path is the step's result, with the
        // operator's type as an assignment would give it.
        ProgramStatement::StepValue {
            aggregate_layout,
            steps,
            expression,
            value_type,
            pointee_constant,
            ..
        } => {
            if let Some(layout) = aggregate_layout {
                execute_program_aggregate_step_paths(
                    state,
                    steps,
                    expression,
                    layout,
                    assumptions,
                    budget,
                )?
            } else {
                let mut paths = Vec::new();
                for mut path in
                    evaluate_expression_value_paths(state, expression, assumptions, budget)?
                {
                    let outcome = match path.outcome {
                        ExpressionOutcome::Value(value) => {
                            if value.shared().is_some()
                                && value.float().is_some()
                                && value_type.is_none_or(|ty| ty == value.program_type())
                            {
                                let mut next = state.clone();
                                for step in steps {
                                    next.set_retained_step_result(*step, value.clone());
                                }
                                StatementOutcome::Normal(Box::new(next))
                            } else {
                                let retained_direct = value
                                    .shared()
                                    .filter(|root| {
                                        root.ty() == &KernelType::Bool
                                            || matches!(root.ty(), KernelType::Algebraic(_))
                                    })
                                    .cloned();
                                let retained_pointer = value
                                    .shared()
                                    .filter(|root| root.pointer_payload().is_some())
                                    .cloned();
                                let value = value.into_native();
                                let value = match value_type {
                            Some(value_type) => {
                                crate::kernel::functions::coerce_program_value_with_pointee_constant(
                                    value,
                                    *value_type,
                                    *pointee_constant,
                                    &mut path.obligations,
                                    assumptions,
                                )
                            }
                            None => Some(value),
                        };
                                match value {
                                    Some(value) => {
                                        let mut next = state.clone();
                                        let value = if let Some(root) = retained_direct
                                            && ExecutionValue::Shared(root.clone()).program_type()
                                                == value.program_type()
                                        {
                                            ExecutionValue::Shared(root)
                                        } else {
                                            match retained_pointer {
                                                Some(root) => ExecutionValue::Shared(root)
                                                    .retain_checked_pointer(value),
                                                None => ExecutionValue::from(value)
                                                    .retain_pointer_result()
                                                    .retain_float_result(),
                                            }
                                        };
                                        for step in steps {
                                            next.set_retained_step_result(*step, value.clone());
                                        }
                                        StatementOutcome::Normal(Box::new(next))
                                    }
                                    None => {
                                        StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
                                    }
                                }
                            }
                        }
                        ExpressionOutcome::UndefinedBehavior(error) => {
                            StatementOutcome::UndefinedBehavior(error)
                        }
                        ExpressionOutcome::RuntimeError(error) => {
                            StatementOutcome::RuntimeError(error)
                        }
                    };
                    paths.push(StatementExecutionPath::new(
                        outcome,
                        path.facts,
                        path.obligations,
                    ));
                }
                paths
            }
        }
        ProgramStatement::Seq(_) => unreachable!("sequences dispatch before leaf execution"),
        ProgramStatement::Return(ProgramExpression::Value(ProgramValue::Void)) => {
            let outcome = if let Some(refusal) = return_authority_refusal(state) {
                refusal
            } else if state.memory.has_pending_heap_allocation() {
                StatementOutcome::RuntimeError(RuntimeError::UnresolvedAllocationOutcome)
            } else {
                StatementOutcome::Return {
                    value: ProgramValue::Void.into(),
                    state: Box::new(state.clone()),
                }
            };
            vec![StatementExecutionPath::new(
                outcome,
                Vec::new().into(),
                Vec::new(),
            )]
        }
        ProgramStatement::Return(expression) => {
            execute_program_return_expression_paths(state, expression, assumptions, budget)?
        }
        ProgramStatement::ThrowOpaque(payload_type) => {
            let outcome = if payload_type.is_enum() {
                StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
            } else if let Some(refusal) = return_authority_refusal(state) {
                refusal
            } else {
                let variable = budget.allocate_kernel_variable()?;
                StatementOutcome::Throw {
                    value: crate::kernel::functions::symbolic_call_result(
                        ProgramType::Parameter(*payload_type),
                        variable,
                    )
                    .into(),
                    state: Box::new(state.clone()),
                }
            };
            vec![StatementExecutionPath::new(
                outcome,
                Vec::new().into(),
                Vec::new(),
            )]
        }
        ProgramStatement::Throw(expression) => {
            let mut paths = Vec::new();
            for path in evaluate_expression_value_paths(state, expression, assumptions, budget)? {
                let outcome = match path.outcome {
                    ExpressionOutcome::Value(value)
                        if matches!(
                            value.program_type(),
                            ProgramType::Int32 | ProgramType::Parameter(_)
                        ) =>
                    {
                        if let Some(refusal) = return_authority_refusal(state) {
                            refusal
                        } else {
                            StatementOutcome::Throw {
                                value: value.into(),
                                state: Box::new(state.clone()),
                            }
                        }
                    }
                    ExpressionOutcome::Value(_) => {
                        StatementOutcome::RuntimeError(RuntimeError::TypeMismatch)
                    }
                    ExpressionOutcome::UndefinedBehavior(error) => {
                        StatementOutcome::UndefinedBehavior(error)
                    }
                    ExpressionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
                };
                paths.push(StatementExecutionPath::new(
                    outcome,
                    path.facts,
                    path.obligations,
                ));
            }
            paths
        }
        ProgramStatement::TryCatchInt32 {
            try_body,
            binding,
            handler,
            ..
        } => {
            let mut paths = Vec::new();
            for try_path in execute_statement_paths(
                state,
                try_body,
                assumptions,
                execution_context,
                budget,
                judgment,
            )? {
                if let StatementOutcome::Throw {
                    value,
                    state: thrown_state,
                } = &try_path.outcome
                    && value.program_type() == ProgramType::Int32
                {
                    if thrown_state.locals.contains_name(binding) {
                        paths.push(StatementExecutionPath {
                            call_parameters: None,
                            loop_invariant_correspondence: Default::default(),
                            call_result: None,
                            outcome: StatementOutcome::RuntimeError(
                                RuntimeError::FunctionContract(format!(
                                    "int32 handler binding `{binding}` is not fresh"
                                )),
                            ),
                            facts: try_path.facts,
                            obligations: try_path.obligations,
                            loan_evidence: try_path.loan_evidence,
                        });
                        continue;
                    }
                    let bound_handler = program_seq(
                        program_declare(binding.clone(), ProgramType::Int32),
                        program_seq(
                            program_assign(
                                binding.clone(),
                                ProgramExpression::Value(value.clone().into_native()),
                            ),
                            (**handler).clone(),
                        ),
                    );
                    paths.extend(execute_statement_paths_with_prefix(
                        thrown_state,
                        &bound_handler,
                        assumptions,
                        execution_context,
                        &try_path.facts,
                        &try_path.obligations,
                        &try_path.loan_evidence,
                        budget,
                        judgment,
                    )?);
                } else {
                    paths.push(try_path);
                }
            }
            paths
        }
        // On an int32 exceptional exit, the cleanup runs in the thrown state
        // and the same exception continues: `cleanup; throw <payload>`.
        ProgramStatement::UnwindCleanup { body, cleanup } => {
            let mut paths = Vec::new();
            for body_path in execute_statement_paths(
                state,
                body,
                assumptions,
                execution_context,
                budget,
                judgment,
            )? {
                if let StatementOutcome::Throw {
                    value,
                    state: thrown_state,
                } = &body_path.outcome
                    && value.program_type() == ProgramType::Int32
                {
                    let unwinding = crate::kernel::program_unwind_continuation(
                        cleanup,
                        ProgramExpression::Value(value.clone().into_native()),
                    );
                    paths.extend(execute_statement_paths_with_prefix(
                        thrown_state,
                        &unwinding,
                        assumptions,
                        execution_context,
                        &body_path.facts,
                        &body_path.obligations,
                        &body_path.loan_evidence,
                        budget,
                        judgment,
                    )?);
                } else {
                    paths.push(body_path);
                }
            }
            paths
        }
        ProgramStatement::Store { pointer, value } => execute_program_lvalue_assignment_paths(
            state,
            &ProgramExpression::Load(Box::new(pointer.clone())),
            value,
            assumptions,
            budget,
        )?,
        ProgramStatement::TypedStore {
            pointer,
            value,
            value_type,
            access_class,
            volatile,
            pointee_constant,
            source,
        } => execute_program_lvalue_assignment_paths_with_source(
            state,
            &ProgramExpression::TypedLoad {
                pointer: Box::new(pointer.clone()),
                value_type: *value_type,
                volatile: *volatile,
                pointee_constant: *pointee_constant,
                access_class: access_class.clone(),
                source: Default::default(),
            },
            value,
            assumptions,
            budget,
            source.clone(),
        )?,
        ProgramStatement::Update {
            target,
            operator,
            operand,
        } => execute_program_lvalue_update_paths(
            state,
            target,
            *operator,
            operand,
            assumptions,
            budget,
        )?,
        ProgramStatement::If { condition, .. } | ProgramStatement::LoopTest { condition, .. } => {
            let mut paths = Vec::new();
            for condition_path in
                evaluate_program_condition_paths(state, condition, assumptions, budget)?
            {
                let ExpressionPath {
                    outcome,
                    facts,
                    obligations,
                } = condition_path;
                match outcome {
                    ExpressionOutcome::Value(value) => {
                        let truthiness_paths =
                            program_truthiness_paths(value, facts, obligations, assumptions);
                        for mut truthiness_path in truthiness_paths {
                            let path_assumptions = assumptions_with_path_context(
                                assumptions,
                                &truthiness_path.facts,
                                &truthiness_path.obligations,
                            );
                            let branch_state = resolve_pending_heap_allocations_recording(
                                state,
                                &path_assumptions,
                                &mut truthiness_path.obligations,
                            );
                            let branch_state =
                                crate::kernel::publication::resolve_observed_publications(
                                    &branch_state,
                                    &path_assumptions,
                                );
                            let branch_state = if let Some(pending) =
                                &branch_state.pending_thread_create
                            {
                                match pending.resolve(&branch_state, &path_assumptions) {
                                    Some(resolved) => resolved,
                                    None => {
                                        paths.push(StatementExecutionPath::new(StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
                                                "C branch does not decide the pending pthread create status".to_string(),
                                            )), truthiness_path.facts, truthiness_path.obligations));
                                        continue;
                                    }
                                }
                            } else {
                                branch_state
                            };
                            // The condition's call results end with it.
                            let branch_state = without_read_step_results(branch_state, condition);
                            // A test carries its own exit reason. End its
                            // temporaries on either decision, without manufacturing
                            // a source `break` or an extra statement theorem.
                            if let ProgramStatement::LoopTest {
                                aggregate_steps, ..
                            } = statement
                            {
                                let outcome = match end_aggregate_step_lifetimes(
                                    &branch_state,
                                    aggregate_steps,
                                ) {
                                    Ok(next) if truthiness_path.is_true => {
                                        StatementOutcome::Normal(Box::new(next))
                                    }
                                    Ok(next) => StatementOutcome::LoopTestFalse(Box::new(next)),
                                    Err(error) => StatementOutcome::RuntimeError(error),
                                };
                                paths.push(StatementExecutionPath::new(
                                    outcome,
                                    truthiness_path.facts,
                                    truthiness_path.obligations,
                                ));
                                continue;
                            }
                            let ProgramStatement::If {
                                then_branch,
                                else_branch,
                                ..
                            } = statement
                            else {
                                unreachable!("condition statement handled above");
                            };
                            let branch = if truthiness_path.is_true {
                                then_branch
                            } else {
                                else_branch
                            };
                            // The arm is a scope: what it declares stops
                            // existing however control leaves it.
                            let declared = scope_declared_names(branch);
                            paths.extend(paths_after_scope_exit(
                                execute_statement_paths_with_prefix(
                                    &branch_state,
                                    branch,
                                    assumptions,
                                    execution_context,
                                    &truthiness_path.facts,
                                    &truthiness_path.obligations,
                                    &empty_checked_loan_evidence_sequence(),
                                    budget,
                                    judgment,
                                )?,
                                &declared,
                            ));
                        }
                    }
                    ExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        paths.push(StatementExecutionPath::new(
                            StatementOutcome::UndefinedBehavior(undefined_behavior),
                            facts,
                            obligations,
                        ))
                    }
                    ExpressionOutcome::RuntimeError(error) => {
                        paths.push(StatementExecutionPath::new(
                            StatementOutcome::RuntimeError(error),
                            facts,
                            obligations,
                        ))
                    }
                }
            }
            if matches!(statement, ProgramStatement::LoopTest { .. })
                && let Some(helper) = &budget.inline_call_name
                && paths
                    .iter()
                    .any(|path| matches!(path.outcome, StatementOutcome::Normal(_)))
                && paths
                    .iter()
                    .any(|path| matches!(path.outcome, StatementOutcome::LoopTestFalse(_)))
            {
                vec![StatementExecutionPath::new(
                    StatementOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                        "inline helper `{helper}`: loop guard cannot be decided at the call site; give the helper a Click contract with a checked loop proof"
                    ))),
                    Vec::new().into(),
                    Vec::new(),
                )]
            } else {
                paths
            }
        }
        ProgramStatement::Loop {
            test: loop_test,
            update,
            invariant,
            invariant_checks: _,
            effect_checks: _,
            resource_specs: _,
            ranking_measures: _,
            structural_measure: _,
            body,
            ..
        } => {
            // The one judgment-specific step: verification takes an
            // annotated loop, or one an environment rule covers, as its
            // checked abstraction. Execution, and verification of a loop
            // with neither, unrolls it.
            let abstracted = match judgment {
                StatementJudgment::Verifies(variables) => {
                    crate::kernel::loops::abstract_loop_paths(
                        state,
                        statement,
                        assumptions,
                        execution_context,
                        budget,
                        variables,
                    )?
                }
                StatementJudgment::Executes => None,
            };
            match abstracted {
                Some(paths) => paths,
                None => execute_program_loop_paths(
                    state,
                    invariant,
                    body,
                    update.as_deref(),
                    loop_test,
                    assumptions,
                    execution_context,
                    budget,
                    judgment,
                )?,
            }
        }
        ProgramStatement::Switch { expression, cases } => execute_program_switch_paths(
            state,
            expression,
            cases,
            assumptions,
            execution_context,
            budget,
            judgment,
        )?,
    };
    // A statement's steps come just before it, and each result ends with
    // the statement that reads it: none is left at a loop head or a join.
    let mut paths = paths;
    if state.step_results.is_some() {
        let read = step_results_read(statement);
        if !read.is_empty() {
            for path in &mut paths {
                if let Some(state) = execution_statement_outcome_state_mut(&mut path.outcome) {
                    state.end_step_results(&read);
                }
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// `state` past a condition that read its call results, which end with it.
pub(in crate::kernel) fn without_read_step_results(
    mut state: ExecutionState,
    condition: &ProgramExpression,
) -> ExecutionState {
    if state.step_results.is_some() {
        let mut read = Vec::new();
        condition.collect_step_results_read(&mut read);
        state.end_step_results(&read);
    }
    state
}

/// The steps whose results `statement` itself reads.
fn step_results_read(statement: &ProgramStatement) -> Vec<u32> {
    let mut expressions = Vec::new();
    super::undefined_site::statement_expressions(statement, &mut expressions);
    let mut read = Vec::new();
    for (expression, _) in expressions {
        expression.collect_step_results_read(&mut read);
    }
    read
}

/// The state an outcome continues in, when it has one.
fn execution_statement_outcome_state_mut(
    outcome: &mut StatementOutcome,
) -> Option<&mut ExecutionState> {
    match outcome {
        StatementOutcome::Normal(state)
        | StatementOutcome::LoopTestFalse(state)
        | StatementOutcome::Break(state)
        | StatementOutcome::Continue(state)
        | StatementOutcome::Jump { state, .. }
        | StatementOutcome::Return { state, .. }
        | StatementOutcome::Throw { state, .. } => Some(state),
        _ => None,
    }
}

fn execute_program_switch_paths(
    state: &ExecutionState,
    expression: &ProgramExpression,
    cases: &[SwitchCase],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    judgment: &mut StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    // A `switch` body is one scope: cases fall through into each other, so a
    // declaration in one case is in scope in the next and stops existing only
    // where control leaves the switch.
    let mut declared = Vec::new();
    for case in cases {
        collect_scope_declared_names(&case.body, &mut declared);
    }
    let mut paths = Vec::new();
    for selector_path in evaluate_program_expression_paths(state, expression, assumptions, budget)?
    {
        let ExpressionPath {
            outcome,
            facts,
            obligations,
        } = selector_path;
        match outcome {
            ExpressionOutcome::Value(value) => {
                // Integer promotion keeps unsigned int unsigned. Narrower
                // integers and bool still promote to int on the supported ABI.
                let selector_type = if value.program_type() == ProgramType::UInt32 {
                    MachineIntegerType::UInt32
                } else {
                    MachineIntegerType::Int32
                };
                let Some(selector) = promote_program_path_value(value, selector_type) else {
                    paths.push(StatementExecutionPath::new(
                        StatementOutcome::RuntimeError(RuntimeError::TypeMismatch),
                        facts,
                        obligations,
                    ));
                    continue;
                };
                paths.extend(execute_program_switch_dispatch_paths(
                    state,
                    &selector,
                    selector_type,
                    cases,
                    0,
                    facts,
                    obligations,
                    assumptions,
                    execution_context,
                    budget,
                    judgment,
                )?);
            }
            ExpressionOutcome::UndefinedBehavior(error) => paths.push(StatementExecutionPath::new(
                StatementOutcome::UndefinedBehavior(error),
                facts,
                obligations,
            )),
            ExpressionOutcome::RuntimeError(error) => paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(error),
                facts,
                obligations,
            )),
        }
    }
    Ok(paths_after_scope_exit(paths, &declared))
}

fn execute_program_switch_dispatch_paths(
    state: &ExecutionState,
    selector: &MachineTerm,
    selector_type: MachineIntegerType,
    cases: &[SwitchCase],
    case_index: usize,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    judgment: &mut StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    if case_index == cases.len() {
        let default_index = cases.iter().position(|case| case.value.is_none());
        return match default_index {
            Some(default_index) => execute_program_switch_suffix_paths(
                state,
                cases,
                default_index,
                facts,
                obligations,
                assumptions,
                execution_context,
                budget,
                judgment,
            ),
            None => Ok(vec![StatementExecutionPath::new(
                StatementOutcome::Normal(Box::new(state.clone())),
                facts,
                obligations,
            )]),
        };
    }

    let case = &cases[case_index];
    let Some(value) = case.value else {
        return execute_program_switch_dispatch_paths(
            state,
            selector,
            selector_type,
            cases,
            case_index + 1,
            facts,
            obligations,
            assumptions,
            execution_context,
            budget,
            judgment,
        );
    };
    // A case label holds its 32-bit pattern after conversion to the promoted
    // selector type, including -1 becoming UINT_MAX for an unsigned selector.
    let condition = if selector_type == MachineIntegerType::UInt32 {
        ConditionTerm::uint32_equal(selector.clone(), MachineTerm::uint32_constant(value))
    } else {
        ConditionTerm::equal(selector.clone(), MachineTerm::constant(value))
    };
    let mut paths = Vec::new();
    for condition_path in
        condition_as_program_int32_paths(condition, facts, obligations, assumptions)
    {
        let ExpressionPath {
            outcome,
            facts,
            obligations,
        } = condition_path;
        let ExpressionOutcome::Value(ProgramValue::Int32(result)) = outcome else {
            unreachable!("switch case conditions produce promoted int32 values");
        };
        if result.as_const() == Some(1) {
            paths.extend(execute_program_switch_suffix_paths(
                state,
                cases,
                case_index,
                facts,
                obligations,
                assumptions,
                execution_context,
                budget,
                judgment,
            )?);
        } else {
            paths.extend(execute_program_switch_dispatch_paths(
                state,
                selector,
                selector_type,
                cases,
                case_index + 1,
                facts,
                obligations,
                assumptions,
                execution_context,
                budget,
                judgment,
            )?);
        }
    }
    Ok(paths)
}

fn execute_program_switch_suffix_paths(
    state: &ExecutionState,
    cases: &[SwitchCase],
    case_index: usize,
    facts: ExecutionFacts,
    obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    judgment: &mut StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    if case_index == cases.len() {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::Normal(Box::new(state.clone())),
            facts,
            obligations,
        )]);
    }
    let case_assumptions = assumptions_with_path_context(assumptions, &facts, &obligations);
    let mut paths = Vec::new();
    for case_path in execute_statement_paths(
        state,
        &cases[case_index].body,
        &case_assumptions,
        execution_context,
        budget,
        judgment,
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
            StatementOutcome::Normal(next_state) => {
                paths.extend(execute_program_switch_suffix_paths(
                    &next_state,
                    cases,
                    case_index + 1,
                    case_facts,
                    case_obligations,
                    assumptions,
                    execution_context,
                    budget,
                    judgment,
                )?)
            }
            StatementOutcome::Break(next_state) => paths.push(StatementExecutionPath::new(
                StatementOutcome::Normal(next_state),
                case_facts,
                case_obligations,
            )),
            outcome @ (StatementOutcome::LoopTestFalse(_)
            | StatementOutcome::Continue(_)
            | StatementOutcome::Jump { .. }
            | StatementOutcome::Return { .. }
            | StatementOutcome::Throw { .. }
            | StatementOutcome::VerificationDiverges
            | StatementOutcome::UndefinedBehavior(_)
            | StatementOutcome::RuntimeError(_)) => paths.push(StatementExecutionPath::new(
                outcome,
                case_facts,
                case_obligations,
            )),
        }
    }
    Ok(paths)
}

pub(in crate::kernel) fn execute_program_assert_paths(
    state: &ExecutionState,
    condition: &ProgramExpression,
    label: Option<&str>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let mut paths = Vec::new();
    for condition_path in evaluate_program_condition_paths(state, condition, assumptions, budget)? {
        let ExpressionPath {
            outcome,
            facts,
            obligations,
        } = condition_path;
        match outcome {
            ExpressionOutcome::Value(value) => {
                let assertion_obligation = assertion_truthiness_obligation(&value, label);
                for truthiness_path in
                    program_truthiness_paths(value, facts, obligations, assumptions)
                {
                    let mut obligations = truthiness_path.obligations;
                    if !truthiness_path.is_true {
                        obligations.push(assertion_obligation.clone());
                    }
                    paths.push(StatementExecutionPath::new(
                        StatementOutcome::Normal(Box::new(state.clone())),
                        truthiness_path.facts,
                        obligations,
                    ));
                }
            }
            ExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                paths.push(StatementExecutionPath::new(
                    StatementOutcome::UndefinedBehavior(undefined_behavior),
                    facts,
                    obligations,
                ))
            }
            ExpressionOutcome::RuntimeError(error) => paths.push(StatementExecutionPath::new(
                StatementOutcome::RuntimeError(error),
                facts,
                obligations,
            )),
        }
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(in crate::kernel) fn assertion_truthiness_obligation(
    value: &ProgramValue,
    label: Option<&str>,
) -> ProofObligation {
    let obligation = ProofObligation::verification_condition(Proposition::Equal(
        Term::ProgramValue(value.clone()),
        Term::ProgramValue(int32(1)),
    ))
    .with_assertion_failure();
    match label {
        Some(label) => obligation.with_context(label),
        None => obligation,
    }
}

/// One iteration's shared phases. The pre-test is outside the body scope:
/// a false pre-test never retires declarations in a body it did not enter.
pub(in crate::kernel) fn execute_loop_iteration_paths(
    state: &ExecutionState,
    start: crate::kernel::LoopEntryPhase,
    body: &ProgramStatement,
    update: Option<&ProgramStatement>,
    test: &LoopTestRegion,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    prefix_facts: &(impl ExecutionFactSource + ?Sized),
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
    judgment: &mut StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let entries = if start == crate::kernel::LoopEntryPhase::Test {
        execute_statement_paths_with_prefix(
            state,
            &test.statement,
            assumptions,
            execution_context,
            prefix_facts,
            prefix_obligations,
            &empty_checked_loan_evidence_sequence(),
            budget,
            judgment,
        )?
    } else {
        vec![StatementExecutionPath::new(
            StatementOutcome::Normal(Box::new(state.clone())),
            prefix_facts.persistent_facts(),
            prefix_obligations.to_vec(),
        )]
    };
    let declared = scope_declared_names(body);
    let mut paths = Vec::new();
    for entry in entries {
        if let StatementOutcome::Normal(state) = entry.outcome {
            paths.extend(paths_after_scope_exit(
                execute_statement_paths_with_prefix(
                    &state,
                    body,
                    assumptions,
                    execution_context,
                    &entry.facts,
                    &entry.obligations,
                    &entry.loan_evidence,
                    budget,
                    judgment,
                )?,
                &declared,
            ));
        } else {
            paths.push(entry);
        }
    }
    let continuation = program_loop_continuation(update, Some(test));
    paths_after_loop_update(
        paths,
        continuation.as_deref(),
        assumptions,
        execution_context,
        budget,
        judgment,
    )
}

pub(in crate::kernel) fn execute_program_loop_paths(
    state: &ExecutionState,
    invariant: &[Proposition],
    body: &ProgramStatement,
    update: Option<&ProgramStatement>,
    test: &LoopTestRegion,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    judgment: &mut StatementJudgment<'_, '_>,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    struct PendingLoopPath {
        state: ExecutionState,
        facts: ExecutionFacts,
        obligations: Vec<ProofObligation>,
    }

    let mut pending = vec![PendingLoopPath {
        state: state.clone(),
        facts: Vec::new().into(),
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

        for body_path in execute_loop_iteration_paths(
            &current_state,
            test.entry_phase(),
            body,
            update,
            test,
            &loop_assumptions,
            execution_context,
            &[],
            &[],
            budget,
            judgment,
        )? {
            let Some((step_facts, step_obligations)) = merge_execution_pure_facts_and_obligations(
                &[],
                &base_obligations,
                &body_path.facts,
                &body_path.obligations,
                &current_assumptions,
            ) else {
                continue;
            };
            let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                &accumulated_facts,
                &accumulated_obligations,
                &step_facts,
                &step_obligations,
                assumptions,
            ) else {
                continue;
            };
            match body_path.outcome {
                StatementOutcome::Normal(next_state) | StatementOutcome::Continue(next_state) => {
                    pending.push(PendingLoopPath {
                        state: *next_state,
                        facts,
                        obligations,
                    });
                }
                StatementOutcome::LoopTestFalse(next_state)
                | StatementOutcome::Break(next_state) => {
                    paths.push(StatementExecutionPath::new(
                        StatementOutcome::Normal(next_state),
                        facts,
                        obligations,
                    ));
                }
                outcome => paths.push(StatementExecutionPath::new(outcome, facts, obligations)),
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
///   the caller's `buf` would be one block, one size and one cell map. That
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
    state: &mut ExecutionState,
    name: &BindingName,
) -> Result<Address, RuntimeError> {
    let previous = state.locals.slot(name).cloned();
    if let Some(previous) = previous
        && previous.base.is_local_block()
    {
        if let Some(error) =
            crate::kernel::mutexes::automatic_storage_refusal(state, name, &previous.base)
        {
            return Err(error);
        }
        let end = state
            .memory
            .block_size(&previous.base)
            .cloned()
            .unwrap_or(MachineTerm::Variable(Variable(u64::MAX)));
        let old_range =
            MemoryRange::new_with_element_width(previous.clone(), MachineTerm::constant(0), end, 1);
        if let Some(error) = state.automatic_storage_loan_refusal(&previous.base) {
            return Err(error);
        }
        retire_automatic_storage_owner(state, &old_range);
        state.set_memory(state.memory.without_local_block(&previous.base));
        return Ok(fresh_local_object_identity(state, name));
    }
    let unnumbered = SymbolicMemory::local_pointer(name);
    if state.enclosing_frame_holds_locals()
        || state.memory.local_block_is_occupied(&unnumbered.base)
    {
        return Ok(fresh_local_object_identity(state, name));
    }
    Ok(unnumbered)
}

/// Construction authority belongs to the automatic object being retired.
/// Consume its complete byte owner through the indexed supplier frontier;
/// ordinary locals with implicit authority have no such fact to consume.
/// Live loans and protocol reservations must be checked before calling this.
pub(in crate::kernel) fn retire_automatic_storage_owner(
    state: &mut ExecutionState,
    range: &MemoryRange,
) {
    let owner = ResourceFact::own_memory(range.clone());
    let assumptions = PureFactContext::default();
    let resources = if state.resources.exact_count(&owner) != 0 {
        state
            .resources
            .clone()
            .without_fact_delaying_normalization(&owner, &assumptions)
    } else {
        state
            .resources
            .clone()
            .without_fact_incrementally(&owner, &assumptions)
    };
    if let Some(resources) = resources {
        state.resources = resources;
    }
}

/// Takes the next unused generation of `name`'s automatic object.
///
/// Refuses to hand back an identity this memory has already given out. The
/// counter is monotone and every generation it hands out is declared, so the
/// first candidate is free; checking it is what makes the uniqueness
/// invariant enforced at the one place it is created.
fn fresh_local_object_identity(state: &mut ExecutionState, name: &BindingName) -> Address {
    loop {
        let lifetime = state.next_local_lifetime();
        assert!(
            lifetime != u64::MAX,
            "ran out of automatic-object generations for `{name}`"
        );
        *state = state
            .clone()
            .with_next_local_lifetime(lifetime.saturating_add(1));
        let pointer = SymbolicMemory::local_lifetime_pointer(lifetime, name);
        if !state.memory.local_block_is_occupied(&pointer.base) {
            return pointer;
        }
        debug_assert!(
            false,
            "generation {lifetime} of `{name}` was minted twice; \
             an automatic object would share a block with another one"
        );
    }
}

/// The declaration, rather than a later memory claim or address lookup, is
/// the trusted creation event for an automatic object.
fn note_declared_population_storage(
    mut state: ExecutionState,
    name: &BindingName,
) -> ExecutionState {
    if let Some(slot) = state.locals.slot(name).cloned()
        && slot.base.is_local_block()
        && state.memory.has_block(&slot.base)
    {
        state.record_population_storage_creation(slot.base);
    }
    state
}

/// Zero-fills the automatic array `name` that was just declared, as its
/// initializer does before the elements it writes are stored: C
/// zero-initializes every element and field the initializer does not name
/// (C11 6.7.9p21). Each zero cell of an element holds the zero initializer
/// coerced to the cell's type exactly as its typed store would coerce it,
/// and holds it in every element, so the cells are one constant run each
/// over the fresh block: the declaration costs the element's cells, not the
/// array's length. Where the memory refuses runs the cells are stored one by
/// one, which leaves the same cells.
fn zero_fill_declared_array(
    mut state: ExecutionState,
    name: &BindingName,
    zero_fill: &ZeroFill,
) -> Result<ExecutionState, RuntimeError> {
    let slot = state
        .locals
        .slot(name)
        .cloned()
        .filter(|slot| slot.base.is_local_block() && state.memory.has_block(&slot.base))
        .ok_or(RuntimeError::TypeMismatch)?;
    let object_bytes = zero_fill
        .stride
        .checked_mul(zero_fill.count)
        .ok_or(RuntimeError::TypeMismatch)?;
    if state
        .memory
        .block_size(&slot.base)
        .and_then(MachineTerm::as_const)
        != Some(object_bytes)
    {
        return Err(RuntimeError::TypeMismatch);
    }
    let mut runs = Vec::with_capacity(zero_fill.cells.len());
    let mut element_end = 0u32;
    for cell in zero_fill.cells.iter() {
        crate::instrumentation::record_deterministic_work(1);
        let mut obligations = Vec::new();
        let value = crate::kernel::functions::coerce_program_value_with_pointee_constant(
            cell.zero.clone(),
            cell.value_type,
            cell.pointee_constant,
            &mut obligations,
            &PureFactContext::new(),
        )
        .filter(|_| obligations.is_empty())
        .ok_or(RuntimeError::TypeMismatch)?;
        // The cells of one element are ascending and disjoint, and lie in it.
        let end = cell
            .offset
            .checked_add(value.byte_width())
            .filter(|end| cell.offset >= element_end && *end <= zero_fill.stride)
            .ok_or(RuntimeError::TypeMismatch)?;
        element_end = end;
        runs.push(ConstantRun {
            offset: cell.offset,
            stride: zero_fill.stride,
            count: zero_fill.count,
            value,
        });
    }
    let memory = match state.memory.clone().with_constant_runs(&slot, &runs) {
        Ok(filled) => filled,
        Err(mut memory) => {
            for run in &runs {
                for index in 0..run.count {
                    crate::instrumentation::record_deterministic_work(1);
                    let offset = index
                        .checked_mul(run.stride)
                        .and_then(|offset| offset.checked_add(run.offset))
                        .ok_or(RuntimeError::TypeMismatch)?;
                    memory = memory.store(slot.offset_by_bytes(offset), run.value.clone());
                }
            }
            memory
        }
    };
    // The initializer writes every byte of the object, so they stay
    // initialized once the zero cells' values are forgotten: a run dropped
    // as a whole by a loop havoc or a store the facts cannot place then
    // costs one covering query, not its slots.
    state.set_memory(memory.with_initialized_object(&slot, object_bytes));
    Ok(state)
}

/// A local array's frame owns its bytes, as a declared scalar's does, so the
/// function can lend them to a callee that owns its buffer, such as
/// `snprintf(tmp, sizeof(tmp), ...)`.
fn own_local_array(state: &mut ExecutionState, pointer: &Address, bytes: u32) {
    state.resources = state
        .resources
        .clone()
        .unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(
                pointer.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(bytes),
                1,
            ),
        ));
}

pub(in crate::kernel) fn declare_local(
    state: &ExecutionState,
    name: &BindingName,
    program_type: ProgramType,
    volatile: bool,
    pointee_volatile: bool,
    constant: bool,
    pointee_constant: bool,
    declared_class: Option<crate::kernel::effective_type::CAccessClass>,
) -> Result<ExecutionState, RuntimeError> {
    let mut state = state.clone();
    let pointer = local_declaration_pointer(&mut state, name)?;
    // A declared local's block is placed at its type's alignment; record it
    // with the block so the alignment decision is intrinsic, as for heap
    // and file-scope blocks, rather than a path fact at each address-of.
    register_block_alignment(&pointer.base, program_type.abi_alignment());
    let byte_width = match program_type {
        ProgramType::Int128 | ProgramType::UInt128 => 16,
        // An abstract value's object holds its value in its binding; its
        // bytes are the model width it takes in memory.
        ProgramType::Parameter(_) => crate::kernel::ABSTRACT_VALUE_WIDTH,
        ProgramType::Void => unreachable!("void local objects are not supported"),
        ProgramType::Bool => 1,
        ProgramType::VoidPointer | ProgramType::VoidPointerPointer => C_POINTER_BYTE_WIDTH,
        ProgramType::Int8 => 1,
        ProgramType::Int16 | ProgramType::UInt16 => 2,
        ProgramType::Int32 => 4,
        ProgramType::Int64 | ProgramType::UInt64 | ProgramType::Float64 => 8,
        ProgramType::UInt8 => 1,
        ProgramType::UInt32 | ProgramType::Float32 => 4,
        ProgramType::Int8Pointer | ProgramType::Int8PointerPointer => C_POINTER_BYTE_WIDTH,
        ProgramType::ParameterPointer(_)
        | ProgramType::Int16Pointer
        | ProgramType::UInt16Pointer
        | ProgramType::Int32Pointer
        | ProgramType::UInt8Pointer
        | ProgramType::UInt32Pointer
        | ProgramType::Int128Pointer
        | ProgramType::Int64Pointer
        | ProgramType::UInt128Pointer
        | ProgramType::UInt64Pointer
        | ProgramType::Int16PointerPointer
        | ProgramType::UInt16PointerPointer
        | ProgramType::Int32PointerPointer
        | ProgramType::UInt8PointerPointer
        | ProgramType::UInt32PointerPointer
        | ProgramType::Int128PointerPointer
        | ProgramType::Int64PointerPointer
        | ProgramType::UInt128PointerPointer
        | ProgramType::UInt64PointerPointer
        | ProgramType::Float32Pointer
        | ProgramType::Float64Pointer
        | ProgramType::Float32PointerPointer
        | ProgramType::Float64PointerPointer
        | ProgramType::FunctionPointer(_) => C_POINTER_BYTE_WIDTH,
        ProgramType::Int32Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(4),
            ));
            own_local_array(&mut state, &pointer, length.saturating_mul(4));
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::Int32,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::UInt8Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length,
            ));
            own_local_array(&mut state, &pointer, length);
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::UInt8,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::Int8Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length,
            ));
            own_local_array(&mut state, &pointer, length);
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::Int8,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::Int16Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(2),
            ));
            own_local_array(&mut state, &pointer, length.saturating_mul(2));
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::Int16,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::UInt16Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(2),
            ));
            own_local_array(&mut state, &pointer, length.saturating_mul(2));
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::UInt16,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::UInt32Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(4),
            ));
            own_local_array(&mut state, &pointer, length.saturating_mul(4));
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::UInt32,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::Int64Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(8),
            ));
            own_local_array(&mut state, &pointer, length.saturating_mul(8));
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::Int64,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::Int128Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(16),
            ));
            own_local_array(&mut state, &pointer, length.saturating_mul(16));
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::Int128,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::UInt64Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(8),
            ));
            own_local_array(&mut state, &pointer, length.saturating_mul(8));
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::UInt64,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::UInt128Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(16),
            ));
            own_local_array(&mut state, &pointer, length.saturating_mul(16));
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::UInt128,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::Float32Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(4),
            ));
            own_local_array(&mut state, &pointer, length.saturating_mul(4));
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::Float32,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::Float64Array(length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(8),
            ));
            own_local_array(&mut state, &pointer, length.saturating_mul(8));
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                ProgramType::Float64,
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
        ProgramType::PointerArray(element, length) => {
            state.set_memory(state.memory.clone().with_classed_block(
                pointer.base.clone(),
                declared_class,
                length.saturating_mul(C_POINTER_BYTE_WIDTH),
            ));
            own_local_array(
                &mut state,
                &pointer,
                length.saturating_mul(C_POINTER_BYTE_WIDTH),
            );
            state.locals.set_array_object_at_with_constant(
                name.clone(),
                element.pointer_type(),
                length,
                pointer,
                constant,
            );
            return Ok(state);
        }
    };
    state.set_memory(state.memory.clone().with_classed_scalar_block(
        pointer.base.clone(),
        byte_width,
        program_type,
        declared_class,
    ));
    state.resources = state
        .resources
        .clone()
        .unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(
                pointer.clone(),
                MachineTerm::constant(0),
                MachineTerm::constant(byte_width),
                1,
            ),
        ));
    if volatile {
        state.locals.set_uninitialized_with_all_qualifiers(
            name.clone(),
            program_type,
            pointer,
            true,
            pointee_volatile,
            constant,
            pointee_constant,
        );
    } else {
        state.locals.set_uninitialized_with_all_qualifiers(
            name.clone(),
            program_type,
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
    state: &ExecutionState,
    name: &BindingName,
    layout: &AggregateLayout,
    declared_class: Option<crate::kernel::effective_type::CAccessClass>,
) -> Result<ExecutionState, RuntimeError> {
    let mut state = state.clone();
    let pointer = local_declaration_pointer(&mut state, name)?;
    register_block_alignment(&pointer.base, layout.alignment_bytes());
    // An object that holds one value of a library or enum type, a borrowed
    // Rust `Vec` or iterator, is a scalar of that type: a loop frame keeps
    // its owner as it keeps any automatic scalar's.
    let memory = match layout.value_type() {
        Some(value_type) => state.memory.clone().with_classed_scalar_block(
            pointer.base.clone(),
            layout.size_bytes(),
            value_type,
            declared_class,
        ),
        None => state.memory.clone().with_classed_block(
            pointer.base.clone(),
            declared_class,
            layout.size_bytes(),
        ),
    };
    state.set_memory(memory);
    state
        .locals
        .set_aggregate_object_at(name.clone(), layout.clone(), pointer.clone());
    // Every automatic record owns its complete storage, just like a scalar
    // local or a construction destination. A modular pointer result can name
    // this storage through a symbolic address, where implicit local access
    // alone cannot provide the caller's field-read permission.
    state.resources = state
        .resources
        .clone()
        .unchecked_with_fact(ResourceFact::own_memory(
            MemoryRange::new_with_element_width(
                pointer,
                MachineTerm::constant(0),
                MachineTerm::constant(layout.size_bytes()),
                1,
            ),
        ));
    Ok(state)
}

fn begin_aggregate_construction(
    state: &ExecutionState,
    name: &BindingName,
    layout: &AggregateLayout,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ExecutionState, RuntimeError>> {
    let mut state = match declare_aggregate_local(state, name, layout, None) {
        Ok(state) => state,
        Err(refusal) => return Ok(Err(refusal)),
    };
    let pointer = state
        .locals
        .slot(name)
        .expect("aggregate construction has a declared stack slot")
        .clone();
    for field in layout.fields() {
        // Aggregate array fields have no scalar placeholder. Their actual
        // constructor writes establish initialization before the value is live.
        if matches!(
            field.program_type(),
            ProgramType::Int32Array(_) | ProgramType::UInt8Array(_) | ProgramType::UInt32Array(_)
        ) {
            continue;
        }
        let variable = budget.allocate_kernel_variable()?;
        let value = crate::kernel::functions::symbolic_call_result(field.program_type(), variable);
        state.set_memory(
            state
                .memory
                .clone()
                .store(pointer.offset_by_bytes(field.offset_bytes()), value),
        );
    }
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
/// The store's byte interval is compared against the object's. A compatible
/// current cell at the slot supplies the refreshed value, including a scalar
/// reconstructed from complete byte writes. Otherwise an incompletely written
/// uninitialized object stays uninitialized; other overlaps use a symbolic
/// read of the current slot. Separate bytes leave the binding alone.
///
/// Bounded: one slot lookup keyed by the written block, then the shared byte
/// comparison against that one object. No scan of the frame.
pub(in crate::kernel) fn refresh_scalar_local_after_memory_store(
    state: &mut ExecutionState,
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) {
    let slot = Address {
        base: pointer.base.clone(),
        offset: AddressOffset::Constant(0),
    };
    let Some(name) = state.locals.name_for_slot(&slot).cloned() else {
        return;
    };
    let Some(program_type) = state.locals.scalar_object_type(&name) else {
        return;
    };
    let overlap = crate::kernel::reasoning::memory_resolution::access_byte_overlap(
        pointer,
        bytes,
        &slot,
        program_type.byte_width(),
        assumptions,
    );
    if overlap == crate::kernel::reasoning::memory_resolution::AccessByteOverlap::Separate {
        return;
    }
    refresh_scalar_local_binding(state, name, slot, program_type, assumptions);
}

/// Reconcile one address-backed scalar after a checked call effect. SymbolicMemory
/// decides its current value and initialization; a postcondition is not a store.
pub(in crate::kernel) fn refresh_scalar_local_from_memory(
    state: &mut ExecutionState,
    slot: &Address,
    assumptions: &PureFactContext,
) {
    let Some(name) = state.locals.name_for_slot(slot).cloned() else {
        return;
    };
    let Some(program_type) = state.locals.scalar_object_type(&name) else {
        return;
    };
    refresh_scalar_local_binding(state, name, slot.clone(), program_type, assumptions);
}

fn refresh_scalar_local_binding(
    state: &mut ExecutionState,
    name: BindingName,
    slot: Address,
    program_type: ProgramType,
    assumptions: &PureFactContext,
) {
    // A store through a pointer to the other signedness of the object's
    // width wrote the same bits; the local reads them in its own type.
    let current = state
        .memory
        .known_value(&slot)
        .and_then(|value| program_type.read_cell(&value));
    let refreshed = if current.is_some() {
        current
    } else if state.locals.is_uninitialized_object(&name)
        && !state
            .memory
            .has_initialized_bytes_under(&slot, program_type.byte_width(), assumptions)
    {
        // A byte write cannot turn a partially initialized scalar binding
        // into an unconstrained typed value. Allocation is not initialization.
        None
    } else {
        crate::kernel::eval::symbolic_load_value(&state.memory, &slot, program_type)
    };
    let (object_volatile, object_pointee_volatile, object_pointee_constant) =
        match state.locals.binding(&name) {
            Some(LocalBinding::Object {
                volatile,
                pointee_volatile,
                pointee_constant,
                ..
            })
            | Some(LocalBinding::UninitializedObject {
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
            program_type,
            object_volatile,
            object_pointee_volatile,
            false,
            object_pointee_constant,
        ),
        // No symbolic form for this object's type: the binding must not keep
        // saying what it said before the store.
        None => state.locals.set_uninitialized_with_all_qualifiers(
            name,
            program_type,
            slot,
            object_volatile,
            object_pointee_volatile,
            false,
            object_pointee_constant,
        ),
    }
}

pub(in crate::kernel) fn sync_stack_local(
    state: &mut ExecutionState,
    name: &BindingName,
    value: &ProgramValue,
) {
    let Some(pointer) = state.locals.slot(name).cloned() else {
        return;
    };
    if state.memory.has_block(&pointer.base) {
        state.set_memory(state.memory.clone().store(pointer, value.clone()));
    }
}

/// Keep the same retained value in a local and its memory-resident slot.
pub(in crate::kernel) fn sync_retained_stack_local(
    state: &mut ExecutionState,
    name: &BindingName,
    value: &ExecutionValue,
) {
    let Some(pointer) = state.locals.slot(name).cloned() else {
        return;
    };
    if state.memory.has_block(&pointer.base) {
        state.set_memory(state.memory.clone().store_retained(pointer, value.clone()));
    }
}

/// A pointer value moved from a pending allocation's base to its resolved
/// block. Its subobject bounds, which names the same block, moves with it.
pub(in crate::kernel) fn rebase_resolved_allocation(
    value: &Pointer,
    base: &Address,
    resolved: &Address,
) -> Pointer {
    let resolved_value = value
        .map_pointers(|address| {
            if address == base {
                resolved.clone()
            } else if address.base == base.base && base.offset == AddressOffset::Constant(0) {
                Address {
                    base: resolved.base.clone(),
                    offset: AddressOffset::add(resolved.offset.clone(), address.offset.clone()),
                }
            } else {
                address.clone()
            }
        })
        .with_bounds_owner(None);
    if resolved_value.bounds().is_none() {
        resolved_value.with_root_bounds()
    } else {
        resolved_value
    }
}
