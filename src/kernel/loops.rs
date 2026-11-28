use super::borrows::{
    CheckedBorrowCallEvidenceSequence, concat_checked_borrow_evidence,
    empty_checked_borrow_evidence_sequence,
};
use super::prelude::*;
use crate::kernel::int32_constant;
use crate::kernel::{CompareRelation, MachineIntegerType};

mod head_locals;

#[cfg(test)]
mod empty_loop_rule_tests;

#[cfg(test)]
mod pointee_const_return_tests;

#[cfg(test)]
mod head_invariant_refusal_tests;

pub(super) fn assign_call_result(
    state: &mut ExecutionState,
    target: &BindingName,
    value: impl Into<StoredExecutionValue>,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Result<(), RuntimeError> {
    let value = value.into();
    if value.program_type() == ProgramType::Void {
        return Err(RuntimeError::TypeMismatch);
    }
    let (program_type, volatile, pointee_volatile, pointee_constant) =
        match state.locals.binding(target) {
            Some(
                LocalBinding::Object {
                    program_type,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                    ..
                }
                | LocalBinding::UninitializedObject {
                    program_type,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                    ..
                }
                | LocalBinding::GlobalObject {
                    program_type,
                    volatile,
                    pointee_volatile,
                    constant,
                    pointee_constant,
                    ..
                },
            ) => {
                if *constant {
                    return Err(RuntimeError::TypeMismatch);
                }
                (
                    *program_type,
                    *volatile,
                    *pointee_volatile,
                    *pointee_constant,
                )
            }
            Some(_) => return Err(RuntimeError::TypeMismatch),
            None => (value.program_type(), false, false, false),
        };
    let value = if value.shared().is_some()
        && value.program_type() == program_type
        && matches!(
            program_type,
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
        let converted = super::eval::coerce_program_value_to_type(
            value.native().into_owned(),
            program_type,
            obligations,
            assumptions,
        )
        .ok_or(RuntimeError::TypeMismatch)?;
        value.retain_checked_pointer(converted).into()
    };
    if let Some(pointer) = state.locals.slot(target) {
        let range = MemoryRange::new_with_element_width(
            pointer.clone(),
            0u32.into(),
            1u32.into(),
            value.byte_width(),
        );
        if let Some(error) = super::mutexes::storage_write_refusal(state, &range, assumptions) {
            return Err(error);
        }
    }
    sync_retained_stack_local(state, target, &value);
    state.locals.set_retained_typed_with_all_qualifiers(
        target.clone(),
        value,
        program_type,
        volatile,
        pointee_volatile,
        false,
        pointee_constant,
    );
    Ok(())
}

/// The modeled mutex operations transfer ordinary resources, including an
/// authority-bearing control, and change no population. Thread creation and
/// join follow the worker authority protocol: create applies the worker's
/// checked contract under the authority it transfers, and join returns it.
fn is_modeled_pthread_call(function_name: &str, environment: &ExecutionEnvironment) -> bool {
    environment
        .modeled_pthread_binding
        .as_ref()
        .is_some_and(|binding| {
            [
                binding.mutex_init_name,
                binding.mutex_lock_name,
                binding.mutex_unlock_name,
                binding.mutex_destroy_name,
                binding.create_name,
                binding.join_name,
            ]
            .contains(&function_name)
        })
}

fn authority_call_refusal_path() -> StatementExecutionPath {
    StatementExecutionPath::new(
        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
            super::functions::AUTHORITY_ASSUMED_CALL_REFUSAL.to_string(),
        )),
        Vec::new().into(),
        Vec::new(),
    )
}

pub(super) fn execute_program_call_construct_paths(
    state: &ExecutionState,
    target: &BindingName,
    function_name: &str,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let Some(function) = execution_context.environment.get_function(function_name) else {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::RuntimeError(RuntimeError::UnknownFunction(
                function_name.to_string(),
            )),
            Vec::new().into(),
            Vec::new(),
        )]);
    };
    let selection = state
        .locals
        .aggregate_layout(target)
        .zip(state.locals.aggregate_object_pointer(target));
    let Some((layout, pointer)) = selection.filter(|(layout, _)| {
        function.contract_interface().aggregate_return_mode() == AggregateReturnMode::Construction
            && Some(*layout) == function.return_aggregate_layout()
            && !matches!(
                state.locals.binding(target),
                Some(LocalBinding::AggregateObject { constant: true, .. })
            )
    }) else {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
                "construction call requires a compatible writable destination".into(),
            )),
            Vec::new().into(),
            Vec::new(),
        )]);
    };
    let selected = state
        .clone()
        .with_aggregate_return_destination(pointer.clone(), layout.clone());
    let mut paths = execute_program_call_paths(
        &selected,
        None,
        function_name,
        CallDispatch::Direct,
        None,
        arguments,
        assumptions,
        execution_context,
        budget,
    )?;
    for path in &mut paths {
        if let StatementOutcome::Normal(next) | StatementOutcome::Throw { state: next, .. } =
            &mut path.outcome
        {
            next.aggregate_destination = state.aggregate_destination.clone();
        }
    }
    Ok(paths)
}

pub(super) fn execute_program_call_paths(
    state: &ExecutionState,
    result_call: Option<u32>,
    function_name: &str,
    dispatch: CallDispatch,
    callee: Option<&Callee>,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    if dispatch == CallDispatch::CppVirtual {
        let environment = execution_context.environment;
        let Some(rule) = environment.get_cpp_virtual_rule(function_name) else {
            return Ok(vec![StatementExecutionPath::new(
                StatementOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                    "virtual call to `{function_name}` requires a virtual interface contract"
                ))),
                Vec::new().into(),
                Vec::new(),
            )]);
        };
        return execute_external_transition(
            state,
            rule,
            None,
            arguments,
            assumptions,
            environment,
            budget,
        );
    }
    // A call through a function pointer calls whatever the pointer holds.
    if let Some(callee) = callee {
        let paths = indirect_call_statement_paths(execute_program_indirect_call_paths(
            state,
            function_name,
            &callee.pointer,
            callee.pointer_type,
            arguments,
            assumptions,
            execution_context,
            budget,
        )?);
        budget.check_path_width(paths.len())?;
        return Ok(paths);
    }
    if !is_modeled_pthread_call(function_name, execution_context.environment)
        && !matches!(
            state.locals.object_type(function_name),
            Some(ProgramType::FunctionPointer(_))
        )
        && execution_context
            .environment
            .get_verified_function_rule(function_name)
            .is_none()
        && execution_context
            .environment
            .get_external_function_rule(function_name)
            .is_some_and(|rule| {
                super::functions::contract_reaches_population(rule.function.contract_interface())
            })
        && !execution_context
            .environment
            .get_external_function_rule(function_name)
            .is_some_and(|rule| {
                rule.is_scoped_unselected()
                    || super::functions::authority_preserves_assumed_resource_contract(
                        rule.function.contract_interface(),
                    )
            })
    {
        return Ok(vec![authority_call_refusal_path()]);
    }
    if execution_context
        .environment
        .modeled_pthread_binding
        .as_ref()
        .is_some_and(|binding| function_name == binding.create_name)
    {
        return execute_modeled_pthread_create_paths(
            state,
            match result_call {
                Some(call) => ModeledCreateStatus::CallResult(call),
                None => ModeledCreateStatus::Discarded,
            },
            arguments,
            assumptions,
            execution_context.environment,
            budget,
        );
    }
    if execution_context
        .environment
        .modeled_pthread_binding
        .as_ref()
        .is_some_and(|binding| function_name == binding.join_name)
    {
        return execute_modeled_pthread_join_paths(
            state,
            None,
            arguments,
            assumptions,
            execution_context.environment,
            budget,
        );
    }
    if let Some(binding) = execution_context
        .environment
        .modeled_pthread_binding
        .as_ref()
        && [
            binding.mutex_init_name,
            binding.mutex_lock_name,
            binding.mutex_unlock_name,
            binding.mutex_destroy_name,
        ]
        .contains(&function_name)
    {
        return execute_modeled_pthread_mutex_paths(
            state,
            None,
            function_name,
            arguments,
            assumptions,
            execution_context.environment,
            budget,
        );
    }
    if execution_context
        .environment
        .modeled_pthread_binding
        .is_some()
        && super::publication::is_publication_operation(function_name)
    {
        return super::publication::execute_publication_paths(
            state,
            None,
            function_name,
            arguments,
            assumptions,
            execution_context.environment,
            budget,
        );
    }
    if let Some(path) = unbound_modeled_pthread_call(function_name, execution_context.environment) {
        return Ok(vec![path]);
    }
    if let Some(ProgramType::FunctionPointer(signature)) = state.locals.object_type(function_name) {
        let paths = indirect_call_statement_paths(execute_program_indirect_call_paths(
            state,
            function_name,
            &crate::kernel::program_expression::variable(function_name.to_string()),
            ProgramType::FunctionPointer(signature),
            arguments,
            assumptions,
            execution_context,
            budget,
        )?);
        budget.check_path_width(paths.len())?;
        return Ok(paths);
    }

    let Some(function) = execution_context.environment.get_function(function_name) else {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::RuntimeError(RuntimeError::UnknownFunction(
                function_name.to_string(),
            )),
            Vec::new().into(),
            Vec::new(),
        )]);
    };

    let paths = execute_program_function_call_paths(
        state,
        function,
        arguments,
        assumptions,
        execution_context,
        budget,
    )?;
    call_statement_paths(paths, budget)
}

pub(super) fn execute_reference_binding_paths(
    state: &ExecutionState,
    binding: &ReferenceBindingContract,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let environment = execution_context.environment;
    let Some(rule) = environment.get_reference_binding_rule(binding) else {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                "missing contract for {binding}"
            ))),
            Vec::new().into(),
            Vec::new(),
        )]);
    };
    execute_external_transition(
        state,
        rule,
        Some(binding),
        arguments,
        assumptions,
        environment,
        budget,
    )
}

fn execute_external_transition(
    state: &ExecutionState,
    rule: &ExternalFunctionRule,
    binding: Option<&ReferenceBindingContract>,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    if environment.selected_call_contract.is_some() {
        return Ok(vec![StatementExecutionPath::new(
            StatementOutcome::RuntimeError(RuntimeError::FunctionContract(
                "step(Contract) requires a function-pointer call".into(),
            )),
            Vec::new().into(),
            Vec::new(),
        )]);
    }
    if super::functions::contract_reaches_population(rule.function.contract_interface())
        && !super::functions::authority_preserves_assumed_resource_contract(
            rule.function.contract_interface(),
        )
    {
        return Ok(vec![authority_call_refusal_path()]);
    }
    let paths = super::functions::execute_external_function_rule(
        state,
        rule,
        binding,
        arguments,
        assumptions,
        environment,
        budget,
    )?;
    call_statement_paths(paths, budget)
}

fn call_statement_paths(
    paths: Vec<FunctionPath>,
    budget: &ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let paths = paths
        .into_iter()
        .map(|path| StatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            call_result: match &path.outcome {
                FunctionOutcome::Return { value, .. }
                    if value.program_type() != ProgramType::Void =>
                {
                    Some(value.clone())
                }
                _ => None,
            },
            outcome: match path.outcome {
                FunctionOutcome::Return { state, .. } => StatementOutcome::Normal(state),
                FunctionOutcome::Throw { value, state } => StatementOutcome::Throw { value, state },
                FunctionOutcome::VerificationDiverges => StatementOutcome::VerificationDiverges,
                FunctionOutcome::UndefinedBehavior(undefined_behavior) => {
                    StatementOutcome::UndefinedBehavior(undefined_behavior)
                }
                FunctionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
            },
            facts: path.facts,
            obligations: path.obligations,
            borrow_evidence: path.borrow_evidence,
        })
        .collect::<Vec<_>>();
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn unbound_modeled_pthread_call(
    function_name: &str,
    environment: &ExecutionEnvironment,
) -> Option<StatementExecutionPath> {
    let binding = environment.modeled_pthread_binding.as_ref()?;
    if ![
        binding.create_name,
        binding.join_name,
        binding.mutex_init_name,
        binding.mutex_lock_name,
        binding.mutex_unlock_name,
        binding.mutex_destroy_name,
    ]
    .contains(&function_name)
    {
        return None;
    }
    Some(StatementExecutionPath::new(
        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
            "modeled-pthread `{function_name}` has no checked C transition yet"
        ))),
        Vec::new().into(),
        Vec::new(),
    ))
}

/// Other workers may change an unlocked payload before the next parent
/// operation. Forget observations both before acquisition and after release;
/// otherwise joining immediately after a parent write could preserve it.
fn freshen_shared_mutex_payload(
    state: &ExecutionState,
    mutex: &Address,
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> Result<(ExecutionState, Vec<MemoryRange>), RuntimeError> {
    if !state
        .thread_ledger
        .as_ref()
        .is_some_and(|threads| threads.has_mutex_workers(mutex))
    {
        return Ok((state.clone(), Vec::new()));
    }
    let description = state
        .mutex_ledger
        .as_ref()
        .and_then(|ledger| ledger.protected_type(mutex))
        .ok_or_else(|| RuntimeError::MissingMutexUse {
            mutex: mutex.clone(),
        })?;
    let definition = environment
        .modeled_mutex_definitions
        .get(description.family())
        .ok_or_else(|| {
            RuntimeError::FunctionContract(
                "shared mutex access requires a guarded resource definition".into(),
            )
        })?;
    super::mutexes::MutexLedger::havoc_protected_for_call(
        state,
        mutex,
        definition,
        &environment.modeled_mutex_definition_list,
        assumptions,
        budget,
        super::mutexes::ProtocolSite::Own,
    )
    .map_err(|error| error.into_runtime_error(mutex))
}

fn execute_modeled_pthread_mutex_paths(
    state: &ExecutionState,
    target: Option<&BindingName>,
    function_name: &str,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let binding = environment
        .modeled_pthread_binding
        .as_ref()
        .expect("selected runtime");
    let initializing = function_name == binding.mutex_init_name;
    let expected_arity = if initializing { 2 } else { 1 };
    use crate::languages::c::thread_runtime::{MutexOperation, MutexResourceRole};
    let selected = environment.selected_call_binders.as_ref();
    let selected_contract = selected.and_then(|_| {
        MutexOperation::for_function_name(function_name).map(MutexOperation::descriptor)
    });
    let selected_is_valid = match (selected, selected_contract) {
        (None, _) => true,
        (Some(transport), Some(contract))
            if matches!(
                MutexOperation::for_function_name(function_name),
                Some(
                    MutexOperation::Init
                        | MutexOperation::Destroy
                        | MutexOperation::Lock
                        | MutexOperation::Unlock
                )
            ) =>
        {
            matches!(&transport.target, CallBinderTarget::Function(name) if name.as_ref() == contract.function_name)
                && transport.arity == contract.arity
                && transport.bindings.iter().all(|(identity, _)| {
                    contract
                        .implemented_binders()
                        .any(|binder| identity == binder.resource_binder())
                })
                && contract.implemented_binders().all(|binder| {
                    transport.bindings.contains(binder.resource_binder())
                        || (initializing && binder.role == MutexResourceRole::State)
                })
                && transport
                    .bindings
                    .iter()
                    .map(|(_, actual)| actual)
                    .collect::<std::collections::BTreeSet<_>>()
                    .len()
                    == transport.bindings.len()
        }
        _ => false,
    };
    let refusal = |message: &str| {
        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message.to_string()))
    };
    if state.pending_thread_create.is_some()
        || environment.selected_call_contract.is_some()
        || arguments.len() != expected_arity
        || !selected_is_valid
    {
        return Ok(vec![StatementExecutionPath::new(
            refusal(
                "modeled-pthread mutex call has unsupported arguments or pending thread authority",
            ),
            Vec::new().into(),
            Vec::new(),
        )]);
    }
    let mut paths = Vec::new();
    for mut path in super::functions::evaluate_program_arguments_paths(
        state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        let mut borrow_evidence = empty_checked_borrow_evidence_sequence();
        let outcome = if let Some(outcome) = path.outcome {
            match outcome {
                FunctionOutcome::UndefinedBehavior(error) => {
                    StatementOutcome::UndefinedBehavior(error)
                }
                FunctionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
                _ => refusal("modeled-pthread mutex argument did not evaluate"),
            }
        } else if !matches!(&path.values[0], ProgramValue::Pointer(pointer) if !pointer.is_null()) {
            refusal("modeled-pthread mutex requires a nonnull mutex pointer")
        } else if initializing
            && !matches!(&path.values[1],
                ProgramValue::Pointer(pointer) if pointer.is_null())
            && !matches!(&path.values[1], ProgramValue::Int32(int32_constant!(0)))
        {
            refusal("modeled-pthread mutex init requires null attributes")
        } else {
            let ProgramValue::Pointer(mutex) = &path.values[0] else {
                unreachable!()
            };
            let current = super::reasoning::path_facts::assumptions_with_path_context(
                assumptions,
                &path.facts,
                &path.obligations,
            );
            let footprint = super::mutexes::storage_write_range(mutex, binding.mutex_storage_bytes);
            let storage_refusal = (initializing && !state.preserves_mutex_protocols)
                .then(|| {
                    super::mutexes::initialization_storage_refusal(
                        state,
                        mutex.address(),
                        binding.mutex_storage_bytes,
                        binding.mutex_storage_alignment,
                        &current,
                    )
                })
                .flatten();
            let transition = if let Some(error) = storage_refusal {
                Err(error)
            } else if initializing {
                let state_binder = MutexOperation::Init
                    .descriptor()
                    .binder_by_role(MutexResourceRole::State)
                    .expect("initialization declares its optional state input");
                let state_identity = selected
                    .and_then(|transport| transport.bindings.get(state_binder.resource_binder()))
                    .and_then(ResourceBinder::instance);
                let context = if let Some(identity) = state_identity {
                    super::mutexes::MutexContext::new(state.clone())
                        .publish_declared(
                            mutex.address(),
                            identity,
                            &environment.modeled_mutex_definitions,
                            &current,
                            binding.mutex_storage_bytes,
                        )
                        .map_err(|message| RuntimeError::FunctionContract(message.to_string()))
                } else {
                    super::mutexes::MutexContext::new(state.clone())
                        .initialize_empty(mutex.address().clone(), binding.mutex_storage_bytes)
                        .map_err(|message| RuntimeError::FunctionContract(message.to_string()))
                };
                let context = context.and_then(|context| {
                    context
                        .consume_initialized_storage(
                            mutex.address(),
                            binding.mutex_storage_bytes,
                            &current,
                        )
                        .map_err(|message| RuntimeError::FunctionContract(message.to_string()))
                });
                context.and_then(|context| {
                    let (next, evidence) = context.into_runtime_transition();
                    let Some(transport) = selected else {
                        return Ok((next, evidence));
                    };
                    let lifetime = MutexOperation::Init
                        .descriptor()
                        .binder_by_role(MutexResourceRole::Lifetime)
                        .expect("initialization declares its lifetime output");
                    let output = transport
                        .bindings
                        .get(lifetime.resource_binder())
                        .and_then(ResourceBinder::mutex_authority)
                        .expect("a selected initialization binds its lifetime output");
                    let live = super::mutexes::live_resource(&next, mutex.address(), false)
                        .expect("successful initialization establishes lifetime authority");
                    next.bind_named_mutex_authority(output, &live)
                        .map(|next| (next, evidence))
                        .map_err(|_| {
                            RuntimeError::FunctionContract(
                                "mutex lifetime output could not bind its owned authority".into(),
                            )
                        })
                })
            } else if state.preserves_mutex_protocols
                && (function_name == binding.mutex_lock_name
                    || function_name == binding.mutex_unlock_name)
                && (function_name == binding.mutex_lock_name
                    || state
                        .resources
                        .mutex_use_candidate_at(mutex.address())
                        .is_some()
                    || state.opaque_mutex_acquisitions.is_some())
            {
                let acquiring = function_name == binding.mutex_lock_name;
                let operation = if acquiring {
                    MutexOperation::Lock
                } else {
                    MutexOperation::Unlock
                };
                let selected_role = |role| {
                    selected.map(|transport| {
                        let binder = operation
                            .descriptor()
                            .binder_by_role(role)
                            .expect("runtime binder role");
                        transport
                            .bindings
                            .get(binder.resource_binder())
                            .expect("a selected lock call binds each implemented binder")
                    })
                };
                let usage = state.resources.mutex_use_candidate_at(mutex.address());
                let access_matches = selected_role(MutexResourceRole::Access)
                    .and_then(ResourceBinder::mutex_authority)
                    .is_none_or(|identity| {
                        state.resolve_named_mutex_authority(identity) == usage && usage.is_some()
                    });
                let guard_matches = acquiring
                    || selected_role(MutexResourceRole::Guard)
                        .and_then(ResourceBinder::mutex_authority)
                        .is_none_or(|identity| {
                            matches!((state.resolve_named_mutex_authority(identity),
                        super::mutexes::guard_resource(state, mutex.address(), false)),
                        (Some(actual), Some(expected)) if actual == &expected)
                        });
                if !access_matches {
                    Err(RuntimeError::MissingMutexUse {
                        mutex: mutex.address().clone(),
                    })
                } else if !guard_matches {
                    Err(RuntimeError::MissingMutexGuard {
                        mutex: mutex.address().clone(),
                    })
                } else {
                    let definition = usage
                        .and_then(|fact| match fact.resource() {
                            Resource::MutexUse(usage) => usage.protected.as_ref(),
                            _ => None,
                        })
                        .and_then(|description| {
                            environment
                                .modeled_mutex_definitions
                                .get(description.family())
                        });
                    super::mutexes::opaque_runtime_transition_with_payload(
                        state,
                        mutex.address(),
                        acquiring,
                        &current,
                        definition,
                        &environment.modeled_mutex_definition_list,
                        selected_role(MutexResourceRole::State).and_then(ResourceBinder::instance),
                        budget,
                    )
                    .map_err(|error| error.into_runtime_error(mutex.address()))
                    .and_then(|(next, evidence)| {
                        if !acquiring {
                            return Ok((next, evidence));
                        }
                        let Some(output) = selected_role(MutexResourceRole::Guard)
                            .and_then(ResourceBinder::mutex_authority)
                        else {
                            return Ok((next, evidence));
                        };
                        let guard = super::mutexes::guard_resource(&next, mutex.address(), false)
                            .expect("checked acquisition establishes its guard");
                        next.bind_named_mutex_authority(output, &guard)
                            .map(|next| (next, evidence))
                            .map_err(|_| {
                                RuntimeError::FunctionContract(
                                    "mutex guard output could not bind its owned authority".into(),
                                )
                            })
                    })
                }
            } else {
                let context = super::mutexes::MutexContext::new(state.clone());
                let result = if selected.is_some()
                    && (function_name == binding.mutex_lock_name
                        || function_name == binding.mutex_unlock_name)
                {
                    Err(RuntimeError::FunctionContract(
                        "named mutex lock and unlock require an assumed mutex_use protocol".into(),
                    ))
                } else if function_name == binding.mutex_lock_name {
                    (|| {
                        let (fresh, ranges) = freshen_shared_mutex_payload(
                            state,
                            mutex.address(),
                            &current,
                            environment,
                            budget,
                        )?;
                        let before = state.memory.clone();
                        let before_point = state.path_link().clone();
                        let after = fresh.memory.clone();
                        let after_point = fresh.path_link().clone();
                        let acquired = super::mutexes::MutexContext::new(fresh)
                            .acquire_current(mutex.address(), &current)
                            .map_err(|error| error.into_runtime_error(mutex.address()))?;
                        if !ranges.is_empty() {
                            path.facts.push(
                                ExecutionPureFact::internal(Proposition::MemoryEffectSummary {
                                    before,
                                    before_point,
                                    after,
                                    after_point,
                                    mutable_ranges: ranges,
                                })
                                .into_certified(),
                            );
                        }
                        Ok(acquired)
                    })()
                } else if function_name == binding.mutex_unlock_name {
                    context
                        .release_current(mutex.address(), &current)
                        .map_err(|error| error.into_runtime_error(mutex.address()))
                } else {
                    let selected_live = selected.map(|transport| {
                        let lifetime = MutexOperation::Destroy
                            .descriptor()
                            .binder_by_role(MutexResourceRole::Lifetime)
                            .expect("destruction declares its lifetime input");
                        transport
                            .bindings
                            .get(lifetime.resource_binder())
                            .and_then(ResourceBinder::mutex_authority)
                            .expect("a selected destruction binds its lifetime input")
                    });
                    if selected_live.is_some_and(|identity| {
                        !matches!(
                            (
                                state.resolve_named_mutex_authority(identity),
                                super::mutexes::live_resource(state, mutex.address(), false)
                            ),
                            (Some(actual), Some(expected)) if actual == &expected
                        )
                    }) {
                        Err(RuntimeError::MissingMutexLive {
                            mutex: mutex.address().clone(),
                        })
                    } else {
                        context
                            .destroy(mutex.address(), &current)
                            .map_err(|error| error.into_runtime_error(mutex.address()))
                    }
                };
                result.map(super::mutexes::MutexContext::into_runtime_transition)
            };
            let transition = transition.and_then(|(next, evidence)| {
                if function_name != binding.mutex_unlock_name {
                    return Ok((next, evidence));
                }
                let (fresh, ranges) = freshen_shared_mutex_payload(
                    &next,
                    mutex.address(),
                    &current,
                    environment,
                    budget,
                )?;
                if !ranges.is_empty() {
                    path.facts.push(
                        ExecutionPureFact::internal(Proposition::MemoryEffectSummary {
                            before: next.memory.clone(),
                            before_point: next.path_link().clone(),
                            after: fresh.memory.clone(),
                            after_point: fresh.path_link().clone(),
                            mutable_ranges: ranges,
                        })
                        .into_certified(),
                    );
                }
                Ok((fresh, evidence))
            });
            match transition {
                Ok((mut next, evidence)) => {
                    borrow_evidence = evidence;
                    // Every runtime transition may change the opaque representation.
                    // Only this checked path bypasses its ordinary-write reservation.
                    if let Some(requirement) = state
                        .borrow_ledger()
                        .and_then(|ledger| ledger.memory_access_requirement(&footprint))
                    {
                        path.obligations.push(
                            ProofObligation::verification_condition(requirement)
                                .with_statement_entry_required(true)
                                .with_context("pthread mutex storage write separation"),
                        );
                    }
                    let storage = current.equality_graph.storage_address(mutex.address());
                    let storage_range = MemoryRange::new_with_element_width(
                        storage,
                        0u32.into(),
                        binding.mutex_storage_bytes.into(),
                        1,
                    );
                    let identity = budget.allocate_kernel_variable()?;
                    let memory = next.memory.clone().with_storage_memory_havoc(
                        identity,
                        &[storage_range],
                        &current,
                    );
                    next.set_memory(memory);
                    if let Some(error) = target.and_then(|target| {
                        assign_call_result(
                            &mut next,
                            target,
                            ProgramValue::Int32(OldMachineTerm::constant(0)),
                            &mut path.obligations,
                            &current,
                        )
                        .err()
                    }) {
                        StatementOutcome::RuntimeError(error)
                    } else {
                        StatementOutcome::Normal(Box::new(next))
                    }
                }
                Err(error) => StatementOutcome::RuntimeError(error),
            }
        };
        paths.push(StatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            call_result: matches!(outcome, StatementOutcome::Normal(_))
                .then(|| ProgramValue::Int32(OldMachineTerm::constant(0)).into()),
            outcome,
            facts: path.facts,
            obligations: path.obligations,
            borrow_evidence,
        });
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn modeled_pthread_handle_store(
    state: &ExecutionState,
    slot: &ProgramValue,
    value: ProgramValue,
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<(ExecutionState, Vec<ProofObligation>)>> {
    let statement = ProgramStatement::TypedStore {
        access_class: None,
        pointer: ProgramExpression::Value(slot.clone()),
        value: ProgramExpression::Value(value),
        value_type: ProgramType::UInt64,
        volatile: false,
        pointee_constant: false,
        source: Default::default(),
    };
    let paths = super::eval::execute_execution_statement_paths(
        state,
        &statement,
        assumptions,
        ExecutionContext::apply_verified_rules(environment),
        budget,
    )?;
    let [path] = paths.as_slice() else {
        return Ok(None);
    };
    match &path.outcome {
        StatementOutcome::Normal(next) => Ok(Some((*next.clone(), path.obligations.clone()))),
        _ => Ok(None),
    }
}

fn modeled_pthread_indeterminate_handle(
    mut state: ExecutionState,
    slot: &Address,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<ExecutionState> {
    let range = MemoryRange::new_with_element_width(
        slot.clone(),
        OldMachineTerm::constant(0),
        OldMachineTerm::constant(1),
        8,
    );
    let marker = budget.allocate_kernel_variable()?;
    state.set_memory(state.memory.clone().with_call_memory_havoc(
        marker,
        &[range],
        assumptions,
        None,
    ));
    if let Some(name) = state.locals.slots.get(slot).cloned() {
        let binding = state.locals.binding(&name).cloned();
        if let Some(
            LocalBinding::Object {
                program_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
                ..
            }
            | LocalBinding::UninitializedObject {
                program_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            },
        ) = binding
        {
            state.locals.set_uninitialized_with_all_qualifiers(
                name,
                program_type,
                slot,
                volatile,
                pointee_volatile,
                constant,
                pointee_constant,
            );
        }
    }
    Ok(state)
}

/// Where a modeled `pthread_create` call's status goes.
#[derive(Clone, Copy)]
enum ModeledCreateStatus {
    /// Read by its statement as this call's result.
    CallResult(u32),
    /// Not used.
    Discarded,
}

fn execute_modeled_pthread_create_paths(
    state: &ExecutionState,
    status_destination: ModeledCreateStatus,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let refusal = |message: &str| {
        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message.to_string()))
    };
    if state.pending_thread_create.is_some()
        || environment.selected_call_contract.is_some()
        || arguments.len() != 4
        || matches!(status_destination, ModeledCreateStatus::Discarded)
    {
        return Ok(vec![StatementExecutionPath::new(
            refusal(
                "modeled-pthread create requires a direct, assigned four-argument call with no unresolved earlier create",
            ),
            Vec::new().into(),
            Vec::new(),
        )]);
    }
    let mut paths = Vec::new();
    for mut path in super::functions::evaluate_program_arguments_paths(
        state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        let mut call_result = None;
        let outcome = if let Some(outcome) = path.outcome {
            match outcome {
                FunctionOutcome::UndefinedBehavior(error) => {
                    StatementOutcome::UndefinedBehavior(error)
                }
                FunctionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
                _ => refusal("modeled-pthread create argument did not evaluate"),
            }
        } else if !matches!(&path.values[0], ProgramValue::Pointer(slot) if slot.program_type() == ProgramType::UInt64Pointer)
            || !matches!(&path.values[1], ProgramValue::Pointer(attr) if attr.is_null())
            || !matches!(&path.values[3], ProgramValue::Pointer(_))
        {
            refusal(
                "modeled-pthread create requires a writable pthread_t slot, null attributes, and a pointer argument",
            )
        } else if let ProgramValue::Pointer(callback) = &path.values[2] {
            if let AddressBase::Function(worker_name) = &callback.base {
                let Some(worker) = environment.get_verified_function_rule(worker_name) else {
                    paths.push(StatementExecutionPath::new(
                        refusal(
                            "modeled-pthread create requires the direct worker's verified contract",
                        ),
                        path.facts,
                        path.obligations,
                    ));
                    continue;
                };
                let callback_type = ProgramType::FunctionPointer(
                    ProgramType::qualified_function_pointer_signature(
                        ProgramType::VoidPointer,
                        false,
                        &[(ProgramType::VoidPointer, false)],
                    ),
                );
                if callback.program_type() != callback_type
                    || worker.function.function_pointer_type() != callback_type
                {
                    paths.push(StatementExecutionPath::new(
                        refusal("modeled-pthread create requires a void *(*)(void *) worker"),
                        path.facts,
                        path.obligations,
                    ));
                    continue;
                }
                let termination = environment.get_verified_function_termination_rule(worker_name);
                let current = super::reasoning::path_facts::assumptions_with_path_context(
                    assumptions,
                    &path.facts,
                    &path.obligations,
                );
                match super::threads::ThreadContext::new(state.clone()) {
                    Ok(context) => match context.prepare_create(
                        worker,
                        termination,
                        path.values[3].clone(),
                        &current,
                        environment,
                        budget,
                    )? {
                        Ok(mut prepared) => {
                            let invocation = std::sync::Arc::new(arguments.to_vec());
                            let worker_arguments = std::sync::Arc::new(vec![arguments[3].clone()]);
                            for mut obligation in prepared.take_obligations() {
                                if let Some(source) = &mut obligation.call_requirement_site {
                                    let source = std::sync::Arc::make_mut(source);
                                    let site = std::sync::Arc::make_mut(&mut source.site);
                                    site.source_callee = Some("pthread_create".into());
                                    site.source_invocation_arguments = Some(invocation.clone());
                                    site.source_arguments = worker_arguments.clone();
                                }
                                path.obligations.push(obligation);
                            }
                            let failure = prepared.failure();
                            let (success, handle, _) = prepared.success();
                            let checked_failure_value =
                                ProgramValue::UInt64(OldMachineTerm::uint64_constant(0));
                            let slot = &path.values[0];
                            let checked_success = modeled_pthread_handle_store(
                                success.parent(),
                                slot,
                                handle.program_value(),
                                &current,
                                environment,
                                budget,
                            )?;
                            let checked_failure = modeled_pthread_handle_store(
                                failure.parent(),
                                slot,
                                checked_failure_value,
                                &current,
                                environment,
                                budget,
                            )?;
                            if let (
                                Some((mut success, success_obligations)),
                                Some((_, failure_obligations)),
                            ) = (checked_success, checked_failure)
                            {
                                path.obligations.extend(success_obligations);
                                path.obligations.extend(failure_obligations);
                                let ProgramValue::Pointer(slot_pointer) = slot else {
                                    unreachable!()
                                };
                                let output_slot = slot_pointer.address();
                                let mut failure = modeled_pthread_indeterminate_handle(
                                    failure.parent().clone(),
                                    output_slot,
                                    &current,
                                    budget,
                                )?;
                                let status =
                                    OldMachineTerm::Variable(budget.allocate_kernel_variable()?);
                                let result = ProgramValue::Int32(status.clone());
                                call_result = Some(result.clone());
                                let ModeledCreateStatus::CallResult(call) = status_destination
                                else {
                                    unreachable!("checked used status")
                                };
                                success.set_step_result(call, result.clone());
                                failure.set_step_result(call, result);
                                {
                                    let mut neutral = failure.clone();
                                    neutral.resources = success.resources.clone();
                                    neutral.borrow_ledger = success.borrow_ledger.clone();
                                    neutral.borrow_bindings = success.borrow_bindings.clone();
                                    neutral.mutex_ledger = success.mutex_ledger.clone();
                                    neutral.mutex_input_reservations =
                                        success.mutex_input_reservations.clone();
                                    neutral.opaque_mutex_acquisitions =
                                        success.opaque_mutex_acquisitions.clone();
                                    neutral.named_mutex_authorities =
                                        success.named_mutex_authorities.clone();
                                    neutral = modeled_pthread_indeterminate_handle(
                                        neutral,
                                        output_slot,
                                        &current,
                                        budget,
                                    )?;
                                    neutral.pending_thread_create =
                                        Some(super::threads::PendingThreadCreate::new(
                                            status,
                                            output_slot.clone(),
                                            handle.program_value(),
                                            &success,
                                            &failure,
                                        ));
                                    StatementOutcome::Normal(Box::new(neutral))
                                }
                            } else {
                                refusal(
                                    "modeled-pthread handle output is not writable or overlaps the worker task",
                                )
                            }
                        }
                        Err(error) => StatementOutcome::RuntimeError(error),
                    },
                    Err(error) => StatementOutcome::RuntimeError(error),
                }
            } else {
                refusal("modeled-pthread create requires a direct worker address")
            }
        } else {
            refusal("modeled-pthread create requires a direct worker address")
        };
        paths.push(
            StatementExecutionPath::new(outcome, path.facts, path.obligations)
                .with_call_result(call_result),
        );
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn execute_modeled_pthread_join_paths(
    state: &ExecutionState,
    target: Option<&BindingName>,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let refusal = |message: &str| {
        StatementOutcome::RuntimeError(RuntimeError::FunctionContract(message.to_string()))
    };
    if environment.selected_call_contract.is_some() || arguments.len() != 2 {
        return Ok(vec![StatementExecutionPath::new(
            refusal("modeled-pthread join requires its direct two-argument C call"),
            Vec::new().into(),
            Vec::new(),
        )]);
    }
    let mut paths = Vec::new();
    for mut path in super::functions::evaluate_program_arguments_paths(
        state,
        arguments,
        assumptions,
        budget,
        Some(environment),
    )? {
        let current = super::reasoning::path_facts::assumptions_with_path_context(
            assumptions,
            &path.facts,
            &path.obligations,
        );
        let outcome = if let Some(outcome) = path.outcome {
            match outcome {
                FunctionOutcome::UndefinedBehavior(error) => {
                    StatementOutcome::UndefinedBehavior(error)
                }
                FunctionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
                _ => refusal("modeled-pthread join argument did not evaluate"),
            }
        } else if !matches!(&path.values[1], ProgramValue::Pointer(pointer) if pointer.is_null()) {
            refusal("modeled-pthread join requires a null result slot")
        } else if let Some(handle) =
            super::threads::ThreadHandle::resolve_program_value(&path.values[0], &current)
        {
            let joined = super::threads::ThreadContext::new(state.clone()).and_then(|context| {
                context
                    .join(
                        handle,
                        super::threads::JoinRuntimeAssumption::ValidJoinSucceeds,
                        &current,
                    )
                    .map_err(|message| RuntimeError::FunctionContract(message.to_string()))
            });
            match joined {
                Ok((joined, facts)) => {
                    path.facts.extend(facts);
                    let mut next = joined.parent().clone();
                    if let Some(error) = target.and_then(|target| {
                        assign_call_result(
                            &mut next,
                            target,
                            ProgramValue::Int32(OldMachineTerm::constant(0)),
                            &mut path.obligations,
                            &current,
                        )
                        .err()
                    }) {
                        StatementOutcome::RuntimeError(error)
                    } else {
                        StatementOutcome::Normal(Box::new(next))
                    }
                }
                Err(error) => StatementOutcome::RuntimeError(error),
            }
        } else {
            refusal("modeled-pthread join handle does not name a live child")
        };
        paths.push(
            StatementExecutionPath::new(outcome, path.facts, path.obligations)
                .with_call_result(Some(ProgramValue::Int32(OldMachineTerm::constant(0)))),
        );
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

fn indirect_call_statement_paths(paths: Vec<FunctionPath>) -> Vec<StatementExecutionPath> {
    paths
        .into_iter()
        .map(|path| StatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            call_result: match &path.outcome {
                FunctionOutcome::Return { value, .. }
                    if value.program_type() != ProgramType::Void =>
                {
                    Some(value.clone())
                }
                _ => None,
            },
            outcome: match path.outcome {
                FunctionOutcome::Return { state, .. } => StatementOutcome::Normal(state),
                FunctionOutcome::Throw { value, state } => StatementOutcome::Throw { value, state },
                FunctionOutcome::VerificationDiverges => StatementOutcome::VerificationDiverges,
                FunctionOutcome::UndefinedBehavior(error) => {
                    StatementOutcome::UndefinedBehavior(error)
                }
                FunctionOutcome::RuntimeError(error) => StatementOutcome::RuntimeError(error),
            },
            facts: path.facts,
            obligations: path.obligations,
            borrow_evidence: path.borrow_evidence,
        })
        .collect()
}

fn execute_program_indirect_call_paths(
    state: &ExecutionState,
    function_name: &str,
    pointer: &ProgramExpression,
    function_type: ProgramType,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<FunctionPath>> {
    budget.install_program_byte_order(execution_context.environment.byte_order());
    if function_type == ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED) {
        return Ok(vec![FunctionPath::new(
            FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                "indirect calls require a supported callback signature".into(),
            )),
            Vec::new().into(),
            Vec::new(),
        )]);
    }
    let mut paths = Vec::new();
    for target_path in evaluate_program_expression_paths(state, pointer, assumptions, budget)? {
        let ExpressionPath {
            outcome,
            facts,
            obligations,
        } = target_path;
        let target_names = match outcome {
            ExpressionOutcome::Value(ProgramValue::Pointer(pointer))
                if matches!(pointer.offset.view(), OffsetView::Constant(0)) =>
            {
                match &pointer.base {
                    AddressBase::Function(name)
                        if execution_context
                            .environment
                            .selected_call_contract
                            .is_none() =>
                    {
                        vec![Ok(name.clone())]
                    }
                    AddressBase::FunctionSymbolic(_)
                    | AddressBase::Function(_)
                    | AddressBase::Load(_)
                        if matches!(pointer.program_type(), ProgramType::FunctionPointer(_)) =>
                    {
                        let target_assumptions =
                            assumptions_with_path_context(assumptions, &facts, &obligations);
                        let owned = super::functions::contracts_for_pointer(
                            pointer.address(),
                            &target_assumptions,
                            execution_context.environment,
                            &function_type,
                        );
                        let contracts = owned.iter().collect::<Vec<_>>();
                        if let Some(selected) =
                            &execution_context.environment.selected_call_contract
                            && !contracts
                                .iter()
                                .any(|contract| contract.name() == selected.as_ref())
                        {
                            paths.push(FunctionPath::new(FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(
                                    format!("contract `{selected}` is not established for this callback with its call signature"))), facts, obligations));
                            continue;
                        }
                        if contracts.is_empty() {
                            paths.push(FunctionPath::new(
                                FunctionOutcome::RuntimeError(
                                    RuntimeError::AbstractFunctionPointerCall(
                                        function_name.to_string(),
                                    ),
                                ),
                                facts,
                                obligations,
                            ));
                            continue;
                        }
                        for mut call_path in execute_program_function_contracts_paths(
                            state,
                            &contracts,
                            arguments,
                            &target_assumptions,
                            execution_context.environment,
                            budget,
                        )? {
                            let mut merged_facts = facts.clone();
                            merged_facts.extend_shared(&call_path.facts);
                            let mut merged_obligations = obligations.clone();
                            merged_obligations.extend(call_path.obligations);
                            call_path.facts = merged_facts;
                            call_path.obligations = merged_obligations;
                            paths.push(call_path);
                        }
                        continue;
                    }
                    _ => vec![Err(RuntimeError::TypeMismatch)],
                }
            }
            ExpressionOutcome::Value(_) => vec![Err(RuntimeError::TypeMismatch)],
            ExpressionOutcome::UndefinedBehavior(error) => {
                paths.push(FunctionPath::new(
                    FunctionOutcome::UndefinedBehavior(error),
                    facts,
                    obligations,
                ));
                continue;
            }
            ExpressionOutcome::RuntimeError(error) => {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(error),
                    facts,
                    obligations,
                ));
                continue;
            }
        };

        for target_name in target_names {
            let Ok(target_name) = target_name else {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(target_name.unwrap_err()),
                    facts.clone(),
                    obligations.clone(),
                ));
                continue;
            };
            let Some(function) = execution_context.environment.get_function(&target_name) else {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(RuntimeError::UnknownFunction(target_name)),
                    facts.clone(),
                    obligations.clone(),
                ));
                continue;
            };
            if function.function_pointer_type() != function_type {
                paths.push(FunctionPath::new(
                    FunctionOutcome::RuntimeError(RuntimeError::FunctionContract(format!(
                        "function pointer target `{}` has an incompatible signature",
                        function.name()
                    ))),
                    facts.clone(),
                    obligations.clone(),
                ));
                continue;
            }
            let target_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            for mut call_path in execute_program_function_call_paths(
                state,
                function,
                arguments,
                &target_assumptions,
                execution_context,
                budget,
            )? {
                let mut merged_facts = facts.clone();
                merged_facts.extend_shared(&call_path.facts);
                let mut merged_obligations = obligations.clone();
                // Target selection owns the original invocation name. Keep it
                // on this call's output obligations, without inspecting the
                // caller's facts or changing nested inline-call sources.
                let source_callee: std::sync::Arc<str> = function_name.into();
                merged_obligations.extend(call_path.obligations.into_iter().map(
                    |mut obligation| {
                        if let Some(source) = &mut obligation.call_requirement_site
                            && source.site.callee == function.name()
                        {
                            let source = std::sync::Arc::make_mut(source);
                            std::sync::Arc::make_mut(&mut source.site).source_callee =
                                Some(source_callee.clone());
                        }
                        obligation
                    },
                ));
                call_path.facts = merged_facts;
                call_path.obligations = merged_obligations;
                paths.push(FunctionPath {
                    outcome: call_path.outcome,
                    facts: call_path.facts,
                    obligations: call_path.obligations,
                    borrow_evidence: call_path.borrow_evidence,
                });
            }
        }
    }
    budget.check_path_width(paths.len())?;
    Ok(paths)
}

/// `ProgramStatementVerifies` for `statement`: the one statement driver under the
/// verification judgment.
pub(super) fn execute_execution_statement_verification_paths(
    state: &ExecutionState,
    statement: &ProgramStatement,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    super::eval::execute_statement_paths(
        state,
        statement,
        assumptions,
        execution_context,
        budget,
        &mut super::eval::StatementJudgment::Verifies(variables),
    )
}

/// The verification judgment's step of a loop, when it has one: the paths
/// of the environment's verified rule for it, or, with checks, its exit
/// paths from those checks. `None` leaves the loop to be unrolled, as the
/// execution judgment does.
///
/// Under [`LoopSemantics::ApplyVerifiedRules`] a loop with checks and no
/// applicable rule has no paths: its authority is the rule.
pub(in crate::kernel) fn abstract_loop_paths(
    state: &ExecutionState,
    statement: &ProgramStatement,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Option<Vec<StatementExecutionPath>>> {
    let annotated = matches!(
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
    );
    if execution_context.semantics.loops == LoopSemantics::ApplyVerifiedRules {
        // A checked rule may have no invariant, effect, or measure checks.
        // Its authority is the rule itself, not a nonempty annotation bundle.
        if let Some(rule) = execution_context.environment.applicable_verified_loop_rule(
            state,
            statement,
            assumptions,
        ) {
            let paths = rule
                .paths
                .iter()
                .cloned()
                .map(|mut path| {
                    path.facts = path
                        .facts
                        .into_iter()
                        .map(ExecutionPureFact::into_certified)
                        .collect();
                    path
                })
                .collect::<Vec<_>>();
            budget.check_path_width(paths.len())?;
            return Ok(Some(paths));
        }
        if annotated {
            return Ok(Some(Vec::new()));
        }
    }
    if !annotated {
        return Ok(None);
    }
    // Loop verification and verified-call execution share one symbolic
    // identity stream: `variables` allocates from `budget`, so nothing has
    // to be synchronized across this boundary.
    let paths = execute_program_loop_exit_paths(
        state,
        LoopExecutionView::of(statement).expect("matched a loop statement"),
        assumptions,
        execution_context.environment,
        Some(execution_context.environment),
        &[],
        &[],
        &[],
        &[],
        None,
        None,
        execution_context.semantics,
        false,
        budget,
        variables,
    )?;
    budget.check_path_width(paths.len())?;
    Ok(Some(paths))
}

/// Checks the state components that a loop back edge cannot silently reset.
/// Scalar locals and ordinary memory cells are handled by the existing loop
/// abstraction and effect checks; heap lifetime, resource ownership, and
/// counted resource populations are separate semantic state and must either
/// be unchanged at the loop-state join.
#[cfg(test)]
pub(crate) fn loop_state_components_match_at_back_edge(
    top_state: &ExecutionState,
    next_state: &ExecutionState,
    assumptions: &PureFactContext,
    composite_resource_definitions: &[CompositeResourceDefinition],
) -> Result<(), String> {
    loop_state_components_match_at_back_edge_inner(
        top_state,
        next_state,
        composite_resource_definitions,
        assumptions,
        &[],
    )
}

/// Validate protocol custody before forgetting a loop binder's model values.
pub(crate) fn loop_binder_state_components_match_at_back_edge(
    top: &ExecutionState,
    next: &ExecutionState,
    binders: &[LoopBinder],
    assumptions: &PureFactContext,
    definitions: &[CompositeResourceDefinition],
) -> Result<(), String> {
    let (direct_next, mut checked) =
        super::mutexes::normalize_direct_loop_guards(top, next, assumptions)?;
    let next = &direct_next;
    for binder in binders {
        let Some(head) = top.resources().owned_instance(binder.identity) else {
            continue;
        };
        let Some((mutex, _)) =
            super::functions::loop_instance_guard(top, head, definitions, assumptions)?
        else {
            continue;
        };
        if !top
            .mutex_ledger
            .as_ref()
            .is_some_and(|l| l.is_loop_abstract(&mutex))
        {
            continue;
        }
        let actual = next
            .resources()
            .owned_instance(binder.identity)
            .ok_or_else(|| format!("Requires owns {} for loop guard", binder.name))?;
        let Some((next_mutex, held)) =
            super::functions::loop_instance_guard(next, actual, definitions, assumptions)?
        else {
            return Err("loop guard resource changed its definition".into());
        };
        if mutex != next_mutex {
            return Err("loop guard resource changed its mutex".into());
        }
        check_loop_guard_custody(next, &mutex, &held, assumptions)?;
        checked.push(mutex);
    }
    loop_state_components_match_at_back_edge_inner(
        top,
        &loop_state_with_head_binder_models(next, top, binders),
        definitions,
        assumptions,
        &checked,
    )
}

fn check_loop_guard_custody(
    state: &ExecutionState,
    mutex: &Address,
    held: &OldConditionTerm,
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let ledger = state
        .mutex_ledger
        .as_ref()
        .ok_or("Requires an initialized loop mutex")?;
    let expected = condition_is_decided(assumptions, held)
        .ok_or("Requires the loop resource condition to determine guard ownership")?;
    if condition_is_decided(assumptions, ledger.held_condition(mutex).old_form()) != Some(expected)
    {
        return Err("loop resource guard ownership does not match the mutex acquisition".into());
    }
    Ok(())
}

/// Feasible decisions at a loop head, independent of its ownership join.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub(crate) enum LoopConditionFeasibility {
    Unreachable,
    TrueOnly,
    FalseOnly,
    Both,
}

impl LoopConditionFeasibility {
    fn from_possible_outcomes(may_continue: bool, may_exit: bool) -> Self {
        match (may_continue, may_exit) {
            (false, false) => Self::Unreachable,
            (true, false) => Self::TrueOnly,
            (false, true) => Self::FalseOnly,
            (true, true) => Self::Both,
        }
    }

    pub(crate) fn may_continue(self) -> bool {
        matches!(self, Self::TrueOnly | Self::Both)
    }

    /// The declared measures that this boundary must read and prove.
    pub(crate) fn required_ranking_measures(
        self,
        declared: &[RankingComponent],
    ) -> &[RankingComponent] {
        if self.may_continue() { declared } else { &[] }
    }

    pub(crate) fn may_exit(self) -> bool {
        matches!(self, Self::FalseOnly | Self::Both)
    }
}

/// Classify the selected condition once; an unresolved evaluation remains
/// conservative and cannot itself certify an exit.
pub(crate) fn classify_loop_condition(
    state: &ExecutionState,
    condition: &ProgramExpression,
    assumptions: &PureFactContext,
) -> Result<LoopConditionFeasibility, String> {
    loop_condition_feasibility(state, condition, assumptions).map_err(|limit| {
        format!(
            "could not classify the loop condition: it stopped at {}",
            limit.describe()
        )
    })
}

fn loop_condition_feasibility(
    state: &ExecutionState,
    condition: &ProgramExpression,
    assumptions: &PureFactContext,
) -> ExecutionResult<LoopConditionFeasibility> {
    let mut budget = ExecutionBudget::beside_live_state().with_program_expression_cost(condition);
    let expression_paths =
        evaluate_program_condition_paths(state, condition, assumptions, &mut budget)?;
    let mut may_continue = false;
    let mut may_exit = false;
    for path in expression_paths {
        match path.outcome {
            ExpressionOutcome::Value(value) => {
                if condition_path_is_ruled_out(&path.facts, assumptions) {
                    continue;
                }
                for path in
                    program_truthiness_paths(value, path.facts, path.obligations, assumptions)
                {
                    if path.is_true {
                        may_continue = true;
                    } else {
                        may_exit = true;
                    }
                }
            }
            ExpressionOutcome::UndefinedBehavior(_) | ExpressionOutcome::RuntimeError(_) => {
                may_continue = true;
                may_exit = true;
            }
        }
    }
    Ok(LoopConditionFeasibility::from_possible_outcomes(
        may_continue,
        may_exit,
    ))
}

fn condition_path_is_ruled_out(
    facts: &(impl ExecutionFactSource + ?Sized),
    assumptions: &PureFactContext,
) -> bool {
    facts.fact_iter().any(|fact| {
        let Proposition::ConditionIs(condition, value) = fact.proposition() else {
            return false;
        };
        condition_value_is_proven(assumptions, condition.old_form(), !value)
    })
}

/// Decide one bare condition through the exact fact index, the intrinsic
/// rule, and the frozen condition checker. This is deliberately not the
/// general proposition prover: a kernel route that prunes an execution path
/// or a mutable-footprint check must be a theory decision over the named
/// condition, not a logical proof search over unrelated ambient facts.
pub(super) fn condition_is_decided(
    assumptions: &PureFactContext,
    condition: &OldConditionTerm,
) -> Option<bool> {
    assumptions
        .exact_condition_value(condition)
        .or_else(|| PureFactContext::decide_intrinsically(condition))
        .or_else(|| assumptions.difference_decision(condition, &[]))
}

fn condition_is_decided_true(assumptions: &PureFactContext, condition: &OldConditionTerm) -> bool {
    condition_is_decided(assumptions, condition) == Some(true)
}

fn condition_value_is_proven(
    assumptions: &PureFactContext,
    condition: &OldConditionTerm,
    value: bool,
) -> bool {
    condition_is_decided(assumptions, condition) == Some(value)
        || (!value
            && condition_complement(condition)
                .is_some_and(|complement| condition_is_decided_true(assumptions, &complement)))
}

fn condition_complement(condition: &OldConditionTerm) -> Option<OldConditionTerm> {
    match condition {
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessThan,
            left,
            right,
        } => Some(OldConditionTerm::signed_greater_equal(
            left.as_ref().clone(),
            right.as_ref().clone(),
        )),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::LessEqual,
            left,
            right,
        } => Some(OldConditionTerm::signed_greater_than(
            left.as_ref().clone(),
            right.as_ref().clone(),
        )),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterThan,
            left,
            right,
        } => Some(OldConditionTerm::signed_less_equal(
            left.as_ref().clone(),
            right.as_ref().clone(),
        )),
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32,
            relation: CompareRelation::GreaterEqual,
            left,
            right,
        } => Some(OldConditionTerm::signed_less_than(
            left.as_ref().clone(),
            right.as_ref().clone(),
        )),
        _ => None,
    }
}

fn loop_state_components_match_at_back_edge_inner(
    top_state: &ExecutionState,
    next_state: &ExecutionState,
    composite_resource_definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    checked_mutexes: &[Address],
) -> Result<(), String> {
    let mut changed = Vec::new();
    if !top_state
        .memory()
        .heap
        .has_same_allocation_lifetimes_up_to_ended(&next_state.memory().heap)
    {
        changed.push("heap allocation lifetime");
    }
    // The read authority an owned instance publishes is an observation of
    // that instance, which the head derives again on every visit. Ownership
    // is what a back edge has to return, so the two contexts are compared
    // without it.
    let top_resources = top_state
        .resources()
        .clone()
        .without_owned_instance_read_views();
    let next_resources = next_state
        .resources()
        .clone()
        .without_owned_instance_read_views();
    if !crate::kernel::api::contract_certification::resource_contexts_definitionally_equal_with_definitions(
        composite_resource_definitions,
        &top_state.program_point(),
        &top_resources,
        &next_state.program_point(),
        &next_resources,
        assumptions,
    ) {
        changed.push("resource ownership");
    }
    if !crate::kernel::api::population_observations_equal(top_state, next_state) {
        changed.push("counted resource populations");
    }
    if top_state.borrow_ledger != next_state.borrow_ledger {
        changed.push("stable-view borrow authority");
    }
    // The head keeps a pointer local's subobject only if every back edge
    // returns the local to that same subobject.
    if top_state.locals().object_values().any(|(name, value)| {
        program_value_subobject_bounds(value).is_some()
            && next_state
                .locals()
                .get(name)
                .map(program_value_subobject_bounds)
                != Some(program_value_subobject_bounds(value))
    }) {
        changed.push("pointer subobject bounds");
    }
    // Likewise the class of the object a pointer local designates
    // (`design/effective-types.md`). A proved-null back edge designates no
    // object, so it cannot conflict with that class. This does not attach
    // the head's class to the null value.
    let object_class_mismatch = top_state
        .locals()
        .object_values()
        .find_map(|(name, value)| {
            let head = program_value_object_class(value)?;
            let next = next_state.locals().get(name);
            let back_edge = next.map(program_value_object_class);
            if back_edge == Some(Some(head.clone()))
                || next
                    .and_then(|value| value.pointer())
                    .is_some_and(|pointer| {
                        assumptions.pointers_known_equal(pointer.address(), &Address::null())
                    })
            {
                return None;
            }
            Some((name.to_owned(), head, back_edge))
        });
    if object_class_mismatch.is_some() {
        changed.push("pointer object classes");
    }
    if top_state.borrow_participant != next_state.borrow_participant {
        changed.push("stable-view borrow participant");
    }
    if top_state.borrow_bindings != next_state.borrow_bindings {
        changed.push("stable-view occurrence bindings");
    }
    if top_state.preserves_mutex_protocols != next_state.preserves_mutex_protocols {
        changed.push("mutex protocol frame");
    }
    if top_state.opaque_mutex_acquisitions != next_state.opaque_mutex_acquisitions {
        changed.push("opaque mutex acquisitions");
    }
    let same_named_authorities = match (
        &top_state.named_mutex_authorities,
        &next_state.named_mutex_authorities,
    ) {
        (None, None) => true,
        (Some(top), Some(next)) => top.same_logical_bindings(next),
        _ => false,
    };
    // Checked preserving calls may refresh occurrence indexes. The raw
    // resource/protocol checks still require the same authority at the edge.
    if !same_named_authorities {
        changed.push("named mutex authority bindings");
    }
    if top_state.mutex_input_reservations != next_state.mutex_input_reservations {
        changed.push("mutex input storage reservations");
    }
    match (&top_state.mutex_ledger, &next_state.mutex_ledger) {
        (None, None) => {}
        (Some(top), Some(next)) => match top.check_loop_protocol_state_since(next, checked_mutexes)
        {
            Ok(()) => {}
            Err(super::mutexes::MutexProtocolMismatch::Initialization) => {
                return Err("Click does not yet support destroying and reinitializing a loop-head mutex across a loop backedge; the loop requires the same initialization".into());
            }
            Err(super::mutexes::MutexProtocolMismatch::State) => changed.push("mutex ownership"),
        },
        _ => changed.push("mutex ownership"),
    }
    if changed.is_empty() {
        Ok(())
    } else {
        let mut message = format!(
            "loop state join changes {}; the body path does not reach the loop-head state",
            changed.join(", ")
        );
        if let Some((name, head, back_edge)) = object_class_mismatch {
            let back_edge = match back_edge {
                Some(Some(class)) => class.to_string(),
                Some(None) => "unknown (no retained object class)".into(),
                None => "local is not bound".into(),
            };
            message.push_str(&format!(
                "\npointer local `{name}`: loop-head object class: {head}; back-edge object class: {back_edge}"
            ));
        }
        Err(message)
    }
}

/// The parts of one program loop the loop rule reads, borrowed from it.
#[derive(Clone, Copy)]
pub(super) struct LoopExecutionView<'a> {
    pub(super) entry_guard: Option<&'a ProgramExpression>,
    pub(super) invariant: &'a [Proposition],
    pub(super) invariant_checks: &'a [LoopInvariantCheck],
    pub(super) effect_checks: &'a [LoopEffectCheck],
    pub(super) resource_specs: &'a [ResourceSpec],
    pub(super) ranking_measures: &'a [RankingComponent],
    pub(super) structural_measure: Option<&'a str>,
    pub(super) body: &'a ProgramStatement,
    pub(super) update: Option<&'a ProgramStatement>,
    pub(super) test: &'a LoopTestRegion,
    pub(super) backedge_target: Option<ControlTargetId>,
    pub(super) natural_exit_target: Option<ControlTargetId>,
}

impl<'a> LoopExecutionView<'a> {
    /// The loop a program statement states, or `None` for any other statement.
    pub(super) fn of(statement: &'a ProgramStatement) -> Option<Self> {
        let ProgramStatement::Loop {
            test: loop_test,
            update,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure,
            body,
            backedge_target,
            natural_exit_target,
        } = statement
        else {
            return None;
        };
        let condition = loop_test.entry_condition();
        let test = loop_test;
        Some(Self {
            test,
            update: update.as_deref(),
            entry_guard: condition,
            invariant,
            invariant_checks,
            effect_checks,
            resource_specs,
            ranking_measures,
            structural_measure: structural_measure.as_deref(),
            body,
            backedge_target: *backedge_target,
            natural_exit_target: *natural_exit_target,
        })
    }
}

#[allow(clippy::too_many_arguments)]
pub(super) fn execute_program_loop_exit_paths_with_proven_phases(
    state: &ExecutionState,
    program_loop: LoopExecutionView<'_>,
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    initialization_proven: bool,
    preservation_proven: bool,
    final_exit_candidates: &[LoopFinalExitCandidate],
    early_exits: &[LoopEarlyExit],
    return_exits: &[LoopReturnExit],
    back_edges: &[super::api::LoopBackEdges],
    otherwise: Option<&mut LoopOtherwiseProof<'_>>,
    exit_fact_scope: Option<&LoopExitFactScope<'_>>,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    execute_program_loop_exit_paths(
        state,
        program_loop,
        assumptions,
        execution_context.environment,
        (!preservation_proven).then_some(execution_context.environment),
        final_exit_candidates,
        early_exits,
        return_exits,
        back_edges,
        otherwise,
        exit_fact_scope,
        execution_context.semantics,
        initialization_proven,
        budget,
        variables,
    )
}

/// The disjunction of what each short-circuit guard path states on its own.
///
/// One entry per path, holding only the facts that path added. A conjunct an
/// earlier disjunct contradicts (an earlier path states the same exact
/// condition with the other truth value) is dropped, which only weakens that disjunct
/// and so keeps the disjunction true, turning `!a | (a & !b)` into the
/// `!a | !b` a proof can name. A path that states nothing of its own makes the
/// whole disjunction vacuous, so there is nothing to export.
///
/// The disjuncts come out in short-circuit evaluation order, which is a stable
/// sort of the paths by how many facts each states: the path that decided the
/// guard on an earlier operand states fewer of them, and ties keep the order
/// the paths were enumerated in. The kernel enumerates a disjunctive guard's
/// entry paths with the operand-false one first, so `a || b` would otherwise
/// read `(a == 0 and b != 0) or a != 0` instead of the `a != 0 or b != 0` a
/// proof writes. Narrowing runs after the sort, so it drops the conjunct the
/// short-circuit path refutes rather than the other way round. Both the entry
/// join and the exit join come through here, so they agree on the spelling.
pub(super) fn guard_path_disjunction(own_facts: &[Vec<Proposition>]) -> Option<Proposition> {
    if own_facts.len() <= 1 {
        return None;
    }
    // A fact that holds by the read-over-write authority alone (a store's
    // value read back in the path that stored it) states nothing the exit
    // can use, and the path's read has no spelling there, so it is neither
    // a disjunct's conjunct nor counted in the order below.
    let own_facts = own_facts
        .iter()
        .map(|own| {
            own.iter()
                .filter(|fact| !crate::kernel::eval::holds_by_read_over_write(fact))
                .cloned()
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let mut ordered = own_facts.iter().collect::<Vec<_>>();
    ordered.sort_by_key(|own| own.len());
    let mut disjuncts = Vec::new();
    // What the earlier paths state, keyed so that "some earlier path states
    // the negation of this fact" is one lookup. Asking every earlier fact of
    // every earlier path instead compared each pair of paths, fact by fact:
    // a hundred exits of a long loop body spent most of the join here.
    let mut earlier: std::collections::HashSet<(&OldConditionTerm, bool)> =
        std::collections::HashSet::new();
    for own in &ordered {
        crate::instrumentation::record_deterministic_work(own.len());
        let narrowed = own
            .iter()
            .filter(|fact| match fact {
                Proposition::ConditionIs(condition, value) => {
                    !earlier.contains(&(condition.old_form(), !*value))
                }
                _ => true,
            })
            .collect::<Vec<_>>();
        for fact in own.iter() {
            if let Proposition::ConditionIs(condition, value) = fact {
                earlier.insert((condition.old_form(), *value));
            }
        }
        let mut own = if narrowed.is_empty() {
            own.iter().collect::<Vec<_>>().into_iter()
        } else {
            narrowed.into_iter()
        };
        let first = own.next()?;
        disjuncts.push(own.fold(first.clone(), |left, right| {
            Proposition::And(Box::new(left), Box::new(right.clone()))
        }));
    }
    let mut disjunction = disjuncts.pop()?;
    while let Some(disjunct) = disjuncts.pop() {
        disjunction = Proposition::Or(Box::new(disjunct), Box::new(disjunction));
    }
    Some(disjunction)
}

#[derive(Clone, Copy, PartialEq, Eq)]
enum LoopExitFactsMode {
    Legacy,
    Common,
    Otherwise,
}

/// Joins the exit paths of one loop guard into the single exit the loop rule
/// certifies.
///
/// A short-circuit guard such as `while (a && b)` leaves the loop by one path
/// per conjunct: `!a`, or `a && !b`. They reach the same exit state — the
/// loop's top state, with the invariants holding and the body's effects
/// summarized — and differ only in what the failed guard says. Dropping any of
/// them would export an exit the C never reaches that way (the hole S1
/// closed), and keeping them as separate statement successors is what the
/// `loop` tactic refused. So the rule exports their join instead: every fact
/// all the paths state, in the order the first path stated them, followed by
/// the disjunction of what each path states alone. A proof after the loop
/// reasons from the disjunction by cases.
///
/// Obligations are the union: an obligation any exit path owes is owed by the
/// join, which can only refuse more, never less. Keep deterministic fact
/// order; invariant source correspondence is retained separately by clause
/// index and never inferred from this ordering.
fn join_loop_exit_paths(
    mut exits: Vec<LoopExitFacts>,
    mode: LoopExitFactsMode,
) -> Option<(
    ExecutionFacts,
    Vec<ProofObligation>,
    CheckedBorrowCallEvidenceSequence,
)> {
    if exits.len() <= 1 {
        let exit = exits.pop()?;
        return Some((exit.stated, exit.obligations, exit.borrow_evidence));
    }
    let (first_facts, first_obligations) = (exits[0].stated.clone(), exits[0].obligations.clone());
    let borrow_evidence = exits[1..]
        .iter()
        .fold(exits[0].borrow_evidence.clone(), |sequence, exit| {
            concat_checked_borrow_evidence(&sequence, &exit.borrow_evidence)
        });
    // Each exit's facts are indexed once and the first exit's are looked up
    // in every index, so the common prefix costs the exits' facts and a
    // logarithmic lookup each, not every fact against every other exit's.
    crate::instrumentation::record_deterministic_work(
        exits
            .iter()
            .map(|exit| exit.stated.len() + exit.disjunct.len())
            .sum(),
    );
    let mut obligations = first_obligations;
    for exit in exits.iter().skip(1) {
        for obligation in &exit.obligations {
            if !obligations.contains(obligation) {
                obligations.push(obligation.clone());
            }
        }
    }
    if mode == LoopExitFactsMode::Common {
        // Include both the stated fact and its verified restatement. An exit
        // that already uses the successor's name need not restate its fact.
        fn entries(exit: &LoopExitFacts) -> impl Iterator<Item = &Proposition> {
            exit.stated
                .iter()
                .map(ExecutionPureFact::proposition)
                .chain(exit.restated.iter())
        }
        #[derive(Clone, Eq, Ord, PartialEq, PartialOrd)]
        enum Identity<'a> {
            Alpha(crate::kernel::proof::PropositionIdentityKey),
            Exact(&'a Proposition),
        }
        fn identity(proposition: &Proposition) -> Identity<'_> {
            crate::kernel::proof::proposition_identity_key(proposition)
                .map_or(Identity::Exact(proposition), Identity::Alpha)
        }
        let first = entries(&exits[0]).collect::<Vec<_>>();
        let identities = first.iter().copied().map(identity).collect::<Vec<_>>();
        let first_objects = first_facts.iter().collect::<Vec<_>>();
        let mut seen = BTreeSet::new();
        let facts = positions_in_every_set(
            identities.iter().cloned(),
            exits[1..].iter().map(|exit| entries(exit).map(identity)),
        )
        .into_iter()
        .filter(|&index| seen.insert(&identities[index]))
        .map(|index| {
            first_objects
                .get(index)
                .map(|fact| (*fact).clone())
                .unwrap_or_else(|| ExecutionPureFact::new(first[index].clone()))
        })
        .collect();
        return Some((facts, obligations, borrow_evidence));
    }

    let in_every_exit = positions_in_every_set(
        first_facts.iter().map(ExecutionPureFact::proposition),
        exits[1..]
            .iter()
            .map(|exit| exit.stated.iter().map(ExecutionPureFact::proposition)),
    );
    let shared = in_every_exit
        .into_iter()
        .map(|position| first_facts[position].clone())
        .collect::<Vec<_>>();
    let shared_propositions = shared
        .iter()
        .map(ExecutionPureFact::proposition)
        .collect::<BTreeSet<_>>();
    let own_facts = exits
        .iter()
        .map(|exit| {
            // A closed true conjunct, such as a guard lowering decided,
            // says nothing about the path. Counting it would reorder the
            // disjuncts below and change what narrowing drops.
            exit.disjunct
                .iter()
                .filter(|proposition| {
                    !shared_propositions.contains(proposition)
                        // Composition certificates establish a well-formed
                        // resource context, not an observable exit guard.
                        // Dropping this conjunct weakens the path disjunction
                        // and keeps its pure successor facts spellable.
                        && !matches!(proposition, Proposition::ResourceComposition(_))
                        && proposition.literal_condition().is_none_or(|(actual, expected)| actual != expected)
                })
                .cloned()
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    drop(shared_propositions);
    // Short-circuit paths refine one another: the second conjunct's exit also
    // states the first conjunct true, which the first exit states false. A
    // conjunct another disjunct contradicts is dropped, which only weakens
    // that disjunct and so keeps the disjunction true, and turns
    // `!a | (a & !b)` into the `!a | !b` a proof can name.
    let mut facts = shared;
    facts.extend(facts_every_exit_restates(&exits, &facts));
    // A synthesized summary can help check an explicit otherwise proof.
    // Such facts never become implicit exports under the common-facts rule.
    let summarize = if mode == LoopExitFactsMode::Otherwise {
        ExecutionPureFact::internal
    } else {
        ExecutionPureFact::new
    };
    let historical_disjunction = guard_path_disjunction(&own_facts);
    if let Some(disjunction) = &historical_disjunction {
        facts.push(summarize(disjunction.clone()));
    }
    // Pinning equations describe only the successor's abstracted components.
    // Keep their weaker disjunction independently of historical path guards:
    // a guard can mention an iteration value no successor state names.
    let successor_equations = exits
        .iter()
        .map(|exit| exit.successor_equations.clone())
        .collect::<Vec<_>>();
    if let Some(disjunction) = guard_path_disjunction(&successor_equations)
        && historical_disjunction.as_ref() != Some(&disjunction)
    {
        facts.push(summarize(disjunction));
    }
    Some((facts.into(), obligations, borrow_evidence))
}

/// The facts every exit states about the successor's merged binder names.
///
/// Where the exits hold a binder at different values, the join gives the
/// successor one fresh name for it, and each exit's [`LoopExitFacts::restated`]
/// is that exit's own facts with its value for the binder replaced by that
/// name. On each exit path the fresh name equals the exit's value (that is
/// the equation the exit contributes to the disjunction), so a restated fact
/// holds on the path that stated the original. A proposition that every exit
/// restates identically therefore holds on every path into the successor,
/// and is kept as an ordinary fact. Nothing is kept that some exit did not
/// state: an exit that restates nothing empties the result.
///
/// Identity is of kernel propositions, so two exits that spell a fact with
/// the same words about different symbols (an arm binding of each exit's own
/// arm, say) do not agree, and a name only one exit has cannot survive.
///
/// Nothing is searched or re-proved: each kept fact was checked where its
/// exit stated it. Each exit's restated facts are indexed once and the first
/// exit's are looked up in each index, so the work is the restated facts
/// times a logarithmic lookup, not exits squared.
fn facts_every_exit_restates(
    exits: &[LoopExitFacts],
    already_shared: &(impl ExecutionFactSource + ?Sized),
) -> ExecutionFacts {
    let Some((first, others)) = exits.split_first() else {
        return Vec::new().into();
    };
    if first.restated.is_empty() || others.iter().any(|exit| exit.restated.is_empty()) {
        return Vec::new().into();
    }
    crate::instrumentation::record_deterministic_work(
        exits.iter().map(|exit| exit.restated.len()).sum(),
    );
    let shared = already_shared
        .fact_iter()
        .map(ExecutionPureFact::proposition)
        .collect::<BTreeSet<_>>();
    let mut kept = BTreeSet::new();
    positions_in_every_set(
        first.restated.iter(),
        others.iter().map(|exit| exit.restated.iter()),
    )
    .into_iter()
    .map(|position| &first.restated[position])
    .filter(|proposition| !shared.contains(proposition) && kept.insert(*proposition))
    .map(|proposition| ExecutionPureFact::new(proposition.clone()))
    .collect()
}

/// The positions of the `first` items that every one of `others` also holds,
/// in `first`'s order.
///
/// Each of `others` is indexed once and each `first` item is looked up in
/// the indexes until one lacks it, so the comparisons are the items times a
/// logarithm of one set's size. Nothing compares one exit's facts with every
/// other exit's.
fn positions_in_every_set<T: Ord>(
    first: impl Iterator<Item = T>,
    others: impl Iterator<Item = impl Iterator<Item = T>>,
) -> Vec<usize> {
    let indexes = others
        .map(|items| items.collect::<BTreeSet<_>>())
        .collect::<Vec<_>>();
    first
        .enumerate()
        .filter(|(_, item)| indexes.iter().all(|index| index.contains(item)))
        .map(|(position, _)| position)
        .collect()
}

/// One exit's contribution to a loop's join.
///
/// `stated` is what that path actually holds, and the join's common prefix is
/// the intersection of those. These facts keep the symbolic names under
/// which they were established; they are not necessarily exit invariants.
/// `disjunct` is the same path restated about the successor the join builds:
/// with no abstraction it is exactly `stated`, and when a component was
/// abstracted it is that path's own description of the fresh names instead of
/// names the loop left behind.
struct LoopExitFacts {
    stated: ExecutionFacts,
    disjunct: Vec<Proposition>,
    /// The stated facts that mention this exit's value for a binder the join
    /// renamed, with that value replaced by the successor's name; see
    /// [`facts_every_exit_restates`].
    restated: Vec<Proposition>,
    /// Nonvacuous pinning equations, with no historical path conditions.
    successor_equations: Vec<Proposition>,
    obligations: Vec<ProofObligation>,
    borrow_evidence: CheckedBorrowCallEvidenceSequence,
}

impl LoopExitFacts {
    /// An exit whose state the join did not have to abstract: it describes the
    /// successor in the names it already used.
    fn unabstracted(
        facts: ExecutionFacts,
        obligations: Vec<ProofObligation>,
        borrow_evidence: CheckedBorrowCallEvidenceSequence,
    ) -> Self {
        Self {
            disjunct: facts
                .iter()
                .map(|fact| fact.proposition().clone())
                .collect(),
            stated: facts,
            restated: Vec::new(),
            successor_equations: Vec::new(),
            obligations,
            borrow_evidence,
        }
    }
}

/// Joins every way out of one loop into the single successor path the
/// enclosing frontier continues from.
///
/// The guard-false exits stand at the loop's head state; a `break` exit
/// stands where that path left the body. A loop has one successor, so the
/// exits that reach one state are joined by [`join_loop_exit_paths`], which
/// keeps what every exit states and disjoins what each states alone.
///
/// Exits that reach *different* states are described the way the loop head
/// describes an arbitrary visit (D5), by
/// [`abstract_loop_exit_states`]: the loop's declared binders are rebound at
/// each exit by family and argument equality, whatever the body called them;
/// every component the exits disagree about — a binder's model, a local, a
/// cell one exit wrote differently — becomes one fresh name; and each exit
/// contributes, as its own disjunct, the equations pinning those fresh names
/// to what that exit actually reached. Each disjunct is exactly what its path
/// established about the successor, so the join is the standard weakening and
/// nothing is assumed of an exit that did not state it. A component no binder
/// can describe is still refused by name; dropping an exit, or picking one
/// exit's state for all of them, would export an exit the C never reaches
/// that way.
#[allow(clippy::too_many_arguments)]
fn join_loop_exits(
    head: &LoopHead,
    body: &ProgramStatement,
    invariant_propositions: &crate::kernel::proof::PersistentSequence<Proposition>,
    binders: &[LoopBinder],
    exits: Vec<(
        ExecutionState,
        ExecutionFacts,
        Vec<ProofObligation>,
        CheckedBorrowCallEvidenceSequence,
        Option<PureFactContext>,
    )>,
    assumptions: &PureFactContext,
    exit_fact_scope: Option<&LoopExitFactScope<'_>>,
    mode: LoopExitFactsMode,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Option<StatementExecutionPath> {
    let exit_state = exits.first()?.0.clone();
    let states = exits
        .iter()
        .map(|(state, _, _, _, _)| state)
        .collect::<Vec<_>>();
    let unchanged = || vec![LoopExitRestatement::default(); exits.len()];
    let invariant_state_unchanged = states[1..].iter().all(|other| **other == exit_state);
    let mut join_requirements = Vec::new();
    let (mut exit_state, restatements, mismatch) = if invariant_state_unchanged {
        (exit_state, unchanged(), None)
    } else {
        let facts = exits
            .iter()
            .map(|(_, facts, _, _, _)| facts)
            .collect::<Vec<_>>();
        let contexts = exits
            .iter()
            .map(|(_, _, _, _, context)| context.clone())
            .collect::<Vec<_>>();
        match abstract_loop_exit_states(
            head,
            body,
            binders,
            &states,
            &facts,
            &contexts,
            assumptions,
            &mut join_requirements,
            variables,
            budget,
        ) {
            Ok((state, restatements)) => (state, restatements, None),
            Err(mismatch) => (exit_state, unchanged(), Some(mismatch)),
        }
    };
    if mismatch.is_none() {
        exit_state.join_loop_exit_program_points(&states);
    }
    let source_exits = exit_fact_scope.map(|_| {
        exits
            .iter()
            .map(|(state, facts, _, _, _)| (state.clone(), facts.clone()))
            .collect::<Vec<_>>()
    });
    let (mut facts, mut obligations, borrow_evidence) = join_loop_exit_paths(
        exits
            .into_iter()
            .zip(restatements)
            .map(
                |((_, facts, obligations, borrow_evidence, _), restatement)| {
                    restatement.restate(
                        facts,
                        obligations,
                        borrow_evidence,
                        mode == LoopExitFactsMode::Common,
                    )
                },
            )
            .collect(),
        mode,
    )?;
    if let Some((scope, source_exits)) = exit_fact_scope.zip(source_exits) {
        let (admitted, written_exports) =
            scope(&exit_state, &head.iterations, &source_exits, &facts);
        facts = facts
            .into_iter()
            .zip(admitted)
            .filter_map(|(fact, visible)| visible.then_some(fact))
            .chain(written_exports.into_iter().map(ExecutionPureFact::new))
            .collect();
    }
    if let Some(mismatch) = mismatch {
        obligations.push(
            ProofObligation::verification_condition(false_equals_true_proposition())
                .with_context(format!(
                    "loop exits reach different states, so they have no common successor: {mismatch}"
                )),
        );
    } else {
        obligations.extend(join_requirements);
    }
    // Only name invariants whose source still denotes this successor. A
    // changed-state break can leave old head facts in the intersection; those
    // facts must not acquire spellings about fresh exit values.
    let loop_invariant_correspondence = if invariant_state_unchanged {
        retained_loop_invariant_correspondence(invariant_propositions, &facts)
    } else {
        Default::default()
    };
    Some(StatementExecutionPath {
        loop_invariant_correspondence,
        call_result: None,
        outcome: StatementOutcome::Normal(Box::new(exit_state)),
        facts,
        obligations,
        borrow_evidence,
    })
}

/// Associate only this producer's surviving facts with the original clause
/// indices. Semantic duplicates retain each index; guard and lowering side
/// facts never consume a clause slot. Work is confined to the output delta.
fn retained_loop_invariant_correspondence(
    declarations: &crate::kernel::proof::PersistentSequence<Proposition>,
    facts: &(impl ExecutionFactSource + ?Sized),
) -> LoopInvariantCorrespondence {
    if declarations.is_empty() {
        return Default::default();
    }
    let correspondence = retained_loop_invariant_declarations(
        declarations.iter(),
        facts.fact_iter().map(ExecutionPureFact::proposition),
    )
    .into_iter()
    .map(|(index, proposition)| (index, proposition.clone()))
    .collect::<Vec<_>>();
    LoopInvariantCorrespondence {
        invariants: (!correspondence.is_empty()).then(|| correspondence.into()),
        iterations: None,
    }
}

fn retained_loop_invariant_declarations<'a, T: Ord + 'a>(
    declarations: impl Iterator<Item = &'a T>,
    facts: impl Iterator<Item = &'a T>,
) -> Vec<(usize, &'a T)> {
    let emitted = facts.collect::<BTreeSet<_>>();
    declarations
        .enumerate()
        .filter(|(_, proposition)| emitted.contains(proposition))
        .collect()
}

#[cfg(test)]
mod loop_exit_resource_agreement_tests;

#[cfg(test)]
mod loop_exit_shared_fact_tests;

#[cfg(test)]
mod loop_invariant_correspondence_tests;

/// The one post-loop state several exits join into, and the equations each
/// exit owes about it.
///
/// This is decision D5 applied at the exits, exactly as the loop head and the
/// back edge apply it. Every exit first rebinds the loop's declared binders by
/// family and argument equality, so a body that refolded its instance under
/// another name still hands the loop back the resource the header declared.
/// Then, component by component, the exits' agreement is kept and their
/// disagreement is replaced by a fresh symbolic name:
///
/// - a declared binder's arguments and fields (the loop head havocs the same
///   fields, for the same reason: an exit's model is whatever its own path
///   established, and the successor holds only the disjunction of those);
/// - the locals the exits disagree on, with the local's stack cell resynced;
/// - a memory cell the exits wrote differently, which is a cell folded into a
///   declared binder — the loop body owns nothing else — and which a proof
///   after the loop therefore reads back through that binder's model.
///
/// The returned restatement is per exit: it pins every fresh name to the value
/// that exit reached, so the caller's disjunction says exactly "the successor
/// is what one of these exits reached" and never more, and it renames the
/// exit's own bare symbolic values to those fresh names so the disjunct speaks
/// about the successor rather than about a value the loop left behind.
///
/// Refusals are named, never silent: an exit that holds no instance for a
/// declared binder, a cell the exits disagree about when the loop declares no
/// binder to describe it, and any disagreement outside these components
/// (allocation lifetimes, block shapes, ownership beyond the binders) refuse
/// with the component that differs.
///
/// Cost is the loop's own binders, the locals the exits disagree on, and the
/// cells they disagree on; no unrelated project-wide or path-wide state is
/// scanned, and a component every exit agrees on is compared once and kept.
#[allow(clippy::too_many_arguments)]
fn abstract_loop_exit_states(
    head: &LoopHead,
    body: &ProgramStatement,
    binders: &[LoopBinder],
    states: &[&ExecutionState],
    exit_facts: &[&ExecutionFacts],
    retained_contexts: &[Option<PureFactContext>],
    assumptions: &PureFactContext,
    join_requirements: &mut Vec<ProofObligation>,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<(ExecutionState, Vec<LoopExitRestatement>), String> {
    // This join already restates and exports each exit's facts. Index that
    // explicit input once per exit, shared by all binder equality checks;
    // never rebuild the path context for each binder or argument.
    let contexts = loop_exit_argument_contexts(
        exit_facts,
        retained_contexts,
        assumptions,
        !binders.is_empty(),
    );
    let mut rebound = Vec::with_capacity(states.len());
    for (index, state) in states.iter().enumerate() {
        match loop_state_with_loop_binders_rebound(
            &head.top,
            state,
            binders,
            contexts.get(index).unwrap_or(assumptions),
        ) {
            Ok(state) => rebound.push(state),
            Err(failure) => {
                return Err(format!("at loop exit {}, {failure}", index + 1));
            }
        }
    }
    discard_loop_exit_partial_value_bindings(&head.top, body, &mut rebound);
    retain_proven_loop_exit_cells(
        &mut rebound,
        exit_facts,
        &contexts,
        assumptions,
        binders.is_empty(),
    )?;
    let mut successor = rebound[0].clone();
    let mut restatements = vec![LoopExitRestatement::default(); rebound.len()];
    // Every binding shared by all exits already has its joined value and
    // initialization in the successor. Keep the changed names in binding
    // order so the fresh variables and their equations keep that order.
    let changed_locals = rebound[1..]
        .iter()
        .flat_map(|state| successor.locals.differing_names(&state.locals))
        .cloned()
        .collect::<BTreeSet<_>>();
    let uninitialized =
        abstract_loop_exit_initialization(&mut successor, &rebound, &changed_locals);
    let locals = abstract_loop_exit_locals(
        &mut successor,
        &rebound,
        changed_locals,
        &mut restatements,
        variables,
        budget,
    )?;
    abstract_loop_exit_binders(
        &mut successor,
        &rebound,
        binders,
        &contexts,
        &mut restatements,
        variables,
        budget,
    )?;
    let resynced = locals
        .iter()
        .filter_map(|(name, _)| successor.locals.slot(name).cloned())
        .collect::<BTreeSet<_>>();
    // A cell the exits wrote differently is described through a binder's
    // model, so a cell the loop declared as plain memory of its own has no
    // such description. Those ranges are what the head handed the body
    // besides its binders.
    let declared_memory = if binders.is_empty() {
        Vec::new()
    } else {
        loop_declared_memory_ranges(&head.body)
    };
    let cells = abstract_loop_exit_memory(
        &mut successor,
        &rebound,
        &resynced,
        binders.is_empty(),
        &declared_memory,
        assumptions,
        &contexts,
        &mut restatements,
        join_requirements,
        variables,
        budget,
    )?;
    let bookkeeping =
        join_loop_exit_storage_bookkeeping(&mut successor, &rebound, variables, budget)?;
    // Everything the rule knows how to describe has now been made common. A
    // state that still differs differs in something this rule does not model,
    // so it is refused under its own name rather than abstracted blindly.
    let abstracted = LoopExitAbstraction {
        locals: &locals,
        uninitialized: &uninitialized,
        cells: &cells,
        bookkeeping,
    };
    if let Some(mismatch) = rebound.iter().find_map(|state| {
        loop_exit_residual_difference(&successor, state, &abstracted, binders, assumptions)
    }) {
        return Err(mismatch);
    }
    Ok((successor, restatements))
}

fn loop_exit_argument_contexts(
    facts: &[&ExecutionFacts],
    retained_contexts: &[Option<PureFactContext>],
    assumptions: &PureFactContext,
    has_binders: bool,
) -> Vec<PureFactContext> {
    if !has_binders {
        return Vec::new();
    }
    facts
        .iter()
        .enumerate()
        .map(|(index, facts)| {
            if let Some(Some(context)) = retained_contexts.get(index) {
                let mut retained = context.clone();
                for change in context
                    .execution_fact_projection
                    .diff(&assumptions.execution_fact_projection)
                {
                    crate::instrumentation::record_deterministic_work(1);
                    // The exit is later than the incoming context. Preserve
                    // its recorded truth when both name the same condition.
                    if let imbl::ordmap::DiffItem::Add(_, fact) = change {
                        retained = retained.assume_execution_pure_fact(fact);
                    }
                }
                // The compositions the incoming context states and the exit
                // does not: a walk of the two sets' difference, not of every
                // composition the path stated.
                for (composition, in_exit) in context
                    .resource_compositions
                    .diff(&assumptions.resource_compositions)
                {
                    if !in_exit && !retained.resource_compositions.contains(composition) {
                        retained = retained.assume_proposition(Proposition::ResourceComposition(
                            composition.clone(),
                        ));
                    }
                }
                return retained;
            }
            crate::instrumentation::record_deterministic_work(facts.len());
            assumptions_with_path_context(assumptions, *facts, &[])
        })
        .collect()
}

/// Fill only changed concrete cache entries whose exact typed value every
/// exit already proves. A load equation is evidence for a cache entry, never
/// for a C store, initialization, or additional memory authority.
///
/// `built` holds the exit contexts the join already indexed for its binders
/// (empty when the loop has none); an exit's context is built here only when
/// it is missing, so no exit's facts are assumed twice.
fn retain_proven_loop_exit_cells(
    states: &mut [ExecutionState],
    facts: &[&ExecutionFacts],
    built: &[PureFactContext],
    assumptions: &PureFactContext,
    no_binders: bool,
) -> Result<(), String> {
    let candidates = states
        .iter()
        .skip(1)
        .flat_map(|state| {
            states[0]
                .memory
                .cells
                .differing_cells(&state.memory.cells)
                .pointers
        })
        .collect::<BTreeSet<_>>();
    let mut contexts = (0..states.len()).map(|_| None).collect::<Vec<_>>();
    for pointer in candidates {
        let Some(value) = states
            .iter()
            .find_map(|state| state.memory.known_value(&pointer))
        else {
            continue;
        };
        // Numerical floating equality does not establish equal stored bits
        // (the signs of zero differ). Boolean reads normalize their byte.
        if matches!(
            value,
            ProgramValue::Bool(_) | ProgramValue::Float32(_) | ProgramValue::Float64(_)
        ) {
            continue;
        }
        let mut agrees = true;
        for (index, state) in states.iter().enumerate() {
            crate::instrumentation::record_deterministic_work(1);
            if let Some(held) = state.memory.known_value(&pointer) {
                agrees &= held == value;
                continue;
            }
            let Some(load) =
                cached_symbolic_storage_cell_value(state.memory(), &pointer, value.program_type())
            else {
                agrees = false;
                continue;
            };
            let context = match built.get(index) {
                Some(context) => context,
                None => contexts[index].get_or_insert_with(|| {
                    assumptions_with_path_context(assumptions, facts[index], &[])
                }),
            };
            let equality = indexed_loop_exit_load_equality(context, &load, &value);
            if equality != Some(true) {
                agrees = false;
                if no_binders && equality == Some(false) {
                    return Err(format!(
                        "the cell in `{}` that the exits write differently is owned by no loop binder",
                        pointer.base
                    ));
                }
            }
        }
        if agrees {
            for state in states.iter_mut() {
                let memory = state
                    .memory()
                    .clone()
                    .materialize_named_cell(pointer.clone(), value.clone());
                *state = state.clone().with_memory(memory);
            }
        }
    }
    Ok(())
}

/// An optional cache reconciliation must not ask the general memory resolver
/// to prove anything. Consult only exact fact indexes and the trusted graph.
fn indexed_loop_exit_load_equality(
    context: &PureFactContext,
    load: &ProgramValue,
    value: &ProgramValue,
) -> Option<bool> {
    let Proposition::ConditionIs(condition, expected) =
        program_value_comparison_proposition(load, ComparisonOperator::Equal, value)?
    else {
        return None;
    };
    if let Some(answer) = context.exact_condition_value(condition.old_form()) {
        return Some(answer == expected);
    }
    match condition.old_form() {
        OldConditionTerm::Compare {
            format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
            relation: CompareRelation::Equal,
            left,
            right,
        } if expected => {
            if context.int32_values_known_equal(left, right) {
                return Some(true);
            }
            let constant = |term: &OldMachineTerm| {
                term.as_const().or_else(|| {
                    context
                        .equality_graph
                        .exact_literal_sources(term)?
                        .keys()
                        .find_map(|condition| {
                            crate::instrumentation::record_deterministic_work(1);
                            let OldConditionTerm::Compare {
                                format: MachineIntegerType::Int32 | MachineIntegerType::UInt32,
                                relation: CompareRelation::Equal,
                                left: a,
                                right: b,
                            } = condition
                            else {
                                return None;
                            };
                            if a.as_ref() == term {
                                b.as_const()
                            } else if b.as_ref() == term {
                                a.as_const()
                            } else {
                                None
                            }
                        })
                })
            };
            Some(constant(left)? == constant(right)?)
        }
        OldConditionTerm::AddressEqual(left, right) if expected => {
            context.pointers_known_equal(left, right).then_some(true)
        }
        _ => None,
    }
}

fn is_loop_exit_state_marker(block: &AddressBase) -> bool {
    block.is_havoc_block() || block.is_call_havoc_block() || block.starts_with("call-write-set:")
}

#[cfg(test)]
mod contract_exit_join_tests;

/// What one loop exit owes about the successor the join exports.
///
/// `equations` pin the successor's fresh names to the values this exit
/// reached. `renamings` say which bare symbolic value this exit held for a
/// name the successor now calls something else: a guard-false exit stands at
/// the loop head, where every local the body writes is one fresh variable, so
/// `i <= 0` there is a fact about a variable that no longer names anything
/// after the loop. Rewriting this exit's own facts through its own equation is
/// the weakening that turns such a fact into one about the local a proof after
/// the loop can name, and it is valid exactly because the equation holds on
/// this path — which is why it is applied only to this exit's disjunct.
#[derive(Clone, Debug, Default)]
struct LoopExitRestatement {
    equations: Vec<Proposition>,
    renamings: Vec<(Variable, OldMachineTerm)>,
    /// For each binder argument or field of algebraic sort that the join
    /// renamed: the term this exit held there, and the successor's name.
    /// The held value is a term, not only a symbol: one exit may hold the
    /// head's own model variable and another a constructor it folded.
    replacements: Vec<(AlgebraicTerm, AlgebraicTerm)>,
    /// The first successor name for a selected symbolic resource value.
    /// Further fields holding that same value pin to this name directly,
    /// without exporting the private exit variable or walking other pins.
    symbolic_resource_pins: BTreeMap<Variable, AlgebraicTerm>,
}

impl LoopExitRestatement {
    /// Records that this exit's `held` value became the successor's `fresh`
    /// one.
    fn pin(&mut self, fresh: &ProgramValue, held: &ProgramValue) {
        // The C comparison form, not a raw term equality: a proof after the
        // loop spells this disjunct as `x == <value>`, and `cases` needs the
        // exported fact to be exactly what that spelling lowers to.
        self.equations.push(
            program_value_comparison_proposition(fresh, ComparisonOperator::Equal, held)
                .unwrap_or_else(|| {
                    Proposition::Equal(
                        Term::ProgramValue(fresh.clone().into()),
                        Term::ProgramValue(held.clone().into()),
                    )
                }),
        );
        if let (Some(OldMachineTerm::Variable(from)), Some(to)) =
            (scalar_bitvector(held), scalar_bitvector(fresh))
        {
            self.renamings.push((*from, to.clone()));
        }
    }

    /// Records that this exit's `held` resource argument or field became the
    /// successor's `fresh` one.
    fn pin_resource_value(&mut self, fresh: &AlgebraicValue, held: &AlgebraicValue) {
        if let (AlgebraicValue::Program(fresh), AlgebraicValue::Program(held)) = (fresh, held) {
            self.pin(fresh, held);
            return;
        }
        if let (AlgebraicValue::Algebraic(fresh), AlgebraicValue::Algebraic(held)) = (fresh, held) {
            self.replacements.push((held.clone(), fresh.clone()));
            if let AlgebraicTermNode::Variable(variable) = held.node {
                let representative = self
                    .symbolic_resource_pins
                    .entry(variable)
                    .or_insert_with(|| fresh.clone());
                if representative != fresh {
                    self.equations.push(Proposition::Equal(
                        Term::Algebraic(fresh.clone().into()),
                        Term::Algebraic(representative.clone().into()),
                    ));
                }
                return;
            }
        }
        self.equations.push(Proposition::Equal(
            resource_value_term(fresh),
            resource_value_term(held),
        ));
    }

    /// One stated fact with this exit's value for each renamed binder
    /// replaced by the successor's name, or `None` when the fact mentions no
    /// such value. Every occurrence is replaced, which is the one choice that
    /// lets two exits arrive at the same proposition; the result holds on
    /// this path because the name equals the value here.
    fn restated_about_merged_binders(
        &self,
        proposition: &Proposition,
        symbolic_only: bool,
        common_only: bool,
    ) -> Option<Proposition> {
        let mut restated = None;
        for (held, fresh) in &self.replacements {
            // A constructor can already be spelled after the loop. Replacing
            // it would also rename historical equalities to that constructor
            // and change exact `cases` interfaces that need no fresh name.
            if symbolic_only && !matches!(held.node, AlgebraicTermNode::Variable(_)) {
                continue;
            }
            let current = restated.as_ref().unwrap_or(proposition);
            let mut rewrite = crate::kernel::proof::term_rewrite::TermRewrite::new(held, fresh);
            // A written export can be a disjunction or quantify a model.
            // Use the capture-avoiding walk through the entire proposition.
            let rewritten = if common_only {
                rewrite.substitute_proposition(current)
            } else {
                rewrite.proposition(current)
            };
            // A refused walk hands back a placeholder, not a rewritten fact.
            if rewrite.refusal().is_some() {
                return None;
            }
            if rewrite.changed {
                restated = Some(rewritten);
            }
        }
        restated
    }

    /// This exit's contribution to the join: what it states, and the same
    /// path restated about the successor's fresh names for its disjunct.
    ///
    /// Keep the original facts available for the intersection across exits.
    /// For the disjunct, use the successor's scalar names where they replace
    /// exit-only names. Effect summaries keep the states and ranges of the
    /// transitions that established them.
    fn restate(
        self,
        facts: ExecutionFacts,
        obligations: Vec<ProofObligation>,
        borrow_evidence: CheckedBorrowCallEvidenceSequence,
        common_only: bool,
    ) -> LoopExitFacts {
        if self.renamings.is_empty() && self.equations.is_empty() && self.replacements.is_empty() {
            return LoopExitFacts::unabstracted(facts, obligations, borrow_evidence);
        }
        let rename = |proposition: &Proposition| {
            self.renamings
                .iter()
                .fold(proposition.clone(), |proposition, (from, to)| {
                    crate::kernel::reasoning::restate_loop_exit_scalar(&proposition, *from, to)
                })
        };
        let mut restated = Vec::new();
        let mut disjunct = Vec::new();
        for fact in facts.iter() {
            let original = fact.proposition();
            if common_only {
                let algebraic = self.restated_about_merged_binders(original, false, true);
                let restatement = rename(algebraic.as_ref().unwrap_or(original));
                if &restatement != original {
                    restated.push(restatement);
                }
            } else {
                let rewritten = self.restated_about_merged_binders(original, true, false);
                disjunct.push(rename(rewritten.as_ref().unwrap_or(original)));
                if let Some(rewritten) = self.restated_about_merged_binders(original, false, false)
                {
                    restated.push(rewritten);
                }
            }
        }
        let mut successor_equations = Vec::new();
        for equation in self.equations.iter().filter(|_| !common_only) {
            // A pin reduced to a reflexive equality states nothing.
            let renamed = rename(equation);
            if equation_states_nothing(&renamed) {
                continue;
            }
            successor_equations.push(renamed.clone());
            disjunct.push(renamed);
        }
        LoopExitFacts {
            stated: facts,
            disjunct,
            restated,
            successor_equations,
            obligations,
            borrow_evidence,
        }
    }
}

/// Whether a pinning equation has become vacuous, which is what a renaming
/// that already covered it leaves behind.
fn equation_states_nothing(equation: &Proposition) -> bool {
    match equation {
        Proposition::Equal(left, right) => left == right,
        Proposition::ConditionIs(condition, value) => {
            PureFactContext::decide_intrinsically(condition.old_form()) == Some(*value)
        }
        _ => false,
    }
}

/// The scalar term a C value carries, for the one-variable renaming above.
fn scalar_bitvector(value: &ProgramValue) -> Option<&OldMachineTerm> {
    match value.numeric_value() {
        ProgramValue::PointerInteger(_) => unreachable!("numeric projection"),
        ProgramValue::Int8(term) => Some(term),
        ProgramValue::Bool(term)
        | ProgramValue::Int16(term)
        | ProgramValue::Int32(term)
        | ProgramValue::UInt8(term)
        | ProgramValue::UInt16(term)
        | ProgramValue::UInt32(term)
        | ProgramValue::Int64(term)
        | ProgramValue::UInt64(term)
        | ProgramValue::Int128(term)
        | ProgramValue::UInt128(term)
        | ProgramValue::Float32(term)
        | ProgramValue::Float64(term) => Some(term),
        ProgramValue::Void | ProgramValue::Pointer(_) | ProgramValue::Parameter(_) => None,
    }
}

/// Gives each declared loop binder the arguments and fields every exit agrees
/// on, and one fresh name wherever they disagree.
fn abstract_loop_exit_binders(
    successor: &mut ExecutionState,
    exits: &[ExecutionState],
    binders: &[LoopBinder],
    contexts: &[PureFactContext],
    restatements: &mut [LoopExitRestatement],
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<(), String> {
    for binder in binders {
        let mut instances = Vec::with_capacity(exits.len());
        for (index, state) in exits.iter().enumerate() {
            let Some(instance) = state.resources().owned_instance(binder.identity) else {
                return Err(format!(
                    "at loop exit {}, loop binder `{}` holds no instance",
                    index + 1,
                    binder.name
                ));
            };
            instances.push(instance.clone());
        }
        let base = instances[0].clone();
        if instances[1..].iter().any(|instance| {
            instance.name != base.name
                || instance.schema != base.schema
                || instance.resource_arguments() != base.resource_arguments()
        }) {
            return Err(format!(
                "the exits hold different resources for loop binder `{}`",
                binder.name
            ));
        }
        let local_arguments =
            loop_exit_local_arguments(successor, exits, binder, &instances, contexts);
        let arguments = joined_resource_values(
            &base.arguments,
            instances.iter().map(|instance| &instance.arguments),
            &local_arguments,
            restatements,
            variables,
            budget,
        )?;
        let fields = joined_resource_fields(
            &base.fields,
            instances.iter().map(|instance| &instance.fields),
            restatements,
            variables,
            budget,
        )?;
        if arguments == base.arguments && fields == base.fields {
            continue;
        }
        let Some(joined) = ResourceInstance::new_with_resource_arguments(
            binder.identity,
            base.name.clone(),
            arguments,
            base.schema.clone(),
            fields,
            base.resource_arguments().to_vec(),
        ) else {
            return Err(format!(
                "loop binder `{}` names an instance whose fields do not match its schema",
                binder.name
            ));
        };
        // Joined fields are fresh values just as call-return fields are.
        // Retain their declared names at the mint so explicit branch proofs
        // can cite the exported disjunction through this binder.
        for (field_index, ((name, _), value)) in joined
            .schema()
            .fields()
            .iter()
            .zip(joined.fields())
            .enumerate()
        {
            if base.fields().get(field_index) == Some(value) {
                continue;
            }
            if let Some(variable) = crate::kernel::model_fields::algebraic_value_variable(value) {
                crate::kernel::model_fields::register_model_field_variable(
                    variable,
                    crate::kernel::model_fields::ModelFieldOrigin {
                        identity: binder.identity,
                        field: std::sync::Arc::from(name.as_str()),
                        field_index,
                        minted_by: crate::kernel::model_fields::ModelMint::Join,
                    },
                );
            }
        }
        let Some(resources) = successor.resources().clone().without_fact_incrementally(
            &ResourceFact::own(Resource::Instance(base)),
            &PureFactContext::new(),
        ) else {
            return Err(format!(
                "loop binder `{}` could not be rebound at the loop's exit",
                binder.name
            ));
        };
        *successor = successor.clone().with_resource_context(
            resources.unchecked_with_fact(ResourceFact::own(Resource::Instance(joined))),
        );
    }
    Ok(())
}

/// A declared current-local argument must name that same local after the
/// join. Select it by its declaration, then check the correspondence on every
/// exit; equal-looking values in unrelated components are never paired.
/// Locals have already been joined, so a changed cursor supplies its one
/// fresh value to every binder that explicitly tracks it.
fn loop_exit_local_arguments(
    successor: &ExecutionState,
    exits: &[ExecutionState],
    binder: &LoopBinder,
    instances: &[ResourceInstance],
    contexts: &[PureFactContext],
) -> Vec<Option<AlgebraicValue>> {
    let Some(spec) = binder
        .spec
        .as_ref()
        .and_then(ResourceSpec::instance_resource_spec)
    else {
        return Vec::new();
    };
    let ResourceTerm::Composite {
        arguments,
        argument_state_sources,
        ..
    } = spec.term()
    else {
        return Vec::new();
    };
    arguments
        .iter()
        .enumerate()
        .map(|(position, expression)| {
            crate::instrumentation::record_deterministic_work(1);
            if argument_state_sources.get(position) != Some(&ResourceStateSource::Current) {
                return None;
            }
            // A numeric address is a pure projection of the declared local.
            // It must follow the local's joined value just as a direct index
            // does; it never transfers the pointer's provenance or bounds.
            let (name, address_only) = match expression {
                ProgramExpression::Variable(name) => (name, false),
                ProgramExpression::Cast {
                    expression,
                    target_type: ProgramType::UInt64,
                    ..
                } => {
                    let ProgramExpression::Variable(name) = expression.as_ref() else {
                        return None;
                    };
                    (name, true)
                }
                _ => return None,
            };
            let project = |value: &ProgramValue| {
                if address_only {
                    let ProgramValue::Pointer(pointer) = value else {
                        return None;
                    };
                    Some(ProgramValue::UInt64(OldMachineTerm::integer_address(
                        pointer.address().clone(),
                    )))
                } else {
                    Some(value.clone())
                }
            };
            let fresh = project(&successor.locals().get(name)?.native())?;
            for ((exit, instance), context) in exits.iter().zip(instances).zip(contexts) {
                crate::instrumentation::record_deterministic_work(1);
                let held = project(&exit.locals().get(name)?.native())?;
                let argument = instance.arguments().get(position)?;
                if !crate::kernel::resource_field_values_proven_equal(
                    argument,
                    (&AlgebraicValue::Program(held.clone())).into(),
                    context,
                ) {
                    return None;
                }
            }
            Some(AlgebraicValue::Program(fresh.clone()))
        })
        .collect()
}

#[cfg(test)]
mod exit_local_argument_tests;

/// A value-only binding introduced by lowering is not an automatic object.
/// If an exit never produced it, no common value can be read after the loop.
/// Discard only loop-written names absent at entry, and only when every held
/// binding has no declared storage. SymbolicMemory and resource authority remain intact.
fn discard_loop_exit_partial_value_bindings(
    top: &ExecutionState,
    body: &ProgramStatement,
    exits: &mut [ExecutionState],
) {
    let mut names = BTreeSet::new();
    collect_loop_modified_locals(body, &mut names);
    for name in names {
        crate::instrumentation::record_deterministic_work(1);
        if top.locals.binding(&name).is_some() {
            continue;
        }
        let mut missing = false;
        let mut value_only = true;
        for state in exits.iter() {
            crate::instrumentation::record_deterministic_work(1);
            match state.locals.binding(&name) {
                None => missing = true,
                Some(LocalBinding::Object {
                    storage_declared: false,
                    ..
                }) => {}
                _ => {
                    value_only = false;
                    break;
                }
            }
        }
        if missing && value_only {
            for state in exits.iter_mut() {
                state.locals.remove(&name);
            }
        }
    }
}

/// One resource argument or field vector, position by position: the common
/// value where every exit agrees, a fresh name plus one equation per exit
/// where they do not.
fn joined_resource_values<'a>(
    base: &ResourceArguments,
    exits: impl Iterator<Item = &'a ResourceArguments> + Clone,
    local_arguments: &[Option<AlgebraicValue>],
    restatements: &mut [LoopExitRestatement],
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<ResourceArguments, String> {
    let mut joined = base.to_vec();
    for (position, value) in joined.iter_mut().enumerate() {
        let mut held = Vec::with_capacity(restatements.len());
        for exit in exits.clone() {
            let Some(value) = exit.get(position) else {
                return Err("the exits hold resource instances of different widths".to_string());
            };
            held.push(value.into_native());
        }
        let local = local_arguments.get(position).and_then(Option::as_ref);
        if held.iter().all(|other| other == value) && local.is_none_or(|local| local == value) {
            continue;
        }
        let fresh = match local {
            Some(local) => local.clone(),
            None => fresh_resource_value_like(&*value, variables, budget)?,
        };
        for (restatement, held) in restatements.iter_mut().zip(held) {
            restatement.pin_resource_value(&fresh, &held);
        }
        *value = fresh;
    }
    Ok(joined.into())
}

/// Join the selected model fields while keeping every unchanged producer.
fn joined_resource_fields<'a>(
    base: &ResourceFieldValues,
    exits: impl Iterator<Item = &'a ResourceFieldValues> + Clone,
    restatements: &mut [LoopExitRestatement],
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<ResourceFieldValues, String> {
    let mut joined = Vec::with_capacity(base.len());
    for position in 0..base.len() {
        if let Some(initial) = base.integer_term(position)
            && let Some(held) = exits
                .clone()
                .map(|exit| exit.integer_term(position))
                .collect::<Option<Vec<_>>>()
        {
            if held
                .iter()
                .all(|other| same_loop_exit_integer(&initial, other))
            {
                joined.push(base.stored_field(position).expect("field index"));
                continue;
            }
            let variable = variables.next_in(budget).map_err(exhausted_identities)?;
            let root = KernelTerm::variable(KernelType::Integer, variable);
            let fresh = Term::Integer(
                StoredIntegerTerm::from_root(root.clone()).expect("fresh Integer field"),
            );
            for (restatement, held) in restatements.iter_mut().zip(held) {
                restatement
                    .equations
                    .push(Proposition::Equal(fresh.clone(), Term::Integer(held)));
            }
            joined.push(StoredResourceField::Integer(root));
            continue;
        }
        let value = base.get(position).expect("field index");
        let held = exits
            .clone()
            .map(|exit| {
                exit.get(position).ok_or_else(|| {
                    "the exits hold resource instances of different widths".to_string()
                })
            })
            .collect::<Result<Vec<_>, _>>()?;
        if held.iter().all(|other| *other == value) {
            joined.push(base.stored_field(position).expect("field index"));
            continue;
        }
        let fresh = fresh_resource_value_like(value, variables, budget)?;
        for (restatement, held) in restatements.iter_mut().zip(held) {
            restatement.pin_resource_value(&fresh, &held.into_native());
        }
        joined.push(StoredResourceField::from_minted(fresh));
    }
    Ok(ResourceFieldValues::from_stored(joined))
}

fn same_loop_exit_integer(left: &StoredIntegerTerm, right: &StoredIntegerTerm) -> bool {
    match (left.root(), right.root()) {
        (Some(left), Some(right)) => left.integer_native_syntax_equal(right),
        _ => left == right,
    }
}

/// A fresh symbolic value of the same sort as `value`.
fn fresh_resource_value_like<'a>(
    value: impl Into<ResourceFieldValue<'a>>,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<AlgebraicValue, String> {
    let variable = variables.next_in(budget).map_err(exhausted_identities)?;
    Ok(match value.into() {
        ResourceFieldValue::Integer(_) => AlgebraicValue::Integer(IntegerTerm::Variable(variable)),
        ResourceFieldValue::Program(value) => {
            AlgebraicValue::Program(symbolic_call_result(value.program_type(), variable))
        }
        ResourceFieldValue::Algebraic(term) => AlgebraicValue::Algebraic(AlgebraicTerm {
            algebraic_type: term.algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(variable),
        }),
    })
}

/// The loop-exit abstraction reports its refusals as text the caller shows
/// beside the states it could not make common. An exhausted identity counter
/// is one of those refusals, named rather than swallowed.
fn exhausted_identities(limit: ExecutionLimit) -> String {
    format!(
        "the execution has no fresh identity left: it stopped at {}",
        limit.describe()
    )
}

/// One resource argument or field as the term an equation is written over.
fn resource_value_term(value: &AlgebraicValue) -> Term {
    match value {
        AlgebraicValue::Integer(term) => Term::Integer(term.clone().into()),
        AlgebraicValue::Program(value) => Term::ProgramValue(value.clone().into()),
        AlgebraicValue::Algebraic(term) => Term::Algebraic(term.clone().into()),
    }
}

/// What the join replaced in the successor, for the residual comparison to
/// put back at each exit.
struct LoopExitAbstraction<'a> {
    locals: &'a [(BindingName, ProgramType)],
    uninitialized: &'a [BindingName],
    cells: &'a BTreeSet<Address>,
    bookkeeping: bool,
}

/// Leaves uninitialized every scalar local some exit has initialized and
/// another has not, and reports their names.
///
/// A path that leaves the loop before its first assignment to a local holds
/// it uninitialized; one that leaves after holds a value. The successor
/// claims neither: the local keeps its slot, type and qualifiers and has no
/// value, so a read of it after the loop is refused rather than given a value
/// one path never produced. What this gives up is exactly such a read.
///
/// Look up each changed scalar binding in the exits.
fn abstract_loop_exit_initialization(
    successor: &mut ExecutionState,
    exits: &[ExecutionState],
    changed_locals: &BTreeSet<BindingName>,
) -> Vec<BindingName> {
    let mut uninitialized = Vec::new();
    for name in changed_locals {
        if !matches!(
            successor.locals.bindings.get(name),
            Some(LocalBinding::Object { .. } | LocalBinding::UninitializedObject { .. })
        ) {
            continue;
        }
        let mut initialized = false;
        let mut not_initialized = false;
        for state in exits {
            crate::instrumentation::record_deterministic_work(1);
            match state.locals.binding(name) {
                Some(LocalBinding::Object { .. }) => initialized = true,
                Some(LocalBinding::UninitializedObject { .. }) => not_initialized = true,
                // Any other shape is a difference the residual comparison
                // names; this step only reconciles initialization.
                _ => {}
            }
        }
        if initialized && not_initialized {
            successor.locals.forget_initialization(name);
            uninitialized.push(name.clone());
        }
    }
    uninitialized
}

/// Joins automatic-storage records and call state epochs when they differ.
///
/// A path that called a function with a local holds a tombstone for that
/// local's ended block, a forget mark from retiring its cell, and a larger
/// lifetime counter than a path that did not. None of these is a value the
/// C can observe after the loop, and each has a conservative join:
///
/// - **Tombstones: the union.** A tombstone for a block a path never created
///   forbids accesses that path could not make, and only disables the
///   inference that a loaded pointer predates the block. The interface join
///   takes the same union.
/// - **Lifetime counter: the maximum,** so the next re-entered declaration
///   gets an identity no exit has used. The branch join takes the same
///   maximum. A smaller counter would reissue an ended block's identity.
/// - **Call epochs: common history plus one fresh marker.** Branch-local
///   havoc and checked write-set markers describe different states, not
///   physical blocks. Retain their common history and mint one new epoch,
///   avoiding a union that each residual check would have to scan.
/// - **SymbolicMemory state identity: fresh.** A forget mark says a memory is not known
///   to be the memory it forgot from. When the exits' marks differ, the
///   successor's memory keeps only what every exit agrees on (the cells the
///   join has already made common) and is marked as forgetting from a
///   state minted here when forget marks or call epochs differ, which no
///   exit's memory and no earlier state
///   is, with no derivation recorded. A load after the loop of a cell the
///   successor does not hold is therefore related to no load before or
///   inside the loop. That relation is what this gives up.
///
/// Applied only when an exit differs from the successor in one of these, so
/// a loop whose exits agree keeps its memory's identity and every read
/// equality through it. Returns whether it applied.
fn join_loop_exit_storage_bookkeeping(
    successor: &mut ExecutionState,
    exits: &[ExecutionState],
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<bool, String> {
    crate::instrumentation::record_deterministic_work(exits.len());
    let forgotten_differ = exits
        .iter()
        .any(|state| state.memory.forgotten != successor.memory.forgotten);
    let counter = exits
        .iter()
        .map(|state| state.next_local_lifetime)
        .max()
        .unwrap_or(successor.next_local_lifetime);
    let counters_differ = exits
        .iter()
        .any(|state| state.next_local_lifetime != successor.next_local_lifetime);
    let frame_counter = exits
        .iter()
        .map(|state| state.next_local_frame)
        .max()
        .unwrap_or(successor.next_local_frame);
    let frames_differ = exits
        .iter()
        .any(|state| state.next_local_frame != successor.next_local_frame);
    let mut marker_delta = BTreeSet::new();
    for state in exits {
        for change in state.memory.blocks.diff(&successor.memory.blocks) {
            crate::instrumentation::record_deterministic_work(1);
            if is_loop_exit_state_marker(change.key()) {
                marker_delta.insert(change.key().clone());
            }
        }
    }
    let markers_differ = !marker_delta.is_empty();
    if !forgotten_differ && !counters_differ && !frames_differ && !markers_differ {
        return Ok(false);
    }
    successor.next_local_lifetime = counter;
    successor.next_local_frame = frame_counter;
    if forgotten_differ || markers_differ {
        let mut memory = successor.memory.clone();
        for key in marker_delta {
            std::sync::Arc::make_mut(&mut memory.blocks).remove(&key);
        }
        let ended = exits
            .iter()
            .flat_map(|state| state.memory.forgotten.ended_local_blocks.iter().cloned())
            .collect::<crate::kernel::HashedOrdSet<_>>();
        let ended_addressable = exits
            .iter()
            .flat_map(|state| {
                state
                    .memory
                    .forgotten
                    .ended_addressable_local_blocks
                    .iter()
                    .cloned()
            })
            .collect::<crate::kernel::HashedOrdSet<_>>();
        let forgotten = std::sync::Arc::make_mut(&mut memory.forgotten);
        forgotten.ended_local_blocks = ended;
        forgotten.ended_addressable_local_blocks = ended_addressable;
        let marker = variables.next_in(budget).map_err(exhausted_identities)?;
        if markers_differ {
            // Keep the common history and mint one new epoch. A union of all
            // branch-local markers would cost exits squared at the residual
            // checks, and no old epoch may stand for this joined memory.
            let prefix = if exits
                .iter()
                .any(|state| state.memory.has_call_memory_havoc())
            {
                "call-havoc"
            } else {
                "havoc"
            };
            std::sync::Arc::make_mut(&mut memory.blocks).insert(
                AddressBase::Concrete(format!("{prefix}:{}", marker.0)),
                MemoryBlock::new(0),
            );
        }
        let minted = crate::kernel::intern_memory(
            SymbolicMemory::new().with_block(format!("loop-exit-join:{}", marker.0).as_str(), 0),
        );
        memory.mark_forgotten_from(&minted);
        memory.record_diagnostic_transform(
            "join loop exit markers",
            std::iter::once(successor.memory.clone())
                .chain(exits.iter().map(|state| state.memory.clone()))
                .collect(),
            Vec::new(),
        );
        *successor = successor.clone().with_memory(memory);
    }
    Ok(true)
}

/// Havocs the locals the exits disagree on, keeping the rest, and reports
/// which ones it abstracted.
fn abstract_loop_exit_locals(
    successor: &mut ExecutionState,
    exits: &[ExecutionState],
    changed_locals: BTreeSet<BindingName>,
    restatements: &mut [LoopExitRestatement],
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<Vec<(BindingName, ProgramType)>, String> {
    let mut abstracted = Vec::new();
    for name in changed_locals {
        if !matches!(
            successor.locals.bindings.get(&name),
            Some(LocalBinding::Object { .. })
        ) {
            continue;
        }
        let mut held = Vec::with_capacity(exits.len());
        for state in exits {
            crate::instrumentation::record_deterministic_work(1);
            let Some(value) = state.locals().get(&name) else {
                return Err(format!("local `{name}` is not bound by every exit"));
            };
            held.push(value.clone());
        }
        if held[1..].iter().all(|value| *value == held[0]) {
            continue;
        }
        let Some(program_type) = successor.local_object_type(&name) else {
            return Err(format!("local `{name}` has no scalar type here"));
        };
        let Some(fresh) = fresh_loop_local_value(program_type, variables, budget)
            .map_err(exhausted_identities)?
        else {
            return Err(format!("local `{name}` has no abstract value of its type"));
        };
        // Exits that agree on the subobject a pointer designates keep it.
        let fresh = match held
            .iter()
            .map(program_value_subobject_bounds)
            .collect::<Vec<_>>()
        {
            all_bounds
                if all_bounds[1..]
                    .iter()
                    .all(|bounds| *bounds == all_bounds[0]) =>
            {
                with_retained_bounds(fresh, held.first())
            }
            _ => fresh,
        };
        // So do exits that agree on the class of the object it designates.
        let fresh = match held
            .iter()
            .map(program_value_object_class)
            .collect::<Vec<_>>()
        {
            classes if classes[1..].iter().all(|class| *class == classes[0]) => {
                let mut evidence = None::<ObjectTypeEvidence>;
                let mut complete = true;
                for value in &held {
                    if let Some(pointer) = value.pointer()
                        && !pointer.is_null()
                    {
                        match pointer.object_type_evidence() {
                            Some(next) => {
                                evidence = Some(match evidence {
                                    Some(previous) => previous.merge(next),
                                    None => next.clone(),
                                })
                            }
                            None => complete = false,
                        }
                    }
                }
                with_retained_object_class(fresh, held.first())
                    .with_pointer_object_type_evidence(complete.then_some(evidence).flatten())
            }
            _ => fresh,
        };
        for (restatement, held) in restatements.iter_mut().zip(held) {
            restatement.pin(&fresh, &held.native());
        }
        sync_stack_local(successor, &name, &fresh);
        successor
            .locals
            .set_typed(name.clone(), fresh, program_type);
        abstracted.push((name, program_type));
    }
    Ok(abstracted)
}

/// Havocs the cells the exits wrote differently, keeping the rest.
///
/// The loop body owns exactly what the loop header declared, so a cell one
/// exit left holding a different value is a cell inside a declared binder: the
/// binder's model is what a proof after the loop reads it back through, and
/// the disjunction relates the two. A loop that declares no binder has nothing
/// to read such a cell through, so the disagreement is refused by name.
fn abstract_loop_exit_memory(
    successor: &mut ExecutionState,
    exits: &[ExecutionState],
    resynced: &BTreeSet<Address>,
    no_binders: bool,
    declared_memory: &[MemoryRange],
    assumptions: &PureFactContext,
    contexts: &[PureFactContext],
    restatements: &mut [LoopExitRestatement],
    join_requirements: &mut Vec<ProofObligation>,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> Result<BTreeSet<Address>, String> {
    let mut memory = successor.memory().clone();
    if exits.iter().any(|state| {
        !state
            .memory()
            .heap
            .have_same_allocation_lifetimes(&memory.heap)
    }) {
        return Err("heap allocation lifetimes".to_string());
    }
    // Compare post-resynchronization memory with each exit. This also
    // selects cells only another exit holds, and skips the persistent
    // concrete cells and compact runs that every exit shares.
    let pointers = exits
        .iter()
        .flat_map(|state| memory.cells.differing_pointers(&state.memory().cells))
        .filter(|pointer| !resynced.contains(pointer))
        .collect::<BTreeSet<_>>();
    let mut dropped = Vec::new();
    let mut havoced = Vec::new();
    let mut abstracted = BTreeSet::new();
    for pointer in pointers {
        if !memory.cells.contains_key(&pointer) {
            // Only another exit holds this value. The successor already
            // omits it, but the residual comparison must set it aside.
            abstracted.insert(pointer);
            continue;
        }
        let mut held = Vec::with_capacity(exits.len());
        for state in exits {
            crate::instrumentation::record_deterministic_work(1);
            match state.memory().cells.get(&pointer) {
                Some(value) => held.push(value.clone()),
                // A cell one exit does not hold is authority the successor
                // cannot have; dropping it only makes a later read fail.
                None => {
                    dropped.push(pointer.clone());
                    break;
                }
            }
        }
        if held.len() != exits.len() {
            continue;
        }
        if held[1..].iter().all(|value| *value == held[0]) {
            continue;
        }
        if no_binders || !assumptions.ranges_proven_disjoint_from_pointer(declared_memory, &pointer)
        {
            return Err(format!(
                "the cell in `{}` that the exits write differently is owned by no loop binder",
                pointer.base
            ));
        }
        let Some(fresh) = fresh_loop_local_value(held[0].program_type(), variables, budget)
            .map_err(exhausted_identities)?
        else {
            return Err(format!(
                "the cell in `{}` has no abstract value of its type",
                pointer.base
            ));
        };
        for (index, (restatement, held)) in restatements.iter_mut().zip(held).enumerate() {
            let context = contexts.get(index).unwrap_or(assumptions);
            let named = loop_exit_cell_pin_value(&held, context);
            restatement.pin(&fresh, &named);
        }
        havoced.push((pointer, fresh));
    }
    if let Some(ledger) = successor
        .borrow_ledger()
        .filter(|ledger| ledger.has_active_memory_borrows())
    {
        // Use the cells this join is about to abstract and the common exit
        // ledger retained in the successor. The resulting conditions are
        // prerequisites of the join, independent of its pinning equations.
        for pointer in dropped
            .iter()
            .chain(havoced.iter().map(|(pointer, _)| pointer))
        {
            crate::instrumentation::record_deterministic_work(1);
            let byte_width = memory
                .cells
                .get(pointer)
                .map(|value| value.byte_width())
                .unwrap_or(0);
            if byte_width == 0 {
                continue;
            }
            let range = MemoryRange::new_with_element_width(
                pointer.clone(),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(byte_width),
                1,
            );
            join_requirements.extend(loop_borrow_separation(
                ledger,
                &range,
                "loop exit join separation",
            ));
        }
    }
    if !dropped.is_empty() || !havoced.is_empty() {
        let cells = std::sync::Arc::make_mut(&mut memory.cells);
        for pointer in dropped {
            cells.remove(&pointer);
            abstracted.insert(pointer);
        }
        for (pointer, value) in havoced {
            cells.insert(pointer.clone(), value);
            abstracted.insert(pointer);
        }
        memory.record_diagnostic_transform(
            "abstract loop exit cells",
            std::iter::once(successor.memory.clone())
                .chain(exits.iter().map(|state| state.memory.clone()))
                .collect(),
            Vec::new(),
        );
        *successor = successor
            .clone()
            .with_memory_relative_to(memory, successor.memory());
    }
    Ok(abstracted)
}

/// Export a proved scalar constant instead of a private loop-body read.
/// The selected cell supplies the literal index key; no fact or equality class is
/// enumerated, and this changes a produced equation rather than lowering.
fn loop_exit_cell_pin_value(value: &ProgramValue, context: &PureFactContext) -> ProgramValue {
    match value {
        ProgramValue::Int32(term) | ProgramValue::UInt32(term) => {
            match crate::kernel::assumptions::exact_signed_constant(term, context) {
                Some(constant) => match value {
                    ProgramValue::Int32(_) => int32(OldMachineTerm::constant(constant as u32)),
                    _ => uint32(OldMachineTerm::constant(constant as u32)),
                },
                None => value.clone(),
            }
        }
        _ => value.clone(),
    }
}

/// The memory ranges a loop's own header declared, rather than folded into one
/// of its binders.
fn loop_declared_memory_ranges(body_state: &ExecutionState) -> Vec<MemoryRange> {
    body_state
        .resources()
        .facts()
        .iter()
        .filter_map(|fact| match fact {
            ResourceFact::Own(Resource::Memory(range), _) => Some(range.clone()),
            _ => None,
        })
        .collect()
}

/// The abstract value a loop havoc gives a local of this type, if it has one.
fn fresh_loop_local_value(
    program_type: ProgramType,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<ProgramValue>> {
    // An array object is never assigned by name (C forbids it) and binds as
    // an array object rather than a scalar one, and `void` has no value, so
    // neither type takes an identity from the counter at all.
    match program_type {
        ProgramType::Int8Array(_) => return Ok(None),
        ProgramType::Void
        | ProgramType::Int32Array(_)
        | ProgramType::UInt8Array(_)
        | ProgramType::Int16Array(_)
        | ProgramType::UInt16Array(_)
        | ProgramType::UInt32Array(_)
        | ProgramType::Int128Array(_)
        | ProgramType::Int64Array(_)
        | ProgramType::UInt128Array(_)
        | ProgramType::UInt64Array(_)
        | ProgramType::Float32Array(_)
        | ProgramType::Float64Array(_) => return Ok(None),
        _ => {}
    }
    let variable = variables.next_in(budget)?;
    Ok(Some(match program_type {
        ProgramType::Bool => ProgramValue::Bool(OldMachineTerm::Variable(variable)),
        ProgramType::Int8 => int8(OldMachineTerm::Variable(variable)),
        ProgramType::Int16 => int16(OldMachineTerm::Variable(variable)),
        ProgramType::Int32 => int32(OldMachineTerm::Variable(variable)),
        ProgramType::UInt8 => uint8(OldMachineTerm::Variable(variable)),
        ProgramType::UInt16 => uint16(OldMachineTerm::Variable(variable)),
        ProgramType::UInt32 => uint32(OldMachineTerm::Variable(variable)),
        ProgramType::Int64 => ProgramValue::Int64(OldMachineTerm::Variable(variable))
            .complete_word(Address::symbolic(variable)),
        ProgramType::UInt64 => ProgramValue::UInt64(OldMachineTerm::Variable(variable))
            .complete_word(Address::symbolic(variable)),
        ProgramType::Float32 => ProgramValue::Float32(OldMachineTerm::Variable(variable)),
        ProgramType::Float64 => ProgramValue::Float64(OldMachineTerm::Variable(variable)),
        ProgramType::FunctionPointer(_) => {
            ProgramValue::typed_pointer(Address::symbolic_function(variable), program_type)
        }
        // A local holding a spec value, a Rust enum, a `Vec` or a library
        // iterator, takes a fresh value of its own type.
        ProgramType::Parameter(parameter) => ProgramValue::Parameter(Box::new(AlgebraicTerm {
            algebraic_type: parameter.algebraic_type(),
            node: AlgebraicTermNode::Variable(variable),
        })),
        // A slice local reassigned in the body is a fresh slice, its data
        // pointer and count named by the one variable.
        ProgramType::SlicePointer(_) => crate::kernel::symbolic_call_result(program_type, variable),
        // A pointer local reassigned in the body (`p = p + 1`) must not keep
        // its entry value across the abstract iteration, exactly as the join
        // abstraction treats it; an invariant must relate it.
        _ => ProgramValue::typed_pointer(Address::symbolic(variable), program_type),
    }))
}

/// What an abstracted successor and one exit still disagree about once the
/// components the abstraction deliberately replaced are put back.
///
/// The successor is reconstructed at this exit: its binder instances, its
/// havocked locals, and its havocked cells are restored to the values this
/// exit reached. Anything still different is a component the rule did not
/// model — an allocation lifetime, a block shape, ownership beyond the
/// binders — and the join refuses under that name rather than exporting a
/// state no exit stands in.
fn loop_exit_residual_difference(
    successor: &ExecutionState,
    exit: &ExecutionState,
    abstracted: &LoopExitAbstraction<'_>,
    binders: &[LoopBinder],
    assumptions: &PureFactContext,
) -> Option<String> {
    let LoopExitAbstraction {
        locals,
        uninitialized,
        cells,
        bookkeeping,
    } = *abstracted;
    let mut witness = successor.clone();
    // Where a path last folded a binder is not a component of its state: a
    // resource context is a multiset, and the witness below re-seats each
    // binder instance after everything else. The exit is re-seated the same
    // way, so an exit that refolded one binder and left another untouched is
    // compared by what it holds rather than by the order it folded in.
    let mut seated = exit.clone();
    for binder in binders {
        let Some(joined) = witness.resources().owned_instance(binder.identity).cloned() else {
            continue;
        };
        let Some(held) = exit.resources().owned_instance(binder.identity).cloned() else {
            continue;
        };
        let Some(resources) = witness.resources().clone().without_fact_incrementally(
            &ResourceFact::own(Resource::Instance(joined)),
            &PureFactContext::new(),
        ) else {
            continue;
        };
        let held_fact = ResourceFact::own(Resource::Instance(held));
        let Some(exit_resources) = seated
            .resources()
            .clone()
            .without_fact_incrementally(&held_fact, &PureFactContext::new())
        else {
            continue;
        };
        witness = witness.with_resource_context(resources.unchecked_with_fact(held_fact.clone()));
        seated = seated.with_resource_context(exit_resources.unchecked_with_fact(held_fact));
    }
    for name in uninitialized {
        // This exit's own binding, initialized or not, is what the successor
        // left without a value.
        if let Some(binding) = seated.locals.binding(name).cloned() {
            witness.locals.restore_binding(name, binding);
        }
    }
    if bookkeeping {
        witness.next_local_frame = seated.next_local_frame;
        witness.next_local_lifetime = seated.next_local_lifetime;
        let diagnostic_base = witness.memory.clone();
        witness.memory.forgotten = seated.memory.forgotten.clone();
        let changes = witness
            .memory
            .blocks
            .diff(&seated.memory.blocks)
            .map(|change| change.key().clone())
            .filter(is_loop_exit_state_marker)
            .collect::<Vec<_>>();
        for key in changes {
            crate::instrumentation::record_deterministic_work(1);
            let blocks = std::sync::Arc::make_mut(&mut witness.memory.blocks);
            if let Some(block) = seated.memory.blocks.get(&key) {
                blocks.insert(key, block.clone());
            } else {
                blocks.remove(&key);
            }
        }
        witness.memory.record_diagnostic_transform(
            "align loop exit markers",
            vec![diagnostic_base, seated.memory.clone()],
            Vec::new(),
        );
    }
    for (name, program_type) in locals {
        let value = seated.locals().get(name)?.clone();
        sync_retained_stack_local(&mut witness, name, &value);
        witness.locals.set_retained_typed_with_all_qualifiers(
            name.clone(),
            value,
            *program_type,
            false,
            false,
            false,
            false,
        );
    }
    if !cells.is_empty() {
        let mut memory = witness.memory().clone();
        let mut exit_memory = seated.memory().clone();
        let restored = std::sync::Arc::make_mut(&mut memory.cells);
        let held = std::sync::Arc::make_mut(&mut exit_memory.cells);
        for pointer in cells {
            if !restored.contains_key(pointer) {
                // The successor does not hold this cell: it was dropped, or
                // only some exit ever held it. That is knowledge the exit has
                // and the successor does not claim, so it is set aside on the
                // exit's side rather than written into the witness.
                held.remove(pointer);
                continue;
            }
            match held.get(pointer) {
                Some(value) => {
                    restored.insert(pointer.clone(), value);
                }
                None => {
                    restored.remove(pointer);
                }
            }
        }
        memory.record_diagnostic_transform(
            "restore loop exit cells",
            vec![witness.memory.clone(), seated.memory.clone()],
            cells.iter().cloned().map(ProgramValue::pointer).collect(),
        );
        exit_memory.record_diagnostic_transform(
            "abstract unmatched loop exit cells",
            vec![seated.memory.clone(), witness.memory.clone()],
            cells.iter().cloned().map(ProgramValue::pointer).collect(),
        );
        witness = witness.with_memory_relative_to(memory, successor.memory());
        seated = seated.with_memory_relative_to(exit_memory, successor.memory());
    }
    loop_exit_state_difference(&witness, &seated, successor.memory(), assumptions)
}

/// Whether two exits hold the same resources: structurally, or after each
/// context drops only its exact owner-supported observations and identity
/// expansion caches, then is normalized once. An independent view, a live
/// borrow-bound view, a nontrivial expansion, or different quantities stay distinct.
fn loop_exit_resources_agree(
    left: &ResourceContext,
    right: &ResourceContext,
    assumptions: &PureFactContext,
) -> bool {
    left == right
        || left
            .clone()
            .without_redundant_owned_memory_views()
            .normalized(assumptions)
            == right
                .clone()
                .without_redundant_owned_memory_views()
                .normalized(assumptions)
}

/// What two loop exit states disagree about, named for a refusal.
///
/// Two components are compared by what they mean rather than by how the
/// path that built them happened to lay them out, because a layout is not
/// something a path reaches:
///
/// - memory, by [`SymbolicMemory::same_contents_as`]: the same cells with the same
///   values, whether the cell cache holds one as a concrete cell or as a
///   slot of a seeded run;
/// - resource ownership, by the normalized context, the form
///   `ResourceContext::normalized` already gives two contexts before the
///   kernel compares an unfolded body with its expected one. It merges only
///   what the resource algebra says is one authority (an unbound view held
///   twice, an owner and its own unbound view), including an exact
///   owner-supported observation and identity cache, but never a borrow-bound
///   view or a nontrivial supported description.
///
/// Both are exact: a byte, a value, an owned or viewed fact, a quantity, a
/// read-only block, a heap lifetime or a borrow dependency that differs still
/// differs afterwards. The equivalent component is then taken from the left
/// state so the remaining components are compared by `==` as before.
fn loop_exit_state_difference(
    left: &ExecutionState,
    right: &ExecutionState,
    memory_base: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> Option<String> {
    let same_memory = left
        .memory()
        .same_contents_relative_to(right.memory(), memory_base);
    let mut aligned = right.clone();
    // Creation ledgers that record the same state differ only in their
    // fresh names: a local one exit created and retired leaves none behind.
    if same_memory {
        // Reuse the already compared memory in the state equality check.
        aligned.memory = left.memory.clone();
        if left.equal_up_to_creation_ledger_identity(&aligned) {
            return None;
        }
    }
    let same_resources =
        loop_exit_resources_agree(left.resources(), right.resources(), assumptions);
    if same_memory && same_resources {
        aligned.resources = left.resources.clone();
        if left.equal_up_to_creation_ledger_identity(&aligned) {
            return None;
        }
    }
    // Keep this exhaustive: a new checked state component must also acquire a
    // diagnostic name. These comparisons explain rejection, not join acceptance.
    let ExecutionState {
        aggregate_destination,
        instance_field_scope,
        body_field_view,
        resource_bindings,
        borrow_ledger,
        borrow_participant,
        borrow_bindings,
        thread_ledger,
        mutex_ledger,
        preserves_mutex_protocols,
        mutex_input_reservations,
        opaque_mutex_acquisitions,
        named_mutex_authorities,
        pending_thread_create,
        population_access,
        observed_population_families,
        population_effects,
        next_local_frame,
        next_local_lifetime,
        enclosing_frame_holds_locals,
        step_results,
        aggregate_step_objects,
        literal_values,
        locals,
        memory: _,
        // Where a state was reached is not part of what it holds.
        point: _,
        resources: _,
    } = left;
    let mut differences = Vec::new();
    macro_rules! component {
        ($field:ident, $label:literal) => {
            if $field != &right.$field {
                differences.push($label.to_string());
            }
        };
        ($field:ident, $label:literal, values) => {
            if $field != &right.$field {
                differences.push(format!(
                    "{} (successor: {:?}; exit: {:?})",
                    $label, $field, right.$field
                ));
            }
        };
    }
    if locals != &right.locals {
        let names = locals.differing_names(&right.locals).collect::<Vec<_>>();
        let shown = names
            .iter()
            .take(12)
            .map(|name| name.to_string())
            .collect::<Vec<_>>();
        let mut detail = if shown.is_empty() {
            "local storage slot bindings".to_string()
        } else {
            format!("local `{}`", shown.join("`, `"))
        };
        if names.len() > shown.len() {
            detail.push_str(&format!(
                " ({} additional locals differ)",
                names.len() - shown.len()
            ));
        }
        differences.push(detail);
    }
    if !same_memory {
        differences.push("memory".to_string());
    }
    if !same_resources {
        differences.push("resource ownership".to_string());
    }
    component!(aggregate_destination, "aggregate call destination");
    component!(instance_field_scope, "resource field evaluation scope");
    component!(body_field_view, "resource body field view");
    if resource_bindings != &right.resource_bindings {
        differences.push(format!(
            "call resource bindings (successor: {} entries; exit: {} entries)",
            resource_bindings
                .as_ref()
                .map_or(0, |bindings| bindings.len()),
            right
                .resource_bindings
                .as_ref()
                .map_or(0, |bindings| bindings.len())
        ));
    }
    component!(borrow_ledger, "stable-view borrow authority");
    component!(borrow_participant, "stable-view borrow participant");
    component!(borrow_bindings, "stable-view occurrence bindings");
    component!(thread_ledger, "thread completion authority");
    component!(mutex_ledger, "mutex authority");
    component!(
        preserves_mutex_protocols,
        "mutex protocol preservation",
        values
    );
    component!(mutex_input_reservations, "mutex input reservations");
    component!(opaque_mutex_acquisitions, "opaque mutex acquisitions");
    component!(named_mutex_authorities, "named mutex authority bindings");
    component!(pending_thread_create, "pending thread creation");
    component!(population_access, "population access");
    component!(observed_population_families, "observed population families");
    if population_effects != &right.population_effects {
        let mut effects_only = left.clone();
        effects_only.population_effects = right.population_effects.clone();
        if !left.equal_up_to_creation_ledger_identity(&effects_only) {
            differences.push("population effects".to_string());
        }
    }
    component!(next_local_frame, "next automatic-storage frame", values);
    component!(
        next_local_lifetime,
        "next automatic-storage lifetime",
        values
    );
    component!(
        enclosing_frame_holds_locals,
        "enclosing frame holds automatic objects",
        values
    );
    component!(aggregate_step_objects, "aggregate expression storage");
    component!(literal_values, "literal objects");
    component!(step_results, "call results");
    Some(differences.join(", "))
}

#[allow(clippy::too_many_arguments)]
fn execute_program_loop_exit_paths(
    state: &ExecutionState,
    program_loop: LoopExecutionView<'_>,
    assumptions: &PureFactContext,
    environment: &ExecutionEnvironment,
    preservation_environment: Option<&ExecutionEnvironment>,
    final_exit_candidates: &[LoopFinalExitCandidate],
    early_exits: &[LoopEarlyExit],
    return_exits: &[LoopReturnExit],
    back_edges: &[super::api::LoopBackEdges],
    otherwise: Option<&mut LoopOtherwiseProof<'_>>,
    exit_fact_scope: Option<&LoopExitFactScope<'_>>,
    execution_semantics: ExecutionSemantics,
    initialization_proven: bool,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<Vec<StatementExecutionPath>> {
    let LoopExecutionView {
        entry_guard: condition,
        invariant,
        invariant_checks,
        effect_checks,
        resource_specs,
        body,
        update,
        test,
        backedge_target,
        natural_exit_target,
        ..
    } = program_loop;
    let pass_body = program_loop_pass(body, update, Some(test));
    let body = &pass_body;
    let mut base_obligations = Vec::new();
    for proposition in invariant {
        if add_proof_obligation(&mut base_obligations, assumptions, proposition.clone()).is_none() {
            return Ok(Vec::new());
        }
    }

    let composite_resource_definitions = environment_composite_resource_definitions(environment);
    // A proof-checked body ran from a head the kernel already built; its
    // exits, back edges and this rule's guard exit share that one head.
    let head = match back_edges.first() {
        Some(proof) => {
            // The head's identities were invented before this rule; what it
            // invents now comes after them.
            budget.continue_past_mark(proof.next_kernel_variable);
            (*proof.head).clone()
        }
        None => prepare_loop_top_state(
            state,
            effect_checks,
            invariant_checks,
            resource_specs,
            &composite_resource_definitions,
            body,
            assumptions,
            budget,
            variables,
        )?,
    };
    // Entry invariants are checked at the real loop entry, with the loop's
    // binders already bound to the instances they name there. `old(...)` keeps
    // reading the state as the enclosing proof wrote it, under the identities
    // that proof used.
    let entry_obligations = if initialization_proven {
        Vec::new()
    } else {
        collect_invariant_check_obligations(
            &head.entry,
            state,
            invariant_checks,
            InvariantPhase::Entry,
            None,
            assumptions,
            budget,
        )?
    };
    let top_state = head.top.clone();
    // The loop's declared binders, for the exit join: D5 names them at the
    // head, at the back edge, and at every exit by the same rule.
    let binders = loop_binders(resource_specs);
    // The guard and the invariants are read with the selected arm's cells
    // published (D7); the loop's exit outcome stays `top_state`, so that read
    // authority never leaves the head.
    let guard_state = head.guard.clone();
    let whole_loop_effect_summaries = head.summaries.clone();
    let (preservation_obligations, mut final_exit_paths, body_early_exits, iteration_writes) =
        if let Some(environment) = preservation_environment {
            let summary = collect_loop_preservation_summary(
                state,
                &head,
                LoopExecutionView {
                    effect_checks: &head.effect_checks,
                    ..program_loop
                },
                &composite_resource_definitions,
                &whole_loop_effect_summaries,
                assumptions,
                ExecutionContext::new(environment, execution_semantics),
                budget,
                variables,
            )?;
            (
                summary.obligations,
                summary.final_exit_paths,
                summary.early_exits,
                summary.iteration_writes,
            )
        } else {
            (Vec::new(), Vec::new(), Vec::new(), None)
        };
    let mut loop_check_obligations = Vec::new();
    // A loop may only declare resources the enclosing context actually holds.
    for failure in &head.resource_failures {
        loop_check_obligations.push(
            ProofObligation::verification_condition(false_equals_true_proposition())
                .with_context(failure.context()),
        );
    }
    append_required_proof_obligations(&mut loop_check_obligations, assumptions, &entry_obligations);
    append_required_proof_obligations(
        &mut loop_check_obligations,
        assumptions,
        &preservation_obligations,
    );
    for path in &mut final_exit_paths {
        append_required_proof_obligations(
            &mut path.obligations,
            assumptions,
            &loop_check_obligations,
        );
    }
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();

    let initial_test = match condition {
        None => LoopConditionFeasibility::TrueOnly,
        Some(_) if final_exit_candidates.is_empty() => LoopConditionFeasibility::Both,
        Some(condition) => loop_condition_feasibility(state, condition, assumptions)?,
    };
    let initial_may_continue = initial_test.may_continue();
    let initial_may_exit = initial_test.may_exit();
    let mut paths = Vec::new();
    paths.append(&mut final_exit_paths);
    // Every `return` a checked preservation proof reached is one more way
    // out of the loop, and out of the function: the path's own value and
    // state, under the loop's checks. It is a successor of its own, never a
    // state at which the guard is re-read, so a guard the C never falsifies
    // cannot drop it. Exporting it here is what lets a summarized body's
    // `return` reach contract certification at all.
    for exit in return_exits {
        paths.push(StatementExecutionPath {
            loop_invariant_correspondence: Default::default(),
            call_result: None,
            outcome: StatementOutcome::Return {
                value: exit.value().clone(),
                state: Box::new(head.restored_exit_state(exit.state(), assumptions)),
            },
            facts: exit.pure_facts().certified_facts(),
            obligations: loop_check_obligations.clone(),
            borrow_evidence: exit.borrow_evidence().clone(),
        });
    }
    let public_exit_mode = if exit_fact_scope.is_some() {
        LoopExitFactsMode::Common
    } else {
        LoopExitFactsMode::Legacy
    };
    let guard_exit_mode = if exit_fact_scope.is_some() && otherwise.is_some() {
        LoopExitFactsMode::Otherwise
    } else {
        public_exit_mode
    };
    let mut candidate_exit_entries = Vec::new();
    let mut jump_exit_entries = std::collections::BTreeMap::<_, Vec<_>>::new();
    if initial_may_continue {
        for candidate in final_exit_candidates {
            if let Some(target) = candidate.jump_target() {
                let mut obligations = loop_check_obligations.clone();
                if backedge_target.is_some() && natural_exit_target != Some(target) {
                    obligations.push(
                        ProofObligation::verification_condition(false_equals_true_proposition())
                            .with_context("natural loop exit target"),
                    );
                }
                // This path executed a forward goto. Its successor is the
                // label even when the loop guard is still true.
                jump_exit_entries.entry(target).or_default().push((
                    head.restored_exit_state(candidate.state(), assumptions),
                    candidate.pure_facts().certified_facts(),
                    obligations,
                    candidate.borrow_evidence().clone(),
                    None,
                ));
                continue;
            }
            let candidate_assumptions = candidate.pure_facts().context_with(assumptions);
            let mut exits = Vec::new();
            for assumption in assume_loop_entry_truthiness(
                candidate.state(),
                condition,
                &composite_resource_definitions,
                &candidate_assumptions,
                &[],
                &[],
                false,
                budget,
            )? {
                let candidate_facts = candidate.pure_facts().certified_facts();
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &candidate_facts,
                    &[],
                    &assumption.facts,
                    &assumption.obligations,
                    assumptions,
                ) else {
                    continue;
                };
                // A guard that did not evaluate here decides nothing: this is
                // not an exit, it is a refusal that carries the guard's own
                // outcome.
                if let Some(outcome) = assumption.undecided_outcome() {
                    paths.push(StatementExecutionPath::new(
                        outcome.clone(),
                        facts,
                        obligations,
                    ));
                    continue;
                }
                exits.push(LoopExitFacts::unabstracted(
                    facts,
                    obligations,
                    candidate.borrow_evidence().clone(),
                ));
            }
            if let Some((facts, obligations, borrow_evidence)) =
                join_loop_exit_paths(exits, guard_exit_mode)
            {
                // A candidate is one more way out, not a second successor:
                // it joins the guard-false and `break` exits below on the
                // same terms. Exporting it as its own path would give the
                // loop statement several successors, and for a `do ... while`
                // — whose only guard-false exit is this one, since its guard
                // is read after the body — it is the exit, so dropping it
                // exported no exit state at all and made every post-loop
                // claim vacuous.
                candidate_exit_entries.push((
                    (
                        head.restored_exit_state(candidate.state(), assumptions),
                        facts,
                        obligations,
                        borrow_evidence,
                        None,
                    ),
                    candidate.guard_points_index(),
                ));
            }
        }
    }
    let (invariant_contexts, head_refusal) = assume_invariant_checks_explained(
        &guard_state,
        state,
        invariant_checks,
        &head.iterations,
        assumptions,
        &whole_loop_effect_facts,
        &base_obligations,
        budget,
    )?;
    let mut has_live_iteration = false;
    for (invariant_facts, invariant_obligations, _) in &invariant_contexts {
        if !assume_loop_entry_truthiness(
            &guard_state,
            condition,
            &composite_resource_definitions,
            assumptions,
            invariant_facts,
            invariant_obligations,
            true,
            budget,
        )?
        .is_empty()
        {
            has_live_iteration = true;
            break;
        }
    }
    // Every early iteration exit (break, false test or natural exit) carries
    // the state that path reached. They are certified exits, so they carry no
    // invariant and no measure, and they join the guard-false exit below
    // rather than exporting a second successor the enclosing frontier would
    // have to choose between.
    let mut early_exit_entries = Vec::new();
    let mut otherwise_exits = Vec::new();
    for exit in early_exits.iter().chain(body_early_exits.iter()) {
        let entry = (
            head.restored_exit_state(exit.state(), assumptions),
            exit.pure_facts().certified_facts(),
            loop_check_obligations.clone(),
            exit.borrow_evidence().clone(),
            exit.fact_context().cloned(),
        );
        if otherwise.is_some() && exit.guard_false() {
            otherwise_exits.push((entry, exit.guard_points_index()));
        } else {
            early_exit_entries.push(entry);
        }
    }
    if otherwise.is_some() {
        otherwise_exits.extend(candidate_exit_entries);
    } else {
        early_exit_entries.extend(candidate_exit_entries.into_iter().map(|(exit, _)| exit));
    }
    let mut guard_exits = Vec::new();
    if initial_may_exit {
        for (invariant_facts, invariant_obligations, invariant_propositions) in invariant_contexts {
            let condition_contexts = assume_loop_entry_truthiness(
                &guard_state,
                condition,
                &composite_resource_definitions,
                assumptions,
                &invariant_facts,
                &invariant_obligations,
                false,
                budget,
            )?;
            let mut exits = Vec::new();
            for assumption in condition_contexts {
                let ConditionAssumption {
                    branch,
                    mut facts,
                    mut obligations,
                } = assumption;
                append_required_proof_obligations(
                    &mut obligations,
                    assumptions,
                    &loop_check_obligations,
                );
                // An operand the function has no authority to read leaves the
                // guard undecided. This is not the exit: assuming the
                // negation of the operands that did evaluate would assume
                // strictly less than `!condition`, and the loop would export
                // an exit state the C never reaches that way.
                if let ConditionBranch::Undecided(outcome) = branch {
                    paths.push(StatementExecutionPath::new(outcome, facts, obligations));
                    continue;
                }
                // D7 applied to refutation at the loop exit, the same way the
                // head and the back edge apply it. The invariants and the
                // failed loop condition are the exit's premises, and a
                // premise that contradicts a field-free arm's own fact says
                // the binder's model is not that constructor: an ascending
                // walk learns `ctx.model != Context::Left(..)` from the
                // failed guard `parent != 0` against that arm's
                // `fact parent != 0`, which is what lets the proof after the
                // loop close those arms by contradiction instead of
                // unfolding a frame whose cells the arm does not describe.
                let exit_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
                for fact in crate::kernel::publish_instance_arms(
                    top_state.resources(),
                    &composite_resource_definitions,
                    &top_state,
                    &exit_assumptions,
                )
                .model_facts
                {
                    facts.push(ExecutionPureFact::new(fact));
                }
                exits.push((facts, obligations, empty_checked_borrow_evidence_sequence()));
            }
            // A short-circuit guard leaves the loop by one path per conjunct,
            // all at the same exit state. Every one of them is certified, and
            // the loop exports their join: what they all state, plus the
            // disjunction of what each states alone. A `break` exit joins
            // here too, on the same terms.
            let exits = exits
                .into_iter()
                .map(|(facts, obligations, borrow_evidence)| {
                    (top_state.clone(), facts, obligations, borrow_evidence, None)
                });
            if otherwise.is_some() {
                otherwise_exits.extend(exits.map(|exit| (exit, None)));
                continue;
            }
            if exit_fact_scope.is_some() {
                guard_exits.extend(exits);
                continue;
            }
            let exits = exits.chain(early_exit_entries.iter().cloned()).collect();
            if let Some(path) = join_loop_exits(
                &head,
                body,
                &invariant_propositions,
                &binders,
                exits,
                assumptions,
                None,
                LoopExitFactsMode::Legacy,
                variables,
                budget,
            ) {
                paths.push(path);
            }
        }
    } else if otherwise.is_none()
        && exit_fact_scope.is_none()
        && let Some(path) = join_loop_exits(
            &head,
            body,
            &Default::default(),
            &binders,
            std::mem::take(&mut early_exit_entries),
            assumptions,
            None,
            LoopExitFactsMode::Legacy,
            variables,
            budget,
        )
    {
        // A guard that cannot be false, `while (true)`, has no guard-false
        // exit: the successor is the join of the `break` exits alone.
        paths.push(path);
    }
    let had_otherwise = otherwise.is_some();
    if let Some(prove) = otherwise {
        // An otherwise block has one entry, even when different operands of
        // a short-circuit guard can make it false. Keep breaks out of this
        // frontier and join them only after checking the block.
        let false_exit = if otherwise_exits.len() <= 1 {
            otherwise_exits.pop()
        } else {
            join_loop_exits(
                &head,
                body,
                &Default::default(),
                &binders,
                otherwise_exits.into_iter().map(|(exit, _)| exit).collect(),
                assumptions,
                None,
                guard_exit_mode,
                variables,
                budget,
            )
            .map(|path| {
                let StatementOutcome::Normal(state) = path.outcome else {
                    unreachable!("the loop-exit join produces a normal outcome");
                };
                (
                    (
                        *state,
                        path.facts,
                        path.obligations,
                        path.borrow_evidence,
                        None,
                    ),
                    None,
                )
            })
        };
        if let Some(((state, mut facts, mut obligations, evidence, _), points_index)) = false_exit {
            let proven = prove(&head.entry, &state, &facts, points_index);
            if guard_exit_mode == LoopExitFactsMode::Otherwise {
                facts = facts.filtered(ExecutionPureFact::is_public);
            }
            if let Some(proven) = proven {
                facts.extend(proven);
            } else {
                obligations.push(
                    ProofObligation::verification_condition(false_equals_true_proposition())
                        .with_context("loop otherwise proof failed"),
                );
            }
            early_exit_entries.insert(0, (state, facts, obligations, evidence, None));
        }
    }
    if (had_otherwise || exit_fact_scope.is_some())
        && let Some(path) = join_loop_exits(
            &head,
            body,
            &Default::default(),
            &binders,
            guard_exits.into_iter().chain(early_exit_entries).collect(),
            assumptions,
            exit_fact_scope,
            public_exit_mode,
            variables,
            budget,
        )
    {
        paths.push(path);
    }
    // Several checked edges to one label have one successor. Preserve
    // their disjunction and abstract differing states by the same checked
    // join used for break exits, then retain the label on that successor.
    for (target, exits) in jump_exit_entries {
        if let Some(mut path) = join_loop_exits(
            &head,
            body,
            &Default::default(),
            &binders,
            exits,
            assumptions,
            exit_fact_scope,
            public_exit_mode,
            variables,
            budget,
        ) {
            let StatementOutcome::Normal(state) = path.outcome else {
                unreachable!("loop exit join returns a normal state")
            };
            path.outcome = StatementOutcome::Jump { target, state };
            paths.push(path);
        }
    }
    if paths.is_empty() {
        let mut obligations = base_obligations;
        append_required_proof_obligations(&mut obligations, assumptions, &loop_check_obligations);
        if !has_live_iteration {
            let context = match &head_refusal {
                Some(refusal) => format!(
                    "loop has neither a safe exit nor a safe iteration: {}",
                    refusal.describe()
                ),
                None => "loop has neither a safe exit nor a safe iteration".to_string(),
            };
            obligations.push(
                ProofObligation::verification_condition(false_equals_true_proposition())
                    .with_context(context),
            );
        }
        paths.push(StatementExecutionPath::new(
            StatementOutcome::VerificationDiverges,
            whole_loop_effect_facts.into(),
            obligations,
        ));
    }
    budget.check_path_width(paths.len())?;
    // Every exit follows the iterations that returned to a head; record
    // what they wrote where each exit's history can see it. A kernel-checked
    // body gave its back edges above; a proof-checked body's come with it.
    let mut iterations = Vec::new();
    if let Some(head_point) = head.top.path_link().loop_head()
        && let Some(writes) = iteration_writes
    {
        iterations.push((head_point, Some(std::sync::Arc::new(writes))));
    }
    for proof in back_edges {
        let Some(head_point) = proof.head.body.path_link().loop_head() else {
            continue;
        };
        let writes = proof.states.iter().try_fold(
            crate::kernel::RecordedWrites::default(),
            |mut writes, state| {
                let mut reached = state.clone();
                reached.complete_staged_memory();
                writes.merge(&crate::kernel::RecordedWrites::between(
                    proof.head.body.path_link(),
                    reached.path_link(),
                )?);
                Some(writes)
            },
        );
        iterations.push((head_point, writes.map(std::sync::Arc::new)));
    }
    for path in &mut paths {
        path.obligations
            .extend(head.borrow_requirements.iter().cloned());
        path.loop_invariant_correspondence.iterations = Some(head.iterations.clone());
        if let Some(state) = path.outcome.state_mut() {
            for (head_point, writes) in &iterations {
                state.record_loop_iterations(crate::kernel::program_point::LoopIterations::new(
                    *head_point,
                    writes.clone(),
                ));
            }
        }
    }
    Ok(paths)
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum InvariantPhase {
    Entry,
    Preservation,
}

pub(super) fn invariant_context(check: &LoopInvariantCheck, phase: InvariantPhase) -> Option<&str> {
    match phase {
        InvariantPhase::Entry => check.entry_context(),
        InvariantPhase::Preservation => check.preservation_context(),
    }
}

/// Why a stated range was pruned as a byte span, in the terms the reader
/// wrote it in: an element count and a width.
fn dropped_range_span_reason(span: &crate::kernel::DroppedRangeSpan) -> String {
    if span.element_count < 0 {
        let count = -span.element_count;
        let elements = if count == 1 { "element" } else { "elements" };
        format!(
            "a memory range it states runs backwards, so it is not a byte span: its end is {count} {elements} before its start"
        )
    } else {
        format!(
            "a memory range it states is too wide to be a 32-bit byte span: {} elements of {} bytes is past the {}-byte limit",
            span.element_count, span.element_width, span.byte_limit
        )
    }
}

pub(super) fn collect_invariant_check_obligations(
    state: &ExecutionState,
    loop_entry_state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    phase: InvariantPhase,
    head_iterations: Option<&IntegerTerm>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    collect_invariant_check_obligations_with_mode(
        state,
        loop_entry_state,
        invariant_checks,
        phase,
        head_iterations,
        assumptions,
        budget,
        false,
        None,
    )
}

pub(super) fn collect_invariant_check_obligations_without_search(
    state: &ExecutionState,
    loop_entry_state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    phase: InvariantPhase,
    head_iterations: Option<&IntegerTerm>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    collect_invariant_check_obligations_with_mode(
        state,
        loop_entry_state,
        invariant_checks,
        phase,
        head_iterations,
        assumptions,
        budget,
        true,
        None,
    )
}

/// Collects every declaration's exact lowered goals before outstanding-obligation
/// filtering. Equal or already-known goals retain their declaration positions.
pub(super) fn collect_loop_entry_goals(
    state: &ExecutionState,
    checks: &[LoopInvariantCheck],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    declarations: &mut [Vec<ProofObligation>],
) -> ExecutionResult<Vec<ProofObligation>> {
    collect_invariant_check_obligations_with_mode(
        state,
        state,
        checks,
        InvariantPhase::Entry,
        None,
        assumptions,
        budget,
        true,
        Some(declarations),
    )
}

#[allow(clippy::too_many_arguments)]
fn collect_invariant_check_obligations_with_mode(
    state: &ExecutionState,
    loop_entry_state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    phase: InvariantPhase,
    head_iterations: Option<&IntegerTerm>,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    without_search: bool,
    mut declarations: Option<&mut [Vec<ProofObligation>]>,
) -> ExecutionResult<Vec<ProofObligation>> {
    // `iterations` counts the passes completed: none at entry, and at a back
    // edge one more than the head the pass started from.
    let iterations = match (phase, head_iterations) {
        (InvariantPhase::Entry, None) => IntegerTerm::constant(0.into()),
        (InvariantPhase::Preservation, Some(head)) => {
            IntegerTerm::add(head.clone(), IntegerTerm::constant(1.into()))
        }
        _ => return Err(ExecutionLimit::LoopIterationsUnbound),
    };
    let _iterations = crate::kernel::spec::LoopIterationsScope::enter(iterations);
    // Each context carries, beside its facts and obligations, the guards a
    // later declaration is wrapped with: the same list position for position,
    // except that an earlier declaration's own entry is its lowered
    // proposition rather than the member that proposition was wrapped into.
    // The member's guards are a prefix of every later member's guards, so the
    // bare proposition is equivalent there, and guarding with the wrapped
    // member instead would nest every earlier member inside every later one,
    // doubling the bundle with each declaration.
    let mut contexts = vec![(
        ExecutionFacts::new(),
        Vec::new(),
        Vec::<ProofObligation>::new(),
        assumptions.clone(),
    )];
    let mut all_obligations = Vec::new();
    for (declaration_index, check) in invariant_checks.iter().enumerate() {
        let mut next_contexts = Vec::new();
        for (facts, obligations, guards, prepared_assumptions) in contexts {
            let context_timing = crate::instrumentation::OperationTiming::new(
                "kernel",
                "loop invariant bundle",
                "invariant obligations: extend path context",
            );
            let effective_assumptions = if without_search {
                prepared_assumptions
                    .clone()
                    .defer_non_exact_condition_reasoning()
                    .defer_non_exact_loadability_obligations()
            } else {
                assumptions_with_path_context(assumptions, &facts, &obligations)
            };
            drop(context_timing);
            let declaration_timing = crate::instrumentation::OperationTiming::new(
                "kernel",
                "loop invariant bundle",
                "invariant obligations: lower declaration",
            );
            let dropped_span_before = budget.dropped_range_span().is_some();
            let paths = lower_spec_proposition_at_state_with_loop_entry(
                state,
                check.proposition(),
                Some(loop_entry_state),
                &effective_assumptions,
                budget,
            )?;
            drop(declaration_timing);
            // A declaration with no reading at this state owes the
            // impossible goal, never nothing. Lowering prunes a path whose
            // obligation it already decides false — a stated range whose
            // span is reversed or too wide, for one — so an empty result
            // means the invariant does not hold here. Owing nothing would
            // let the head assume a hypothesis nobody proved: the head
            // assumes a stated range's span half as content.
            if paths.is_empty() {
                let reason = if !dropped_span_before && let Some(span) = budget.dropped_range_span()
                {
                    dropped_range_span_reason(span)
                } else {
                    "a condition it owes is already decided false at this state".to_string()
                };
                let context = invariant_context(check, phase).unwrap_or("loop invariant");
                let goal = ProofObligation::verification_condition(false_equals_true_proposition())
                    .with_context(format!(
                        "{context}: this invariant cannot hold here: {reason}"
                    ));
                if let Some(declarations) = declarations.as_deref_mut() {
                    declarations[declaration_index].push(goal.clone());
                }
                append_required_proof_obligations(&mut all_obligations, assumptions, &[goal]);
                next_contexts.push((facts, obligations, guards, prepared_assumptions));
                continue;
            }
            for path in paths {
                let merge_timing = crate::instrumentation::OperationTiming::new(
                    "kernel",
                    "loop invariant bundle",
                    "invariant obligations: merge declaration path",
                );
                let merged = if without_search {
                    merge_prepared_execution_path(
                        &facts,
                        &obligations,
                        &path.facts,
                        &path.obligations,
                        assumptions,
                        &prepared_assumptions,
                        &effective_assumptions,
                    )
                } else {
                    merge_execution_pure_facts_and_obligations(
                        &facts,
                        &obligations,
                        &path.facts,
                        &path.obligations,
                        assumptions,
                    )
                    .map(|(facts, obligations)| PreparedExecutionPath {
                        assumptions: assumptions_with_path_context(
                            assumptions,
                            &facts,
                            &obligations,
                        ),
                        facts,
                        changed_obligations: (0..obligations.len()).collect(),
                        obligations,
                    })
                };
                let Some(PreparedExecutionPath {
                    facts,
                    mut obligations,
                    assumptions: mut obligation_assumptions,
                    mut changed_obligations,
                }) = merged
                else {
                    continue;
                };
                drop(merge_timing);
                let retain_timing = crate::instrumentation::OperationTiming::new(
                    "kernel",
                    "loop invariant bundle",
                    "invariant obligations: retain required members",
                );
                // `merge` keeps the earlier obligations as a prefix and
                // appends this path's own; those are their own guards.
                let mut guards = guards.clone();
                let side_conditions = obligations.iter().skip(guards.len()).cloned();
                // This path's own side conditions are invariant content: the
                // head assumes them (`assume_invariant_checks`), so the entry
                // owes each as a judgment of its own, exactly as the back
                // edge's bundle carries each as a member. Wrapping them only
                // as antecedents of the declaration's goal would let a proved
                // entry owe nothing for them.
                if let Some(declarations) = declarations.as_deref_mut() {
                    for side_condition in side_conditions.clone() {
                        let mut goal = side_condition;
                        if let Some(context) = invariant_context(check, phase) {
                            goal = goal.with_context(context);
                        }
                        declarations[declaration_index].push(goal);
                    }
                }
                guards.extend(side_conditions);
                // The guards this wrap inserts, then the head chain the
                // invariant's own lowering recorded: one record for the
                // obligation proposition, produced by the same wrap that
                // built it, so a consumer introducing its head never pairs
                // a hidden guard with a written connective.
                let (proposition, guard_introductions) =
                    wrap_path_context_with_introductions(path.proposition.clone(), &facts, &guards);
                let mut introductions = guard_introductions;
                introductions.extend(path.introductions.iter().cloned());
                let introductions = std::sync::Arc::new(introductions);
                if let Some(declarations) = declarations.as_deref_mut() {
                    let mut goal = ProofObligation::new(proposition.clone())
                        .with_shared_introductions(Some(&introductions));
                    if let Some(context) = invariant_context(check, phase) {
                        goal = goal.with_context(context);
                    }
                    declarations[declaration_index].push(goal);
                }
                let before = obligations.len();
                if without_search {
                    add_required_proof_obligation_without_search(
                        &mut obligations,
                        &obligation_assumptions,
                        proposition,
                        invariant_context(check, phase),
                        Some(&introductions),
                    );
                } else {
                    add_required_proof_obligation_with_context(
                        &mut obligations,
                        &obligation_assumptions,
                        proposition,
                        invariant_context(check, phase),
                        Some(&introductions),
                    );
                    append_required_proof_obligations(
                        &mut all_obligations,
                        assumptions,
                        &obligations,
                    );
                }
                if obligations.len() > before {
                    guards.push(ProofObligation::new(path.proposition.clone()));
                    changed_obligations.push(before);
                    if without_search && obligations[before].is_assumable() {
                        crate::kernel::reasoning::path_facts::count_context_rebuild_entries(1);
                        // All preceding members are hypotheses of this prepared
                        // path. Admit the new bare member, as the guard list
                        // above does, rather than regenerating its implication
                        // prefix and every partially discharged suffix.
                        obligation_assumptions =
                            obligation_assumptions.assume_proposition(path.proposition);
                    }
                }
                if without_search {
                    // Only this fragment's canonical delta is new to the
                    // collected bundle. A replaced source tuple is included
                    // even when its position precedes this fragment's tail.
                    for index in changed_obligations {
                        append_required_proof_obligations_without_search(
                            &mut all_obligations,
                            assumptions,
                            std::slice::from_ref(&obligations[index]),
                        );
                    }
                }
                next_contexts.push((facts, obligations, guards, obligation_assumptions));
                drop(retain_timing);
            }
        }
        contexts = next_contexts;
    }
    Ok(all_obligations)
}

/// The back-edge ranking members of a ranked loop's invariant bundle.
///
/// Membership order is fixed so a retained certificate is stable across runs
/// and sites: one `0 <= component` obligation per declared component at the
/// back edge, in declaration order, then exactly one decrease obligation.
/// The decrease obligation is `post < pre` for a single component; for a
/// tuple it is the right-nested disjunction over pivots
/// `(post0 < pre0) or ((post0 == pre0) and (post1 < pre1)) or ...`, so the
/// pivot is an ordinary arm choice a proof makes with `left` and `right` and
/// expansion prints, rather than a kernel search over pivot indices.
///
/// `pre` reads each component at the iteration entry and `post` at the back
/// edge. Work is linear in the declared measure; no ambient fact is scanned.
///
/// A measure that reads memory has each read evaluated at both states by the
/// expression evaluator, under `assumptions`, as an invariant about the same
/// cell is. What those reads owe, their loadability, comes first and only
/// where it is not already an exact fact, so a measure over locals alone, or
/// over cells the context already shows loadable, has exactly the members
/// above.
pub(super) fn collect_loop_ranking_obligations(
    state: &ExecutionState,
    iteration_entry_state: &ExecutionState,
    head_iterations: Option<&IntegerTerm>,
    ranking_measures: &[RankingComponent],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Result<Vec<ProofObligation>, String> {
    if ranking_measures.is_empty() {
        return Ok(Vec::new());
    }
    let mut reader = crate::kernel::termination::RankingMeasureReader {
        assumptions,
        budget,
        reads: Default::default(),
    };
    let mut pre = Vec::with_capacity(ranking_measures.len());
    let mut post = Vec::with_capacity(ranking_measures.len());
    // A measure may read the loop's pass count `iterations`: the head's `K`
    // where the pass starts, and `K + 1` at its back edge.
    let scope =
        |count: Option<IntegerTerm>| count.map(crate::kernel::spec::LoopIterationsScope::enter);
    for measure in ranking_measures {
        let entry = scope(head_iterations.cloned());
        pre.push(crate::kernel::termination::ranking_measure_term(
            measure,
            iteration_entry_state,
            &mut reader,
        )?);
        drop(entry);
        let _back_edge = scope(
            head_iterations
                .map(|head| IntegerTerm::add(head.clone(), IntegerTerm::constant(1.into()))),
        );
        post.push(crate::kernel::termination::ranking_measure_term(
            measure,
            state,
            &mut reader,
        )?);
    }
    let reads = reader.reads;
    let read_assumptions = assumptions_with_path_context(assumptions, &reads.facts, &[]);
    let mut obligations = Vec::with_capacity(ranking_measures.len() + 1);
    for obligation in &reads.obligations {
        add_required_proof_obligation_without_search(
            &mut obligations,
            &read_assumptions,
            obligation.proposition().clone(),
            Some("a loop ranking measure's read is viewable"),
            None,
        );
    }
    for (measure, post) in ranking_measures.iter().zip(post.iter()) {
        obligations.push(
            ProofObligation::verification_condition(
                crate::kernel::termination::ranking_nonnegative_proposition(post),
            )
            // A ranking member is one condition read from the declared
            // measure: no lowering wrapped it, so its recorded chain is
            // empty. Recording that keeps the bundle's member records
            // aligned with its members.
            .with_introductions(LoweringIntroductions::new())
            .with_context(format!(
                "loop ranking component `{}` is nonnegative at the back edge",
                crate::kernel::termination::ranking_measure_display(measure)
            )),
        );
    }
    let decrease = crate::kernel::termination::ranking_lexicographic_decrease_proposition(
        &post,
        &pre,
        ranking_measures,
    )?;
    obligations.push(
        ProofObligation::verification_condition(decrease)
            .with_introductions(LoweringIntroductions::new())
            .with_context(format!(
                "loop ranking measure `{}` decreases at the back edge",
                crate::kernel::termination::ranking_measures_display(ranking_measures)
            )),
    );
    Ok(obligations)
}

/// The ranking members, or one refusal obligation naming why the declared
/// measure has no value at this state. A measure that does not read as a
/// scalar int32 expression is a proof failure at the loop, never a silently
/// dropped ranking obligation.
pub(super) fn loop_ranking_obligations_or_refusal(
    state: &ExecutionState,
    iteration_entry_state: &ExecutionState,
    head_iterations: &IntegerTerm,
    ranking_measures: &[RankingComponent],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> Vec<ProofObligation> {
    match collect_loop_ranking_obligations(
        state,
        iteration_entry_state,
        Some(head_iterations),
        ranking_measures,
        assumptions,
        budget,
    ) {
        Ok(obligations) => obligations,
        Err(message) => vec![
            ProofObligation::verification_condition(false_equals_true_proposition())
                .with_context(message),
        ],
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct LoopPreservationSummary {
    pub(super) obligations: Vec<ProofObligation>,
    pub(super) final_exit_paths: Vec<StatementExecutionPath>,
    /// The body paths that left through `break`, as exits at the states they
    /// reached. The rule joins them with the guard-false exit exactly as it
    /// joins the ones a checked preservation proof reports.
    pub(super) early_exits: Vec<LoopEarlyExit>,
    /// What the body wrote on its paths back to the head: the writes of the
    /// iterations that reach no exit. `None` when some such path does not
    /// record them.
    pub(super) iteration_writes: Option<crate::kernel::RecordedWrites>,
}

pub(super) fn collect_loop_preservation_summary(
    loop_entry_state: &ExecutionState,
    head: &LoopHead,
    program_loop: LoopExecutionView<'_>,
    composite_resource_definitions: &[CompositeResourceDefinition],
    whole_loop_effect_summaries: &[Proposition],
    assumptions: &PureFactContext,
    execution_context: ExecutionContext<'_>,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<LoopPreservationSummary> {
    let LoopExecutionView {
        entry_guard: condition,
        invariant_checks,
        effect_checks,
        resource_specs,
        ranking_measures,
        structural_measure,
        body,
        update,
        test,
        backedge_target,
        natural_exit_target,
        ..
    } = program_loop;
    let mut obligations = Vec::new();
    let mut final_exit_paths = Vec::new();
    let mut early_exits = Vec::new();
    let mut iteration_writes = Some(crate::kernel::RecordedWrites::default());
    // The body executes from the loop's own resource context; everything the
    // enclosing frame withheld is returned on the way out.
    let top_state = &head.body;
    let binders = loop_binders(resource_specs);
    let whole_loop_effect_facts = whole_loop_effect_summaries
        .iter()
        .cloned()
        .map(ExecutionPureFact::new)
        .collect::<Vec<_>>();
    for (invariant_facts, invariant_obligations, _) in assume_invariant_checks(
        top_state,
        loop_entry_state,
        invariant_checks,
        &head.iterations,
        assumptions,
        &whole_loop_effect_facts,
        &[],
        budget,
    )? {
        let condition_contexts = assume_loop_entry_truthiness(
            top_state,
            condition,
            composite_resource_definitions,
            assumptions,
            &invariant_facts,
            &invariant_obligations,
            true,
            budget,
        )?;
        for assumption in condition_contexts {
            // The body cannot run from a guard that produced no value: this
            // iteration is not entered, it is unproven. Refuse it here rather
            // than letting the iteration disappear from the rule.
            if let Some(outcome) = assumption.undecided_outcome() {
                obligations.push(
                    ProofObligation::verification_condition(false_equals_true_proposition())
                        .with_context(undecided_loop_guard_context(outcome)),
                );
                continue;
            }
            let ConditionAssumption {
                facts: condition_facts,
                obligations: condition_obligations,
                ..
            } = assumption;
            for body_path in super::eval::execute_loop_iteration_paths(
                top_state,
                test.preservation_phase(),
                body,
                update,
                test,
                assumptions,
                execution_context,
                &condition_facts,
                &condition_obligations,
                budget,
                &mut super::eval::StatementJudgment::Verifies(variables),
            )? {
                let outcome = body_path.outcome;
                let natural_backedge = matches!(
                    &outcome,
                    StatementOutcome::Jump { target, .. }
                        if backedge_target == Some(*target)
                );
                if matches!(
                    &outcome,
                    StatementOutcome::Normal(_) | StatementOutcome::Continue(_)
                ) || natural_backedge
                {
                    let next_state = match outcome {
                        StatementOutcome::Normal(state)
                        | StatementOutcome::Continue(state)
                        | StatementOutcome::Jump { state, .. } => state,
                        _ => unreachable!("classified loop back edge has another outcome"),
                    };
                    // This iteration returns to the head, so no exit's path
                    // holds its writes: read them from its own history.
                    let mut reached = (*next_state).clone();
                    reached.complete_staged_memory();
                    iteration_writes = iteration_writes.and_then(|mut writes| {
                        writes.merge(&crate::kernel::RecordedWrites::between(
                            top_state.path_link(),
                            reached.path_link(),
                        )?);
                        Some(writes)
                    });
                    // The back edge binds the loop's names again exactly as
                    // the head did. A body that refolded its instance under
                    // another name still hands the binder back, and a body
                    // that ends with no instance at those arguments fails
                    // here, named.
                    let back_edge_assumptions = assumptions_with_path_context(
                        assumptions,
                        &body_path.facts,
                        &body_path.obligations,
                    );
                    let (next_state, binder_failure) = match loop_state_with_loop_binders_rebound(
                        top_state,
                        &next_state,
                        &binders,
                        &back_edge_assumptions,
                    ) {
                        Ok(rebound) => (rebound, None),
                        Err(failure) => (*next_state, Some(failure)),
                    };
                    // Both back-edge directions come from one evaluation
                    // of the guard, so a path the guard did not decide is
                    // reported once instead of twice.
                    let condition_contexts = assume_loop_entry_branches(
                        &next_state,
                        condition,
                        composite_resource_definitions,
                        assumptions,
                        &body_path.facts,
                        &body_path.obligations,
                        budget,
                    )?;
                    for assumption in condition_contexts {
                        // Neither the back edge nor the exit is taken
                        // when the guard produced no value; the loop
                        // rule cannot certify this edge at all.
                        if let Some(outcome) = assumption.undecided_outcome() {
                            obligations.push(
                                ProofObligation::verification_condition(
                                    false_equals_true_proposition(),
                                )
                                .with_context(undecided_loop_guard_context(outcome)),
                            );
                            continue;
                        }
                        let ConditionAssumption {
                            branch,
                            facts: condition_facts,
                            obligations: condition_obligations,
                        } = assumption;
                        let guard = match branch {
                            ConditionBranch::Decided(true) => LoopConditionFeasibility::TrueOnly,
                            ConditionBranch::Decided(false) => LoopConditionFeasibility::FalseOnly,
                            ConditionBranch::Undecided(_) => {
                                unreachable!("undecided guard was handled")
                            }
                        };
                        let may_continue = guard.may_continue();
                        let path_assumptions = assumptions_with_path_context(
                            assumptions,
                            &condition_facts,
                            &condition_obligations,
                        );
                        let effect_obligations = collect_loop_effect_check_obligations(
                            top_state,
                            &next_state,
                            effect_checks,
                            &condition_facts,
                            &condition_obligations,
                            assumptions,
                            budget,
                        )?;
                        let mut path_obligations = {
                            collect_invariant_check_obligations(
                                &next_state,
                                loop_entry_state,
                                invariant_checks,
                                InvariantPhase::Preservation,
                                Some(&head.iterations),
                                &path_assumptions,
                                budget,
                            )?
                        };
                        path_obligations.extend(loop_ranking_obligations_or_refusal(
                            &next_state,
                            top_state,
                            &head.iterations,
                            guard.required_ranking_measures(ranking_measures),
                            &path_assumptions,
                            budget,
                        ));
                        if may_continue {
                            // A structural measure is not a ranking
                            // member: the kernel decides the descent
                            // here and reports a refusal obligation
                            // naming the binder when it does not hold.
                            if let Some(measure) = structural_measure
                                && let Some(failure) = loop_structural_descent_failure(
                                    top_state,
                                    &next_state,
                                    &binders,
                                    measure,
                                    composite_resource_definitions,
                                    &path_assumptions,
                                )
                            {
                                path_obligations.push(
                                    ProofObligation::verification_condition(
                                        false_equals_true_proposition(),
                                    )
                                    .with_context(failure),
                                );
                            }
                        }
                        let mut state_obligations = condition_obligations.clone();
                        // A binder the body did not hand back is the
                        // whole verdict for this edge; the ownership
                        // join would only repeat it less precisely.
                        let join_failure = if !may_continue {
                            None
                        } else if let Some(failure) = &binder_failure {
                            Some(failure.clone())
                        } else {
                            loop_binder_state_components_match_at_back_edge(
                                top_state,
                                &next_state,
                                &binders,
                                &path_assumptions,
                                composite_resource_definitions,
                            )
                            .err()
                        };
                        if let Some(message) = join_failure {
                            state_obligations.push(
                                ProofObligation::verification_condition(
                                    false_equals_true_proposition(),
                                )
                                .with_context(message),
                            );
                        }
                        append_required_proof_obligations(
                            &mut obligations,
                            assumptions,
                            &state_obligations,
                        );
                        append_required_proof_obligations_under_path_context(
                            &mut obligations,
                            assumptions,
                            &effect_obligations,
                            &condition_facts,
                            &condition_obligations,
                        );
                        append_required_proof_obligations_under_path_context(
                            &mut obligations,
                            assumptions,
                            &path_obligations,
                            &condition_facts,
                            &condition_obligations,
                        );
                        if !may_continue {
                            let final_path_facts = condition_facts.clone();
                            let final_path_obligations = condition_obligations.clone();
                            let mut final_obligations = condition_obligations;
                            append_required_proof_obligations_under_path_context(
                                &mut final_obligations,
                                assumptions,
                                &effect_obligations,
                                &final_path_facts,
                                &final_path_obligations,
                            );
                            append_required_proof_obligations_under_path_context(
                                &mut final_obligations,
                                assumptions,
                                &path_obligations,
                                &final_path_facts,
                                &final_path_obligations,
                            );
                            final_exit_paths.push(StatementExecutionPath {
                                loop_invariant_correspondence: Default::default(),
                                call_result: None,
                                outcome: StatementOutcome::Normal(Box::new(
                                    head.restored_exit_state(&next_state, assumptions),
                                )),
                                facts: final_path_facts,
                                obligations: final_obligations,
                                borrow_evidence: body_path.borrow_evidence.clone(),
                            });
                        }
                    }
                } else {
                    match outcome {
                        StatementOutcome::LoopTestFalse(next_state)
                        | StatementOutcome::Break(next_state) => {
                            // A written break or false test exits: invariants are not
                            // closed on it and no measure is required to
                            // decrease on it. What the body wrote on the way
                            // out is still checked against the loop's declared
                            // effects, and the path itself becomes one of the
                            // exits the rule joins into the loop's successor.
                            let effect_obligations = collect_loop_effect_check_obligations(
                                top_state,
                                &next_state,
                                effect_checks,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                                budget,
                            )?;
                            let exit_facts = body_path.facts;
                            let exit_obligations = body_path.obligations;
                            let borrow_evidence = body_path.borrow_evidence;
                            append_required_proof_obligations(
                                &mut obligations,
                                assumptions,
                                &exit_obligations,
                            );
                            append_required_proof_obligations_under_path_context(
                                &mut obligations,
                                assumptions,
                                &effect_obligations,
                                &exit_facts,
                                &exit_obligations,
                            );
                            early_exits.push(
                                LoopEarlyExit::new(
                                    *next_state,
                                    exit_facts
                                        .iter()
                                        .map(|fact| fact.proposition().clone())
                                        .collect(),
                                )
                                .with_borrow_evidence(borrow_evidence),
                            );
                        }
                        StatementOutcome::Return { value, state } if backedge_target.is_some() => {
                            let effect_obligations = collect_loop_effect_check_obligations(
                                top_state,
                                &state,
                                effect_checks,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                                budget,
                            )?;
                            let exit_facts = body_path.facts;
                            let exit_obligations = body_path.obligations;
                            let mut final_obligations = exit_obligations.clone();
                            append_required_proof_obligations_under_path_context(
                                &mut final_obligations,
                                assumptions,
                                &effect_obligations,
                                &exit_facts,
                                &exit_obligations,
                            );
                            final_exit_paths.push(StatementExecutionPath {
                                loop_invariant_correspondence: Default::default(),
                                call_result: None,
                                outcome: StatementOutcome::Return {
                                    value,
                                    state: Box::new(head.restored_exit_state(&state, assumptions)),
                                },
                                facts: exit_facts,
                                obligations: final_obligations,
                                borrow_evidence: body_path.borrow_evidence,
                            });
                        }
                        StatementOutcome::Jump { target, state }
                            if backedge_target.is_none() || natural_exit_target == Some(target) =>
                        {
                            let effect_obligations = collect_loop_effect_check_obligations(
                                top_state,
                                &state,
                                effect_checks,
                                &body_path.facts,
                                &body_path.obligations,
                                assumptions,
                                budget,
                            )?;
                            let exit_facts = body_path.facts;
                            let exit_obligations = body_path.obligations;
                            let mut final_obligations = exit_obligations.clone();
                            append_required_proof_obligations_under_path_context(
                                &mut final_obligations,
                                assumptions,
                                &effect_obligations,
                                &exit_facts,
                                &exit_obligations,
                            );
                            final_exit_paths.push(StatementExecutionPath {
                                loop_invariant_correspondence: Default::default(),
                                call_result: None,
                                outcome: StatementOutcome::Jump {
                                    target,
                                    state: Box::new(head.restored_exit_state(&state, assumptions)),
                                },
                                facts: exit_facts,
                                obligations: final_obligations,
                                borrow_evidence: body_path.borrow_evidence,
                            });
                        }
                        StatementOutcome::Return { .. }
                        | StatementOutcome::Normal(_)
                        | StatementOutcome::Continue(_)
                        | StatementOutcome::Throw { .. }
                        | StatementOutcome::Jump { .. }
                        | StatementOutcome::VerificationDiverges
                        | StatementOutcome::UndefinedBehavior(_)
                        | StatementOutcome::RuntimeError(_) => {
                            let mut path_obligations = body_path.obligations;
                            path_obligations.push(
                                ProofObligation::verification_condition(
                                    false_equals_true_proposition(),
                                )
                                .with_context("loop preservation body safety"),
                            );
                            append_required_proof_obligations(
                                &mut obligations,
                                assumptions,
                                &path_obligations,
                            );
                        }
                    }
                }
            }
        }
    }
    Ok(LoopPreservationSummary {
        obligations,
        final_exit_paths,
        early_exits,
        iteration_writes,
    })
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) struct EvaluatedMemorySegment {
    pub(super) base: Address,
    pub(super) provenance: Address,
    /// The array object of the pointer that names the segment, without
    /// bounds of its own.
    pub(super) carrier: crate::kernel::primitives::ArrayObject,
    pub(super) start: OldMachineTerm,
    pub(super) end: OldMachineTerm,
    pub(super) element_width: u32,
    pub(super) kind: RangeIndexKind,
    pub(super) formation_coverage: std::sync::Arc<[Proposition]>,
}

impl EvaluatedMemorySegment {
    /// The range this segment denotes, in its own index kind.
    pub(super) fn into_range(self) -> MemoryRange {
        let provenance = self.provenance;
        let range = match self.kind {
            RangeIndexKind::Int32 => MemoryRange::new_with_element_width(
                self.base,
                self.start,
                self.end,
                self.element_width,
            ),
            RangeIndexKind::UInt64 => {
                MemoryRange::new_wide(self.base, self.start, self.end, self.element_width)
            }
        };
        let mut range = range;
        range.formation_coverage = self.formation_coverage;
        range
            .with_provenance(provenance)
            .with_carrier_array(self.carrier)
            .with_typed_carrier()
    }
}

fn evaluate_whole_loop_effect_ranges(
    before_state: &ExecutionState,
    effect_checks: &[LoopEffectCheck],
    include_mutable_summaries: bool,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(Vec<Vec<MemoryRange>>, bool)> {
    let mut ranges_by_summary = Vec::new();
    let mut all_ranges_evaluable = true;
    for check in effect_checks {
        if check.span() != LoopEffectSpan::Whole {
            continue;
        }

        let ranges = match check.effect() {
            // A mutable clause is an upper bound. Without a memory-writing
            // body, it is not evidence of mutation and should not block an
            // enclosing immutable claim.
            LoopEffect::Mutable(_) if !include_mutable_summaries => continue,
            LoopEffect::Mutable(segments) => {
                if let Some(validated) = check.validated_ranges() {
                    ranges_by_summary.push(validated.to_vec());
                    continue;
                }
                if matches!(
                    check.origin(),
                    LoopEffectOrigin::InheritedResourceDerived | LoopEffectOrigin::DeclaredResource
                ) {
                    // A resource-derived frame carries no segments of its
                    // own: it is authoritative only once the checked entry
                    // transition (for an inherited frame) or the loop's
                    // entry evaluation (for a declared one) has installed
                    // fixed ranges.
                    all_ranges_evaluable = false;
                    continue;
                }
                let mut ranges = Vec::new();
                let mut failed = false;
                for segment in segments {
                    let element_width = segment.element_width;
                    match evaluate_loop_effect_segment(before_state, segment, assumptions, budget)?
                    {
                        Ok(segment) => ranges.push(MemoryRange::new_with_element_width(
                            segment.base,
                            segment.start,
                            segment.end,
                            element_width,
                        )),
                        Err(_) => {
                            failed = true;
                            break;
                        }
                    }
                }
                if failed {
                    all_ranges_evaluable = false;
                    continue;
                }
                ranges
            }
        };
        ranges_by_summary.push(ranges);
    }
    Ok((ranges_by_summary, all_ranges_evaluable))
}

pub(super) fn collect_whole_loop_effect_summaries(
    before_state: &ExecutionState,
    after_state: &ExecutionState,
    ranges_by_summary: &[Vec<MemoryRange>],
) -> Vec<Proposition> {
    ranges_by_summary
        .iter()
        .map(|ranges| Proposition::MemoryEffectSummary {
            before: before_state.memory().clone(),
            before_point: before_state.path_link().clone(),
            after: after_state.memory().clone(),
            after_point: after_state.path_link().clone(),
            mutable_ranges: ranges.clone(),
        })
        .collect()
}

/// The abstract head of one loop.
///
/// `top` is the state the enclosing frame continues from; `body` is the state
/// the body executes from. They differ only in the resource context, and only
/// when the loop declares resources of its own: the body then owns exactly
/// what the loop declared, and the rest of the enclosing frame's resources are
/// withheld until the loop exits.
#[derive(Clone, Debug)]
pub(super) struct LoopHead {
    pub(super) top: ExecutionState,
    pub(super) body: ExecutionState,
    /// The head state the loop reads its guard and invariants from: `top`
    /// with the cells of each folded matched instance's selected arm
    /// published as views (D7). Ownership is untouched, and the loop's exit
    /// outcome is `top`, so the extra read authority never leaves the head.
    pub(super) guard: ExecutionState,
    /// The loop's entry state with each binder bound to the instance it
    /// names. Entry invariant checks read binder fields from here, so a loop
    /// binder that renames an enclosing instance is available at entry too.
    pub(super) entry: ExecutionState,
    /// The head's pass count `K`: a fresh Integer standing for the number of
    /// passes the loop has completed when it reaches this head. Every
    /// invariant this head assumes reads `iterations` as `K`, and every back
    /// edge from it owes them at `K + 1`.
    pub(super) iterations: IntegerTerm,
    pub(super) summaries: Vec<Proposition>,
    /// Why a declared loop resource could not be taken from the enclosing
    /// resource context. A non-empty list is a verification failure.
    pub(super) resource_failures: Vec<LoopResourceFailure>,
    /// Premises of applying the head abstraction to the original loop entry.
    borrow_requirements: Vec<ProofObligation>,
    /// The loop's effect checks with every declared-resource frame installed
    /// from the checked evaluation of the loop's own resource specs at entry.
    /// Every later check of this loop reads these, never the originals.
    pub(super) effect_checks: Vec<LoopEffectCheck>,
}

/// Why a declared loop resource could not be taken from the enclosing
/// context. An unheld resource keeps the fact and the state it was
/// evaluated over, so the surface can spell it in the source's names.
#[derive(Clone, Debug)]
pub(super) enum LoopResourceFailure {
    Message(String),
    Contract(String),
    Tactic(String),
    Evaluation(String),
    Unheld {
        fact: ResourceFact,
        state: ExecutionState,
    },
}

impl LoopResourceFailure {
    pub(super) const UNHELD: &'static str =
        "loop declares a resource the enclosing function does not hold";

    /// The failure as an obligation context, where no state is at hand to
    /// spell the resource; the loop-head refusal carries it instead.
    pub(super) fn context(&self) -> String {
        match self {
            Self::Message(message)
            | Self::Evaluation(message)
            | Self::Contract(message)
            | Self::Tactic(message) => message.clone(),
            Self::Unheld { .. } => Self::UNHELD.to_string(),
        }
    }
}

impl From<String> for LoopResourceFailure {
    fn from(message: String) -> Self {
        Self::Message(message)
    }
}

impl From<&str> for LoopResourceFailure {
    fn from(message: &str) -> Self {
        Self::Message(message.to_owned())
    }
}

impl LoopHead {
    /// Whether the body executes with a narrower resource context than the
    /// enclosing frame holds.
    pub(super) fn narrows_resources(&self) -> bool {
        self.body.resources() != self.top.resources()
    }

    /// Return the withheld frame while retaining the body's final exchange.
    pub(super) fn restored_exit_state(
        &self,
        state: &ExecutionState,
        assumptions: &PureFactContext,
    ) -> ExecutionState {
        if !self.narrows_resources() {
            return state.clone();
        }
        restore_loop_exit_state(
            state,
            self.body.resources(),
            self.top.resources(),
            assumptions,
        )
    }
}

pub(crate) fn restore_loop_exit_state(
    state: &ExecutionState,
    body: &ResourceContext,
    frame: &ResourceContext,
    assumptions: &PureFactContext,
) -> ExecutionState {
    if state.resources() == body {
        return state.clone().with_resource_context(frame.clone());
    }
    let Some(resources) = state
        .resources()
        .restore_frame_after_exchange(body, frame, assumptions)
    else {
        // No additional authority is granted for an unrepresentable or
        // conflicting exchange. Exit obligations still see the actual state.
        return state.clone();
    };
    state.clone().with_resource_context(resources)
}

/// Every composite resource definition this environment's functions declare,
/// sorted by family name and without exact repeats.
pub(super) fn environment_composite_resource_definitions(
    environment: &ExecutionEnvironment,
) -> Vec<CompositeResourceDefinition> {
    let mut definitions = environment
        .functions
        .values()
        .flat_map(|function| function.composite_resource_definitions().iter().cloned())
        .fold(Vec::new(), |mut definitions, definition| {
            if !definitions.contains(&definition) {
                definitions.push(definition);
            }
            definitions
        });
    // Consumers can index the table rather than scanning it per loop binder.
    // Conflicting definitions retain distinct entries and are not resolved by
    // choosing an arbitrary family body.
    definitions.sort_by(|left, right| left.name().cmp(right.name()));
    definitions
}

/// Installs a loop's declared-resource frame from the kernel's own reading
/// of the loop's resource specs at entry: each owned spec evaluated against
/// the entering context, and its owned footprint derived from the resource
/// definitions (`checked_owned_memory_ranges`), the same derivation a
/// function's resource-derived frame gets. A check that already carries validated
/// ranges keeps them. When the specs do not evaluate, the checks stay
/// uninstalled and the loop's declaration failure is the verdict; the
/// declared frame then fails closed like an inherited one.
fn install_declared_loop_frames(
    entry_state: &ExecutionState,
    effect_checks: &[LoopEffectCheck],
    resource_specs: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<LoopEffectCheck>> {
    if !effect_checks.iter().any(|check| {
        check.origin() == LoopEffectOrigin::DeclaredResource && check.validated_ranges().is_none()
    }) {
        return Ok(effect_checks.to_vec());
    }
    let Ok((_, checked)) = super::functions::evaluate_function_resource_context_with_metadata(
        entry_state,
        resource_specs,
        definitions,
        assumptions,
        budget,
    )?
    else {
        return Ok(effect_checks.to_vec());
    };
    let mut ranges = BTreeSet::new();
    for fact in checked.iter().filter(|checked| checked.fact.is_own()) {
        crate::instrumentation::record_deterministic_work(1);
        let Some(expanded) = super::functions::checked_owned_memory_ranges(
            &fact.fact,
            definitions,
            entry_state,
            assumptions,
        ) else {
            return Ok(effect_checks.to_vec());
        };
        ranges.extend(expanded);
    }
    let ranges = ranges.into_iter().collect::<Vec<_>>();
    Ok(effect_checks
        .iter()
        .map(|check| {
            if check.origin() == LoopEffectOrigin::DeclaredResource
                && check.validated_ranges().is_none()
            {
                check.clone().with_validated_ranges(ranges.clone())
            } else {
                check.clone()
            }
        })
        .collect())
}

/// Capture ordinary entry memory footprints before modified locals are
/// havocked. Named resource binders still read their arguments/models at the
/// abstract head; their independently derived views are never captured here.
fn capture_loop_entry_memory_specs(
    entry: &ExecutionState,
    specs: &[ResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(Vec<ResourceSpec>, Vec<LoopResourceFailure>)> {
    let mut captured = Vec::with_capacity(specs.len());
    let mut failures = Vec::new();
    for spec in specs {
        let ResourceTerm::Memory(segment) = spec.term() else {
            captured.push(spec.clone());
            continue;
        };
        if spec.state_source() != ResourceStateSource::Entry
            || spec.guard().is_some()
            || segment.guard().is_some()
        {
            captured.push(spec.clone());
            continue;
        }
        let mut segment = segment.clone();
        let mut failed = false;
        for expression in [&mut segment.base, &mut segment.start, &mut segment.end] {
            match evaluate_loop_effect_segment_value(
                entry,
                expression,
                assumptions,
                "loop entry memory operand",
                budget,
            )? {
                Ok(value) => *expression = ProgramExpression::Value(value),
                Err(message) => {
                    failures.push(LoopResourceFailure::Message(format!(
                        "could not capture loop entry memory footprint: {message}"
                    )));
                    failed = true;
                    break;
                }
            }
        }
        captured.push(if failed {
            spec.clone()
        } else {
            spec.with_captured_memory_segment(segment)
        });
    }
    Ok((captured, failures))
}

pub(super) fn prepare_loop_top_state(
    entry_state: &ExecutionState,
    effect_checks: &[LoopEffectCheck],
    invariant_checks: &[LoopInvariantCheck],
    resource_specs: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    body: &ProgramStatement,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    variables: &mut KernelVariableGenerator,
) -> ExecutionResult<LoopHead> {
    let iterations = IntegerTerm::var(variables.next_in(budget)?);
    let (captured_resource_specs, capture_failures) =
        capture_loop_entry_memory_specs(entry_state, resource_specs, assumptions, budget)?;
    let resource_specs = captured_resource_specs.as_slice();
    let effect_checks = install_declared_loop_frames(
        entry_state,
        effect_checks,
        resource_specs,
        definitions,
        assumptions,
        budget,
    )?;
    let include_mutable_summaries = statement_may_write_memory(entry_state, body);
    // The locals whose address a body that writes memory may write through,
    // found once for the write set below and the head's havoc.
    let escaped = if include_mutable_summaries {
        address_escaped_scalar_locals(entry_state, body)
    } else {
        Default::default()
    };
    let (effect_ranges, all_ranges_evaluable) = evaluate_whole_loop_effect_ranges(
        entry_state,
        &effect_checks,
        include_mutable_summaries,
        assumptions,
        budget,
    )?;
    // A verified footprint is an edge fact, not merely a copy-back hint. If
    // any whole mutable segment could not be evaluated, keep the old barrier
    // semantics for the entire loop; the failed effect check still produces
    // its own false proof obligation. Preserve Some(empty) for a checked
    // immutable/no-write summary, distinct from no footprint at all.
    let loop_havoc_ranges = (all_ranges_evaluable && !effect_ranges.is_empty()).then(|| {
        let mut ranges = effect_ranges.iter().flatten().cloned().collect::<Vec<_>>();
        // A write set derived from the function's resources covers the
        // memory the function was given, never its own automatic objects. A
        // body that writes memory may write those through a pointer: a call
        // given `&local`, or a store through an address taken earlier.
        if include_mutable_summaries {
            ranges.extend(loop_written_automatic_objects(entry_state, body, &escaped));
        }
        ranges
    });
    // The stable-borrow barrier is checked below, after the loop's declared
    // ownership. A loop that declares a resource the function does not hold
    // also derives its havoc footprint from that bad declaration, so running
    // the barrier first would report the overlap it caused instead of the
    // ownership violation that is the real error.
    let borrow_check = if let Some(ledger) = entry_state
        .borrow_ledger()
        .filter(|ledger| include_mutable_summaries && ledger.has_active_memory_borrows())
    {
        // When the loop has no checked summary, use the enclosing checked
        // owned footprint as the existing upper bound on its writes.
        let fallback = loop_havoc_ranges
            .is_none()
            .then(|| checked_owned_entry_footprint(entry_state.resources()))
            .flatten();
        loop_head_borrow_requirements(ledger, loop_havoc_ranges.as_deref().or(fallback.as_deref()))
    } else {
        Ok(Vec::new())
    };
    let mut resource_failures = capture_failures;
    let withheld = if resource_specs.is_empty() || effect_ranges.is_empty() {
        None
    } else {
        loop_declared_and_withheld_resources(
            entry_state,
            resource_specs,
            assumptions,
            budget,
            false,
        )?
        .ok()
        .map(|(_, withheld)| withheld)
    };
    let mut top_state = havoc_loop_modified_locals(
        entry_state,
        body,
        &escaped,
        variables,
        budget,
        loop_havoc_ranges.as_deref(),
        withheld
            .as_ref()
            .map(|frame| CallKeptRanges::new(frame.clone(), Vec::new(), None)),
    )?;
    if statement_may_write_memory(entry_state, body) {
        let mut resources = top_state.resources().clone();
        resources.havoc_owned_structural_witnesses();
        top_state = top_state.with_resource_context(resources);
    }
    let mut summaries =
        collect_whole_loop_effect_summaries(entry_state, &top_state, &effect_ranges);

    // Whole-loop effects are part of the induction hypothesis at the abstract
    // head and are checked independently at every back edge.
    let mut framed_memory = top_state.memory().clone();
    // Restore the entry's blocks over the havocked ones. Only the blocks
    // that differ are written, so a table havoc left alone keeps its root,
    // and the comparison with the top state below stays constant rather
    // than linear in every block the path has declared.
    if !summaries.is_empty() {
        std::sync::Arc::make_mut(&mut framed_memory.blocks)
            .overwrite_with(&entry_state.memory().blocks);
    }
    // A declaring loop's body holds only its declared resources and views of
    // the rest, and a store needs ownership, so memory the enclosing function
    // keeps owning is memory the loop cannot write, whatever its footprint
    // covers. The footprint over-approximates what the loop owns (an
    // iterated fact counts every element it could ever hold), so a cell the
    // function owns can sit inside it without being writable; the partition
    // at entry is what keeps it apart.
    let kept_by_function = |pointer: &Address, bytes: u32| {
        withheld.as_ref().is_some_and(|withheld| {
            assumptions.access_held_by_owned_member(withheld, pointer, bytes)
        })
    };
    // A run is reinstalled whole where a summary's mutable ranges are proven
    // clear of all of its bytes, which clears each slot's; with no summary
    // and nothing withheld no slot is stable. Anything else is asked slot by
    // slot below.
    let mut runs_by_slot = Vec::new();
    for run in entry_state.memory().cells.runs() {
        crate::instrumentation::record_deterministic_work(1);
        if run.base().base.is_local_block() || run.live_count() == 0 {
            continue;
        }
        if summaries.is_empty() && withheld.is_none() {
            continue;
        }
        let whole_bytes = run
            .count()
            .checked_sub(1)
            .and_then(|last| last.checked_mul(run.element_width()))
            .and_then(|last| last.checked_add(run.value_width()));
        let whole_stable = whole_bytes.is_some_and(|bytes| {
            summaries.iter().any(|summary| {
                let Proposition::MemoryEffectSummary { mutable_ranges, .. } = summary else {
                    return false;
                };
                crate::kernel::memory_history::typed_ranges_disjoint_from_pointer_evidence(
                    mutable_ranges,
                    run.base(),
                    bytes,
                    assumptions,
                )
                .is_some()
            })
        });
        #[cfg(debug_assertions)]
        let before = framed_memory.cells.clone();
        let stable_run = if whole_stable || withheld.is_some() {
            None
        } else {
            run_slots_clear_of_loop_summaries(run, &summaries, assumptions)
        };
        if let Some(stable_run) = stable_run
            && std::sync::Arc::make_mut(&mut framed_memory.cells).install_run(&stable_run)
        {
            continue;
        }
        if whole_stable && std::sync::Arc::make_mut(&mut framed_memory.cells).install_run(run) {
            #[cfg(debug_assertions)]
            if run.count() <= crate::kernel::primitives::CHECKED_RUN_SLOTS {
                crate::instrumentation::uncharged_debug_check(|| {
                    let mut expected = (*before).clone();
                    for index in run.live_indexes() {
                        expected.insert(run.slot_pointer(index), run.value(index));
                    }
                    assert_eq!(
                        expected.logical(),
                        framed_memory.cells.logical(),
                        "installing a run whole disagrees with storing its slots one by one"
                    );
                });
            }
            continue;
        }
        runs_by_slot.push(run.clone());
    }
    let slots_asked_one_by_one = runs_by_slot
        .iter()
        .flat_map(|run| {
            run.live_indexes()
                .map(|index| {
                    (
                        run.slot_pointer(index),
                        StoredMemoryValue::from(run.value(index)),
                    )
                })
                .collect::<Vec<_>>()
        })
        .collect::<Vec<_>>();
    let reachable_cells = entry_state.memory().cells.caught_up_pointer_reachable();
    for (pointer, value) in reachable_cells
        .iter()
        .map(|(pointer, value)| (pointer.clone(), value.clone()))
        .chain(slots_asked_one_by_one)
    {
        let pointer = &pointer;
        let value = &value;
        if pointer.base.is_local_block() {
            continue;
        }
        let is_stable = summaries.iter().any(|summary| {
            let Proposition::MemoryEffectSummary { mutable_ranges, .. } = summary else {
                return false;
            };
            assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
        }) || kept_by_function(
            pointer,
            crate::kernel::reasoning::cell_access_byte_width(value.native()),
        );
        if is_stable {
            std::sync::Arc::make_mut(&mut framed_memory.cells)
                .insert_retained(pointer.clone(), value.clone());
        }
    }
    for ((pointer, program_type), value) in entry_state.memory().union_cells.iter() {
        if pointer.base.is_local_block() {
            continue;
        }
        let is_stable = summaries.iter().any(|summary| {
            let Proposition::MemoryEffectSummary { mutable_ranges, .. } = summary else {
                return false;
            };
            assumptions.ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
        });
        if is_stable {
            std::sync::Arc::make_mut(&mut framed_memory.union_cells)
                .insert((pointer.clone(), *program_type), value.clone());
        }
    }

    if framed_memory != *top_state.memory() {
        // Restoring checked stable cells observes the abstract head's bytes;
        // it does not write them. Retain that edge so a complete pointer read
        // can follow the loop's checked footprint back to its entry origin.
        record_memory_derivation(
            &mut framed_memory,
            MemoryDerivation::CellObserved {
                base: intern_memory_ref(top_state.memory()),
            },
        );
        top_state = top_state.with_memory(framed_memory);
        summaries = collect_whole_loop_effect_summaries(entry_state, &top_state, &effect_ranges);
    }
    // A loop binder takes the instance the enclosing context holds and gives
    // it fresh fields: the head is an arbitrary visit, so only the invariants
    // say what model the binder carries there. The enclosing frame continues
    // from that same head, which is why the loop's exit sees the final model.
    let (entry_state, head_state, top_state, mut rebound_failures) =
        match rebind_loop_binder_instances(entry_state, resource_specs, assumptions, budget)? {
            Ok(rebound) => {
                // The head is an arbitrary visit, so the binder's arguments
                // are read from the havocked locals rather than from the
                // values the loop was entered with (D5). That is what lets a
                // body that advances its cursor find its binder again.
                let head_carrier = top_state
                    .clone()
                    .with_resource_context(rebound.resources().clone());
                let head_state = havoc_loop_binder_instance_fields(
                    &head_carrier,
                    resource_specs,
                    assumptions,
                    variables,
                    budget,
                )?;
                let top_state = top_state.with_resource_context(head_state.resources().clone());
                (rebound, head_state, top_state, Vec::new())
            }
            Err(failure) => (
                entry_state.clone(),
                entry_state.clone(),
                top_state,
                vec![failure],
            ),
        };
    // A declared conditional guard carries an existential acquisition. Check
    // its real entry custody before replacing concrete heldness at the head.
    let mut top_state = top_state;
    let mut selected_mutexes = std::collections::BTreeSet::new();
    for binder in loop_binders(resource_specs) {
        let result = (|| -> Result<(), String> {
            let Some(entry_instance) = entry_state.resources().owned_instance(binder.identity)
            else {
                return Ok(());
            };
            let Some((mutex, entry_held)) = super::functions::loop_instance_guard(
                &entry_state,
                entry_instance,
                definitions,
                assumptions,
            )?
            else {
                return Ok(());
            };
            if !selected_mutexes.insert(mutex.clone()) {
                return Err("two loop resources describe the same mutex guard".into());
            }
            check_loop_guard_custody(&entry_state, &mutex, &entry_held, assumptions)?;
            let head_instance = top_state
                .resources()
                .owned_instance(binder.identity)
                .ok_or("loop guard binder is absent at the head")?;
            let Some((head_mutex, held)) = super::functions::loop_instance_guard(
                &top_state,
                head_instance,
                definitions,
                assumptions,
            )?
            else {
                return Err("loop guard definition changed at the head".into());
            };
            if head_mutex != mutex {
                return Err("loop guard mutex must not depend on changing model fields".into());
            }
            top_state = super::mutexes::abstract_loop_mutex(&top_state, &mutex, held)?;
            Ok(())
        })();
        if let Err(message) = result {
            rebound_failures.push(LoopResourceFailure::Message(message));
        }
    }
    // A direct conditional clause owns a typed occurrence whose condition
    // captures the head expression, independently of later local mutations.
    let mut ordinary_specs = Vec::new();
    let mut direct_carriers = Vec::new();
    let mut direct_mutexes = Vec::new();
    for spec in resource_specs {
        if spec.guard().is_some() && matches!(spec.term(), ResourceTerm::MutexGuard { .. }) {
            let identity = budget.allocate_instance_identity()?;
            match super::mutexes::prepare_direct_loop_guard(
                &entry_state,
                &top_state,
                spec,
                identity,
                assumptions,
            ) {
                Ok((updated, mutex, carrier)) => {
                    direct_carriers.push(carrier);
                    direct_mutexes.push(mutex);
                    top_state = updated;
                }
                Err(message) => rebound_failures.push(message),
            }
        } else {
            ordinary_specs.push(spec.clone());
        }
    }
    top_state = super::mutexes::select_direct_loop_guards(&top_state, direct_mutexes);
    // The loop's declarations are evaluated where the loop starts, over the
    // head's models: the clause arguments are the ones at loop entry, and the
    // models are the fresh ones an arbitrary visit carries.
    if let Ok((declared, _)) = loop_declared_and_withheld_resources(
        &head_state,
        &ordinary_specs,
        assumptions,
        budget,
        false,
    )? {
        let refreshed = with_owner_read_authority_rederived(
            top_state.resources().clone(),
            declared.facts(),
            definitions,
            &top_state,
            assumptions,
            None,
        );
        top_state = top_state.with_resource_context(refreshed);
    }
    let (mut body_state, body_failures) = loop_body_resource_context(
        &head_state,
        &top_state,
        &ordinary_specs,
        definitions,
        assumptions,
        budget,
    )?;
    if ordinary_specs.is_empty() && !direct_carriers.is_empty() {
        body_state =
            body_state.with_resource_context(ResourceContext::new_with_equalities(assumptions));
    }
    if !direct_carriers.is_empty() {
        let missing = direct_carriers
            .into_iter()
            .filter(|fact| !body_state.resources().contains_exact_representation(fact))
            .collect::<Vec<_>>();
        body_state = body_state
            .clone()
            .with_resource_context(body_state.resources().clone().unchecked_with_facts(missing));
    }
    // A declaring loop's body does not hold the frame's iterated ownership
    // facts, so a guard cell it writes escapes the store rule; the frame
    // loses any fact whose guard cells the loop may write.
    let top_state = if resource_specs.is_empty() {
        top_state
    } else {
        super::iterated::frame_out_iterated_facts_written_by_loop(
            top_state,
            loop_havoc_ranges.as_deref(),
        )
    };
    resource_failures.append(&mut rebound_failures);
    resource_failures.extend(body_failures);
    let borrow_requirements = borrow_check.unwrap_or_else(|message| {
        resource_failures.push(LoopResourceFailure::Message(message.to_string()));
        Vec::new()
    });
    // D7 at a loop head: the invariants play the part of a contract's
    // requirements, so a folded matched instance publishes the cells of the
    // arm they select. That is what lets a guard such as `root->left != 0`
    // read through the focused subtree the binder holds.
    // Publish owned projections with their support before adding any remaining
    // arm views. A bare view inserted first would make the attachment pass
    // skip that cell, leaving call recovery with no supporting occurrence.
    let guard_state = with_selected_arm_views_attached(
        top_state.clone(),
        &top_state,
        invariant_checks,
        &iterations,
        definitions,
        assumptions,
        budget,
    )?;
    let body_state = with_selected_arm_views_attached(
        body_state,
        &top_state,
        invariant_checks,
        &iterations,
        definitions,
        assumptions,
        budget,
    )?;
    let guard_state = with_selected_arm_views(
        &guard_state,
        &top_state,
        invariant_checks,
        &iterations,
        definitions,
        assumptions,
        budget,
    )?;
    let body_state = with_selected_arm_views(
        &body_state,
        &top_state,
        invariant_checks,
        &iterations,
        definitions,
        assumptions,
        budget,
    )?;
    // The exit also keeps each observation attached to its owned instance.
    let premise_state = top_state.clone();
    let top_state = with_selected_arm_views_attached(
        top_state,
        &premise_state,
        invariant_checks,
        &iterations,
        definitions,
        assumptions,
        budget,
    )?;
    Ok(LoopHead {
        top: top_state,
        body: body_state,
        guard: guard_state,
        entry: entry_state,
        iterations,
        summaries,
        resource_failures,
        borrow_requirements,
        effect_checks,
    })
}

/// `state` with the cells of each owned instance's selected arm published as
/// views attached to that instance, under this loop's invariants.
///
/// The decision is the one [`with_selected_arm_views`] makes; only the form
/// differs. A view attached to its owner retires when the owner is unfolded,
/// consumed or freed, so it may outlive the loop head where a free-standing
/// one may not. Cost is one pass over the instances the state holds, as the
/// free-standing publication is.
fn with_selected_arm_views_attached(
    state: ExecutionState,
    premise_state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    iterations: &IntegerTerm,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<ExecutionState> {
    if definitions.is_empty() {
        return Ok(state);
    }
    let contexts = assume_invariant_checks(
        premise_state,
        premise_state,
        invariant_checks,
        iterations,
        assumptions,
        &[],
        &[],
        budget,
    )?;
    let [(facts, obligations, _)] = contexts.as_slice() else {
        return Ok(state);
    };
    let head_assumptions = assumptions_with_path_context(assumptions, facts, obligations);
    let decided = crate::kernel::publish_instance_arms(
        state.resources(),
        definitions,
        &state,
        &head_assumptions,
    )
    .model_facts
    .into_iter()
    .fold(head_assumptions, PureFactContext::assume_proposition);
    let owners = state
        .resources()
        .facts()
        .iter()
        .filter(|fact| matches!(fact, ResourceFact::Own(Resource::Instance(_), _)))
        .cloned()
        .collect::<Vec<_>>();
    let mut resources = state.resources().clone();
    let mut changed = false;
    for owner in owners {
        crate::instrumentation::record_deterministic_work(1);
        let Resource::Instance(instance) = owner.resource() else {
            continue;
        };
        let Some((occurrence, _)) = resources.unique_owned_occurrence_for_fact(&owner) else {
            continue;
        };
        // A matched body publishes its selected arm; a plain body publishes
        // its own cells.
        let views =
            super::functions::instance_arm_read_authority(instance, definitions, &state, &decided)
                .into_iter()
                .chain(crate::kernel::unmatched_instance_body_views(
                    &owner,
                    definitions,
                    &state,
                    &decided,
                ))
                .filter(|view| view.memory_view_range().is_some())
                .filter(|view| !resources.contains_exact_representation(view))
                .collect::<Vec<_>>();
        if views.is_empty() {
            continue;
        }
        resources = resources.unchecked_with_supported_facts_from_occurrence_with_memory(
            occurrence,
            &owner,
            views,
            state.memory(),
        );
        changed = true;
    }
    Ok(if changed {
        state.with_resource_context(resources)
    } else {
        state
    })
}

/// `state` with the cells of every folded matched instance's selected arm
/// published as read authority (D7).
///
/// The premises are this loop's own invariants, assumed at `premise_state`.
/// The decision itself is [`crate::kernel::select_resource_model_arm`], the
/// one arm-selection mechanism; nothing here proves by cases, and ownership
/// is untouched. An instance whose arm the invariants do not select publishes
/// nothing, exactly as a contract clause's would.
///
/// Cost is the selected arms' own clauses plus one lowering of each invariant.
fn with_selected_arm_views(
    state: &ExecutionState,
    premise_state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    iterations: &IntegerTerm,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<ExecutionState> {
    if definitions.is_empty() {
        return Ok(state.clone());
    }
    let contexts = assume_invariant_checks(
        premise_state,
        premise_state,
        invariant_checks,
        iterations,
        assumptions,
        &[],
        &[],
        budget,
    )?;
    // Two invariant readings would be two different premise sets, and a
    // published arm must be the one every reading selects. One reading is the
    // ordinary case; anything else publishes nothing.
    let [(facts, obligations, _)] = contexts.as_slice() else {
        return Ok(state.clone());
    };
    let head_assumptions = assumptions_with_path_context(assumptions, facts, obligations);
    let views = crate::kernel::publish_instance_arms(
        state.resources(),
        definitions,
        state,
        &head_assumptions,
    )
    .views;
    if views.is_empty() {
        return Ok(state.clone());
    }
    Ok(with_arm_views_preserving_support(state, views))
}

// Re-publishing a view must not add an unsupported copy beside an existing
// owned projection: that copy could survive consumption of the owner. Each
// explicit output view uses the exact membership index, without scanning
// owners or other representations of the view.
fn with_arm_views_preserving_support(
    state: &ExecutionState,
    views: Vec<ResourceFact>,
) -> ExecutionState {
    let mut resources = state.resources().clone();
    for view in views {
        crate::instrumentation::record_deterministic_work(1);
        if !resources.contains_exact_representation(&view) {
            resources = resources.unchecked_with_fact(view);
        }
    }
    state.clone().with_resource_context(resources)
}

#[cfg(test)]
mod written_automatic_objects_tests {
    include!("../scaling_tests/kernel/loops/written_automatic_objects_tests.rs");
}

#[cfg(test)]
mod arm_view_support_tests {
    include!("../scaling_tests/kernel/loops/arm_view_support.rs");
}

/// Builds the resource context a declaring loop's body executes with.
///
/// The loop takes its declared resources out of the enclosing context, exactly
/// as a call takes a callee's requirements out of its caller's. What remains is
/// viewed rather than owned, so a body store outside the loop's owned memory
/// fails at the store for want of a resource, and the loop's havoc footprint
/// is the memory it owns. A loop that declares views of its own keeps no
/// ambient read authority either.
/// A declaring loop's resources as its clauses evaluate at `entry_state`,
/// and what the enclosing function keeps: the entry context with those
/// resources taken out. The body sees the kept part only as views, so it
/// can write none of it. `Err` names a clause the function does not hold.
fn loop_declared_and_withheld_resources(
    entry_state: &ExecutionState,
    resource_specs: &[ResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    inherit_view_bindings: bool,
) -> ExecutionResult<Result<(ResourceContext, ResourceContext), LoopResourceFailure>> {
    let evaluated = if inherit_view_bindings {
        super::functions::evaluate_loop_resource_context(
            entry_state,
            resource_specs,
            assumptions,
            budget,
        )
    } else {
        evaluate_function_resource_context(entry_state, resource_specs, &[], assumptions, budget)
    };
    let declared = match evaluated? {
        Ok(declared) => declared,
        Err(error) => {
            return Ok(Err(LoopResourceFailure::Evaluation(format!(
                "loop declares a resource the enclosing function does not hold: {}",
                super::api::contract_certification::describe_certification_runtime_error(&error)
            ))));
        }
    };
    let mut withheld = entry_state.resources().clone();
    for fact in declared.facts() {
        let Some(remaining) = withheld
            .clone()
            .without_fact_incrementally(fact, assumptions)
        else {
            return Ok(Err(LoopResourceFailure::Unheld {
                fact: fact.clone(),
                state: entry_state.clone(),
            }));
        };
        withheld = remaining;
    }
    Ok(Ok((declared, withheld)))
}

/// Holding a resource lets C read the memory it owns directly, and that read
/// authority is an observation attached to the owner's occurrence. A loop
/// head derives it again for each owner the loop declares, from the owner's
/// definition over the head's state, as a call does where it returns one.
/// It is never kept from the state before the loop: an address the
/// definition reads out of memory or out of a model may differ on an
/// arbitrary visit, and a view of the old address would outlive the owner's
/// claim to it.
///
/// A resource without fields is expanded one level. A resource with fields
/// is left to [`with_selected_arm_views_attached`], which needs the loop's
/// invariants to select its arm. Cost is each declared owner's own clauses.
fn with_owner_read_authority_rederived(
    mut resources: ResourceContext,
    declared: &[ResourceFact],
    definitions: &[CompositeResourceDefinition],
    head: &ExecutionState,
    assumptions: &PureFactContext,
    binding_source: Option<&ExecutionState>,
) -> ResourceContext {
    for owner in declared.iter().filter(|fact| fact.is_own()) {
        if matches!(owner.resource(), Resource::Instance(_)) {
            continue;
        }
        let Some((occurrence, _)) = resources.unique_owned_occurrence_for_fact(owner) else {
            continue;
        };
        resources = resources.without_memory_views_supported_by_occurrence(occurrence);
        let derived: Vec<ResourceFact> =
            super::functions::expand_composite_resource_fact_with_children(
                &ResourceContext::new_with_equalities(assumptions)
                    .unchecked_with_fact(owner.clone()),
                owner,
                definitions,
                &head.program_point(),
                assumptions,
            )
            .map(|(_, children, _)| {
                children
                    .iter()
                    .filter_map(ResourceFact::memory_own_range)
                    .map(|range| ResourceFact::view_memory(range.clone()))
                    .collect()
            })
            .unwrap_or_default();
        let views = derived
            .into_iter()
            .filter(|view| view.memory_view_range().is_some())
            .filter(|view| !resources.contains_exact_representation(view))
            .collect::<Vec<_>>();
        if views.is_empty() {
            continue;
        }
        let (next, inserted) = resources
            .unchecked_with_supported_facts_from_occurrence_with_memory_and_occurrences(
                occurrence,
                owner,
                views,
                head.memory(),
            );
        resources = match binding_source {
            Some(source) => source.borrow_bindings().attach_to_inserted_views(
                source.resources(),
                next,
                &inserted,
                assumptions,
            ),
            None => next,
        };
    }
    resources
}

/// Rebuild the permitted loop frame with per-fact validity checks, then
/// normalize the accumulated frame once. Normalizing after every insertion
/// repeatedly visits all previously retained scalar and view endpoints.
fn with_loop_frame_resources(
    mut body_resources: ResourceContext,
    withheld: &ResourceContext,
    allow_frame_views: bool,
    top_state: &ExecutionState,
    assumptions: &PureFactContext,
    binding_source: &ExecutionState,
) -> ResourceContext {
    let candidates: Box<dyn Iterator<Item = &ResourceFact> + '_> = if allow_frame_views {
        Box::new(withheld.iter())
    } else {
        Box::new(
            top_state
                .memory()
                .blocks
                .scalar_blocks()
                .flat_map(|block| withheld.owned_memory_facts_in_block(block)),
        )
    };
    for fact in candidates {
        crate::instrumentation::record_deterministic_work(1);
        // The explicit-interface iterator already selects scalar owners.
        let allocation_owner = !allow_frame_views
            || (fact.is_own()
                && matches!(fact.resource(),
            Resource::Memory(range) if top_state.memory().requires_explicit_scalar_ownership(range.base())));
        let Some(viewed) = viewed_form_of_resource_fact(fact) else {
            continue;
        };
        if body_resources.satisfies_fact(&viewed, assumptions) {
            continue;
        }
        let supplied = if allocation_owner {
            fact.clone()
        } else {
            viewed
        };
        match body_resources
            .clone()
            .install_established_partition(std::iter::once(supplied), assumptions)
        {
            Ok((composed, inserted)) => {
                body_resources = binding_source.borrow_bindings().attach_to_inserted_views(
                    binding_source.resources(),
                    composed,
                    &inserted,
                    assumptions,
                );
            }
            Err(_) => continue,
        }
    }
    body_resources.normalized_without_discovery(assumptions)
}

fn loop_body_resource_context(
    entry_state: &ExecutionState,
    top_state: &ExecutionState,
    resource_specs: &[ResourceSpec],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(ExecutionState, Vec<LoopResourceFailure>)> {
    if resource_specs.is_empty() {
        return Ok((top_state.clone(), Vec::new()));
    }
    let (declared, withheld) = match loop_declared_and_withheld_resources(
        entry_state,
        resource_specs,
        assumptions,
        budget,
        true,
    )? {
        Ok(split) => split,
        Err(failure) => return Ok((top_state.clone(), vec![failure])),
    };
    let mut body_resources = with_loop_frame_resources(
        declared.clone(),
        &withheld,
        !resource_specs.iter().any(resource_spec_is_view),
        top_state,
        assumptions,
        entry_state,
    );
    body_resources = with_owner_read_authority_rederived(
        body_resources,
        declared.facts(),
        definitions,
        top_state,
        assumptions,
        Some(entry_state),
    );
    // Only bindings attached to newly produced views are listed here. The
    // inherited map is shared, not scanned or reconstructed from contexts.
    let mut body_bindings = top_state.borrow_bindings().clone();
    let produced =
        super::borrows::BorrowBindings::from_state(body_resources.borrow_dependency_state());
    for (occurrence, binding) in produced.iter() {
        body_bindings = body_bindings.with_inserted(*occurrence, binding.clone());
    }
    Ok((
        top_state
            .clone()
            .with_resource_context(body_resources)
            .with_borrow_bindings(body_bindings),
        Vec::new(),
    ))
}

/// Whether a declared loop resource asks only to read.
fn resource_spec_is_view(spec: &ResourceSpec) -> bool {
    spec.is_view()
}

/// One `owns name: resource(args);` loop binder: the name the header writes
/// and the instance identity it binds.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct LoopBinder {
    identity: InstanceId,
    name: String,
    /// The declared resource the binder names. The back edge re-evaluates its
    /// arguments in the state the body reached (D5), so a body that advances
    /// its cursor hands the loop the instance at the new arguments.
    spec: Option<ResourceSpec>,
}

/// The binders a loop's `owns name: resource(args);` clauses declare.
pub(crate) fn loop_binders(resource_specs: &[ResourceSpec]) -> Vec<LoopBinder> {
    resource_specs
        .iter()
        .filter_map(|spec| {
            Some(LoopBinder {
                identity: spec.instance_identity()?,
                name: spec.instance_binder().unwrap_or("<unnamed>").to_string(),
                spec: Some(spec.clone()),
            })
        })
        .collect()
}

/// Binds each `owns name: resource(args);` loop binder to the owned instance
/// it names, whatever identity the surrounding proof gave that instance.
///
/// A loop header names an instance the way a callee contract does, and there
/// is no binder map: the binder takes the unique owned instance of its family
/// whose arguments, evaluated in this state, are provably the declared ones.
/// The same rule runs at the loop head and at the back edge, so a body that
/// refolded its instance under another name still hands the loop binder back.
///
/// The search reads the family's shape bucket of the resource context and
/// checks the arguments of those instances alone, so it costs the instances
/// of one family rather than the surrounding context.
fn rebind_loop_binder_instances(
    state: &ExecutionState,
    resource_specs: &[ResourceSpec],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ExecutionState, LoopResourceFailure>> {
    if !resource_specs.iter().any(ResourceSpec::is_instance) {
        return Ok(Ok(state.clone()));
    }
    let mut state = state.clone();
    let mut claimed: BTreeSet<InstanceId> = BTreeSet::new();
    for spec in resource_specs {
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        let binder = spec.instance_binder().unwrap_or("<unnamed>").to_string();
        let Some(inner) = spec.instance_resource_spec() else {
            continue;
        };
        // Evaluate only the scalar shape here; references are checked separately below.
        let inner = inner.with_resource_arguments(Vec::new());
        let (name, arguments) =
            match evaluate_function_resource_spec(&state, &inner, assumptions, budget)? {
                Ok(ResourceFact::Own(Resource::Composite { name, arguments }, quantity))
                    if quantity.as_const() == Some(1) =>
                {
                    (name, arguments)
                }
                Ok(_) => {
                    return Ok(Err(format!(
                        "loop binder `{binder}` requires one owned resource definition"
                    )
                    .into()));
                }
                Err(error) => {
                    return Ok(Err(format!(
                        "loop binder `{binder}` could not be evaluated here: {error}"
                    )
                    .into()));
                }
            };
        let references =
            match crate::kernel::functions::evaluate_resource_reference_arguments(&state, spec) {
                Ok(references) => references,
                Err(_) => {
                    return Ok(Err(format!(
                        "loop binder `{binder}` requires its declared resource arguments"
                    )
                    .into()));
                }
            };
        state = match rebind_one_loop_binder_instance(
            &state,
            identity,
            &binder,
            (&name, &arguments, &references),
            &mut claimed,
            assumptions,
        ) {
            Ok(state) => state,
            Err(failure) => return Ok(Err(failure)),
        };
    }
    Ok(Ok(state))
}

/// Binds the loop's names again on a state the body reached, taking each
/// binder's family and arguments from the instance it held at the loop head.
///
/// The head already decided what every binder names; a back edge only has to
/// find that resource again in whatever the body ended holding. Nothing here
/// re-reads the loop's source clauses, so the same rule serves the kernel's
/// own back edge and the surface `close_invariants` join.
pub(crate) fn loop_state_with_loop_binders_rebound(
    loop_head_state: &ExecutionState,
    state: &ExecutionState,
    binders: &[LoopBinder],
    assumptions: &PureFactContext,
) -> Result<ExecutionState, String> {
    if binders.is_empty() {
        return Ok(state.clone());
    }
    let mut rebound = state.clone();
    let mut claimed: BTreeSet<InstanceId> = BTreeSet::new();
    for binder in binders {
        // D5: the back edge selects the instance the same way the head did,
        // with the clause's arguments re-evaluated in the current state. A
        // body that assigned `root = root->left` therefore hands the loop the
        // `tree_at(root)` at the new cursor, not the one it started from.
        let declared = binder.spec.as_ref().and_then(|spec| {
            let mut budget = ExecutionBudget::beside_live_state();
            loop_binder_declared_arguments(state, spec, assumptions, &mut budget)
                .ok()
                .flatten()
        });
        let (name, arguments) = match declared {
            Some(declared) => declared,
            None => {
                let Some(head) = loop_head_state.resources().owned_instance(binder.identity) else {
                    continue;
                };
                (head.name.clone(), head.arguments.clone())
            }
        };
        let references = match &binder.spec {
            Some(spec) => {
                crate::kernel::functions::evaluate_resource_reference_arguments(state, spec)
                    .map_err(|_| {
                        format!(
                            "loop binder `{}` requires its declared resource arguments",
                            binder.name
                        )
                    })?
            }
            None => loop_head_state
                .resources()
                .owned_instance(binder.identity)
                .map(|head| head.resource_arguments().to_vec())
                .unwrap_or_default(),
        };
        rebound = rebind_one_loop_binder_instance(
            &rebound,
            binder.identity,
            &binder.name,
            (&name, &arguments, &references),
            &mut claimed,
            assumptions,
        )
        .map_err(|refusal| refusal.context())?;
    }
    Ok(rebound)
}

/// Moves one loop binder onto the instance it names in `state`.
///
/// The binder keeps the instance it already names when that instance still
/// has the right family and arguments. Otherwise exactly one owned instance
/// of that family may match, and it is renamed to the binder's identity. The
/// candidates come from the family's shape bucket, so the search costs the
/// instances of that family rather than the whole resource context.
fn rebind_one_loop_binder_instance(
    state: &ExecutionState,
    identity: InstanceId,
    binder: &str,
    resource: (
        &str,
        &ResourceArguments,
        &[crate::kernel::ResourceReference],
    ),
    claimed: &mut BTreeSet<InstanceId>,
    assumptions: &PureFactContext,
) -> Result<ExecutionState, LoopResourceFailure> {
    let (name, arguments, references) = resource;
    let arguments_match = |instance: &ResourceInstance| {
        instance.resource_arguments() == references
            && instance.arguments.len() == arguments.len()
            && instance
                .arguments
                .iter()
                .zip(arguments.iter())
                .all(|(held, declared)| {
                    crate::kernel::resource_field_values_proven_equal(held, declared, assumptions)
                })
    };
    let selected = if let Some(instance) = state
        .resources()
        .owned_instance(identity)
        .filter(|instance| instance.name == name && arguments_match(instance))
    {
        if instance.arguments == *arguments {
            claimed.insert(identity);
            return Ok(state.clone());
        }
        instance.clone()
    } else {
        let mut candidates = state
            .resources()
            .owned_instances_of_shape(name, arguments.len())
            .into_iter()
            .filter(|instance| !claimed.contains(&instance.identity) && arguments_match(instance))
            .cloned()
            .collect::<Vec<_>>();
        let Some(selected) = candidates.pop() else {
            return Err(LoopResourceFailure::Tactic(format!(
                "loop binder `{binder}` has no owned `{name}` instance at its arguments here"
            )));
        };
        if !candidates.is_empty() {
            let count = candidates.len() + 1;
            let names = candidates
                .iter()
                .chain(std::iter::once(&selected))
                .map(|instance| {
                    crate::kernel::model_fields::registered_instance_spelling(instance.identity)
                        .map(|name| format!("`{name}`"))
                })
                .collect::<Option<Vec<_>>>();
            let choices = names.map_or_else(String::new, |names| {
                format!(" ({}). Use the intended enclosing binder", names.join(", "))
            });
            return Err(LoopResourceFailure::Tactic(format!(
                "loop binder `{binder}` matches {count} owned `{name}` instances at its arguments; a loop binder must name exactly one{choices}"
            )));
        }
        selected
    };
    claimed.insert(identity);
    let held = ResourceFact::own(Resource::Instance(selected.clone()));
    let Some(rebound) = ResourceInstance::new_with_resource_arguments(
        identity,
        selected.name.clone(),
        arguments.clone(),
        selected.schema.clone(),
        selected.fields.clone(),
        selected.resource_arguments().to_vec(),
    ) else {
        return Err(format!(
            "loop binder `{binder}` names an instance whose fields do not match its schema"
        )
        .into());
    };
    // The matching step established the declared argument values on this exit.
    // Publish those values before joining exits, while their equality premises
    // are still available. The rename removes one exact instance fact and adds
    // it back under the binder's identity. Incremental consumption touches its own
    // bucket instead of normalizing the ambient context.
    let Some(resources) = state
        .resources()
        .clone()
        .without_fact_incrementally(&held, assumptions)
    else {
        return Err(format!("loop binder `{binder}` could not take the instance it names").into());
    };
    Ok(state.clone().with_resource_context(
        resources.unchecked_with_fact(ResourceFact::own(Resource::Instance(rebound))),
    ))
}

/// Whether a loop's structural `decreases` binder descends at this back edge,
/// and why not when it does not (D6).
///
/// The instance the binder ends holding must be a strict contained descendant,
/// in the exact resource definitions, of the instance it held at the loop head:
/// the loop head's model selects one arm, that arm names its children, and the
/// back-edge instance is one of them, or one of *their* children by the same
/// rule again, with the submodel that child carries. A model is a finite
/// inductive term, so a strictly deeper submodel at every back edge is
/// well-founded; no counter, size function, or automatic unfolding takes part.
///
/// The evidence is the unfold that exposed the child: the arm comes from
/// [`crate::kernel::select_resource_model_arm`] over the premises this path
/// already carries, which is the one arm-selection decision in Click. Cost is
/// the selected arm's own children and the constructor's own fields; the
/// surrounding resource context is never scanned.
pub(crate) fn loop_structural_descent_failure(
    loop_head_state: &ExecutionState,
    back_edge_state: &ExecutionState,
    binders: &[LoopBinder],
    measure: &str,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Option<String> {
    let Some(binder) = binders.iter().find(|binder| binder.name == measure) else {
        return Some(format!(
            "loop `decreases {measure}` does not name a resource binder this loop declares"
        ));
    };
    let Some(head) = loop_head_state.resources().owned_instance(binder.identity) else {
        return Some(format!(
            "loop `decreases {measure}` has no owned instance at the loop head"
        ));
    };
    let Some(next) = back_edge_state.resources().owned_instance(binder.identity) else {
        return Some(format!(
            "loop `decreases {measure}` has no owned instance at the back edge"
        ));
    };
    structural_instance_descent_failure(
        head,
        next,
        &format!("loop `decreases {measure}`"),
        "the binder holds at the back edge",
        "it held at the loop head",
        definitions,
        assumptions,
    )
}

/// Whether `next` holds a model strictly contained in `head`'s, through the
/// arms the premises in `assumptions` decide, and why not when it does not.
///
/// This is the one structural descent decision: a loop back edge asks it of
/// the instance its binder ends holding, and a call ranked by a structural
/// `decreases t` asks it of the instance the call passes for the callee's
/// measured binder. `label` names the measure, and the two phrases name the
/// two instances, in a refusal.
pub(crate) fn structural_instance_descent_failure(
    head: &ResourceInstance,
    next: &ResourceInstance,
    label: &str,
    next_role: &str,
    head_role: &str,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
) -> Option<String> {
    let measure = label;
    let Some(definition) = definitions
        .iter()
        .find(|definition| definition.name() == head.name)
    else {
        return Some(format!(
            "resource measure `{}` has no definition",
            head.name
        ));
    };
    let Some(body) = definition.matched.as_ref() else {
        return Some(format!(
            "{measure} needs a resource with a `match` body; `{}` has none",
            head.name
        ));
    };
    let Some(crate::kernel::ResourceFieldValue::Algebraic(model)) =
        head.fields.get(body.field_index)
    else {
        return Some(format!(
            "{measure} names an instance whose matched field is not algebraic"
        ));
    };
    let Some(ResourceModelArmSelection::Constructor(constructor)) =
        crate::kernel::select_resource_model_arm(model, assumptions)
    else {
        return Some(format!(
            "{measure} cannot name a child: the facts do not say which `{}` constructor the instance {head_role} carries",
            head.name
        ));
    };
    let AlgebraicTermNode::Constructor { variant, .. } = &constructor.node else {
        return Some(format!("{measure} selected a non-constructor model"));
    };
    if body.arms.iter().all(|arm| &arm.variant != variant) {
        return Some(format!(
            "{measure} selected the unknown constructor `{variant}`"
        ));
    }
    let mut seen = BTreeSet::new();
    if let AlgebraicTermNode::Variable(variable) = &model.node {
        seen.insert(*variable);
    }
    if structural_measure_reaches_instance(
        &constructor,
        definition,
        next,
        definitions,
        assumptions,
        &mut seen,
    ) {
        return None;
    }
    Some(format!(
        "{measure} does not descend: the `{}` {next_role} is not a contained child of the `{}` {head_role}, through the arms this path decided, starting at the `{variant}` arm of `{}`",
        next.name, head.name, head.name
    ))
}

/// Whether the back-edge instance is a contained child of this arm, or of a
/// child of it that the path has likewise decided.
///
/// A direct child is one step of this walk. The uncle-red case of
/// `__rb_insert` sets `node = gparent`, so the frame it hands to the next
/// iteration is `up.up`, two frames above the one the binder held — and the
/// body unfolded each frame it passed, which is exactly what decides that
/// frame's constructor here. The walk follows the evidence the body already
/// produced: it descends only into a child whose own constructor a premise
/// names, and stops the moment one is undecided. It never proves by cases,
/// never searches the resource context, and never unfolds anything itself, so
/// its cost is the constructors this path spelled out.
///
/// `seen` closes the walk over model variables: a premise set that equated a
/// variable with a term mentioning it cannot make this spin.
fn structural_measure_reaches_instance(
    constructor: &AlgebraicTerm,
    definition: &CompositeResourceDefinition,
    next: &ResourceInstance,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    seen: &mut BTreeSet<Variable>,
) -> bool {
    let Some(body) = definition.matched.as_ref() else {
        return false;
    };
    let AlgebraicTermNode::Constructor { variant, fields } = &constructor.node else {
        return false;
    };
    let Some(arm) = body.arms.iter().find(|arm| &arm.variant == variant) else {
        return false;
    };
    for child in &arm.children {
        if child.resource != next.name {
            continue;
        }
        let Some(child_definition) = definitions
            .iter()
            .find(|definition| definition.name() == child.resource)
        else {
            continue;
        };
        let Some(child_body) = child_definition.matched.as_ref() else {
            continue;
        };
        let Some(submodel) = child
            .field_bindings
            .get(child_body.field_index)
            .and_then(|source| match source {
                ResourceChildField::Constructor(index) => fields.get(*index),
                ResourceChildField::Parent(_) => None,
            })
        else {
            continue;
        };
        let Some(held) = next.fields.get(child_body.field_index) else {
            continue;
        };
        if crate::kernel::resource_field_values_proven_equal(held, submodel.into(), assumptions) {
            return true;
        }
        let AlgebraicValue::Algebraic(submodel) = submodel else {
            continue;
        };
        if let AlgebraicTermNode::Variable(variable) = &submodel.node
            && !seen.insert(*variable)
        {
            continue;
        }
        let Some(ResourceModelArmSelection::Constructor(child_constructor)) =
            crate::kernel::select_resource_model_arm(submodel, assumptions)
        else {
            continue;
        };
        if structural_measure_reaches_instance(
            &child_constructor,
            child_definition,
            next,
            definitions,
            assumptions,
            seen,
        ) {
            return true;
        }
    }
    false
}

/// The back-edge state as the ownership join compares it: each loop binder
/// carrying the model it had at the head.
///
/// A binder's fields are what its invariants constrain, and a body is expected
/// to change them; those changes are checked as invariant preservation, not as
/// a change of ownership. The join therefore compares the binder's family and
/// arguments and sets its model aside.
pub(crate) fn loop_state_with_head_binder_models(
    next_state: &ExecutionState,
    head_state: &ExecutionState,
    binders: &[LoopBinder],
) -> ExecutionState {
    let mut state = next_state.clone();
    for binder in binders {
        let identity = binder.identity;
        let Some(head) = head_state.resources().owned_instance(identity) else {
            continue;
        };
        let Some(held) = state.resources().owned_instance(identity).cloned() else {
            continue;
        };
        if held.fields == head.fields && held.arguments == head.arguments {
            continue;
        }
        let Some(compared) = ResourceInstance::new_with_resource_arguments(
            identity,
            held.name.clone(),
            head.arguments.clone(),
            held.schema.clone(),
            head.fields.clone(),
            held.resource_arguments().to_vec(),
        ) else {
            continue;
        };
        let Some(resources) = state.resources().clone().without_fact_incrementally(
            &ResourceFact::own(Resource::Instance(held)),
            &PureFactContext::new(),
        ) else {
            continue;
        };
        state = state.with_resource_context(
            resources.unchecked_with_fact(ResourceFact::own(Resource::Instance(compared))),
        );
    }
    state
}

/// Gives each loop binder instance fresh symbolic fields.
///
/// A loop head is an arbitrary visit, so the model a binder carries there is
/// whatever the invariants state about it, never the model it happened to
/// carry at loop entry. This is the resource-field counterpart of havocking
/// the locals the body writes.
fn havoc_loop_binder_instance_fields(
    state: &ExecutionState,
    resource_specs: &[ResourceSpec],
    assumptions: &PureFactContext,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<ExecutionState> {
    let mut state = state.clone();
    for spec in resource_specs {
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        let Some(instance) = state.resources().owned_instance(identity).cloned() else {
            continue;
        };
        let arguments = match loop_binder_declared_arguments(&state, spec, assumptions, budget)? {
            Some((_, arguments)) => arguments,
            None => instance.arguments.clone(),
        };
        let fields = crate::kernel::functions::fresh_resource_instance_fields(
            &instance.schema,
            crate::kernel::functions::ModelFieldMintSite {
                identity,
                minted_by: &crate::kernel::model_fields::ModelMint::LoopHead,
            },
            variables,
            budget,
        )?;
        let Some(havoced) = ResourceInstance::new_with_resource_arguments(
            identity,
            instance.name.clone(),
            arguments,
            instance.schema.clone(),
            fields,
            instance.resource_arguments().to_vec(),
        ) else {
            continue;
        };
        let held = ResourceFact::own(Resource::Instance(instance));
        let Some(resources) = state
            .resources()
            .clone()
            .without_fact_incrementally(&held, &PureFactContext::new())
        else {
            continue;
        };
        state = state.with_resource_context(
            resources.unchecked_with_fact(ResourceFact::own(Resource::Instance(havoced))),
        );
    }
    Ok(state)
}

/// The family and arguments one `owns name: resource(args);` clause denotes
/// in `state`.
///
/// `None` means the clause could not be read here; the caller keeps whatever
/// the instance already carries rather than inventing arguments.
fn loop_binder_declared_arguments(
    state: &ExecutionState,
    spec: &ResourceSpec,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<(String, ResourceArguments)>> {
    let Some(inner) = spec.instance_resource_spec() else {
        return Ok(None);
    };
    // This helper returns scalar arguments only. Its callers retain and check
    // reference arguments separately when selecting or reconstructing an instance.
    let inner = inner.with_resource_arguments(Vec::new());
    Ok(
        match evaluate_function_resource_spec(state, &inner, assumptions, budget)? {
            Ok(ResourceFact::Own(Resource::Composite { name, arguments }, quantity))
                if quantity.as_const() == Some(1) =>
            {
                Some((name, arguments))
            }
            _ => None,
        },
    )
}

/// The read-only form of a resource the loop did not declare. SymbolicMemory and
/// composite resources have one; an exclusive token or instance does not, so
/// the body simply does not hold it.
fn viewed_form_of_resource_fact(fact: &ResourceFact) -> Option<ResourceFact> {
    match fact {
        ResourceFact::Own(
            Resource::Footprint(_) | Resource::Parameter(_) | Resource::Emp | Resource::Star(_),
            _,
        ) => None,
        ResourceFact::View(_) => Some(fact.clone()),
        ResourceFact::Own(resource @ (Resource::Memory(_) | Resource::Composite { .. }), _) => {
            Some(ResourceFact::View(resource.clone()))
        }
        ResourceFact::Own(
            Resource::Token { .. }
            | Resource::PopulationAuthority(_)
            | Resource::Instance(_)
            | Resource::ConditionalMutexGuard(_)
            | Resource::MutexGuard(_)
            | Resource::MutexLive(_)
            | Resource::MutexUse(_)
            | Resource::Publication(_)
            | Resource::Iterated(_),
            _,
        ) => None,
    }
}

pub(super) fn collect_loop_effect_check_obligations(
    before_state: &ExecutionState,
    after_state: &ExecutionState,
    effect_checks: &[LoopEffectCheck],
    facts: &(impl ExecutionFactSource + ?Sized),
    path_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ProofObligation>> {
    if effect_checks.is_empty() {
        return Ok(Vec::new());
    }

    let effective_assumptions = assumptions_with_path_context(assumptions, facts, path_obligations);
    let mut writes = after_state
        .memory()
        .differing_cell_pointers(before_state.memory())
        .into_iter()
        .filter(is_loop_effect_relevant_pointer)
        .filter(|pointer| {
            let has_disjoint_effect_summary = facts.fact_iter().any(|fact| {
                matches!(
                    fact.proposition(),
                    Proposition::MemoryEffectSummary { mutable_ranges, .. }
                        if effective_assumptions
                            .ranges_proven_disjoint_from_pointer(mutable_ranges, pointer)
                )
            });
            // The cell is read at the kind it holds; a cell neither state
            // types stays a candidate.
            let Some(kind) = after_state
                .memory()
                .known_value(pointer)
                .or_else(|| before_state.memory().known_value(pointer))
                .and_then(|value| LoadKind::of_value(&value))
            else {
                return true;
            };
            !has_disjoint_effect_summary
                || !explicit_atomic_equality_from_memory_derivations(
                    &OldMachineTerm::read_named(
                        before_state.memory_named_point(),
                        pointer.clone(),
                        kind,
                    ),
                    &OldMachineTerm::read_named(
                        after_state.memory_named_point(),
                        pointer.clone(),
                        kind,
                    ),
                    &effective_assumptions,
                )
        })
        .map(|pointer| {
            let bytes = after_state
                .memory()
                .known_value(&pointer)
                .or_else(|| before_state.memory().known_value(&pointer))
                .map_or_else(
                    || {
                        crate::kernel::AccessExtent::Bytes(
                            crate::kernel::resource_tracker::widest_scalar_access_bytes(),
                        )
                    },
                    |value| crate::kernel::assumptions::access_extent_of_value(&value),
                );
            (pointer, bytes)
        })
        .collect::<BTreeMap<_, _>>();
    for (pointer, bytes) in facts
        .fact_iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::MemoryMutatesOnly { writes, .. } => Some(writes.as_slice()),
            _ => None,
        })
        .flatten()
    {
        writes
            .entry(pointer.clone())
            .and_modify(|known| *known = (*known).max(*bytes))
            .or_insert(*bytes);
    }
    let effect_summary_ranges = facts
        .fact_iter()
        .filter_map(|fact| match fact.proposition() {
            Proposition::MemoryEffectSummary { mutable_ranges, .. } => {
                Some(mutable_ranges.as_slice())
            }
            _ => None,
        })
        .flatten()
        .filter(|range| is_loop_effect_relevant_pointer(range.base()))
        .collect::<Vec<_>>();

    let mut obligations = Vec::new();
    for check in effect_checks {
        let mut segment_evaluation_failed = false;
        let segments = match check.effect() {
            LoopEffect::Mutable(segments) => {
                if let Some(validated) = check.validated_ranges() {
                    validated
                        .iter()
                        .map(|range| EvaluatedMemorySegment {
                            provenance: range.provenance.clone(),
                            carrier: range.carrier_array().clone(),
                            base: range.base.clone(),
                            start: range.bound_terms().0.clone(),
                            end: range.bound_terms().1.clone(),
                            element_width: range.element_width,
                            kind: range.kind(),
                            formation_coverage: range.formation_coverage.clone(),
                        })
                        .collect()
                } else if matches!(
                    check.origin(),
                    LoopEffectOrigin::InheritedResourceDerived | LoopEffectOrigin::DeclaredResource
                ) {
                    segment_evaluation_failed = true;
                    push_false_loop_effect_obligation(
                        &mut obligations,
                        loop_effect_failure_context(
                            check,
                            "resource-derived loop frame was not established from the checked entry transition".to_string(),
                        ),
                    );
                    Vec::new()
                } else {
                    let mut evaluated = Vec::new();
                    for (segment_index, segment) in segments.iter().enumerate() {
                        match evaluate_loop_effect_segment(
                            before_state,
                            segment,
                            &effective_assumptions,
                            budget,
                        )? {
                            Ok(segment) => evaluated.push(segment),
                            Err(message) => {
                                segment_evaluation_failed = true;
                                push_false_loop_effect_obligation(
                                    &mut obligations,
                                    loop_effect_failure_context(
                                        check,
                                        format!(
                                            "could not evaluate the loop's mutable segment {segment_index}: {message}"
                                        ),
                                    ),
                                );
                            }
                        }
                    }
                    evaluated
                }
            }
        };

        if segment_evaluation_failed {
            continue;
        }

        for (pointer, bytes) in &writes {
            // A whole object of abstract size fits no byte-counted segment.
            if !bytes.bytes().is_some_and(|bytes| {
                segments.iter().any(|segment| {
                    loop_effect_segment_contains_pointer(
                        segment,
                        pointer,
                        bytes,
                        &effective_assumptions,
                    )
                })
            }) {
                push_false_loop_effect_obligation(
                    &mut obligations,
                    loop_effect_failure_context(
                        check,
                        format!(
                            "a {bytes}-byte write in the loop body is outside the loop's mutable footprint ({})",
                            describe_loop_footprint_segments(&segments)
                        ),
                    ),
                );
            }
        }

        for range in &effect_summary_ranges {
            if !segments.iter().any(|segment| {
                loop_effect_segment_contains_range(segment, range, &effective_assumptions)
            }) {
                push_false_loop_effect_obligation(
                    &mut obligations,
                    loop_effect_failure_context(
                        check,
                        format!(
                            "a call in the loop body may write {} outside the loop's mutable footprint ({})",
                            describe_loop_footprint_range(
                                range.bound_terms().0,
                                range.bound_terms().1,
                                range.element_width
                            ),
                            describe_loop_footprint_segments(&segments)
                        ),
                    ),
                );
            }
        }
    }

    Ok(obligations)
}

pub(super) fn evaluate_loop_effect_segment(
    state: &ExecutionState,
    segment: &MemorySegment,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<EvaluatedMemorySegment, ValueRefusal>> {
    Ok(
        evaluate_loop_effect_segment_with_facts(state, segment, assumptions, budget)?.map(
            |(mut segment, facts)| {
                segment.formation_coverage = facts
                    .iter()
                    .filter_map(|fact| match fact.proposition() {
                        Proposition::Predicate { name, .. }
                            if name
                                .starts_with(crate::kernel::SUBOBJECT_COVERS_PREDICATE_PREFIX) =>
                        {
                            Some(fact.proposition().clone())
                        }
                        _ => None,
                    })
                    .collect();
                segment
            },
        ),
    )
}

pub(super) fn evaluate_loop_effect_segment_with_facts(
    state: &ExecutionState,
    segment: &MemorySegment,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(EvaluatedMemorySegment, ExecutionFacts), ValueRefusal>> {
    let mut facts = Vec::new();
    let mut evaluate = |expression: &ProgramExpression, label: &str| {
        let local_assumptions = assumptions_with_path_context(assumptions, &facts, &[]);
        let evaluated = evaluate_loop_effect_segment_value_with_facts(
            state,
            expression,
            &local_assumptions,
            label,
            budget,
        )?;
        let (value, new_facts) = match evaluated {
            Ok(evaluated) => evaluated,
            Err(message) => return Ok(Err(message)),
        };
        for fact in new_facts {
            if !facts.contains(&fact) {
                facts.push(fact);
            }
        }
        Ok(Ok(value))
    };
    let base = match evaluate(&segment.base, "segment base")? {
        Ok(ProgramValue::Pointer(pointer)) => pointer,
        Ok(value) => {
            return Ok(Err(ValueRefusal::from(format!(
                "segment base evaluated to a {} value, not a pointer",
                super::functions::program_type_spelling(value.program_type())
            ))));
        }
        Err(message) => return Ok(Err(message)),
    };
    let base_value = base;
    let base = base_value.address().clone();
    let start_value = evaluate(&segment.start, "segment start")?;
    let end_value = evaluate(&segment.end, "segment end")?;
    // A range with a 64-bit bound retains that bound's width.
    // Evaluate each endpoint only once.
    if let (Ok(start), Ok(end)) = (&start_value, &end_value)
        && let Some((start, end)) = crate::kernel::wide_range_bounds(start, end)
    {
        let evaluated = EvaluatedMemorySegment {
            provenance: base_value.provenance().clone(),
            carrier: crate::kernel::primitives::ArrayObject::from_parts(
                base_value.bounds_are_known(),
                None,
                base_value.bounds_owner().cloned(),
            ),
            base,
            start,
            end,
            element_width: segment.element_width,
            kind: RangeIndexKind::UInt64,
            formation_coverage: Default::default(),
        };
        let context = assumptions_with_path_context(assumptions, &facts, &[]);
        if let Some(refusal) = segment_bounds_refusal(&base_value, &evaluated, &context) {
            return Ok(Err(refusal.into()));
        }
        return Ok(Ok((evaluated, facts.into())));
    }
    let start = match start_value {
        Ok(ProgramValue::Int32(value)) => value,
        Ok(value) if crate::kernel::narrow_range_constant(&value).is_some() => {
            crate::kernel::narrow_range_constant(&value).expect("checked above")
        }
        Ok(value) => {
            return Ok(Err(ValueRefusal::from(format!(
                "segment start evaluated to a {} value, not an int32",
                super::functions::program_type_spelling(value.program_type())
            ))));
        }
        Err(message) => return Ok(Err(message)),
    };
    let end = match end_value {
        Ok(ProgramValue::Int32(value)) => value,
        Ok(value) if crate::kernel::narrow_range_constant(&value).is_some() => {
            crate::kernel::narrow_range_constant(&value).expect("checked above")
        }
        Ok(value) => {
            return Ok(Err(ValueRefusal::from(format!(
                "segment end evaluated to a {} value, not an int32",
                super::functions::program_type_spelling(value.program_type())
            ))));
        }
        Err(message) => return Ok(Err(message)),
    };
    let element_width = segment.element_width;
    let evaluated = EvaluatedMemorySegment {
        provenance: base_value.provenance().clone(),
        carrier: crate::kernel::primitives::ArrayObject::from_parts(
            base_value.bounds_are_known(),
            None,
            base_value.bounds_owner().cloned(),
        ),
        base,
        start,
        end,
        element_width,
        kind: RangeIndexKind::Int32,
        formation_coverage: Default::default(),
    };
    let context = assumptions_with_path_context(assumptions, &facts, &[]);
    if let Some(refusal) = segment_bounds_refusal(&base_value, &evaluated, &context) {
        return Ok(Err(refusal.into()));
    }
    Ok(Ok((evaluated, facts.into())))
}

pub(super) fn evaluate_loop_effect_segment_value(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ProgramValue, ValueRefusal>> {
    Ok(evaluate_loop_effect_segment_value_with_facts(
        state,
        expression,
        assumptions,
        label,
        budget,
    )?
    .map(|(value, _)| value))
}

/// How a segment endpoint the facts do not keep defined is refused. A
/// clause that fails this way needs a requirement, not another clause's
/// cells, so the resource evaluator does not report it as a stall.
pub(in crate::kernel) const UNRULED_OUT_UNDEFINED_BEHAVIOR: &str =
    "may have undefined behavior the facts do not rule out";

/// Why a resource or loop-effect expression has no single defined value.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::kernel) struct ValueRefusal {
    message: String,
    /// The expression may have undefined behavior the facts do not rule
    /// out: a requirement repairs it, never another clause's cells.
    undefined_behavior: bool,
}

impl ValueRefusal {
    pub(in crate::kernel) fn is_undefined_behavior(&self) -> bool {
        self.undefined_behavior
    }
}

impl From<String> for ValueRefusal {
    fn from(message: String) -> Self {
        Self {
            message,
            undefined_behavior: false,
        }
    }
}

impl From<ValueRefusal> for String {
    fn from(refusal: ValueRefusal) -> Self {
        refusal.message
    }
}

impl std::fmt::Display for ValueRefusal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.message)
    }
}

fn evaluate_loop_effect_segment_value_with_facts(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<(ProgramValue, ExecutionFacts), ValueRefusal>> {
    evaluate_loop_effect_segment_value_capturing(
        state,
        expression,
        assumptions,
        label,
        budget,
        None,
    )
}

pub(super) fn evaluate_resource_argument_value(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
    diagnostic: &mut Option<RuntimeError>,
) -> ExecutionResult<Result<ProgramValue, ValueRefusal>> {
    Ok(evaluate_loop_effect_segment_value_capturing(
        state,
        expression,
        assumptions,
        label,
        budget,
        Some(diagnostic),
    )?
    .map(|(value, _)| value))
}

pub(super) fn evaluate_resource_argument_value_retained(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
    diagnostic: &mut Option<RuntimeError>,
) -> ExecutionResult<Result<ExecutionValue, ValueRefusal>> {
    Ok(evaluate_loop_effect_segment_value_retained_capturing(
        state,
        expression,
        assumptions,
        label,
        budget,
        Some(diagnostic),
    )?
    .map(|(value, _)| value))
}

fn evaluate_loop_effect_segment_value_capturing(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
    diagnostic: Option<&mut Option<RuntimeError>>,
) -> ExecutionResult<Result<(ProgramValue, ExecutionFacts), ValueRefusal>> {
    Ok(evaluate_loop_effect_segment_value_retained_capturing(
        state,
        expression,
        assumptions,
        label,
        budget,
        diagnostic,
    )?
    .map(|(value, facts)| (value.into_native(), facts)))
}

pub(super) fn evaluate_loop_effect_segment_value_retained(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Result<ExecutionValue, ValueRefusal>> {
    Ok(evaluate_loop_effect_segment_value_retained_capturing(
        state,
        expression,
        assumptions,
        label,
        budget,
        None,
    )?
    .map(|(value, _)| value))
}

fn evaluate_loop_effect_segment_value_retained_capturing(
    state: &ExecutionState,
    expression: &ProgramExpression,
    assumptions: &PureFactContext,
    label: &str,
    budget: &mut ExecutionBudget,
    diagnostic: Option<&mut Option<RuntimeError>>,
) -> ExecutionResult<Result<(ExecutionValue, ExecutionFacts), ValueRefusal>> {
    // A contract's operand, such as a resource argument, is a specification:
    // its reads are not C accesses, and facts must not replace pointer metadata.
    // Use the same fact-stable evaluation as written proof propositions so a
    // resource footprint and its explicit memory(...) spelling have one identity.
    let paths = {
        let _specification = crate::kernel::eval::SpecificationReadScope::enter();
        crate::kernel::eval::evaluate_expression_value_paths(
            state,
            expression,
            assumptions,
            budget,
        )?
    };
    // An endpoint the facts do not keep defined splits into its defined value
    // and the undefined behavior beside it: name that behavior, which a
    // requirement can rule out, rather than the path count.
    let undefined = paths
        .iter()
        .filter_map(|path| match &path.outcome {
            ExpressionOutcome::UndefinedBehavior(undefined) => Some(undefined.description()),
            _ => None,
        })
        .collect::<BTreeSet<_>>();
    if paths.len() > 1 && !undefined.is_empty() {
        return Ok(Err(ValueRefusal {
            message: format!(
                "{label} {UNRULED_OUT_UNDEFINED_BEHAVIOR}: {}",
                undefined.into_iter().collect::<Vec<_>>().join("; ")
            ),
            undefined_behavior: true,
        }));
    }
    if paths.len() != 1 {
        return Ok(Err(ValueRefusal::from(format!(
            "{label} evaluated through {} paths, expected exactly one",
            paths.len()
        ))));
    }
    let Some(path) = paths.into_iter().next() else {
        return Ok(Err(ValueRefusal::from(format!(
            "{label} had no evaluation path"
        ))));
    };
    if !path.obligations.is_empty() {
        // Named by the sentences their lowering wrote; the kernel has no
        // source spelling of the conditions themselves.
        let contexts = path
            .obligations
            .iter()
            .map(|obligation| obligation.context().unwrap_or("an unnamed condition"))
            .collect::<Vec<_>>();
        // A cast to `int32` written in a bound has to be exact. Say what
        // to state, and that the range needs no cast.
        let narrowing = contexts
            .iter()
            .any(|context| context.contains("int32 narrowing"));
        return Ok(Err(ValueRefusal::from(format!(
            "{label} left {} proof obligation(s): {}{}",
            contexts.len(),
            contexts.join("; "),
            if narrowing {
                "; this bound is cast to a 32-bit index, so the contract has to state that it \
                 fits one, as in `requires n <= 2147483647`; a range with a 64-bit bound written \
                 without a cast needs no such bound"
            } else {
                ""
            }
        ))));
    }
    match path.outcome {
        ExpressionOutcome::Value(value) => {
            // Segment and contract arguments retain the value, not its temporary
            // fact stream. As for recursive child indices, carry only certified
            // typed-read definitions and cached observations into this context.
            for fact in &path.facts {
                fact.retain_pointer_read_definition(assumptions);
            }
            Ok(Ok((value, path.facts)))
        }
        ExpressionOutcome::UndefinedBehavior(UndefinedBehavior::UninitializedRead) => {
            Ok(Err(ValueRefusal::from(format!(
                "{label} could not establish that the memory location contains an initialized value"
            ))))
        }
        ExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
            Ok(Err(ValueRefusal::from(format!(
                "{label} produced undefined behavior: {}",
                undefined_behavior.description()
            ))))
        }
        ExpressionOutcome::RuntimeError(error) => {
            if let RuntimeError::MissingResource { resource } = &error {
                crate::kernel::functions::record_resource_dependency(*resource.clone());
                if let Some(diagnostic) = diagnostic {
                    *diagnostic = Some(RuntimeError::ContractResourceDiagnostic {
                        reason: format!(
                            "{label} could not be evaluated: required access authority is unavailable"
                        ),
                        held: None,
                        required: resource.clone(),
                        memory: Some(Box::new(state.memory().clone())),
                    });
                }
            }
            Ok(Err(ValueRefusal::from(format!(
                "{label} produced runtime error: {}",
                super::api::contract_certification::describe_certification_runtime_error(&error)
            ))))
        }
    }
}

pub(super) fn loop_effect_segment_contains_pointer(
    segment: &EvaluatedMemorySegment,
    pointer: &Address,
    bytes: u32,
    assumptions: &PureFactContext,
) -> bool {
    // An unnamed footprint covers every access: it is the write set of
    // memory the frame's resources reach past what their clauses name.
    if crate::kernel::primitives::is_unnamed_footprint_base(&segment.base) {
        return true;
    }
    assumptions.pointer_access_in_memory_range(pointer, bytes, &segment.clone().into_range())
}

pub(super) fn loop_effect_segment_contains_range(
    segment: &EvaluatedMemorySegment,
    range: &MemoryRange,
    assumptions: &PureFactContext,
) -> bool {
    if crate::kernel::primitives::is_unnamed_footprint_base(&segment.base) {
        return true;
    }
    if range.wide_bounds().is_some() || segment.kind == RangeIndexKind::UInt64 {
        return crate::kernel::primitives::wide_memory_range_covers(
            &segment.clone().into_range(),
            range,
            assumptions,
        );
    }
    if range.element_width() != segment.element_width {
        return false;
    }
    let Some(base_index) = range
        .base()
        .shared_element_index_from_base_with_width(&segment.base, segment.element_width)
    else {
        return false;
    };
    let range_start = crate::kernel::assumptions::index_binary(
        MachineBinaryOp::Add,
        base_index.operand_view(),
        MachineOperandView::Old(range.start()),
    );
    let range_end = crate::kernel::assumptions::index_binary(
        MachineBinaryOp::Add,
        base_index.operand_view(),
        MachineOperandView::Old(range.end()),
    );
    condition_is_decided_true(
        assumptions,
        &crate::kernel::assumptions::index_comparison(
            CompareRelation::LessEqual,
            MachineOperandView::Old(&segment.start),
            range_start.operand_view(),
        ),
    ) && condition_is_decided_true(
        assumptions,
        &crate::kernel::assumptions::index_comparison(
            CompareRelation::LessEqual,
            range_end.operand_view(),
            MachineOperandView::Old(&segment.end),
        ),
    )
}

pub(super) fn is_loop_effect_relevant_pointer(pointer: &Address) -> bool {
    !pointer.base.is_local_block() && !pointer.base.is_havoc_block()
}

/// A footprint range for a loop-effect refusal, without the kernel's
/// internal spelling of its base: the kernel has no source names here, and a
/// `Debug` of the pointer or of symbolic bounds is lowering state rather than
/// anything the reader wrote. Constant bounds are the one part worth printing.
fn describe_loop_footprint_range(
    start: &OldMachineTerm,
    end: &OldMachineTerm,
    element_width: u32,
) -> String {
    match (start.as_const(), end.as_const()) {
        (Some(start), Some(end)) => format!(
            "elements {}..{} of a {element_width}-byte-element range",
            start as i32, end as i32
        ),
        _ => format!("a range of {element_width}-byte elements"),
    }
}

/// How many mutable segments the loop declared and could evaluate, for a
/// loop-effect refusal.
fn describe_loop_footprint_segments(segments: &[EvaluatedMemorySegment]) -> String {
    match segments.len() {
        0 => "the loop declares no mutable memory".to_string(),
        1 => "no part of its one mutable segment covers it".to_string(),
        count => format!("none of its {count} mutable segments covers it"),
    }
}

pub(super) fn loop_effect_failure_context(check: &LoopEffectCheck, message: String) -> String {
    match check.context() {
        Some(context) => format!("{context}: {message}"),
        None => message,
    }
}

pub(super) fn push_false_loop_effect_obligation(
    obligations: &mut Vec<ProofObligation>,
    context: String,
) {
    obligations.push(
        ProofObligation::verification_condition(false_equals_true_proposition())
            .with_context(context),
    );
}

pub(super) fn false_equals_true_proposition() -> Proposition {
    Proposition::Equal(
        Term::Condition(OldConditionTerm::Constant(false).into()),
        Term::Condition(OldConditionTerm::Constant(true).into()),
    )
}

#[allow(clippy::too_many_arguments)]
pub(super) fn assume_invariant_checks(
    state: &ExecutionState,
    loop_entry_state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    iterations: &IntegerTerm,
    assumptions: &PureFactContext,
    prefix_facts: &(impl ExecutionFactSource + ?Sized),
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<HeadContexts> {
    assume_invariant_checks_explained(
        state,
        loop_entry_state,
        invariant_checks,
        iterations,
        assumptions,
        prefix_facts,
        prefix_obligations,
        budget,
    )
    .map(|(contexts, _)| contexts)
}

type HeadContexts = Vec<(
    ExecutionFacts,
    Vec<ProofObligation>,
    crate::kernel::proof::PersistentSequence<Proposition>,
)>;

/// Why the loop head could not assume its invariants: the first declaration
/// that left no context, by its position, and what happened to it.
pub(super) struct HeadInvariantRefusal {
    declaration: usize,
    reason: String,
}

impl HeadInvariantRefusal {
    fn describe(&self) -> String {
        format!(
            "the loop head cannot assume invariant {}: {}",
            self.declaration + 1,
            self.reason
        )
    }
}

/// [`assume_invariant_checks`], also saying which declaration left the head
/// with no context when that happens.
#[allow(clippy::too_many_arguments)]
fn assume_invariant_checks_explained(
    state: &ExecutionState,
    loop_entry_state: &ExecutionState,
    invariant_checks: &[LoopInvariantCheck],
    iterations: &IntegerTerm,
    assumptions: &PureFactContext,
    prefix_facts: &(impl ExecutionFactSource + ?Sized),
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<(HeadContexts, Option<HeadInvariantRefusal>)> {
    // The head assumes the invariants at its own pass count, a fresh `K`
    // that is never negative.
    let _iterations = crate::kernel::spec::LoopIterationsScope::enter(iterations.clone());
    let mut head_facts = prefix_facts.persistent_facts();
    head_facts.push(ExecutionPureFact::new(Proposition::condition_is(
        OldConditionTerm::IntegerLessEqual(
            IntegerTerm::constant(0.into()).into(),
            iterations.clone().into(),
        ),
        true,
    )));
    // Each lowering path forks this declaration history. Keep its prefix
    // persistent so a loop with many explicit invariants does not clone the
    // whole preceding clause vector at every declaration.
    let mut contexts = vec![(
        head_facts,
        prefix_obligations.to_vec(),
        crate::kernel::proof::PersistentSequence::default(),
    )];
    for (declaration, check) in invariant_checks.iter().enumerate() {
        let mut next_contexts = Vec::new();
        let mut lowered_any = false;
        let dropped_span_before = budget.dropped_range_span().is_some();
        for (facts, obligations, invariant_propositions) in contexts {
            let effective_assumptions =
                assumptions_with_path_context(assumptions, &facts, &obligations);
            for path in crate::kernel::spec::lower_assumed_interface_proposition(
                state,
                check.proposition(),
                Some(loop_entry_state),
                &effective_assumptions,
                budget,
            )? {
                lowered_any = true;
                // Every side condition the lowering emits — a stated range's
                // span half, an int32 conversion's bounds, a count that
                // must not overflow, a checked read's definedness — is
                // invariant content: `collect_invariant_check_obligations`
                // owes every obligation this lowering emits at entry and at
                // every back edge, together with the proposition. So the head
                // assumes them beside it instead of demanding them as
                // prerequisites of a hypothesis it never has to prove.
                let mut path_facts = path.facts;
                path_facts.extend(
                    path.obligations
                        .into_iter()
                        .map(|obligation| ExecutionPureFact::new(obligation.proposition)),
                );
                let Some((mut facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &facts,
                    &obligations,
                    &path_facts,
                    &[],
                    assumptions,
                ) else {
                    continue;
                };
                // A loop invariant is an explicit induction hypothesis at the
                // fresh loop-top state. Even when the entry assumptions can
                // derive it, retain the lowered proposition itself: the facts
                // used for that derivation may belong to an earlier state
                // and are not a substitute for this loop's hypothesis after
                // havoc.
                let mut invariant_propositions = invariant_propositions.clone();
                invariant_propositions.push(path.proposition.clone());
                if assumptions.proves_exact(&path.proposition)
                    || facts
                        .iter()
                        .any(|fact| fact.proposition() == &path.proposition)
                {
                    if !facts
                        .iter()
                        .any(|fact| fact.proposition() == &path.proposition)
                    {
                        facts.push(ExecutionPureFact::new(path.proposition));
                    }
                    next_contexts.push((facts, obligations, invariant_propositions));
                } else {
                    let before = facts.len();
                    if add_path_fact(&mut facts, assumptions, path.proposition.clone()).is_some() {
                        // A condition inferred from the enclosing context is
                        // consistent but add_path_fact need not emit it. The
                        // loop head still owes its declared hypothesis to the
                        // separate preservation proof and exit correspondence.
                        if facts.len() == before && !equation_states_nothing(&path.proposition) {
                            // Intrinsic truths carry no induction information.
                            // Keep their existing omission so explicit closure
                            // scripts still see the same reflexive obligation.
                            facts.push(ExecutionPureFact::new(path.proposition));
                        }
                        next_contexts.push((facts, obligations, invariant_propositions));
                    }
                }
            }
        }
        if next_contexts.is_empty() {
            let reason = if lowered_any {
                "assuming it contradicts the invariants before it and the facts the loop \
                 keeps"
                    .to_string()
            } else if !dropped_span_before && let Some(span) = budget.dropped_range_span() {
                format!(
                    "it has no reading at the loop head: {}",
                    dropped_range_span_reason(span)
                )
            } else {
                "it has no reading at the loop head".to_string()
            };
            return Ok((
                next_contexts,
                Some(HeadInvariantRefusal {
                    declaration,
                    reason,
                }),
            ));
        }
        contexts = next_contexts;
    }
    Ok((contexts, None))
}

/// What one evaluation path of a loop guard settled.
#[derive(Clone, Debug)]
pub(super) enum ConditionBranch {
    /// The guard produced a value, and its truthiness is this.
    Decided(bool),
    /// The guard produced no value at all on this path: an operand the
    /// function has no authority to read, an unresolved allocation, or
    /// undefined behavior reached while evaluating it. Such a path selects
    /// neither the iteration nor the exit, so it may never be dropped — the
    /// exit assumption would otherwise be the negation of the operands that
    /// happened to be evaluable, which is not the negation of the guard.
    Undecided(StatementOutcome),
}

/// One way a loop guard can leave a state, with the facts and obligations
/// that path carries.
#[derive(Clone, Debug)]
pub(super) struct ConditionAssumption {
    pub(super) branch: ConditionBranch,
    pub(super) facts: ExecutionFacts,
    pub(super) obligations: Vec<ProofObligation>,
}

impl ConditionAssumption {
    /// The statement outcome an undecided guard must be reported as, or
    /// `None` when the guard decided this path.
    pub(super) fn undecided_outcome(&self) -> Option<&StatementOutcome> {
        match &self.branch {
            ConditionBranch::Decided(_) => None,
            ConditionBranch::Undecided(outcome) => Some(outcome),
        }
    }
}

/// Every way this guard can leave `state`: one entry per feasible value path,
/// plus one entry for each path on which the guard could not be evaluated.
///
/// When the function has composite definitions, a short-circuit guard is
/// evaluated conjunct by conjunct, because a later conjunct is read under the
/// truth of its earlier ones and that prefix may publish read authority (D7,
/// extended to the arms a prefix leaves possible). `parent != 0 &&
/// node == parent->rb_right` is the shape: the first conjunct refutes the
/// folded frame's `Top` arm, the `Left` and `Right` arms both own
/// `parent->rb_right`, and the second conjunct reads it. Any other guard is
/// evaluated whole. Either way the guard is evaluated once.
pub(super) fn assume_condition_branches(
    state: &ExecutionState,
    condition: &ProgramExpression,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    prefix_facts: &(impl ExecutionFactSource + ?Sized),
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ConditionAssumption>> {
    let mut conjuncts = Vec::new();
    if !definitions.is_empty() {
        guard_conjuncts(condition, &mut conjuncts);
    }
    if conjuncts.len() < 2 {
        return assume_condition_branches_at_state(
            state,
            condition,
            assumptions,
            prefix_facts,
            prefix_obligations,
            budget,
        );
    }
    assume_guard_conjunct_branches(
        state,
        &conjuncts,
        definitions,
        assumptions,
        prefix_facts,
        prefix_obligations,
        budget,
    )
}

/// The top-level conjuncts of a short-circuit guard, left to right.
///
/// `a && b && c` is one guard with three exit paths and three reading
/// positions; anything else is one conjunct, evaluated exactly as it is.
fn guard_conjuncts<'a>(
    condition: &'a ProgramExpression,
    conjuncts: &mut Vec<&'a ProgramExpression>,
) {
    match condition {
        ProgramExpression::And(left, right) => {
            guard_conjuncts(left, conjuncts);
            guard_conjuncts(right, conjuncts);
        }
        _ => conjuncts.push(condition),
    }
}

/// Every way a short-circuit guard can leave `state`, evaluating conjunct `k`
/// under the truth of conjuncts `1..k-1` and under the read authority those
/// truths publish.
///
/// The C is unchanged: the guard is false as soon as one conjunct is false,
/// true when the last one is, and undecided wherever a conjunct produced no
/// value — which is the refusal S1 installed, kept here. What evaluating by
/// conjunct adds is where each conjunct is read: a folded matched instance publishes the
/// cells every arm the prefix leaves possible owns, so a conjunct may read what
/// an earlier conjunct unlocked and nothing more.
///
/// Cost is one evaluation of each conjunct per live prefix, plus one arm-view
/// publication per conjunct: the arms of the instances held, evaluated once
/// each. No conjunct is revisited and no prefix is searched over.
fn assume_guard_conjunct_branches(
    state: &ExecutionState,
    conjuncts: &[&ProgramExpression],
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    prefix_facts: &(impl ExecutionFactSource + ?Sized),
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ConditionAssumption>> {
    let mut branches = Vec::new();
    let mut live = vec![(prefix_facts.persistent_facts(), prefix_obligations.to_vec())];
    for (index, conjunct) in conjuncts.iter().enumerate() {
        let is_last = index + 1 == conjuncts.len();
        let mut next = Vec::new();
        for (facts, obligations) in live {
            let conjunct_state =
                with_guard_prefix_arm_views(state, definitions, assumptions, &facts, &obligations);
            for assumption in assume_condition_branches_at_state(
                &conjunct_state,
                conjunct,
                assumptions,
                &facts,
                &obligations,
                budget,
            )? {
                match assumption.branch {
                    // A true conjunct that is not the last decides nothing on
                    // its own; it is the premise the next one is read under.
                    ConditionBranch::Decided(true) if !is_last => {
                        next.push((assumption.facts, assumption.obligations));
                    }
                    _ => branches.push(assumption),
                }
            }
        }
        live = next;
    }
    budget.check_path_width(branches.len())?;
    Ok(branches)
}

/// `state` with the cells published that every arm the guard prefix in `facts`
/// leaves possible owns (D7).
///
/// The prefix's own conclusion comes first: a conjunct that contradicts an
/// arm's binding-free fact refutes that arm, which is the same refutation rule
/// the loop head, the back edge, and the exit already apply, and it is what
/// leaves a set of possible arms rather than a decided one. Ownership is
/// untouched; only read authority is published, and only for a cell every
/// possible arm owns.
fn with_guard_prefix_arm_views(
    state: &ExecutionState,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    facts: &(impl ExecutionFactSource + ?Sized),
    obligations: &[ProofObligation],
) -> ExecutionState {
    let prefix_assumptions = assumptions_with_path_context(assumptions, facts, obligations);
    let views = crate::kernel::publish_instance_arms(
        state.resources(),
        definitions,
        state,
        &prefix_assumptions,
    )
    .views;
    if views.is_empty() {
        return state.clone();
    }
    with_arm_views_preserving_support(state, views)
}

/// One evaluation of a whole guard at one state.
fn assume_condition_branches_at_state(
    state: &ExecutionState,
    condition: &ProgramExpression,
    assumptions: &PureFactContext,
    prefix_facts: &(impl ExecutionFactSource + ?Sized),
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ConditionAssumption>> {
    let effective_assumptions =
        assumptions_with_path_context(assumptions, prefix_facts, prefix_obligations);
    let mut contexts = Vec::new();
    for condition_path in
        evaluate_program_condition_paths(state, condition, &effective_assumptions, budget)?
    {
        if matches!(condition_path.outcome, ExpressionOutcome::Value(_))
            && condition_path_is_ruled_out(&condition_path.facts, &effective_assumptions)
        {
            continue;
        }
        let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
            prefix_facts,
            prefix_obligations,
            &condition_path.facts,
            &condition_path.obligations,
            assumptions,
        ) else {
            continue;
        };
        let value = match condition_path.outcome {
            ExpressionOutcome::Value(value) => value,
            // The guard itself did not run to a value here. Keep the path and
            // name its outcome; every caller reports it rather than choosing
            // an arm for it.
            ExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                contexts.push(ConditionAssumption {
                    branch: ConditionBranch::Undecided(StatementOutcome::UndefinedBehavior(
                        undefined_behavior,
                    )),
                    facts,
                    obligations,
                });
                continue;
            }
            ExpressionOutcome::RuntimeError(error) => {
                contexts.push(ConditionAssumption {
                    branch: ConditionBranch::Undecided(StatementOutcome::RuntimeError(error)),
                    facts,
                    obligations,
                });
                continue;
            }
        };
        for truthiness_path in program_truthiness_paths(value, facts, obligations, assumptions) {
            contexts.push(ConditionAssumption {
                branch: ConditionBranch::Decided(truthiness_path.is_true),
                facts: truthiness_path.facts,
                obligations: truthiness_path.obligations,
            });
        }
    }
    Ok(contexts)
}

/// A checked entry guard can preselect a preservation context. Otherwise
/// execution starts in the test/body phase itself, without a synthetic guard.
pub(super) fn assume_loop_entry_branches(
    state: &ExecutionState,
    condition: Option<&ProgramExpression>,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    prefix_facts: &(impl ExecutionFactSource + ?Sized),
    prefix_obligations: &[ProofObligation],
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ConditionAssumption>> {
    match condition {
        Some(condition) => assume_condition_branches(
            state,
            condition,
            definitions,
            assumptions,
            prefix_facts,
            prefix_obligations,
            budget,
        ),
        None => Ok(vec![ConditionAssumption {
            branch: ConditionBranch::Decided(true),
            facts: prefix_facts.persistent_facts(),
            obligations: prefix_obligations.to_vec(),
        }]),
    }
}

pub(super) fn assume_loop_entry_truthiness(
    state: &ExecutionState,
    condition: Option<&ProgramExpression>,
    definitions: &[CompositeResourceDefinition],
    assumptions: &PureFactContext,
    prefix_facts: &(impl ExecutionFactSource + ?Sized),
    prefix_obligations: &[ProofObligation],
    desired_truthiness: bool,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Vec<ConditionAssumption>> {
    Ok(assume_loop_entry_branches(state, condition, definitions, assumptions, prefix_facts, prefix_obligations, budget)?
        .into_iter().filter(|entry| !matches!(entry.branch, ConditionBranch::Decided(value) if value != desired_truthiness)).collect())
}

/// Names an undecided loop guard for a refusal context, without dumping the
/// guard's internal representation.
pub(super) fn undecided_loop_guard_context(outcome: &StatementOutcome) -> String {
    let reason = match outcome {
        StatementOutcome::UndefinedBehavior(undefined_behavior) => {
            format!(
                "it reaches undefined behavior ({})",
                undefined_behavior.description()
            )
        }
        StatementOutcome::RuntimeError(error) => {
            crate::kernel::api::describe_certification_runtime_error(error)
        }
        _ => "it produced no value".to_string(),
    };
    format!("the loop condition could not be evaluated on this path: {reason}")
}

pub(super) fn havoc_loop_modified_locals(
    state: &ExecutionState,
    body: &ProgramStatement,
    escaped: &BTreeSet<BindingName>,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
    mutable_ranges: Option<&[MemoryRange]>,
    kept_by_function: Option<CallKeptRanges>,
) -> ExecutionResult<ExecutionState> {
    let mut names = BTreeSet::new();
    collect_loop_modified_locals(body, &mut names);
    let may_write_memory = statement_may_write_memory(state, body);
    if may_write_memory {
        // A local whose address escapes can be written by the loop body
        // through a pointer without ever being assigned by name, so treat it
        // as loop-modified too (otherwise its stale value survives the havoc).
        names.extend(escaped.iter().cloned());
    }
    let locals = head_locals::LoopHeadLocals::new(state, names, variables, budget)?;
    let mut state = locals.prepare();
    let memory = if may_write_memory {
        // Keep only scalar stack local cells (constructed above); every other
        // concrete cell could have been
        // overwritten by the loop body through a pointer. Address-escaped
        // locals were havoced above, so their preserved cells now hold fresh
        // symbolic values rather than stale ones.
        // Cells under an active stable-view borrow are stable across the loop
        // by the borrow itself; erasing them would only lose borrow-supported
        // framing, never authority.
        state
            .memory
            .clone()
            .with_loop_memory_havoc_preserving_locals(
                variables.next_in(budget)?,
                &state.locals,
                mutable_ranges,
                state.borrow_ledger(),
                kept_by_function,
            )
    } else {
        state.memory.clone()
    };
    state.set_loop_head_memory(memory);
    Ok(state)
}

/// The memory the enclosing function owns where the loop is entered.
///
/// A loop body can only write memory the function owns, so this is a checked
/// upper bound on the bytes the head abstraction may erase, usable as the
/// validated ranges when the loop's own declared write set did not evaluate.
/// `None` means the footprint itself is unknown: some owned fact names memory
/// this level cannot enumerate -- a folded composite, an instance, or a token
/// -- and the caller must keep failing closed rather than guess a smaller set.
fn checked_owned_entry_footprint(resources: &ResourceContext) -> Option<Vec<MemoryRange>> {
    resources
        .facts()
        .iter()
        .filter(|fact| fact.is_own())
        .map(|fact| fact.memory_own_range().cloned())
        .collect()
}

/// Retain separation from the entry ledger for each checked write range.
fn loop_head_borrow_requirements(
    ledger: &super::borrows::BorrowLedger,
    ranges: Option<&[MemoryRange]>,
) -> Result<Vec<ProofObligation>, &'static str> {
    let Some(ranges) =
        ranges.filter(|ranges| ranges.iter().all(|range| !range.is_unnamed_footprint()))
    else {
        return Err(
            "loop memory havoc has no checked write set while a stable-view borrow is active",
        );
    };
    Ok(ranges
        .iter()
        .filter_map(|range| loop_borrow_separation(ledger, range, "loop head write separation"))
        .collect())
}

fn loop_borrow_separation(
    ledger: &super::borrows::BorrowLedger,
    range: &MemoryRange,
    context: &'static str,
) -> Option<ProofObligation> {
    ledger.memory_access_requirement(range).map(|requirement| {
        ProofObligation::verification_condition(requirement)
            .with_statement_entry_required(true)
            .with_context(context)
    })
}

pub(super) fn statement_may_write_memory(
    state: &ExecutionState,
    statement: &ProgramStatement,
) -> bool {
    match statement {
        ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::CreateClosure { .. }
        | ProgramStatement::BuiltinConstantP { .. }
        | ProgramStatement::Skip
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare {
            zero_fill: None,
            initializer: None,
            ..
        }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_) => false,
        // A zero-filled declaration stores into the object it declares, as
        // the element stores it stands for did.
        ProgramStatement::Declare {
            zero_fill: Some(_), ..
        }
        | ProgramStatement::Declare {
            initializer: Some(_),
            ..
        } => true,
        ProgramStatement::Assign { name, .. } => state.locals.is_global_object(name),
        ProgramStatement::CallConstruct { .. }
        | ProgramStatement::Call { .. }
        | ProgramStatement::CallResult { .. }
        | ProgramStatement::HeapAllocate { .. }
        | ProgramStatement::HeapFree { .. }
        | ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. }
        | ProgramStatement::Update { .. } => true,
        ProgramStatement::Seq(statements) => statements
            .iter()
            .any(|statement| statement_may_write_memory(state, statement)),
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        }
        | ProgramStatement::UnwindCleanup {
            body: try_body,
            cleanup: handler,
        } => {
            statement_may_write_memory(state, try_body)
                || statement_may_write_memory(state, handler)
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            statement_may_write_memory(state, then_branch)
                || statement_may_write_memory(state, else_branch)
        }

        ProgramStatement::Loop {
            test: loop_test,
            update,
            body,
            ..
        } => {
            let test = loop_test.source_region();
            statement_may_write_memory(state, body)
                || test
                    .as_ref()
                    .is_some_and(|test| statement_may_write_memory(state, &test.statement))
                || update
                    .as_ref()
                    .is_some_and(|update| statement_may_write_memory(state, update))
        }
        ProgramStatement::Switch { cases, .. } => cases
            .iter()
            .any(|case| statement_may_write_memory(state, &case.body)),
    }
}

#[cfg(test)]
mod v10_tests;

pub(super) fn collect_loop_modified_locals(
    statement: &ProgramStatement,
    names: &mut BTreeSet<BindingName>,
) {
    match statement {
        ProgramStatement::EndAutomaticLifetimes { names: retired, .. } => {
            names.extend(retired.iter().cloned())
        }
        ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::CreateClosure { .. }
        | ProgramStatement::BuiltinConstantP { .. }
        | ProgramStatement::Skip
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::Declare {
            initializer: None, ..
        }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::Assert { .. }
        | ProgramStatement::StepValue { .. }
        | ProgramStatement::LoopTest { .. }
        | ProgramStatement::Throw(_)
        | ProgramStatement::Return(_)
        | ProgramStatement::Store { .. }
        | ProgramStatement::TypedStore { .. }
        | ProgramStatement::CopyAggregate { .. }
        | ProgramStatement::InitializeScalarArray { .. } => {}
        ProgramStatement::Update { target, .. } => {
            if let ProgramExpression::Variable(name) = target {
                names.insert(name.clone());
            }
        }
        ProgramStatement::Declare {
            name,
            initializer: Some(_),
            ..
        } => {
            names.insert(name.binding().clone());
        }
        ProgramStatement::Assign { name, .. } => {
            names.insert(name.clone());
        }
        ProgramStatement::CallConstruct { target, .. } => {
            names.insert(target.clone());
        }
        ProgramStatement::Call { .. } | ProgramStatement::CallResult { .. } => {}
        ProgramStatement::HeapAllocate { target, .. } => {
            names.insert(target.clone());
        }
        ProgramStatement::HeapFree { .. } => {}
        ProgramStatement::Seq(statements) => {
            for statement in statements.iter() {
                collect_loop_modified_locals(statement, names);
            }
        }
        ProgramStatement::TryCatchInt32 {
            try_body,
            binding,
            handler,
            ..
        } => {
            collect_loop_modified_locals(try_body, names);
            names.insert(binding.clone());
            collect_loop_modified_locals(handler, names);
        }
        ProgramStatement::UnwindCleanup { body, cleanup } => {
            collect_loop_modified_locals(body, names);
            collect_loop_modified_locals(cleanup, names);
        }
        ProgramStatement::If {
            then_branch,
            else_branch,
            ..
        } => {
            collect_loop_modified_locals(then_branch, names);
            collect_loop_modified_locals(else_branch, names);
        }

        ProgramStatement::Loop {
            test: loop_test,
            update,
            body,
            ..
        } => {
            let test = loop_test.source_region();
            collect_loop_modified_locals(body, names);
            if let Some(test) = test {
                collect_loop_modified_locals(&test.statement, names);
            }
            if let Some(update) = update {
                collect_loop_modified_locals(update, names);
            }
        }
        ProgramStatement::Switch { cases, .. } => {
            for case in cases {
                collect_loop_modified_locals(&case.body, names);
            }
        }
    }
}

/// Scalar locals the loop body could write *through a pointer* without ever
/// assigning them by name. `collect_loop_modified_locals` ignores `Store`, so
/// these would otherwise be wrongly preserved across the loop havoc. A local
/// counts as escaped if a live pointer in the pre-loop state already points at
/// its block, or if the body takes its address syntactically.
/// The slots of `run` the loop's effect summaries leave in place, as `run`
/// with every other slot a hole, or `None` when only slot by slot can say.
///
/// A slot stays when some summary's mutable ranges all miss it. A range in a
/// block proven distinct from the run's misses every slot. One over the run's
/// own base and element width misses the slots below the least value the facts
/// allow its start and those from the greatest value they allow its end. Any
/// other range is asked slot by slot. A slot kept this way is proven outside
/// every range of its summary; one dropped is only forgotten.
fn run_slots_clear_of_loop_summaries(
    run: &crate::kernel::primitives::CellRun,
    summaries: &[Proposition],
    assumptions: &PureFactContext,
) -> Option<crate::kernel::primitives::CellRun> {
    use crate::kernel::primitives::IndexIntervals;
    let count = run.count();
    let mut all = IndexIntervals::default();
    all.insert_range(0, count);
    let mut kept = IndexIntervals::default();
    for summary in summaries {
        let Proposition::MemoryEffectSummary { mutable_ranges, .. } = summary else {
            continue;
        };
        let mut kept_by_summary = all.clone();
        for range in mutable_ranges {
            crate::instrumentation::record_deterministic_work(1);
            if range.base().blocks_proven_distinct(run.base()) {
                continue;
            }
            if range.base() != run.base()
                || range.element_width() != run.element_width()
                || run.value_width() > run.element_width()
            {
                return None;
            }
            // This run optimization uses signed intervals. A native summary
            // falls back to forgetting the run rather than reading its low word.
            let (start, end) = range.int32_bounds()?;
            let (start_low, _) = assumptions.signed_interval(start)?;
            let (_, end_high) = assumptions.signed_interval(end)?;
            let clamp = |value: i64| value.clamp(0, i64::from(count)) as u32;
            let mut missed = IndexIntervals::default();
            missed.insert_range(0, clamp(start_low));
            missed.insert_range(clamp(end_high), count);
            kept_by_summary = kept_by_summary.intersection(&missed);
        }
        for (low, high) in kept_by_summary.intervals() {
            kept.insert_range(low, high);
        }
    }
    let mut holes = run.holes().clone();
    for (low, high) in all.difference(&kept).intervals() {
        holes.insert_range(low, high);
    }
    Some(run.with_holes(holes))
}

pub(super) fn address_escaped_scalar_locals(
    state: &ExecutionState,
    body: &ProgramStatement,
) -> BTreeSet<BindingName> {
    let mut escaped = BTreeSet::new();
    collect_address_taken_locals(body, &mut escaped);

    let record_pointer = |value: &ProgramValue, escaped: &mut BTreeSet<BindingName>| {
        if let ProgramValue::Pointer(pointer) = value
            && let Some(name) = state.locals.name_for_slot(pointer)
        {
            escaped.insert(name.clone());
        }
    };
    for (block, _) in state.locals.pointer_objects_by_block.iter() {
        for (_, pointer) in state.locals.pointer_objects_in_block(block) {
            if let Some(name) = state.locals.name_for_slot(pointer.address()) {
                escaped.insert(name.clone());
            }
        }
    }
    // A private scalar slot is only read through its local binding, whose
    // pointer value was checked above. Memory can supply another pointer
    // only from storage C can address.
    for value in state.memory.cells.caught_up_pointer_reachable().values() {
        record_pointer(value.native(), &mut escaped);
    }
    // A run's slots hold values of its element type, so only a run of
    // pointers holds a pointer to visit.
    for run in state.memory.cells.runs() {
        crate::instrumentation::record_deterministic_work(1);
        if run.element_type().is_pointer() {
            for index in run.live_indexes() {
                record_pointer(&run.value(index), &mut escaped);
            }
        }
    }
    for value in state.memory.union_cells.values() {
        record_pointer(value.native(), &mut escaped);
    }
    escaped
}

/// The automatic objects, records and arrays, a loop body may write through
/// a pointer, each as its whole byte range: those the body names, since a
/// bare object name is its address, and the `escaped` ones, whose address a
/// local or a memory cell holds where the loop is entered. Constant objects
/// are never written.
fn loop_written_automatic_objects(
    state: &ExecutionState,
    body: &ProgramStatement,
    escaped: &BTreeSet<BindingName>,
) -> Vec<MemoryRange> {
    let mut names = escaped.clone();
    for_each_statement_expression(body, &mut |expression| {
        collect_variable_names(expression, &mut names);
    });
    names
        .iter()
        .filter_map(|name| {
            crate::instrumentation::record_deterministic_work(1);
            let (slot, bytes) = match state.locals.binding(name)? {
                LocalBinding::AggregateObject {
                    layout,
                    slot,
                    constant: false,
                    ..
                } => (slot, layout.size_bytes()),
                LocalBinding::ArrayObject {
                    element_type,
                    length,
                    slot,
                    constant: false,
                } => (slot, length.saturating_mul(element_type.byte_width())),
                _ => return None,
            };
            Some(MemoryRange::new_with_element_width(
                slot.clone(),
                OldMachineTerm::constant(0),
                OldMachineTerm::constant(bytes),
                1,
            ))
        })
        .collect()
}

/// Calls `visit` on each expression `statement` and its nested statements
/// evaluate.
fn for_each_statement_expression<'a>(
    statement: &'a ProgramStatement,
    visit: &mut impl FnMut(&'a ProgramExpression),
) {
    match statement {
        ProgramStatement::EndAutomaticLifetimes { .. }
        | ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::BuiltinConstantP { .. }
        | ProgramStatement::Skip
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::DeclareAggregate { .. }
        | ProgramStatement::HeapAllocate { .. } => {}
        ProgramStatement::Declare {
            initializer,
            zero_fill,
            ..
        } => {
            for expression in initializer
                .iter()
                .chain(zero_fill.iter().flat_map(ZeroFill::expressions))
            {
                visit(expression);
            }
        }
        ProgramStatement::Assign { expression, .. }
        | ProgramStatement::HeapFree {
            pointer: expression,
        }
        | ProgramStatement::Assert {
            condition: expression,
            ..
        }
        | ProgramStatement::LoopTest {
            condition: expression,
            ..
        }
        | ProgramStatement::StepValue { expression, .. }
        | ProgramStatement::Return(expression)
        | ProgramStatement::Throw(expression) => visit(expression),
        ProgramStatement::CreateClosure {
            captures: arguments,
            ..
        }
        | ProgramStatement::CallConstruct { arguments, .. } => {
            arguments.iter().for_each(&mut *visit)
        }
        ProgramStatement::Call {
            arguments, callee, ..
        }
        | ProgramStatement::CallResult {
            arguments, callee, ..
        } => {
            if let Some(callee) = callee {
                visit(&callee.pointer);
            }
            arguments.iter().for_each(&mut *visit);
        }
        ProgramStatement::Store { pointer, value }
        | ProgramStatement::TypedStore { pointer, value, .. } => {
            visit(pointer);
            visit(value);
        }
        ProgramStatement::CopyAggregate { target, source, .. }
        | ProgramStatement::InitializeScalarArray { target, source, .. } => {
            visit(target);
            visit(source);
        }
        ProgramStatement::Update {
            target, operand, ..
        } => {
            visit(target);
            visit(operand);
        }
        ProgramStatement::Seq(statements) => {
            for statement in statements.iter() {
                for_each_statement_expression(statement, visit);
            }
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        }
        | ProgramStatement::UnwindCleanup {
            body: try_body,
            cleanup: handler,
        } => {
            for_each_statement_expression(try_body, visit);
            for_each_statement_expression(handler, visit);
        }
        ProgramStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            visit(condition);
            for_each_statement_expression(then_branch, visit);
            for_each_statement_expression(else_branch, visit);
        }

        ProgramStatement::Loop {
            test: loop_test,
            update,
            body,
            ..
        } => {
            let condition = loop_test.source_condition();
            let test = loop_test.source_region();
            if let Some(condition) = condition {
                visit(condition);
            }
            for_each_statement_expression(body, visit);
            if let Some(test) = test {
                for_each_statement_expression(&test.statement, visit);
            }
            if let Some(update) = update {
                for_each_statement_expression(update, visit);
            }
        }
        ProgramStatement::Switch { expression, cases } => {
            visit(expression);
            for case in cases {
                for_each_statement_expression(&case.body, visit);
            }
        }
    }
}

pub(crate) fn collect_address_taken_locals(
    statement: &ProgramStatement,
    names: &mut BTreeSet<BindingName>,
) {
    match statement {
        ProgramStatement::EndAutomaticLifetimes { .. } => {}
        ProgramStatement::ThrowOpaque(_)
        | ProgramStatement::BuiltinConstantP { .. }
        | ProgramStatement::Skip
        | ProgramStatement::Break
        | ProgramStatement::Continue
        | ProgramStatement::Goto { .. }
        | ProgramStatement::DeclareAggregate { .. } => {}
        ProgramStatement::Declare {
            initializer,
            zero_fill,
            ..
        } => {
            for expression in initializer
                .iter()
                .chain(zero_fill.iter().flat_map(ZeroFill::expressions))
            {
                collect_address_taken_in_expression(expression, names);
            }
        }
        ProgramStatement::Assign { expression, .. } => {
            collect_address_taken_in_expression(expression, names)
        }
        ProgramStatement::CreateClosure {
            captures: arguments,
            ..
        }
        | ProgramStatement::CallConstruct { arguments, .. } => {
            for argument in arguments {
                collect_address_taken_in_expression(argument, names);
            }
        }
        ProgramStatement::Call { arguments, .. }
        | ProgramStatement::CallResult { arguments, .. } => {
            for argument in arguments {
                collect_address_taken_in_expression(argument, names);
            }
        }
        ProgramStatement::HeapAllocate { .. } => {}
        ProgramStatement::HeapFree { pointer } => {
            collect_address_taken_in_expression(pointer, names);
        }
        ProgramStatement::Assert { condition, .. }
        | ProgramStatement::LoopTest { condition, .. }
        | ProgramStatement::StepValue {
            expression: condition,
            ..
        } => collect_address_taken_in_expression(condition, names),
        ProgramStatement::Return(expression) | ProgramStatement::Throw(expression) => {
            collect_address_taken_in_expression(expression, names)
        }
        ProgramStatement::Store { pointer, value } => {
            collect_address_taken_in_expression(pointer, names);
            collect_address_taken_in_expression(value, names);
        }
        ProgramStatement::TypedStore { pointer, value, .. } => {
            collect_address_taken_in_expression(pointer, names);
            collect_address_taken_in_expression(value, names);
        }
        ProgramStatement::CopyAggregate { target, source, .. }
        | ProgramStatement::InitializeScalarArray { target, source, .. } => {
            collect_address_taken_in_expression(target, names);
            collect_address_taken_in_expression(source, names);
        }
        ProgramStatement::Update {
            target, operand, ..
        } => {
            collect_address_taken_in_expression(target, names);
            collect_address_taken_in_expression(operand, names);
        }
        ProgramStatement::Seq(statements) => {
            for statement in statements.iter() {
                collect_address_taken_locals(statement, names);
            }
        }
        ProgramStatement::TryCatchInt32 {
            try_body, handler, ..
        }
        | ProgramStatement::UnwindCleanup {
            body: try_body,
            cleanup: handler,
        } => {
            collect_address_taken_locals(try_body, names);
            collect_address_taken_locals(handler, names);
        }
        ProgramStatement::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_address_taken_in_expression(condition, names);
            collect_address_taken_locals(then_branch, names);
            collect_address_taken_locals(else_branch, names);
        }

        ProgramStatement::Loop {
            test: loop_test,
            update,
            body,
            ..
        } => {
            let condition = loop_test.source_condition();
            let test = loop_test.source_region();
            if let Some(condition) = condition {
                collect_address_taken_in_expression(condition, names);
            }
            collect_address_taken_locals(body, names);
            if let Some(test) = test {
                collect_address_taken_locals(&test.statement, names);
            }
            if let Some(update) = update {
                collect_address_taken_locals(update, names);
            }
        }
        ProgramStatement::Switch { expression, cases } => {
            collect_address_taken_in_expression(expression, names);
            for case in cases {
                collect_address_taken_locals(&case.body, names);
            }
        }
    }
}

pub(super) fn collect_address_taken_in_expression(
    expression: &ProgramExpression,
    names: &mut BTreeSet<BindingName>,
) {
    match expression {
        // `&target`: any local reachable in the target may have its address
        // escape, so conservatively record every variable it mentions.
        ProgramExpression::AddressOf(target) | ProgramExpression::CheckedObjectAddress(target) => {
            collect_variable_names(target, names)
        }
        ProgramExpression::StringLiteral(_)
        | ProgramExpression::Value(_)
        | ProgramExpression::Variable(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => {}
        ProgramExpression::Cast { expression, .. } => {
            collect_address_taken_in_expression(expression, names)
        }
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_address_taken_in_expression(condition, names);
            collect_address_taken_in_expression(then_branch, names);
            collect_address_taken_in_expression(else_branch, names);
        }
        ProgramExpression::Negate(expression)
        | ProgramExpression::FloatNegate(expression)
        | ProgramExpression::FloatClassification { expression, .. }
        | ProgramExpression::EnumField {
            value: expression, ..
        }
        | ProgramExpression::EnumIs {
            value: expression, ..
        }
        | ProgramExpression::SliceLength(expression)
        | ProgramExpression::SliceData(expression) => {
            collect_address_taken_in_expression(expression, names)
        }
        ProgramExpression::EnumConstruct { fields, .. } => {
            for field in fields {
                collect_address_taken_in_expression(field, names);
            }
        }
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => {
            collect_address_taken_in_expression(pointer, names)
        }
        ProgramExpression::Not(inner) | ProgramExpression::Load(inner) => {
            collect_address_taken_in_expression(inner, names)
        }
        ProgramExpression::TypedLoad { pointer, .. } => {
            collect_address_taken_in_expression(pointer, names)
        }
        crate::kernel::binary_c_expression!(left, right)
        | ProgramExpression::SliceFromRawParts {
            data: left,
            count: right,
        } => {
            collect_address_taken_in_expression(left, names);
            collect_address_taken_in_expression(right, names);
        }
        ProgramExpression::BitwiseNot(expression) => {
            collect_address_taken_in_expression(expression, names);
        }
    }
}

pub(super) fn collect_variable_names(
    expression: &ProgramExpression,
    names: &mut BTreeSet<BindingName>,
) {
    match expression {
        ProgramExpression::Variable(name) => {
            names.insert(name.clone());
        }
        ProgramExpression::StringLiteral(_)
        | ProgramExpression::Value(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => {}
        ProgramExpression::Cast { expression, .. } => collect_variable_names(expression, names),
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_variable_names(condition, names);
            collect_variable_names(then_branch, names);
            collect_variable_names(else_branch, names);
        }
        ProgramExpression::Negate(expression)
        | ProgramExpression::FloatNegate(expression)
        | ProgramExpression::FloatClassification { expression, .. }
        | ProgramExpression::EnumField {
            value: expression, ..
        }
        | ProgramExpression::EnumIs {
            value: expression, ..
        }
        | ProgramExpression::SliceLength(expression)
        | ProgramExpression::SliceData(expression) => collect_variable_names(expression, names),
        ProgramExpression::EnumConstruct { fields, .. } => {
            for field in fields {
                collect_variable_names(field, names);
            }
        }
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => collect_variable_names(pointer, names),
        ProgramExpression::AddressOf(inner)
        | ProgramExpression::CheckedObjectAddress(inner)
        | ProgramExpression::Not(inner)
        | ProgramExpression::Load(inner) => collect_variable_names(inner, names),
        ProgramExpression::TypedLoad { pointer, .. } => collect_variable_names(pointer, names),
        crate::kernel::binary_c_expression!(left, right)
        | ProgramExpression::SliceFromRawParts {
            data: left,
            count: right,
        } => {
            collect_variable_names(left, names);
            collect_variable_names(right, names);
        }
        ProgramExpression::BitwiseNot(expression) => {
            collect_variable_names(expression, names);
        }
    }
}

#[cfg(test)]
mod wide_range_reader_tests;

#[cfg(test)]
mod resource_argument_diagnostic_tests;

fn program_value_subobject_bounds(value: &StoredExecutionValue) -> Option<&SubobjectBounds> {
    value.pointer()?.bounds()
}

fn program_value_object_class(
    value: &StoredExecutionValue,
) -> Option<crate::kernel::effective_type::CAccessClass> {
    value.pointer()?.object_class()
}

fn with_retained_object_class(
    fresh: ProgramValue,
    previous: Option<&StoredExecutionValue>,
) -> ProgramValue {
    fresh.with_pointer_declared_object_class(previous.and_then(program_value_object_class))
}

/// Legacy fresh-pointer construction is the output boundary for this loop abstraction.
fn with_retained_bounds(
    fresh: ProgramValue,
    previous: Option<&StoredExecutionValue>,
) -> ProgramValue {
    let Some(previous) = previous.filter(|value| value.pointer().is_some()) else {
        return fresh;
    };
    let previous = previous.native();
    match (fresh, previous.as_ref()) {
        (ProgramValue::Pointer(pointer), ProgramValue::Pointer(previous))
            if previous.bounds().is_some() =>
        {
            ProgramValue::Pointer(
                pointer
                    .with_bounds(previous.bounds().cloned())
                    .with_provenance(previous.provenance().clone())
                    .with_bounds_owner(previous.bounds_owner().cloned()),
            )
        }
        (fresh, _) => fresh,
    }
}

/// A memory clause names its range through a pointer, and so claims that the
/// pointer designates that range (`design/pointer-subobject-bounds.md`, D1).
/// Through a pointer narrowed to a member, the range must lie inside the
/// member: passing `&pair.first` where a callee views `p[0..2]` would
/// otherwise let the callee read `pair.second` through it. An empty range
/// claims nothing. A pointer without bounds is bounded by its complete
/// object, as before.
fn segment_bounds_refusal(
    base: &Pointer,
    segment: &EvaluatedMemorySegment,
    assumptions: &PureFactContext,
) -> Option<String> {
    range_bounds_refusal(
        base,
        &segment.start,
        &segment.end,
        segment.element_width,
        segment.kind,
        assumptions,
    )
}

/// [`segment_bounds_refusal`] for a lowered range: a proof step's clause
/// names its range through the same pointer value.
pub(crate) fn memory_range_bounds_refusal(
    base: &Pointer,
    range: &MemoryRange,
    assumptions: &PureFactContext,
) -> Option<String> {
    let (start, end) = match range.wide_bounds() {
        Some(bounds) => bounds,
        None => (range.start(), range.end()),
    };
    range_bounds_refusal(
        base,
        start,
        end,
        range.element_width(),
        range.kind(),
        assumptions,
    )
}

fn range_bounds_refusal(
    base: &Pointer,
    start: &OldMachineTerm,
    end: &OldMachineTerm,
    element_width: u32,
    kind: RangeIndexKind,
    assumptions: &PureFactContext,
) -> Option<String> {
    let crate::kernel::assumptions::PointerDomain::Selected(bounds) =
        assumptions.pointer_domain(base)
    else {
        return None;
    };
    let refusal = || {
        Some(match bounds.constant_width() {
            Some(width) => format!(
                "the clause's range of {element_width}-byte elements reaches outside the {width}-byte subobject its pointer designates"
            ),
            None => format!(
                "the clause's range of {element_width}-byte elements reaches outside the subobject its pointer designates"
            ),
        })
    };
    // The domain witness can use another equal pointer's coordinates.
    // Resolve only the checked address; the clause's base value stays intact.
    let respelled = assumptions
        .pointer_at_known_base(base.address(), bounds.start())
        .filter(|respelled| {
            respelled != base.address()
                && assumptions.pointers_known_equal(base.address(), respelled)
        });
    let Some(offset) = respelled
        .as_ref()
        .and_then(|respelled| {
            crate::kernel::reasoning::shared_pointer_byte_offset_from_base(
                respelled,
                bounds.start(),
            )
        })
        .or_else(|| {
            crate::kernel::reasoning::shared_pointer_byte_offset_from_base(
                base.address(),
                bounds.start(),
            )
        })
    else {
        return refusal();
    };
    let Some(width) = bounds.constant_width().map(i64::from) else {
        return refusal();
    };
    let element_width = i64::from(element_width);
    let proves = |condition: OldConditionTerm| assumptions.decide(&condition) == Some(true);
    let offset = offset.checking_cast_operand(MachineIntegerType::Int64);
    let compare = |left: MachineOperandView<'_>, right: MachineOperandView<'_>| {
        crate::kernel::machine_integer::comparison::condition_for_operand_views(
            MachineIntegerType::Int64,
            CompareRelation::LessEqual,
            [left, right],
        )
    };
    match kind {
        RangeIndexKind::Int32 => {
            let start = OldMachineTerm::int64_from_32(start.clone());
            let end = OldMachineTerm::int64_from_32(end.clone());
            if proves(OldConditionTerm::int64_signed_less_equal(
                end.clone(),
                start.clone(),
            )) {
                return None;
            }
            let byte = |index: OldMachineTerm| {
                let product = OldMachineTerm::int64_multiply(
                    index,
                    OldMachineTerm::int64_constant(element_width),
                );
                let root = crate::kernel::proof::term_rewrite::TermRewrite::machine_binary_reading(
                    MachineIntegerType::Int64,
                    MachineBinaryOp::Add,
                    crate::kernel::KernelTerm::retained_machine_operand(
                        MachineIntegerType::Int64,
                        offset.operand_view(),
                    ),
                    crate::kernel::KernelTerm::retained_machine_operand(
                        MachineIntegerType::Int64,
                        MachineOperandView::Old(&product),
                    ),
                );
                MachineOperandView::Shared(&root).retain(MachineIntegerType::Int64)
            };
            let inside = proves(compare(
                MachineOperandView::Old(&OldMachineTerm::int64_constant(0)),
                byte(start).operand_view(),
            )) && proves(compare(
                byte(end).operand_view(),
                MachineOperandView::Old(&OldMachineTerm::int64_constant(width)),
            ));
            (!inside).then(refusal).flatten()
        }
        // An unsigned 64-bit range is inside when its constant offset leaves
        // room for its end; its start is never below zero.
        RangeIndexKind::UInt64 => {
            let offset = offset.operand_view().int64_constant()?.max(0);
            let room = u64::try_from((width - offset) / element_width.max(1)).ok()?;
            let inside = proves(OldConditionTerm::uint64_less_equal(
                end.clone(),
                OldMachineTerm::uint64_constant(room),
            ));
            (!inside).then(refusal).flatten()
        }
    }
}

#[cfg(test)]
mod frame_resource_tests {
    use super::*;
    mod scaling_tests {
        include!("../scaling_tests/kernel/loops/frame_resource_tests.rs");
    }
}

#[cfg(test)]
mod shared_update_tests;

#[cfg(test)]
mod pointer_domain_clause_tests {
    use super::*;

    #[test]
    fn clause_ranges_check_admitted_member_bounds_without_rewriting_the_base() {
        let _session = crate::kernel::VerificationSession::enter();
        let base = Pointer::new(
            Address::symbolic(Variable(1013200)),
            ProgramType::Int32Pointer,
        );
        let selected = base.clone().with_bounds(Some(SubobjectBounds::new(
            base.address().clone(),
            4u32.into(),
        )));
        let context = PureFactContext::new().assume_condition(
            OldConditionTerm::pointer_equal(base.clone(), selected),
            true,
        );
        for (end, refused) in [(0, false), (1, false), (2, true)] {
            for wide in [false, true] {
                let (start, end, kind) = if wide {
                    (
                        OldMachineTerm::uint64_constant(0),
                        OldMachineTerm::uint64_constant(end),
                        RangeIndexKind::UInt64,
                    )
                } else {
                    (
                        0u32.into(),
                        OldMachineTerm::constant(end as u32),
                        RangeIndexKind::Int32,
                    )
                };
                assert_eq!(
                    range_bounds_refusal(&base, &start, &end, 4, kind, &context).is_some(),
                    refused
                );
            }
        }
        assert_eq!(base.bounds(), None);
    }
}
