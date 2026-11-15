//! A call's arguments and result: evaluating and binding arguments, coercing argument and return values to the declared types, and symbolic results for calls whose body is not executed.

use super::*;

pub(super) fn with_contract_argument_views(
    state: &ExecutionState,
    function: &ProgramFunction,
    values: &[ProgramValue],
) -> ExecutionState {
    with_contract_interface_argument_views(state, function.contract_interface(), values)
}

pub(super) fn with_contract_interface_argument_views(
    state: &ExecutionState,
    interface: &FunctionContractInterface,
    values: &[ProgramValue],
) -> ExecutionState {
    let mut state = state.clone();
    state.resources = state.resources.unpublished_contract_view();
    for (parameter, value) in interface.parameters().iter().zip(values) {
        if parameter.aggregate_layout().is_some() {
            // Aggregate parameters are already represented by the copied
            // address-backed object installed by argument binding. Keeping
            // that binding lets contract field accesses inspect the copy
            // rather than accidentally replacing it with the caller's source
            // pointer.
            continue;
        }
        // Keep the contract view identical to the typed parameter binding.
        // In particular, a C null-pointer constant arrives here as the
        // caller's int32 `0`, but the callee parameter is a pointer.  Using
        // the raw caller value would overwrite the correctly coerced binding
        // and make pointer preconditions impossible to lower.
        let value = coerce_contract_argument_without_obligations(value, parameter)
            .expect("function arguments were type-checked before building contract views");
        let value = value
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant())
            .with_pointer_declared_object_class(parameter.pointee_class());
        state.locals.set_typed_with_all_qualifiers(
            parameter.name().to_string(),
            value.clone(),
            parameter.program_type(),
            parameter.is_volatile(),
            parameter.pointee_is_volatile(),
            parameter.is_constant(),
            parameter.pointee_is_constant(),
        );
        if let ProgramValue::Pointer(pointer) = &value {
            let Some(element_width) = parameter
                .program_type()
                .pointee_type()
                .map(ProgramType::byte_width)
            else {
                // An opaque object pointer carries identity and qualifiers,
                // but no element width. Do not manufacture a contract view
                // that would make an untyped dereference look loadable.
                continue;
            };
            state.resources = state
                .resources
                .unchecked_with_fact(ResourceFact::view_memory(
                    MemoryRange::new_with_element_width(
                        pointer.pointer().clone(),
                        MachineTerm::constant(0),
                        MachineTerm::constant(i32::MAX as u32),
                        element_width,
                    ),
                ));
        }
    }
    state
}

pub(super) fn set_function_result(
    state: &mut ExecutionState,
    function: &ProgramFunction,
    value: impl Into<StoredExecutionValue>,
) {
    set_contract_result(state, function.contract_interface(), value);
}

pub(super) fn set_contract_result(
    state: &mut ExecutionState,
    interface: &FunctionContractInterface,
    value: impl Into<StoredExecutionValue>,
) {
    let value = value.into();
    if value.shared().is_some_and(|root| {
        root.is_shared_machine_operand()
            || root.ty() == &KernelType::Bool
            || matches!(root.ty(), KernelType::Algebraic(_))
    }) {
        state.locals.set_retained_typed_with_all_qualifiers(
            C_CONTRACT_RESULT_NAME,
            value,
            interface.return_type(),
            false,
            false,
            false,
            interface.return_pointee_is_constant(),
        );
        return;
    }
    let source = value;
    let value = source.native().into_owned();
    if let Some(layout) = interface.return_aggregate_layout()
        && let ProgramValue::Pointer(pointer) = &value
    {
        if interface.aggregate_return_mode() == AggregateReturnMode::Copy {
            state.set_memory(
                // A returned-by-value temporary is fresh caller storage. Its
                // declaration must remain in the memory history so copying
                // its fields does not disconnect unrelated input states.
                // A symbolic pointer still supplies only a synthetic layout.
                if matches!(pointer.block, PointerBlock::Symbolic(_)) {
                    state
                        .memory
                        .clone()
                        .with_block_without_derivation(pointer.block.clone(), layout.size_bytes())
                } else {
                    state
                        .memory
                        .clone()
                        .with_block(pointer.block.clone(), layout.size_bytes())
                },
            );
        }
        state.locals.set_aggregate_object_at(
            C_CONTRACT_RESULT_NAME.to_string(),
            layout.clone(),
            pointer.pointer().clone(),
        );
        return;
    }
    let value = value
        .with_pointer_pointee_constant(interface.return_pointee_is_constant())
        .with_pointer_declared_object_class(interface.return_pointee_class());
    state.locals.set_retained_typed_with_all_qualifiers(
        C_CONTRACT_RESULT_NAME.to_string(),
        source.retain_checked_pointer(value),
        interface.return_type(),
        false,
        false,
        false,
        interface.return_pointee_is_constant(),
    );
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(super) enum AggregateReturnRefusal {
    InvalidValue,
    UninitializedRead,
}

// Keep initialization and result identity in one checked transition: copy mode
// materializes a value, while construction mode completes the selected object.
// Every body-completion path must use this boundary before retiring the source.
pub(super) fn complete_aggregate_return(
    state: &mut ExecutionState,
    function: &ProgramFunction,
    value: ProgramValue,
) -> Result<ProgramValue, AggregateReturnRefusal> {
    if function.contract_interface().aggregate_return_mode() == AggregateReturnMode::Construction {
        return construction_return::complete(state, function.contract_interface(), value);
    }
    let layout = function
        .return_aggregate_layout()
        .ok_or(AggregateReturnRefusal::InvalidValue)?;
    let ProgramValue::Pointer(pointer) = value else {
        return Err(AggregateReturnRefusal::InvalidValue);
    };
    if pointer.is_null() {
        return Err(AggregateReturnRefusal::InvalidValue);
    }
    let source = pointer.pointer().clone();
    if aggregate_copy_reads_uninitialized(&state.memory, &source, layout) {
        return Err(AggregateReturnRefusal::UninitializedRead);
    }
    let frame = state.next_local_frame;
    let destination = Memory::frame_local_pointer(frame, "__return");
    state.set_memory(
        state
            .memory
            .clone()
            .with_block(destination.block.clone(), layout.size_bytes()),
    );
    state.set_memory(copy_aggregate_fields(
        state.memory.clone(),
        &source,
        &destination,
        layout,
    ));
    state.next_local_frame = frame.saturating_add(1);
    Ok(ProgramValue::typed_pointer(
        destination,
        function.return_type(),
    ))
}

/// The undefined behavior of the implicit conversion a `return` performs when
/// it converts a pointer into a freed allocation to a non-pointer return type
/// such as `_Bool`; see [`freed_pointer_use`]. Returning the pointer from a
/// pointer-returning function only moves it and is not refused. `state` is the
/// state at the `return`.
pub(super) fn freed_pointer_return_conversion(
    state: &ExecutionState,
    function: &ProgramFunction,
    value: &StoredExecutionValue,
    assumptions: &PureFactContext,
) -> Option<UndefinedBehavior> {
    let value = value.native_payload()?;
    let return_type = function.return_type();
    if return_type == ProgramType::Void
        || return_type.is_pointer()
        || function.return_aggregate_layout().is_some()
        || state.memory().heap_has_no_deallocations()
    {
        return None;
    }
    freed_pointer_use(state, value, assumptions)
}

/// The undefined behavior of the implicit conversion a call performs when it
/// passes a pointer into a freed allocation to a non-pointer parameter such as
/// `_Bool`; see [`freed_pointer_use`]. Passing the pointer to a pointer
/// parameter only moves it and is not refused. `state` is the caller state the
/// arguments were evaluated in.
pub(super) fn freed_pointer_argument_conversion(
    state: &ExecutionState,
    interface: &FunctionContractInterface,
    values: &[ProgramValue],
    assumptions: &PureFactContext,
) -> Option<UndefinedBehavior> {
    if state.memory().heap_has_no_deallocations() {
        return None;
    }
    interface
        .parameters()
        .iter()
        .zip(values)
        .filter(|(parameter, _)| {
            parameter.aggregate_layout().is_none() && !parameter.program_type().is_pointer()
        })
        .find_map(|(_, value)| freed_pointer_use(state, value, assumptions))
}

/// The refusal of a call that passes a pointer to an object whose known
/// type the parameter's pointee type cannot designate
/// (`design/effective-types.md`). The callee is verified accessing the
/// object through that type, so the caller must not hand it another.
pub(super) fn incompatible_pointer_argument(
    state: &ExecutionState,
    function_name: &str,
    interface: &FunctionContractInterface,
    values: &[ProgramValue],
    assumptions: &PureFactContext,
) -> Option<RuntimeError> {
    interface
        .parameters()
        .iter()
        .zip(values)
        .find_map(|(parameter, value)| {
            let pointee = parameter.pointee_class()?;
            let ProgramValue::Pointer(pointer) = value else {
                return None;
            };
            let object = state
                .memory()
                .declared_class(pointer.pointer())
                .or_else(|| pointer.object_class())?;
            if pointee.may_designate(&object) || pointer.is_null() {
                return None;
            }
            if assumptions.decide(&ConditionTerm::pointer_equal(
                pointer.pointer().clone(),
                Pointer::null(),
            )) == Some(true)
            {
                return None;
            }
            Some({
                RuntimeError::FunctionContract(format!(
                    "call to `{function_name}` passes an object of type `{}` to parameter \
                     `{}`, which points to `{}`: the callee accesses it through that type, \
                     and an object may be accessed only through its own type, up to \
                     signedness and qualifiers, or a character type (C11 6.5p7)",
                    object.spelling(),
                    parameter.name(),
                    pointee.spelling(),
                ))
            })
        })
}

/// The refusal of a return whose pointer designates an object of a known
/// type that the declared return type's pointee cannot designate; callers
/// access the object through that type (`design/effective-types.md`).
pub(super) fn incompatible_pointer_return(
    state: &ExecutionState,
    function: &ProgramFunction,
    value: &StoredExecutionValue,
    assumptions: &PureFactContext,
) -> Option<RuntimeError> {
    let value = value.native_payload()?;
    let pointee = function.contract_interface().return_pointee_class()?;
    let ProgramValue::Pointer(pointer) = value else {
        return None;
    };
    let object = state
        .memory()
        .declared_class(pointer.pointer())
        .or_else(|| pointer.object_class())?;
    if pointee.may_designate(&object) || pointer.is_null() {
        return None;
    }
    if assumptions.decide(&ConditionTerm::pointer_equal(
        pointer.pointer().clone(),
        Pointer::null(),
    )) == Some(true)
    {
        return None;
    }
    Some({
        RuntimeError::FunctionContract(format!(
            "`{}` returns a pointer to an object of type `{}` as a pointer to `{}`: its \
             callers access the object through that type, and an object may be accessed \
             only through its own type, up to signedness and qualifiers, or a character \
             type (C11 6.5p7)",
            function.name(),
            object.spelling(),
            pointee.spelling(),
        ))
    })
}

pub(in crate::kernel) fn coerce_retained_function_return_value(
    value: StoredExecutionValue,
    function: &ProgramFunction,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<StoredExecutionValue> {
    if value.shared().is_some()
        && matches!(
            value.program_type(),
            ProgramType::Bool
                | ProgramType::Parameter(_)
                | ProgramType::Int8
                | ProgramType::UInt8
                | ProgramType::Int16
                | ProgramType::UInt16
                | ProgramType::Int32
                | ProgramType::UInt32
                | ProgramType::Int64
                | ProgramType::UInt64
        )
        && value.program_type() == function.return_type()
    {
        return Some(value);
    }
    let converted = coerce_function_return_value(
        value.native().into_owned(),
        function,
        obligations,
        assumptions,
    )?;
    // Aggregate ABI conversion deliberately forms its own complete payload.
    if function.return_aggregate_layout().is_some() {
        Some(converted.into())
    } else {
        Some(value.retain_checked_pointer(converted).into())
    }
}

pub(super) fn coerce_function_return_value(
    value: ProgramValue,
    function: &ProgramFunction,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<ProgramValue> {
    // Plain struct returns use `uint8*` as their internal ABI slot, while the
    // source expression that supplies the value retains the pointee type of
    // the object it addresses (for example, `int32*` for `return *source`).
    // The aggregate return materializer copies through the pointer and is the
    // type boundary that validates the complete object. The C struct model
    // uses `int32*` for a struct pointer and `uint8*` for an address-backed
    // struct value, so only those two data-pointer views cross this boundary.
    if function.return_aggregate_layout().is_some()
        && let ProgramValue::Pointer(pointer) = &value
        && matches!(
            pointer.program_type(),
            ProgramType::Int32Pointer | ProgramType::UInt8Pointer
        )
        && !pointer.pointer().block.is_function()
    {
        return Some(ProgramValue::typed_pointer(
            pointer.pointer().clone(),
            function.return_type(),
        ));
    }
    coerce_program_value_with_pointee_constant(
        value,
        function.return_type(),
        function.return_pointee_is_constant(),
        obligations,
        assumptions,
    )
}

pub(in crate::kernel) fn coerce_program_value_with_pointee_constant(
    value: ProgramValue,
    program_type: ProgramType,
    pointee_constant: bool,
    obligations: &mut Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<ProgramValue> {
    // This is an implicit conversion boundary. Explicit C casts have their
    // own rules; storage read-only status is independently checked on writes.
    if matches!(&value, ProgramValue::Pointer(pointer) if pointer.pointee_constant())
        && program_type.is_pointer()
        && !pointee_constant
    {
        return None;
    }
    Some(
        coerce_program_value_to_type(value, program_type, obligations, assumptions)?
            .with_pointer_pointee_constant(pointee_constant),
    )
}

#[cfg(test)]
pub(super) fn symbolic_function_result(
    function: &ProgramFunction,
    variable: Variable,
) -> ProgramValue {
    symbolic_contract_result(function.contract_interface(), variable)
}

pub(super) fn symbolic_contract_result(
    interface: &FunctionContractInterface,
    variable: Variable,
) -> ProgramValue {
    // An aggregate returned by value is not a pointer the callee handed over:
    // it is a fresh object the C abstract machine creates for the caller to
    // copy out of, and the program has no name and no prior pointer for it.
    // Giving it a `Temporary` identity rather than a symbolic one is what lets
    // `PointerBlock::proven_distinct` separate it from every other block, so a
    // read of one of its fields is framed across an unrelated store by
    // structure alone. A symbolic block would be separated from nothing, and a
    // load through it would then need aliasing evidence that no honest contract
    // about a returned struct can state.
    if interface.return_aggregate_layout().is_some() {
        return ProgramValue::typed_pointer(
            Pointer::verifier_temporary(variable),
            interface.return_type(),
        )
        .with_pointer_pointee_constant(interface.return_pointee_is_constant());
    }
    symbolic_call_result(interface.return_type(), variable)
        .complete_word(Pointer::symbolic(variable))
        .with_pointer_pointee_constant(interface.return_pointee_is_constant())
        .with_pointer_declared_object_class(interface.return_pointee_class())
}

pub(crate) fn symbolic_call_result(program_type: ProgramType, variable: Variable) -> ProgramValue {
    match program_type {
        ProgramType::Parameter(name) => ProgramValue::Parameter(Box::new(AlgebraicTerm {
            algebraic_type: name.algebraic_type(),
            node: AlgebraicTermNode::Variable(variable),
        })),
        ProgramType::Void => ProgramValue::Void,
        // A `bool` is a binder of the kernel sort `Bool` (Stage 5), carried
        // as its cast (rule C1), so the binder is the parameter's own name.
        ProgramType::Bool => {
            ProgramValue::of_bool(crate::kernel::ConditionTerm::Variable(variable))
        }
        ProgramType::VoidPointer | ProgramType::VoidPointerPointer => {
            ProgramValue::typed_pointer(Pointer::symbolic(variable), program_type)
        }
        ProgramType::Int8 => ProgramValue::Int8(MachineTerm::Variable(variable)),
        ProgramType::Int16 => ProgramValue::Int16(MachineTerm::Variable(variable)),
        ProgramType::Int32 => ProgramValue::Int32(MachineTerm::Variable(variable)),
        ProgramType::UInt8 => ProgramValue::UInt8(MachineTerm::Variable(variable)),
        ProgramType::UInt16 => ProgramValue::UInt16(MachineTerm::Variable(variable)),
        ProgramType::UInt32 => ProgramValue::UInt32(MachineTerm::Variable(variable)),
        ProgramType::Int64 => ProgramValue::Int64(MachineTerm::Variable(variable)),
        ProgramType::UInt64 => ProgramValue::UInt64(MachineTerm::Variable(variable)),
        ProgramType::Int128 => ProgramValue::Int128(MachineTerm::Variable(variable)),
        ProgramType::UInt128 => ProgramValue::UInt128(MachineTerm::Variable(variable)),
        ProgramType::Float32 => ProgramValue::Float32(MachineTerm::Variable(variable)),
        ProgramType::Float64 => ProgramValue::Float64(MachineTerm::Variable(variable)),
        ProgramType::Int8Pointer | ProgramType::Int8PointerPointer => {
            ProgramValue::typed_pointer(Pointer::symbolic(variable), program_type)
        }
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
        | ProgramType::Float64PointerPointer => {
            ProgramValue::typed_pointer(Pointer::symbolic(variable), program_type)
        }
        ProgramType::FunctionPointer(_) => {
            ProgramValue::typed_pointer(Pointer::symbolic_function(variable), program_type)
        }
        ProgramType::Int8Array(_) => {
            unreachable!("C functions cannot return array values")
        }
        ProgramType::Int32Array(_)
        | ProgramType::UInt8Array(_)
        | ProgramType::Int16Array(_)
        | ProgramType::UInt16Array(_)
        | ProgramType::UInt32Array(_)
        | ProgramType::Int128Array(_)
        | ProgramType::Int64Array(_)
        | ProgramType::UInt128Array(_)
        | ProgramType::UInt64Array(_)
        | ProgramType::Float32Array(_)
        | ProgramType::Float64Array(_) => {
            unreachable!("C functions cannot return array values")
        }
        ProgramType::PointerArray(_, _) => {
            unreachable!("C functions cannot return array values")
        }
    }
}

pub(in crate::kernel) fn add_memory_store_obligation(
    memory: &Memory,
    pointer: &Pointer,
    value: &ProgramValue,
    mut obligations: Vec<ProofObligation>,
    assumptions: &PureFactContext,
) -> Option<Vec<ProofObligation>> {
    if memory.can_store_concretely(pointer, value) {
        return Some(obligations);
    }

    add_proof_obligation(
        &mut obligations,
        assumptions,
        Proposition::MemoryCanStore {
            memory: memory.clone(),
            pointer: pointer.clone(),
            byte_width: value.byte_width(),
        },
    )?;
    Some(obligations)
}

/// Native compatibility for builtin operations whose argument descriptors
/// remain native. Runtime function calls use the retained carrier directly.
pub(in crate::kernel) fn evaluate_program_arguments_paths(
    state: &ExecutionState,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    environment: Option<&ExecutionEnvironment>,
) -> ExecutionResult<Vec<ArgumentsPath>> {
    Ok(evaluate_retained_program_arguments_paths(
        state,
        arguments,
        assumptions,
        budget,
        environment,
    )?
    .into_iter()
    .map(|path| ArgumentsPath {
        values: path
            .values
            .into_iter()
            .map(ExecutionValue::into_native)
            .collect(),
        outcome: path.outcome,
        facts: path.facts,
        obligations: path.obligations,
    })
    .collect())
}

pub(in crate::kernel) fn evaluate_retained_program_arguments_paths(
    state: &ExecutionState,
    arguments: &[ProgramExpression],
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
    environment: Option<&ExecutionEnvironment>,
) -> ExecutionResult<Vec<ArgumentsPath<ExecutionValue>>> {
    let mut paths = vec![ArgumentsPath {
        values: Vec::new(),
        outcome: None,
        facts: Vec::new().into(),
        obligations: Vec::new(),
    }];

    for argument in arguments {
        let mut next_paths = Vec::new();
        for path in paths {
            if path.outcome.is_some() {
                next_paths.push(path);
                continue;
            }

            let argument_assumptions =
                assumptions_with_path_context(assumptions, &path.facts, &path.obligations);
            for argument_path in crate::kernel::eval::evaluate_expression_value_paths(
                state,
                argument,
                &argument_assumptions,
                budget,
            )? {
                let Some((facts, obligations)) = merge_execution_pure_facts_and_obligations(
                    &path.facts,
                    &path.obligations,
                    &argument_path.facts,
                    &argument_path.obligations,
                    assumptions,
                ) else {
                    continue;
                };

                match argument_path.outcome {
                    ExpressionOutcome::Value(value) => {
                        let value = if matches!(argument, ProgramExpression::FunctionAddress(_)) {
                            let typed = type_function_address_value(
                                argument,
                                value.native().into_owned(),
                                environment,
                            );
                            value.retain_checked_pointer(typed)
                        } else {
                            value
                        };
                        let mut values = path.values.clone();
                        values.push(value);
                        next_paths.push(ArgumentsPath {
                            values,
                            outcome: None,
                            facts,
                            obligations,
                        });
                    }
                    ExpressionOutcome::UndefinedBehavior(undefined_behavior) => {
                        next_paths.push(ArgumentsPath {
                            values: path.values.clone(),
                            outcome: Some(FunctionOutcome::UndefinedBehavior(undefined_behavior)),
                            facts,
                            obligations,
                        })
                    }
                    ExpressionOutcome::RuntimeError(error) => next_paths.push(ArgumentsPath {
                        values: path.values.clone(),
                        outcome: Some(FunctionOutcome::RuntimeError(error)),
                        facts,
                        obligations,
                    }),
                }
            }
        }
        budget.check_path_width(next_paths.len())?;
        paths = next_paths;
    }

    budget.check_path_width(paths.len())?;
    Ok(paths)
}

pub(super) fn type_function_address_value(
    expression: &ProgramExpression,
    value: ProgramValue,
    environment: Option<&ExecutionEnvironment>,
) -> ProgramValue {
    let ProgramExpression::FunctionAddress(name) = expression else {
        return value;
    };
    let Some(environment) = environment else {
        return value;
    };
    let Some(function) = environment.get_function(name) else {
        return value;
    };
    match value {
        ProgramValue::Pointer(pointer)
            if pointer.block.is_function()
                && pointer.program_type()
                    == ProgramType::FunctionPointer(CallbackSignature::UNSPECIFIED) =>
        {
            // Return and parameter qualifications belong to the callback
            // signature, not to the function-pointer object's pointee view.
            ProgramValue::typed_pointer(pointer.into_pointer(), function.function_pointer_type())
        }
        value => value,
    }
}

pub(super) fn argument_binding_error(
    function: &ProgramFunction,
    values: &[ProgramValue],
) -> String {
    contract_argument_binding_error(function.contract_interface(), function.name(), values)
}

pub(super) fn contract_argument_binding_error(
    interface: &FunctionContractInterface,
    name: &str,
    values: &[ProgramValue],
) -> String {
    if interface
        .parameters()
        .iter()
        .zip(values)
        .any(|(parameter, value)| {
            matches!(
                (parameter.program_type(), value),
                (ProgramType::FunctionPointer(expected), ProgramValue::Pointer(actual))
                    if actual.block.is_function()
                        && actual.program_type() != ProgramType::FunctionPointer(expected)
            )
        })
    {
        format!(
            "incompatible signature for function pointer argument to {}",
            name
        )
    } else {
        format!("could not bind arguments for {name}")
    }
}

/// A function-level path carries the loadability of its own string literals
/// across the call boundary. This is intentionally derived from the function
/// metadata rather than by scanning all read-only memory, so a call summary
/// cannot accidentally certify an unrelated block.
pub(super) fn append_string_literal_loadable_facts(
    function: &ProgramFunction,
    outcome: &FunctionOutcome,
    facts: &mut ExecutionFacts,
) {
    let state = match outcome {
        FunctionOutcome::Return { state, .. } | FunctionOutcome::Throw { state, .. } => state,
        _ => return,
    };
    for literal in function.string_literals() {
        let base = Memory::string_literal_pointer(function.name(), literal.name(), literal.bytes());
        let proposition = Proposition::MemoryLoadable {
            memory: state.memory.clone(),
            base,
            bytes: MachineTerm::constant(literal.bytes().len() as u32),
            wide: false,
        };
        if !facts.iter().any(|fact| fact.proposition() == &proposition) {
            facts.push(ExecutionPureFact::certified(proposition));
        }
    }
}

pub(in crate::kernel) fn bind_program_function_arguments(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    values: &[ProgramValue],
) -> Option<ExecutionState> {
    bind_program_function_arguments_with(caller_state, function, values, false)
}

pub(super) fn bind_program_function_arguments_retained(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    values: &[ProgramValue],
    roots: &[ExecutionValue],
) -> Option<ExecutionState> {
    bind_program_function_arguments_impl(caller_state, function, values, false, Some(roots))
}

/// [`bind_program_function_arguments`], except that with `input_aggregates` each
/// by-value aggregate parameter's object is declared and not copied into:
/// it is the function's input itself, whose cells the producer of a proof's
/// entry names as their own entry values.
pub(in crate::kernel) fn bind_program_function_arguments_with(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    values: &[ProgramValue],
    input_aggregates: bool,
) -> Option<ExecutionState> {
    bind_program_function_arguments_impl(caller_state, function, values, input_aggregates, None)
}

fn bind_program_function_arguments_impl(
    caller_state: &ExecutionState,
    function: &ProgramFunction,
    values: &[ProgramValue],
    input_aggregates: bool,
    roots: Option<&[ExecutionValue]>,
) -> Option<ExecutionState> {
    // Preserve the value-only representation for parameters whose addresses
    // never escape. Besides avoiding unnecessary memory cells, this
    // keeps ordinary call summaries unchanged. A frame is needed only when
    // the function body actually contains an address-taking expression for a
    // parameter.
    let address_taken = function.address_taken_locals();
    let address_taken_parameters = function
        .parameters()
        .iter()
        // Taking the address of a pointer parameter's pointee (for example
        // `&p[1]`) mentions `p` while addressing the pointed-to object, not the
        // parameter object itself. A volatile pointer parameter is different:
        // its own object is the access, so it needs an address-backed slot for
        // the volatile event to name.
        .filter(|parameter| {
            (address_taken.contains(parameter.name()) || parameter.is_volatile())
                && (parameter.is_volatile() && parameter.program_type().is_pointer()
                    || matches!(
                        parameter.program_type(),
                        ProgramType::Int8
                            | ProgramType::Int16
                            | ProgramType::Int32
                            | ProgramType::UInt8
                            | ProgramType::UInt16
                            | ProgramType::UInt32
                            | ProgramType::Float32
                            | ProgramType::Float64
                    ))
        })
        .map(|parameter| parameter.name())
        .collect::<BTreeSet<_>>();
    let frame = caller_state.next_local_frame();
    let has_aggregate_parameters = function
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some());
    let mut callee_state = ExecutionState::new()
        .with_memory(caller_state.memory.clone())
        .with_resource_context(caller_state.resources.clone())
        .with_next_local_frame(
            if address_taken_parameters.is_empty() && !has_aggregate_parameters {
                frame
            } else {
                frame.saturating_add(1)
            },
        )
        .with_next_local_lifetime(caller_state.next_local_lifetime())
        // The body below declares its locals into the caller's memory with
        // this fresh locals map, which cannot see the caller's objects. Pass
        // down whether there are any to collide with, so each declaration
        // that could take a caller's `local:<name>` takes its own identity
        // instead. A frame that has bound nothing owns nothing, which is what
        // makes the outermost one answer no.
        .with_enclosing_frame_holds_locals(
            caller_state.enclosing_frame_holds_locals() || !caller_state.locals.is_empty(),
        );
    callee_state.mutex_ledger = caller_state.mutex_ledger.clone();
    callee_state.mutex_input_reservations = caller_state.mutex_input_reservations.clone();
    callee_state.opaque_mutex_acquisitions = caller_state.opaque_mutex_acquisitions.clone();
    callee_state.named_mutex_authorities = caller_state.named_mutex_authorities.clone();
    // The caller's outstanding workers stay outstanding across the call. A
    // callee cannot join them (each completion right names the caller's loan
    // participant), and returning its ledger must not erase their rights or
    // the population changes they defer to join.
    callee_state.thread_ledger = caller_state.thread_ledger.clone();
    callee_state.preserves_mutex_protocols = caller_state.preserves_mutex_protocols
        || preserves_mutex_protocols(function.contract_interface());
    callee_state.population_access = caller_state.population_access.clone();
    callee_state.observed_population_families = caller_state.observed_population_families.clone();
    Arc::make_mut(&mut callee_state.population_effects).creation = caller_state
        .population_effects
        .creation
        .as_ref()
        .map(|events| events.enter_call());
    // A function entry is a lexical/frame rebind, not an authority reset.
    // Preserve an already-active candidate loan through calls whose resource
    // interface is empty; the resource-transfer planner may replace these
    // fields with a checked callee participant when it lends new views.
    callee_state.loan_ledger = caller_state.loan_ledger.clone();
    callee_state.loan_participant = caller_state.loan_participant;
    callee_state.loan_view_bindings = caller_state.loan_view_bindings.clone();
    callee_state = initialize_program_function_globals(&callee_state, function);
    for (index, (parameter, value)) in function.parameters().iter().zip(values).enumerate() {
        if let Some(layout) = parameter.aggregate_layout() {
            let ProgramValue::Pointer(pointer) = value else {
                return None;
            };
            if pointer.is_null() {
                return None;
            }
            let source = pointer.pointer().clone();
            let slot = Memory::frame_local_pointer(frame, parameter.name());
            register_block_alignment(&slot.block, layout.alignment_bytes());
            // A proof's input object holds its own entry values: each field
            // is the read of that field before the object is declared, so
            // the value has the parameter's own spelling and no other
            // object stands behind it.
            let source = if input_aggregates {
                slot.clone()
            } else {
                register_aggregate_argument_source(&slot.block, &source);
                source
            };
            // Preserve the caller's memory state for symbolic source
            // loads. Declaring the destination first would make an unknown
            // external field load depend on the callee's fresh block and
            // prevent entry facts from relating it to the caller's value.
            callee_state.set_memory(copy_aggregate_fields(
                callee_state.memory.clone(),
                &source,
                &slot,
                layout,
            ));
            callee_state.set_memory(
                callee_state
                    .memory
                    .clone()
                    .with_block(slot.block.clone(), layout.size_bytes()),
            );
            callee_state.locals.set_aggregate_object_at(
                parameter.name().to_string(),
                layout.clone(),
                slot.clone(),
            );
            // A by-value parameter owns its fresh private bytes, just as an
            // aggregate local does. This grants no authority over pointers
            // stored inside it or over the caller's original object.
            callee_state.resources = callee_state
                .resources
                .clone()
                .unchecked_with_fact(private_aggregate_storage_owner(slot, layout));
            continue;
        }
        let value = coerce_program_function_argument_without_obligations(value, parameter)?
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant())
            .with_pointer_declared_object_class(parameter.pointee_class());
        if address_taken_parameters.contains(parameter.name()) {
            let slot = Memory::frame_local_pointer(frame, parameter.name());
            register_block_alignment(&slot.block, parameter.program_type().abi_alignment());
            callee_state.set_memory(
                callee_state
                    .memory
                    .clone()
                    .with_block(slot.block.clone(), value.byte_width())
                    .store(slot.clone(), value.clone()),
            );
            callee_state
                .locals
                .set_retained_typed_qualified_with_all_qualifiers(
                    parameter.name().to_string(),
                    roots.and_then(|roots| roots.get(index)).map_or_else(
                        || ExecutionValue::from(value.clone()),
                        |source| source.retain_coerced_argument(value.clone()),
                    ),
                    parameter.program_type(),
                    slot,
                    parameter.is_volatile(),
                    parameter.pointee_is_volatile(),
                    parameter.is_constant(),
                    parameter.pointee_is_constant(),
                );
        } else {
            callee_state
                .locals
                .set_retained_typed_qualified_with_all_qualifiers(
                    parameter.name().to_string(),
                    roots.and_then(|roots| roots.get(index)).map_or_else(
                        || ExecutionValue::from(value.clone()),
                        |source| source.retain_coerced_argument(value.clone()),
                    ),
                    parameter.program_type(),
                    Memory::value_parameter_pointer(parameter.name()),
                    parameter.is_volatile(),
                    parameter.pointee_is_volatile(),
                    parameter.is_constant(),
                    parameter.pointee_is_constant(),
                );
        }
    }
    // A contract's value parameters, such as `let n: uint64;`, follow the
    // C arguments when a proof is entered: at fresh values, as the C
    // parameters are, so the proof holds for every value.
    let value_parameters = function.contract_interface().value_parameters();
    let c_count = function.parameters().len();
    if !value_parameters.is_empty() && values.len() == c_count + value_parameters.len() {
        super::super::api::bind_contract_value_parameters(
            &mut callee_state,
            value_parameters,
            &values[c_count..],
        );
    }
    construction_return::bind(
        caller_state,
        function.contract_interface(),
        &mut callee_state,
    )?;
    Some(callee_state)
}

/// Binds only the locals needed to instantiate a body-independent contract
/// interface. This intentionally does not inspect a statement body or collect
/// address-taken locals. A direct application can additionally supply its
/// concrete declaration identity so global and static names in the interface
/// resolve to the program's stable storage; that identity is not body-proof
/// evidence. Named callbacks supply no concrete storage.
pub(super) fn bind_contract_arguments(
    caller_state: &ExecutionState,
    interface: &FunctionContractInterface,
    values: &[ProgramValue],
    storage: Option<&ProgramFunction>,
    roots: &[ExecutionValue],
) -> Option<ExecutionState> {
    if values.len() != interface.parameters().len() {
        return None;
    }
    let frame = caller_state.next_local_frame();
    let has_aggregate_parameters = interface
        .parameters()
        .iter()
        .any(|parameter| parameter.aggregate_layout().is_some());
    let mut callee_state = ExecutionState::new()
        .with_memory(caller_state.memory.clone())
        .with_resource_context(caller_state.resources.clone())
        .with_next_local_frame(if has_aggregate_parameters {
            frame.saturating_add(1)
        } else {
            frame
        })
        .with_next_local_lifetime(caller_state.next_local_lifetime())
        .with_enclosing_frame_holds_locals(
            caller_state.enclosing_frame_holds_locals() || !caller_state.locals.is_empty(),
        );
    callee_state.mutex_ledger = caller_state.mutex_ledger.clone();
    callee_state.mutex_input_reservations = caller_state.mutex_input_reservations.clone();
    callee_state.opaque_mutex_acquisitions = caller_state.opaque_mutex_acquisitions.clone();
    callee_state.named_mutex_authorities = caller_state.named_mutex_authorities.clone();
    // The caller's outstanding workers stay outstanding across the call. A
    // callee cannot join them (each completion right names the caller's loan
    // participant), and returning its ledger must not erase their rights or
    // the population changes they defer to join.
    callee_state.thread_ledger = caller_state.thread_ledger.clone();
    callee_state.preserves_mutex_protocols =
        caller_state.preserves_mutex_protocols || preserves_mutex_protocols(interface);
    callee_state.population_access = caller_state.population_access.clone();
    callee_state.observed_population_families = caller_state.observed_population_families.clone();
    Arc::make_mut(&mut callee_state.population_effects).creation = caller_state
        .population_effects
        .creation
        .as_ref()
        .map(|events| events.enter_call());
    callee_state.loan_ledger = caller_state.loan_ledger.clone();
    callee_state.loan_participant = caller_state.loan_participant;
    callee_state.loan_view_bindings = caller_state.loan_view_bindings.clone();
    if let Some(function) = storage {
        callee_state = initialize_program_function_globals(&callee_state, function);
    }
    for (index, (parameter, value)) in interface.parameters().iter().zip(values).enumerate() {
        if let Some(layout) = parameter.aggregate_layout() {
            let ProgramValue::Pointer(pointer) = value else {
                return None;
            };
            if pointer.is_null() {
                return None;
            }
            let source = pointer.pointer().clone();
            let slot = Memory::frame_local_pointer(frame, parameter.name());
            register_block_alignment(&slot.block, layout.alignment_bytes());
            callee_state.set_memory(copy_aggregate_fields(
                callee_state.memory.clone(),
                &source,
                &slot,
                layout,
            ));
            callee_state.set_memory(
                callee_state
                    .memory
                    .clone()
                    .with_block(slot.block.clone(), layout.size_bytes()),
            );
            callee_state.locals.set_aggregate_object_at(
                parameter.name().to_string(),
                layout.clone(),
                slot,
            );
            continue;
        }
        let value = coerce_program_function_argument_without_obligations(value, parameter)?
            .with_pointer_pointee_volatile(parameter.pointee_is_volatile())
            .with_pointer_pointee_constant(parameter.pointee_is_constant())
            .with_pointer_declared_object_class(parameter.pointee_class());
        callee_state
            .locals
            .set_retained_typed_qualified_with_all_qualifiers(
                parameter.name().to_string(),
                roots.get(index).map_or_else(
                    || ExecutionValue::from(value.clone()),
                    |source| source.retain_coerced_argument(value.clone()),
                ),
                parameter.program_type(),
                Memory::value_parameter_pointer(parameter.name()),
                parameter.is_volatile(),
                parameter.pointee_is_volatile(),
                parameter.is_constant(),
                parameter.pointee_is_constant(),
            );
    }
    construction_return::bind(caller_state, interface, &mut callee_state)?;
    Some(callee_state)
}

pub(super) fn coerce_program_function_argument_without_obligations(
    value: &ProgramValue,
    parameter: &ProgramParameter,
) -> Option<ProgramValue> {
    coerce_contract_argument_without_obligations(value, parameter)
}

pub(super) fn coerce_contract_argument_without_obligations(
    value: &ProgramValue,
    parameter: &ProgramParameter,
) -> Option<ProgramValue> {
    let mut obligations = Vec::new();
    let value = coerce_program_value_with_pointee_constant(
        value.clone(),
        parameter.program_type(),
        parameter.pointee_is_constant(),
        &mut obligations,
        &PureFactContext::new(),
    )?;
    obligations.is_empty().then_some(value)
}

pub(super) fn coerce_program_function_arguments(
    function: &ProgramFunction,
    values: &[ProgramValue],
    existing_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<ProgramValue>, Vec<ProofObligation>)> {
    coerce_contract_arguments(
        function.contract_interface(),
        values,
        existing_obligations,
        assumptions,
    )
}

pub(super) fn coerce_contract_arguments(
    interface: &FunctionContractInterface,
    values: &[ProgramValue],
    existing_obligations: &[ProofObligation],
    assumptions: &PureFactContext,
) -> Option<(Vec<ProgramValue>, Vec<ProofObligation>)> {
    if values.len() != interface.parameters().len() {
        return None;
    }
    let mut obligations = existing_obligations.to_vec();
    let mut coerced = Vec::with_capacity(values.len());
    for (parameter, value) in interface.parameters().iter().zip(values) {
        if parameter.aggregate_layout().is_some() {
            coerced.push(value.clone());
        } else {
            // A contract stated over one integer type's cells accepts a
            // pointer to the other signedness of the same width: C11 6.5p7
            // lets either read the object, and loads read a cell of either
            // signedness through either type (`ProgramType::read_cell`). This is
            // how a byte contract such as `strlen`'s serves a signed plain
            // `char *`.
            let value = match value {
                ProgramValue::Pointer(pointer)
                    if parameter.program_type() != pointer.program_type()
                        && parameter
                            .program_type()
                            .is_signedness_view_of(pointer.program_type()) =>
                {
                    ProgramValue::Pointer(pointer.clone().with_type(parameter.program_type()))
                }
                value => value.clone(),
            };
            coerced.push(coerce_program_value_with_pointee_constant(
                value,
                parameter.program_type(),
                parameter.pointee_is_constant(),
                &mut obligations,
                assumptions,
            )?);
        }
    }
    Some((coerced, obligations))
}

#[cfg(test)]
mod retained_result_scaling_tests {
    include!("../../scaling_tests/kernel/functions/call_arguments/tests.rs");
}

#[cfg(test)]
mod pointer_argument_tests {
    use super::*;

    #[test]
    fn algebraic_arguments_returns_and_caller_results_keep_roots() {
        let _session = crate::kernel::VerificationSession::enter();
        let ty = TypeParameterName::intern("ArgumentAlgebraicT");
        let root = KernelTermImport::default().algebraic(&AlgebraicTerm {
            algebraic_type: ty.algebraic_type(),
            node: AlgebraicTermNode::PureFunctionApplication {
                name: "algebraic_argument".into(),
                arguments: vec![],
            },
        });
        let source = ExecutionValue::Shared(root.clone());
        let native = source.clone().into_native();
        let function = program_function(
            ProgramType::Parameter(ty),
            "identity",
            vec![program_parameter("x", ProgramType::Parameter(ty))],
            program_return(crate::kernel::program_expression::variable("x")),
        );
        let state = ExecutionState::new();
        let callee = bind_program_function_arguments_retained(
            &state,
            &function,
            &[native.clone()],
            &[source.clone()],
        )
        .unwrap();
        let bound = callee.locals.get("x").unwrap();
        assert_eq!(bound.shared(), Some(&root));
        let legacy = bind_program_function_arguments(&state, &function, &[native.clone()]).unwrap();
        assert_eq!(bound, legacy.locals.get("x").unwrap());
        let returned = coerce_retained_function_return_value(
            bound.clone(),
            &function,
            &mut vec![],
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(returned.shared(), Some(&root));
        let mut caller = ExecutionState::new();
        set_function_result(&mut caller, &function, returned.clone());
        assert_eq!(
            caller.locals.get(C_CONTRACT_RESULT_NAME).unwrap().shared(),
            Some(&root)
        );
        crate::kernel::loops::assign_call_result(
            &mut caller,
            "received",
            returned,
            &mut vec![],
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(caller.locals.get("received").unwrap().shared(), Some(&root));
    }

    #[test]
    fn boolean_arguments_returns_and_caller_results_keep_roots() {
        let _session = crate::kernel::VerificationSession::enter();
        let root = KernelTermImport::default().boolean_call(&SharedPureApplication::intern(
            "boolean_argument".into(),
            vec![],
        ));
        let source = ExecutionValue::Shared(root.clone());
        let native = source.clone().into_native();
        let function = program_function(
            ProgramType::Bool,
            "identity",
            vec![program_parameter("x", ProgramType::Bool)],
            program_return(crate::kernel::program_expression::variable("x")),
        );
        let state = ExecutionState::new();
        let callee = bind_program_function_arguments_retained(
            &state,
            &function,
            &[native.clone()],
            &[source.clone()],
        )
        .unwrap();
        let bound = callee.locals.get("x").unwrap();
        assert_eq!(bound.shared(), Some(&root));
        let legacy = bind_program_function_arguments(&state, &function, &[native.clone()]).unwrap();
        assert_eq!(bound, legacy.locals.get("x").unwrap());
        let returned = coerce_retained_function_return_value(
            bound.clone(),
            &function,
            &mut vec![],
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(returned.shared(), Some(&root));
        let mut caller = ExecutionState::new();
        set_function_result(&mut caller, &function, returned.clone());
        assert_eq!(
            caller.locals.get(C_CONTRACT_RESULT_NAME).unwrap().shared(),
            Some(&root)
        );
        crate::kernel::loops::assign_call_result(
            &mut caller,
            "received",
            returned,
            &mut vec![],
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(caller.locals.get("received").unwrap().shared(), Some(&root));
        // Changed-type coercion uses the existing native conversion result.
        let converted = ProgramValue::Int32(MachineTerm::bool_cast(
            MachineIntegerType::Int32,
            ConditionTerm::Constant(true),
        ));
        assert_eq!(
            source
                .retain_coerced_argument(converted.clone())
                .into_native(),
            converted
        );
        let raw = ProgramValue::Bool(MachineTerm::Constant {
            format: MachineIntegerType::UInt8,
            bits: 2,
        });
        assert_eq!(
            ExecutionValue::Native(raw.clone())
                .retain_coerced_argument(raw.clone())
                .into_native(),
            raw
        );
    }

    #[test]
    fn pointer_execution_arguments_keep_selected_roots_and_native_bindings() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(1027100)),
            ProgramType::Int32Pointer,
        );
        let root = KernelTerm::shared_pointer_call(
            KernelTerm::checked_call(
                KernelType::Program(ProgramType::Int32Pointer),
                "argument_source".into(),
                vec![],
            ),
            SharedPointerValue::import(&pointer),
        );
        let mut state = ExecutionState::new();
        state.locals.set_retained_typed_with_all_qualifiers(
            "p",
            ExecutionValue::Shared(root.clone()),
            ProgramType::Int32Pointer,
            false,
            false,
            false,
            false,
        );
        let arguments = evaluate_retained_program_arguments_paths(
            &state,
            &[crate::kernel::program_expression::variable("p")],
            &PureFactContext::new(),
            &mut ExecutionBudget::default(),
            None,
        )
        .unwrap();
        assert_eq!(arguments.len(), 1);
        assert!(arguments[0].outcome.is_none());
        assert_eq!(arguments[0].values[0].shared(), Some(&root));
        let function = program_function(
            ProgramType::Int32Pointer,
            "identity",
            vec![program_parameter("x", ProgramType::Int32Pointer)],
            program_return(crate::kernel::program_expression::variable("x")),
        );
        let native = vec![ProgramValue::Pointer(pointer)];
        let retained = bind_program_function_arguments_retained(
            &state,
            &function,
            &native,
            &arguments[0].values,
        )
        .unwrap();
        let legacy = bind_program_function_arguments(&state, &function, &native).unwrap();
        let retained = retained.locals.get("x").unwrap();
        let legacy = legacy.locals.get("x").unwrap();
        assert!(matches!(
            retained.shared().unwrap().node(),
            KernelTermNode::PointerCall { .. }
        ));
        assert_eq!(retained, legacy);
        assert!(
            retained
                .shared()
                .unwrap()
                .pointer_payload()
                .unwrap()
                .same_source_payload(&SharedPointerValue::import(legacy.pointer().unwrap()))
        );
    }
}

#[cfg(test)]
mod pointer_return_tests {
    use super::*;
    #[test]
    fn pointer_returns_keep_complete_payload_and_const_drop_refusals() {
        let _session = crate::kernel::VerificationSession::enter();
        let pointer = PointerValue::new(
            Pointer::symbolic(Variable(1027400)),
            ProgramType::Int32Pointer,
        )
        .with_pointee_volatile(true)
        .with_pointee_constant(true);
        let root = KernelTerm::shared_pointer_call(
            KernelTerm::checked_call(
                KernelType::Program(ProgramType::Int32Pointer),
                "source".into(),
                vec![],
            ),
            SharedPointerValue::import(&pointer),
        );
        let plain = program_function(
            ProgramType::Int32Pointer,
            "result",
            Vec::new(),
            program_return(crate::kernel::program_expression::int32_literal(0)),
        );
        let retained = || StoredExecutionValue::from(ExecutionValue::Shared(root.clone()));
        assert!(
            coerce_retained_function_return_value(
                retained(),
                &plain,
                &mut Vec::new(),
                &PureFactContext::new()
            )
            .is_none()
        );
        let constant = plain.with_return_pointee_constant(true);
        let result = coerce_retained_function_return_value(
            retained(),
            &constant,
            &mut Vec::new(),
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(result.shared(), Some(&root));
        let expected = coerce_function_return_value(
            ProgramValue::Pointer(pointer),
            &constant,
            &mut Vec::new(),
            &PureFactContext::new(),
        )
        .unwrap();
        assert_eq!(result.native().as_ref(), &expected);
        let mut state = ExecutionState::new();
        set_function_result(&mut state, &constant, result.clone());
        let bound = state.locals.get(C_CONTRACT_RESULT_NAME).unwrap();
        assert!(bound.shared().is_some());
        assert!(bound.pointer().unwrap().pointee_constant());
        assert!(!bound.pointer().unwrap().pointee_volatile());
        state.locals.set_typed(
            "mutable",
            ProgramValue::typed_pointer(Pointer::null(), ProgramType::Int32Pointer),
            ProgramType::Int32Pointer,
        );
        assert!(
            crate::kernel::loops::assign_call_result(
                &mut state,
                "mutable",
                result.clone(),
                &mut Vec::new(),
                &PureFactContext::new()
            )
            .is_err()
        );
        crate::kernel::loops::assign_call_result(
            &mut state,
            "fresh",
            result,
            &mut Vec::new(),
            &PureFactContext::new(),
        )
        .unwrap();
        assert!(state.locals.get("fresh").unwrap().shared().is_some());
        assert!(
            state
                .locals
                .get("fresh")
                .unwrap()
                .pointer()
                .unwrap()
                .pointee_constant()
        );
    }
}
