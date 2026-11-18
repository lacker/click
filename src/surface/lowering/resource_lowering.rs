use super::*;
use crate::kernel::{ResourceFieldSchema, ResourceTerm};
use crate::kernel::{bits32_constant, constant_u32, int32_constant};

pub(in crate::surface) fn construction_result_layout(
    parsed: &crate::languages::interface::ImportedFunction,
) -> Option<&crate::kernel::AggregateLayout> {
    let interface = parsed.prelowered_kernel_function()?.contract_interface();
    (interface.aggregate_return_mode() == crate::kernel::AggregateReturnMode::Construction)
        .then(|| interface.return_aggregate_layout())
        .flatten()
}

/// The frontend's result object is an implicit in/out resource. Its authority
/// originates with the caller's storage, not with the destination binding.
pub(in crate::surface) fn construction_result_resource(
    parsed: &crate::languages::interface::ImportedFunction,
) -> Result<Option<ResourceSpec>, ClickError> {
    let Some(layout) = construction_result_layout(parsed) else {
        return Ok(None);
    };
    if layout.size_bytes() > i32::MAX as u32 {
        return Err(ClickError::new(
            "construction result exceeds the supported byte-range size",
        ));
    }
    Ok(Some(ResourceSpec::owned_memory(
        MemorySegment::new(
            crate::kernel::program_expression::variable(crate::kernel::CONTRACT_RESULT),
            crate::kernel::program_expression::int32_literal(0),
            crate::kernel::program_expression::int32_literal(layout.size_bytes()),
        )
        .with_element_width(1),
    )))
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct ConcreteMemoryRangeSeed {
    pub(in crate::surface) base: Address,
    pub(in crate::surface) bytes: u32,
    pub(in crate::surface) element_width: u32,
    /// `None` denotes a range whose logical elements are aggregates, such as
    /// C structs. Those ranges are materialized one typed field at a time
    /// using `struct_layout`.
    pub(in crate::surface) element_type: Option<ProgramType>,
    pub(in crate::surface) struct_layout: Option<crate::languages::interface::RecordLayout>,
}

impl ConcreteMemoryRangeSeed {
    /// A typed element wider than the contract segment's stride, such as a
    /// pointer field owned as two `int32` halves, is one cell of its own
    /// width: seeding one per stride would overlap each with the next.
    fn with_element_cells(mut self) -> Self {
        if let Some(element_type) = self.element_type
            && self.struct_layout.is_none()
        {
            let width = element_type.byte_width();
            if width > self.element_width && width != 0 && self.bytes.is_multiple_of(width) {
                self.element_width = width;
            }
        }
        self
    }
}

// Input addresses from different function proofs must not share load/type
// metadata. Derive their identities from the function and parameter, so adding
// unrelated functions cannot change proof search order. This range lies above
// frontend/termination/callback names and below scalar loads: input addresses
// remain preferred canonical representatives. Hash collisions are reported,
// never resolved by allocation order or by aliasing two inputs.
const INPUT_VARIABLE_BASE: u64 = 1 << 34;
const INPUT_VARIABLE_CEILING: u64 = 1 << 40;
thread_local! {
    static INPUT_SCOPES: std::cell::RefCell<std::collections::HashMap<u64, String>> = Default::default();
    static INPUT_POINTER_PLACES: std::cell::RefCell<std::collections::HashMap<Variable, (u64, usize, crate::kernel::Pointer)>> = Default::default();
    static INPUT_VARIABLE_OWNERS: std::cell::RefCell<std::collections::HashMap<Variable, (u64, usize)>> = Default::default();
    static INPUT_VARIABLES: std::cell::RefCell<std::collections::HashMap<(u64, usize), Variable>> = Default::default();
}

pub(in crate::surface) fn input_scope(name: &str) -> u64 {
    use std::hash::{Hash, Hasher};
    let mut hasher = std::collections::hash_map::DefaultHasher::new();
    name.hash(&mut hasher);
    let mut slot = hasher.finish();
    INPUT_SCOPES.with(|scopes| {
        let mut scopes = scopes.borrow_mut();
        loop {
            match scopes.get(&slot) {
                Some(known) if known == name => return slot,
                Some(_) => slot = slot.wrapping_add(1),
                None => {
                    scopes.insert(slot, name.to_string());
                    return slot;
                }
            }
        }
    })
}

/// Clears input metadata with the kernel's session tables. Content-based names
/// survive session resets; metadata about previous proofs does not.
pub(in crate::surface) fn reset_input_identities() {
    INPUT_SCOPES.with(|scopes| scopes.borrow_mut().clear());
    INPUT_POINTER_PLACES.with(|places| places.borrow_mut().clear());
    INPUT_VARIABLES.with(|variables| variables.borrow_mut().clear());
    INPUT_VARIABLE_OWNERS.with(|owners| owners.borrow_mut().clear());
}

/// Prepares input metadata for all functions before any proof runs, including
/// selected-unit verification. Names depend only on the function and parameter;
/// failures remain the responsibility of the function's entry lowering.
pub(in crate::surface) fn reserve_input_identities(
    function: &crate::languages::interface::ImportedFunction,
) {
    let scope = input_scope(function.kernel_name());
    if input_arguments(scope, function.parameters(), |_| None).is_ok()
        && function.returns_by_construction()
    {
        let _ = input_pointer_variable(scope, function.parameters().len());
    }
}

/// The input names this thread holds for the function `name`, by parameter
/// index.
#[cfg(test)]
pub(in crate::surface) fn input_identities_of(name: &str) -> Vec<(usize, Variable)> {
    let scopes = INPUT_SCOPES.with(|scopes| {
        scopes
            .borrow()
            .iter()
            .filter(|(_, known)| known.as_str() == name)
            .map(|(scope, _)| *scope)
            .collect::<Vec<_>>()
    });
    let mut identities = INPUT_VARIABLES.with(|variables| {
        variables
            .borrow()
            .iter()
            .filter(|((scope, _), _)| scopes.contains(scope))
            .map(|((_, index), variable)| (*index, *variable))
            .collect::<Vec<_>>()
    });
    identities.sort();
    identities
}

fn input_pointer_variable(scope: u64, index: usize) -> Result<Variable, ClickError> {
    INPUT_VARIABLES.with(|variables| {
        let mut variables = variables.borrow_mut();
        if let Some(variable) = variables.get(&(scope, index)) {
            return Ok(*variable);
        }
        use std::hash::{Hash, Hasher};
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        (scope, index as u64).hash(&mut hasher);
        let variable = Variable(
            INPUT_VARIABLE_BASE + hasher.finish() % (INPUT_VARIABLE_CEILING - INPUT_VARIABLE_BASE),
        );
        INPUT_VARIABLE_OWNERS.with(|owners| {
            let mut owners = owners.borrow_mut();
            match owners.entry(variable) {
                std::collections::hash_map::Entry::Vacant(entry) => {
                    entry.insert((scope, index));
                    Ok(())
                }
                std::collections::hash_map::Entry::Occupied(entry)
                    if *entry.get() == (scope, index) =>
                {
                    Ok(())
                }
                _ => Err(ClickError::new("pointer input variable identity collision")),
            }
        })?;
        variables.insert((scope, index), variable);
        Ok(variable)
    })
}

// Resolve only an exact universal input, including its physical stride and type.
// This index is populated during lowering, so expansion scopes may be entered
// before the function is verified. No unrelated function inputs are searched.
pub(in crate::surface) fn input_pointer_parameter(
    scope: u64,
    pointer: &crate::kernel::Pointer,
) -> Option<usize> {
    let variable = input_pointer_identity(pointer)?;
    crate::instrumentation::record_deterministic_work(1);
    INPUT_POINTER_PLACES.with(|places| {
        let places = places.borrow();
        let (owner, index, original) = places.get(&variable)?;
        (*owner == scope && original == pointer).then_some(*index)
    })
}

fn input_pointer_identity(pointer: &crate::kernel::Pointer) -> Option<Variable> {
    if pointer.address().base != AddressBase::ExternalArgument {
        return None;
    }
    match &pointer.address().offset {
        AddressOffset::Int32Scaled { value, .. } => value.operand_view().variable().copied(),
        _ => None,
    }
}

/// Keep the declaration class on the symbolic caller argument as well as
/// on the checked callee binding. Contract evaluation still needs that
/// information after the callee frame has been popped.
fn initial_pointer_argument(
    pointer: Address,
    parameter: &crate::languages::interface::ImportedParameter,
    index: usize,
    scope: u64,
    required: Option<crate::kernel::effective_type::CAccessClass>,
) -> ProgramExpression {
    let parameter = parameter.to_kernel_parameter();
    ProgramExpression::Value(
        ProgramValue::typed_pointer(pointer, parameter.program_type())
            .with_contract_pointer_object_class(parameter.pointee_class(), required, index, scope),
    )
}

/// The symbolic argument each parameter receives at function entry, naming
/// the inputs that need a scoped identity. `required` gives the object
/// class the contract requires of a pointer parameter; reserving names
/// before any proof runs passes none, since classes do not affect names.
fn input_arguments(
    scope: u64,
    parameters: &[crate::languages::interface::ImportedParameter],
    required: impl Fn(usize) -> Option<crate::kernel::effective_type::CAccessClass>,
) -> Result<Vec<ProgramExpression>, ClickError> {
    let initial_pointer_argument = |pointer, parameter, index, scope| {
        initial_pointer_argument(pointer, parameter, index, scope, required(index))
    };
    let mut arguments = Vec::new();
    for (index, parameter) in parameters.iter().enumerate() {
        if parameter.is_struct_value() {
            arguments.push(initial_pointer_argument(
                Address {
                    base: AddressBase::ExternalArgument,
                    offset: scale_int32_offset(
                        MachineTerm::Variable(input_pointer_variable(scope, index)?),
                        1,
                    ),
                },
                parameter,
                index,
                scope,
            ));
            continue;
        }
        match parameter.interface_type() {
            InterfaceType::Parameter(name) => {
                arguments.push(ProgramExpression::Value(
                    crate::kernel::symbolic_call_result(
                        crate::kernel::ProgramType::Parameter(name),
                        Variable(arguments.len() as u64),
                    ),
                ));
            }
            InterfaceType::Int128 => {
                arguments.push(ProgramExpression::Value(ProgramValue::Int128(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }
            InterfaceType::UInt128 => {
                arguments.push(ProgramExpression::Value(ProgramValue::UInt128(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }

            InterfaceType::Void => {
                return Err(ClickError::new(format!(
                    "parameter `{}` cannot have type void",
                    parameter.name()
                )));
            }
            // A `Bool` parameter is a binder of the kernel sort (Stage 5).
            InterfaceType::Bool => {
                arguments.push(ProgramExpression::Value(
                    crate::kernel::ProgramValue::of_bool(crate::kernel::ConditionTerm::Variable(
                        Variable(arguments.len() as u64),
                    )),
                ));
            }
            InterfaceType::VoidPointer | InterfaceType::VoidPointerPointer => {
                arguments.push(initial_pointer_argument(
                    Address {
                        base: AddressBase::ExternalArgument,
                        offset: scale_int32_offset(
                            MachineTerm::Variable(input_pointer_variable(scope, index)?),
                            1,
                        ),
                    },
                    parameter,
                    index,
                    scope,
                ));
            }
            InterfaceType::FunctionPointer(_) => {
                arguments.push(initial_pointer_argument(
                    Address::symbolic_function(input_pointer_variable(scope, index)?),
                    parameter,
                    index,
                    scope,
                ));
            }
            InterfaceType::Int8Pointer | InterfaceType::Int8PointerPointer => {
                let interface_type = parameter.interface_type();
                // Struct array parameters are lowered to byte pointers in the
                // kernel, so their symbolic external argument address uses
                // byte-pointer identity. The struct stride is retained only
                // when indexing the parameter and lowering its resource
                // clauses.
                let element_width = parameter.array_element_width().map_or_else(
                    || {
                        interface_type
                            .pointee_type()
                            .expect("pointer parameter has a pointee")
                            .to_kernel_type()
                            .byte_width()
                    },
                    |_| 1,
                );
                arguments.push(initial_pointer_argument(
                    Address {
                        base: AddressBase::ExternalArgument,
                        offset: scale_int32_offset(
                            MachineTerm::Variable(input_pointer_variable(scope, index)?),
                            i64::from(element_width),
                        ),
                    },
                    parameter,
                    index,
                    scope,
                ));
            }
            InterfaceType::Int16Pointer
            | InterfaceType::UInt16Pointer
            | InterfaceType::Int32Pointer
            | InterfaceType::CharPointer(_)
            | InterfaceType::UInt8Pointer
            | InterfaceType::UInt32Pointer
            | InterfaceType::Int128Pointer
            | InterfaceType::Int64Pointer(_)
            | InterfaceType::UInt128Pointer
            | InterfaceType::UInt64Pointer(_)
            | InterfaceType::Int16PointerPointer
            | InterfaceType::UInt16PointerPointer
            | InterfaceType::Int32PointerPointer
            | InterfaceType::CharPointerPointer(_)
            | InterfaceType::UInt8PointerPointer
            | InterfaceType::UInt32PointerPointer
            | InterfaceType::Int128PointerPointer
            | InterfaceType::Int64PointerPointer(_)
            | InterfaceType::UInt128PointerPointer
            | InterfaceType::UInt64PointerPointer(_)
            | InterfaceType::Float32Pointer
            | InterfaceType::Float64Pointer
            | InterfaceType::Float32PointerPointer
            | InterfaceType::Float64PointerPointer
            | InterfaceType::ParameterPointer(_) => {
                let interface_type = parameter.interface_type();
                // Struct array parameters are lowered to byte pointers in the
                // kernel, so their symbolic external argument address uses
                // byte-pointer identity. The struct stride is retained only
                // when indexing the parameter and lowering its resource
                // clauses.
                let element_width = parameter.array_element_width().map_or_else(
                    || {
                        interface_type
                            .pointee_type()
                            .expect("pointer parameter has a pointee")
                            .to_kernel_type()
                            .byte_width()
                    },
                    |_| 1,
                );
                let pointer = Address {
                    base: AddressBase::ExternalArgument,
                    offset: scale_int32_offset(
                        MachineTerm::Variable(input_pointer_variable(scope, index)?),
                        i64::from(element_width),
                    ),
                };
                arguments.push(initial_pointer_argument(pointer, parameter, index, scope));
            }
            InterfaceType::Int8 => {
                arguments.push(ProgramExpression::Value(ProgramValue::Int8(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }
            InterfaceType::Int16 => {
                arguments.push(ProgramExpression::Value(ProgramValue::Int16(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }
            InterfaceType::Int32 => {
                arguments.push(ProgramExpression::Value(ProgramValue::Int32(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }
            InterfaceType::Char(crate::languages::c::syntax::PlainChar::Signed) => {
                arguments.push(ProgramExpression::Value(ProgramValue::Int8(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }
            InterfaceType::Char(crate::languages::c::syntax::PlainChar::Unsigned)
            | InterfaceType::UInt8 => {
                arguments.push(ProgramExpression::Value(ProgramValue::UInt8(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }
            InterfaceType::UInt16 => {
                arguments.push(ProgramExpression::Value(ProgramValue::UInt16(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }
            InterfaceType::UInt32 => {
                arguments.push(ProgramExpression::Value(ProgramValue::UInt32(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }
            InterfaceType::Int64(_) => {
                arguments.push(ProgramExpression::Value(
                    ProgramValue::Int64(MachineTerm::Variable(Variable(arguments.len() as u64)))
                        .complete_word(Address::symbolic(input_pointer_variable(scope, index)?)),
                ));
            }
            InterfaceType::UInt64(_) => {
                arguments.push(ProgramExpression::Value(
                    ProgramValue::UInt64(MachineTerm::Variable(Variable(arguments.len() as u64)))
                        .complete_word(Address::symbolic(input_pointer_variable(scope, index)?)),
                ));
            }
            InterfaceType::Float32 => {
                arguments.push(ProgramExpression::Value(ProgramValue::Float32(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }
            InterfaceType::Float64 => {
                arguments.push(ProgramExpression::Value(ProgramValue::Float64(
                    MachineTerm::Variable(Variable(arguments.len() as u64)),
                )));
            }
            InterfaceType::Int8Array(_) => {
                return Err(ClickError::new(format!(
                    "array parameter `{}` should have lowered to a pointer",
                    parameter.name()
                )));
            }
            InterfaceType::Int32Array(_)
            | InterfaceType::CharArray(_, _)
            | InterfaceType::UInt8Array(_)
            | InterfaceType::Int16Array(_)
            | InterfaceType::UInt16Array(_)
            | InterfaceType::UInt32Array(_)
            | InterfaceType::Int128Array(_)
            | InterfaceType::Int64Array(_, _)
            | InterfaceType::UInt128Array(_)
            | InterfaceType::UInt64Array(_, _)
            | InterfaceType::Float32Array(_)
            | InterfaceType::Float64Array(_) => {
                return Err(ClickError::new(format!(
                    "array parameter `{}` should have lowered to a pointer",
                    parameter.name()
                )));
            }
            InterfaceType::PointerArray(_, _, _) => {
                return Err(ClickError::new(format!(
                    "array parameter `{}` should have lowered to a pointer",
                    parameter.name()
                )));
            }
        }
    }
    Ok(arguments)
}

pub(in crate::surface) fn initial_call_state(
    requires: &[Requirement],
    parameters: &[crate::languages::interface::ImportedParameter],
    function: &ProgramFunction,
    composite_definitions: &[CompositeResourceDefinition],
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(ExecutionState, Vec<ProgramExpression>, PureFactContext), ClickError> {
    if parameters.len() as u64 >= POINTER_ARGUMENT_VARIABLE_BASE {
        return Err(ClickError::new(
            "function parameter variable namespace exhausted",
        ));
    }
    let aggregate_parameters = parameters
        .iter()
        .filter(|parameter| parameter.is_struct_value())
        .map(|parameter| parameter.name())
        .collect::<BTreeSet<_>>();
    for requirement in requires {
        if let Requirement::Resource(resource) = requirement {
            reject_aggregate_parameter_storage_resource(resource, &aggregate_parameters)?;
        }
    }
    let required = |index: usize| {
        function
            .contract_interface()
            .object_type_requirements()
            .get(&index)
            .cloned()
    };
    let initial_pointer_argument = |pointer, parameter, index, scope| {
        initial_pointer_argument(pointer, parameter, index, scope, required(index))
    };
    let scope = input_scope(function.name());
    let mut arguments = input_arguments(scope, parameters, required)?;

    // Install ordinary function storage before adding symbolic loadable
    // cells. Otherwise a loadable clause can create a block first and leave
    // entry initialization unable to install its stable typed cells.
    let initial = ExecutionState::new().with_population_creation_tracking();
    let mut state = crate::kernel::initialize_program_function_globals(&initial, function);
    if function.contract_interface().aggregate_return_mode()
        == crate::kernel::AggregateReturnMode::Construction
    {
        let layout = function
            .contract_interface()
            .return_aggregate_layout()
            .ok_or_else(|| ClickError::new("construction result has no layout"))?
            .clone();
        let destination = Address::symbolic(input_pointer_variable(scope, parameters.len())?);
        crate::kernel::register_block_alignment(&destination.base, layout.alignment_bytes());
        let memory = state
            .memory()
            .clone()
            .with_uninitialized_block(destination.base.clone(), layout.size_bytes());
        state = state.with_memory(memory);
        state = state.with_aggregate_return_destination(destination.clone(), layout.clone());
        // Resource preparation evaluates the implicit contract segment before
        // the checked function-entry binder installs its aggregate local.
        state = state.with_local(
            crate::kernel::CONTRACT_RESULT,
            ProgramValue::typed_pointer(destination.clone(), function.return_type()),
        );
        let storage = ResourceFact::own_memory(MemoryRange::new_with_element_width(
            destination,
            0.into(),
            layout.size_bytes().into(),
            1,
        ));
        // Materializing by-value arguments also binds the function's selected
        // return destination. Install its existing implicit byte owner with
        // the raw storage, before that checked binding; requirement lowering
        // below retains the owner rather than manufacturing a second one.
        let resources = state.resources().clone().unchecked_with_fact(storage);
        state = state.with_resource_context(resources);
    }
    if let Some((index, layout)) = function.contract_interface().construction_parameter() {
        let parameter = parameters
            .get(index)
            .ok_or_else(|| ClickError::new("constructor destination parameter is missing"))?;
        // A symbolic block is an arbitrary input identity, not a fresh local.
        // Record the raw footprint before resource naming can seed typed cells.
        // The constructor can target a subobject, so do not fix its containing
        // allocation's size. Field liveness comes from the entry contract.
        let destination = Address::symbolic(input_pointer_variable(scope, index)?);
        crate::kernel::register_block_alignment(&destination.base, layout.alignment_bytes());
        arguments[index] = initial_pointer_argument(destination.clone(), parameter, index, scope);
        let memory = state
            .memory()
            .clone()
            .with_uninitialized_object(destination, layout.size_bytes());
        state = state.with_memory(memory);
    }
    if parameters
        .iter()
        .any(|parameter| parameter.is_struct_value())
    {
        // A by-value argument is an already-evaluated C value. Materialize its
        // aggregate image using the same typed copy operation as C calls,
        // before resource clauses follow any pointer fields. This image is
        // caller storage; the callee still receives its own fresh copy.
        state = crate::kernel::program_function_input_objects_state(&state, function, &arguments)
            .ok_or_else(|| {
            ClickError::new("could not materialize aggregate argument values")
        })?;
        for (index, (parameter, argument)) in parameters.iter().zip(&mut arguments).enumerate() {
            if parameter.is_struct_value() {
                *argument = initial_pointer_argument(
                    state
                        .locals()
                        .aggregate_object_pointer(parameter.name())
                        .expect("materialized aggregate argument")
                        .clone(),
                    parameter,
                    index,
                    scope,
                );
            }
        }
    }
    // Every pass below lowers one requirement at a time; the index lets each
    // read only the parameters that requirement names.
    let parameter_index = crate::surface::ParameterIndex::new(parameters);
    let parameter_binding =
        ParameterBinding::new(parameters, &arguments).with_index(&parameter_index);
    let mut loadable_ranges = BTreeMap::new();
    for requirement in requires {
        if let Some((name, bytes)) = concrete_loadable_block(requirement, parameter_binding)? {
            loadable_ranges.insert(name, bytes);
        }
        if let Requirement::Resource(resource) = requirement {
            for (name, bytes) in concrete_access_resource_blocks(resource, parameter_binding)? {
                loadable_ranges.insert(name, bytes);
            }
        }
    }

    let memory = memory_with_symbolic_loadable_cells(state.memory().clone(), &loadable_ranges);
    // In particular, a resource such as `pointer[0..1]` must follow the
    // pointer value already present in the entry state, rather than deriving
    // a second pointer from the raw memory-load term for the pointer slot.
    let memory =
        materialize_symbolic_access_resource_cells(memory, &state, requires, parameter_binding)?;
    let memory = mark_uninitialized_resource_memory(memory, requires, parameter_binding)?;
    let state = state.with_memory(memory);
    // Resource endpoints are named under the entry's declared pure premises.
    // Calls still discharge these requirements before transferring ownership.
    let entry_propositions = crate::surface::proof::available_initial_requirement_propositions(
        requires,
        parameter_binding,
        &state,
        spec_definitions,
    );
    let entry_assumptions =
        crate::surface::verification::assumptions_from_propositions(&entry_propositions);
    let resources = resource_context_from_requirements(
        requires,
        parameter_binding,
        &state,
        &entry_assumptions,
    )?;
    let mut state = crate::kernel::execution_state_with_assumed_mutex_inputs(
        state.with_resource_context(resources),
    );
    {
        // A standalone helper is proved for an arbitrary population supplied
        // by its caller. Import only the explicitly declared ownership, with
        // no exact total or C creation right; the call site later checks the actual
        // authority and member transfer against its concrete ledger.
        // Index this entry's member inputs by their complete authority scope,
        // not just family: another pool's member is an ordinary frame, not
        // evidence for this pool's population. Include unsupported quantities
        // so they fail checked import instead of becoming authority-only input.
        let mut wildcard_members =
            BTreeMap::<crate::kernel::ResourceDescription, Vec<ResourceFact>>::new();
        for fact in state.resources().facts() {
            let ResourceFact::Own(Resource::Composite { name, arguments }, _) = fact else {
                continue;
            };
            if arguments.len() < 2 {
                continue;
            }
            let scope = crate::kernel::ResourceDescription::new(
                name.clone(),
                vec![arguments.get(0).expect("argument index").into_native()].into(),
                ResourceFieldSchema::new(vec![]).expect("empty resource schema"),
            )
            .with_population_arity(arguments.len());
            if let Ok(scope) = scope {
                wildcard_members
                    .entry(scope)
                    .or_default()
                    .push(fact.clone());
            }
        }
        let authorities = state
            .resources()
            .facts()
            .iter()
            .filter(|fact| matches!(fact.resource(), Resource::PopulationAuthority(_)))
            .cloned()
            .collect::<Vec<_>>();
        for authority in authorities {
            let Resource::PopulationAuthority(description) = authority.resource() else {
                unreachable!();
            };
            if description.population_arity().is_some() {
                let Some(members) = wildcard_members.get(description) else {
                    state = state
                        .import_opaque_wildcard_authority(&authority)
                        .map_err(ClickError::new)?;
                    continue;
                };
                if members.len() != 1 {
                    return Err(ClickError::new(
                        "wildcard helper entry currently supports one concrete member",
                    ));
                }
                state = state
                    .import_opaque_wildcard_population(&authority, &members[0])
                    .map_err(ClickError::new)?;
                continue;
            }
            state = state
                .import_opaque_population_inputs(&authority)
                .map_err(ClickError::new)?;
        }
        let controls = state
            .resources()
            .facts()
            .iter()
            .filter_map(|fact| {
                let Resource::Composite { name, .. } = fact.resource() else {
                    return None;
                };
                let definition = composite_definitions
                    .iter()
                    .find(|definition| definition.name() == name)?;
                definition
                    .contains()
                    .iter()
                    .any(|child| matches!(child.term(), ResourceTerm::PopulationAuthority { .. }))
                    .then(|| (fact.clone(), definition))
            })
            .collect::<Vec<_>>();
        for (control, definition) in controls {
            state = state
                .import_opaque_control_wrapper(
                    &control,
                    definition,
                    &PureFactContext::new(),
                    &wildcard_members,
                )
                .map_err(ClickError::new)?;
        }
    }
    INPUT_POINTER_PLACES.with(|places| {
        let mut places = places.borrow_mut();
        for (index, argument) in arguments.iter().take(parameters.len()).enumerate() {
            if let ProgramExpression::Value(ProgramValue::Pointer(pointer)) = argument
                && let Some(variable) = input_pointer_identity(pointer)
            {
                places.insert(variable, (scope, index, pointer.clone()));
            }
        }
    });
    state
        .memory()
        .prepare_parameter_store_partition(state.resources());
    Ok((state, arguments, entry_assumptions))
}

/// A contract may transfer memory reached through a copied pointer value,
/// but cannot borrow or transfer the callee's private parameter object.
fn reject_aggregate_parameter_storage_resource(
    resource: &ResourceClause,
    parameters: &BTreeSet<&str>,
) -> Result<(), ClickError> {
    fn root(expression: &ProgramExpression) -> Option<&str> {
        match expression {
            ProgramExpression::Variable(name) => name.named(),
            ProgramExpression::PointerOffsetBytes { pointer, .. }
            | ProgramExpression::Subobject { pointer, .. }
            | ProgramExpression::AddressOf(pointer)
            | ProgramExpression::CheckedObjectAddress(pointer) => root(pointer),
            ProgramExpression::Add(pointer, _) | ProgramExpression::Subtract(pointer, _) => {
                root(pointer)
            }
            ProgramExpression::TypedLoad {
                pointer,
                value_type:
                    ProgramType::Int32Array(_)
                    | ProgramType::UInt32Array(_)
                    | ProgramType::UInt8Array(_)
                    | ProgramType::Int128Array(_)
                    | ProgramType::Int64Array(_)
                    | ProgramType::UInt128Array(_)
                    | ProgramType::UInt64Array(_),
                ..
            } => root(pointer),
            _ => None,
        }
    }
    let segments = match resource {
        ResourceClause::Named { resource, .. } => {
            return reject_aggregate_parameter_storage_resource(resource, parameters);
        }
        ResourceClause::OwnMemory(segment) | ResourceClause::ViewMemory(segment) => {
            std::slice::from_ref(segment)
        }
        ResourceClause::MemoryAggregate { segments, .. } => segments,
        _ => return Ok(()),
    };
    for segment in segments {
        if let Some(parameter) = root(&segment.base).filter(|name| parameters.contains(name)) {
            return Err(ClickError::new(format!(
                "by-value parameter `{parameter}` supplies its field values directly; its private storage cannot be an input resource"
            )));
        }
    }
    Ok(())
}

pub(in crate::surface) fn memory_with_symbolic_loadable_cells(
    mut memory: SymbolicMemory,
    loadable_ranges: &BTreeMap<String, ConcreteMemoryRangeSeed>,
) -> SymbolicMemory {
    let base_memory = memory.clone();
    for range in loadable_ranges.values() {
        if let Some(layout) = &range.struct_layout {
            let mut offset: u32 = 0;
            while offset
                .checked_add(range.element_width)
                .is_some_and(|end| end <= range.bytes)
            {
                let element_pointer = offset_pointer_by_elements(
                    range.base.clone(),
                    MachineTerm::constant(offset / range.element_width),
                    range.element_width,
                );
                for field in layout.fields().values() {
                    memory = visit_struct_field_cells(
                        field,
                        &element_pointer,
                        memory,
                        |memory, pointer, element_type| {
                            if !seeds_symbolic_field_cell(element_type)
                                || matches!(memory.load(&pointer), ExpressionOutcome::Value(_))
                            {
                                return memory;
                            }
                            // A value of an abstract type is a cell of its
                            // own, seeded as a field owned alone is.
                            if let ProgramType::Parameter(_) = element_type {
                                return memory.with_seeded_cells(
                                    pointer,
                                    crate::kernel::ABSTRACT_VALUE_WIDTH,
                                    element_type,
                                    0,
                                    1,
                                    crate::kernel::intern_memory(base_memory.clone()),
                                );
                            }
                            memory.materialize_cell_from_source(
                                pointer,
                                element_type,
                                crate::kernel::intern_memory(base_memory.clone()),
                            )
                        },
                    );
                }
                offset += range.element_width;
            }
            continue;
        }

        let Some(element_type) = range.element_type else {
            continue;
        };
        // Every whole element of the range, as one run: the cells it holds
        // are exactly the typed source loads seeded in element
        // order, skipping elements that already hold a cell, at a cost that
        // does not depend on how many elements there are.
        let count = range.bytes.checked_div(range.element_width).unwrap_or(0);
        memory = memory.with_seeded_cells(
            range.base.clone(),
            range.element_width,
            element_type,
            0,
            count,
            crate::kernel::intern_memory(base_memory.clone()),
        );
    }
    memory
}

pub(in crate::surface) fn visit_struct_field_cells(
    field: &crate::languages::interface::RecordField,
    element_pointer: &Address,
    mut memory: SymbolicMemory,
    mut visit: impl FnMut(SymbolicMemory, Address, ProgramType) -> SymbolicMemory,
) -> SymbolicMemory {
    let field_pointer = element_pointer.offset_by_bytes(field.offset_bytes());
    let field_type = field.interface_type().to_kernel_type();
    let Some((element_type, length)) = array_field_elements(field_type) else {
        return visit(memory, field_pointer, field_type);
    };
    for index in 0..length {
        memory = visit(
            memory,
            field_pointer.offset_by_bytes(
                index
                    .checked_mul(element_type.byte_width())
                    .expect("validated array field stride must fit in the pointer offset"),
            ),
            element_type,
        );
    }
    memory
}

/// The element type and length of an array field, whose cells are its
/// elements.
pub(super) fn array_field_elements(field_type: ProgramType) -> Option<(ProgramType, u32)> {
    Some(match field_type {
        ProgramType::Int8Array(length) => (ProgramType::Int8, length),
        ProgramType::UInt8Array(length) => (ProgramType::UInt8, length),
        ProgramType::Int16Array(length) => (ProgramType::Int16, length),
        ProgramType::UInt16Array(length) => (ProgramType::UInt16, length),
        ProgramType::Int32Array(length) => (ProgramType::Int32, length),
        ProgramType::UInt32Array(length) => (ProgramType::UInt32, length),
        ProgramType::Int64Array(length) => (ProgramType::Int64, length),
        ProgramType::UInt64Array(length) => (ProgramType::UInt64, length),
        ProgramType::Int128Array(length) => (ProgramType::Int128, length),
        ProgramType::UInt128Array(length) => (ProgramType::UInt128, length),
        ProgramType::Float32Array(length) => (ProgramType::Float32, length),
        ProgramType::Float64Array(length) => (ProgramType::Float64, length),
        ProgramType::PointerArray(element, length) => (element.pointer_type(), length),
        _ => return None,
    })
}

/// Whether a field cell of `element_type` has a symbolic seeded value. A
/// `void *` cell has none: its pointee has no width to scale the loaded
/// value by, and the kernel's symbolic loads do not model one, so the cell
/// stays unseeded, as static-storage seeding leaves it.
fn seeds_symbolic_field_cell(element_type: ProgramType) -> bool {
    element_type != ProgramType::VoidPointer
}

fn materialize_symbolic_access_resource_cells(
    mut memory: SymbolicMemory,
    state: &ExecutionState,
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
) -> Result<SymbolicMemory, ClickError> {
    // A segment based at a static pointer reads it before seeding the cells
    // it points at; keep that read so a later read of the pointer is the
    // same value rather than a question of whether those cells alias it.
    let seed = |memory: SymbolicMemory, segment: &ContractSegment| {
        let memory = match &segment.base {
            ProgramExpression::Variable(name) => {
                crate::kernel::with_static_pointer_read_cached(state, memory, name)
            }
            _ => memory,
        };
        materialize_access_segment_cells(memory, segment, parameter_binding)
    };
    for requirement in requires {
        let Requirement::Resource(resource) = requirement else {
            continue;
        };
        match resource {
            ResourceClause::Conditional { .. } => {
                return Err(ClickError::new(
                    "conditional resource assertions are supported only in loop contracts",
                ));
            }
            ResourceClause::Named { .. } => {}
            ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
                if !segment.is_uninitialized() {
                    memory = seed(memory, segment)?;
                }
            }
            ResourceClause::MemoryAggregate { segments, .. } => {
                for segment in segments
                    .iter()
                    .filter(|segment| !segment.is_uninitialized())
                {
                    memory = seed(memory, segment)?;
                }
            }
            ResourceClause::Declared { .. }
            | ResourceClause::Quantified { .. }
            | ResourceClause::Iterated(_) => {}
        }
    }
    Ok(memory)
}

/// `owns uninitialized(p[a..b])` holds bytes the caller makes no claim to have
/// initialized, so the proof starts with them unwritten: a read needs a store
/// or `defined` evidence first, as for a fresh local.
fn mark_uninitialized_resource_memory(
    mut memory: SymbolicMemory,
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
) -> Result<SymbolicMemory, ClickError> {
    for requirement in requires {
        let Requirement::Resource(resource) = requirement else {
            continue;
        };
        let segments = match resource {
            ResourceClause::OwnMemory(segment) => std::slice::from_ref(segment),
            ResourceClause::MemoryAggregate { segments, .. } => segments,
            _ => continue,
        };
        for segment in segments.iter().filter(|segment| segment.is_uninitialized()) {
            let state = ExecutionState::new().with_memory(memory.clone());
            let element_width =
                contract_segment_element_width(parameter_binding.parameters, segment);
            let (start, span) =
                match evaluate_requirement_segment(parameter_binding, &state, segment) {
                    Ok(evaluated) => {
                        let span = match (&evaluated.start, &evaluated.end) {
                            (bits32_constant!(start), bits32_constant!(end)) => {
                                if constant_u32(*end) <= constant_u32(*start) {
                                    continue;
                                }
                                (constant_u32(*end) - constant_u32(*start))
                                    .checked_mul(element_width)
                                    .ok_or_else(|| {
                                        ClickError::new(
                                            "`uninitialized` segment overflows byte count",
                                        )
                                    })?
                            }
                            _ => SymbolicMemory::UNBOUNDED_UNWRITTEN_SPAN,
                        };
                        let start = offset_pointer_by_elements(
                            evaluated.base,
                            evaluated.start,
                            element_width,
                        );
                        (start, span)
                    }
                    // Wide bounds, such as `buffer[0..size]` with a `uint64`
                    // size: mark from the base, which covers the segment.
                    Err(_) => {
                        let base =
                            evaluate_requirement_segment_base(parameter_binding, &state, segment)
                                .map_err(|message| {
                                ClickError::new(format!(
                                    "could not lower `{}`: {message}",
                                    crate::surface::diagnostics::describe_contract_segment(segment)
                                ))
                            })?;
                        (base, SymbolicMemory::UNBOUNDED_UNWRITTEN_SPAN)
                    }
                };
            memory = memory.with_uninitialized_object(start, span);
        }
    }
    Ok(memory)
}

/// Refuses a resource clause whose segment is addressed through a cell the
/// contract does not hold. `views old->left->augmented` reads the parameter
/// cell `old->left` to name its segment, so the entry state must justify
/// that read exactly as it justifies a `requires old->left != 0` reading
/// the same cell. Without this check a clause could address memory through
/// an arbitrary parameter link while a requirement naming the same link was
/// refused, which is how adding a guard to a contract used to make it fail.
///
/// The entry state already carries what every clause of the section supplies,
/// including the cells a folded composite holds, so this decides the whole
/// clause set at once and clause order does not enter into it. That is the
/// same question the kernel's section evaluator answers when it cannot read a
/// clause's base at all, so a refusal here identifies the clause -- or the
/// clauses that stall together -- in the kernel's wording
/// (`resource_clause_position_note`, `resource_clause_stall_note`) rather
/// than inventing a second one for one defect.
pub(in crate::surface) fn check_resource_segment_base_loadability(
    function_block: &FunctionBlock,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Result<(), ClickError> {
    let clauses = function_block
        .requires()
        .iter()
        .filter_map(|requirement| match requirement {
            Requirement::Resource(resource) => Some(resource),
            _ => None,
        })
        .collect::<Vec<_>>();
    // Positions are the clauses the author wrote: a flattened aggregate's
    // members share one, the same numbering the kernel evaluator carries.
    let positions = function_block.resource_requirement_positions();
    let clause_count = positions.first().map_or(clauses.len(), |(_, count)| *count);
    let mut stalled = Vec::new();
    for (flattened, resource) in clauses.iter().enumerate() {
        let position = positions
            .get(flattened)
            .map_or(flattened, |(position, _)| *position);
        if stalled
            .iter()
            .any(|(seen, _, _): &(usize, String, String)| *seen == position)
        {
            continue;
        }
        let segments: &[ContractSegment] = match resource {
            ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
                std::slice::from_ref(segment)
            }
            ResourceClause::MemoryAggregate { segments, .. } => segments,
            ResourceClause::Named { .. }
            | ResourceClause::Conditional { .. }
            | ResourceClause::Declared { .. }
            | ResourceClause::Quantified { .. }
            | ResourceClause::Iterated(_) => continue,
        };
        for segment in segments {
            let Err(message) = check_segment_base_loadability(
                &segment.base,
                parameter_binding,
                state,
                assumptions,
            ) else {
                continue;
            };
            stalled.push((
                position,
                crate::surface::diagnostics::describe_contract_segment(segment),
                message,
            ));
            break;
        }
    }
    let Some((position, segment, message)) = stalled.first() else {
        return Ok(());
    };
    // One unaddressed clause is that clause's own problem. Two or more stall
    // together: no order of them supplies what they read, so name a second
    // position instead of sending the user to whichever was written first.
    let note = match stalled.get(1) {
        Some((other, _, _)) => crate::kernel::resource_clause_stall_note(*position, *other),
        None => crate::kernel::resource_clause_position_note(*position, clause_count),
    };
    Err(ClickError::new(format!(
        "could not address resource clause `{segment}` ({note}): {message}"
    )))
}

/// Checks the loads a segment base performs, innermost first, so a chain
/// such as `old->left->augmented` reports the first cell the contract does
/// not hold rather than the last.
fn check_segment_base_loadability(
    base: &ProgramExpression,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Result<(), String> {
    let ProgramExpression::TypedLoad {
        pointer,
        value_type,
        ..
    } = base
    else {
        return Ok(());
    };
    check_segment_base_loadability(pointer, parameter_binding, state, assumptions)?;
    // An inline array field is addressed by a typed load of the array
    // itself. That reads no cell: the elements are the struct's own storage,
    // and the segment covers them directly.
    if matches!(
        value_type,
        ProgramType::Int32Array(_)
            | ProgramType::UInt8Array(_)
            | ProgramType::Int8Array(_)
            | ProgramType::Int16Array(_)
            | ProgramType::UInt16Array(_)
            | ProgramType::UInt32Array(_)
            | ProgramType::Int128Array(_)
            | ProgramType::Int64Array(_)
            | ProgramType::UInt128Array(_)
            | ProgramType::UInt64Array(_)
            | ProgramType::Float32Array(_)
            | ProgramType::Float64Array(_)
    ) {
        return Ok(());
    }
    let Ok(values) = parameter_values(parameter_binding) else {
        return Ok(());
    };
    let array_refs = array_refs_for_parameters(
        parameter_binding.parameters,
        &values,
        &state.program_point(),
    );
    // The address of the cell, not its content: a base whose address this
    // entry cannot evaluate is reported by the clause's own lowering.
    let Ok(ProgramValue::Pointer(cell)) =
        crate::surface::proof::evaluate_program_expression_through_kernel(
            pointer,
            assumptions,
            ContractEnvironment::new(&values, &array_refs).with_parameters(parameter_binding),
            state,
            None,
        )
    else {
        return Ok(());
    };
    let obligation = Proposition::MemoryLoadable {
        memory: state.memory().clone(),
        base: cell.into_pointer(),
        bytes: (MachineTerm::constant(value_type.byte_width())).into(),
        wide: false,
    };
    if crate::kernel::execution_state_justifies_loadability_obligation(
        state,
        &obligation,
        assumptions,
    ) {
        return Ok(());
    }
    Err(format!(
        "{}{}",
        crate::surface::diagnostics::describe_missing_pure_fact(
            &obligation,
            &[],
            &[],
            parameter_binding,
            &[],
        ),
        folded_matched_instance_note(state, parameter_binding, assumptions)
    ))
}

/// Says why the cells a folded matched instance owns are unreadable here.
///
/// A resource whose body is `match model { ... }` exposes nothing until one
/// arm is selected, so a requirement or a resource clause that reads through
/// it fails for a loadability that names no resource at all. Name the instance
/// and the evidence that would select an arm, rather than leaving the reader
/// with an unexplained missing fact.
///
/// The note costs the contract's own resource clauses, never the project: it
/// reads the clause set this entry state already holds.
pub(in crate::surface) fn folded_matched_instance_note(
    state: &ExecutionState,
    parameter_binding: ParameterBinding<'_>,
    assumptions: &PureFactContext,
) -> String {
    // Only an instance whose arm nothing selects explains a missing cell. One
    // whose arm is selected already published its cells, so naming it here
    // would send the reader to a clause that is fine.
    fn undecided<'a>(
        instance: &'a crate::kernel::ResourceInstance,
        assumptions: &PureFactContext,
    ) -> Option<(&'a str, Vec<String>)> {
        instance
            .schema()
            .fields()
            .iter()
            .zip(instance.fields())
            .filter_map(|((name, _), value)| match value {
                crate::kernel::ResourceFieldValue::Algebraic(model) => Some((name.as_str(), model)),
                _ => None,
            })
            .find_map(|(name, model)| {
                let possible = match crate::kernel::decide_resource_model_arm(model, assumptions) {
                    crate::kernel::ResourceModelArmDecision::Selected(_) => return None,
                    crate::kernel::ResourceModelArmDecision::Possible(possible) => possible,
                    crate::kernel::ResourceModelArmDecision::Open => Vec::new(),
                };
                let possible = possible
                    .iter()
                    .map(|variant| format!("{}::{variant}", model.algebraic_type.name))
                    .collect::<Vec<_>>();
                Some((name, possible))
            })
    }
    let Some((instance, field, possible)) = state
        .resources()
        .facts()
        .iter()
        .filter_map(|fact| match fact.resource() {
            Resource::Instance(instance) => Some(instance),
            _ => None,
        })
        .find_map(|instance| {
            undecided(instance, assumptions).map(|(field, possible)| (instance, field, possible))
        })
    else {
        return String::new();
    };
    let declared = crate::surface::proof_diagnostics::render::render_resource_diagnostic(
        &Resource::Instance(instance.clone()),
        parameter_binding,
    );
    // The premises may have refuted some arms without deciding one. Then the
    // cells every surviving arm owns are readable and this cell is not one of
    // them, so name the arms the reader has to reconcile rather than repeating
    // that no arm is selected.
    if possible.len() > 1 {
        return format!(
            "\n  `{declared}` stays folded: the requirements leave the arms {} possible, and this \
             cell is not owned by every one of them, so it is not readable here",
            possible
                .iter()
                .map(|variant| format!("`{variant}`"))
                .collect::<Vec<_>>()
                .join(" and ")
        );
    }
    format!(
        "\n  `{declared}` stays folded: no requirement of this contract selects one arm of its \
         `{field}` field, so the cells its arms own are not readable here",
    )
}

fn materialize_access_segment_cells(
    mut memory: SymbolicMemory,
    segment: &ContractSegment,
    parameter_binding: ParameterBinding<'_>,
) -> Result<SymbolicMemory, ClickError> {
    let state = ExecutionState::new().with_memory(memory.clone());
    let source_segment = segment;
    let Ok(segment) = evaluate_requirement_segment(parameter_binding, &state, source_segment)
    else {
        return Ok(memory);
    };
    let (int32_constant!(start), bits32_constant!(end)) = (&segment.start, &segment.end) else {
        return Ok(memory);
    };
    if constant_u32(*end) < constant_u32(*start) {
        return Err(ClickError::new(format!(
            "resource segment has an end before its start: {start}..{end}",
            start = constant_u32(*start),
            end = constant_u32(*end)
        )));
    }

    // A complete object (`*p`) is one struct at the base: its cells
    // take the field types of the layout, so a `uint64` or pointer field
    // reads back with its own type rather than as int32 words.
    if let Some(layout) = object_segment_layout(parameter_binding.parameters, source_segment) {
        let base_memory = memory.clone();
        for field in layout.fields().values() {
            memory = visit_struct_field_cells(
                field,
                &segment.base,
                memory,
                |memory, pointer, element_type| {
                    if !seeds_symbolic_field_cell(element_type)
                        || matches!(memory.load(&pointer), ExpressionOutcome::Value(_))
                    {
                        return memory;
                    }
                    memory.materialize_cell_from_source(
                        pointer,
                        element_type,
                        crate::kernel::intern_memory(base_memory.clone()),
                    )
                },
            );
        }
        return Ok(memory);
    }
    if let Some(layout) =
        contract_segment_struct_layout(parameter_binding.parameters, source_segment)
    {
        let base_memory = memory.clone();
        for index in constant_u32(*start)..constant_u32(*end) {
            let element_pointer = offset_pointer_by_elements(
                segment.base.clone(),
                MachineTerm::constant(index),
                layout.size_bytes(),
            );
            for field in layout.fields().values() {
                memory = visit_struct_field_cells(
                    field,
                    &element_pointer,
                    memory,
                    |memory, pointer, element_type| {
                        if !seeds_symbolic_field_cell(element_type)
                            || matches!(memory.load(&pointer), ExpressionOutcome::Value(_))
                        {
                            return memory;
                        }
                        memory.materialize_cell_from_source(
                            pointer,
                            element_type,
                            crate::kernel::intern_memory(base_memory.clone()),
                        )
                    },
                );
            }
        }
        return Ok(memory);
    }

    let element_type = contract_segment_element_type(parameter_binding.parameters, &segment.source);
    let mut element_width =
        contract_segment_element_width(parameter_binding.parameters, &segment.source);
    let (mut start, mut end) = (constant_u32(*start), constant_u32(*end));
    // A typed element wider than the segment's stride is one cell of its
    // own width (see `ConcreteMemoryRangeSeed::with_element_cells`).
    let width = element_type.byte_width();
    if width > element_width
        && width != 0
        && (start * element_width).is_multiple_of(width)
        && (end * element_width).is_multiple_of(width)
    {
        start = start * element_width / width;
        end = end * element_width / width;
        element_width = width;
    }
    let source = crate::kernel::intern_memory(memory.clone());
    // One run for the segment's elements, spelled from the segment's own
    // base as each element's pointer is (see `memory_with_symbolic_loadable_cells`).
    Ok(memory.with_seeded_cells(
        segment.base.clone(),
        element_width,
        element_type,
        start,
        end,
        source,
    ))
}

pub(in crate::surface) fn requirement_propositions(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Vec<Proposition>, ClickError> {
    requirement_propositions_with_assumptions(
        requires,
        parameter_binding,
        state,
        spec_definitions,
        &PureFactContext::new(),
    )
}

pub(in crate::surface) fn requirement_propositions_with_assumptions(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
    initial_assumptions: &PureFactContext,
) -> Result<Vec<Proposition>, ClickError> {
    Ok(requirement_propositions_with_sources_and_assumptions(
        requires,
        parameter_binding,
        state,
        spec_definitions,
        initial_assumptions,
    )?
    .into_iter()
    .map(|fact| fact.proposition)
    .collect())
}

/// One fact emitted while lowering the function's written requirement list.
///
/// This is a construction-time record, before later entry-context passes
/// add resource observations or definedness consequences.  Keeping the outer
/// source ordinal here avoids trying to reconstruct it from the final fact
/// vector, whose ordering deliberately differs from requirement order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub(in crate::surface) struct LoweredRequirementFact {
    pub(in crate::surface) source_ordinal: usize,
    pub(in crate::surface) role: LoweredRequirementFactRole,
    pub(in crate::surface) proposition: Proposition,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(in crate::surface) enum LoweredRequirementFactRole {
    Principal,
    Guard(usize),
}

pub(in crate::surface) fn requirement_propositions_with_sources_and_assumptions(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
    initial_assumptions: &PureFactContext,
) -> Result<Vec<LoweredRequirementFact>, ClickError> {
    requirement_propositions_sharing_lowering_state(
        requires,
        parameter_binding,
        state,
        spec_definitions,
        initial_assumptions,
        &RequirementLoweringState::default(),
    )
}

/// The state proposition requirements are lowered at
/// (`requirement_lowering_state`), built on first use. Every requirement
/// lowered at one entry state with one parameter binding lowers at the same
/// state, so a caller lowering them one list at a time shares one.
#[derive(Default)]
pub(in crate::surface) struct RequirementLoweringState(
    std::cell::OnceCell<Result<ExecutionState, String>>,
);

pub(in crate::surface) fn requirement_propositions_sharing_lowering_state(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
    initial_assumptions: &PureFactContext,
    lowering_state: &RequirementLoweringState,
) -> Result<Vec<LoweredRequirementFact>, ClickError> {
    // A proposition requirement may contain a memory read whose range is
    // justified by another requirement, such as `1 <= n` before
    // `a[0] == 7` under `views a[0..n]`. Lower requirements independently
    // used to make this valid dependency invisible. Retry clauses that need
    // more facts after successfully lowered clauses have contributed their
    // propositions to the local assumption context. Keeping the result in
    // source order preserves the contract-to-kernel mapping.
    let mut lowered = (0..requires.len())
        .map(|_| None)
        .collect::<Vec<Option<Vec<Proposition>>>>();
    let mut errors = (0..requires.len())
        .map(|_| None)
        .collect::<Vec<Option<ClickError>>>();
    let mut pending = (0..requires.len()).collect::<Vec<_>>();
    // These are the function's own entry requirements: a member selected
    // through a pointer argument was checked by the caller, so it is
    // assumed and recorded (`PureFactContext::assume_entry_clause_spans`).
    let mut assumptions = initial_assumptions.clone().assume_entry_clause_spans();

    // Requirements may be written in either order, so use one retry pass
    // after the first pass has published the facts it could lower. A bounded
    // retry keeps setup work linear in the explicit requirement list rather
    // than turning a long dependency chain into repeated whole-list scans.
    for _ in 0..2 {
        if pending.is_empty() {
            break;
        }
        let mut next_pending = Vec::new();
        let mut made_progress = false;
        for index in std::mem::take(&mut pending) {
            let requirement = &requires[index];
            let result = match requirement {
                Requirement::LoadableSegment { .. } => loadable_requirement_props(
                    requirement,
                    parameter_binding,
                    state.memory(),
                    &assumptions,
                )
                .map(Some),
                Requirement::Proposition(proposition) => lowering_state
                    .0
                    .get_or_init(|| {
                        requirement_lowering_state(parameter_binding, state)
                            .map_err(|error| error.message().to_string())
                    })
                    .as_ref()
                    .map_err(|message| ClickError::new(message.clone()))
                    .and_then(|lowering_state| {
                        requirement_proposition_and_facts_with_assumptions(
                            parameter_binding,
                            state,
                            lowering_state,
                            proposition,
                            spec_definitions,
                            &assumptions,
                        )
                    })
                    .map(|(proposition, facts)| {
                        Some(std::iter::once(proposition).chain(facts).collect())
                    }),
                Requirement::Resource(resource) => resource_clause_loadable_props_at_state(
                    resource,
                    parameter_binding,
                    state,
                    &assumptions,
                ),
            };
            let result = match result {
                Ok(Some(propositions)) => Ok(propositions),
                Ok(None) => continue,
                Err(error) => Err(error),
            };
            match result {
                Ok(propositions) => {
                    for proposition in &propositions {
                        assumptions = assumptions.assume_proposition(proposition.clone());
                    }
                    lowered[index] = Some(propositions);
                    made_progress = true;
                }
                Err(error) => {
                    errors[index] = Some(error);
                    next_pending.push(index);
                }
            }
        }
        if !made_progress {
            if next_pending.is_empty() {
                break;
            }
            pending = next_pending;
            break;
        }
        pending = next_pending;
    }

    if let Some(index) = pending.first() {
        return Err(errors[*index]
            .take()
            .expect("pending requirement always has a lowering error"));
    }

    let mut facts = Vec::new();
    let mut guards = Vec::new();
    for (source_ordinal, propositions) in lowered.into_iter().enumerate() {
        let Some(propositions) = propositions else {
            continue;
        };
        let mut propositions = propositions.into_iter();
        if let Some(fact) = propositions.next() {
            facts.push(LoweredRequirementFact {
                source_ordinal,
                role: LoweredRequirementFactRole::Principal,
                proposition: fact,
            });
        }
        guards.extend(
            propositions
                .enumerate()
                .map(|(guard_ordinal, proposition)| LoweredRequirementFact {
                    source_ordinal,
                    role: LoweredRequirementFactRole::Guard(guard_ordinal),
                    proposition,
                }),
        );
    }
    facts.extend(guards);
    Ok(facts)
}

/// Checked definedness facts implicit in accepting arithmetic requirements.
///
/// Evaluating a C comparison containing partial arithmetic first establishes
/// that arithmetic's evaluator guards. Record those guards explicitly so a
/// later call certificate can name the exact fact it consumed instead of
/// asking a simple statement step to repeat arithmetic reasoning.
pub(in crate::surface) fn requirement_definedness_surfaces(
    requires: &[Requirement],
) -> Vec<ClickProposition> {
    fn contains_partial_arithmetic(expression: &ContractExpression) -> bool {
        match expression {
            ContractExpression::Add(_, _)
            | ContractExpression::Subtract(_, _)
            | ContractExpression::Multiply(_, _)
            | ContractExpression::Divide(_, _)
            | ContractExpression::Remainder(_, _)
            | ContractExpression::ShiftLeft(_, _)
            | ContractExpression::RustShiftLeft(_, _)
            | ContractExpression::ShiftRight(_, _)
            | ContractExpression::RustShiftRight(_, _) => true,
            ContractExpression::BitwiseAnd(left, right)
            | ContractExpression::BitwiseOr(left, right)
            | ContractExpression::BitwiseXor(left, right) => {
                contains_partial_arithmetic(left) || contains_partial_arithmetic(right)
            }
            ContractExpression::BitwiseNot(body) => contains_partial_arithmetic(body),
            _ => false,
        }
    }

    fn collect<'a>(
        proposition: &'a ClickProposition,
        expressions: &mut Vec<&'a ContractExpression>,
    ) {
        match proposition {
            ClickProposition::Value(expression) => {
                if let ContractExpression::Proposition(body) = expression {
                    collect(body, expressions);
                }
            }
            ClickProposition::Comparison { left, right, .. } => {
                if contains_partial_arithmetic(left) {
                    expressions.push(left);
                }
                if contains_partial_arithmetic(right) {
                    expressions.push(right);
                }
            }
            ClickProposition::FloatClassification { expression, .. } => {
                if contains_partial_arithmetic(expression) {
                    expressions.push(expression);
                }
            }
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                collect(left, expressions);
                collect(right, expressions);
            }
            ClickProposition::Not(body) => collect(body, expressions),
            // Bound-variable definedness must remain under its quantifier.
            ClickProposition::ForAll { .. }
            | ClickProposition::Exists { .. }
            | ClickProposition::RangeAll { .. }
            | ClickProposition::RangeAny { .. }
            | ClickProposition::Separate { .. }
            | ClickProposition::ResourceViewable { .. }
            | ClickProposition::Contains { .. }
            | ClickProposition::Loadable { .. }
            | ClickProposition::Defined { .. }
            | ClickProposition::At { .. }
            | ClickProposition::PredicateCall { .. } => {}
        }
    }

    let mut result = Vec::new();
    for requirement in requires {
        let Requirement::Proposition(proposition) = requirement else {
            continue;
        };
        let mut expressions = Vec::new();
        collect(proposition, &mut expressions);
        for expression in expressions {
            if contract_expression_to_program_expression(expression).is_none() {
                continue;
            }
            let surface = ClickProposition::Defined {
                expression: expression.clone(),
            };
            if !result.contains(&surface) {
                result.push(surface);
            }
        }
    }
    result
}

pub(in crate::surface) fn requirement_definedness_propositions(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Vec<(ClickProposition, Proposition)>, ClickError> {
    let mut result = Vec::new();
    for surface in requirement_definedness_surfaces(requires) {
        let kernel =
            requirement_proposition_prop(parameter_binding, state, &surface, spec_definitions)?;
        if matches!(normalize_proposition(&kernel), NormalizedProposition::True)
            || result
                .iter()
                .any(|(_, fact): &(ClickProposition, Proposition)| fact == &kernel)
        {
            continue;
        }
        result.push((surface, kernel));
    }
    Ok(result)
}

pub(in crate::surface) fn resource_context_from_requirements(
    requires: &[Requirement],
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    base_assumptions: &PureFactContext,
) -> Result<ResourceContext, ClickError> {
    let mut context = state.resources().clone();
    // One section-local state, moved forward after each owning requirement.
    // Later references can select earlier binders without cloning the state
    // for every clause or introducing ownership beyond these requirements.
    let mut lowering_state = state.clone();
    // Moving the state forward changes only its resources, so every clause
    // reads the same parameter values and array references.
    let values =
        parameter_values(parameter_binding).map_err(|error| ClickError::new(error.message))?;
    let clause_parameters = ClauseParameters::new(parameter_binding.parameters, &values, state)
        .with_index(parameter_binding.index);
    for requirement in requires {
        if let Requirement::Resource(resource) = requirement {
            // This builds a provisional context under declared entry premises.
            // Resource arguments may contain
            // loads whose authority is supplied by another clause, so keep
            // those arguments symbolic here.  The entry context is checked by
            // the kernel section evaluator once all pure requirements and
            // clause supplies are available.
            context = context.unchecked_with_facts(
                lower_resource_clause_facts_with_values_mode_at_entry(
                    resource,
                    &clause_parameters,
                    &lowering_state,
                    &lowering_state,
                    None,
                    true,
                    base_assumptions,
                )?,
            );
            lowering_state = lowering_state.with_resource_context(context.clone());
        }
    }
    Ok(context)
}

#[cfg(test)]
pub(in crate::surface) fn lower_resource_clause(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    memory: &SymbolicMemory,
) -> Result<ResourceFact, ClickError> {
    if matches!(resource, ResourceClause::MemoryAggregate { .. }) {
        let mut facts = lower_resource_clause_facts(resource, parameter_binding, memory)?;
        if facts.len() != 1 {
            return Err(ClickError::new(format!(
                "resource clause expands to {} typed memory facts where one fact is required",
                facts.len()
            )));
        }
        return Ok(facts.pop().expect("resource clause fact count was checked"));
    }
    let values = resource_clause_parameter_values(resource, parameter_binding)?;
    let state = ExecutionState::new().with_memory(memory.clone());
    lower_resource_clause_with_values(resource, parameter_binding, &values, &state, None)
}

#[cfg(test)]
pub(in crate::surface) fn lower_resource_clause_facts(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    memory: &SymbolicMemory,
) -> Result<Vec<ResourceFact>, ClickError> {
    let values = resource_clause_parameter_values(resource, parameter_binding)?;
    let state = ExecutionState::new().with_memory(memory.clone());
    lower_resource_clause_facts_with_values(resource, parameter_binding, &values, &state, None)
}

pub(in crate::surface) fn lower_resource_clause_at_state(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Result<ResourceFact, ClickError> {
    if matches!(resource, ResourceClause::MemoryAggregate { .. }) {
        let mut facts = lower_resource_clause_facts_at_state(resource, parameter_binding, state)?;
        if facts.len() != 1 {
            return Err(ClickError::new(format!(
                "resource clause expands to {} typed memory facts where one fact is required",
                facts.len()
            )));
        }
        return Ok(facts.pop().expect("resource clause fact count was checked"));
    }
    let values = resource_clause_parameter_values(resource, parameter_binding)?;
    lower_resource_clause_with_values(resource, parameter_binding, &values, state, None)
}

pub(in crate::surface) fn lower_resource_clause_facts_at_state(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Result<Vec<ResourceFact>, ClickError> {
    let values = resource_clause_parameter_values(resource, parameter_binding)?;
    lower_resource_clause_facts_with_values(resource, parameter_binding, &values, state, None)
}

pub(in crate::surface) fn lower_resource_clause_at_state_with_result(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    result: &ProgramValue,
) -> Result<ResourceFact, ClickError> {
    lower_resource_clause_at_state_with_assumptions(
        resource,
        parameter_binding,
        state,
        Some(result),
        &PureFactContext::new(),
    )
}

/// Lowers a live proof operation's resource clause under its checked context.
/// Retain the persistent assumption handle, including its trusted equality
/// graph; do not reconstruct facts or publish ambient resources at this query.
pub(in crate::surface) fn lower_resource_clause_at_state_with_assumptions(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
    assumptions: &PureFactContext,
) -> Result<ResourceFact, ClickError> {
    let values = resource_clause_parameter_values(resource, parameter_binding)?;
    if matches!(resource, ResourceClause::MemoryAggregate { .. }) {
        let mut facts = lower_resource_clause_facts_with_values_mode_at_entry(
            resource,
            &ClauseParameters::new(parameter_binding.parameters, &values, state)
                .with_index(parameter_binding.index),
            state,
            state,
            result,
            false,
            assumptions,
        )?;
        if facts.len() != 1 {
            return Err(ClickError::new(format!(
                "resource clause expands to {} typed memory facts where one fact is required",
                facts.len()
            )));
        }
        return Ok(facts.pop().expect("resource clause fact count was checked"));
    }
    lower_resource_clause_with_values_mode_at_entry(
        resource,
        &ClauseParameters::new(parameter_binding.parameters, &values, state)
            .with_index(parameter_binding.index),
        state,
        state,
        result,
        false,
        assumptions,
    )
}

/// Lower a join interface at the current C bindings, under the proof's facts.
/// Its parameter names denote their current values, just as in `fold`.
pub(in crate::surface) fn lower_interface_resource_clause(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Result<ResourceFact, ClickError> {
    lower_resource_clause_at_current_locals_with_assumptions(
        resource,
        parameter_binding,
        state,
        None,
        assumptions,
    )
}

/// Lower a proof resource argument at the current C bindings, retaining only
/// the facts already checked at this frontier. These facts can identify an
/// owned cell through an alias; they do not assume the proposed fold's body.
pub(in crate::surface) fn lower_resource_clause_at_current_locals_with_assumptions(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
    assumptions: &PureFactContext,
) -> Result<ResourceFact, ClickError> {
    lower_resource_clause_at_current_locals_with_entry_and_assumptions(
        resource,
        parameter_binding,
        state,
        state,
        result,
        assumptions,
    )
}

/// Explicit state arguments keep their function-entry state while ordinary
/// arguments use the current C bindings. Both states reach the existing typed
/// resource-argument evaluator; no argument is rewritten to a different cursor.
pub(in crate::surface) fn lower_resource_clause_at_current_locals_with_entry_and_assumptions(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    entry_state: &ExecutionState,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
    assumptions: &PureFactContext,
) -> Result<ResourceFact, ClickError> {
    let values = resource_clause_parameter_values(resource, parameter_binding)?;
    let array_refs = array_refs_for_values(parameter_binding, &values, &state.program_point());
    let (values, _) = contract_environment_at_state(&values, &array_refs, state);
    if matches!(resource, ResourceClause::MemoryAggregate { .. }) {
        let mut facts = lower_resource_clause_facts_with_values_mode_at_entry(
            resource,
            &ClauseParameters::new(parameter_binding.parameters, &values, state)
                .with_index(parameter_binding.index),
            entry_state,
            state,
            result,
            false,
            assumptions,
        )?;
        if facts.len() != 1 {
            return Err(ClickError::new(format!(
                "resource clause expands to {} typed memory facts where one fact is required",
                facts.len()
            )));
        }
        return Ok(facts.pop().expect("resource clause fact count was checked"));
    }
    lower_resource_clause_with_values_mode_at_entry(
        resource,
        &ClauseParameters::new(parameter_binding.parameters, &values, state)
            .with_index(parameter_binding.index),
        entry_state,
        state,
        result,
        false,
        assumptions,
    )
}

pub(in crate::surface) fn lower_resource_clause_facts_at_state_with_result_and_entry(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    entry_state: &ExecutionState,
    state: &ExecutionState,
    result: &ProgramValue,
    base_assumptions: &PureFactContext,
) -> Result<Vec<ResourceFact>, ClickError> {
    let values = resource_clause_parameter_values(resource, parameter_binding)?;
    lower_resource_clause_facts_with_values_mode_at_entry(
        resource,
        &ClauseParameters::new(parameter_binding.parameters, &values, state)
            .with_index(parameter_binding.index),
        entry_state,
        state,
        Some(result),
        false,
        base_assumptions,
    )
}

/// The parameters and argument values every resource clause lowered over one
/// memory reads, with the array references over that memory built on
/// first use. The clauses of one entry share it, so lowering each clause does
/// not rebuild a map over every parameter.
struct ClauseParameters<'a> {
    parameters: &'a [crate::languages::interface::ImportedParameter],
    values: &'a ProgramValueBindings,
    state: &'a ExecutionState,
    index: Option<&'a crate::surface::ParameterIndex>,
    array_refs: std::cell::OnceCell<ClickArrayRefs>,
}

impl<'a> ClauseParameters<'a> {
    fn new(
        parameters: &'a [crate::languages::interface::ImportedParameter],
        values: &'a ProgramValueBindings,
        state: &'a ExecutionState,
    ) -> Self {
        Self {
            parameters,
            values,
            state,
            index: None,
            array_refs: std::cell::OnceCell::new(),
        }
    }

    /// These parameters with the binding's index, so the array references
    /// cover only the parameters `values` binds.
    fn with_index(self, index: Option<&'a crate::surface::ParameterIndex>) -> Self {
        Self { index, ..self }
    }

    fn array_refs(&self) -> &ClickArrayRefs {
        self.array_refs.get_or_init(|| {
            let binding = ParameterBinding {
                parameters: self.parameters,
                arguments: &[],
                index: self.index,
                naming: None,
            };
            array_refs_for_values(binding, self.values, &self.state.program_point())
        })
    }
}

fn lower_resource_clause_with_values(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    values: &ProgramValueBindings,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
) -> Result<ResourceFact, ClickError> {
    lower_resource_clause_with_values_mode(
        resource,
        parameter_binding,
        values,
        state,
        result,
        false,
    )
}

fn lower_resource_clause_with_values_mode(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    values: &ProgramValueBindings,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
    allow_symbolic_resource_arguments: bool,
) -> Result<ResourceFact, ClickError> {
    let base_assumptions = PureFactContext::new();
    lower_resource_clause_with_values_mode_at_entry(
        resource,
        &ClauseParameters::new(parameter_binding.parameters, values, state)
            .with_index(parameter_binding.index),
        state,
        state,
        result,
        allow_symbolic_resource_arguments,
        &base_assumptions,
    )
}

fn lower_resource_clause_with_values_mode_at_entry(
    resource: &ResourceClause,
    clause_parameters: &ClauseParameters<'_>,
    entry_state: &ExecutionState,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
    allow_symbolic_resource_arguments: bool,
    base_assumptions: &PureFactContext,
) -> Result<ResourceFact, ClickError> {
    let (parameters, values) = (clause_parameters.parameters, clause_parameters.values);
    match resource {
        ResourceClause::Conditional { .. } => Err(ClickError::new(
            "conditional resource assertions require loop-contract lowering",
        )),
        ResourceClause::Named { binding, resource } => {
            let lowered = lower_resource_clause_with_values_mode_at_entry(
                resource,
                clause_parameters,
                entry_state,
                state,
                result,
                allow_symbolic_resource_arguments,
                base_assumptions,
            )?;
            if matches!(
                lowered.resource(),
                Resource::MutexGuard(_) | Resource::MutexLive(_) | Resource::MutexUse(_)
            ) {
                // This lowering constructs the independent precondition. The
                // kernel subsequently binds its name to the rooted occurrence.
                return Ok(lowered);
            }
            let ResourceFact::Own(Resource::Composite { name, arguments }, _) = lowered else {
                return Err(ClickError::new(
                    "named instance requires an owned resource definition",
                ));
            };
            let schema = binding
                .schema
                .clone()
                .ok_or_else(|| ClickError::new("resource instance has no checked schema"))?;
            // Ownership names select current fields, but the clause still
            // determines the required resource family, arguments, and schema.
            let fields = state
                .owned_resource_instance(binding.identity)
                .map(|instance| instance.fields().to_vec().into())
                .or_else(|| binding.fields.clone())
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "no `{}` instance is held under the name `{}`; name the instance a call \
                         produces with `let {{ binder: {} }} = step(callee, {{ ... }})`, or fold \
                         one under that name",
                        name, binding.name, binding.name
                    ))
                })?;
            let instance = crate::kernel::ResourceInstance::new_with_resource_arguments(
                binding.identity,
                name,
                arguments,
                schema,
                fields,
                lower_resource_reference_arguments(resource, state)?,
            )
            .ok_or_else(|| {
                ClickError::new("resource instance fields do not match the declared schema")
            })?;
            Ok(ResourceFact::own(Resource::Instance(instance)))
        }
        ResourceClause::MemoryAggregate { .. } => Err(ClickError::new(
            "aggregate resource clauses require batch lowering",
        )),
        ResourceClause::Iterated(clause) => {
            let assumptions = if allow_symbolic_resource_arguments {
                base_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads()
            } else {
                base_assumptions.clone()
            };
            lower_iterated_clause_with_values(
                clause,
                parameters,
                values,
                state,
                result,
                &assumptions,
            )
        }
        ResourceClause::Quantified { quantity, resource } => {
            let original_quantity = quantity.clone();
            let (quantity, quantity_state_source) =
                resource_argument_to_typed_program_expression_with_state(
                    quantity,
                    crate::languages::interface::InterfaceType::Int32,
                )?;
            let assumptions = if allow_symbolic_resource_arguments {
                base_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads()
            } else {
                base_assumptions.clone()
            };
            let array_refs = clause_parameters.array_refs();
            let quantity = evaluate_resource_argument_with_state(
                &original_quantity,
                &quantity,
                quantity_state_source,
                &assumptions,
                ContractEnvironment::new(values, array_refs),
                entry_state,
                state,
                result,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "could not lower declared resource quantity: {message}"
                ))
            })?;
            let ProgramValue::Int32(quantity) = quantity else {
                return Err(ClickError::new(
                    "declared resource quantity must evaluate to int32",
                ));
            };
            let lowered = lower_resource_clause_with_values_mode_at_entry(
                resource,
                clause_parameters,
                entry_state,
                state,
                result,
                allow_symbolic_resource_arguments,
                base_assumptions,
            )?;
            let ResourceFact::Own(resource, _) = lowered else {
                return Err(ClickError::new(
                    "declared resource quantity requires owned authority",
                ));
            };
            Ok(ResourceFact::own_quantity(resource, quantity))
        }
        ResourceClause::ViewMemory(segment) => {
            let range = lower_resource_segment_with_values(
                "read",
                segment,
                ContractEnvironment::new(values, clause_parameters.array_refs()),
                state,
                result,
                contract_segment_element_width_for_result_type(
                    parameters,
                    segment,
                    result.and_then(|value| match value {
                        ProgramValue::Pointer(pointer) => Some(pointer.program_type()),
                        _ => None,
                    }),
                ),
                base_assumptions,
            )?;
            Ok(ResourceFact::view_memory(range))
        }
        ResourceClause::OwnMemory(segment) => {
            let range = lower_resource_segment_with_values(
                "write",
                segment,
                ContractEnvironment::new(values, clause_parameters.array_refs()),
                state,
                result,
                contract_segment_element_width_for_result_type(
                    parameters,
                    segment,
                    result.and_then(|value| match value {
                        ProgramValue::Pointer(pointer) => Some(pointer.program_type()),
                        _ => None,
                    }),
                ),
                base_assumptions,
            )?;
            Ok(ResourceFact::own_memory(range))
        }
        ResourceClause::Declared {
            type_schema: _,
            resource_type_arguments,
            resource_arguments: _,
            access,
            kind,
            name,
            arguments: resource_arguments,
            parameter_types,
        } => {
            if !resource_type_arguments.is_empty()
                && (!matches!(
                    name.as_str(),
                    "mutex_use" | "authority" | "publisher" | "subscriber"
                ) || resource_type_arguments.len() != 1)
            {
                return Err(ClickError::new("unsupported resource type arguments"));
            }
            let assumptions = if allow_symbolic_resource_arguments {
                base_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads()
            } else {
                base_assumptions.clone()
            };
            let array_refs = clause_parameters.array_refs();
            let mut resource_values = Vec::new();
            if resource_arguments.len() != parameter_types.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` has malformed argument type metadata"
                )));
            }
            for (index, (argument, parameter_type)) in
                resource_arguments.iter().zip(parameter_types).enumerate()
            {
                let original_argument = argument.clone();
                let (argument, argument_state_source) =
                    resource_argument_to_typed_program_expression_with_state(
                        argument,
                        *parameter_type,
                    )?;
                let value = evaluate_resource_argument_with_state(
                    &original_argument,
                    &argument,
                    argument_state_source,
                    &assumptions,
                    ContractEnvironment::new(values, array_refs),
                    entry_state,
                    state,
                    result,
                )
                .map_err(|message| {
                    ClickError::new(format!(
                        "could not lower resource `{name}` argument {index}: {message}"
                    ))
                })?;
                let matches_type = if name == ResourceFact::ALLOCATION_RESOURCE_NAME && index == 0 {
                    program_value_matches_allocation_pointer(&value)
                } else if name == ResourceFact::ALLOCATION_RESOURCE_NAME && index == 1 {
                    program_value_matches_allocation_size(&value)
                } else {
                    program_value_matches_click_type(&value, *parameter_type)
                };
                if !matches_type {
                    let (naming_parameters, naming_arguments) =
                        crate::surface::diagnostics::value_naming_tables(values);
                    return Err(ClickError::new(format!(
                        "resource `{name}` argument {index} `{}` evaluated to `{}` of type `{}`, which does not match the parameter type `{}`",
                        crate::surface::diagnostics::describe_contract_expression(
                            &original_argument
                        ),
                        crate::surface::diagnostics::describe_program_value(
                            &value,
                            ParameterBinding::new(&naming_parameters, &naming_arguments)
                        ),
                        crate::kernel::program_type_spelling(value.program_type()),
                        crate::surface::validation::describe_interface_type(*parameter_type)
                    )));
                }
                resource_values
                    .push(value.resource_argument_at_type(parameter_type.to_kernel_type()));
            }
            if name == "mutex_guard" {
                let [ProgramValue::Pointer(mutex)] = resource_values.as_slice() else {
                    return Err(ClickError::new("mutex_guard expects one mutex pointer"));
                };
                let guard = crate::kernel::program_mutex_guard_resource(
                    state,
                    mutex.address(),
                    allow_symbolic_resource_arguments,
                )
                .ok_or_else(|| ClickError::new("mutex_guard requires a live acquisition"))?;
                return Ok(match access {
                    ResourceAccessMode::Own => guard,
                    ResourceAccessMode::View => ResourceFact::View(guard.resource().clone()),
                });
            }
            if name == "authority" {
                let [protected] = resource_type_arguments.as_slice() else {
                    return Err(ClickError::new(
                        "authority expects one checked resource type",
                    ));
                };
                let ResourceClause::Declared {
                    type_schema: Some(schema),
                    ..
                } = protected
                else {
                    return Err(ClickError::new(
                        "authority requires a checked resource type",
                    ));
                };
                let mut anchor_clause = protected.clone();
                let population_arity = if let ResourceClause::Declared {
                    arguments,
                    parameter_types,
                    ..
                } = &mut anchor_clause
                {
                    if arguments.len() > 1 {
                        let arity = arguments.len();
                        arguments.truncate(1);
                        parameter_types.truncate(1);
                        Some(arity)
                    } else {
                        None
                    }
                } else {
                    None
                };
                let protected_fact = lower_resource_clause_with_values_mode_at_entry(
                    &anchor_clause,
                    clause_parameters,
                    entry_state,
                    state,
                    result,
                    allow_symbolic_resource_arguments,
                    base_assumptions,
                )?;
                let (family, arguments) = match protected_fact.resource() {
                    Resource::Composite { name, arguments }
                    | Resource::Token { name, arguments } => (name, arguments),
                    _ => {
                        return Err(ClickError::new(
                            "authority requires a declared resource type",
                        ));
                    }
                };
                let description = crate::kernel::ResourceDescription::new(
                    family.clone(),
                    arguments.clone(),
                    schema.clone(),
                );
                let description = match population_arity {
                    Some(arity) => description
                        .with_population_arity(arity)
                        .map_err(ClickError::new)?,
                    None => description,
                };
                return Ok(ResourceFact::own(Resource::PopulationAuthority(
                    description,
                )));
            }
            if name == "mutex_live" {
                let [ProgramValue::Pointer(mutex)] = resource_values.as_slice() else {
                    return Err(ClickError::new("mutex_live expects one mutex pointer"));
                };
                let guard = crate::kernel::program_mutex_live_resource(
                    state,
                    mutex.address(),
                    allow_symbolic_resource_arguments,
                )
                .ok_or_else(|| ClickError::new("mutex_live requires a live initialization"))?;
                return Ok(match access {
                    ResourceAccessMode::Own => guard,
                    ResourceAccessMode::View => ResourceFact::View(guard.resource().clone()),
                });
            }
            if let Some(side) = crate::kernel::PublicationSide::for_keyword(name) {
                let [ProgramValue::Pointer(flag)] = resource_values.as_slice() else {
                    return Err(ClickError::new(format!(
                        "{name} expects one atomic flag pointer"
                    )));
                };
                let Some(
                    payload @ ResourceClause::Declared {
                        type_schema: Some(schema),
                        ..
                    },
                ) = resource_type_arguments.first()
                else {
                    return Err(ClickError::new(format!(
                        "{name} requires the published resource type"
                    )));
                };
                let fact = lower_resource_clause_with_values_mode_at_entry(
                    payload,
                    clause_parameters,
                    entry_state,
                    state,
                    result,
                    allow_symbolic_resource_arguments,
                    base_assumptions,
                )?;
                let Resource::Composite {
                    name: payload_name,
                    arguments,
                } = fact.resource()
                else {
                    return Err(ClickError::new(
                        "the published resource type must be a composite resource",
                    ));
                };
                let right = Resource::Publication(crate::kernel::PublicationRight::new(
                    side,
                    flag.address().clone(),
                    crate::kernel::ResourceDescription::new(
                        payload_name.clone(),
                        arguments.clone(),
                        schema.clone(),
                    ),
                ));
                return Ok(match access {
                    ResourceAccessMode::Own => ResourceFact::own(right),
                    ResourceAccessMode::View => ResourceFact::View(right),
                });
            }
            if name == "mutex_use" {
                let [ProgramValue::Pointer(mutex)] = resource_values.as_slice() else {
                    return Err(ClickError::new("mutex_use expects one mutex pointer"));
                };
                let guard = if let Some(protected) = resource_type_arguments.first() {
                    let ResourceClause::Declared {
                        type_schema: Some(schema),
                        ..
                    } = protected
                    else {
                        return Err(ClickError::new(
                            "protected resource type has no checked schema",
                        ));
                    };
                    let fact = lower_resource_clause_with_values_mode_at_entry(
                        protected,
                        clause_parameters,
                        entry_state,
                        state,
                        result,
                        allow_symbolic_resource_arguments,
                        base_assumptions,
                    )?;
                    let Resource::Composite { name, arguments } = fact.resource() else {
                        return Err(ClickError::new(
                            "protected resource type must be a composite resource",
                        ));
                    };
                    crate::kernel::program_mutex_use_resource_with_type(
                        state,
                        mutex.address(),
                        crate::kernel::ResourceDescription::new(
                            name.clone(),
                            arguments.clone(),
                            schema.clone(),
                        ),
                    )
                } else {
                    crate::kernel::program_mutex_use_resource(state, mutex.address())
                };
                return Ok(match access {
                    ResourceAccessMode::Own => guard,
                    ResourceAccessMode::View => ResourceFact::View(guard.resource().clone()),
                });
            }
            let resource = match kind {
                ResourceKind::Composite => Resource::Composite {
                    name: name.clone(),
                    arguments: resource_values
                        .into_iter()
                        .map(AlgebraicValue::Program)
                        .collect(),
                },
                ResourceKind::Token => Resource::Token {
                    name: name.clone(),
                    arguments: resource_values
                        .into_iter()
                        .map(AlgebraicValue::Program)
                        .collect(),
                },
            };
            Ok(match access {
                ResourceAccessMode::Own => ResourceFact::own(resource),
                ResourceAccessMode::View => ResourceFact::View(resource),
            })
        }
    }
}

fn evaluate_resource_argument_with_state(
    original: &ContractExpression,
    lowered: &ProgramExpression,
    retained_state: crate::kernel::ResourceStateSource,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    entry_state: &ExecutionState,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
) -> Result<ProgramValue, String> {
    if retained_state == crate::kernel::ResourceStateSource::Entry {
        let direct = crate::surface::proof::evaluate_fixed_state_expression_through_kernel(
            original,
            assumptions,
            contract_environment,
            FixedStateFrame::new(entry_state, state, result, &RecordedStates::new()),
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(&[]),
            ),
            &BTreeSet::new(),
        )?;
        return Ok(direct);
    }
    crate::surface::proof::evaluate_resource_argument_through_kernel(
        original,
        lowered,
        assumptions,
        contract_environment,
        state,
        result,
    )
}

fn lower_resource_clause_facts_with_values(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    values: &ProgramValueBindings,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
) -> Result<Vec<ResourceFact>, ClickError> {
    lower_resource_clause_facts_with_values_mode(
        resource,
        parameter_binding,
        values,
        state,
        result,
        false,
    )
}

fn lower_resource_clause_facts_with_values_mode(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    values: &ProgramValueBindings,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
    allow_symbolic_resource_arguments: bool,
) -> Result<Vec<ResourceFact>, ClickError> {
    let base_assumptions = PureFactContext::new();
    lower_resource_clause_facts_with_values_mode_at_entry(
        resource,
        &ClauseParameters::new(parameter_binding.parameters, values, state)
            .with_index(parameter_binding.index),
        state,
        state,
        result,
        allow_symbolic_resource_arguments,
        &base_assumptions,
    )
}

fn lower_resource_clause_facts_with_values_mode_at_entry(
    resource: &ResourceClause,
    clause_parameters: &ClauseParameters<'_>,
    entry_state: &ExecutionState,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
    allow_symbolic_resource_arguments: bool,
    base_assumptions: &PureFactContext,
) -> Result<Vec<ResourceFact>, ClickError> {
    let values = clause_parameters.values;
    match resource {
        ResourceClause::MemoryAggregate { access, segments } => segments
            .iter()
            .map(|segment| {
                let leaf = match access {
                    ResourceAccessMode::Own => ResourceClause::OwnMemory(segment.clone()),
                    ResourceAccessMode::View => ResourceClause::ViewMemory(segment.clone()),
                };
                lower_resource_clause_with_values_mode_at_entry(
                    &leaf,
                    clause_parameters,
                    entry_state,
                    state,
                    result,
                    allow_symbolic_resource_arguments,
                    base_assumptions,
                )
            })
            .collect(),
        ResourceClause::Quantified { quantity, resource } => {
            let original_quantity = quantity.clone();
            let (quantity, quantity_state_source) =
                resource_argument_to_typed_program_expression_with_state(
                    quantity,
                    crate::languages::interface::InterfaceType::Int32,
                )?;
            let assumptions = if allow_symbolic_resource_arguments {
                base_assumptions
                    .clone()
                    .allow_symbolic_contract_loads()
                    .prefer_symbolic_external_loads()
            } else {
                base_assumptions.clone()
            };
            let array_refs = clause_parameters.array_refs();
            let quantity = evaluate_resource_argument_with_state(
                &original_quantity,
                &quantity,
                quantity_state_source,
                &assumptions,
                ContractEnvironment::new(values, array_refs),
                entry_state,
                state,
                result,
            )
            .map_err(|message| {
                ClickError::new(format!(
                    "could not lower declared resource quantity: {message}"
                ))
            })?;
            let ProgramValue::Int32(quantity) = quantity else {
                return Err(ClickError::new(
                    "declared resource quantity must evaluate to int32",
                ));
            };
            lower_resource_clause_facts_with_values_mode_at_entry(
                resource,
                clause_parameters,
                entry_state,
                state,
                result,
                allow_symbolic_resource_arguments,
                base_assumptions,
            )?
            .into_iter()
            .map(|lowered| {
                let ResourceFact::Own(resource, _) = lowered else {
                    return Err(ClickError::new(
                        "declared resource quantity requires owned authority",
                    ));
                };
                Ok(ResourceFact::own_quantity(resource, quantity.clone()))
            })
            .collect()
        }
        _ => Ok(vec![lower_resource_clause_with_values_mode_at_entry(
            resource,
            clause_parameters,
            entry_state,
            state,
            result,
            allow_symbolic_resource_arguments,
            base_assumptions,
        )?]),
    }
}

/// Whether this argument is the C null pointer constant standing at a
/// pointer-typed resource or pure-function parameter.
///
/// A walk that ends at the root of a parent-linked structure reaches a
/// position whose parent is null, and null is the only truthful spelling of
/// that argument: the parameter the body reassigned means its entry value at
/// the boundary, which is a different node. The same holds inside the model:
/// `rb_parent_is(sub, 0)` is how a pure function says "this subtree is the
/// root", and a caller should not have to write the null case out by hand.
/// `0` is already a contract expression, so this is the C null-pointer-constant
/// typing rule rather than new syntax.
pub(in crate::surface) fn argument_is_null_pointer_constant(
    argument: &ContractExpression,
    parameter_type: InterfaceType,
) -> bool {
    parameter_type.is_pointer()
        && matches!(argument, ContractExpression::IntegerLiteral(text) if text == "0")
}

/// `resource_argument_to_program_expression` with the declared parameter type in
/// hand, so the null pointer constant lowers to that pointer type's null
/// value instead of an `int32` zero.
pub(in crate::surface) fn resource_argument_to_typed_program_expression(
    argument: &ContractExpression,
    parameter_type: InterfaceType,
) -> Result<ProgramExpression, ClickError> {
    if argument_is_null_pointer_constant(argument, parameter_type) {
        return Ok(crate::kernel::program_expression::typed_pointer_value(
            Address::null(),
            parameter_type.to_kernel_type(),
        ));
    }
    resource_argument_to_program_expression(argument)
}

/// Lowers a declared-resource argument together with the state that supplies
/// its value.  The surrounding resource clause still has its own state
/// (entry for requirements, post for produced resources); `old(...)` selects
/// the entry state for only this argument.
pub(in crate::surface) fn resource_argument_to_typed_program_expression_with_state(
    argument: &ContractExpression,
    parameter_type: InterfaceType,
) -> Result<(ProgramExpression, crate::kernel::ResourceStateSource), ClickError> {
    if let ContractExpression::Old(inner) = argument {
        return Ok((
            resource_argument_to_typed_program_expression(inner, parameter_type)?,
            crate::kernel::ResourceStateSource::Entry,
        ));
    }
    Ok((
        resource_argument_to_typed_program_expression(argument, parameter_type)?,
        crate::kernel::ResourceStateSource::Current,
    ))
}

pub(in crate::surface) fn resource_argument_to_program_expression(
    argument: &ContractExpression,
) -> Result<ProgramExpression, ClickError> {
    match argument {
        ContractExpression::IntegerContext(_) => Err(ClickError::new(
            "an Integer context is not a C resource argument",
        )),

        ContractExpression::Proposition(_) => {
            Err(ClickError::new("a Prop is not a C resource argument"))
        }
        ContractExpression::Resource(_) => {
            Err(ClickError::new("a Resource descriptor is not a C argument"))
        }
        ContractExpression::Lambda { .. } | ContractExpression::Apply { .. } => Err(
            ClickError::new("a specification lambda application is not a C resource argument"),
        ),

        ContractExpression::IntegerLiteral(text) => {
            let value = text.parse::<u64>().map_err(|_| {
                ClickError::new("an arbitrary Integer literal requires Integer context")
            })?;
            let value = if value <= i32::MAX as u64 {
                ProgramValue::Int32(MachineTerm::constant(value as u32))
            } else if value <= i64::MAX as u64 {
                ProgramValue::Int64(MachineTerm::int64_constant(value as i64))
            } else {
                ProgramValue::UInt64(MachineTerm::uint64_constant(value))
            };
            Ok(ProgramExpression::Value(value))
        }
        ContractExpression::Negate(expression) => {
            if let ContractExpression::IntegerLiteral(text) = expression.as_ref()
                && let Ok(value) = text.parse::<u64>()
                && value <= (i32::MAX as u64) + 1
            {
                return Ok(ProgramExpression::Value(ProgramValue::Int32(
                    MachineTerm::constant(0u32.wrapping_sub(value as u32)),
                )));
            }
            Ok(ProgramExpression::Negate(Box::new(
                resource_argument_to_program_expression(expression)?,
            )))
        }
        ContractExpression::ResourceField(_) => Err(ClickError::new(
            "resource fields are symbolic Click values, not C arguments",
        )),
        ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::AlgebraicConstructor { .. }
        | ContractExpression::AlgebraicMatch { .. } => Err(ClickError::new(
            "declared resource arguments do not yet accept algebraic values",
        )),
        ContractExpression::SequenceLiteral(_) | ContractExpression::SequenceConcat(_, _) => Err(
            ClickError::new("declared resource arguments do not yet accept sequence values"),
        ),
        ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::CUnary {
            lowered: expression,
            ..
        }
        | ContractExpression::ProgramExpression(expression) => Ok(expression.clone()),
        ContractExpression::Field { lowered, .. } => Ok(lowered.clone()),
        ContractExpression::ArrayIndex { lowered, .. } => Ok(lowered.clone()),
        // A loop's pass count is a Click Integer, never a C value; a program
        // variable of that name is `program::iterations`.
        ContractExpression::Binding(name) if name == crate::surface::LOOP_ITERATIONS_NAME => Err(
            ClickError::new("a loop's `iterations` is an Integer, not a C value"),
        ),
        ContractExpression::Binding(name) | ContractExpression::ProgramBinding(name) => {
            Ok(ProgramExpression::Variable((name.clone()).into()))
        }
        ContractExpression::Add(left, right) => Ok(ProgramExpression::Add(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::Subtract(left, right) => Ok(ProgramExpression::Subtract(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::Multiply(left, right) => Ok(ProgramExpression::Multiply(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::Divide(left, right) => Ok(ProgramExpression::Divide(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::Remainder(left, right) => Ok(ProgramExpression::Remainder(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::ShiftLeft(left, right) => Ok(ProgramExpression::ShiftLeft(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::RustShiftLeft(left, right) => Ok(ProgramExpression::RustShiftLeft(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::ShiftRight(left, right) => Ok(ProgramExpression::ShiftRight(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::RustShiftRight(left, right) => Ok(ProgramExpression::RustShiftRight(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::BitwiseAnd(left, right) => Ok(ProgramExpression::BitwiseAnd(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::BitwiseOr(left, right) => Ok(ProgramExpression::BitwiseOr(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::BitwiseXor(left, right) => Ok(ProgramExpression::BitwiseXor(
            Box::new(resource_argument_to_program_expression(left)?),
            Box::new(resource_argument_to_program_expression(right)?),
        )),
        ContractExpression::BitwiseNot(expression) => Ok(ProgramExpression::BitwiseNot(Box::new(
            resource_argument_to_program_expression(expression)?,
        ))),
        ContractExpression::Index(base, index) => Ok(ProgramExpression::Index(
            Box::new(resource_argument_to_program_expression(base)?),
            Box::new(resource_argument_to_program_expression(index)?),
        )),
        ContractExpression::Old(_)
        | ContractExpression::ResourceCount(_)
        | ContractExpression::ResourceWildcard
        | ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. }
        | ContractExpression::At { .. }
        | ContractExpression::If { .. }
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Call { .. }
        | ContractExpression::MethodCall { .. } => Err(ClickError::new(
            "declared resource arguments currently support current-state C expressions only",
        )),
        ContractExpression::Let { body, .. } => {
            // `apply_contract_lets_to_expression` already substituted every
            // referenced value into the body; the wrapper only preserves
            // sharing for later passes. Unwrap to the substituted body.
            resource_argument_to_program_expression(body)
        }
    }
}

fn lower_resource_segment_with_values(
    resource_name: &str,
    segment: &ContractSegment,
    contract_environment: ContractEnvironment<'_>,
    state: &ExecutionState,
    result: Option<&ProgramValue>,
    element_width: u32,
    base_assumptions: &PureFactContext,
) -> Result<MemoryRange, ClickError> {
    if segment.state != ContractSegmentState::Current {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: resource segments cannot use `old(...)`"
        )));
    }
    // Resource ranges embed field loads symbolically (the canonical
    // `load(arg-memory@...)` forms), so segment evaluation must not
    // demand concrete loadability.
    let assumptions = base_assumptions
        .clone()
        .allow_symbolic_contract_loads()
        .prefer_symbolic_external_loads()
        // This pass names a clause; the kernel checks its establishment
        // against the actual pointer and resources at a call or fold.
        .assume_entry_clause_spans();
    let (surface_base, surface_start, surface_end) = match &segment.surface {
        ContractSegmentSurface::Range { base, start, end }
        | ContractSegmentSurface::StructRange {
            base, start, end, ..
        } => (Some(base), Some(start), Some(end)),
        _ => (None, None, None),
    };
    let evaluate =
        |expression: &ProgramExpression, original: Option<&ContractExpression>| match original {
            Some(original) => crate::surface::proof::evaluate_resource_argument_through_kernel(
                original,
                expression,
                &assumptions,
                contract_environment,
                state,
                result,
            ),
            None => crate::surface::proof::evaluate_resource_fragment_through_kernel(
                expression,
                &assumptions,
                contract_environment,
                state,
                result,
            ),
        };
    let base = evaluate(&segment.base, surface_base).map_err(|message| {
        // A parameter or local has no storage a contract can name.
        if let ProgramExpression::AddressOf(variable) = &segment.base
            && let ProgramExpression::Variable(name) = &**variable
        {
            return ClickError::new(format!(
                "could not lower `{resource_name}` resource: `{name}` alone names the variable itself, which a contract cannot own; write `*{name}` for the object it points at"
            ));
        }
        ClickError::new(format!(
            "could not lower `{resource_name}` resource: {message} (segment {})",
            super::super::diagnostics::describe_contract_segment(segment)
        ))
    })?;
    let ProgramValue::Pointer(base) = base else {
        return Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment base did not evaluate to a pointer"
        )));
    };
    // A local pointer has no function-parameter entry. Its evaluated typed
    // value still supplies the element width; do not use the legacy int32
    // default for ranges selected through a byte or wide-integer local.
    // Only a named pointer base uses this path. Field/address expressions
    // retain their explicitly supplied frontend layout widths.
    let element_width = if matches!(segment.surface, ContractSegmentSurface::Range { .. })
        && matches!(segment.base, ProgramExpression::Variable(_))
        && segment.field_element_width().is_none()
    {
        base.program_type()
            .pointee_type()
            .map(ProgramType::byte_width)
            .unwrap_or(element_width)
    } else {
        element_width
    };
    let base_value = base;
    // A clause through a member pointer may not claim past the member
    // (`design/pointer-subobject-bounds.md`, D1). Constant bounds are
    // refused here by name; the kernel decides the rest when it checks
    // the step.
    let refuse_past_bounds = |range: MemoryRange| {
        let (start, end) = match range.wide_bounds() {
            Some(bounds) => bounds,
            None => (range.start(), range.end()),
        };
        if start.as_const().is_none() || end.as_const().is_none() {
            return Ok(range);
        }
        match crate::kernel::memory_range_bounds_refusal(
            &base_value,
            &range,
            &crate::kernel::PureFactContext::new(),
        ) {
            Some(message) => Err(ClickError::new(format!(
                "could not lower `{resource_name}` resource: {message}"
            ))),
            None => Ok(range),
        }
    };
    // A bound keeps its own integer type in the contract: a range with a
    // 64-bit bound is wide, and one with two `int32` bounds is not
    // (`design/typed-indices.md`, stage 2).
    let start_value = evaluate(&segment.start, surface_start).map_err(|message| {
        ClickError::new(format!(
            "could not lower `{resource_name}` resource: {message}"
        ))
    })?;
    let end_value = evaluate(&segment.end, surface_end).map_err(|message| {
        ClickError::new(format!(
            "could not lower `{resource_name}` resource: {message}"
        ))
    })?;
    let bound = |value: ProgramValue, which: &str| match value {
        ProgramValue::Int32(term) => Ok(term),
        value if crate::kernel::narrow_range_constant(&value).is_some() => {
            Ok(crate::kernel::narrow_range_constant(&value).expect("checked above"))
        }
        _ => Err(ClickError::new(format!(
            "could not lower `{resource_name}` resource: segment {which} did not evaluate to an integer index"
        ))),
    };
    // The same rule as the kernel's resource and proposition lowering.
    if let Some((start, end)) = crate::kernel::wide_range_bounds(&start_value, &end_value) {
        return refuse_past_bounds(MemoryRange::from_pointer_value_wide(
            &base_value,
            start,
            end,
            element_width,
        ));
    }
    let start = bound(start_value, "start")?;
    let end = bound(end_value, "end")?;
    if let (int32_constant!(start), bits32_constant!(end)) = (&start, &end)
        && constant_u32(*end) < constant_u32(*start)
    {
        return Err(ClickError::new(format!(
            "`{resource_name}` segment has an end before its start: {start}..{end}",
            start = constant_u32(*start),
            end = constant_u32(*end)
        )));
    }
    refuse_past_bounds(MemoryRange::from_pointer_value(
        &base_value,
        start,
        end,
        element_width,
    ))
}

fn loadable_requirement_props(
    requirement: &Requirement,
    parameter_binding: ParameterBinding<'_>,
    memory: &SymbolicMemory,
    assumptions: &PureFactContext,
) -> Result<Vec<Proposition>, ClickError> {
    if let Requirement::LoadableSegment { segment } = requirement
        && segment.state == ContractSegmentState::Current
    {
        let state = ExecutionState::new().with_memory(memory.clone());
        let values = parameter_values(parameter_binding)?;
        // A requirement names the footprint and its formation conditions.
        // Collect these debts once; callers owe them and function entry
        // assumes them alongside the viewability requirement.
        let (range, formation) = crate::surface::proof::probe_open_obligations(|| {
            lower_resource_segment_with_values(
                "viewable",
                segment,
                ContractEnvironment::new(
                    &values,
                    &array_refs_for_parameters(
                        parameter_binding.parameters,
                        &values,
                        &state.program_point(),
                    ),
                )
                .with_parameters(parameter_binding),
                &state,
                None,
                contract_segment_element_width(parameter_binding.parameters, segment),
                assumptions,
            )
        });
        let range = range?;
        let mut guards = memory_range_loadable_guards(&range);
        guards.extend(
            formation
                .recorded
                .into_iter()
                .map(|requirement| requirement.proposition),
        );
        reject_impossible_range_guards(&guards, assumptions)?;
        let mut propositions = vec![memory_range_loadable_atom_prop(memory, &range)];
        propositions.extend(guards);
        return Ok(propositions);
    }
    let (base, bytes, guards) = loadable_base_and_bytes(requirement, parameter_binding)?;
    reject_impossible_range_guards(&guards, assumptions)?;
    let mut propositions = vec![Proposition::MemoryLoadable {
        memory: memory.clone(),
        base,
        bytes: (bytes).into(),
        wide: false,
    }];
    propositions.extend(guards);
    Ok(propositions)
}

pub(in crate::surface) fn resource_clause_loadable_prop(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    memory: &SymbolicMemory,
) -> Result<Option<Proposition>, ClickError> {
    resource_clause_loadable_prop_at_state(
        resource,
        parameter_binding,
        &ExecutionState::new().with_memory(memory.clone()),
    )
}

pub(in crate::surface) fn resource_clause_loadable_prop_at_state(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Result<Option<Proposition>, ClickError> {
    let Some(ranges) = resource_clause_memory_ranges_at_state(resource, parameter_binding, state)?
    else {
        return Ok(None);
    };
    let mut propositions = ranges
        .iter()
        .map(|range| memory_range_loadable_atom_prop(state.memory(), range))
        .collect::<Vec<_>>();
    let first = propositions
        .drain(..1)
        .next()
        .expect("memory resource clause has at least one range");
    Ok(Some(propositions.into_iter().fold(first, |left, right| {
        Proposition::And(Box::new(left), Box::new(right))
    })))
}

pub(in crate::surface) fn resource_clause_loadable_props_at_state(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    assumptions: &PureFactContext,
) -> Result<Option<Vec<Proposition>>, ClickError> {
    // Naming an ownership requirement retains its endpoint domains alongside
    // the loadability fact, just as an explicit viewable requirement does.
    let (ranges, formation) = crate::surface::proof::probe_open_obligations(|| {
        resource_clause_memory_ranges_at_state(resource, parameter_binding, state)
    });
    let Some(ranges) = ranges? else {
        return Ok(None);
    };
    let loadable = ranges
        .iter()
        .map(|range| memory_range_loadable_atom_prop(state.memory(), range))
        .reduce(|left, right| Proposition::And(Box::new(left), Box::new(right)))
        .expect("memory resource clause has at least one range");
    // Every stated range carries its byte-count guards, whichever clause
    // states it. `owns p[lo..hi]` and an aggregate range mean the same thing
    // about `lo..hi` as `views p[lo..hi]` does, and the loadability rules read
    // all three at element granularity; a guard that rode along with one
    // clause and not another would make the same range mean two things.
    let mut propositions = vec![loadable];
    let guards = ranges
        .iter()
        .flat_map(memory_range_loadable_guards)
        .collect::<Vec<_>>();
    reject_impossible_range_guards(&guards, assumptions)?;
    propositions.extend(guards);
    propositions.extend(formation.recorded.into_iter().map(|debt| debt.proposition));
    Ok(Some(propositions))
}

fn reject_impossible_range_guards(
    guards: &[Proposition],
    assumptions: &PureFactContext,
) -> Result<(), ClickError> {
    if guards.iter().any(|guard| match guard {
        condition_source_0 @ Proposition::ConditionIs(_, true)
            if let Some((ConditionTerm::Constant(false), _)) =
                condition_source_0.condition_native() =>
        {
            true
        }
        Proposition::ConditionIs(condition, true) => {
            assumptions.decide(condition.native_compat()) == Some(false)
        }
        _ => false,
    }) {
        return Err(ClickError::new(
            "memory range requires the verifier to have assumed a condition fact that cannot hold",
        ));
    }
    Ok(())
}

pub(in crate::surface) fn resource_clause_memory_ranges_at_state(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Result<Option<Vec<MemoryRange>>, ClickError> {
    let ranges = match resource {
        ResourceClause::Conditional { .. } => return Ok(None),
        ResourceClause::Named { .. } => return Ok(None),
        ResourceClause::ViewMemory(_) | ResourceClause::OwnMemory(_) => {
            let lowered = lower_resource_clause_at_state(resource, parameter_binding, state)?;
            vec![
                lowered
                    .memory_view_range()
                    .or_else(|| lowered.memory_own_range())
                    .expect("memory clause should lower to a memory range")
                    .clone(),
            ]
        }
        ResourceClause::MemoryAggregate { .. } => {
            lower_resource_clause_facts_at_state(resource, parameter_binding, state)?
                .into_iter()
                .map(|lowered| {
                    lowered
                        .memory_view_range()
                        .or_else(|| lowered.memory_own_range())
                        .expect("aggregate memory clause should lower to memory ranges")
                        .clone()
                })
                .collect()
        }
        ResourceClause::Declared { .. }
        | ResourceClause::Quantified { .. }
        | ResourceClause::Iterated(_) => return Ok(None),
    };
    Ok(Some(ranges))
}

pub(in crate::surface) fn memory_range_loadable_prop(
    memory: &SymbolicMemory,
    range: &MemoryRange,
) -> Proposition {
    memory_range_loadable_atom_prop(memory, range)
}

pub(in crate::surface) fn memory_range_loadable_atom_prop(
    memory: &SymbolicMemory,
    range: &MemoryRange,
) -> Proposition {
    if range.wide_bounds().is_some() {
        return range.loadable_fact(memory);
    }
    let (base, bytes) = range.byte_footprint();
    Proposition::MemoryLoadable {
        memory: memory.clone(),
        base,
        bytes: (bytes).into(),
        wide: false,
    }
}

pub(in crate::surface) fn memory_range_loadable_guards(range: &MemoryRange) -> Vec<Proposition> {
    crate::kernel::memory_range_span_guard_spellings(range)
}

pub(in crate::surface) fn concrete_loadable_block(
    requirement: &Requirement,
    parameter_binding: ParameterBinding<'_>,
) -> Result<Option<(String, ConcreteMemoryRangeSeed)>, ClickError> {
    match requirement {
        Requirement::LoadableSegment { segment } => {
            let state = ExecutionState::new();
            let source_segment = segment;
            let Ok(segment) =
                evaluate_requirement_segment(parameter_binding, &state, source_segment)
            else {
                return Ok(None);
            };
            if segment.base.offset != AddressOffset::Constant(0)
                || segment.start != MachineTerm::constant(0)
            {
                return Ok(None);
            }
            let bits32_constant!(end) = segment.end else {
                return Ok(None);
            };
            if let Some(layout) =
                object_segment_layout(parameter_binding.parameters, source_segment)
            {
                return Ok(Some((
                    format!("{:?}", segment.source),
                    object_range_seed(segment.base, layout),
                )));
            }
            let element_width =
                contract_segment_element_width(parameter_binding.parameters, &segment.source);
            let bytes = constant_u32(end)
                .checked_mul(element_width)
                .ok_or_else(|| ClickError::new("`viewable` segment overflows byte count"))?;
            Ok(Some((
                format!("{:?}", segment.source),
                ConcreteMemoryRangeSeed {
                    base: segment.base,
                    bytes,
                    element_width,
                    element_type: (!contract_expression_is_struct_array(
                        parameter_binding.parameters,
                        &segment.source.base,
                    ))
                    .then(|| {
                        contract_segment_element_type(parameter_binding.parameters, &segment.source)
                    }),
                    struct_layout: contract_segment_struct_layout(
                        parameter_binding.parameters,
                        source_segment,
                    )
                    .cloned(),
                }
                .with_element_cells(),
            )))
        }
        Requirement::Resource(_) | Requirement::Proposition(_) => Ok(None),
    }
}

pub(in crate::surface) fn concrete_access_resource_blocks(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
) -> Result<Vec<(String, ConcreteMemoryRangeSeed)>, ClickError> {
    let segments = match resource {
        ResourceClause::Conditional { .. } => return Ok(vec![]),
        ResourceClause::Named { .. } => return Ok(vec![]),
        ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => {
            vec![segment]
        }
        ResourceClause::MemoryAggregate { segments, .. } => segments.iter().collect(),
        ResourceClause::Declared { .. }
        | ResourceClause::Quantified { .. }
        | ResourceClause::Iterated(_) => {
            return Ok(Vec::new());
        }
    };
    let mut result = Vec::new();
    // An uninitialized segment's bytes hold no value to seed.
    for segment in segments
        .into_iter()
        .filter(|segment| !segment.is_uninitialized())
    {
        let state = ExecutionState::new();
        let source_segment = segment;
        let Ok(segment) = evaluate_requirement_segment(parameter_binding, &state, source_segment)
        else {
            continue;
        };
        let (int32_constant!(start), bits32_constant!(end)) = (&segment.start, &segment.end) else {
            continue;
        };
        if constant_u32(*end) < constant_u32(*start) {
            return Err(ClickError::new(format!(
                "resource segment has an end before its start: {start}..{end}",
                start = constant_u32(*start),
                end = constant_u32(*end)
            )));
        }
        if let Some(layout) = object_segment_layout(parameter_binding.parameters, source_segment)
            && constant_u32(*start) == 0
        {
            result.push((
                format!("{:?}", segment.source),
                object_range_seed(segment.base, layout),
            ));
            continue;
        }
        let element_width =
            contract_segment_element_width(parameter_binding.parameters, &segment.source);
        let element_count = constant_u32(*end) - constant_u32(*start);
        let bytes = element_count
            .checked_mul(element_width)
            .ok_or_else(|| ClickError::new("`write` segment overflows byte count"))?;
        result.push((
            format!("{:?}", segment.source),
            ConcreteMemoryRangeSeed {
                base: offset_pointer_by_elements(segment.base, segment.start, element_width),
                bytes,
                element_width,
                element_type: (!contract_expression_is_struct_array(
                    parameter_binding.parameters,
                    &segment.source.base,
                ))
                .then(|| {
                    contract_segment_element_type(parameter_binding.parameters, &segment.source)
                }),
                struct_layout: contract_segment_struct_layout(
                    parameter_binding.parameters,
                    source_segment,
                )
                .cloned(),
            }
            .with_element_cells(),
        ));
    }
    Ok(result)
}

pub(in crate::surface) fn loadable_base_and_bytes(
    requirement: &Requirement,
    parameter_binding: ParameterBinding<'_>,
) -> Result<(Address, MachineTerm, Vec<Proposition>), ClickError> {
    match requirement {
        Requirement::LoadableSegment { segment } => {
            let state = ExecutionState::new();
            let segment = evaluate_requirement_segment(parameter_binding, &state, segment)
                .map_err(|message| {
                    ClickError::new(format!("could not lower `viewable` segment: {message}"))
                })?;
            if let (int32_constant!(start), bits32_constant!(end)) = (&segment.start, &segment.end)
                && constant_u32(*end) < constant_u32(*start)
            {
                return Err(ClickError::new(format!(
                    "`viewable` segment has an end before its start: {start}..{end}",
                    start = constant_u32(*start),
                    end = constant_u32(*end)
                )));
            }
            let element_width =
                contract_segment_element_width(parameter_binding.parameters, &segment.source);
            let bytes = crate::kernel::memory_range_byte_count(
                segment.start.clone(),
                segment.end.clone(),
                element_width,
            );
            // A written `viewable(p[a..b])` states the same range a `views
            // p[a..b]` clause does, so it carries the same guards in the same
            // spellings (`memory_range_loadable_guards`): the endpoint form
            // memory reasoning reads and the signed count form a proof can
            // write, such as `n <= 1073741823` for `p[0..n]` of `int32`.
            let guards = memory_range_loadable_guards(&MemoryRange::new_with_element_width(
                segment.base.clone(),
                segment.start.clone(),
                segment.end.clone(),
                element_width,
            ));
            Ok((
                offset_pointer_by_elements(segment.base, segment.start.clone(), element_width),
                bytes,
                guards,
            ))
        }
        Requirement::Proposition(_) | Requirement::Resource(_) => {
            Err(ClickError::new("expected viewable requirement"))
        }
    }
}

/// The struct layout behind `*p` for a struct-pointer parameter `p`.
/// Such a segment is one complete object, not a run of int32 words, so its
/// cells take the field types of the layout.
/// The byte runs, from a memory clause's start, that hold values: a scalar
/// field's leading bytes, or each field of the objects it names. A
/// call checks only these for initialization; the rest of the range is
/// padding. `None` is every byte, which a range whose length is not a
/// constant gets.
pub(in crate::surface) fn contract_segment_value_runs(
    parameters: &[crate::languages::interface::ImportedParameter],
    segment: &ContractSegment,
) -> Option<std::sync::Arc<[(u32, u32)]>> {
    const OBJECT_LIMIT: u32 = 4096;
    if let Some(width) = segment.scalar_field_value_bytes() {
        return Some(std::sync::Arc::from([(0, width)]));
    }
    let (layout, count) = match &segment.surface {
        ContractSegmentSurface::StructRange { layout, .. } => {
            let (
                ProgramExpression::Value(ProgramValue::Int32(start)),
                ProgramExpression::Value(ProgramValue::Int32(end)),
            ) = (&segment.start, &segment.end)
            else {
                return None;
            };
            (
                &layout.layout,
                end.as_const()?.checked_sub(start.as_const()?)?,
            )
        }
        _ => (object_segment_layout(parameters, segment)?, 1),
    };
    if count > OBJECT_LIMIT {
        return None;
    }
    let fields = layout.value_byte_runs();
    let size = layout.size_bytes();
    Some(
        (0..count)
            .flat_map(|index| {
                fields
                    .iter()
                    .map(move |(offset, width)| (index * size + offset, *width))
            })
            .collect(),
    )
}

pub(in crate::surface) fn object_segment_layout<'a>(
    parameters: &'a [crate::languages::interface::ImportedParameter],
    segment: &'a ContractSegment,
) -> Option<&'a crate::languages::interface::RecordLayout> {
    if let ContractSegmentSurface::ObjectPlace { layout, .. } = &segment.surface {
        return Some(&layout.layout);
    }
    let ContractSegmentSurface::Object(struct_name) = &segment.surface else {
        return None;
    };
    // The base is the named parameter while the clause is written against
    // it, and a pointer value once a body has been instantiated for a held
    // resource; in both cases the surface names the struct, whose layout
    // any parameter of that struct type carries.
    if let ProgramExpression::Variable(name) = &segment.base
        && let Some(layout) = parameters
            .iter()
            .find(|parameter| parameter.matches_binding(name))
            .and_then(crate::languages::interface::ImportedParameter::pointee_struct_layout)
    {
        return Some(layout);
    }
    parameters
        .iter()
        .find(|parameter| parameter.struct_name() == Some(struct_name.as_str()))
        .and_then(|parameter| {
            parameter
                .pointee_struct_layout()
                .or_else(|| parameter.struct_layout())
        })
}

/// One complete struct object as a memory range seed: a single element of
/// the layout's size, materialized field by field.
fn object_range_seed(
    base: Address,
    layout: &crate::languages::interface::RecordLayout,
) -> ConcreteMemoryRangeSeed {
    ConcreteMemoryRangeSeed {
        base,
        bytes: layout.size_bytes(),
        element_width: layout.size_bytes(),
        element_type: None,
        struct_layout: Some(layout.clone()),
    }
}

pub(in crate::surface) fn contract_segment_element_width(
    parameters: &[crate::languages::interface::ImportedParameter],
    segment: &ContractSegment,
) -> u32 {
    contract_segment_element_width_for_result_type(parameters, segment, None)
}

pub(in crate::surface) fn contract_segment_element_width_for_result_type(
    parameters: &[crate::languages::interface::ImportedParameter],
    segment: &ContractSegment,
    result_type: Option<ProgramType>,
) -> u32 {
    contract_segment_element_width_with_parameter(segment, result_type, &|name| {
        parameters
            .iter()
            .find(|parameter| parameter.matches_binding(name))
    })
}

pub(in crate::surface) fn contract_segment_element_width_with_binding(
    binding: ParameterBinding<'_>,
    segment: &ContractSegment,
) -> u32 {
    let Some(index) = binding.index else {
        return contract_segment_element_width(binding.parameters, segment);
    };
    contract_segment_element_width_with_parameter(segment, None, &|name| {
        binding
            .parameters
            .get(index.position(name.source_name())?)
            .filter(|parameter| parameter.matches_binding(name))
    })
}

fn contract_segment_element_width_with_parameter<'a>(
    segment: &ContractSegment,
    result_type: Option<ProgramType>,
    parameter: &impl Fn(
        &crate::kernel::BindingName,
    ) -> Option<&'a crate::languages::interface::ImportedParameter>,
) -> u32 {
    if matches!(
        segment.surface,
        ContractSegmentSurface::Object(_) | ContractSegmentSurface::ObjectPlace { .. }
    ) {
        return 4;
    }
    if let Some(element_width) = segment.field_element_width() {
        return element_width;
    }
    if matches!(&segment.base, ProgramExpression::Variable(name)
        if name == &crate::kernel::CONTRACT_RESULT
            || (name.is_named("result") && !matches!(&segment.surface,
                ContractSegmentSurface::Range { base: ContractExpression::ProgramBinding(_), .. })))
        && let Some(element_width) = result_type
            .and_then(ProgramType::pointee_type)
            .map(ProgramType::byte_width)
    {
        return element_width;
    }
    contract_expression_element_width_with_parameter(&segment.base, parameter).unwrap_or(4)
}

/// Loop locals have frontend-declared types even before execution binds values.
/// Preserve explicit field layouts and parameter ABI widths before consulting
/// that index. No scalar declaration itself supplies a readable range.
pub(in crate::surface) fn contract_segment_element_width_with_pointer_types(
    parameters: &[crate::languages::interface::ImportedParameter],
    segment: &ContractSegment,
    result_type: Option<ProgramType>,
    pointer_types: Option<&BTreeMap<String, ProgramType>>,
) -> u32 {
    fn local_element(
        expression: &ProgramExpression,
        types: &BTreeMap<String, ProgramType>,
    ) -> Option<ProgramType> {
        match expression {
            ProgramExpression::Variable(name) => name
                .program_type()
                .and_then(|ty| ty.pointee_type().or_else(|| ty.array_element_type()))
                .or_else(|| name.named_in(types).copied()),
            ProgramExpression::Add(left, right) => {
                local_element(left, types).or_else(|| local_element(right, types))
            }
            ProgramExpression::Subtract(left, _) => local_element(left, types),
            ProgramExpression::PointerOffsetBytes { pointer, .. }
            | ProgramExpression::Subobject { pointer, .. } => local_element(pointer, types),
            _ => None,
        }
    }
    if segment.field_element_width().is_some()
        || contract_expression_element_width(parameters, &segment.base).is_some()
        || matches!(&segment.base, ProgramExpression::Variable(name)
            if name == &crate::kernel::CONTRACT_RESULT
                || (name.is_named("result") && !matches!(&segment.surface,
                    ContractSegmentSurface::Range { base: ContractExpression::ProgramBinding(_), .. })))
    {
        return contract_segment_element_width_for_result_type(parameters, segment, result_type);
    }
    pointer_types
        .and_then(|types| local_element(&segment.base, types))
        .map(ProgramType::byte_width)
        .unwrap_or_else(|| {
            contract_segment_element_width_for_result_type(parameters, segment, result_type)
        })
}

pub(in crate::surface) fn declared_segment_observation_count(
    segment: &ContractSegment,
) -> Option<u32> {
    segment.field_element_type()?;
    match &segment.base {
        ProgramExpression::TypedLoad {
            value_type:
                ProgramType::Int8Array(count)
                | ProgramType::UInt8Array(count)
                | ProgramType::Int16Array(count)
                | ProgramType::UInt16Array(count)
                | ProgramType::Int32Array(count)
                | ProgramType::UInt32Array(count)
                | ProgramType::Int64Array(count)
                | ProgramType::UInt64Array(count)
                | ProgramType::Int128Array(count)
                | ProgramType::UInt128Array(count)
                | ProgramType::Float32Array(count)
                | ProgramType::Float64Array(count)
                | ProgramType::PointerArray(_, count),
            ..
        } => Some(*count),
        _ => Some(1),
    }
}

pub(in crate::surface) fn contract_segment_element_type(
    parameters: &[crate::languages::interface::ImportedParameter],
    segment: &ContractSegment,
) -> ProgramType {
    segment
        .field_element_type()
        .or_else(|| contract_expression_element_type(parameters, &segment.base))
        .unwrap_or(ProgramType::Int32)
}

fn contract_expression_is_struct_array(
    parameters: &[crate::languages::interface::ImportedParameter],
    expression: &ProgramExpression,
) -> bool {
    match expression {
        ProgramExpression::Variable(name) => parameters
            .iter()
            .find(|parameter| parameter.matches_binding(name))
            .is_some_and(|parameter| parameter.array_element_width().is_some()),
        ProgramExpression::Add(left, right) => {
            contract_expression_is_struct_array(parameters, left)
                || contract_expression_is_struct_array(parameters, right)
        }
        ProgramExpression::Subtract(left, _) => {
            contract_expression_is_struct_array(parameters, left)
        }
        _ => false,
    }
}

fn contract_expression_struct_layout<'a>(
    parameters: &'a [crate::languages::interface::ImportedParameter],
    expression: &ProgramExpression,
) -> Option<&'a crate::languages::interface::RecordLayout> {
    match expression {
        ProgramExpression::Variable(name) => parameters
            .iter()
            .find(|parameter| parameter.matches_binding(name))
            .and_then(|parameter| {
                (parameter.array_element_width().is_some() || parameter.is_struct_value())
                    .then(|| parameter.struct_layout())
                    .flatten()
            }),
        ProgramExpression::Add(left, right) => contract_expression_struct_layout(parameters, left)
            .or_else(|| contract_expression_struct_layout(parameters, right)),
        ProgramExpression::Subtract(left, _) => contract_expression_struct_layout(parameters, left),
        _ => None,
    }
}

fn contract_segment_struct_layout<'a>(
    parameters: &'a [crate::languages::interface::ImportedParameter],
    segment: &'a ContractSegment,
) -> Option<&'a crate::languages::interface::RecordLayout> {
    if let ContractSegmentSurface::StructRange { layout, .. } = &segment.surface {
        return Some(&layout.layout);
    }
    // A field segment already carries the leaf's physical type and width.
    // Treating its base as an aggregate range would expand every struct field
    // at the leaf's address, which can install a different typed cell there.
    if segment.field_element_type().is_some() {
        return None;
    }
    contract_expression_struct_layout(parameters, &segment.base)
}

fn contract_expression_element_type(
    parameters: &[crate::languages::interface::ImportedParameter],
    expression: &ProgramExpression,
) -> Option<ProgramType> {
    match expression {
        // An indexed place becomes `&base[index]` when used as ownership.
        // Its address still points to the base's element type.
        ProgramExpression::AddressOf(place) => match place.as_ref() {
            ProgramExpression::Index(base, _) => contract_expression_element_type(parameters, base),
            _ => None,
        },
        ProgramExpression::Value(value) => value.program_type().pointee_type(),
        ProgramExpression::Cast { target_type, .. } => target_type.pointee_type(),
        ProgramExpression::Variable(name) => parameters
            .iter()
            .find(|parameter| parameter.matches_binding(name))
            .and_then(|parameter| parameter.interface_type().pointee_type())
            .map(InterfaceType::to_kernel_type),
        ProgramExpression::Add(left, right) => contract_expression_element_type(parameters, left)
            .or_else(|| contract_expression_element_type(parameters, right)),
        ProgramExpression::Subtract(left, _) => contract_expression_element_type(parameters, left),
        ProgramExpression::TypedLoad { value_type, .. } => match value_type {
            ProgramType::Int32Array(_) => Some(ProgramType::Int32),
            ProgramType::UInt8Array(_) => Some(ProgramType::UInt8),
            ProgramType::Int8Array(_) => Some(ProgramType::Int8),
            ProgramType::Int16Array(_) => Some(ProgramType::Int16),
            ProgramType::UInt16Array(_) => Some(ProgramType::UInt16),
            ProgramType::UInt32Array(_) => Some(ProgramType::UInt32),
            ProgramType::Int64Array(_) => Some(ProgramType::Int64),
            ProgramType::Int128Array(_) => Some(ProgramType::Int128),
            ProgramType::UInt64Array(_) => Some(ProgramType::UInt64),
            ProgramType::UInt128Array(_) => Some(ProgramType::UInt128),
            value_type => value_type.pointee_type(),
        },
        _ => None,
    }
}

pub(in crate::surface) fn contract_expression_element_width(
    parameters: &[crate::languages::interface::ImportedParameter],
    expression: &ProgramExpression,
) -> Option<u32> {
    contract_expression_element_width_with_parameter(expression, &|name| {
        parameters
            .iter()
            .find(|parameter| parameter.matches_binding(name))
    })
}

fn contract_expression_element_width_with_parameter<'a>(
    expression: &ProgramExpression,
    parameter: &impl Fn(
        &crate::kernel::BindingName,
    ) -> Option<&'a crate::languages::interface::ImportedParameter>,
) -> Option<u32> {
    match expression {
        ProgramExpression::AddressOf(place) => match place.as_ref() {
            ProgramExpression::Index(base, _) => {
                contract_expression_element_width_with_parameter(base, parameter)
            }
            _ => None,
        },
        ProgramExpression::Value(value) => value
            .program_type()
            .pointee_type()
            .map(ProgramType::byte_width),
        ProgramExpression::Cast { target_type, .. } => {
            target_type.pointee_type().map(ProgramType::byte_width)
        }
        ProgramExpression::Variable(name) => parameter(name).and_then(|parameter| {
            if parameter.is_struct_value() {
                Some(4)
            } else {
                parameter
                    .array_element_width()
                    .or_else(|| match parameter.interface_type() {
                        interface_type if interface_type.is_pointer() => interface_type
                            .pointee_type()
                            .map(InterfaceType::to_kernel_type)
                            .map(ProgramType::byte_width),
                        // Abstract values and enums use their model
                        // width, as do the cells that hold them.
                        InterfaceType::ParameterPointer(name) => {
                            Some(ProgramType::Parameter(name).byte_width())
                        }
                        InterfaceType::Int32Array(_) => Some(4),
                        InterfaceType::CharArray(_, _) => Some(1),
                        InterfaceType::UInt8Array(_) => Some(1),
                        InterfaceType::Int8Array(_) => Some(1),
                        InterfaceType::Int16Array(_) | InterfaceType::UInt16Array(_) => Some(2),
                        InterfaceType::UInt32Array(_) => Some(4),
                        InterfaceType::Int64Array(_, _) | InterfaceType::UInt64Array(_, _) => {
                            Some(8)
                        }
                        InterfaceType::Int128Array(_) | InterfaceType::UInt128Array(_) => Some(16),
                        _ => None,
                    })
            }
        }),
        ProgramExpression::Add(left, right) => {
            contract_expression_element_width_with_parameter(left, parameter)
                .or_else(|| contract_expression_element_width_with_parameter(right, parameter))
        }
        ProgramExpression::Subtract(left, _) => {
            contract_expression_element_width_with_parameter(left, parameter)
        }
        ProgramExpression::TypedLoad { value_type, .. } => match value_type {
            interface_type if interface_type.is_pointer() => {
                interface_type.pointee_type().map(ProgramType::byte_width)
            }
            ProgramType::Int32Array(_) => Some(4),
            ProgramType::UInt8Array(_) => Some(1),
            ProgramType::Int8Array(_) => Some(1),
            ProgramType::Int16Array(_) | ProgramType::UInt16Array(_) => Some(2),
            ProgramType::UInt32Array(_) => Some(4),
            ProgramType::Int64Array(_) | ProgramType::UInt64Array(_) => Some(8),
            ProgramType::Int128Array(_) | ProgramType::UInt128Array(_) => Some(16),
            _ => None,
        },
        _ => None,
    }
}

pub(in crate::surface) fn requirement_proposition_prop(
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<Proposition, ClickError> {
    requirement_proposition_prop_with_assumptions(
        parameter_binding,
        state,
        proposition,
        spec_definitions,
        &PureFactContext::new(),
    )
}

pub(in crate::surface) fn requirement_proposition_prop_with_assumptions(
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
    assumptions: &PureFactContext,
) -> Result<Proposition, ClickError> {
    requirement_proposition_and_facts_with_assumptions(
        parameter_binding,
        state,
        &requirement_lowering_state(parameter_binding, state)?,
        proposition,
        spec_definitions,
        assumptions,
    )
    .map(|(proposition, _)| proposition)
}

/// The entry state with the parameters bound to their argument values where
/// it does not bind them: the state every requirement of one list is lowered
/// at, built once for the list.
fn requirement_lowering_state(
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
) -> Result<ExecutionState, ClickError> {
    let mut lowering_state = state.clone();
    for (parameter, argument) in parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
    {
        let ProgramExpression::Value(value) = argument else {
            return Err(ClickError::new(format!(
                "could not build contract environment for parameter `{}`",
                parameter.name()
            )));
        };
        if !lowering_state
            .locals()
            .contains_name(parameter.binding_name())
        {
            lowering_state = lowering_state.with_local(parameter.binding_name(), value.clone());
        }
    }
    Ok(lowering_state)
}

fn requirement_proposition_and_facts_with_assumptions(
    parameter_binding: ParameterBinding<'_>,
    state: &ExecutionState,
    lowering_state: &ExecutionState,
    proposition: &ClickProposition,
    spec_definitions: SpecDefinitions<'_>,
    assumptions: &PureFactContext,
) -> Result<(Proposition, Vec<Proposition>), ClickError> {
    // The requirement is elaborated as the contract elaborates it and
    // lowered by the kernel at the entry state with the parameters bound
    // (`requirement_lowering_state`).
    let spec = crate::surface::lowering::elaborate_requirement_proposition(
        parameter_binding,
        state,
        proposition,
        spec_definitions,
    )
    .map_err(ClickError::new)?;
    let (lowered, facts, obligations) = crate::kernel::program_lower_spec_proposition_at_state(
        lowering_state,
        &spec,
        None,
        assumptions,
    )
    .map_err(|message| {
        ClickError::new(format!(
            "could not lower requirement `{}`: {message}",
            crate::surface::diagnostics::describe_click_proposition(proposition)
        ))
    })?;
    // A requirement may read only memory the function's entry justifies:
    // cells the entry holds, a resource it views or owns, or a loadability
    // the requirements state.
    if let Some(obligation) = obligations.iter().find(|obligation| {
        !crate::kernel::execution_state_justifies_loadability_obligation(
            lowering_state,
            obligation,
            assumptions,
        )
    }) {
        return Err(ClickError::new(format!(
            "{}{}",
            crate::surface::diagnostics::describe_missing_pure_fact(
                obligation,
                &[],
                &[],
                parameter_binding,
                &[],
            ),
            folded_matched_instance_note(lowering_state, parameter_binding, assumptions)
        )));
    }
    // The kernel selected this lowering path, and every outstanding read
    // obligation was checked above. Its auxiliary facts include the checked
    // population lower bound; retaining them avoids losing ownership-derived
    // facts when the written requirement observes a count.
    let facts = { facts };
    Ok((lowered, facts))
}

pub(in crate::surface) fn parameter_values(
    parameter_binding: ParameterBinding<'_>,
) -> Result<ProgramValueBindings, ClickError> {
    crate::instrumentation::record_deterministic_work(parameter_binding.parameters.len());
    parameter_binding
        .parameters
        .iter()
        .zip(parameter_binding.arguments)
        .map(|(parameter, argument)| {
            let ProgramExpression::Value(value) = argument else {
                return Err(ClickError::new(format!(
                    "could not build contract environment for parameter `{}`",
                    parameter.name()
                )));
            };
            Ok((parameter.name().to_string(), value.clone()))
        })
        .collect()
}

/// The values of the parameters among `names`, or of every parameter when
/// the binding has no index. A name that is not a parameter is skipped.
pub(in crate::surface) fn parameter_values_named(
    parameter_binding: ParameterBinding<'_>,
    names: &BTreeSet<String>,
) -> Result<ProgramValueBindings, ClickError> {
    let Some(index) = parameter_binding.index else {
        return parameter_values(parameter_binding);
    };
    names
        .iter()
        .filter_map(|name| {
            let position = index.position(name)?;
            Some((
                &parameter_binding.parameters[position],
                parameter_binding.arguments.get(position)?,
            ))
        })
        .map(|(parameter, argument)| {
            let ProgramExpression::Value(value) = argument else {
                return Err(ClickError::new(format!(
                    "could not build contract environment for parameter `{}`",
                    parameter.name()
                )));
            };
            Ok((parameter.name().to_string(), value.clone()))
        })
        .collect()
}

/// The array references of the parameters `values` binds: with the binding's
/// index, found from those values alone rather than from every parameter.
pub(in crate::surface) fn array_refs_for_values(
    parameter_binding: ParameterBinding<'_>,
    values: &ProgramValueBindings,
    point: &crate::kernel::ProgramPoint,
) -> ClickArrayRefs {
    let Some(index) = parameter_binding.index else {
        return array_refs_for_parameters(parameter_binding.parameters, values, point);
    };
    values
        .iter()
        .filter_map(|(name, value)| {
            let parameter = &parameter_binding.parameters[index.position(name)?];
            let element_type = click_array_element_type(parameter.interface_type())?;
            let ProgramValue::Pointer(pointer) = value else {
                return None;
            };
            Some((
                name.clone(),
                ClickArrayRef {
                    point: point.clone(),
                    pointer: pointer.address().clone(),
                    element_type,
                },
            ))
        })
        .collect()
}

/// The parameter names explicitly read by a resource clause. Iterated clauses
/// retain their existing environment construction until their binders are handled.
fn resource_clause_referenced_names(resource: &ResourceClause) -> Option<BTreeSet<String>> {
    match resource {
        ResourceClause::ViewMemory(segment) | ResourceClause::OwnMemory(segment) => Some(
            super::source_layout::contract_segment_referenced_names(segment),
        ),
        ResourceClause::MemoryAggregate { segments, .. } => Some(
            segments
                .iter()
                .flat_map(super::source_layout::contract_segment_referenced_names)
                .collect(),
        ),
        ResourceClause::Declared {
            arguments,
            resource_type_arguments,
            ..
        } => {
            let mut names = BTreeSet::new();
            for argument in arguments {
                collect_contract_expression_referenced_names(argument, &mut names);
            }
            for resource_type in resource_type_arguments {
                names.extend(resource_clause_referenced_names(resource_type)?);
            }
            Some(names)
        }
        ResourceClause::Named { resource, .. } => resource_clause_referenced_names(resource),
        ResourceClause::Quantified { quantity, resource } => {
            let mut names = resource_clause_referenced_names(resource)?;
            collect_contract_expression_referenced_names(quantity, &mut names);
            Some(names)
        }
        ResourceClause::Conditional { .. } | ResourceClause::Iterated(_) => None,
    }
}

/// The parameter values lowering `resource` reads.
fn resource_clause_parameter_values(
    resource: &ResourceClause,
    parameter_binding: ParameterBinding<'_>,
) -> Result<ProgramValueBindings, ClickError> {
    match resource_clause_referenced_names(resource) {
        Some(names) => parameter_values_named(parameter_binding, &names),
        None => parameter_values(parameter_binding),
    }
}

pub(in crate::surface) fn array_refs_for_parameters(
    parameters: &[crate::languages::interface::ImportedParameter],
    values: &ProgramValueBindings,
    point: &crate::kernel::ProgramPoint,
) -> ClickArrayRefs {
    crate::instrumentation::record_deterministic_work(parameters.len());
    parameters
        .iter()
        .filter_map(|parameter| {
            let element_type = click_array_element_type(parameter.interface_type())?;
            let Some(ProgramValue::Pointer(pointer)) = values.get(parameter.name()) else {
                return None;
            };
            Some((
                parameter.name().to_string(),
                ClickArrayRef {
                    point: point.clone(),
                    pointer: pointer.address().clone(),
                    element_type,
                },
            ))
        })
        .collect()
}

/// Capturing an argument preserves only its reference, never its current fields
/// or ownership. The retained scope also contains already transferred instances.
pub(in crate::surface) fn lower_resource_reference_arguments(
    resource: &ResourceClause,
    state: &ExecutionState,
) -> Result<Vec<crate::kernel::ResourceReference>, ClickError> {
    let ResourceClause::Declared {
        resource_arguments, ..
    } = resource
    else {
        return Ok(Vec::new());
    };
    resource_arguments
        .iter()
        .map(|binding| {
            crate::instrumentation::record_deterministic_work(1);
            state
                .resource_instance_fields(binding.identity)
                .map(crate::kernel::ResourceReference::from_instance)
                .ok_or_else(|| {
                    ClickError::new(format!("Requires resource reference `{}`", binding.name))
                })
        })
        .collect()
}

#[cfg(test)]
mod input_identity_tests {
    use super::*;

    #[test]
    fn pointer_input_names_are_stable_and_function_specific() {
        let first = input_scope("input-identity-first");
        let second = input_scope("input-identity-second");
        assert_eq!(
            input_pointer_variable(first, 0).unwrap(),
            input_pointer_variable(input_scope("input-identity-first"), 0).unwrap()
        );
        assert_ne!(
            input_pointer_variable(first, 0).unwrap(),
            input_pointer_variable(first, 1).unwrap()
        );
        assert_ne!(
            input_pointer_variable(first, 0).unwrap(),
            input_pointer_variable(second, 0).unwrap()
        );
    }

    #[test]
    fn input_names_ignore_allocation_history_and_cover_large_parameter_lists() {
        let expected = (0..130)
            .map(|index| input_pointer_variable(input_scope("stable-target"), index).unwrap())
            .collect::<Vec<_>>();
        for order in [vec![0, 1, 2, 3], vec![3, 1, 0, 2]] {
            reset_input_identities();
            for function in order {
                for index in 0..130 {
                    input_pointer_variable(input_scope(&format!("unrelated-{function}")), index)
                        .unwrap();
                }
            }
            let actual = (0..130)
                .map(|index| input_pointer_variable(input_scope("stable-target"), index).unwrap())
                .collect::<Vec<_>>();
            assert_eq!(actual, expected);
            assert_eq!(
                actual
                    .iter()
                    .collect::<std::collections::HashSet<_>>()
                    .len(),
                130
            );
            assert!(
                actual
                    .iter()
                    .all(|v| (INPUT_VARIABLE_BASE..INPUT_VARIABLE_CEILING).contains(&v.0))
            );
        }
    }

    #[test]
    fn input_identity_collisions_fail_without_aliasing_or_renumbering() {
        reset_input_identities();
        let scope = input_scope("collision-target");
        let variable = input_pointer_variable(scope, 0).unwrap();
        INPUT_VARIABLES.with(|variables| variables.borrow_mut().clear());
        INPUT_VARIABLE_OWNERS.with(|owners| owners.borrow_mut().insert(variable, (scope, 1)));
        assert!(
            input_pointer_variable(scope, 0)
                .unwrap_err()
                .message()
                .contains("identity collision")
        );
        assert!(INPUT_VARIABLES.with(|variables| variables.borrow().is_empty()));
        reset_input_identities();
        assert_eq!(
            input_pointer_variable(input_scope("collision-target"), 0).unwrap(),
            variable
        );
    }

    #[cfg(test)]
    mod scaling_tests {
        include!("../../scaling_tests/surface/lowering/resource_lowering/input_identity_tests.rs");
    }
}
