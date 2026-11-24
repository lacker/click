//! Checking that a function refines a named contract: the refinement theorem's statement, the entry and implementation states, and the resource instances both sides are compared on.

use super::*;

/// Prints the explicit refinement theorem that automatic formation could not
/// replace, with every slot filled from the two declarations the check read.
///
/// The skeleton is the expand affordance of the automatic route. It is built
/// from the same `FunctionContract` and `ProgramFunction` interfaces the check
/// uses — the target's proof parameters, the implementation's binders, and
/// the implementation's C parameter list — so the printed obligation cannot
/// drift from the one that was refused. A target with no proof parameters
/// gets the `unfold(Name(&function))` form, which is the route that already exists.
///
/// `declared_parameter_spellings` carries, per parameter position, the C
/// spelling the caller's source declaration uses where this interface cannot
/// reconstruct it: an aggregate pointer is a layout here, not a struct tag,
/// so `struct node*` would print as the pointer type it is modeled by. The
/// caller supplies the tag rather than the kernel storing one; a position
/// without a supplied spelling keeps this interface's own.
pub(in crate::kernel) fn named_contract_refinement_theorem_skeleton(
    contract: &FunctionContract,
    function: &ProgramFunction,
    declared_parameter_spellings: &[Option<String>],
) -> String {
    let theorem = format!(
        "{}_is_{}",
        function.name(),
        snake_case_contract_name(contract.name())
    );
    let parameters = function
        .parameters()
        .iter()
        .enumerate()
        .map(|(index, parameter)| {
            let spelling = declared_parameter_spellings
                .get(index)
                .and_then(Option::as_deref)
                .map(str::to_string)
                .unwrap_or_else(|| program_parameter_type_spelling(parameter));
            format!("{spelling} {}", parameter.name())
        })
        .collect::<Vec<_>>()
        .join(", ");
    let target_binders = declared_instance_binder_names(&[contract.proof_parameters()]);
    if target_binders.is_empty() {
        return format!(
            "theorem {theorem}() {{\n    \
             ensures {contract}(&{function}) by {{\n        \
             unfold({contract}(&{function}));\n        \
             close();\n    \
             }}\n\
             }}",
            contract = contract.name(),
            function = function.name(),
        );
    }
    let implementation_binders = declared_instance_binder_names(&[
        function.resource_requires(),
        function.resource_ensures(),
    ]);
    let introduced =
        introduced_instance_names(target_binders.len().max(implementation_binders.len()));
    let map = |binders: &[String]| {
        binders
            .iter()
            .zip(&introduced)
            .map(|(binder, name)| format!("{binder}: {name}"))
            .collect::<Vec<_>>()
            .join(", ")
    };
    let aliases: BTreeMap<_, _> = implementation_binders
        .iter()
        .zip(&introduced)
        .map(|(binder, name)| (binder.as_str(), name.as_str()))
        .collect();
    let inputs = declared_instance_binder_names(&[function.resource_requires()]);
    let outputs = function
        .resource_ensures()
        .iter()
        .filter(|spec| spec.role() == ResourceTransferRole::Produce)
        .filter_map(|spec| spec.instance_binder())
        .collect::<Vec<_>>();
    let input_map = inputs
        .iter()
        .map(|binder| format!("{binder}: {}", aliases[binder.as_str()]))
        .collect::<Vec<_>>()
        .join(", ");
    let output_map = outputs
        .iter()
        .map(|binder| format!("{binder}: {}", aliases[binder]))
        .collect::<Vec<_>>()
        .join(", ");
    let binding = if outputs.is_empty() {
        String::new()
    } else {
        format!("let {{ {output_map} }} = ")
    };
    format!(
        "theorem {theorem}() executes {function}({parameters}) {{\n    \
         ensures {contract}(&{function}) as {{ {target} }} by {{\n        \
         {binding}step({function}, {{ {input_map} }});\n        \
         close();\n    \
         }}\n\
         }}",
        contract = contract.name(),
        function = function.name(),
        target = map(&target_binders),
        binding = binding,
        input_map = input_map,
    )
}

/// The binder spellings a declaration introduces, in declaration order, once
/// per identity.
pub(super) fn declared_instance_binder_names(specs: &[&[ResourceSpec]]) -> Vec<String> {
    let mut seen = BTreeSet::new();
    let mut names = Vec::new();
    for spec in specs.iter().flat_map(|specs| specs.iter()) {
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        if seen.insert(identity) {
            names.push(spec.instance_binder().unwrap_or_default().to_string());
        }
    }
    names
}

/// Fresh names for the instances the theorem introduces. One instance is
/// `r`; several are numbered so the two maps can name the same instance.
pub(super) fn introduced_instance_names(count: usize) -> Vec<String> {
    if count == 1 {
        return vec!["r".to_string()];
    }
    (1..=count).map(|index| format!("r{index}")).collect()
}

pub(super) fn snake_case_contract_name(name: &str) -> String {
    let mut snake = String::with_capacity(name.len() + 4);
    for (index, character) in name.char_indices() {
        if character.is_uppercase() && index != 0 {
            snake.push('_');
        }
        snake.extend(character.to_lowercase());
    }
    snake
}

/// The C spelling of a parameter's declared type.
///
/// Struct tags are not part of the kernel interface: an aggregate parameter
/// keeps its layout, not the tag its source wrote, so a pointer to one is
/// spelled by its pointer type. The skeleton is source the user edits, and
/// this is the one slot they may have to correct.
pub(super) fn program_parameter_type_spelling(parameter: &ProgramParameter) -> String {
    let base = program_type_spelling(parameter.program_type());
    if parameter.pointee_is_constant() {
        format!("const {base}")
    } else {
        base.to_string()
    }
}

/// The C spelling of a kernel C type, for a diagnostic that has to say what
/// type a value had. An aggregate pointer is spelled by its pointer type, as
/// [`program_parameter_type_spelling`] explains.
pub(crate) fn program_type_spelling(program_type: ProgramType) -> &'static str {
    match program_type {
        ProgramType::Parameter(name) => name.name(),
        ProgramType::ParameterPointer(name) => {
            crate::kernel::TypeParameterName::intern(&format!("{}*", name.name())).name()
        }
        ProgramType::Void => "void",
        ProgramType::Bool => "bool",
        ProgramType::VoidPointer => "void*",
        ProgramType::VoidPointerPointer => "void**",
        // Click's untyped pointer is not a C type; it has Click's spelling.
        ProgramType::Pointer => "Pointer",
        ProgramType::Int8 => "int8",
        ProgramType::Int16 => "int16",
        ProgramType::Int32 => "int32",
        ProgramType::UInt8 => "uint8",
        ProgramType::UInt16 => "uint16",
        ProgramType::UInt32 => "uint32",
        ProgramType::Int64 => "int64",
        ProgramType::UInt64 => "uint64",
        ProgramType::Int128 => "int128",
        ProgramType::UInt128 => "uint128",
        ProgramType::Float32 => "float32",
        ProgramType::Float64 => "float64",
        ProgramType::Int8Pointer => "int8*",
        ProgramType::Int16Pointer => "int16*",
        ProgramType::UInt16Pointer => "uint16*",
        ProgramType::Int32Pointer => "int32*",
        ProgramType::UInt8Pointer => "uint8*",
        ProgramType::UInt32Pointer => "uint32*",
        ProgramType::Int64Pointer => "int64*",
        ProgramType::Int128Pointer => "int128*",
        ProgramType::UInt64Pointer => "uint64*",
        ProgramType::UInt128Pointer => "uint128*",
        ProgramType::Float32Pointer => "float32*",
        ProgramType::Float64Pointer => "float64*",
        ProgramType::Int8PointerPointer => "int8**",
        ProgramType::Int16PointerPointer => "int16**",
        ProgramType::UInt16PointerPointer => "uint16**",
        ProgramType::Int32PointerPointer => "int32**",
        ProgramType::UInt8PointerPointer => "uint8**",
        ProgramType::UInt32PointerPointer => "uint32**",
        ProgramType::Int64PointerPointer => "int64**",
        ProgramType::Int128PointerPointer => "int128**",
        ProgramType::UInt64PointerPointer => "uint64**",
        ProgramType::UInt128PointerPointer => "uint128**",
        ProgramType::Float32PointerPointer => "float32**",
        ProgramType::Float64PointerPointer => "float64**",
        ProgramType::FunctionPointer(_) => "void (*)()",
        ProgramType::Int8Array(_) => "int8*",
        ProgramType::Int16Array(_) => "int16*",
        ProgramType::Int32Array(_) => "int32*",
        ProgramType::UInt8Array(_) => "uint8*",
        ProgramType::UInt16Array(_) => "uint16*",
        ProgramType::UInt32Array(_) => "uint32*",
        ProgramType::Int64Array(_) => "int64*",
        ProgramType::Int128Array(_) => "int128*",
        ProgramType::UInt64Array(_) => "uint64*",
        ProgramType::UInt128Array(_) => "uint128*",
        ProgramType::Float32Array(_) => "float32*",
        ProgramType::Float64Array(_) => "float64*",
        ProgramType::PointerArray(element, _) => element.decayed_type_spelling(),
    }
}

/// Proves behavioral callback refinement. Exact matching remains the fast
/// path. The semantic path checks framed memory, abstract-token, and folded
/// composite resource transitions and effect containment, instantiates both
/// interfaces with the same symbolic arguments, then checks preconditions
/// contravariantly and postconditions covariantly. Concrete resource needs and
/// mutable ranges may be narrower than the named contract's upper bounds.
/// Stateful refinement is deliberately limited to memory propositions backed
/// by a nonempty resource transition and unguarded named mutable footprint.
pub(in crate::kernel) fn function_refines_named_contract(
    contract: &FunctionContract,
    function: &ProgramFunction,
    object_type_requirements: &ObjectTypeRequirements,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    function_refines_named_contract_reporting(
        contract,
        function,
        object_type_requirements,
        budget,
        None,
    )
}

pub(in crate::kernel) fn function_refines_named_contract_reporting(
    contract: &FunctionContract,
    function: &ProgramFunction,
    object_type_requirements: &ObjectTypeRequirements,
    budget: &mut ExecutionBudget,
    unproved_requirement: Option<&mut Option<usize>>,
) -> ExecutionResult<bool> {
    if object_type_requirements.is_empty() && contract.exactly_matches(function) {
        return Ok(true);
    }
    if !contract.has_same_predicate_unfoldings(function) {
        return Ok(false);
    }
    let Some(mut context) =
        prepare_automatic_contract_refinement_context(contract, function, budget)
    else {
        return Ok(false);
    };
    context.object_type_requirements = object_type_requirements.clone();
    function_refines_named_contract_in_case(
        &context,
        &[],
        false,
        None,
        budget,
        unproved_requirement,
    )
}

/// Whether `source`, a named contract a fact fixed, implements `contract`.
/// It is the automatic route of an explicit contract-to-contract refinement
/// theorem, with the source's value parameters bound to the fact's values.
/// The values are the caller's terms, so the caller's facts about them hold.
pub(super) fn contract_refines_contract(
    contract: &FunctionContract,
    source: &FunctionContract,
    caller_facts: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<bool> {
    if contract.name() == source.name() && contract.value_arguments() == source.value_arguments() {
        return Ok(true);
    }
    let target = contract.interface();
    let implementation = source.interface();
    if !source.proof_parameters().is_empty()
        || target.predicate_unfoldings() != implementation.predicate_unfoldings()
        || !target.has_compatible_signature_and_composite_vocabulary(implementation)
    {
        return Ok(false);
    }
    let Some(mut context) =
        contract_refinement_context_for_interface(contract, source.name(), implementation, budget)
    else {
        return Ok(false);
    };
    context.function_value_arguments = source.value_arguments().to_vec();
    function_refines_named_contract_in_case(&context, &[], false, Some(caller_facts), budget, None)
}

pub(in crate::kernel) fn prepare_function_contract_refinement_context(
    contract: &FunctionContract,
    function: &ProgramFunction,
    budget: &mut ExecutionBudget,
) -> Option<FunctionContractRefinementContext> {
    if !contract.has_compatible_signature_and_resource_vocabulary(function) {
        return None;
    }
    contract_refinement_context_for_checked_interfaces(contract, function, budget)
}

/// The concrete-pointer formation route's context.
///
/// It differs from the explicit route only in admitting a target that
/// declares proof parameters. The instances those parameters stand for are
/// introduced by [`function_refines_named_contract_in_case`], and only when
/// the binding between the two declarations is forced.
pub(super) fn prepare_automatic_contract_refinement_context(
    contract: &FunctionContract,
    function: &ProgramFunction,
    budget: &mut ExecutionBudget,
) -> Option<FunctionContractRefinementContext> {
    if !contract.has_compatible_signature_and_composite_vocabulary(function) {
        return None;
    }
    contract_refinement_context_for_checked_interfaces(contract, function, budget)
}

pub(super) fn contract_refinement_context_for_checked_interfaces(
    contract: &FunctionContract,
    function: &ProgramFunction,
    budget: &mut ExecutionBudget,
) -> Option<FunctionContractRefinementContext> {
    contract_refinement_context_for_interface(
        contract,
        function.name(),
        function.contract_interface(),
        budget,
    )
}

pub(in crate::kernel) fn contract_refinement_context_for_interface(
    contract: &FunctionContract,
    function_name: &str,
    function_interface: &FunctionContractInterface,
    budget: &mut ExecutionBudget,
) -> Option<FunctionContractRefinementContext> {
    let mut argument_values = Vec::with_capacity(function_interface.parameters().len());
    for (index, parameter) in function_interface.parameters().iter().enumerate() {
        let variable = budget.allocate_kernel_variable().ok()?;
        argument_values.push(
            symbolic_call_result(parameter.program_type(), variable)
                .complete_word(Address::symbolic(variable))
                .with_pointer_object_class(
                    contract
                        .interface()
                        .object_type_requirements()
                        .get(&index)
                        .cloned(),
                ),
        );
    }
    let result_variable = budget.allocate_kernel_variable().ok()?;
    // A contract not fixed by a fact holds for arbitrary values of its value
    // parameters.
    let contract =
        if contract.value_arguments().len() == contract.interface().value_parameters().len() {
            contract.clone()
        } else {
            let mut values = Vec::new();
            for parameter in contract.interface().value_parameters() {
                let variable = budget.allocate_kernel_variable().ok()?;
                values.push(symbolic_call_result(parameter.program_type(), variable));
            }
            contract.instantiated(&values)?
        };
    let pointer_type = contract.function_pointer_type();
    Some(FunctionContractRefinementContext {
        object_type_requirements: function_interface.object_type_requirements().clone(),
        contract,
        function_interface: function_interface.clone(),
        function_name: function_name.to_string(),
        pointer: Pointer::new(
            Address {
                base: AddressBase::Function(function_name.to_string()),
                offset: AddressOffset::Constant(0),
            },
            pointer_type,
        ),
        source_contract: None,
        function_value_arguments: Vec::new(),
        argument_values,
        result_variable,
        next_kernel_variable: budget.next_kernel_variable(),
    })
}

pub(in crate::kernel) fn function_contract_refinement_entry_state(
    context: &FunctionContractRefinementContext,
) -> ExecutionState {
    let mut state = with_contract_interface_argument_views(
        &ExecutionState::new().with_population_creation_tracking(),
        &context.contract.interface,
        &context.argument_values,
    );
    for (parameter, value) in context
        .contract
        .interface
        .value_parameters()
        .iter()
        .zip(context.contract.value_arguments())
    {
        state.locals.set_typed_with_all_qualifiers(
            parameter.name().to_string(),
            value.clone(),
            parameter.program_type(),
            false,
            false,
            false,
            false,
        );
    }
    state
}

/// The implementation side's entry frame: the shared arguments, and the
/// values its fact fixed for its own value parameters.
pub(super) fn function_contract_refinement_implementation_state(
    context: &FunctionContractRefinementContext,
) -> ExecutionState {
    let mut state = with_contract_interface_argument_views(
        &ExecutionState::new().with_population_creation_tracking(),
        &context.function_interface,
        &context.argument_values,
    );
    for (parameter, value) in context
        .function_interface
        .value_parameters()
        .iter()
        .zip(&context.function_value_arguments)
    {
        state.locals.set_typed_with_all_qualifiers(
            parameter.name().to_string(),
            value.clone(),
            parameter.program_type(),
            false,
            false,
            false,
            false,
        );
    }
    state
}

pub(in crate::kernel) fn prepare_contract_refinement_obligations(
    context: &FunctionContractRefinementContext,
) -> Result<FunctionContractRefinementObligations, ContractRefinementPreparationError> {
    use ContractRefinementPreparationError as Refusal;
    let target = context.contract.interface();
    let source = &context.function_interface;
    // The theorem's obligation states the normal outcome only; a source that
    // may throw owes its exceptional guarantees too, which it does not
    // carry yet, so that refinement is left to the automatic route.
    if !source.exceptional_signature().is_empty() {
        return Err(Refusal::Unsupported(
            "the source contract may throw, and explicit refinement theorems only support normal returns".to_owned(),
        ));
    }
    let mut budget = ExecutionBudget::continuing_from(context.next_kernel_variable);
    let entry = function_contract_refinement_entry_state(context);
    let source_entry = function_contract_refinement_implementation_state(context);
    let mut assumptions = PureFactContext::new();
    if !assume_contract_propositions(
        &entry,
        &entry,
        target.contract_requires(),
        &mut assumptions,
        &mut budget,
    )? {
        return Err(Refusal::evaluating("the target contract's preconditions"));
    }
    let mut type_arguments = context.argument_values.clone();
    if crate::kernel::object_types::check_requirements(
        &context.function_name,
        source.parameters(),
        &context.object_type_requirements,
        &mut type_arguments,
        entry.memory(),
        &assumptions,
    )
    .is_some()
    {
        return Err(Refusal::Incompatible(
            "the target contract's preconditions do not establish the object bounds required by the source contract",
        ));
    }
    // A single conservative post memory covers every possible source write.
    // This does not enumerate guard combinations or assert that a guarded
    // write happened. Resource/effect containment is checked independently.
    let ranges = evaluate_contract_mutable_ranges_for_interface(
        source,
        &source_entry,
        &assumptions,
        &mut budget,
        false,
    )?
    .ok_or_else(|| Refusal::evaluating("the source contract's allowed write ranges"))?;
    let memory = entry.memory().clone().with_call_memory_havoc(
        budget.allocate_kernel_variable()?,
        &ranges,
        &assumptions,
        None,
    );
    let result = symbolic_call_result(source.return_type(), context.result_variable);
    let mut post = entry.clone().with_memory(memory);
    // The post memory is a step from `entry`: the source's post stands there.
    let mut source_post = source_entry.clone().with_memory_of(&post);
    if source.return_type() != ProgramType::Void {
        set_contract_result(&mut post, target, result.clone());
        set_contract_result(&mut source_post, source, result);
    }
    check_refinement_interfaces(
        target,
        source,
        &entry,
        &source_entry,
        &post,
        &source_post,
        &assumptions,
        &mut budget,
    )?;
    fn conjunction(items: Vec<Proposition>) -> Proposition {
        items
            .into_iter()
            .reduce(|a, b| Proposition::And(Box::new(a), Box::new(b)))
            .unwrap_or(Proposition::condition_is(
                ConditionTerm::Constant(true),
                true,
            ))
    }
    fn lower(
        interface: &FunctionContractInterface,
        specs: &[SpecProposition],
        state: &ExecutionState,
        entry: &ExecutionState,
        clause: &'static str,
        budget: &mut ExecutionBudget,
    ) -> Result<Proposition, ContractRefinementPreparationError> {
        let definitions = interface
            .predicate_unfoldings()
            .iter()
            .map(|definition| (definition.body(), definition.predicate()))
            .collect::<BTreeMap<_, _>>();
        let mut propositions = Vec::new();
        for spec in specs {
            let spec = definitions.get(spec).copied().unwrap_or(spec);
            // Each clause is its own term, so a clause both callback contracts
            // state lowers identically, inline `match` binders included.
            let paths = budget.with_match_binders_from_base(|budget| {
                lower_spec_proposition_at_state_with_loop_entry(
                    state,
                    spec,
                    Some(entry),
                    &PureFactContext::new(),
                    budget,
                )
            })?;
            let [path] = paths.as_slice() else {
                return Err(Refusal::evaluating(clause));
            };
            // Lowering facts name reads and other definitional intermediates;
            // they are not clauses of either callback contract. Both sides
            // use the same kernel load identities in these fixed memories.
            propositions.extend(
                path.obligations
                    .iter()
                    .map(|obligation| obligation.proposition().clone()),
            );
            propositions.push(path.proposition.clone());
        }
        Ok(conjunction(propositions))
    }
    let target_requires = lower(
        target,
        target.contract_requires(),
        &entry,
        &entry,
        "the target contract's preconditions",
        &mut budget,
    )?;
    let source_requires = lower(
        source,
        source.contract_requires(),
        &source_entry,
        &source_entry,
        "the source contract's preconditions",
        &mut budget,
    )?;
    let source_ensures = lower(
        source,
        source.contract_ensures(),
        &source_post,
        &source_entry,
        "the source contract's postconditions",
        &mut budget,
    )?;
    let target_ensures = lower(
        target,
        target.contract_ensures(),
        &post,
        &entry,
        "the target contract's postconditions",
        &mut budget,
    )?;
    let proposition = Proposition::Implies(
        Box::new(target_requires),
        Box::new(Proposition::And(
            Box::new(source_requires),
            Box::new(Proposition::Implies(
                Box::new(source_ensures),
                Box::new(target_ensures),
            )),
        )),
    );
    Ok(FunctionContractRefinementObligations {
        context: context.clone(),
        entry,
        post,
        proposition,
    })
}

/// One forced pair of resource declarations: a target contract proof
/// parameter and the implementation binder that must stand for it. Both sides
/// read the same instance identity, so `root.model` on the named side and
/// `t.model` on the implementation side lower to the same term.
pub(super) struct RefinementInstanceBinding {
    target_identity: InstanceId,
    implementation_identity: InstanceId,
    entry: ResourceInstance,
    post: ResourceInstance,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum RefinementSide {
    Target,
    Implementation,
}

#[derive(Clone, Copy, Eq, PartialEq)]
pub(super) enum RefinementPhase {
    Entry,
    Post,
}

/// One declared instance binder, with its family evaluated at the state that
/// declares it.
pub(super) struct DeclaredResourceInstance {
    identity: InstanceId,
    family: String,
    schema: ResourceFieldSchema,
    arguments: ResourceArguments,
}

/// Collects the instance binders a declaration names, in declaration order,
/// once per identity. `owns` states the same binder in `requires` and
/// `ensures`; the pair is one binder, not two.
pub(super) fn evaluate_declared_resource_instances(
    specs: &[&[ResourceSpec]],
    state: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<DeclaredResourceInstance>>> {
    let mut seen = BTreeSet::new();
    let mut declared = Vec::new();
    for spec in specs.iter().flat_map(|specs| specs.iter()) {
        if !spec.resource_arguments().is_empty() {
            return Ok(None);
        }
        let Some(identity) = spec.instance_identity() else {
            continue;
        };
        if !seen.insert(identity) {
            continue;
        }
        let Some(schema) = spec.instance_schema() else {
            continue;
        };
        let Some(resource) = spec.instance_resource_spec() else {
            continue;
        };
        let instance = match evaluate_function_resource_spec(state, &resource, assumptions, budget)?
        {
            Ok(ResourceFact::Own(Resource::Composite { name, arguments }, quantity))
                if quantity.as_const() == Some(1) =>
            {
                DeclaredResourceInstance {
                    identity,
                    family: name,
                    schema: schema.clone(),
                    arguments,
                }
            }
            Ok(_) | Err(_) => return Ok(None),
        };
        declared.push(instance);
    }
    Ok(Some(declared))
}

/// Indexes declared binders by resource family. A family that appears twice
/// on one side leaves the binding unforced, so its entry is poisoned rather
/// than ranked.
pub(super) fn index_declared_instances_by_family(
    declared: &[DeclaredResourceInstance],
) -> Option<BTreeMap<&str, &DeclaredResourceInstance>> {
    let mut index = BTreeMap::new();
    for instance in declared {
        if index.insert(instance.family.as_str(), instance).is_some() {
            return None;
        }
    }
    Some(index)
}

/// Pairs the target contract's proof parameters with the implementation's
/// binders when exactly one pairing is possible, and instantiates one shared
/// instance per pair.
///
/// The pairing is a map lookup per binder: each side is indexed by resource
/// family once, a repeated family on either side refuses, and the two indexes
/// must have the same keys. No candidate is searched, scored, or preferred.
///
/// Each pair gets one entry instance with arbitrary fields, shared by both
/// entry states, and one post instance with fresh arbitrary fields, shared by
/// both post states. Fresh post fields are the same rule an ordinary call
/// applies to returned ownership: the identity survives, the field values do
/// not, and only the implementation's guarantees relate the two.
pub(super) fn forced_refinement_instance_bindings(
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
    contract_entry: &ExecutionState,
    function_entry: &ExecutionState,
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<RefinementInstanceBinding>>> {
    let Some(target) = evaluate_declared_resource_instances(
        &[contract.proof_parameters()],
        contract_entry,
        assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    let Some(implementation) = evaluate_declared_resource_instances(
        &[function.resource_requires(), function.resource_ensures()],
        function_entry,
        assumptions,
        budget,
    )?
    else {
        return Ok(None);
    };
    if target.is_empty() && implementation.is_empty() {
        return Ok(Some(Vec::new()));
    }
    let (Some(target_index), Some(implementation_index)) = (
        index_declared_instances_by_family(&target),
        index_declared_instances_by_family(&implementation),
    ) else {
        return Ok(None);
    };
    if target_index.len() != implementation_index.len() {
        return Ok(None);
    }
    let mut bindings = Vec::with_capacity(target_index.len());
    for (family, target) in &target_index {
        let Some(implementation) = implementation_index.get(family) else {
            return Ok(None);
        };
        if target.schema != implementation.schema
            || target.arguments.len() != implementation.arguments.len()
            || !target
                .arguments
                .iter()
                .zip(implementation.arguments.iter())
                .all(|(left, right)| {
                    crate::kernel::resource_field_values_proven_equal(left, right, assumptions)
                })
        {
            return Ok(None);
        }
        let identity = budget.allocate_instance_identity()?;
        let instance = |budget: &mut ExecutionBudget| -> ExecutionResult<ResourceInstance> {
            let fields = arbitrary_resource_instance_fields(
                &target.schema,
                ModelFieldMintSite {
                    identity,
                    minted_by: &ModelMint::Refinement,
                },
                budget,
            )?;
            Ok(ResourceInstance::new(
                identity,
                target.family.clone(),
                target.arguments.clone(),
                target.schema.clone(),
                fields,
            )
            .expect("arbitrary fields have their declared types"))
        };
        bindings.push(RefinementInstanceBinding {
            target_identity: target.identity,
            implementation_identity: implementation.identity,
            entry: instance(budget)?,
            post: instance(budget)?,
        });
    }
    Ok(Some(bindings))
}

/// The bindings with each post instance at the arguments its declarations
/// read in the post states.
///
/// A binder whose arguments read memory the call may change, `owns state:
/// boxed(self.item)`, holds the instance at the field's value after the
/// call, as a call's returned instance is. Both sides must read arguments
/// proven equal there; a side that does not produce the binder leaves the
/// entry's arguments.
#[allow(clippy::type_complexity)]
pub(super) fn refinement_bindings_at_post(
    bindings: &[RefinementInstanceBinding],
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
    (contract_entry, contract_post): (&ExecutionState, &ExecutionState),
    (function_entry, function_post): (&ExecutionState, &ExecutionState),
    assumptions: &PureFactContext,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<Option<Vec<RefinementInstanceBinding>>> {
    let post_arguments = |interface: &FunctionContractInterface,
                          identity: InstanceId,
                          entry: &ExecutionState,
                          post: &ExecutionState,
                          budget: &mut ExecutionBudget|
     -> ExecutionResult<Option<Option<ResourceArguments>>> {
        let Some(resource) = interface
            .resource_ensures()
            .iter()
            .find(|spec| spec.instance_identity() == Some(identity))
            .and_then(ResourceSpec::instance_resource_spec)
        else {
            return Ok(Some(None));
        };
        Ok(
            match evaluate_function_resource_spec_with_entry(
                entry,
                post,
                &resource,
                assumptions,
                budget,
            )? {
                Ok(ResourceFact::Own(Resource::Composite { arguments, .. }, quantity))
                    if quantity.as_const() == Some(1) =>
                {
                    Some(Some(arguments))
                }
                Ok(_) | Err(_) => None,
            },
        )
    };
    let mut at_post = Vec::with_capacity(bindings.len());
    for binding in bindings {
        let Some(target) = post_arguments(
            contract,
            binding.target_identity,
            contract_entry,
            contract_post,
            budget,
        )?
        else {
            return Ok(None);
        };
        let Some(implementation) = post_arguments(
            function,
            binding.implementation_identity,
            function_entry,
            function_post,
            budget,
        )?
        else {
            return Ok(None);
        };
        let arguments = match (target, implementation) {
            (Some(target), Some(implementation)) => {
                if target.len() != implementation.len()
                    || !target
                        .iter()
                        .zip(implementation.iter())
                        .all(|(left, right)| {
                            crate::kernel::resource_field_values_proven_equal(
                                left,
                                right,
                                assumptions,
                            )
                        })
                {
                    return Ok(None);
                }
                target
            }
            (Some(arguments), None) | (None, Some(arguments)) => arguments,
            (None, None) => binding.post.arguments().into(),
        };
        let post = &binding.post;
        let Some(post) = ResourceInstance::new(
            post.identity(),
            post.name().to_string(),
            arguments,
            post.schema().clone(),
            post.fields().into(),
        ) else {
            return Ok(None);
        };
        at_post.push(RefinementInstanceBinding {
            target_identity: binding.target_identity,
            implementation_identity: binding.implementation_identity,
            entry: binding.entry.clone(),
            post,
        });
    }
    Ok(Some(at_post))
}

/// An arbitrary model field of `field_type` named by `variable`.
pub(in crate::kernel) fn resource_instance_field_value(
    field_type: &ResourceFieldType,
    variable: Variable,
) -> AlgebraicValue {
    match field_type {
        ResourceFieldType::Integer => AlgebraicValue::Integer(IntegerTerm::Variable(variable)),
        ResourceFieldType::Program(program_type) => {
            AlgebraicValue::Program(symbolic_call_result(*program_type, variable))
        }
        ResourceFieldType::Algebraic(algebraic_type) => AlgebraicValue::Algebraic(AlgebraicTerm {
            algebraic_type: algebraic_type.clone(),
            node: AlgebraicTermNode::Variable(variable),
        }),
    }
}

/// Which instance's model is being replaced, and why. Carried to the two
/// field-minting funnels below so each fresh variable is registered as what it
/// is: a refusal that meets one later has no other way to find out
/// (`crate::kernel::model_fields`).
pub(in crate::kernel) struct ModelFieldMintSite<'a> {
    pub(in crate::kernel) identity: InstanceId,
    pub(in crate::kernel) minted_by: &'a ModelMint,
}

/// Registers the fields just minted for one instance. One insert per field,
/// beside the allocation that produced it, so this is bounded by the schema the
/// mint already walked.
pub(super) fn register_minted_model_fields(
    schema: &ResourceFieldSchema,
    site: &ModelFieldMintSite<'_>,
    fields: &[AlgebraicValue],
) {
    for (field_index, ((name, _), value)) in schema.fields().iter().zip(fields).enumerate() {
        let Some(variable) = algebraic_value_variable(value) else {
            continue;
        };
        crate::kernel::model_fields::register_model_field_variable(
            variable,
            ModelFieldOrigin {
                identity: site.identity,
                field: std::sync::Arc::from(name.as_str()),
                field_index,
                minted_by: site.minted_by.clone(),
            },
        );
    }
}

/// An arbitrary model for one instance, drawn through `variables` so the
/// fields avoid everything that stream reserves as well as everything else
/// the budget has issued.
pub(in crate::kernel) fn fresh_resource_instance_fields(
    schema: &ResourceFieldSchema,
    site: ModelFieldMintSite<'_>,
    variables: &mut KernelVariableGenerator,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<ResourceFieldValues> {
    let mut fields = Vec::with_capacity(schema.fields().len());
    for (_, field_type) in schema.fields() {
        fields.push(resource_instance_field_value(
            field_type,
            variables.next_in(budget)?,
        ));
    }
    register_minted_model_fields(schema, &site, &fields);
    Ok(ResourceFieldValues::from_minted(fields))
}

/// The arbitrary model a join gives one named interface instance, drawn from
/// the join's own fresh-variable counter. Returns the fields and the counter
/// after them. It depends on nothing but its arguments, so the proof side
/// and the kernel's check of the join arrive at the same fields.
pub(crate) fn interface_join_instance_fields(
    schema: &ResourceFieldSchema,
    identity: InstanceId,
    next_kernel_variable: u64,
) -> Option<(ResourceFieldValues, u64)> {
    let mut budget = ExecutionBudget::continuing_from(next_kernel_variable);
    let fields = arbitrary_resource_instance_fields(
        schema,
        ModelFieldMintSite {
            identity,
            minted_by: &ModelMint::Join,
        },
        &mut budget,
    )
    .ok()?;
    Some((fields, budget.next_kernel_variable()))
}

pub(in crate::kernel) fn arbitrary_resource_instance_fields(
    schema: &ResourceFieldSchema,
    site: ModelFieldMintSite<'_>,
    budget: &mut ExecutionBudget,
) -> ExecutionResult<ResourceFieldValues> {
    let mut fields = Vec::with_capacity(schema.fields().len());
    for (_, field_type) in schema.fields() {
        fields.push(resource_instance_field_value(
            field_type,
            budget.allocate_kernel_variable()?,
        ));
    }
    register_minted_model_fields(schema, &site, &fields);
    Ok(ResourceFieldValues::from_minted(fields))
}

/// Installs the shared instances one side reads, under the identities that
/// side's declaration wrote.
pub(super) fn state_with_refinement_instances(
    state: &ExecutionState,
    bindings: &[RefinementInstanceBinding],
    side: RefinementSide,
    phase: RefinementPhase,
    assumptions: &PureFactContext,
) -> Option<ExecutionState> {
    if bindings.is_empty() {
        return Some(state.clone());
    }
    let mut state = state.clone();
    let mut names = ResourceBindings::new();
    let mut facts = Vec::with_capacity(bindings.len());
    for binding in bindings {
        let declared = match side {
            RefinementSide::Target => binding.target_identity,
            RefinementSide::Implementation => binding.implementation_identity,
        };
        let instance = match phase {
            RefinementPhase::Entry => &binding.entry,
            RefinementPhase::Post => &binding.post,
        };
        names.insert_instance(declared, instance.identity());
        facts.push(ResourceFact::own(Resource::Instance(instance.clone())));
    }
    state.resource_bindings = Some(std::sync::Arc::new(names));
    state.resources = state
        .resources
        .clone()
        .try_compose_into_valid_context_delaying_normalization(facts, assumptions)
        .ok()?;
    Some(state)
}

pub(super) fn function_refines_named_contract_in_case(
    context: &FunctionContractRefinementContext,
    case_assumptions: &[Proposition],
    explicit_case: bool,
    caller_facts: Option<&PureFactContext>,
    budget: &mut ExecutionBudget,
    unproved_requirement: Option<&mut Option<usize>>,
) -> ExecutionResult<bool> {
    let contract = &context.contract;
    let function_interface = &context.function_interface;
    let contract_interface = contract.interface();
    if !predicate_interfaces_are_explicitly_compatible(contract_interface, function_interface) {
        return Ok(false);
    }
    let mut propositions = contract_interface
        .contract_requires()
        .iter()
        .chain(contract_interface.contract_ensures())
        .chain(function_interface.contract_requires())
        .chain(function_interface.contract_ensures());
    let state_independent = propositions
        .clone()
        .all(spec_proposition_is_state_independent);
    let supported_syntax = propositions.all(spec_proposition_supports_stateful_memory_refinement);
    let supported_stateful_memory = !state_independent
        && !contract_interface.resource_requires().is_empty()
        && !contract_interface.resource_ensures().is_empty()
        && (!contract_interface.contract_mutable().is_empty()
            || contract_interface.resource_derived_mutable_frame())
        && supported_syntax;
    if !state_independent && !supported_stateful_memory {
        return Ok(false);
    }

    let contract_frame = function_contract_refinement_entry_state(context);
    let function_frame = function_contract_refinement_implementation_state(context);
    // Resource arguments are written over the two parameter lists, which the
    // views above already bind, so the pairing is decided before either
    // contract's own requirements are assumed.
    let Some(mut instances) = forced_refinement_instance_bindings(
        contract_interface,
        function_interface,
        &contract_frame,
        &function_frame,
        &PureFactContext::new(),
        budget,
    )?
    else {
        return Ok(false);
    };
    let install = |state: &ExecutionState, instances: &[RefinementInstanceBinding], side, phase| {
        state_with_refinement_instances(state, instances, side, phase, &PureFactContext::new())
    };
    let (Some(contract_entry), Some(function_entry)) = (
        install(
            &contract_frame,
            &instances,
            RefinementSide::Target,
            RefinementPhase::Entry,
        ),
        install(
            &function_frame,
            &instances,
            RefinementSide::Implementation,
            RefinementPhase::Entry,
        ),
    ) else {
        return Ok(false);
    };
    // Value arguments fixed by facts are the caller's terms, and a pure
    // contract reads nothing else of the caller, so the caller's facts about
    // those terms hold here. A contract over memory would read the frames'
    // own memories, which those facts do not describe.
    let mut preconditions = match caller_facts {
        Some(facts) if state_independent => facts.clone(),
        _ => PureFactContext::new(),
    };
    if !assume_contract_propositions(
        &contract_entry,
        &contract_entry,
        contract_interface.contract_requires(),
        &mut preconditions,
        budget,
    )? {
        return Ok(false);
    }
    preconditions = assumptions_with_propositions(&preconditions, case_assumptions);
    let mut type_arguments = context.argument_values.clone();
    if crate::kernel::object_types::check_requirements(
        &context.function_name,
        function_interface.parameters(),
        &context.object_type_requirements,
        &mut type_arguments,
        contract_entry.memory(),
        &preconditions,
    )
    .is_some()
    {
        return Ok(false);
    }
    if let Some(index) = first_unproved_contract_proposition(
        &function_entry,
        &function_entry,
        function_interface.contract_requires(),
        &mut preconditions,
        budget,
    )? {
        if let Some(unproved_requirement) = unproved_requirement {
            *unproved_requirement = Some(index);
        }
        return Ok(false);
    }

    let post_memory = if state_independent {
        contract_entry.memory().clone()
    } else {
        let memory_variable = budget.allocate_kernel_variable()?;
        let mutable_ranges = if explicit_case {
            let Some(ranges) = evaluate_decided_contract_mutable_ranges_for_interface(
                function_interface,
                &function_entry,
                &preconditions,
                budget,
            )?
            else {
                return Ok(false);
            };
            ranges
        } else {
            let Some(ranges) = evaluate_contract_mutable_ranges_for_interface(
                contract_interface,
                &contract_entry,
                &preconditions,
                budget,
                true,
            )?
            else {
                return Ok(false);
            };
            ranges
        };
        contract_entry.memory().clone().with_call_memory_havoc(
            memory_variable,
            &mutable_ranges,
            &preconditions,
            None,
        )
    };
    let result = symbolic_contract_result(function_interface, context.result_variable);
    // The post states carry the post instances, so a guarantee written over
    // `t.model` reads the fields the call produced while `old(t.model)` still
    // reads the entry fields through the entry state passed alongside.
    // The post memory is a step from `contract_entry`; both frames stand
    // where that step reached, keeping their own locals.
    let post_source = contract_entry.clone().with_memory(post_memory);
    let contract_post_frame = contract_frame.clone().with_memory_of(&post_source);
    let function_post_frame = function_frame.clone().with_memory_of(&post_source);
    if !state_independent {
        let Some(at_post) = refinement_bindings_at_post(
            &instances,
            contract_interface,
            function_interface,
            (&contract_entry, &contract_post_frame),
            (&function_entry, &function_post_frame),
            &preconditions,
            budget,
        )?
        else {
            return Ok(false);
        };
        instances = at_post;
    }
    let (Some(mut contract_post), Some(mut function_post)) = (
        install(
            &contract_post_frame,
            &instances,
            RefinementSide::Target,
            RefinementPhase::Post,
        ),
        install(
            &function_post_frame,
            &instances,
            RefinementSide::Implementation,
            RefinementPhase::Post,
        ),
    ) else {
        return Ok(false);
    };
    if function_interface.return_type() != ProgramType::Void {
        set_contract_result(&mut contract_post, contract_interface, result.clone());
        set_contract_result(&mut function_post, function_interface, result);
    }
    let access_adapter = checked_access_mode_refinement_adapter(
        contract_interface,
        function_interface,
        &contract_entry,
        &function_entry,
        &function_post,
        &preconditions,
        budget,
    )?;
    if access_adapter == Some(false) {
        return Ok(false);
    }
    let resource_and_effects_compatible = if access_adapter == Some(true) {
        // The checked adapter has already established the resource transition
        // and recovery.  Keep the ordinary effect containment check, but do
        // not re-run the algebraic resource comparison that cannot represent
        // the temporary owner-to-view borrow scope.
        mutable_footprint_is_compatible_for_interfaces(
            contract_interface,
            function_interface,
            &contract_entry,
            &function_entry,
            &preconditions,
            budget,
        )?
    } else {
        compatible_resource_and_effect_interfaces(
            contract_interface,
            function_interface,
            &contract_entry,
            &function_entry,
            &contract_post,
            &function_post,
            &preconditions,
            budget,
        )?
    };
    if !resource_and_effects_compatible {
        return Ok(false);
    }
    // A throw leaves memory as it was, since a throwing interface has no
    // effects, and binds the payload in both frames; the implementation's
    // exceptional guarantees must give the contract's. One that never throws
    // owes nothing here.
    let exceptional_preconditions =
        (!function_interface.exceptional_signature().is_empty()).then(|| preconditions.clone());
    let mut postconditions = preconditions;
    if !assume_contract_propositions(
        &function_post,
        &function_entry,
        function_interface.contract_ensures(),
        &mut postconditions,
        budget,
    )? {
        return Ok(false);
    }
    if !prove_contract_propositions(
        &contract_post,
        &contract_entry,
        contract_interface.contract_ensures(),
        &mut postconditions,
        budget,
    )? {
        return Ok(false);
    }
    let Some(mut exceptional) = exceptional_preconditions else {
        return Ok(true);
    };
    let payload = symbolic_call_result(ProgramType::Int32, budget.allocate_kernel_variable()?);
    let throw_frame = |entry: &ExecutionState| {
        let mut state = entry.clone();
        state
            .locals
            .set_typed(CONTRACT_EXCEPTION, payload.clone(), ProgramType::Int32);
        state
    };
    let function_throw = throw_frame(&function_entry);
    let contract_throw = throw_frame(&contract_entry);
    if !assume_contract_propositions(
        &function_throw,
        &function_entry,
        function_interface.exceptional_ensures(),
        &mut exceptional,
        budget,
    )? {
        return Ok(false);
    }
    prove_contract_propositions(
        &contract_throw,
        &contract_entry,
        contract_interface.exceptional_ensures(),
        &mut exceptional,
        budget,
    )
}

/// Predicate bodies are stored as checked, normalized contract propositions,
/// while `predicate_unfoldings` retains their opaque surface identities. Equal
/// unfolding tables need no proof action. Every entry present on only one side
/// must otherwise have its predicate name explicitly opened by the proof.
pub(super) fn predicate_interfaces_are_explicitly_compatible(
    contract: &FunctionContractInterface,
    function: &FunctionContractInterface,
) -> bool {
    contract
        .predicate_unfoldings()
        .iter()
        .collect::<BTreeSet<_>>()
        == function
            .predicate_unfoldings()
            .iter()
            .collect::<BTreeSet<_>>()
}
