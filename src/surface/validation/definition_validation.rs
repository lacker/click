use super::*;
#[cfg(test)]
use crate::kernel::{CompareRelation, MachineIntegerType};
use crate::kernel::{bits32_constant, constant_u32};

#[cfg(test)]
thread_local! {
    static DEFINITION_VALIDATIONS: std::cell::Cell<usize> = const { std::cell::Cell::new(0) };
}

/// How many times this thread has validated a file's definitions. Each
/// validation re-checks the whole standard library.
#[cfg(test)]
pub(in crate::surface) fn definition_validations() -> usize {
    DEFINITION_VALIDATIONS.with(std::cell::Cell::get)
}

pub(in crate::surface) fn validate_click_definitions(file: &ClickFile) -> Result<(), ClickError> {
    #[cfg(test)]
    DEFINITION_VALIDATIONS.with(|count| count.set(count.get() + 1));
    // A failure before the first declaration belongs to none of them.
    crate::surface::clear_ambient_proof_source();
    validate_algebraic_type_declarations(file)?;
    reject_unimported_library_citations(file)?;
    let predicate_definitions = combined_predicate_definitions(file)?;
    let click_function_definitions = combined_click_function_definitions(file)?;
    let resource_definitions = combined_resource_definitions(file)?;
    let theorem_definitions = combined_theorem_definitions(file)?;

    let mut declarations = DeclarationTable::default();
    for definition in &predicate_definitions {
        crate::surface::enter_ambient_declaration(definition.name());
        reject_held_outside_execution(
            definition.body(),
            &format!("predicate `{}`", definition.name()),
        )?;
        generics::validate_type_parameter_list(
            "predicate",
            definition.name(),
            definition.type_parameters(),
        )?;
        declarations.declare(
            DeclarationKind::Predicate,
            definition.name(),
            definition.parameters().len(),
        )?;
    }

    let mut contracts = BinderMap::new();
    for definition in file.contract_definitions() {
        crate::surface::enter_ambient_declaration(definition.name());
        // A contract proposition takes the function value, then one value
        // per value parameter.
        declarations.declare(
            DeclarationKind::Contract,
            definition.name(),
            1 + definition.value_parameters().len(),
        )?;
        contracts.insert(
            definition.name().to_string(),
            definition.function_pointer_type(),
        );
    }

    let mut click_function_types = BinderMap::new();
    for definition in &click_function_definitions {
        crate::surface::enter_ambient_declaration(definition.name());
        generics::validate_type_parameter_list(
            "function",
            definition.name(),
            definition.type_parameters(),
        )?;
        declarations.declare(
            DeclarationKind::Function,
            definition.name(),
            definition.parameters().len(),
        )?;
        click_function_types.insert(
            definition.name().to_string(),
            ClickFunctionType {
                value_parameter: false,
                type_parameters: definition.type_parameters().to_vec(),
                parameters: definition.parameters().to_vec(),
                return_type: definition.return_type_with_object_class(),
            },
        );
    }
    validate_algebraic_type_uses(file, &mut click_function_types)?;

    for definition in &resource_definitions {
        crate::surface::enter_ambient_declaration(definition.name());
        declarations.declare(
            DeclarationKind::Resource,
            definition.name(),
            definition.parameters().len() + definition.resource_parameters().len(),
        )?;
    }

    let recursive_resources = resource_definitions
        .iter()
        .filter(|definition| {
            definition.composite_body().is_some_and(|body| {
                body.contains().iter().any(|resource| {
                    declared_composite_resource_name(resource) == Some(definition.name())
                })
            })
        })
        .map(|definition| definition.name().to_string())
        .collect::<BTreeSet<_>>();

    for definition in &theorem_definitions {
        crate::surface::enter_ambient_declaration(definition.name());
        generics::validate_type_parameter_list(
            "theorem",
            definition.name(),
            definition.type_parameters(),
        )?;
        declarations.declare(
            DeclarationKind::Theorem,
            definition.name(),
            definition.parameters().len(),
        )?;
    }
    let predicates = declarations.arities(DeclarationKind::Predicate);
    let click_functions = declarations.arities(DeclarationKind::Function);
    let resources = declarations.arities(DeclarationKind::Resource);
    let theorems = declarations.arities(DeclarationKind::Theorem);
    let mut proposition_calls = predicates.clone();
    proposition_calls.insert("same_allocation".to_string(), 2);
    proposition_calls.insert("little_endian".to_string(), 0);
    proposition_calls.insert("held".to_string(), 1);
    proposition_calls.extend(
        declarations
            .arities(DeclarationKind::Contract)
            .iter()
            .map(|(name, arity)| (name.clone(), *arity)),
    );

    let predicate_definition_map = predicate_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect();
    let click_function_definition_map = click_function_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect();
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions)
        .with_contracts(file.contract_definitions(), &file.program_function_names);
    let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
        &click_function_definitions,
        &combined_algebraic_type_definitions(file)?,
    );

    let resource_definition_map = resource_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect();
    for definition in &resource_definitions {
        crate::surface::enter_ambient_declaration(definition.name());
        validate_resource_definition(
            definition,
            &resource_definition_map,
            resources,
            &recursive_resources,
            &proposition_calls,
            &contracts,
            click_functions,
            &click_function_types,
            &predicate_definition_map,
            &click_function_definition_map,
            SpecDefinitions::new(&predicate_environment, &click_function_environment),
        )?;
    }
    reject_composite_resource_cycles(&resource_definitions)?;

    for definition in &predicate_definitions {
        crate::surface::enter_ambient_declaration(definition.name());
        let variables = definition
            .parameters()
            .iter()
            .filter_map(|parameter| {
                parameter
                    .click_type()
                    .interface_type()
                    .map(|interface_type| (parameter.name().to_string(), interface_type))
            })
            .collect();
        validate_predicate_calls_in_proposition(
            definition.body(),
            &proposition_calls,
            click_functions,
            &format!("predicate `{}`", definition.name()),
        )?;
        validate_contract_applications_in_proposition(
            definition.body(),
            &contracts,
            &variables,
            &click_function_types,
            &format!("predicate `{}`", definition.name()),
        )?;
    }

    let mut function_calls = BTreeMap::new();
    for definition in &click_function_definitions {
        crate::surface::enter_ambient_declaration(definition.name());
        let Some(body) = definition.body() else {
            function_calls.insert(definition.name().to_string(), BTreeSet::new());
            continue;
        };
        validate_click_function_expression(
            body,
            click_functions,
            &format!("function `{}`", definition.name()),
        )?;
        with_function_parameter_types(
            definition.parameters(),
            &mut click_function_types,
            |types| validate_program_valued_function_folds(definition, types),
        )?;
        let mut calls = BTreeSet::new();
        collect_click_function_calls(body, &mut calls);
        function_calls.insert(definition.name().to_string(), calls);
    }
    validate_well_founded_click_recursion(
        &click_function_definitions,
        &function_calls,
        &combined_algebraic_type_definitions(file)?,
    )?;

    if let Some((name, error)) = &click_function_environment.pointer_type_error {
        crate::surface::enter_ambient_declaration(name);
        return Err(ClickError::new(error.clone()));
    }

    for theorem in &theorem_definitions {
        crate::surface::enter_ambient_declaration(theorem.name());
        validate_theorem_definition(
            theorem,
            &proposition_calls,
            &contracts,
            click_functions,
            &click_function_types,
        )?;
    }

    let user_click_functions = file
        .click_function_definitions()
        .iter()
        .map(|definition| definition.name())
        .collect::<BTreeSet<_>>();

    let mut function_specs = BTreeSet::new();
    for definition in file.contract_definitions() {
        crate::surface::enter_ambient_declaration(definition.name());
        refuse_a_borrow_spelled_as_two_transfers(definition.function_block())?;
        let variables =
            function_signature_type_environment(definition.function_block().signature(), false);
        for parameter in definition.proof_parameters().unwrap_or(&[]) {
            let ResourceClause::Named { binding, .. } = parameter else {
                unreachable!()
            };
            if variables.contains_key(&binding.name) {
                return Err(ClickError::new(format!(
                    "contract proof parameter `{}` conflicts with a C parameter",
                    binding.name
                )));
            }
            // A named contract's proof parameter stands for an instance the
            // caller supplies, so its resource arguments name the signature's
            // own parameters. The null pointer constant is a position a
            // return-side clause can name, not one a caller can pass here.
            if let ResourceClause::Named { resource, .. } = parameter
                && let ResourceClause::Declared {
                    arguments,
                    parameter_types,
                    ..
                } = resource.as_ref()
                && arguments.iter().zip(parameter_types).any(|(argument, ty)| {
                    crate::surface::lowering::argument_is_null_pointer_constant(argument, *ty)
                })
            {
                return Err(ClickError::new(format!(
                    "contract proof parameter `{}` must name the signature's parameters",
                    binding.name
                )));
            }
            validate_resource_clause(
                parameter,
                resources,
                &recursive_resources,
                click_functions,
                &click_function_types,
                &variables,
                &format!("proof parameter in contract `{}`", definition.name()),
            )?;
        }
    }
    let mut contract_and_function_blocks = file
        .contract_definitions()
        .iter()
        .map(|definition| definition.function_block().clone())
        .collect::<Vec<_>>();
    contract_and_function_blocks.extend(combined_external_function_blocks(file)?);
    for function in contract_and_function_blocks {
        crate::surface::enter_ambient_declaration(function.signature().name());
        if !function_specs.insert(function.signature().name().to_string()) {
            return Err(ClickError::new(format!(
                "duplicate contract or C function spec `{}`",
                function.signature().name()
            )));
        }
        if user_click_functions.contains(function.signature().name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a Click function and a C function spec",
                function.signature().name()
            )));
        }
        if theorems.contains_key(function.signature().name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a theorem and a C function spec",
                function.signature().name()
            )));
        }
        let requires_type_environment =
            function_signature_type_environment(function.signature(), false);
        let ensures_type_environment =
            function_signature_type_environment(function.signature(), true);
        validate_declaration_lambda_bindings(
            function.ensures(),
            &requires_type_environment,
            &BinderSet::new(),
            &click_function_types,
            &format!("declaration bindings in `{}`", function.signature().name()),
        )?;

        reject_duplicate_owned_declared_resource_clauses(
            function
                .requires()
                .iter()
                .filter_map(|requirement| match requirement {
                    Requirement::Resource(resource) => Some(resource),
                    _ => None,
                }),
            &format!("requires clauses in `{}`", function.signature().name()),
        )?;
        reject_duplicate_owned_declared_resource_clauses(
            function
                .ensures()
                .iter()
                .filter_map(|ensure| match ensure.ensure() {
                    Ensure::Resource(resource) => Some(resource),
                    _ => None,
                }),
            &format!("ensures clauses in `{}`", function.signature().name()),
        )?;

        for resource in function.constructs() {
            validate_resource_clause(
                resource,
                resources,
                &recursive_resources,
                click_functions,
                &click_function_types,
                &ensures_type_environment,
                &format!("constructs clause in `{}`", function.signature().name()),
            )?;
            let ResourceClause::Declared {
                access: ResourceAccessMode::Own,
                kind: ResourceKind::Token,
                name,
                ..
            } = resource
            else {
                return Err(ClickError::new(format!(
                    "`constructs` in `{}` requires an owned abstract resource token",
                    function.signature().name()
                )));
            };
            if resource_definitions
                .iter()
                .find(|definition| definition.name() == name)
                .is_some_and(|definition| definition.composite_body().is_some())
            {
                return Err(ClickError::new(format!(
                    "`constructs` in `{}` requires an abstract resource token; `{name}` is composite",
                    function.signature().name()
                )));
            }
        }

        for requirement in function.requires() {
            if let Some(proposition) = requirement.proposition() {
                let context = format!("requires clause in `{}`", function.signature().name());
                validate_contract_proposition_names(
                    proposition,
                    &requires_type_environment,
                    &function.program_object_names,
                    "requires",
                    &context,
                )?;
                reject_held_outside_execution(proposition, &context)?;
                validate_predicate_calls_in_proposition(
                    proposition,
                    &proposition_calls,
                    click_functions,
                    &context,
                )?;
                validate_contract_applications_in_proposition(
                    proposition,
                    &contracts,
                    &requires_type_environment,
                    &click_function_types,
                    &context,
                )?;
                refuse_bool_literal_comparisons(
                    proposition,
                    &requires_type_environment,
                    &click_function_types,
                    &context,
                )?;
            } else if let Requirement::Resource(resource) = requirement {
                validate_resource_clause(
                    resource,
                    resources,
                    &recursive_resources,
                    click_functions,
                    &click_function_types,
                    &requires_type_environment,
                    &format!("requires clause in `{}`", function.signature().name()),
                )?;
            }
        }

        for ensure in function.ensures() {
            match ensure.ensure() {
                Ensure::Proposition(proposition) => {
                    let context = format!("ensures clause in `{}`", function.signature().name());
                    validate_contract_proposition_names(
                        proposition,
                        &ensures_type_environment,
                        &function.program_object_names,
                        "ensures",
                        &context,
                    )?;
                    reject_held_outside_execution(proposition, &context)?;
                    validate_predicate_calls_in_proposition(
                        proposition,
                        &proposition_calls,
                        click_functions,
                        &context,
                    )?;
                    validate_contract_applications_in_proposition(
                        proposition,
                        &contracts,
                        &ensures_type_environment,
                        &click_function_types,
                        &context,
                    )?;
                    refuse_bool_literal_comparisons(
                        proposition,
                        &ensures_type_environment,
                        &click_function_types,
                        &context,
                    )?;
                    if function.signature().return_type() == InterfaceType::Void {
                        // The Integer-aware entry point, not the C-only one.
                        // A `void` function's `ensures` may name an Integer
                        // Click function exactly as every other clause may,
                        // and the C-only validator would type such a
                        // comparison against C scalars alone and refuse it.
                        // This validator dispatches the Integer cases and
                        // hands every remaining shape to that same C
                        // validator, so the two return types agree.
                        validate_theorem_proposition_expression_types(
                            proposition,
                            &ensures_type_environment,
                            &BinderSet::new(),
                            &click_function_types,
                            &format!("ensures clause in `{}`", function.signature().name()),
                        )?;
                    }
                }
                Ensure::Resource(resource) => validate_resource_clause(
                    resource,
                    resources,
                    &recursive_resources,
                    click_functions,
                    &click_function_types,
                    &ensures_type_environment,
                    &format!("ensures clause in `{}`", function.signature().name()),
                )?,
            }
        }

        refuse_a_place_returned_twice(&function)?;
        refuse_a_borrow_spelled_as_two_transfers(&function)?;

        if function.ensures().is_empty()
            && function.exceptional_ensures().is_empty()
            && !function
                .requires()
                .iter()
                .any(requirement_contains_resource)
        {
            return Err(ClickError::new(format!(
                "`{}` must contain at least one `ensures`, `exceptional ensures`, or resource-consuming `requires` clause",
                function.signature().name()
            )));
        }
    }

    crate::surface::clear_ambient_proof_source();
    Ok(())
}

/// Refuse unbound value names before a contract reaches proof lowering.
/// The shared collector removes lexical binders (quantifiers, lets, folds,
/// and match arms). Calls have their own declaration checks; qualified C
/// objects are resolved by the source-aware parser rather than this scope.
fn validate_contract_proposition_names(
    proposition: &ClickProposition,
    variables: &BinderMap<InterfaceType>,
    program_objects: &BTreeSet<String>,
    clause: &str,
    context: &str,
) -> Result<(), ClickError> {
    let mut names = BTreeSet::new();
    crate::surface::lowering::collect_click_proposition_referenced_names(proposition, &mut names);
    if let Some(name) = names.iter().find(|name| {
        !variables.contains_key(*name) && !program_objects.contains(*name) && !name.contains("::")
    }) {
        if name == "result" && clause == "ensures" {
            return Err(ClickError::new(format!(
                "`result` is not available in {context}"
            )));
        }
        return Err(ClickError::new(format!(
            "unknown name `{name}` in `{clause} {}` ({context})",
            describe_click_proposition(proposition),
        )));
    }
    Ok(())
}

/// A function cannot hand back two owners of one place. `owns X` already
/// returns `X`, so `owns X; produces X;` returns it twice, and so does
/// `produces X; produces X;`. The kernel refuses such an exit state, but only
/// while checking a proof and without naming the place, and a contract with
/// no body to check would be accepted and then be unusable at every call.
///
/// The check is by spelling, on unconditional clauses. An `owns` clause is
/// read at entry and a `produces` clause at exit, so the two name the same
/// place for certain only when the place does not depend on memory the
/// function may change. A place reached through a loaded pointer
/// (`owns p->data[0..n]; produces p->data[0..n];`) can be a different
/// allocation at exit, and is left to the proof.
fn refuse_a_place_returned_twice(function: &FunctionBlock) -> Result<(), ClickError> {
    let returned = function
        .ensures()
        .iter()
        .filter(|clause| clause.condition().is_none())
        .filter_map(|clause| match clause.ensure() {
            Ensure::Resource(ResourceClause::OwnMemory(segment)) => {
                Some((segment, clause.borrowed()))
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    for (index, (left, left_borrowed)) in returned.iter().enumerate() {
        for (right, right_borrowed) in &returned[index + 1..] {
            // The whole clause, not its range alone: fields of different
            // widths share a range index and differ in their element.
            if left != right {
                continue;
            }
            let same_state = left_borrowed == right_borrowed;
            if *left_borrowed && *right_borrowed {
                // Two `owns` clauses collide at entry, where the entry
                // resources are checked.
                continue;
            }
            let fixed_place = [&left.base, &left.start, &left.end]
                .into_iter()
                .all(program_expression_reads_no_memory);
            if !same_state && !fixed_place {
                continue;
            }
            let place = crate::surface::diagnostics::describe_contract_segment(left);
            let how = if same_state {
                format!("produces `{place}` twice")
            } else {
                format!("both owns and produces `{place}`; `owns` already returns it")
            };
            return Err(ClickError::new(format!(
                "`{}` {how}, so it would return two owners of one place",
                function.signature().name()
            ))
            .with_kind(ClickErrorKind::Type));
        }
    }
    Ok(())
}

/// One spelling per form: `consumes X; produces X;` with the same `X` is the
/// borrow `owns X;`. Both hand `X` to the callee at entry and give it back at
/// exit, and both leave every value inside `X` to the contract's `ensures`.
///
/// The check is by spelling, on unconditional clauses, and only where the two
/// clauses certainly name one resource. A `consumes` clause is read at entry
/// and a `produces` clause at exit, so a place or argument that reads memory
/// (`consumes list(node->next); produces list(node->next);`) can name another
/// object at exit; that pair is a real transformation and stays. A pair whose
/// instances carry different names, or whose produced resource is guarded,
/// also stays.
fn refuse_a_borrow_spelled_as_two_transfers(function: &FunctionBlock) -> Result<(), ClickError> {
    let mut borrowed = function
        .ensures()
        .iter()
        .filter(|clause| clause.borrowed())
        .filter_map(|clause| match clause.ensure() {
            Ensure::Resource(resource) => Some(resource),
            Ensure::Proposition(_) => None,
        })
        .collect::<Vec<_>>();
    // An `owns` clause is a requirement paired with a borrowed return; every
    // other owned requirement is a `consumes` clause.
    let mut consumed = Vec::new();
    for requirement in function.requires() {
        let Requirement::Resource(resource) = requirement else {
            continue;
        };
        if let Some(index) = borrowed.iter().position(|held| *held == resource) {
            borrowed.swap_remove(index);
            continue;
        }
        consumed.push(resource);
    }
    for clause in function.ensures() {
        if clause.borrowed() || clause.condition().is_some() {
            continue;
        }
        let Ensure::Resource(produced) = clause.ensure() else {
            continue;
        };
        if !resource_names_one_place_at_entry_and_exit(produced) || !consumed.contains(&produced) {
            continue;
        }
        let target = crate::surface::printing::format_resource_target(produced);
        let proof = if matches!(clause.proof(), SourceProof::Default) {
            String::new()
        } else {
            ", with the `produces` clause's proof".to_string()
        };
        return Err(ClickError::new(format!(
            "`{}` consumes and produces `{target}`; write the one clause `owns {target};`{proof}",
            function.signature().name()
        ))
        .with_kind(ClickErrorKind::Type));
    }
    Ok(())
}

/// Whether an unconditional resource clause names the same resource read at
/// a function's entry and at its exit: its places and arguments are built from
/// parameters and constants alone.
fn resource_names_one_place_at_entry_and_exit(resource: &ResourceClause) -> bool {
    let fixed_segment = |segment: &ContractSegment| {
        [&segment.base, &segment.start, &segment.end]
            .into_iter()
            .all(program_expression_reads_no_memory)
    };
    let fixed_expression = |expression: &ContractExpression| {
        contract_expression_as_program_expression(expression)
            .is_some_and(|expression| program_expression_reads_no_memory(&expression))
    };
    match resource {
        ResourceClause::OwnMemory(segment) => fixed_segment(segment),
        ResourceClause::MemoryAggregate {
            access: ResourceAccessMode::Own,
            segments,
        } => segments.iter().all(fixed_segment),
        ResourceClause::Named { resource, .. } => {
            resource_names_one_place_at_entry_and_exit(resource)
        }
        ResourceClause::Quantified { quantity, resource } => {
            fixed_expression(quantity) && resource_names_one_place_at_entry_and_exit(resource)
        }
        ResourceClause::Declared {
            access: ResourceAccessMode::Own,
            arguments,
            resource_type_arguments,
            resource_arguments,
            ..
        } => {
            resource_type_arguments.is_empty()
                && resource_arguments.is_empty()
                && arguments.iter().all(fixed_expression)
        }
        _ => false,
    }
}

/// Whether an expression is built from parameters and constants alone, so
/// that it denotes the same value at a function's entry and exit.
pub(in crate::surface) fn program_expression_reads_no_memory(
    expression: &ProgramExpression,
) -> bool {
    match expression {
        ProgramExpression::Variable(_) | ProgramExpression::Value(_) => true,
        ProgramExpression::Add(left, right)
        | ProgramExpression::Subtract(left, right)
        | ProgramExpression::Multiply(left, right) => {
            program_expression_reads_no_memory(left) && program_expression_reads_no_memory(right)
        }
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => {
            program_expression_reads_no_memory(pointer)
        }
        ProgramExpression::Cast { expression, .. } => {
            program_expression_reads_no_memory(expression)
        }
        // `&q[i]` is an address computed from `q` and `i`; nothing is loaded.
        ProgramExpression::AddressOf(place) => match place.as_ref() {
            ProgramExpression::Index(base, index) => {
                program_expression_reads_no_memory(base)
                    && program_expression_reads_no_memory(index)
            }
            _ => false,
        },
        _ => false,
    }
}

fn validate_contract_applications_in_proposition(
    proposition: &ClickProposition,
    contracts: &BinderMap<InterfaceType>,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let mut pending = vec![(proposition, variables)];
    while let Some((proposition, variables)) = pending.pop() {
        match proposition {
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push((right, variables));
                pending.push((left, variables));
            }
            proposition => {
                validate_contract_applications_in_proposition_one(
                    proposition,
                    contracts,
                    variables,
                    click_functions,
                    context,
                )?;
            }
        }
    }
    Ok(())
}

fn validate_contract_applications_in_proposition_one(
    proposition: &ClickProposition,
    contracts: &BinderMap<InterfaceType>,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Value(_) => Ok(()),
        ClickProposition::PredicateCall { name, arguments } => {
            if name == "held" {
                let [mutex] = arguments.as_slice() else {
                    return Err(ClickError::new(format!(
                        "held expects one mutex pointer in {context}, got {}",
                        arguments.len()
                    )));
                };
                let actual =
                    infer_contract_expression_type(mutex, variables, click_functions, context)?;
                if !actual.is_some_and(InterfaceType::is_object_pointer) {
                    return Err(ClickError::new(format!(
                        "held expects a mutex pointer in {context}"
                    )));
                }
                return Ok(());
            }
            if name == "little_endian" {
                return if arguments.is_empty() {
                    Ok(())
                } else {
                    Err(ClickError::new("little_endian expects no arguments"))
                };
            }
            if name == "same_allocation" {
                let [left, right] = arguments.as_slice() else {
                    return Err(ClickError::new(format!(
                        "same_allocation expects two pointer arguments in {context}, got {}",
                        arguments.len()
                    )));
                };
                for argument in [left, right] {
                    let actual = infer_contract_expression_type(
                        argument,
                        variables,
                        click_functions,
                        context,
                    )?;
                    if !actual.is_some_and(InterfaceType::is_object_pointer) {
                        return Err(ClickError::new(format!(
                            "same_allocation expects pointer arguments in {context}, got {}",
                            actual.map_or_else(
                                || "an unknown type".to_string(),
                                describe_interface_type
                            )
                        )));
                    }
                }
                return Ok(());
            }
            let Some(expected) = contracts.get(name) else {
                return Ok(());
            };
            // The function value comes first; the rest are the contract's
            // value parameters, whose count the parser checked by name and
            // whose exact types the kernel checks where it binds them.
            let Some((argument, values)) = arguments.split_first() else {
                return Err(ClickError::new(format!(
                    "contract `{name}` expects one function-pointer argument in {context}"
                )));
            };
            for value in values {
                let actual =
                    infer_contract_expression_type(value, variables, click_functions, context)?;
                if actual.is_some_and(|actual| actual.is_pointer()) {
                    return Err(ClickError::new(format!(
                        "contract `{name}` value parameters are scalars, got {} in {context}",
                        actual
                            .map_or_else(|| "an unknown type".to_string(), describe_interface_type)
                    )));
                }
            }
            // A named C function's address carries its precise signature in
            // the built kernel environment rather than in the pure theorem's
            // local variable map. Accept the address shape here; contract
            // refinement later checks the exact lowered signature before it
            // can issue authority.
            let actual = match contract_expression_function_address(argument) {
                Some(_) => Some(*expected),
                None => {
                    infer_contract_expression_type(argument, variables, click_functions, context)?
                }
            };
            if actual != Some(*expected) {
                return Err(ClickError::new(format!(
                    "contract `{name}` expects {}, got {} in {context}",
                    describe_interface_type(*expected),
                    actual.map_or_else(|| "an unknown type".to_string(), describe_interface_type),
                )));
            }
            Ok(())
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_contract_applications_in_proposition(
                left,
                contracts,
                variables,
                click_functions,
                context,
            )?;
            validate_contract_applications_in_proposition(
                right,
                contracts,
                variables,
                click_functions,
                context,
            )
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        } => validate_contract_applications_in_proposition(
            body,
            contracts,
            variables,
            click_functions,
            context,
        ),
        ClickProposition::ForAll {
            click_type: interface_type,
            name,
            body,
            ..
        }
        | ClickProposition::Exists {
            click_type: interface_type,
            name,
            body,
            ..
        } => {
            let mut variables = variables.clone();
            match interface_type {
                ClickType::Resource => {
                    variables.remove(name);
                }
                ClickType::Program(interface_type)
                | ClickType::CObjectPointer { interface_type, .. } => {
                    variables.insert(name.clone(), *interface_type);
                }
                ClickType::Integer => {
                    variables.remove(name);
                }
                ClickType::Algebraic(_) => {
                    variables.remove(name);
                }
                ClickType::Proposition | ClickType::Function { .. } | ClickType::Parameter(_) => {
                    return Err(ClickError::new(
                        "this quantifier binder type is not supported",
                    ));
                }
            }
            validate_contract_applications_in_proposition(
                body,
                contracts,
                &variables,
                click_functions,
                context,
            )
        }
        ClickProposition::RangeAll { item, body, .. }
        | ClickProposition::RangeAny { item, body, .. } => {
            let mut variables = variables.clone();
            variables.insert(item.clone(), InterfaceType::Int32);
            validate_contract_applications_in_proposition(
                body,
                contracts,
                &variables,
                click_functions,
                context,
            )
        }
        ClickProposition::Comparison { .. }
        | ClickProposition::FloatClassification { .. }
        | ClickProposition::Separate { .. }
        | ClickProposition::ResourceViewable { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. }
        | ClickProposition::IsA { .. } => Ok(()),
    }
}

/// The refusal for a resource `requires` clause in a pure theorem.
///
/// A theorem has no resource context, so `owns` and `consumes` have nothing to
/// take and nothing to give back. Readability is the one thing a range still
/// means without an owner, and `views` is how a theorem says it, so the
/// sentence names the clause the reader most likely wanted.
pub(in crate::surface) fn theorem_resource_clause_refusal(theorem_name: &str) -> String {
    format!(
        "pure theorem `{theorem_name}` cannot require a resource: applying a theorem lends, \
         consumes and separates nothing. A theorem states that a range is readable with `views \
         v[lo..hi];`, which its proof assumes and anyone who applies it owes"
    )
}

/// The refusal for a resource `ensures` clause in a pure theorem.
pub(in crate::surface) fn theorem_resource_conclusion_refusal(theorem_name: &str) -> String {
    format!(
        "pure theorem `{theorem_name}` cannot conclude a resource: applying a theorem creates and \
         returns nothing. A theorem states that a range is readable with `views v[lo..hi];` among \
         its requirements, and concludes propositions only"
    )
}

fn reject_held_outside_execution(
    proposition: &ClickProposition,
    context: &str,
) -> Result<(), ClickError> {
    let mut pending = vec![proposition];
    while let Some(current) = pending.pop() {
        match current {
            ClickProposition::PredicateCall { name, .. } if name == "held" => {
                return Err(ClickError::new(format!(
                    "`held` describes the current execution path and cannot appear in {context}"
                )));
            }
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push(left);
                pending.push(right);
            }
            ClickProposition::Not(body)
            | ClickProposition::At {
                proposition: body, ..
            }
            | ClickProposition::ForAll { body, .. }
            | ClickProposition::Exists { body, .. }
            | ClickProposition::RangeAll { body, .. }
            | ClickProposition::RangeAny { body, .. } => pending.push(body),
            _ => {}
        }
    }
    Ok(())
}

fn validate_theorem_definition(
    theorem: &TheoremDefinition,
    predicates: &BTreeMap<String, usize>,
    contracts: &BinderMap<InterfaceType>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BinderMap<ClickFunctionType>,
) -> Result<(), ClickError> {
    if theorem.ensures().is_empty() {
        return Err(ClickError::new(format!(
            "theorem `{}` must contain at least one `ensures` clause",
            theorem.name()
        )));
    }

    let variables = theorem_type_environment(theorem);
    validate_declaration_lambda_bindings(
        theorem.ensures(),
        &variables,
        &theorem
            .parameters()
            .iter()
            .filter(|parameter| matches!(parameter.click_type(), ClickType::Integer))
            .map(|parameter| parameter.name().to_string())
            .collect(),
        click_function_types,
        &format!("declaration bindings in theorem `{}`", theorem.name()),
    )?;
    for requirement in theorem.requires() {
        let Some(proposition) = requirement.theorem_proposition() else {
            return Err(ClickError::new(theorem_resource_clause_refusal(
                theorem.name(),
            )));
        };
        let proposition = &proposition;
        reject_held_outside_execution(
            proposition,
            &format!("requires clause in theorem `{}`", theorem.name()),
        )?;
        validate_predicate_calls_in_proposition(
            proposition,
            predicates,
            click_functions,
            &format!("requires clause in theorem `{}`", theorem.name()),
        )?;
        validate_contract_applications_in_proposition(
            proposition,
            contracts,
            &variables,
            click_function_types,
            &format!("requires clause in theorem `{}`", theorem.name()),
        )?;
        validate_theorem_proposition_expression_types(
            proposition,
            &variables,
            &theorem
                .parameters()
                .iter()
                .filter(|parameter| matches!(parameter.click_type(), ClickType::Integer))
                .map(|parameter| parameter.name().to_string())
                .collect(),
            click_function_types,
            &format!("requires clause in theorem `{}`", theorem.name()),
        )?;
    }

    for ensure in theorem.ensures() {
        let Ensure::Proposition(proposition) = ensure.ensure() else {
            return Err(ClickError::new(theorem_resource_conclusion_refusal(
                theorem.name(),
            )));
        };
        reject_held_outside_execution(
            proposition,
            &format!("ensures clause in theorem `{}`", theorem.name()),
        )?;
        validate_predicate_calls_in_proposition(
            proposition,
            predicates,
            click_functions,
            &format!("ensures clause in theorem `{}`", theorem.name()),
        )?;
        validate_contract_applications_in_proposition(
            proposition,
            contracts,
            &variables,
            click_function_types,
            &format!("ensures clause in theorem `{}`", theorem.name()),
        )?;
        validate_theorem_proposition_expression_types(
            proposition,
            &variables,
            &theorem
                .parameters()
                .iter()
                .filter(|parameter| matches!(parameter.click_type(), ClickType::Integer))
                .map(|parameter| parameter.name().to_string())
                .collect(),
            click_function_types,
            &format!("ensures clause in theorem `{}`", theorem.name()),
        )?;
        if theorem.executes.is_none() {
            validate_pure_theorem_proof(theorem.name(), ensure.proof())?;
        }
    }

    Ok(())
}

fn validate_resource_definition<'a>(
    definition: &'a ResourceDefinition,
    resource_definitions: &BTreeMap<&'a str, &'a ResourceDefinition>,
    resources: &BTreeMap<String, usize>,
    recursive_resources: &BTreeSet<String>,
    predicates: &BTreeMap<String, usize>,
    contracts: &BinderMap<InterfaceType>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BinderMap<ClickFunctionType>,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(), ClickError> {
    let Some(composite_body) = definition.composite_body() else {
        return Ok(());
    };
    if composite_body.matched.is_some() {
        for (_, _, arm) in resource_match_arm_scopes(
            definition,
            |name| {
                spec_definitions
                    .functions
                    .algebraic_type_definitions
                    .get(name)
            },
            |name| resource_definitions.get(name).copied(),
        )? {
            validate_resource_definition(
                &arm,
                resource_definitions,
                resources,
                recursive_resources,
                predicates,
                contracts,
                click_functions,
                click_function_types,
                predicate_definitions,
                click_function_definitions,
                spec_definitions,
            )?;
        }
        return Ok(());
    }
    if let Some(scope) =
        resource_unmatched_body_scope(definition, |name| resource_definitions.get(name).copied())?
    {
        return validate_resource_definition(
            &scope,
            resource_definitions,
            resources,
            recursive_resources,
            predicates,
            contracts,
            click_functions,
            click_function_types,
            predicate_definitions,
            click_function_definitions,
            spec_definitions,
        );
    }
    if let Some(view) = resource_body_fields_as_parameters(definition)? {
        return validate_resource_definition(
            &view,
            resource_definitions,
            resources,
            recursive_resources,
            predicates,
            contracts,
            click_functions,
            click_function_types,
            predicate_definitions,
            click_function_definitions,
            spec_definitions,
        );
    }
    let mut variables: BinderMap<InterfaceType> = definition
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.interface_type()))
        .collect();
    for witness in composite_body.witnesses() {
        if variables
            .insert(witness.name().to_string(), witness.interface_type())
            .is_some()
        {
            return Err(ClickError::new(format!(
                "resource `{}` witness `{}` shadows a parameter",
                definition.name(),
                witness.name()
            )));
        }
    }
    if let Some(condition) = composite_body.condition() {
        if proposition_contains_old_expression(condition) {
            return Err(ClickError::new(format!(
                "`old(...)` is not available inside resource `{}` condition",
                definition.name()
            )));
        }
        if proposition_contains_at_expression(condition) {
            return Err(ClickError::new(format!(
                "`at(...)` is not available inside resource `{}` condition",
                definition.name()
            )));
        }
        validate_predicate_calls_in_proposition(
            condition,
            predicates,
            click_functions,
            &format!("resource `{}` condition", definition.name()),
        )?;
        validate_contract_applications_in_proposition(
            condition,
            contracts,
            &variables,
            click_function_types,
            &format!("resource `{}` condition", definition.name()),
        )?;
        validate_proposition_expression_types(
            condition,
            &variables,
            click_function_types,
            &format!("resource `{}` condition", definition.name()),
        )?;
        let mut reads = Vec::new();
        collect_resource_fact_reads_from_proposition(
            condition,
            predicate_definitions,
            click_function_definitions,
            &mut Vec::new(),
            &mut ResourceFunctionReadEffects::default(),
            &mut reads,
            definition.name(),
        )?;
        if let Some(read) = reads.first() {
            return Err(ClickError::new(format!(
                "resource `{}` condition must be load-free; `{}` reads memory",
                definition.name(),
                read.expression
            )));
        }
    }
    reject_duplicate_owned_declared_resource_clauses(
        composite_body.contains(),
        &format!("composite resource `{}` body", definition.name()),
    )?;
    validate_iterated_resource_clauses(
        definition,
        composite_body,
        &variables,
        click_function_types,
        predicate_definitions,
        click_function_definitions,
        spec_definitions,
    )?;
    for resource in composite_body.contains() {
        validate_resource_clause(
            resource,
            resources,
            recursive_resources,
            click_functions,
            click_function_types,
            &variables,
            &format!("composite resource `{}` body", definition.name()),
        )?;
    }
    let mut prior_facts = Vec::new();
    for fact in composite_body.facts() {
        reject_held_outside_execution(fact, &format!("resource `{}` fact", definition.name()))?;
        if proposition_contains_old_expression(fact) {
            return Err(ClickError::new(format!(
                "`old(...)` is not available inside resource `{}` fact",
                definition.name()
            )));
        }
        if proposition_contains_at_expression(fact) {
            return Err(ClickError::new(format!(
                "`at(...)` is not available inside resource `{}` fact",
                definition.name()
            )));
        }
        validate_predicate_calls_in_proposition(
            fact,
            predicates,
            click_functions,
            &format!("resource `{}` fact", definition.name()),
        )?;
        validate_contract_applications_in_proposition(
            fact,
            contracts,
            &variables,
            click_function_types,
            &format!("resource `{}` fact", definition.name()),
        )?;
        validate_proposition_expression_types(
            fact,
            &variables,
            click_function_types,
            &format!("resource `{}` fact", definition.name()),
        )?;
        validate_resource_fact_memory_read_authority(
            definition,
            composite_body,
            fact,
            &prior_facts,
            predicate_definitions,
            click_function_definitions,
            spec_definitions,
        )?;
        prior_facts.push(fact);
    }
    Ok(())
}

/// Checks every iterated guarded-ownership clause of one body: the kernel can
/// read its shape, the index shadows nothing, the guard reads only cells the
/// same body owns (so no one can change it while the resource is folded), and
/// the guard cells are not themselves elements.
fn validate_iterated_resource_clauses(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    variables: &BinderMap<InterfaceType>,
    click_function_types: &BinderMap<ClickFunctionType>,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(), ClickError> {
    let clauses = composite_body
        .contains()
        .iter()
        .filter_map(|clause| match clause {
            ResourceClause::Iterated(clause) => Some(clause.as_ref()),
            _ => None,
        })
        .collect::<Vec<_>>();
    if clauses.len() > 1 {
        return Err(ClickError::new(format!(
            "resource `{}` declares {} iterated ownership clauses; a body may declare at most one",
            definition.name(),
            clauses.len()
        )));
    }
    for clause in clauses {
        let context = format!(
            "resource `{}` iterated ownership clause `{}`",
            definition.name(),
            crate::surface::lowering::describe_iterated_clause(clause)
        );
        let index = &clause.binder;
        if variables.contains_key(index)
            || composite_body
                .fields
                .iter()
                .any(|field| field.name() == index)
        {
            return Err(ClickError::new(format!(
                "{context}: the index `{index}` shadows a parameter, field, or witness of the resource; choose a fresh index name"
            )));
        }
        let shape = crate::surface::lowering::iterated_clause_shape(clause)
            .map_err(|message| ClickError::new(format!("{context}: {message}")))?;
        let guard = shape.guard.as_ref().ok_or_else(|| {
            ClickError::new(format!(
                "{context}: an unguarded clause is the plain range `owns base[lo..hi]`"
            ))
        })?;
        if guard.base == shape.element_base {
            return Err(ClickError::new(format!(
                "{context}: the guard cells and the elements are the same array; a guard must read cells the elements do not include"
            )));
        }
        // A range the body owns outright may share the elements' base: the
        // body's facts say which of those elements the guard excludes, and
        // a fold consumes both from one context, where owned memory is a
        // partition, so no cell is ever held twice.
        let mut scoped = variables.clone();
        scoped.insert(index, InterfaceType::Int32);
        let clause_guard = clause
            .guard
            .as_ref()
            .expect("a guarded clause keeps its guard proposition");
        for proposition in [&clause.range, clause_guard] {
            validate_proposition_expression_types(
                proposition,
                &scoped,
                click_function_types,
                &context,
            )?;
            if proposition_contains_old_expression(proposition)
                || proposition_contains_at_expression(proposition)
            {
                return Err(ClickError::new(format!(
                    "{context}: `old(...)` and `at(...)` are not available in a resource body"
                )));
            }
        }
        if let ClickProposition::Comparison { left, right, .. } = clause_guard {
            for side in [left, right] {
                let Some(ty) =
                    infer_contract_expression_type(side, &scoped, click_function_types, &context)?
                else {
                    continue;
                };
                if ty != InterfaceType::Int32 {
                    return Err(ClickError::new(format!(
                        "{context}: the guard compares `int32` cells in this slice, but `{}` has type `{}`",
                        crate::surface::diagnostics::describe_contract_expression(side),
                        describe_interface_type(ty)
                    )));
                }
            }
        }
        // The guard is read against the cells the body itself owns: state it
        // as the bounded fact `forall k. range implies guard` and ask the
        // same read-authority check a body fact gets. A guard over a cell the
        // body does not own could change while the resource is folded.
        let guard_fact = ClickProposition::ForAll {
            click_type: ClickType::Program(InterfaceType::Int32),
            name: index.to_string().into(),
            written_name: None,
            body: Box::new(ClickProposition::Implies(
                Box::new(clause.range.clone()),
                Box::new(clause_guard.clone()),
            )),
        };
        let no_values = BTreeMap::new();
        let guard_fact = crate::surface::lowering::substitute_click_proposition_in(
            &guard_fact,
            &crate::surface::lowering::ContractSubstitutions::with_body_fields_as_program_names(
                &no_values,
            ),
        )
        .map_err(|message| ClickError::new(format!("{context}: {message}")))?;
        validate_resource_fact_memory_read_authority(
            definition,
            composite_body,
            &guard_fact,
            &[],
            predicate_definitions,
            click_function_definitions,
            spec_definitions,
        )
        .map_err(|error| {
            ClickError::new(format!(
                "{context}: the guard must read only cells the same body owns, so that it cannot change while the resource is folded\n{}",
                error.raw_summary()
            ))
        })?;
    }
    Ok(())
}

/// The body of a field-bearing resource as definition validation reads it:
/// each C-typed field becomes a parameter, and every use of that field in
/// the body's facts and guard is spelled as that parameter. The kernel binds
/// a field by name exactly so while it folds or unfolds an instance, which is
/// how a memory endpoint or child argument names it; a matched constructor
/// payload is validated the same way (`resource_match_arm_scopes`). `None`
/// when the body has no C-typed field. A field that shares a parameter's name
/// is refused when the field schema is checked, and is left alone here.
fn resource_body_fields_as_parameters(
    definition: &ResourceDefinition,
) -> Result<Option<ResourceDefinition>, ClickError> {
    let Some(body) = definition.composite_body() else {
        return Ok(None);
    };
    let (scalar, other): (Vec<_>, Vec<_>) = body.fields.iter().cloned().partition(|field| {
        matches!(field.click_type, ClickType::Program(_))
            && !definition
                .parameters()
                .iter()
                .any(|parameter| parameter.name() == field.name())
    });
    if scalar.is_empty() {
        return Ok(None);
    }
    let no_values = BTreeMap::new();
    let substitutions = ContractSubstitutions::with_body_fields_as_program_names(&no_values);
    let mut parameters = definition.parameters.clone();
    parameters.extend(scalar.iter().map(|field| FunctionParameter {
        slice_length: None,
        name: field.name.clone(),
        click_type: field.click_type.clone(),
        struct_name: None,
        function_pointer_signature: None,
        constant: false,
        pointee_constant: false,
        reference: false,
    }));
    let mut view = body.clone();
    view.fields = other;
    view.contains = body
        .contains
        .iter()
        .map(|resource| {
            crate::surface::verification::substitute_resource_clause_for_summary_in(
                resource,
                &substitutions,
            )
        })
        .collect::<Result<_, _>>()
        .map_err(ClickError::new)?;
    view.condition = body
        .condition
        .as_ref()
        .map(|condition| substitute_click_proposition_in(condition, &substitutions))
        .transpose()
        .map_err(ClickError::new)?;
    view.facts = body
        .facts
        .iter()
        .map(|fact| substitute_click_proposition_in(fact, &substitutions))
        .collect::<Result<_, _>>()
        .map_err(ClickError::new)?;
    Ok(Some(ResourceDefinition {
        name: definition.name.clone(),
        resource_parameters: definition.resource_parameters.clone(),
        parameters,
        composite_body: Some(view),
        field_schema: definition.field_schema.clone(),
        authorized: definition.authorized,
        sealed: definition.sealed,
    }))
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResourceFactRead {
    base: ProgramExpression,
    index: ProgramExpression,
    expression: String,
    enclosing_range: Option<(ProgramExpression, ProgramExpression)>,
    /// The bytes a typed read reaches from its base, when it is one.
    extent: Option<crate::kernel::AccessExtent>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResourceFactScalarAssumption {
    source: String,
    proposition: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResourceFactReadAuthorityAnalysis {
    covered: bool,
    notes: Vec<String>,
}

fn validate_resource_fact_memory_read_authority(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    fact: &ClickProposition,
    prior_facts: &[&ClickProposition],
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    spec_definitions: SpecDefinitions<'_>,
) -> Result<(), ClickError> {
    let mut reads = Vec::new();
    let mut visited_predicates = Vec::new();
    let mut visited_functions = ResourceFunctionReadEffects::default();
    collect_resource_fact_reads_from_proposition(
        fact,
        predicate_definitions,
        click_function_definitions,
        &mut visited_predicates,
        &mut visited_functions,
        &mut reads,
        definition.name(),
    )?;
    let mut values = pure_theorem_parameter_values(definition.parameters());
    // Witnesses are validated as opaque symbolic pointers: they exist for
    // the body's own clauses exactly as parameters do.
    for (index, witness) in composite_body.witnesses().iter().enumerate() {
        values.insert(
            witness.name().to_string(),
            crate::kernel::ProgramValue::typed_pointer(
                crate::kernel::Address::symbolic(crate::kernel::Variable(4_100_000 + index as u64)),
                witness.interface_type().to_kernel_type(),
            ),
        );
    }
    let bound_names = definition
        .parameters()
        .iter()
        .map(|parameter| {
            (
                parameter.name().to_string(),
                parameter.interface_type(),
                parameter.struct_name().map(str::to_string),
            )
        })
        .chain(
            composite_body
                .witnesses()
                .iter()
                .map(|witness| (witness.name().to_string(), witness.interface_type(), None)),
        )
        .collect::<Vec<_>>();
    let arguments = bound_names
        .iter()
        .map(|(name, _, _)| {
            ProgramExpression::Value(
                values
                    .get(name)
                    .expect("resource parameter value should exist")
                    .clone(),
            )
        })
        .collect::<Vec<_>>();
    let substitutions = bound_names
        .iter()
        .map(|(name, _, _)| {
            (
                name.clone(),
                ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    (name.clone()).into(),
                )),
            )
        })
        .collect();
    let validation_parameters = bound_names
        .iter()
        .map(|(name, interface_type, struct_name)| {
            crate::languages::interface::ImportedParameter::new(
                *interface_type,
                name.clone(),
                struct_name.clone(),
            )
        })
        .collect::<Vec<_>>();
    // A contained resource's formation domains are part of the assumed body
    // while checking its fact declarations. Actual fold/use still owes them.
    // Set up one root before lowering the body and use it for declared facts.
    let root = crate::kernel::ExecutionState::new().with_memory(SymbolicMemory::new());
    let (materialized, formation) = crate::surface::proof::probe_open_obligations(|| {
        instantiate_composite_resource_body_resources(
            definition.name(),
            composite_body,
            &substitutions,
            ParameterBinding::new(&validation_parameters, &arguments),
            &root,
            &PureFactContext::new(),
        )
    });
    let (memory, _) = materialized
    .map_err(|message| {
        ClickError::new(format!(
            "resource `{}` could not materialize contained memory while validating facts: {message}",
            definition.name()
        ))
    })?;
    let state = root.with_materialized_memory_at_current_point(memory);
    let at = state.program_point();
    let array_refs = pure_theorem_array_refs(definition.parameters(), &values, &at);
    let mut scalar_assumptions = formation
        .recorded
        .into_iter()
        .map(|debt| ResourceFactScalarAssumption {
            source: format!("resource `{}` body formation", definition.name()),
            proposition: debt.proposition,
        })
        .collect::<Vec<_>>();
    for body_fact in prior_facts {
        collect_resource_fact_scalar_assumptions_from_proposition(
            body_fact,
            predicate_definitions,
            ContractEnvironment::new(&values, &array_refs),
            &at,
            spec_definitions,
            &mut Vec::new(),
            &mut scalar_assumptions,
            definition.name(),
        )?;
    }
    let empty_memory = SymbolicMemory::new();
    let empty_at = crate::kernel::ProgramPoint::starting_at(&empty_memory);
    let empty_array_refs = pure_theorem_array_refs(definition.parameters(), &values, &empty_at);
    collect_resource_fact_scalar_assumptions_from_proposition(
        fact,
        predicate_definitions,
        ContractEnvironment::new(&values, &empty_array_refs),
        &empty_at,
        spec_definitions,
        &mut Vec::new(),
        &mut scalar_assumptions,
        definition.name(),
    )?;
    let assumption_propositions = scalar_assumptions
        .iter()
        .map(|assumption| assumption.proposition.clone())
        .collect::<Vec<_>>();
    let assumptions = assumptions_from_propositions(&assumption_propositions);
    for read in reads {
        let analysis = analyze_resource_fact_read_authority(
            &read,
            composite_body.contains(),
            &assumptions,
            ContractEnvironment::new(&values, &array_refs),
            &at,
            spec_definitions,
        );
        if !analysis.covered {
            return Err(ClickError::new(resource_fact_read_authority_error(
                definition.name(),
                &read,
                &analysis,
                &scalar_assumptions,
            )));
        }
    }
    Ok(())
}

fn collect_resource_fact_scalar_assumptions_from_proposition(
    proposition: &ClickProposition,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    contract_environment: ContractEnvironment<'_>,
    at: &crate::kernel::ProgramPoint,
    spec_definitions: SpecDefinitions<'_>,
    visited_predicates: &mut Vec<String>,
    assumptions: &mut Vec<ResourceFactScalarAssumption>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Value(_) => Ok(()),
        ClickProposition::Comparison { .. }
        | ClickProposition::FloatClassification { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. }
        | ClickProposition::IsA { .. } => {
            let source = describe_click_proposition(proposition);
            let state = ExecutionState::at_point(at);
            if let Ok(proposition) =
                crate::surface::proof::lower_fixed_state_proposition_through_kernel(
                    proposition,
                    &PureFactContext::new(),
                    contract_environment,
                    FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
                    spec_definitions,
                )
            {
                assumptions.push(ResourceFactScalarAssumption {
                    source,
                    proposition,
                });
            }
            Ok(())
        }
        ClickProposition::At { proposition, .. } => {
            collect_resource_fact_scalar_assumptions_from_proposition(
                proposition,
                predicate_definitions,
                contract_environment,
                at,
                spec_definitions,
                visited_predicates,
                assumptions,
                resource_name,
            )
        }
        ClickProposition::Separate { .. }
        | ClickProposition::ResourceViewable { .. }
        | ClickProposition::Contains { .. } => Ok(()),
        ClickProposition::And(left, right) => {
            collect_resource_fact_scalar_assumptions_from_proposition(
                left,
                predicate_definitions,
                contract_environment,
                at,
                spec_definitions,
                visited_predicates,
                assumptions,
                resource_name,
            )?;
            collect_resource_fact_scalar_assumptions_from_proposition(
                right,
                predicate_definitions,
                contract_environment,
                at,
                spec_definitions,
                visited_predicates,
                assumptions,
                resource_name,
            )
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let Some(definition) = predicate_definitions.get(name.as_str()) else {
                return Ok(());
            };
            if visited_predicates.contains(name) {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` fact cannot use recursive predicate `{name}`"
                )));
            }
            visited_predicates.push(name.clone());
            let body = instantiate_click_predicate_definition(definition, arguments).map_err(
                |message| {
                    ClickError::new(format!(
                        "resource `{resource_name}` fact could not inspect predicate `{name}`: {message}"
                    ))
                },
            )?;
            let result = collect_resource_fact_scalar_assumptions_from_proposition(
                &body,
                predicate_definitions,
                contract_environment,
                at,
                spec_definitions,
                visited_predicates,
                assumptions,
                resource_name,
            );
            visited_predicates.pop();
            result
        }
        ClickProposition::Or(_, _)
        | ClickProposition::Not(_)
        | ClickProposition::Implies(_, _)
        | ClickProposition::ForAll { .. }
        | ClickProposition::Exists { .. }
        | ClickProposition::RangeAll { .. }
        | ClickProposition::RangeAny { .. } => Ok(()),
    }
}

/// Memoized source-body effects, separate from instantiated caller arguments.
/// A read-free body need not be substituted or traversed again at each call.
#[derive(Default)]
struct ResourceFunctionReadEffects {
    #[cfg(test)]
    body_inspections: usize,
    active: Vec<String>,
    read_free: BTreeSet<String>,
    reads_memory: BTreeSet<String>,
}

fn collect_resource_fact_reads_from_proposition(
    proposition: &ClickProposition,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    visited_predicates: &mut Vec<String>,
    visited_functions: &mut ResourceFunctionReadEffects,
    reads: &mut Vec<ResourceFactRead>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Value(expression) => {
            collect_resource_fact_reads_from_contract_expression(
                expression,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }

        ClickProposition::Comparison { left, right, .. } => {
            collect_resource_fact_reads_from_contract_expression(
                left,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                right,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::FloatClassification { expression, .. } => {
            collect_resource_fact_reads_from_contract_expression(
                expression,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::Separate { left, right } => {
            collect_resource_fact_reads_from_resource_subject(
                left,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_resource_subject(
                right,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::ResourceViewable { resource } => {
            collect_resource_fact_reads_from_resource_subject(
                resource,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::Contains { parent, child } => {
            collect_resource_fact_reads_from_resource_subject(
                parent,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_resource_subject(
                child,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::Loadable { segment } => {
            collect_resource_fact_reads_from_contract_segment(
                segment,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::Defined { expression }
        | ClickProposition::IsA {
            pointer: expression,
            ..
        } => collect_resource_fact_reads_from_contract_expression(
            expression,
            predicate_definitions,
            click_function_definitions,
            visited_predicates,
            visited_functions,
            reads,
            resource_name,
        ),
        ClickProposition::At { proposition, .. } => collect_resource_fact_reads_from_proposition(
            proposition,
            predicate_definitions,
            click_function_definitions,
            visited_predicates,
            visited_functions,
            reads,
            resource_name,
        ),
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_resource_fact_reads_from_proposition(
                left,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_proposition(
                right,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::Not(body) | ClickProposition::Exists { body, .. } => {
            collect_resource_fact_reads_from_proposition(
                body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::ForAll {
            click_type,
            name,
            body,
            ..
        } => {
            if let ClickProposition::Implies(antecedent, consequent) = body.as_ref() {
                collect_resource_fact_reads_from_proposition(
                    antecedent,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
                let first_consequent_read = reads.len();
                collect_resource_fact_reads_from_proposition(
                    consequent,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
                if let Some((start, end)) = quantified_index_interval(body, name, click_type) {
                    for read in &mut reads[first_consequent_read..] {
                        if read.index == ProgramExpression::Variable((name.clone()).into()) {
                            read.enclosing_range = Some((start.clone(), end.clone()));
                        }
                    }
                }
                Ok(())
            } else {
                collect_resource_fact_reads_from_proposition(
                    body,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )
            }
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
            ..
        } => {
            collect_resource_fact_reads_from_contract_expression(
                start,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                end,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            let first_body_read = reads.len();
            collect_resource_fact_reads_from_proposition(
                body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            let start = contract_expression_as_program_expression(start).ok_or_else(|| {
                ClickError::new(format!(
                    "resource `{resource_name}` range fact has a non-C start"
                ))
            })?;
            let end = contract_expression_as_program_expression(end).ok_or_else(|| {
                ClickError::new(format!(
                    "resource `{resource_name}` range fact has a non-C end"
                ))
            })?;
            for read in &mut reads[first_body_read..] {
                if read.index == ProgramExpression::Variable((item.clone()).into()) {
                    read.enclosing_range = Some((start.clone(), end.clone()));
                }
            }
            Ok(())
        }
        ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            collect_resource_fact_reads_from_contract_expression(
                start,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                end,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_proposition(
                body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ClickProposition::PredicateCall { name, arguments } => {
            for argument in arguments {
                collect_resource_fact_reads_from_contract_expression(
                    argument,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            let Some(definition) = predicate_definitions.get(name.as_str()) else {
                return Ok(());
            };
            if visited_predicates.contains(name) {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` fact cannot use recursive predicate `{name}`"
                )));
            }
            visited_predicates.push(name.clone());
            let body = instantiate_click_predicate_definition(definition, arguments).map_err(
                |message| {
                    ClickError::new(format!(
                        "resource `{resource_name}` fact could not inspect predicate `{name}`: {message}"
                    ))
                },
            )?;
            let result = collect_resource_fact_reads_from_proposition(
                &body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            );
            visited_predicates.pop();
            result
        }
    }
}

/// The index interval a quantified fact's guard confines its binder to. An
/// unsigned binder's lower bound is its type's zero when the guard states
/// none: `k < len` over `k: uint64` confines `k` to `0u64..len`. The upper
/// bound must still come from the guard.
fn quantified_index_interval(
    body: &ClickProposition,
    name: &SurfaceBinder,
    binder_type: &ClickType,
) -> Option<(ProgramExpression, ProgramExpression)> {
    let ClickProposition::Implies(antecedent, _) = body else {
        return None;
    };
    fn visit(
        proposition: &ClickProposition,
        name: &SurfaceBinder,
        lower: &mut Option<ProgramExpression>,
        upper: &mut Option<ProgramExpression>,
    ) {
        match proposition {
            ClickProposition::And(left, right) => {
                visit(left, name, lower, upper);
                visit(right, name, lower, upper);
            }
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => {
                // A comparison of two exact observations bounds the index as
                // the native comparison of the observed values does:
                // `to_integer(k) < to_integer(len + 1u64)` is `k < len + 1u64`.
                fn observed(expression: &ContractExpression) -> Option<&ContractExpression> {
                    match expression {
                        ContractExpression::Call { name, arguments } if name == "to_integer" => {
                            match arguments.as_slice() {
                                [argument] => Some(argument),
                                _ => None,
                            }
                        }
                        _ => None,
                    }
                }
                let (left, right) = match (observed(left), observed(right)) {
                    (Some(left), Some(right)) => (left, right),
                    _ => (left, right),
                };
                let variable = ContractExpression::ProgramExpression(ProgramExpression::Variable(
                    name.kernel_name(),
                ));
                match operator {
                    ComparisonOperator::LessEqual if right == &variable => {
                        *lower = contract_expression_as_program_expression(left);
                    }
                    ComparisonOperator::GreaterEqual if left == &variable => {
                        *lower = contract_expression_as_program_expression(right);
                    }
                    ComparisonOperator::LessThan if left == &variable => {
                        *upper = contract_expression_as_program_expression(right);
                    }
                    ComparisonOperator::GreaterThan if right == &variable => {
                        *upper = contract_expression_as_program_expression(left);
                    }
                    _ => {}
                }
            }
            _ => {}
        }
    }
    let mut lower = None;
    let mut upper = None;
    visit(antecedent, name, &mut lower, &mut upper);
    let lower = lower.or_else(|| unsigned_binder_zero(binder_type))?;
    Some((lower, upper?))
}

/// The zero of an unsigned binder's type, spelled as the matching typed
/// literal, or `None` for a type whose values may be negative.
fn unsigned_binder_zero(binder_type: &ClickType) -> Option<ProgramExpression> {
    let value = match binder_type.interface_type()? {
        InterfaceType::UInt8 => crate::kernel::uint8(0),
        InterfaceType::UInt32 => ProgramValue::UInt32(MachineTerm::uint32_constant(0)),
        InterfaceType::UInt64(_) => ProgramValue::UInt64(MachineTerm::uint64_constant(0)),
        _ => return None,
    };
    Some(ProgramExpression::Value(value))
}

fn collect_resource_fact_reads_from_contract_segment(
    segment: &ContractSegment,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    visited_predicates: &mut Vec<String>,
    visited_functions: &mut ResourceFunctionReadEffects,
    reads: &mut Vec<ResourceFactRead>,
    resource_name: &str,
) -> Result<(), ClickError> {
    for expression in [&segment.base, &segment.start, &segment.end] {
        collect_resource_fact_reads_from_contract_expression(
            &ContractExpression::ProgramExpression(expression.clone()),
            predicate_definitions,
            click_function_definitions,
            visited_predicates,
            visited_functions,
            reads,
            resource_name,
        )?;
    }
    Ok(())
}

fn collect_resource_fact_reads_from_resource_subject(
    resource: &ResourceSubject,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    visited_predicates: &mut Vec<String>,
    visited_functions: &mut ResourceFunctionReadEffects,
    reads: &mut Vec<ResourceFactRead>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceSubject::At { resource, .. } => collect_resource_fact_reads_from_resource_subject(
            resource,
            predicate_definitions,
            click_function_definitions,
            visited_predicates,
            visited_functions,
            reads,
            resource_name,
        ),
        ResourceSubject::Emp => Ok(()),
        ResourceSubject::Star(left, right) => {
            collect_resource_fact_reads_from_resource_subject(
                left,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_resource_subject(
                right,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ResourceSubject::Footprint(_)
        | ResourceSubject::Parameter { .. }
        | ResourceSubject::Instance { .. }
        | ResourceSubject::Captured { .. } => Ok(()),
        ResourceSubject::Memory(segment) => collect_resource_fact_reads_from_contract_segment(
            segment,
            predicate_definitions,
            click_function_definitions,
            visited_predicates,
            visited_functions,
            reads,
            resource_name,
        ),
        ResourceSubject::SavedMemory { base, start, end } => {
            for argument in [base, start].into_iter().chain(end.iter()) {
                collect_resource_fact_reads_from_contract_expression(
                    argument,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            Ok(())
        }
        ResourceSubject::Declared { arguments, .. } => {
            for argument in arguments {
                collect_resource_fact_reads_from_contract_expression(
                    argument,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            Ok(())
        }
    }
}

fn collect_resource_fact_reads_from_contract_expression(
    expression: &ContractExpression,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    visited_predicates: &mut Vec<String>,
    visited_functions: &mut ResourceFunctionReadEffects,
    reads: &mut Vec<ResourceFactRead>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match expression {
        ContractExpression::IntegerContext(value) => {
            collect_resource_fact_reads_from_contract_expression(
                value,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }

        ContractExpression::Proposition(proposition) => {
            collect_resource_fact_reads_from_proposition(
                proposition,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::Resource(_) => Ok(()),
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => Ok(()),
        ContractExpression::Lambda { body, .. } => {
            collect_resource_fact_reads_from_contract_expression(
                body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::Apply {
            function,
            arguments,
        } => {
            collect_resource_fact_reads_from_contract_expression(
                function,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            for argument in arguments {
                collect_resource_fact_reads_from_contract_expression(
                    argument,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            Ok(())
        }

        ContractExpression::IntegerLiteral(_) => Ok(()),
        ContractExpression::CUnary { operand: inner, .. }
        | ContractExpression::MemoryLoad { pointer: inner, .. }
        | ContractExpression::Negate(inner) => {
            collect_resource_fact_reads_from_contract_expression(
                inner,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::ResourceField(_)
        | ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::Binding(_) => Ok(()),
        ContractExpression::AlgebraicConstructor { arguments, .. } => {
            for argument in arguments {
                collect_resource_fact_reads_from_contract_expression(
                    argument,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            Ok(())
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            collect_resource_fact_reads_from_contract_expression(
                scrutinee,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            for arm in arms {
                collect_resource_fact_reads_from_contract_expression(
                    &arm.body,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            Ok(())
        }
        ContractExpression::SequenceLiteral(elements) => {
            for element in elements {
                collect_resource_fact_reads_from_contract_expression(
                    element,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            Ok(())
        }
        ContractExpression::SequenceConcat(left, right) => {
            collect_resource_fact_reads_from_contract_expression(
                left,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                right,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::ProgramExpression(expression)
        | ContractExpression::Field {
            lowered: expression,
            ..
        } => {
            collect_resource_fact_reads_from_program_expression(expression, reads);
            Ok(())
        }
        ContractExpression::ProgramBinding(_) => Ok(()),
        ContractExpression::ResourceWildcard => Err(ClickError::new(format!(
            "`_` is only valid inside a `count(...)` resource pattern in resource `{resource_name}`"
        ))),
        ContractExpression::ResourceCount(resource) => {
            let ResourceClause::Declared { arguments, .. } = resource.as_ref() else {
                return Err(ClickError::new(format!(
                    "`count(...)` inside resource `{resource_name}` expects a declared resource"
                )));
            };
            for argument in arguments {
                if !matches!(argument, ContractExpression::ResourceWildcard) {
                    collect_resource_fact_reads_from_contract_expression(
                        argument,
                        predicate_definitions,
                        click_function_definitions,
                        visited_predicates,
                        visited_functions,
                        reads,
                        resource_name,
                    )?;
                }
            }
            Ok(())
        }
        ContractExpression::Old(_) => Err(ClickError::new(format!(
            "`old(...)` is not available inside resource `{resource_name}` fact"
        ))),
        ContractExpression::At { .. } => Err(ClickError::new(format!(
            "`at(...)` is not available inside resource `{resource_name}` fact"
        ))),
        ContractExpression::Exact(_) => Err(ClickError::new(format!(
            "`exact(...)` is not available inside resource `{resource_name}` fact"
        ))),
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::RustShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::RustShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right) => {
            collect_resource_fact_reads_from_contract_expression(
                left,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                right,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::BitwiseNot(expression) => {
            collect_resource_fact_reads_from_contract_expression(
                expression,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::Index(base, index) => {
            collect_resource_fact_reads_from_contract_expression(
                base,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                index,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            let Some(base) = contract_expression_as_program_expression(base) else {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` fact reads `{}` in a form that cannot be matched to a contained memory resource with current read authority",
                    describe_contract_expression(expression)
                )));
            };
            let Some(index) = contract_expression_as_program_expression(index) else {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` fact reads `{}` in a form that cannot be matched to a contained memory resource with current read authority",
                    describe_contract_expression(expression)
                )));
            };
            reads.push(ResourceFactRead {
                expression: describe_contract_expression(expression),
                base,
                index,
                enclosing_range: None,
                extent: None,
            });
            Ok(())
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_resource_fact_reads_from_proposition(
                condition,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                then_branch,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                else_branch,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_resource_fact_reads_from_contract_expression(
                start,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                end,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                initial,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::Let { value, body, .. } => {
            collect_resource_fact_reads_from_contract_expression(
                value,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_expression(
                body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
        ContractExpression::ArrayIndex { base, .. } => {
            collect_resource_fact_reads_from_contract_expression(
                base,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            Ok(())
        }
        ContractExpression::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            for expression in std::iter::once(receiver.as_ref()).chain(arguments) {
                collect_resource_fact_reads_from_contract_expression(
                    expression,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            Ok(())
        }
        ContractExpression::Call { name, arguments } => {
            for argument in arguments {
                collect_resource_fact_reads_from_contract_expression(
                    argument,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    reads,
                    resource_name,
                )?;
            }
            let Some(definition) = click_function_definitions.get(name.as_str()) else {
                return Ok(());
            };
            if visited_functions.read_free.contains(name) {
                return Ok(());
            }
            if visited_functions.active.contains(name) {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` fact cannot use recursive function `{name}`"
                )));
            }
            visited_functions.active.push(name.clone());
            if !visited_functions.reads_memory.contains(name) {
                #[cfg(test)]
                {
                    visited_functions.body_inspections += 1;
                }
                // Inspect the written body with its formal parameters before
                // substitution. Caller argument reads were collected above.
                // This prevents f(f(x)) from being mistaken for recursion and
                // avoids duplicating a read-free argument inside every body.
                // A primitive operation's value is a pure function of its
                // arguments: it reads no memory of its own.
                let Some(definition_body) = definition.body() else {
                    visited_functions.read_free.insert(name.clone());
                    visited_functions.active.pop();
                    return Ok(());
                };
                let mut body_reads = Vec::new();
                let result = collect_resource_fact_reads_from_contract_expression(
                    definition_body,
                    predicate_definitions,
                    click_function_definitions,
                    visited_predicates,
                    visited_functions,
                    &mut body_reads,
                    resource_name,
                );
                if let Err(error) = result {
                    visited_functions.active.pop();
                    return Err(error);
                }
                if body_reads.is_empty() {
                    visited_functions.read_free.insert(name.clone());
                    visited_functions.active.pop();
                    return Ok(());
                }
                visited_functions.reads_memory.insert(name.clone());
            }
            let substitutions: BTreeMap<_, _> = definition
                .parameters()
                .iter()
                .zip(arguments)
                .map(|(parameter, argument)| (parameter.binding_name(), argument.clone()))
                .collect();
            let Some(definition_body) = definition.body() else {
                return Ok(());
            };
            let body = substitute_contract_expression(definition_body, &substitutions).map_err(
                |message| {
                    ClickError::new(format!(
                        "resource `{resource_name}` fact could not inspect function `{name}`: {message}"
                    ))
                },
            )?;
            let result = collect_resource_fact_reads_from_contract_expression(
                &body,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            );
            visited_functions.active.pop();
            result
        }
    }
}

fn collect_resource_fact_reads_from_program_expression(
    expression: &ProgramExpression,
    reads: &mut Vec<ResourceFactRead>,
) {
    match expression {
        ProgramExpression::StringLiteral(_)
        | ProgramExpression::Value(_)
        | ProgramExpression::Variable(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => {}
        ProgramExpression::Cast { expression, .. } => {
            collect_resource_fact_reads_from_program_expression(expression, reads);
        }
        ProgramExpression::Negate(expression)
        | ProgramExpression::FloatNegate(expression)
        | ProgramExpression::FloatClassification { expression, .. }
        | ProgramExpression::EnumField {
            value: expression, ..
        }
        | ProgramExpression::EnumIs {
            value: expression, ..
        } => {
            collect_resource_fact_reads_from_program_expression(expression, reads);
        }
        ProgramExpression::EnumConstruct { fields, .. } => {
            for field in fields {
                collect_resource_fact_reads_from_program_expression(field, reads);
            }
        }
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_resource_fact_reads_from_program_expression(condition, reads);
            collect_resource_fact_reads_from_program_expression(then_branch, reads);
            collect_resource_fact_reads_from_program_expression(else_branch, reads);
        }
        ProgramExpression::AddressOf(_) | ProgramExpression::CheckedObjectAddress(_) => {}
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => {
            collect_resource_fact_reads_from_program_expression(pointer, reads);
        }
        ProgramExpression::Load(pointer) => {
            collect_resource_fact_reads_from_program_expression(pointer, reads);
            reads.push(ResourceFactRead {
                base: pointer.as_ref().clone(),
                index: ProgramExpression::Value(ProgramValue::Int32(MachineTerm::constant(0))),
                expression: describe_program_expression(expression),
                enclosing_range: None,
                extent: None,
            });
        }
        ProgramExpression::TypedLoad {
            pointer,
            value_type,
            ..
        } => {
            collect_resource_fact_reads_from_program_expression(pointer, reads);
            reads.push(ResourceFactRead {
                base: pointer.as_ref().clone(),
                index: ProgramExpression::Value(ProgramValue::Int32(MachineTerm::constant(0))),
                expression: describe_program_expression(expression),
                enclosing_range: None,
                extent: Some(crate::kernel::AccessExtent::of_type(*value_type)),
            });
        }
        ProgramExpression::Index(base, index) => {
            collect_resource_fact_reads_from_program_expression(base, reads);
            collect_resource_fact_reads_from_program_expression(index, reads);
            reads.push(ResourceFactRead {
                base: base.as_ref().clone(),
                index: index.as_ref().clone(),
                expression: describe_program_expression(expression),
                enclosing_range: None,
                extent: None,
            });
        }
        crate::kernel::binary_c_operation!(left, right) => {
            collect_resource_fact_reads_from_program_expression(left, reads);
            collect_resource_fact_reads_from_program_expression(right, reads);
        }
        ProgramExpression::Not(expression) | ProgramExpression::BitwiseNot(expression) => {
            collect_resource_fact_reads_from_program_expression(expression, reads);
        }
    }
}

/// Whether `segment` is the whole object a typed read at its base reaches,
/// `(p as *u8)[0u64..n]` with `n` the read's extent: a field of a symbolic
/// layout, or a value of abstract type, held whole.
fn object_segment_covers_typed_read(segment: &ContractSegment, read: &ResourceFactRead) -> bool {
    let (
        ProgramExpression::Value(ProgramValue::UInt64(start)),
        ProgramExpression::Value(ProgramValue::UInt64(end)),
        Some(extent),
    ) = (&segment.start, &segment.end, read.extent)
    else {
        return false;
    };
    // A byte range's base, written `(p as *u8)` or, for a symbolic object or
    // field, `p` itself.
    let base = match &segment.base {
        ProgramExpression::Cast {
            expression,
            target_type: ProgramType::UInt8Pointer,
            ..
        } => expression.as_ref(),
        base => base,
    };
    if !matches!(&read.index, ProgramExpression::Value(ProgramValue::Int32(index)) if index.as_const() == Some(0))
        || start.uint64_as_const() != Some(0)
    {
        return false;
    }
    if *base == read.base {
        return *end == extent.term();
    }
    // A field's read inside the whole object of its symbolic layout, by the
    // layout's rule: `p + offsetof(L, f)` reaching no further than `f`, in
    // `(p as *u8)[0u64..sizeof(L)]`.
    let ProgramExpression::PointerOffsetBytes {
        pointer,
        bytes: crate::kernel::LayoutOffset::Field(layout, field),
    } = &read.base
    else {
        return false;
    };
    **pointer == *base && *end == layout.size_term() && layout.within_field(*field, extent)
}

fn analyze_resource_fact_read_authority(
    read: &ResourceFactRead,
    contained: &[ResourceClause],
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    at: &crate::kernel::ProgramPoint,
    spec_definitions: SpecDefinitions<'_>,
) -> ResourceFactReadAuthorityAnalysis {
    let mut notes = Vec::new();
    for resource in contained {
        let (segment, access) = match resource {
            ResourceClause::OwnMemory(segment) => (segment, "owned"),
            ResourceClause::ViewMemory(segment) => (segment, "viewed"),
            _ => {
                notes.push(format!(
                    "`{}` is not a memory resource with read authority",
                    describe_resource_clause(resource)
                ));
                continue;
            }
        };
        let resource_description = describe_resource_clause(resource);
        if segment.state != ContractSegmentState::Current {
            notes.push(format!(
                "`{resource_description}` is not a current-state {access} memory resource"
            ));
            continue;
        }
        if object_segment_covers_typed_read(segment, read) {
            return ResourceFactReadAuthorityAnalysis {
                covered: true,
                notes,
            };
        }
        if segment.base == read.base
            && constant_segment_covers_index(&segment.start, &segment.end, &read.index)
        {
            return ResourceFactReadAuthorityAnalysis {
                covered: true,
                notes,
            };
        }
        if segment.base == read.base {
            if read.enclosing_range.as_ref().is_some_and(|(start, end)| {
                symbolic_segment_covers_range(
                    &segment.start,
                    &segment.end,
                    start,
                    end,
                    assumptions,
                    contract_environment,
                    at,
                    spec_definitions,
                )
            }) {
                return ResourceFactReadAuthorityAnalysis {
                    covered: true,
                    notes,
                };
            }
            if symbolic_segment_covers_index(
                &segment.start,
                &segment.end,
                &read.index,
                assumptions,
                contract_environment,
                at,
                spec_definitions,
            ) {
                return ResourceFactReadAuthorityAnalysis {
                    covered: true,
                    notes,
                };
            }
            notes.push(format!(
                "`{resource_description}` has the right base, but the available scalar facts do not prove `{}` <= `{}` < `{}`",
                describe_program_expression(&segment.start),
                describe_program_expression(&read.index),
                describe_program_expression(&segment.end)
            ));
            continue;
        }
        if evaluated_segment_covers_resource_fact_read(
            segment,
            read,
            assumptions,
            contract_environment,
            at,
        ) {
            return ResourceFactReadAuthorityAnalysis {
                covered: true,
                notes,
            };
        }
        notes.push(format!(
            "`{resource_description}` does not prove coverage of `{}`",
            read.expression
        ));
    }
    ResourceFactReadAuthorityAnalysis {
        covered: false,
        notes,
    }
}

fn resource_fact_read_authority_error(
    resource_name: &str,
    read: &ResourceFactRead,
    analysis: &ResourceFactReadAuthorityAnalysis,
    scalar_assumptions: &[ResourceFactScalarAssumption],
) -> String {
    let mut lines = vec![format!(
        "resource `{resource_name}` fact reads `{}` without a covering contained memory resource with current read authority",
        read.expression
    )];
    if analysis.notes.is_empty() {
        lines.push("note: the composite body contains no resources to consider".to_string());
    } else {
        lines.push("note: contained resource coverage considered:".to_string());
        lines.extend(analysis.notes.iter().map(|note| format!("  - {note}")));
    }
    if scalar_assumptions.is_empty() {
        lines.push(
            "note: no scalar fact assumptions were available to prove symbolic coverage"
                .to_string(),
        );
    } else {
        lines.push(format!(
            "note: scalar fact assumptions available: {}",
            scalar_assumptions
                .iter()
                .map(|assumption| assumption.source.as_str())
                .collect::<Vec<_>>()
                .join(", ")
        ));
    }
    lines.join("\n")
}

fn evaluated_segment_covers_resource_fact_read(
    segment: &ContractSegment,
    read: &ResourceFactRead,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    at: &crate::kernel::ProgramPoint,
) -> bool {
    let state = ExecutionState::at_point(at);
    let evaluate = |expression: &ProgramExpression| {
        crate::surface::proof::evaluate_program_expression_through_kernel(
            expression,
            assumptions,
            contract_environment,
            &state,
            None,
        )
    };
    let Ok(ProgramValue::Pointer(base)) = evaluate(&segment.base) else {
        return false;
    };
    let Ok(ProgramValue::Int32(start)) = evaluate(&segment.start) else {
        return false;
    };
    let Ok(ProgramValue::Int32(end)) = evaluate(&segment.end) else {
        return false;
    };
    let Ok(ProgramValue::Pointer(read_base)) = evaluate(&read.base) else {
        return false;
    };
    let Ok(ProgramValue::Int32(index)) = evaluate(&read.index) else {
        return false;
    };
    // A field's segment counts elements of the field's width, `owns c.len`
    // of a `usize` eight bytes; a read's index counts `int32` cells.
    let segment = EvaluatedContractSegment {
        element_width: segment.field_element_width().unwrap_or(4),
        source: segment.clone(),
        base: base.into_pointer(),
        start,
        end,
    };
    let read_pointer = offset_pointer_by_elements(read_base.into_pointer(), index, 4);
    segment_contains_pointer(&segment, &read_pointer, assumptions)
}

fn symbolic_segment_covers_range(
    available_start: &ProgramExpression,
    available_end: &ProgramExpression,
    required_start: &ProgramExpression,
    required_end: &ProgramExpression,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    at: &crate::kernel::ProgramPoint,
    spec_definitions: SpecDefinitions<'_>,
) -> bool {
    let state = ExecutionState::at_point(at);
    let evaluate = |expression: &ProgramExpression| {
        crate::surface::proof::evaluate_fixed_state_expression_through_kernel(
            &ContractExpression::ProgramExpression(expression.clone()),
            &PureFactContext::new(),
            contract_environment,
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            spec_definitions,
            &BTreeSet::new(),
        )
    };
    let Ok(available_start) = evaluate(available_start) else {
        return false;
    };
    let Ok(available_end) = evaluate(available_end) else {
        return false;
    };
    let Ok(required_start) = evaluate(required_start) else {
        return false;
    };
    let Ok(required_end) = evaluate(required_end) else {
        return false;
    };
    let Ok(lower_bound) = comparison_proposition(
        available_start,
        ComparisonOperator::LessEqual,
        required_start,
    ) else {
        return false;
    };
    let Ok(upper_bound) =
        comparison_proposition(required_end, ComparisonOperator::LessEqual, available_end)
    else {
        return false;
    };
    crate::kernel::search::ProofSearch::proves(assumptions, &lower_bound)
        && crate::kernel::search::ProofSearch::proves(assumptions, &upper_bound)
}

fn symbolic_segment_covers_index(
    start: &ProgramExpression,
    end: &ProgramExpression,
    index: &ProgramExpression,
    assumptions: &PureFactContext,
    contract_environment: ContractEnvironment<'_>,
    at: &crate::kernel::ProgramPoint,
    spec_definitions: SpecDefinitions<'_>,
) -> bool {
    let state = ExecutionState::at_point(at);
    let evaluate = |expression: &ProgramExpression| {
        crate::surface::proof::evaluate_fixed_state_expression_through_kernel(
            &ContractExpression::ProgramExpression(expression.clone()),
            &PureFactContext::new(),
            contract_environment,
            FixedStateFrame::new(&state, &state, None, &RecordedStates::new()),
            spec_definitions,
            &BTreeSet::new(),
        )
    };
    let Ok(start) = evaluate(start) else {
        return false;
    };
    let Ok(end) = evaluate(end) else {
        return false;
    };
    let Ok(index) = evaluate(index) else {
        return false;
    };
    let Ok(lower_bound) =
        comparison_proposition(start, ComparisonOperator::LessEqual, index.clone())
    else {
        return false;
    };
    let Ok(upper_bound) = comparison_proposition(index, ComparisonOperator::LessThan, end) else {
        return false;
    };
    crate::kernel::search::ProofSearch::proves(assumptions, &lower_bound)
        && crate::kernel::search::ProofSearch::proves(assumptions, &upper_bound)
}

fn constant_segment_covers_index(
    start: &ProgramExpression,
    end: &ProgramExpression,
    index: &ProgramExpression,
) -> bool {
    let Some(start) = constant_program_expression_i64(start) else {
        return false;
    };
    let Some(end) = constant_program_expression_i64(end) else {
        return false;
    };
    let Some(index) = constant_program_expression_i64(index) else {
        return false;
    };
    start <= index && index < end
}

fn constant_program_expression_i64(expression: &ProgramExpression) -> Option<i64> {
    match expression {
        ProgramExpression::Value(ProgramValue::Int32(bits32_constant!(value))) => {
            Some(constant_u32(*value) as i32 as i64)
        }
        ProgramExpression::Value(ProgramValue::UInt8(bits32_constant!(value))) => {
            Some(i64::from(constant_u32(*value)))
        }
        ProgramExpression::Add(left, right) => {
            Some(constant_program_expression_i64(left)? + constant_program_expression_i64(right)?)
        }
        ProgramExpression::Subtract(left, right) => {
            Some(constant_program_expression_i64(left)? - constant_program_expression_i64(right)?)
        }
        _ => None,
    }
}

fn declared_composite_resource_name(resource: &ResourceClause) -> Option<&str> {
    match resource {
        ResourceClause::Conditional { resource, .. } => declared_composite_resource_name(resource),
        ResourceClause::Named { resource, .. } => declared_composite_resource_name(resource),
        ResourceClause::Declared {
            kind: ResourceKind::Composite,
            name,
            ..
        } => Some(name),
        ResourceClause::Quantified { resource, .. } => declared_composite_resource_name(resource),
        ResourceClause::ViewMemory(_)
        | ResourceClause::OwnMemory(_)
        | ResourceClause::MemoryAggregate { .. }
        | ResourceClause::Declared { .. }
        | ResourceClause::Iterated(_) => None,
    }
}

fn reject_composite_resource_cycles(definitions: &[ResourceDefinition]) -> Result<(), ClickError> {
    let graph: BTreeMap<_, _> = definitions
        .iter()
        .map(|definition| {
            let dependencies = definition
                .composite_body()
                .into_iter()
                .flat_map(CompositeResourceBody::contains)
                .filter_map(|resource| match resource {
                    ResourceClause::Conditional { resource, .. } => {
                        declared_composite_resource_name(resource).map(str::to_string)
                    }
                    ResourceClause::Named { resource, .. } => {
                        declared_composite_resource_name(resource).map(str::to_string)
                    }
                    ResourceClause::Declared {
                        kind: ResourceKind::Composite,
                        name,
                        ..
                    } => Some(name.clone()),
                    ResourceClause::ViewMemory(_)
                    | ResourceClause::OwnMemory(_)
                    | ResourceClause::MemoryAggregate { .. } => None,
                    ResourceClause::Declared { .. }
                    | ResourceClause::Quantified { .. }
                    | ResourceClause::Iterated(_) => None,
                })
                .filter(|dependency| {
                    dependency != definition.name()
                        || definition
                            .composite_body()
                            .is_none_or(|body| body.condition().is_none())
                })
                // A matched arm's children are containment too, and a child
                // may name another definition. The arm itself is the guard
                // that makes direct recursion finite, so only a cycle through
                // another definition is reported here.
                .chain(
                    definition
                        .composite_body()
                        .and_then(|body| body.matched.as_ref())
                        .into_iter()
                        .flat_map(|matched| &matched.arms)
                        .flat_map(|arm| &arm.body.contains)
                        .filter_map(|resource| {
                            declared_composite_resource_name(resource).map(str::to_string)
                        })
                        .filter(|dependency| dependency != definition.name()),
                )
                .collect::<Vec<_>>();
            (definition.name().to_string(), dependencies)
        })
        .collect();
    let mut permanent = BTreeSet::new();
    let mut visiting = Vec::new();
    for name in graph.keys() {
        reject_composite_resource_cycles_from(name, &graph, &mut permanent, &mut visiting)?;
    }
    Ok(())
}

fn reject_composite_resource_cycles_from(
    name: &str,
    graph: &BTreeMap<String, Vec<String>>,
    permanent: &mut BTreeSet<String>,
    visiting: &mut Vec<String>,
) -> Result<(), ClickError> {
    if permanent.contains(name) {
        return Ok(());
    }
    if let Some(index) = visiting.iter().position(|candidate| candidate == name) {
        let mut cycle = visiting[index..].to_vec();
        cycle.push(name.to_string());
        return Err(ClickError::new(format!(
            "composite resource cycle: {}",
            cycle.join(" -> ")
        )));
    }
    visiting.push(name.to_string());
    for dependency in graph.get(name).into_iter().flatten() {
        if graph.contains_key(dependency) {
            reject_composite_resource_cycles_from(dependency, graph, permanent, visiting)?;
        }
    }
    visiting.pop();
    permanent.insert(name.to_string());
    Ok(())
}

#[cfg(test)]
mod read_authority_tests {
    use super::*;
    use crate::surface::parser;

    fn segment(
        state: ContractSegmentState,
        base: ProgramExpression,
        start: ProgramExpression,
        end: ProgramExpression,
    ) -> ContractSegment {
        ContractSegment {
            uninitialized: false,
            state,
            surface: ContractSegmentSurface::Range {
                base: ContractExpression::ProgramExpression(base.clone()),
                start: ContractExpression::ProgramExpression(start.clone()),
                end: ContractExpression::ProgramExpression(end.clone()),
            },
            base,
            start,
            end,
        }
    }

    fn read(base: ProgramExpression, index: ProgramExpression) -> ResourceFactRead {
        ResourceFactRead {
            base,
            index,
            expression: "cell[index]".to_string(),
            enclosing_range: None,
            extent: None,
        }
    }

    fn analysis(
        read: &ResourceFactRead,
        contained: &[ResourceClause],
        assumptions: &PureFactContext,
        values: &ProgramValueBindings,
    ) -> ResourceFactReadAuthorityAnalysis {
        analyze_resource_fact_read_authority(
            read,
            contained,
            assumptions,
            ContractEnvironment::new(values, &BTreeMap::new()),
            &crate::kernel::ProgramPoint::starting_at(&SymbolicMemory::new()),
            SpecDefinitions::new(
                &PredicateEnvironment::new(&[]),
                &ClickFunctionEnvironment::new(&[]),
            ),
        )
    }

    #[test]
    fn current_view_covers_a_zero_valued_cell() {
        let base = ProgramExpression::Variable(("cell".to_string()).into());
        let clause = ResourceClause::ViewMemory(segment(
            ContractSegmentState::Current,
            base.clone(),
            ProgramExpression::Value(int32(0)),
            ProgramExpression::Value(int32(1)),
        ));
        let result = analysis(
            &read(base, ProgramExpression::Value(int32(0))),
            &[clause],
            &PureFactContext::new(),
            &ProgramValueBindings::new(),
        );
        assert!(
            result.covered,
            "a view covers reads regardless of the cell value"
        );
    }

    #[test]
    fn current_view_accepts_a_symbolic_in_bounds_read() {
        let base = ProgramExpression::Variable(("cell".to_string()).into());
        let index = ProgramExpression::Variable(("index".to_string()).into());
        let bound = ProgramExpression::Variable(("bound".to_string()).into());
        let clause = ResourceClause::ViewMemory(segment(
            ContractSegmentState::Current,
            base.clone(),
            ProgramExpression::Value(int32(0)),
            bound.clone(),
        ));
        let index_value = MachineTerm::Variable(Variable(12_001));
        let bound_value = MachineTerm::Variable(Variable(12_002));
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessEqual,
                    left: Box::new(MachineTerm::constant(0)),
                    right: Box::new(index_value.clone()),
                },
                true,
            ))
            .assume_proposition(Proposition::condition_is(
                ConditionTerm::Compare {
                    format: MachineIntegerType::Int32,
                    relation: CompareRelation::LessThan,
                    left: Box::new(index_value.clone()),
                    right: Box::new(bound_value.clone()),
                },
                true,
            ));
        let values = ProgramValueBindings::from([
            ("index".to_string(), ProgramValue::Int32(index_value)),
            ("bound".to_string(), ProgramValue::Int32(bound_value)),
        ]);
        let result = analysis(&read(base, index), &[clause], &assumptions, &values);
        assert!(
            result.covered,
            "scalar bounds should establish view coverage"
        );
    }

    #[test]
    fn current_view_does_not_cover_its_neighbor() {
        let base = ProgramExpression::Variable(("cell".to_string()).into());
        let clause = ResourceClause::ViewMemory(segment(
            ContractSegmentState::Current,
            base.clone(),
            ProgramExpression::Value(int32(0)),
            ProgramExpression::Value(int32(1)),
        ));
        let result = analysis(
            &read(base, ProgramExpression::Value(int32(1))),
            &[clause],
            &PureFactContext::new(),
            &ProgramValueBindings::new(),
        );
        assert!(!result.covered, "a neighboring cell is outside the view");
    }

    #[test]
    fn old_view_does_not_cover_a_current_resource_fact() {
        let base = ProgramExpression::Variable(("cell".to_string()).into());
        let clause = ResourceClause::ViewMemory(segment(
            ContractSegmentState::Old,
            base.clone(),
            ProgramExpression::Value(int32(0)),
            ProgramExpression::Value(int32(1)),
        ));
        let result = analysis(
            &read(base, ProgramExpression::Value(int32(0))),
            &[clause],
            &PureFactContext::new(),
            &ProgramValueBindings::new(),
        );
        assert!(
            !result.covered,
            "old memory cannot supply current read authority"
        );
        assert!(
            result
                .notes
                .iter()
                .any(|note| note.contains("not a current-state viewed memory resource"))
        );
    }

    #[test]
    fn public_definition_validation_accepts_a_viewed_fact_read() {
        let file =
            parser::parse("resource viewed_cell(p: int32*) { views p[0..1]; fact p[0] == 0; }")
                .expect("the viewed resource definition should parse");
        validate_click_definitions(&file)
            .expect("current viewed memory should provide static read authority");
    }

    #[test]
    fn public_definition_validation_rejects_an_uncovered_viewed_fact_read() {
        let error =
            parser::parse("resource viewed_neighbor(p: int32*) { views p[0..1]; fact p[1] == 0; }")
                .expect_err("an uncovered viewed fact read must reach public validation");
        assert!(error.message().contains("current read authority"));
    }
}

#[cfg(test)]
mod contract_name_tests {
    use super::*;

    #[test]
    fn unknown_contract_names_are_refused_without_checking_a_proof() {
        for (clause, name) in [
            ("requires missing > 0; ensures result == 1;", "missing"),
            ("ensures result == one;", "one"),
            ("ensures forall (k: int32) { k == absent };", "absent"),
        ] {
            let source = format!("int32 f(int32 x) {{ {clause} }} by {{ close(); }}");
            let file = crate::surface::parser::parse_file_items(&source).unwrap();
            let error = validate_click_definitions(&file).unwrap_err();
            assert!(
                error.message().contains(&format!("unknown name `{name}`")),
                "{}",
                error.message()
            );
            assert!(!error.message().contains("tactic"), "{}", error.message());
            assert!(
                !error.message().contains("kernel lowering"),
                "{}",
                error.message()
            );
        }
    }

    #[test]
    fn true_and_false_are_bool_literals_that_compare_only_with_bool_values() {
        for (clause, accepted) in [
            ("ensures result == true;", false),
            ("ensures result == false;", false),
            ("requires x; ensures result == x;", false),
            ("requires flag; ensures result == x;", true),
            ("requires flag == false; ensures result == x;", true),
            ("ensures result == 1 or flag != true;", true),
        ] {
            let source = format!("int32 f(int32 x, bool flag) {{ {clause} }} by {{ close(); }}");
            let file = crate::surface::parser::parse_file_items(&source).unwrap();
            let result = validate_click_definitions(&file);
            if accepted {
                result.unwrap_or_else(|error| panic!("{clause}: {}", error.message()));
            } else {
                let error = result.unwrap_err();
                assert!(
                    error.message().contains("not Bool"),
                    "{clause}: {}",
                    error.message()
                );
                assert!(
                    !error.message().contains("unknown name"),
                    "{}",
                    error.message()
                );
            }
        }
    }

    #[test]
    fn a_c_parameter_spelled_true_keeps_its_c_meaning() {
        let source = "int32 f(int32 true) { ensures result == true + 1; } by { close(); }";
        let file = crate::surface::parser::parse_file_items(source).unwrap();
        validate_click_definitions(&file).unwrap();
    }

    #[test]
    fn contract_names_respect_parameters_lets_and_quantifier_scope() {
        let file = crate::surface::parser::parse_file_items(
            r#"
int32 f(int32 x) {
    let saved = x;
    requires forall (k: int32) { k == k };
    ensures forall (x: int32) { saved == saved and x == x };
} by { close(); }
"#,
        )
        .unwrap();
        validate_click_definitions(&file).unwrap();
    }
}

#[cfg(test)]
mod resource_function_composition_tests {
    use super::*;

    #[test]
    fn nested_read_free_getters_inspect_the_definition_once() {
        let file =
            parser::parse_file_items("function identity(value: int32) -> int32 { value }").unwrap();
        let definitions = file
            .click_function_definitions()
            .iter()
            .map(|definition| (definition.name(), definition))
            .collect();
        for depth in [16, 64, 256] {
            let mut expression =
                ContractExpression::ProgramExpression(ProgramExpression::Value(int32(0)));
            for _ in 0..depth {
                expression = ContractExpression::Call {
                    name: "identity".into(),
                    arguments: vec![expression],
                };
            }
            let mut effects = ResourceFunctionReadEffects::default();
            let mut reads = Vec::new();
            collect_resource_fact_reads_from_contract_expression(
                &expression,
                &BTreeMap::new(),
                &definitions,
                &mut Vec::new(),
                &mut effects,
                &mut reads,
                "nested",
            )
            .unwrap();
            assert!(reads.is_empty());
            assert_eq!(
                effects.body_inspections, 1,
                "depth {depth} must inspect only the one definition"
            );
            assert!(effects.active.is_empty());
        }
    }
}
