use super::*;
use crate::surface::planning::proposition_search::PropositionSearch;

pub(in crate::surface) fn validate_click_definitions(file: &ClickFile) -> Result<(), ClickError> {
    validate_algebraic_type_declarations(file)?;
    let predicate_definitions = combined_predicate_definitions(file)?;
    let click_function_definitions = combined_click_function_definitions(file)?;
    let resource_definitions = combined_resource_definitions(file)?;
    let theorem_definitions = combined_theorem_definitions(file)?;

    let mut predicates = BTreeMap::new();
    for definition in &predicate_definitions {
        if matches!(
            definition.name(),
            "same_object" | crate::kernel::SAME_OBJECT_PREDICATE_NAME
        ) {
            return Err(ClickError::new(
                "`same_object` is a built-in proposition and cannot be redefined",
            ));
        }
        generics::validate_type_parameter_list(
            "predicate",
            definition.name(),
            definition.type_parameters(),
        )?;
        if predicates
            .insert(definition.name().to_string(), definition.parameters().len())
            .is_some()
        {
            return Err(ClickError::new(format!(
                "duplicate predicate definition `{}`",
                definition.name()
            )));
        }
    }

    let mut contracts = BTreeMap::new();
    for definition in file.contract_definitions() {
        if matches!(
            definition.name(),
            "same_object" | crate::kernel::SAME_OBJECT_PREDICATE_NAME
        ) {
            return Err(ClickError::new(
                "`same_object` is a built-in proposition and cannot be redefined",
            ));
        }
        if predicates.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a predicate and a contract",
                definition.name()
            )));
        }
        if contracts
            .insert(
                definition.name().to_string(),
                definition.function_pointer_type(),
            )
            .is_some()
        {
            return Err(ClickError::new(format!(
                "duplicate contract definition `{}`",
                definition.name()
            )));
        }
    }
    let mut proposition_calls = predicates.clone();
    proposition_calls.insert("same_object".to_string(), 2);
    proposition_calls.extend(contracts.keys().map(|name| (name.clone(), 1)));

    let mut click_functions = BTreeMap::new();
    let mut click_function_types = BTreeMap::new();
    for definition in &click_function_definitions {
        generics::validate_type_parameter_list(
            "function",
            definition.name(),
            definition.type_parameters(),
        )?;
        if contracts.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a contract and a function",
                definition.name()
            )));
        }
        if predicates.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a predicate and a function",
                definition.name()
            )));
        }
        if is_integer_conversion(definition.name()) || definition.name() == "to_nat" {
            return Err(ClickError::new(format!(
                "`{}` is a built-in Integer conversion name",
                definition.name()
            )));
        }
        if click_functions
            .insert(definition.name().to_string(), definition.parameters().len())
            .is_some()
        {
            return Err(ClickError::new(format!(
                "duplicate function definition `{}`",
                definition.name()
            )));
        }
        click_function_types.insert(
            definition.name().to_string(),
            ClickFunctionType {
                type_parameters: definition.type_parameters().to_vec(),
                parameters: definition.parameters().to_vec(),
                return_type: definition.return_type().clone(),
            },
        );
    }
    validate_algebraic_type_uses(file, &click_function_types)?;

    let mut resources = BTreeMap::new();
    for definition in &resource_definitions {
        if matches!(definition.name(), "read" | "write") {
            return Err(ClickError::new(format!(
                "`{}` is a built-in resource name",
                definition.name()
            )));
        }
        if predicates.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a predicate and a resource",
                definition.name()
            )));
        }
        if contracts.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a contract and a resource",
                definition.name()
            )));
        }
        if click_functions.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a function and a resource",
                definition.name()
            )));
        }
        if resources
            .insert(definition.name().to_string(), definition.parameters().len())
            .is_some()
        {
            return Err(ClickError::new(format!(
                "duplicate resource definition `{}`",
                definition.name()
            )));
        }
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

    let mut theorems = BTreeMap::new();
    for definition in &theorem_definitions {
        generics::validate_type_parameter_list(
            "theorem",
            definition.name(),
            definition.type_parameters(),
        )?;
        if predicates.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a predicate and a theorem",
                definition.name()
            )));
        }
        if contracts.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a contract and a theorem",
                definition.name()
            )));
        }
        if click_functions.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a function and a theorem",
                definition.name()
            )));
        }
        if resources.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a resource and a theorem",
                definition.name()
            )));
        }
        if theorems
            .insert(definition.name().to_string(), definition.parameters().len())
            .is_some()
        {
            return Err(ClickError::new(format!(
                "duplicate theorem definition `{}`",
                definition.name()
            )));
        }
    }

    let predicate_definition_map = predicate_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();
    let click_function_definition_map = click_function_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions)
        .with_contracts(file.contract_definitions());
    let click_function_environment = ClickFunctionEnvironment::with_algebraic_types(
        &click_function_definitions,
        &combined_algebraic_type_definitions(file)?,
    );

    let resource_definition_map = resource_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();
    for definition in &resource_definitions {
        validate_resource_definition(
            definition,
            &resource_definition_map,
            &resources,
            &recursive_resources,
            &proposition_calls,
            &contracts,
            &click_functions,
            &click_function_types,
            &predicate_definition_map,
            &click_function_definition_map,
            &predicate_environment,
            &click_function_environment,
        )?;
    }
    reject_composite_resource_cycles(&resource_definitions)?;

    for definition in &predicate_definitions {
        let variables = definition
            .parameters()
            .iter()
            .filter_map(|parameter| {
                parameter
                    .click_type()
                    .c_type()
                    .map(|c_type| (parameter.name().to_string(), c_type))
            })
            .collect::<BTreeMap<_, _>>();
        validate_predicate_calls_in_proposition(
            definition.body(),
            &proposition_calls,
            &click_functions,
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
        validate_click_function_expression(
            definition.body(),
            &click_functions,
            &format!("function `{}`", definition.name()),
        )?;
        let mut calls = BTreeSet::new();
        collect_click_function_calls(definition.body(), &mut calls);
        function_calls.insert(definition.name().to_string(), calls);
    }
    validate_well_founded_click_recursion(
        &click_function_definitions,
        &function_calls,
        &combined_algebraic_type_definitions(file)?,
    )?;

    for theorem in &theorem_definitions {
        validate_theorem_definition(
            theorem,
            &proposition_calls,
            &contracts,
            &click_functions,
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
                &resources,
                &recursive_resources,
                &click_functions,
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

        reject_duplicate_owned_declared_resource_clauses(
            function
                .requires()
                .iter()
                .filter_map(|requirement| match requirement.inner() {
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
                &resources,
                &recursive_resources,
                &click_functions,
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

        let mut requirement_labels = BTreeSet::new();
        for requirement in function.requires() {
            if let Some(label) = requirement.label()
                && !requirement_labels.insert(label.to_string())
            {
                return Err(ClickError::new(format!(
                    "duplicate requirement label `{label}` in `{}`",
                    function.signature().name()
                )));
            }
            if let Some(proposition) = requirement.proposition() {
                let context = format!("requires clause in `{}`", function.signature().name());
                validate_predicate_calls_in_proposition(
                    proposition,
                    &proposition_calls,
                    &click_functions,
                    &context,
                )?;
                validate_contract_applications_in_proposition(
                    proposition,
                    &contracts,
                    &requires_type_environment,
                    &click_function_types,
                    &context,
                )?;
            } else if let Requirement::Resource(resource) = requirement.inner() {
                validate_resource_clause(
                    resource,
                    &resources,
                    &recursive_resources,
                    &click_functions,
                    &click_function_types,
                    &requires_type_environment,
                    &format!("requires clause in `{}`", function.signature().name()),
                )?;
            }
        }

        for structural_clause in function.structural_clauses() {
            for item in structural_clause.items() {
                {
                    let proposition = item.proposition();
                    let context = format!("invariant clause in `{}`", function.signature().name());
                    validate_predicate_calls_in_proposition(
                        proposition,
                        &proposition_calls,
                        &click_functions,
                        &context,
                    )?;
                    validate_contract_applications_in_proposition(
                        proposition,
                        &contracts,
                        &requires_type_environment,
                        &click_function_types,
                        &context,
                    )?;
                }
            }
        }

        for ensure in function.ensures() {
            match ensure.ensure() {
                Ensure::Proposition(proposition) => {
                    let context = format!("ensures clause in `{}`", function.signature().name());
                    validate_predicate_calls_in_proposition(
                        proposition,
                        &proposition_calls,
                        &click_functions,
                        &context,
                    )?;
                    validate_contract_applications_in_proposition(
                        proposition,
                        &contracts,
                        &ensures_type_environment,
                        &click_function_types,
                        &context,
                    )?;
                    if function.signature().return_type() == C0Type::Void {
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
                            &BTreeSet::new(),
                            &click_function_types,
                            &format!("ensures clause in `{}`", function.signature().name()),
                        )?;
                    }
                }
                Ensure::Resource(resource) => validate_resource_clause(
                    resource,
                    &resources,
                    &recursive_resources,
                    &click_functions,
                    &click_function_types,
                    &ensures_type_environment,
                    &format!("ensures clause in `{}`", function.signature().name()),
                )?,
            }
        }

        if function.ensures().is_empty()
            && !function
                .requires()
                .iter()
                .any(requirement_contains_resource)
        {
            return Err(ClickError::new(format!(
                "`{}` must contain at least one `ensures` or resource-consuming `requires` clause",
                function.signature().name()
            )));
        }
    }

    Ok(())
}

fn validate_contract_applications_in_proposition(
    proposition: &ClickProposition,
    contracts: &BTreeMap<String, C0Type>,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
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
    contracts: &BTreeMap<String, C0Type>,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::PredicateCall { name, arguments } => {
            if name == "same_object" {
                let [left, right] = arguments.as_slice() else {
                    return Err(ClickError::new(format!(
                        "same_object expects two pointer arguments in {context}, got {}",
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
                    if !actual.is_some_and(C0Type::is_object_pointer) {
                        return Err(ClickError::new(format!(
                            "same_object expects pointer arguments in {context}, got {}",
                            actual.map_or_else(|| "an unknown type".to_string(), describe_c0_type)
                        )));
                    }
                }
                return Ok(());
            }
            let Some(expected) = contracts.get(name) else {
                return Ok(());
            };
            let [argument] = arguments.as_slice() else {
                return Err(ClickError::new(format!(
                    "contract `{name}` expects one function-pointer argument in {context}"
                )));
            };
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
                    describe_c0_type(*expected),
                    actual.map_or_else(|| "an unknown type".to_string(), describe_c0_type),
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
            click_type: c_type,
            name,
            body,
            ..
        }
        | ClickProposition::Exists {
            click_type: c_type,
            name,
            body,
            ..
        } => {
            let mut variables = variables.clone();
            match c_type {
                ClickType::C(c_type) => {
                    variables.insert(name.clone(), *c_type);
                }
                ClickType::Integer => {
                    variables.remove(name);
                }
                ClickType::Algebraic(_) => {
                    variables.remove(name);
                }
                ClickType::Parameter(_) => {
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
            variables.insert(item.clone(), C0Type::Int32);
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
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. } => Ok(()),
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

fn validate_theorem_definition(
    theorem: &TheoremDefinition,
    predicates: &BTreeMap<String, usize>,
    contracts: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
) -> Result<(), ClickError> {
    if theorem.ensures().is_empty() {
        return Err(ClickError::new(format!(
            "theorem `{}` must contain at least one `ensures` clause",
            theorem.name()
        )));
    }

    let variables = theorem_type_environment(theorem);
    let mut requirement_labels = BTreeSet::new();
    for requirement in theorem.requires() {
        if let Some(label) = requirement.label()
            && !requirement_labels.insert(label.to_string())
        {
            return Err(ClickError::new(format!(
                "duplicate requirement label `{label}` in theorem `{}`",
                theorem.name()
            )));
        }
        let Some(proposition) = requirement.theorem_proposition() else {
            return Err(ClickError::new(theorem_resource_clause_refusal(
                theorem.name(),
            )));
        };
        let proposition = &proposition;
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
    contracts: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), ClickError> {
    let Some(composite_body) = definition.composite_body() else {
        return Ok(());
    };
    if composite_body.guarded_by().is_some()
        && (composite_body.matched.is_some()
            || composite_body
                .facts()
                .iter()
                .any(proposition_contains_resource_count))
    {
        return Err(ClickError::new(format!(
            "resource `{}` must be exclusive and unmatched to use `guarded_by`",
            definition.name()
        )));
    }
    if composite_body.matched.is_some() {
        for (_, _, arm) in resource_match_arm_scopes(
            definition,
            |name| {
                click_function_environment
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
                predicate_environment,
                click_function_environment,
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
            predicate_environment,
            click_function_environment,
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
            predicate_environment,
            click_function_environment,
        );
    }
    let mut variables = definition
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect::<BTreeMap<_, _>>();
    for witness in composite_body.witnesses() {
        if variables
            .insert(witness.name().to_string(), witness.c_type())
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
            &mut Vec::new(),
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
        predicate_environment,
        click_function_environment,
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
            predicate_environment,
            click_function_environment,
        )?;
        prior_facts.push(fact);
    }
    Ok(())
}

/// Checks every iterated guarded-ownership clause of one body: the kernel can
/// read its shape, the index shadows nothing, the guard reads only cells the
/// same body owns (so no one can change it while the resource is folded), and
/// the guard cells are not themselves elements.
#[allow(clippy::too_many_arguments)]
fn validate_iterated_resource_clauses(
    definition: &ResourceDefinition,
    composite_body: &CompositeResourceBody,
    variables: &BTreeMap<String, C0Type>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
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
        let index = clause.binder.as_str();
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
        scoped.insert(index.to_string(), C0Type::Int32);
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
                if ty != C0Type::Int32 {
                    return Err(ClickError::new(format!(
                        "{context}: the guard compares `int32` cells in this slice, but `{}` has type `{}`",
                        crate::surface::diagnostics::describe_contract_expression(side),
                        describe_c0_type(ty)
                    )));
                }
            }
        }
        // The guard is read against the cells the body itself owns: state it
        // as the bounded fact `forall k. range implies guard` and ask the
        // same read-authority check a body fact gets. A guard over a cell the
        // body does not own could change while the resource is folded.
        let guard_fact = ClickProposition::ForAll {
            click_type: ClickType::C(C0Type::Int32),
            name: index.to_string(),
            written_name: None,
            body: Box::new(ClickProposition::Implies(
                Box::new(clause.range.clone()),
                Box::new(clause_guard.clone()),
            )),
        };
        let no_values = BTreeMap::new();
        let guard_fact = crate::surface::lowering::substitute_click_proposition_in(
            &guard_fact,
            &crate::surface::lowering::ContractSubstitutions::with_body_fields_as_c_names(
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
            predicate_environment,
            click_function_environment,
        )
        .map_err(|error| {
            ClickError::new(format!(
                "{context}: the guard must read only cells the same body owns, so that it cannot change while the resource is folded\n{}",
                error.message()
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
        matches!(field.click_type, ClickType::C(_))
            && !definition
                .parameters()
                .iter()
                .any(|parameter| parameter.name() == field.name())
    });
    if scalar.is_empty() {
        return Ok(None);
    }
    let no_values = BTreeMap::new();
    let substitutions = ContractSubstitutions::with_body_fields_as_c_names(&no_values);
    let mut parameters = definition.parameters.clone();
    parameters.extend(scalar.iter().map(|field| FunctionParameter {
        name: field.name.clone(),
        click_type: field.click_type.clone(),
        struct_name: None,
        function_pointer_signature: None,
        constant: false,
        pointee_constant: false,
    }));
    let mut view = body.clone();
    view.fields = other;
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
        parameters,
        composite_body: Some(view),
        field_schema: definition.field_schema.clone(),
    }))
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResourceFactRead {
    base: CExpression,
    index: CExpression,
    expression: String,
    enclosing_range: Option<(CExpression, CExpression)>,
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
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), ClickError> {
    let mut reads = Vec::new();
    let mut visited_predicates = Vec::new();
    let mut visited_functions = Vec::new();
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
            crate::kernel::CValue::typed_pointer(
                crate::kernel::Pointer::symbolic(crate::kernel::Variable(4_100_000 + index as u64)),
                witness.c_type().to_kernel_type(),
            ),
        );
    }
    let bound_names = definition
        .parameters()
        .iter()
        .map(|parameter| {
            (
                parameter.name().to_string(),
                parameter.c_type(),
                parameter.struct_name().map(str::to_string),
            )
        })
        .chain(
            composite_body
                .witnesses()
                .iter()
                .map(|witness| (witness.name().to_string(), witness.c_type(), None)),
        )
        .collect::<Vec<_>>();
    let arguments = bound_names
        .iter()
        .map(|(name, _, _)| {
            CExpression::Value(
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
                ContractExpression::CFragment(CExpression::Variable(name.clone())),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let validation_parameters = bound_names
        .iter()
        .map(|(name, c_type, struct_name)| {
            syntax::C0Parameter::new(*c_type, name.clone(), struct_name.clone())
        })
        .collect::<Vec<_>>();
    let (memory, _) = instantiate_composite_resource_body_resources(
        definition.name(),
        composite_body,
        &substitutions,
        &validation_parameters,
        &arguments,
        CMemory::new(),
    )
    .map_err(|message| {
        ClickError::new(format!(
            "resource `{}` could not materialize contained memory while validating facts: {message}",
            definition.name()
        ))
    })?;
    let array_refs = pure_theorem_array_refs(definition.parameters(), &values, &memory);
    let mut scalar_assumptions = Vec::new();
    for body_fact in prior_facts {
        collect_resource_fact_scalar_assumptions_from_proposition(
            body_fact,
            predicate_definitions,
            &values,
            &array_refs,
            &memory,
            predicate_environment,
            click_function_environment,
            &mut Vec::new(),
            &mut scalar_assumptions,
            definition.name(),
        )?;
    }
    let empty_memory = CMemory::new();
    let empty_array_refs = pure_theorem_array_refs(definition.parameters(), &values, &empty_memory);
    collect_resource_fact_scalar_assumptions_from_proposition(
        fact,
        predicate_definitions,
        &values,
        &empty_array_refs,
        &empty_memory,
        predicate_environment,
        click_function_environment,
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
            &values,
            &array_refs,
            &memory,
            predicate_environment,
            click_function_environment,
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
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
    visited_predicates: &mut Vec<String>,
    assumptions: &mut Vec<ResourceFactScalarAssumption>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { .. }
        | ClickProposition::FloatClassification { .. }
        | ClickProposition::Loadable { .. }
        | ClickProposition::Defined { .. } => {
            let source = describe_click_proposition(proposition);
            let state = CState::new().with_memory(memory.clone());
            if let Ok(proposition) =
                crate::surface::proof::lower_fixed_state_proposition_through_kernel(
                    proposition,
                    &PureFactContext::new(),
                    values,
                    array_refs,
                    &state,
                    &state,
                    None,
                    &RecordedSnapshots::new(),
                    predicate_environment,
                    click_function_environment,
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
                values,
                array_refs,
                memory,
                predicate_environment,
                click_function_environment,
                visited_predicates,
                assumptions,
                resource_name,
            )
        }
        ClickProposition::Separate { .. } | ClickProposition::Contains { .. } => Ok(()),
        ClickProposition::And(left, right) => {
            collect_resource_fact_scalar_assumptions_from_proposition(
                left,
                predicate_definitions,
                values,
                array_refs,
                memory,
                predicate_environment,
                click_function_environment,
                visited_predicates,
                assumptions,
                resource_name,
            )?;
            collect_resource_fact_scalar_assumptions_from_proposition(
                right,
                predicate_definitions,
                values,
                array_refs,
                memory,
                predicate_environment,
                click_function_environment,
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
                values,
                array_refs,
                memory,
                predicate_environment,
                click_function_environment,
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

fn collect_resource_fact_reads_from_proposition(
    proposition: &ClickProposition,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    visited_predicates: &mut Vec<String>,
    visited_functions: &mut Vec<String>,
    reads: &mut Vec<ResourceFactRead>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match proposition {
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
        ClickProposition::Defined { expression } => {
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
        ClickProposition::ForAll { name, body, .. } => {
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
                if let Some((start, end)) = quantified_index_interval(body, name) {
                    for read in &mut reads[first_consequent_read..] {
                        if read.index == CExpression::Variable(name.clone()) {
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
            let start = contract_expression_as_c_fragment(start).ok_or_else(|| {
                ClickError::new(format!(
                    "resource `{resource_name}` range fact has a non-C start"
                ))
            })?;
            let end = contract_expression_as_c_fragment(end).ok_or_else(|| {
                ClickError::new(format!(
                    "resource `{resource_name}` range fact has a non-C end"
                ))
            })?;
            for read in &mut reads[first_body_read..] {
                if read.index == CExpression::Variable(item.clone()) {
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

fn quantified_index_interval(
    body: &ClickProposition,
    name: &str,
) -> Option<(CExpression, CExpression)> {
    let ClickProposition::Implies(antecedent, _) = body else {
        return None;
    };
    fn visit(
        proposition: &ClickProposition,
        name: &str,
        lower: &mut Option<CExpression>,
        upper: &mut Option<CExpression>,
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
                let variable =
                    ContractExpression::CFragment(CExpression::Variable(name.to_string()));
                match operator {
                    ComparisonOperator::LessEqual if right == &variable => {
                        *lower = contract_expression_as_c_fragment(left);
                    }
                    ComparisonOperator::GreaterEqual if left == &variable => {
                        *lower = contract_expression_as_c_fragment(right);
                    }
                    ComparisonOperator::LessThan if left == &variable => {
                        *upper = contract_expression_as_c_fragment(right);
                    }
                    ComparisonOperator::GreaterThan if right == &variable => {
                        *upper = contract_expression_as_c_fragment(left);
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
    Some((lower?, upper?))
}

fn collect_resource_fact_reads_from_contract_segment(
    segment: &ContractSegment,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    visited_predicates: &mut Vec<String>,
    visited_functions: &mut Vec<String>,
    reads: &mut Vec<ResourceFactRead>,
    resource_name: &str,
) -> Result<(), ClickError> {
    for expression in [&segment.base, &segment.start, &segment.end] {
        collect_resource_fact_reads_from_contract_expression(
            &ContractExpression::CFragment(expression.clone()),
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
    visited_functions: &mut Vec<String>,
    reads: &mut Vec<ResourceFactRead>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceSubject::Memory(segment) => collect_resource_fact_reads_from_contract_segment(
            segment,
            predicate_definitions,
            click_function_definitions,
            visited_predicates,
            visited_functions,
            reads,
            resource_name,
        ),
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
    visited_functions: &mut Vec<String>,
    reads: &mut Vec<ResourceFactRead>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match expression {
        ContractExpression::IntegerLiteral(_) => Ok(()),
        ContractExpression::Negate(inner) => collect_resource_fact_reads_from_contract_expression(
            inner,
            predicate_definitions,
            click_function_definitions,
            visited_predicates,
            visited_functions,
            reads,
            resource_name,
        ),
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
        | ContractExpression::CFragment(expression)
        | ContractExpression::Field {
            lowered: expression,
            ..
        } => {
            collect_resource_fact_reads_from_c_expression(expression, reads);
            Ok(())
        }
        ContractExpression::CBinding(_) => Ok(()),
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
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
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
            let Some(base) = contract_expression_as_c_fragment(base) else {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` fact reads `{}` in a form that cannot be matched to a contained memory resource with current read authority",
                    describe_contract_expression(expression)
                )));
            };
            let Some(index) = contract_expression_as_c_fragment(index) else {
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
            if visited_functions.contains(name) {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` fact cannot use recursive function `{name}`"
                )));
            }
            visited_functions.push(name.clone());
            let substitutions = definition
                .parameters()
                .iter()
                .zip(arguments)
                .map(|(parameter, argument)| (parameter.name().to_string(), argument.clone()))
                .collect::<BTreeMap<_, _>>();
            let body = substitute_contract_expression(definition.body(), &substitutions).map_err(
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
            visited_functions.pop();
            result
        }
    }
}

fn collect_resource_fact_reads_from_c_expression(
    expression: &CExpression,
    reads: &mut Vec<ResourceFactRead>,
) {
    match expression {
        CExpression::Value(_) | CExpression::Variable(_) | CExpression::FunctionAddress(_) => {}
        CExpression::Cast { expression, .. } => {
            collect_resource_fact_reads_from_c_expression(expression, reads);
        }
        CExpression::FloatNegate(expression)
        | CExpression::FloatClassification { expression, .. } => {
            collect_resource_fact_reads_from_c_expression(expression, reads);
        }
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_resource_fact_reads_from_c_expression(condition, reads);
            collect_resource_fact_reads_from_c_expression(then_branch, reads);
            collect_resource_fact_reads_from_c_expression(else_branch, reads);
        }
        CExpression::AddressOf(_) => {}
        CExpression::PointerOffsetBytes { pointer, .. } => {
            collect_resource_fact_reads_from_c_expression(pointer, reads);
        }
        CExpression::Load(pointer) => {
            collect_resource_fact_reads_from_c_expression(pointer, reads);
            reads.push(ResourceFactRead {
                base: pointer.as_ref().clone(),
                index: CExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
                expression: describe_c_expression(expression),
                enclosing_range: None,
            });
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_resource_fact_reads_from_c_expression(pointer, reads);
            reads.push(ResourceFactRead {
                base: pointer.as_ref().clone(),
                index: CExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
                expression: describe_c_expression(expression),
                enclosing_range: None,
            });
        }
        CExpression::Index(base, index) => {
            collect_resource_fact_reads_from_c_expression(base, reads);
            collect_resource_fact_reads_from_c_expression(index, reads);
            reads.push(ResourceFactRead {
                base: base.as_ref().clone(),
                index: index.as_ref().clone(),
                expression: describe_c_expression(expression),
                enclosing_range: None,
            });
        }
        CExpression::LessThan(left, right)
        | CExpression::LessEqual(left, right)
        | CExpression::GreaterThan(left, right)
        | CExpression::GreaterEqual(left, right)
        | CExpression::Equal(left, right)
        | CExpression::NotEqual(left, right)
        | CExpression::And(left, right)
        | CExpression::Or(left, right)
        | CExpression::Add(left, right)
        | CExpression::Subtract(left, right)
        | CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right) => {
            collect_resource_fact_reads_from_c_expression(left, reads);
            collect_resource_fact_reads_from_c_expression(right, reads);
        }
        CExpression::Not(expression) | CExpression::BitwiseNot(expression) => {
            collect_resource_fact_reads_from_c_expression(expression, reads);
        }
    }
}

fn analyze_resource_fact_read_authority(
    read: &ResourceFactRead,
    contained: &[ResourceClause],
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
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
                    values,
                    array_refs,
                    memory,
                    predicate_environment,
                    click_function_environment,
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
                values,
                array_refs,
                memory,
                predicate_environment,
                click_function_environment,
            ) {
                return ResourceFactReadAuthorityAnalysis {
                    covered: true,
                    notes,
                };
            }
            notes.push(format!(
                "`{resource_description}` has the right base, but the available scalar facts do not prove `{}` <= `{}` < `{}`",
                describe_c_expression(&segment.start),
                describe_c_expression(&read.index),
                describe_c_expression(&segment.end)
            ));
            continue;
        }
        if evaluated_segment_covers_resource_fact_read(
            segment,
            read,
            assumptions,
            values,
            array_refs,
            memory,
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
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
) -> bool {
    let state = CState::new().with_memory(memory.clone());
    let evaluate = |expression: &CExpression| {
        crate::surface::proof::evaluate_c_fragment_through_kernel(
            expression,
            assumptions,
            values,
            array_refs,
            &state,
            None,
        )
    };
    let Ok(CValue::Pointer(base)) = evaluate(&segment.base) else {
        return false;
    };
    let Ok(CValue::Int32(start)) = evaluate(&segment.start) else {
        return false;
    };
    let Ok(CValue::Int32(end)) = evaluate(&segment.end) else {
        return false;
    };
    let Ok(CValue::Pointer(read_base)) = evaluate(&read.base) else {
        return false;
    };
    let Ok(CValue::Int32(index)) = evaluate(&read.index) else {
        return false;
    };
    let segment = EvaluatedContractSegment {
        source: segment.clone(),
        base: base.into_pointer(),
        start,
        end,
        element_width: 4,
    };
    let read_pointer = offset_pointer_by_elements(read_base.into_pointer(), index, 4);
    segment_contains_pointer(&segment, &read_pointer, assumptions)
}

fn symbolic_segment_covers_range(
    available_start: &CExpression,
    available_end: &CExpression,
    required_start: &CExpression,
    required_end: &CExpression,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> bool {
    let state = CState::new().with_memory(memory.clone());
    let evaluate = |expression: &CExpression| {
        crate::surface::proof::evaluate_fixed_state_expression_through_kernel(
            &ContractExpression::CFragment(expression.clone()),
            &PureFactContext::new(),
            values,
            array_refs,
            &state,
            &state,
            None,
            &RecordedSnapshots::new(),
            predicate_environment,
            click_function_environment,
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
    assumptions.proves(&lower_bound) && assumptions.proves(&upper_bound)
}

fn symbolic_segment_covers_index(
    start: &CExpression,
    end: &CExpression,
    index: &CExpression,
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> bool {
    let state = CState::new().with_memory(memory.clone());
    let evaluate = |expression: &CExpression| {
        crate::surface::proof::evaluate_fixed_state_expression_through_kernel(
            &ContractExpression::CFragment(expression.clone()),
            &PureFactContext::new(),
            values,
            array_refs,
            &state,
            &state,
            None,
            &RecordedSnapshots::new(),
            predicate_environment,
            click_function_environment,
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
    assumptions.proves(&lower_bound) && assumptions.proves(&upper_bound)
}

fn constant_segment_covers_index(
    start: &CExpression,
    end: &CExpression,
    index: &CExpression,
) -> bool {
    let Some(start) = constant_c_expression_i64(start) else {
        return false;
    };
    let Some(end) = constant_c_expression_i64(end) else {
        return false;
    };
    let Some(index) = constant_c_expression_i64(index) else {
        return false;
    };
    start <= index && index < end
}

fn constant_c_expression_i64(expression: &CExpression) -> Option<i64> {
    match expression {
        CExpression::Value(CValue::Int32(Bitvector32Term::Constant(value))) => {
            Some(*value as i32 as i64)
        }
        CExpression::Value(CValue::UInt8(Bitvector32Term::Constant(value))) => {
            Some(i64::from(*value))
        }
        CExpression::Add(left, right) => {
            Some(constant_c_expression_i64(left)? + constant_c_expression_i64(right)?)
        }
        CExpression::Subtract(left, right) => {
            Some(constant_c_expression_i64(left)? - constant_c_expression_i64(right)?)
        }
        _ => None,
    }
}

fn declared_composite_resource_name(resource: &ResourceClause) -> Option<&str> {
    match resource {
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
    let graph = definitions
        .iter()
        .map(|definition| {
            let dependencies = definition
                .composite_body()
                .into_iter()
                .flat_map(CompositeResourceBody::contains)
                .filter_map(|resource| match resource {
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
        .collect::<BTreeMap<_, _>>();
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
        base: CExpression,
        start: CExpression,
        end: CExpression,
    ) -> ContractSegment {
        ContractSegment {
            state,
            surface: ContractSegmentSurface::Range {
                base: ContractExpression::CFragment(base.clone()),
                start: ContractExpression::CFragment(start.clone()),
                end: ContractExpression::CFragment(end.clone()),
            },
            base,
            start,
            end,
        }
    }

    fn read(base: CExpression, index: CExpression) -> ResourceFactRead {
        ResourceFactRead {
            base,
            index,
            expression: "cell[index]".to_string(),
            enclosing_range: None,
        }
    }

    fn analysis(
        read: &ResourceFactRead,
        contained: &[ResourceClause],
        assumptions: &PureFactContext,
        values: &BTreeMap<String, CValue>,
    ) -> ResourceFactReadAuthorityAnalysis {
        analyze_resource_fact_read_authority(
            read,
            contained,
            assumptions,
            values,
            &BTreeMap::new(),
            &CMemory::new(),
            &PredicateEnvironment::new(&[]),
            &ClickFunctionEnvironment::new(&[]),
        )
    }

    #[test]
    fn current_view_covers_a_zero_valued_cell() {
        let base = CExpression::Variable("cell".to_string());
        let clause = ResourceClause::ViewMemory(segment(
            ContractSegmentState::Current,
            base.clone(),
            CExpression::Value(int32(0)),
            CExpression::Value(int32(1)),
        ));
        let result = analysis(
            &read(base, CExpression::Value(int32(0))),
            &[clause],
            &PureFactContext::new(),
            &BTreeMap::new(),
        );
        assert!(
            result.covered,
            "a view covers reads regardless of the cell value"
        );
    }

    #[test]
    fn current_view_accepts_a_symbolic_in_bounds_read() {
        let base = CExpression::Variable("cell".to_string());
        let index = CExpression::Variable("index".to_string());
        let bound = CExpression::Variable("bound".to_string());
        let clause = ResourceClause::ViewMemory(segment(
            ContractSegmentState::Current,
            base.clone(),
            CExpression::Value(int32(0)),
            bound.clone(),
        ));
        let index_value = Bitvector32Term::Variable(Variable(12_001));
        let bound_value = Bitvector32Term::Variable(Variable(12_002));
        let assumptions = PureFactContext::new()
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessEqual(
                    Box::new(Bitvector32Term::Constant(0)),
                    Box::new(index_value.clone()),
                ),
                true,
            ))
            .assume_proposition(Proposition::ConditionIs(
                ConditionTerm::Bitvector32SignedLessThan(
                    Box::new(index_value.clone()),
                    Box::new(bound_value.clone()),
                ),
                true,
            ));
        let values = BTreeMap::from([
            ("index".to_string(), CValue::Int32(index_value)),
            ("bound".to_string(), CValue::Int32(bound_value)),
        ]);
        let result = analysis(&read(base, index), &[clause], &assumptions, &values);
        assert!(
            result.covered,
            "scalar bounds should establish view coverage"
        );
    }

    #[test]
    fn current_view_does_not_cover_its_neighbor() {
        let base = CExpression::Variable("cell".to_string());
        let clause = ResourceClause::ViewMemory(segment(
            ContractSegmentState::Current,
            base.clone(),
            CExpression::Value(int32(0)),
            CExpression::Value(int32(1)),
        ));
        let result = analysis(
            &read(base, CExpression::Value(int32(1))),
            &[clause],
            &PureFactContext::new(),
            &BTreeMap::new(),
        );
        assert!(!result.covered, "a neighboring cell is outside the view");
    }

    #[test]
    fn old_view_does_not_cover_a_current_resource_fact() {
        let base = CExpression::Variable("cell".to_string());
        let clause = ResourceClause::ViewMemory(segment(
            ContractSegmentState::Old,
            base.clone(),
            CExpression::Value(int32(0)),
            CExpression::Value(int32(1)),
        ));
        let result = analysis(
            &read(base, CExpression::Value(int32(0))),
            &[clause],
            &PureFactContext::new(),
            &BTreeMap::new(),
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
