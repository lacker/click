use super::*;

pub(in crate::surface) fn validate_click_definitions(file: &ClickFile) -> Result<(), ClickError> {
    let predicate_definitions = combined_predicate_definitions(file)?;
    let click_function_definitions = combined_click_function_definitions(file)?;
    let resource_definitions = combined_resource_definitions(file)?;
    let theorem_definitions = combined_theorem_definitions(file)?;

    let mut predicates = BTreeMap::new();
    for definition in &predicate_definitions {
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

    let mut click_functions = BTreeMap::new();
    let mut click_function_types = BTreeMap::new();
    for definition in &click_function_definitions {
        if predicates.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a predicate and a function",
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
                parameters: definition.parameters().to_vec(),
                return_type: definition.return_type(),
            },
        );
    }

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
        if predicates.contains_key(definition.name()) {
            return Err(ClickError::new(format!(
                "`{}` is defined as both a predicate and a theorem",
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
    let predicate_environment = PredicateEnvironment::new(&predicate_definitions);
    let click_function_environment = ClickFunctionEnvironment::new(&click_function_definitions);

    for definition in &resource_definitions {
        validate_resource_definition(
            definition,
            &resources,
            &recursive_resources,
            &predicates,
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
        validate_predicate_calls_in_proposition(
            definition.body(),
            &predicates,
            &click_functions,
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
    validate_well_founded_click_recursion(&click_function_definitions, &function_calls)?;

    for theorem in &theorem_definitions {
        validate_theorem_definition(
            theorem,
            &predicates,
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
    for function in combined_external_function_blocks(file)? {
        if !function_specs.insert(function.signature().name().to_string()) {
            return Err(ClickError::new(format!(
                "duplicate C function spec `{}`",
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
        if function.ensures().is_empty()
            && function.effects().is_empty()
            && !function
                .requires()
                .iter()
                .any(requirement_contains_resource)
        {
            return Err(ClickError::new(format!(
                "`{}` must contain at least one `ensures`, `immutable`, `mutable`, or resource-consuming `requires` clause",
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
                validate_predicate_calls_in_proposition(
                    proposition,
                    &predicates,
                    &click_functions,
                    &format!("requires clause in `{}`", function.signature().name()),
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
                if let Some(proposition) = item.proposition() {
                    validate_predicate_calls_in_proposition(
                        proposition,
                        &predicates,
                        &click_functions,
                        &format!(
                            "{:?} clause in `{}`",
                            item.kind(),
                            function.signature().name()
                        ),
                    )?;
                }
            }
        }

        for ensure in function.ensures() {
            match ensure.ensure() {
                Ensure::Proposition(proposition) => {
                    validate_predicate_calls_in_proposition(
                        proposition,
                        &predicates,
                        &click_functions,
                        &format!("ensures clause in `{}`", function.signature().name()),
                    )?;
                    if function.signature().return_type() == C0Type::Void {
                        validate_proposition_expression_types(
                            proposition,
                            &ensures_type_environment,
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
    }

    Ok(())
}

fn validate_theorem_definition(
    theorem: &TheoremDefinition,
    predicates: &BTreeMap<String, usize>,
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
        let Some(proposition) = requirement.proposition() else {
            return Err(ClickError::new(format!(
                "pure theorem `{}` currently supports proposition `requires` clauses only",
                theorem.name()
            )));
        };
        validate_predicate_calls_in_proposition(
            proposition,
            predicates,
            click_functions,
            &format!("requires clause in theorem `{}`", theorem.name()),
        )?;
        validate_proposition_expression_types(
            proposition,
            &variables,
            click_function_types,
            &format!("requires clause in theorem `{}`", theorem.name()),
        )?;
    }

    for ensure in theorem.ensures() {
        let Ensure::Proposition(proposition) = ensure.ensure() else {
            return Err(ClickError::new(format!(
                "pure theorem `{}` currently supports proposition `ensures` clauses only",
                theorem.name()
            )));
        };
        validate_predicate_calls_in_proposition(
            proposition,
            predicates,
            click_functions,
            &format!("ensures clause in theorem `{}`", theorem.name()),
        )?;
        validate_proposition_expression_types(
            proposition,
            &variables,
            click_function_types,
            &format!("ensures clause in theorem `{}`", theorem.name()),
        )?;
        validate_pure_theorem_proof(theorem.name(), ensure.proof())?;
    }

    Ok(())
}

fn validate_resource_definition(
    definition: &ResourceDefinition,
    resources: &BTreeMap<String, usize>,
    recursive_resources: &BTreeSet<String>,
    predicates: &BTreeMap<String, usize>,
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
    let variables = definition
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect::<BTreeMap<_, _>>();
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
        validate_proposition_expression_types(
            fact,
            &variables,
            click_function_types,
            &format!("resource `{}` fact", definition.name()),
        )?;
        validate_resource_fact_memory_ownership(
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

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResourceFactRead {
    base: CExpression,
    index: CExpression,
    expression: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResourceFactScalarAssumption {
    source: String,
    proposition: Proposition,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResourceFactReadOwnershipAnalysis {
    covered: bool,
    notes: Vec<String>,
}

fn validate_resource_fact_memory_ownership(
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
    let values = pure_theorem_parameter_values(definition.parameters());
    let arguments = definition
        .parameters()
        .iter()
        .map(|parameter| {
            CExpression::Value(
                values
                    .get(parameter.name())
                    .expect("resource parameter value should exist")
                    .clone(),
            )
        })
        .collect::<Vec<_>>();
    let substitutions = definition
        .parameters()
        .iter()
        .map(|parameter| {
            (
                parameter.name().to_string(),
                ContractExpression::CFragment(CExpression::Variable(parameter.name().to_string())),
            )
        })
        .collect::<BTreeMap<_, _>>();
    let validation_parameters = definition
        .parameters()
        .iter()
        .map(|parameter| {
            syntax::C0Parameter::new(
                parameter.c_type(),
                parameter.name().to_string(),
                parameter.struct_name().map(str::to_string),
            )
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
        let analysis = analyze_resource_fact_read_ownership(
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
            return Err(ClickError::new(resource_fact_read_ownership_error(
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
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => collect_resource_fact_reads_from_proposition(
            body,
            predicate_definitions,
            click_function_definitions,
            visited_predicates,
            visited_functions,
            reads,
            resource_name,
        ),
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
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
        ContractExpression::CFragment(expression)
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
                    "resource `{resource_name}` fact reads `{}` in a form that cannot be matched to a contained owned memory resource",
                    describe_contract_expression(expression)
                )));
            };
            let Some(index) = contract_expression_as_c_fragment(index) else {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` fact reads `{}` in a form that cannot be matched to a contained owned memory resource",
                    describe_contract_expression(expression)
                )));
            };
            reads.push(ResourceFactRead {
                expression: describe_contract_expression(expression),
                base,
                index,
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
            });
        }
        CExpression::TypedLoad { pointer, .. } => {
            collect_resource_fact_reads_from_c_expression(pointer, reads);
            reads.push(ResourceFactRead {
                base: pointer.as_ref().clone(),
                index: CExpression::Value(CValue::Int32(Bitvector32Term::Constant(0))),
                expression: describe_c_expression(expression),
            });
        }
        CExpression::Index(base, index) => {
            collect_resource_fact_reads_from_c_expression(base, reads);
            collect_resource_fact_reads_from_c_expression(index, reads);
            reads.push(ResourceFactRead {
                base: base.as_ref().clone(),
                index: index.as_ref().clone(),
                expression: describe_c_expression(expression),
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

fn analyze_resource_fact_read_ownership(
    read: &ResourceFactRead,
    contained: &[ResourceClause],
    assumptions: &PureFactContext,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> ResourceFactReadOwnershipAnalysis {
    let mut notes = Vec::new();
    for resource in contained {
        let ResourceClause::OwnMemory(segment) = resource else {
            notes.push(format!(
                "`{}` is not an owned memory resource",
                describe_resource_clause(resource)
            ));
            continue;
        };
        let resource_description = describe_resource_clause(resource);
        if segment.state != ContractSegmentState::Current {
            notes.push(format!(
                "`{resource_description}` is not a current-state owned memory resource"
            ));
            continue;
        }
        if segment.base == read.base
            && constant_segment_covers_index(&segment.start, &segment.end, &read.index)
        {
            return ResourceFactReadOwnershipAnalysis {
                covered: true,
                notes,
            };
        }
        if segment.base == read.base {
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
                return ResourceFactReadOwnershipAnalysis {
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
            return ResourceFactReadOwnershipAnalysis {
                covered: true,
                notes,
            };
        }
        notes.push(format!(
            "`{resource_description}` does not prove coverage of `{}`",
            read.expression
        ));
    }
    ResourceFactReadOwnershipAnalysis {
        covered: false,
        notes,
    }
}

fn resource_fact_read_ownership_error(
    resource_name: &str,
    read: &ResourceFactRead,
    analysis: &ResourceFactReadOwnershipAnalysis,
    scalar_assumptions: &[ResourceFactScalarAssumption],
) -> String {
    let mut lines = vec![format!(
        "resource `{resource_name}` fact reads `{}` without a covering contained owned memory resource",
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
        ResourceClause::Declared {
            kind: ResourceKind::Composite,
            name,
            ..
        } => Some(name),
        ResourceClause::Quantified { resource, .. } => declared_composite_resource_name(resource),
        ResourceClause::ViewMemory(_)
        | ResourceClause::OwnMemory(_)
        | ResourceClause::MemoryAggregate { .. }
        | ResourceClause::Declared { .. } => None,
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
                    ResourceClause::Declared {
                        kind: ResourceKind::Composite,
                        name,
                        ..
                    } => Some(name.clone()),
                    ResourceClause::ViewMemory(_)
                    | ResourceClause::OwnMemory(_)
                    | ResourceClause::MemoryAggregate { .. } => None,
                    ResourceClause::Declared { .. } | ResourceClause::Quantified { .. } => None,
                })
                .filter(|dependency| {
                    dependency != definition.name()
                        || definition
                            .composite_body()
                            .is_none_or(|body| body.condition().is_none())
                })
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
