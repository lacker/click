use super::diagnostics::*;
use super::proof::{pure_theorem_array_refs, pure_theorem_parameter_values};
use super::*;

fn standard_library_definitions() -> Result<
    (
        Vec<PredicateDefinition>,
        Vec<ClickFunctionDefinition>,
        Vec<ResourceDefinition>,
        Vec<TheoremDefinition>,
    ),
    ClickError,
> {
    let file = expand_declared_resource_clauses(parser::parse_file_items(CLICK_STANDARD_LIBRARY)?)?;
    if !file.verifying_sources().is_empty() || !file.function_blocks().is_empty() {
        return Err(ClickError::new(
            "internal Click standard library must not contain verifying sources or C function specs",
        ));
    }
    Ok((
        file.predicate_definitions().to_vec(),
        file.click_function_definitions().to_vec(),
        file.resource_definitions().to_vec(),
        file.theorem_definitions().to_vec(),
    ))
}

pub(super) fn expand_declared_resource_clauses(
    mut file: ClickFile,
) -> Result<ClickFile, ClickError> {
    let resource_parameters = file
        .resource_definitions()
        .iter()
        .map(|definition| {
            (
                definition.name().to_string(),
                definition
                    .parameters()
                    .iter()
                    .map(FunctionParameter::c_type)
                    .collect::<Vec<_>>(),
            )
        })
        .collect::<BTreeMap<_, _>>();

    file.resource_definitions = file
        .resource_definitions
        .drain(..)
        .map(|definition| expand_declared_resource_definition(definition, &resource_parameters))
        .collect::<Result<Vec<_>, _>>()?;

    for function in &mut file.function_blocks {
        function.requires = function
            .requires
            .drain(..)
            .map(|requirement| {
                expand_declared_resource_requirement(requirement, &resource_parameters)
            })
            .collect::<Result<Vec<_>, _>>()?;
        function.ensures = function
            .ensures
            .drain(..)
            .map(|clause| expand_declared_resource_ensure_clause(clause, &resource_parameters))
            .collect::<Result<Vec<_>, _>>()?;
        function.effects = function
            .effects
            .drain(..)
            .map(|clause| expand_declared_resource_effect_clause(clause, &resource_parameters))
            .collect::<Result<Vec<_>, _>>()?;
        function.structural_clauses = function
            .structural_clauses
            .drain(..)
            .map(|clause| expand_declared_resource_structural_clause(clause, &resource_parameters))
            .collect::<Result<Vec<_>, _>>()?;
    }

    for theorem in &mut file.theorem_definitions {
        theorem.requires = theorem
            .requires
            .drain(..)
            .map(|requirement| {
                expand_declared_resource_requirement(requirement, &resource_parameters)
            })
            .collect::<Result<Vec<_>, _>>()?;
        theorem.ensures = theorem
            .ensures
            .drain(..)
            .map(|clause| expand_declared_resource_ensure_clause(clause, &resource_parameters))
            .collect::<Result<Vec<_>, _>>()?;
    }

    Ok(file)
}

fn expand_declared_resource_definition(
    mut definition: ResourceDefinition,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<ResourceDefinition, ClickError> {
    if let Some(representation) = definition.representation {
        definition.representation = Some(expand_declared_resource_representation(
            representation,
            resource_parameters,
        )?);
    }
    Ok(definition)
}

fn expand_declared_resource_representation(
    representation: ResourceRepresentation,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<ResourceRepresentation, ClickError> {
    Ok(ResourceRepresentation {
        contains: representation
            .contains
            .into_iter()
            .map(|resource| expand_declared_resource_clause(resource, resource_parameters))
            .collect::<Result<Vec<_>, _>>()?,
        facts: representation.facts,
    })
}

fn expand_declared_resource_requirement(
    requirement: Requirement,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<Requirement, ClickError> {
    match requirement {
        Requirement::Labeled { label, requirement } => Ok(Requirement::Labeled {
            label,
            requirement: Box::new(expand_declared_resource_requirement(
                *requirement,
                resource_parameters,
            )?),
        }),
        Requirement::Proposition(ClickProposition::PredicateCall { name, arguments })
            if resource_parameters.contains_key(&name) =>
        {
            let parameter_types =
                declared_resource_parameter_types(&name, arguments.len(), resource_parameters)?;
            Ok(Requirement::Resource(ResourceClause::Named {
                name,
                arguments,
                parameter_types,
            }))
        }
        _ => Ok(requirement),
    }
}

fn expand_declared_resource_ensure_clause(
    mut clause: EnsureClause,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<EnsureClause, ClickError> {
    if let Ensure::Proposition(ClickProposition::PredicateCall { name, arguments }) = clause.ensure
    {
        if resource_parameters.contains_key(&name) {
            let parameter_types =
                declared_resource_parameter_types(&name, arguments.len(), resource_parameters)?;
            clause.ensure = Ensure::Resource(ResourceClause::Named {
                name,
                arguments,
                parameter_types,
            });
        } else {
            clause.ensure =
                Ensure::Proposition(ClickProposition::PredicateCall { name, arguments });
        }
    }
    clause.proof = expand_declared_resource_proof(clause.proof, resource_parameters)?;
    Ok(clause)
}

fn expand_declared_resource_effect_clause(
    mut clause: EffectClause,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<EffectClause, ClickError> {
    clause.proof = expand_declared_resource_proof(clause.proof, resource_parameters)?;
    Ok(clause)
}

fn expand_declared_resource_structural_clause(
    mut clause: StructuralClause,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<StructuralClause, ClickError> {
    clause.items = clause
        .items
        .into_iter()
        .map(|item| expand_declared_resource_structural_item(item, resource_parameters))
        .collect::<Result<Vec<_>, _>>()?;
    Ok(clause)
}

fn expand_declared_resource_structural_item(
    mut item: StructuralItem,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<StructuralItem, ClickError> {
    item.proof = expand_declared_resource_proof(item.proof, resource_parameters)?;
    Ok(item)
}

fn expand_declared_resource_proof(
    proof: Proof,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<Proof, ClickError> {
    match proof {
        Proof::Tactic(_) => Ok(proof),
        Proof::Steps(steps) => Ok(Proof::Steps(
            steps
                .into_iter()
                .map(|step| expand_declared_resource_proof_step(step, resource_parameters))
                .collect::<Result<Vec<_>, _>>()?,
        )),
    }
}

fn expand_declared_resource_proof_step(
    step: ProofStep,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<ProofStep, ClickError> {
    match step {
        ProofStep::OpenResource(resource) => Ok(ProofStep::OpenResource(
            expand_declared_resource_clause(resource, resource_parameters)?,
        )),
        ProofStep::CloseResource(resource) => Ok(ProofStep::CloseResource(
            expand_declared_resource_clause(resource, resource_parameters)?,
        )),
        _ => Ok(step),
    }
}

fn expand_declared_resource_clause(
    resource: ResourceClause,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<ResourceClause, ClickError> {
    match resource {
        ResourceClause::Named {
            name,
            arguments,
            parameter_types,
        } if parameter_types.is_empty() => {
            let parameter_types =
                declared_resource_parameter_types(&name, arguments.len(), resource_parameters)?;
            Ok(ResourceClause::Named {
                name,
                arguments,
                parameter_types,
            })
        }
        resource => Ok(resource),
    }
}

fn declared_resource_parameter_types(
    name: &str,
    actual: usize,
    resource_parameters: &BTreeMap<String, Vec<C0Type>>,
) -> Result<Vec<C0Type>, ClickError> {
    let Some(parameters) = resource_parameters.get(name) else {
        return Err(ClickError::new(format!("unknown resource `{name}`")));
    };
    let expected = parameters.len();
    if expected != actual {
        return Err(ClickError::new(format!(
            "resource `{name}` expects {expected} argument(s), got {actual}"
        )));
    }
    Ok(parameters.clone())
}

pub(super) fn combined_predicate_definitions(
    file: &ClickFile,
) -> Result<Vec<PredicateDefinition>, ClickError> {
    let (mut definitions, _, _, _) = standard_library_definitions()?;
    definitions.extend(file.predicate_definitions().iter().cloned());
    Ok(definitions)
}

pub(super) fn combined_click_function_definitions(
    file: &ClickFile,
) -> Result<Vec<ClickFunctionDefinition>, ClickError> {
    let (_, mut definitions, _, _) = standard_library_definitions()?;
    definitions.extend(file.click_function_definitions().iter().cloned());
    Ok(definitions)
}

pub(super) fn combined_resource_definitions(
    file: &ClickFile,
) -> Result<Vec<ResourceDefinition>, ClickError> {
    let (_, _, mut definitions, _) = standard_library_definitions()?;
    definitions.extend(file.resource_definitions().iter().cloned());
    Ok(definitions)
}

pub(super) fn combined_theorem_definitions(
    file: &ClickFile,
) -> Result<Vec<TheoremDefinition>, ClickError> {
    let (_, _, _, mut definitions) = standard_library_definitions()?;
    definitions.extend(file.theorem_definitions().iter().cloned());
    Ok(definitions)
}

pub(super) fn combined_theorem_definitions_with_stdlib_ensure_count(
    file: &ClickFile,
) -> Result<(Vec<TheoremDefinition>, usize), ClickError> {
    let (_, _, _, mut definitions) = standard_library_definitions()?;
    let stdlib_ensure_count = definitions
        .iter()
        .map(|definition| definition.ensures().len())
        .sum();
    definitions.extend(file.theorem_definitions().iter().cloned());
    Ok((definitions, stdlib_ensure_count))
}

pub(super) fn validate_click_definitions(file: &ClickFile) -> Result<(), ClickError> {
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
        if matches!(definition.name(), "read" | "write" | "free") {
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
            &predicates,
            &click_functions,
            &click_function_types,
            &predicate_definition_map,
            &click_function_definition_map,
            &predicate_environment,
            &click_function_environment,
        )?;
    }
    reject_resource_representation_cycles(&resource_definitions)?;

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
    reject_recursive_click_functions(&function_calls)?;

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

    for function in file.function_blocks() {
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
                "`{}` must contain at least one `ensures`, `immutable`, `mutable`, `mutable_field`, or resource-consuming `requires` clause",
                function.signature().name()
            )));
        }
        let requires_type_environment =
            function_signature_type_environment(function.signature(), false);
        let ensures_type_environment =
            function_signature_type_environment(function.signature(), true);

        reject_duplicate_named_resource_clauses(
            function
                .requires()
                .iter()
                .filter_map(|requirement| match requirement.inner() {
                    Requirement::Resource(resource) => Some(resource),
                    _ => None,
                }),
            &format!("requires clauses in `{}`", function.signature().name()),
        )?;
        reject_duplicate_named_resource_clauses(
            function
                .ensures()
                .iter()
                .filter_map(|ensure| match ensure.ensure() {
                    Ensure::Resource(resource) => Some(resource),
                    _ => None,
                }),
            &format!("ensures clauses in `{}`", function.signature().name()),
        )?;

        let mut requirement_labels = BTreeSet::new();
        for requirement in function.requires() {
            if let Some(label) = requirement.label() {
                if !requirement_labels.insert(label.to_string()) {
                    return Err(ClickError::new(format!(
                        "duplicate requirement label `{label}` in `{}`",
                        function.signature().name()
                    )));
                }
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
                Ensure::Proposition(proposition) => validate_predicate_calls_in_proposition(
                    proposition,
                    &predicates,
                    &click_functions,
                    &format!("ensures clause in `{}`", function.signature().name()),
                )?,
                Ensure::Resource(resource) => validate_resource_clause(
                    resource,
                    &resources,
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
        if let Some(label) = requirement.label() {
            if !requirement_labels.insert(label.to_string()) {
                return Err(ClickError::new(format!(
                    "duplicate requirement label `{label}` in theorem `{}`",
                    theorem.name()
                )));
            }
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
    predicates: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
    predicate_definitions: &BTreeMap<&str, &PredicateDefinition>,
    click_function_definitions: &BTreeMap<&str, &ClickFunctionDefinition>,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> Result<(), ClickError> {
    let Some(representation) = definition.representation() else {
        return Ok(());
    };
    let variables = definition
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect::<BTreeMap<_, _>>();
    reject_duplicate_named_resource_clauses(
        representation.contains(),
        &format!("resource `{}` representation", definition.name()),
    )?;
    for resource in representation.contains() {
        validate_resource_clause(
            resource,
            resources,
            click_functions,
            click_function_types,
            &variables,
            &format!("resource `{}` representation", definition.name()),
        )?;
    }
    for fact in representation.facts() {
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
            representation,
            fact,
            predicate_definitions,
            click_function_definitions,
            predicate_environment,
            click_function_environment,
        )?;
    }
    Ok(())
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct ResourceFactRead {
    base: CExpression,
    index: CExpression,
    expression: String,
}

fn validate_resource_fact_memory_ownership(
    definition: &ResourceDefinition,
    representation: &ResourceRepresentation,
    fact: &ClickProposition,
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
    let memory = CMemory::new();
    let values = pure_theorem_parameter_values(definition.parameters());
    let array_refs = pure_theorem_array_refs(definition.parameters(), &values, &memory);
    let mut scalar_assumptions = Vec::new();
    collect_resource_fact_scalar_assumptions_from_proposition(
        fact,
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
    let assumptions = assumptions_from_propositions(&scalar_assumptions);
    for read in reads {
        if !resource_fact_read_is_owned(
            &read,
            representation.contains(),
            &assumptions,
            &values,
            &array_refs,
            &memory,
            predicate_environment,
            click_function_environment,
        ) {
            return Err(ClickError::new(format!(
                "resource `{}` fact reads `{}` without a covering contained `write(...)` resource",
                definition.name(),
                read.expression
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
    assumptions: &mut Vec<Proposition>,
    resource_name: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { .. } => {
            let mut lowerer = KernelPropositionLowerer::new(
                values.clone(),
                array_refs.clone(),
                memory.clone(),
                predicate_environment,
                click_function_environment,
            );
            if let Ok(proposition) = lowerer.lower_requirement_proposition(proposition) {
                assumptions.push(proposition);
            }
            Ok(())
        }
        ClickProposition::Disjoint { .. } => Ok(()),
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
        ClickProposition::Disjoint { left, right } => {
            collect_resource_fact_reads_from_contract_segment(
                left,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )?;
            collect_resource_fact_reads_from_contract_segment(
                right,
                predicate_definitions,
                click_function_definitions,
                visited_predicates,
                visited_functions,
                reads,
                resource_name,
            )
        }
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
        ContractExpression::CFragment(expression) => {
            collect_resource_fact_reads_from_c_expression(expression, reads);
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
                    "resource `{resource_name}` fact reads `{}` in a form that cannot be matched to a contained `write(...)` resource",
                    describe_contract_expression(expression)
                )));
            };
            let Some(index) = contract_expression_as_c_fragment(index) else {
                return Err(ClickError::new(format!(
                    "resource `{resource_name}` fact reads `{}` in a form that cannot be matched to a contained `write(...)` resource",
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
        CExpression::Value(_) | CExpression::Variable(_) => {}
        CExpression::AddressOf(_) => {}
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

fn resource_fact_read_is_owned(
    read: &ResourceFactRead,
    contained: &[ResourceClause],
    assumptions: &Assumptions,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> bool {
    contained.iter().any(|resource| {
        let ResourceClause::Write(segment) = resource else {
            return false;
        };
        if segment.state != ContractSegmentState::Current {
            return false;
        }
        if segment.base == read.base
            && (constant_segment_covers_index(&segment.start, &segment.end, &read.index)
                || symbolic_segment_covers_index(
                    &segment.start,
                    &segment.end,
                    &read.index,
                    assumptions,
                    values,
                    array_refs,
                    memory,
                    predicate_environment,
                    click_function_environment,
                ))
        {
            return true;
        }
        evaluated_segment_covers_resource_fact_read(segment, read, assumptions, values, memory)
    })
}

fn evaluated_segment_covers_resource_fact_read(
    segment: &ContractSegment,
    read: &ResourceFactRead,
    assumptions: &Assumptions,
    values: &BTreeMap<String, CValue>,
    memory: &CMemory,
) -> bool {
    let state = CState::new().with_memory(memory.clone());
    let Ok(CValue::Pointer(base)) =
        evaluate_c_contract_expression(values, &state, None, assumptions, &segment.base)
    else {
        return false;
    };
    let Ok(CValue::Int32(start)) =
        evaluate_c_contract_expression(values, &state, None, assumptions, &segment.start)
    else {
        return false;
    };
    let Ok(CValue::Int32(end)) =
        evaluate_c_contract_expression(values, &state, None, assumptions, &segment.end)
    else {
        return false;
    };
    let Ok(CValue::Pointer(read_base)) =
        evaluate_c_contract_expression(values, &state, None, assumptions, &read.base)
    else {
        return false;
    };
    let Ok(CValue::Int32(index)) =
        evaluate_c_contract_expression(values, &state, None, assumptions, &read.index)
    else {
        return false;
    };
    let segment = EvaluatedContractSegment {
        source: segment.clone(),
        base,
        start,
        end,
    };
    let read_pointer = offset_pointer_by_elements(read_base, index, 4);
    segment_contains_pointer(&segment, &read_pointer, assumptions)
}

fn symbolic_segment_covers_index(
    start: &CExpression,
    end: &CExpression,
    index: &CExpression,
    assumptions: &Assumptions,
    values: &BTreeMap<String, CValue>,
    array_refs: &ClickArrayRefs,
    memory: &CMemory,
    predicate_environment: &PredicateEnvironment,
    click_function_environment: &ClickFunctionEnvironment,
) -> bool {
    let lowerer = KernelPropositionLowerer::new(
        values.clone(),
        array_refs.clone(),
        memory.clone(),
        predicate_environment,
        click_function_environment,
    );
    let Ok(start) = lowerer.lower_requirement_c_expression(start) else {
        return false;
    };
    let Ok(end) = lowerer.lower_requirement_c_expression(end) else {
        return false;
    };
    let Ok(index) = lowerer.lower_requirement_c_expression(index) else {
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

fn reject_resource_representation_cycles(
    definitions: &[ResourceDefinition],
) -> Result<(), ClickError> {
    let graph = definitions
        .iter()
        .map(|definition| {
            let dependencies = definition
                .representation()
                .into_iter()
                .flat_map(ResourceRepresentation::contains)
                .filter_map(|resource| match resource {
                    ResourceClause::Named { name, .. } => Some(name.clone()),
                    ResourceClause::Read(_)
                    | ResourceClause::Write(_)
                    | ResourceClause::Free(_) => None,
                })
                .collect::<Vec<_>>();
            (definition.name().to_string(), dependencies)
        })
        .collect::<BTreeMap<_, _>>();
    let mut permanent = BTreeSet::new();
    let mut visiting = Vec::new();
    for name in graph.keys() {
        reject_resource_representation_cycles_from(name, &graph, &mut permanent, &mut visiting)?;
    }
    Ok(())
}

fn reject_resource_representation_cycles_from(
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
            "resource representation cycle: {}",
            cycle.join(" -> ")
        )));
    }
    visiting.push(name.to_string());
    for dependency in graph.get(name).into_iter().flatten() {
        if graph.contains_key(dependency) {
            reject_resource_representation_cycles_from(dependency, graph, permanent, visiting)?;
        }
    }
    visiting.pop();
    permanent.insert(name.to_string());
    Ok(())
}

fn function_signature_type_environment(
    signature: &FunctionSignature,
    include_result: bool,
) -> BTreeMap<String, C0Type> {
    let mut variables = signature
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect::<BTreeMap<_, _>>();
    if include_result {
        variables.insert("result".to_string(), signature.return_type());
    }
    variables
}

fn theorem_type_environment(theorem: &TheoremDefinition) -> BTreeMap<String, C0Type> {
    theorem
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect()
}

fn validate_proposition_expression_types(
    proposition: &ClickProposition,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            let _ = infer_contract_expression_type(left, variables, click_functions, context)?;
            let _ = infer_contract_expression_type(right, variables, click_functions, context)?;
            Ok(())
        }
        ClickProposition::Disjoint { left, right } => {
            validate_contract_segment_expression_types(left, variables, click_functions, context)?;
            validate_contract_segment_expression_types(right, variables, click_functions, context)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_proposition_expression_types(left, variables, click_functions, context)?;
            validate_proposition_expression_types(right, variables, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            validate_proposition_expression_types(body, variables, click_functions, context)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            let _ = infer_contract_expression_type(start, variables, click_functions, context)?;
            let _ = infer_contract_expression_type(end, variables, click_functions, context)?;
            validate_proposition_expression_types(body, variables, click_functions, context)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                let _ =
                    infer_contract_expression_type(argument, variables, click_functions, context)?;
            }
            Ok(())
        }
    }
}

fn validate_pure_theorem_proof(theorem_name: &str, proof: &Proof) -> Result<(), ClickError> {
    match proof {
        Proof::Tactic(Tactic::Auto | Tactic::Simp) => Ok(()),
        Proof::Tactic(Tactic::Frame) => Err(ClickError::new(format!(
            "`frame` cannot prove pure theorem `{theorem_name}`"
        ))),
        Proof::Steps(steps) => {
            for step in steps {
                match step {
                    ProofStep::Unfold(_) | ProofStep::ApplyTheorem(_) | ProofStep::Simp => {}
                    ProofStep::SymbolicExecute
                    | ProofStep::BoundedExecute
                    | ProofStep::LoopVc(_)
                    | ProofStep::Frame(_)
                    | ProofStep::OpenResource(_)
                    | ProofStep::CloseResource(_)
                    | ProofStep::Witness(_)
                    | ProofStep::Choose(_) => {
                        return Err(ClickError::new(format!(
                            "proof step `{}` cannot prove pure theorem `{theorem_name}`",
                            proof_step_name(step)
                        )));
                    }
                }
            }
            Ok(())
        }
    }
}

pub(super) fn proof_step_name(step: &ProofStep) -> &'static str {
    match step {
        ProofStep::SymbolicExecute => "symbolic_execute",
        ProofStep::BoundedExecute => "bounded_execute",
        ProofStep::LoopVc(_) => "loop_vc",
        ProofStep::Frame(_) => "frame",
        ProofStep::Unfold(_) => "unfold",
        ProofStep::ApplyTheorem(_) => "apply",
        ProofStep::OpenResource(_) => "open",
        ProofStep::CloseResource(_) => "close",
        ProofStep::Witness(_) => "witness",
        ProofStep::Choose(_) => "choose",
        ProofStep::Simp => "simp",
    }
}

fn reject_duplicate_named_resource_clauses<'a>(
    resources: impl IntoIterator<Item = &'a ResourceClause>,
    context: &str,
) -> Result<(), ClickError> {
    let mut seen = Vec::new();
    for resource in resources {
        if !matches!(resource, ResourceClause::Named { .. }) {
            continue;
        }
        if seen.iter().any(|candidate| *candidate == resource) {
            return Err(ClickError::new(format!(
                "duplicate affine resource `{}` in {context}",
                describe_resource_clause(resource)
            )));
        }
        seen.push(resource);
    }
    Ok(())
}

pub(super) fn describe_resource_clause(resource: &ResourceClause) -> String {
    match resource {
        ResourceClause::Read(segment) => format!(
            "read({}[{}..{}])",
            describe_c_expression(&segment.base),
            describe_c_expression(&segment.start),
            describe_c_expression(&segment.end)
        ),
        ResourceClause::Write(segment) => format!(
            "write({}[{}..{}])",
            describe_c_expression(&segment.base),
            describe_c_expression(&segment.start),
            describe_c_expression(&segment.end)
        ),
        ResourceClause::Free(segment) => format!(
            "free({}[{}..{}])",
            describe_c_expression(&segment.base),
            describe_c_expression(&segment.start),
            describe_c_expression(&segment.end)
        ),
        ResourceClause::Named {
            name, arguments, ..
        } => format!(
            "{name}({})",
            arguments
                .iter()
                .map(describe_contract_expression)
                .collect::<Vec<_>>()
                .join(", ")
        ),
    }
}

pub(super) fn describe_c0_type(c_type: C0Type) -> String {
    match c_type {
        C0Type::Int32 => "int32".to_string(),
        C0Type::UInt8 => "uint8".to_string(),
        C0Type::Int32Pointer | C0Type::Int32Array(_) => "int32*".to_string(),
        C0Type::UInt8Pointer | C0Type::UInt8Array(_) => "uint8*".to_string(),
    }
}

fn click_types_compatible(actual: C0Type, expected: C0Type) -> bool {
    match (actual, expected) {
        (C0Type::Int32Array(_), C0Type::Int32Pointer)
        | (C0Type::Int32Pointer, C0Type::Int32Array(_)) => true,
        (C0Type::UInt8Array(_), C0Type::UInt8Pointer)
        | (C0Type::UInt8Pointer, C0Type::UInt8Array(_)) => true,
        _ => actual == expected,
    }
}

fn infer_contract_expression_type(
    expression: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    match expression {
        ContractExpression::CFragment(expression) => {
            Ok(infer_c_expression_type(expression, variables))
        }
        ContractExpression::Old(expression) | ContractExpression::At { expression, .. } => {
            infer_contract_expression_type(expression, variables, click_functions, context)
        }
        ContractExpression::Add(left, right) => {
            infer_add_expression_type(left, right, variables, click_functions, context)
        }
        ContractExpression::Subtract(left, right) => {
            infer_subtract_expression_type(left, right, variables, click_functions, context)
        }
        ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right) => {
            let left = infer_contract_expression_type(left, variables, click_functions, context)?;
            let right = infer_contract_expression_type(right, variables, click_functions, context)?;
            Ok(match (left, right) {
                (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
                    Some(C0Type::Int32)
                }
                _ => None,
            })
        }
        ContractExpression::BitwiseNot(expression) => {
            let expression =
                infer_contract_expression_type(expression, variables, click_functions, context)?;
            Ok(expression
                .filter(|c_type| type_is_scalar(*c_type))
                .map(|_| C0Type::Int32))
        }
        ContractExpression::Index(base, index) => {
            let _ = infer_contract_expression_type(index, variables, click_functions, context)?;
            Ok(
                infer_contract_expression_type(base, variables, click_functions, context)?
                    .and_then(pointer_element_type),
            )
        }
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            let then_type =
                infer_contract_expression_type(then_branch, variables, click_functions, context)?;
            let else_type =
                infer_contract_expression_type(else_branch, variables, click_functions, context)?;
            Ok(match (then_type, else_type) {
                (Some(then_type), Some(else_type))
                    if click_types_compatible(then_type, else_type) =>
                {
                    Some(then_type)
                }
                (Some(_), Some(_)) => None,
                (Some(c_type), None) | (None, Some(c_type)) => Some(c_type),
                (None, None) => None,
            })
        }
        ContractExpression::RangeFold {
            initial,
            accumulator,
            item,
            body,
            ..
        } => {
            let initial_type =
                infer_contract_expression_type(initial, variables, click_functions, context)?;
            let mut body_variables = variables.clone();
            if let Some(initial_type) = initial_type {
                body_variables.insert(accumulator.clone(), initial_type);
            }
            body_variables.insert(item.clone(), C0Type::Int32);
            infer_contract_expression_type(body, &body_variables, click_functions, context)
                .map(|body_type| body_type.or(initial_type))
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            let value_type =
                infer_contract_expression_type(value, variables, click_functions, context)?;
            if let (Some(expected), Some(actual)) = (*c_type, value_type) {
                if !click_types_compatible(actual, expected) {
                    return Err(ClickError::new(format!(
                        "let binding `{name}` expects {}, got {} in {context}",
                        describe_c0_type(expected),
                        describe_c0_type(actual)
                    )));
                }
            }
            let mut body_variables = variables.clone();
            if let Some(binding_type) = c_type.or(value_type) {
                body_variables.insert(name.clone(), binding_type);
            }
            infer_contract_expression_type(body, &body_variables, click_functions, context)
        }
        ContractExpression::Call { name, arguments } => {
            let Some(function) = click_functions.get(name) else {
                return Ok(None);
            };
            for (index, (parameter, argument)) in
                function.parameters.iter().zip(arguments).enumerate()
            {
                if let Some(actual) =
                    infer_contract_expression_type(argument, variables, click_functions, context)?
                {
                    let expected = parameter.c_type();
                    if !click_types_compatible(actual, expected) {
                        return Err(ClickError::new(format!(
                            "function `{name}` argument {index} expects {}, got {} in {context}",
                            describe_c0_type(expected),
                            describe_c0_type(actual)
                        )));
                    }
                }
            }
            Ok(Some(function.return_type))
        }
    }
}

fn infer_c_expression_type(
    expression: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    match expression {
        CExpression::Value(CValue::Int32(_)) => Some(C0Type::Int32),
        CExpression::Value(CValue::UInt8(_)) => Some(C0Type::UInt8),
        CExpression::Value(CValue::Pointer(_)) => None,
        CExpression::Variable(name) => variables.get(name).copied(),
        CExpression::AddressOf(_) => None,
        CExpression::LessThan(_, _)
        | CExpression::LessEqual(_, _)
        | CExpression::GreaterThan(_, _)
        | CExpression::GreaterEqual(_, _)
        | CExpression::Equal(_, _)
        | CExpression::NotEqual(_, _)
        | CExpression::Not(_)
        | CExpression::And(_, _)
        | CExpression::Or(_, _) => Some(C0Type::Int32),
        CExpression::Add(left, right) => infer_c_add_type(left, right, variables),
        CExpression::Subtract(left, right) => infer_c_subtract_type(left, right, variables),
        CExpression::Multiply(left, right)
        | CExpression::Divide(left, right)
        | CExpression::Remainder(left, right)
        | CExpression::ShiftLeft(left, right)
        | CExpression::ShiftRight(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right) => {
            let left = infer_c_expression_type(left, variables);
            let right = infer_c_expression_type(right, variables);
            match (left, right) {
                (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
                    Some(C0Type::Int32)
                }
                _ => None,
            }
        }
        CExpression::BitwiseNot(expression) => infer_c_expression_type(expression, variables)
            .filter(|c_type| type_is_scalar(*c_type))
            .map(|_| C0Type::Int32),
        CExpression::Load(pointer) => {
            infer_c_expression_type(pointer, variables).and_then(pointer_element_type)
        }
        CExpression::TypedLoad { value_type, .. } => match value_type {
            CType::Int32 => Some(C0Type::Int32),
            CType::UInt8 => Some(C0Type::UInt8),
            CType::Int32Pointer => Some(C0Type::Int32Pointer),
            CType::UInt8Pointer => Some(C0Type::UInt8Pointer),
            CType::Int32Array(_) | CType::UInt8Array(_) => None,
        },
        CExpression::Index(base, _) => {
            infer_c_expression_type(base, variables).and_then(pointer_element_type)
        }
    }
}

fn infer_add_expression_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    let left = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right = infer_contract_expression_type(right, variables, click_functions, context)?;
    Ok(pointer_arithmetic_type(left, right).or_else(|| scalar_arithmetic_type(left, right)))
}

fn infer_subtract_expression_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    let left = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right = infer_contract_expression_type(right, variables, click_functions, context)?;
    Ok(match (left, right) {
        (Some(left), Some(right)) if type_is_pointer(left) && type_is_scalar(right) => Some(left),
        _ => scalar_arithmetic_type(left, right),
    })
}

fn infer_c_add_type(
    left: &CExpression,
    right: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    let left = infer_c_expression_type(left, variables);
    let right = infer_c_expression_type(right, variables);
    pointer_arithmetic_type(left, right).or_else(|| scalar_arithmetic_type(left, right))
}

fn infer_c_subtract_type(
    left: &CExpression,
    right: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    let left = infer_c_expression_type(left, variables);
    let right = infer_c_expression_type(right, variables);
    match (left, right) {
        (Some(left), Some(right)) if type_is_pointer(left) && type_is_scalar(right) => Some(left),
        _ => scalar_arithmetic_type(left, right),
    }
}

fn pointer_arithmetic_type(left: Option<C0Type>, right: Option<C0Type>) -> Option<C0Type> {
    match (left, right) {
        (Some(left), Some(right)) if type_is_pointer(left) && type_is_scalar(right) => Some(left),
        (Some(left), Some(right)) if type_is_scalar(left) && type_is_pointer(right) => Some(right),
        _ => None,
    }
}

fn scalar_arithmetic_type(left: Option<C0Type>, right: Option<C0Type>) -> Option<C0Type> {
    match (left, right) {
        (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
            Some(C0Type::Int32)
        }
        _ => None,
    }
}

fn type_is_scalar(c_type: C0Type) -> bool {
    matches!(c_type, C0Type::Int32 | C0Type::UInt8)
}

fn type_is_pointer(c_type: C0Type) -> bool {
    matches!(
        c_type,
        C0Type::Int32Pointer | C0Type::UInt8Pointer | C0Type::Int32Array(_) | C0Type::UInt8Array(_)
    )
}

fn pointer_element_type(c_type: C0Type) -> Option<C0Type> {
    match c_type {
        C0Type::Int32Pointer | C0Type::Int32Array(_) => Some(C0Type::Int32),
        C0Type::UInt8Pointer | C0Type::UInt8Array(_) => Some(C0Type::UInt8),
        C0Type::Int32 | C0Type::UInt8 => None,
    }
}

fn validate_contract_segment_expression_types(
    segment: &ContractSegment,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let _ = infer_contract_expression_type(
        &ContractExpression::CFragment(segment.base.clone()),
        variables,
        click_functions,
        context,
    )?;
    let _ = infer_contract_expression_type(
        &ContractExpression::CFragment(segment.start.clone()),
        variables,
        click_functions,
        context,
    )?;
    let _ = infer_contract_expression_type(
        &ContractExpression::CFragment(segment.end.clone()),
        variables,
        click_functions,
        context,
    )?;
    Ok(())
}

fn validate_resource_clause(
    resource: &ResourceClause,
    resources: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
    variables: &BTreeMap<String, C0Type>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceClause::Read(_) | ResourceClause::Write(_) | ResourceClause::Free(_) => Ok(()),
        ResourceClause::Named {
            name,
            arguments,
            parameter_types,
        } => {
            let Some(arity) = resources.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown resource `{name}` in {context}"
                )));
            };
            if *arity != arguments.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` expects {arity} argument(s), got {} in {context}",
                    arguments.len()
                )));
            }
            if parameter_types.len() != arguments.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` has malformed argument type metadata in {context}"
                )));
            }
            for (index, argument) in arguments.iter().enumerate() {
                validate_contract_expression_calls(argument, click_functions, context)?;
                if let Some(actual) = infer_contract_expression_type(
                    argument,
                    variables,
                    click_function_types,
                    context,
                )? {
                    let expected = parameter_types[index];
                    if !click_types_compatible(actual, expected) {
                        return Err(ClickError::new(format!(
                            "resource `{name}` argument {index} expects {}, got {} in {context}",
                            describe_c0_type(expected),
                            describe_c0_type(actual)
                        )));
                    }
                }
            }
            Ok(())
        }
    }
}

fn validate_predicate_calls_in_proposition(
    proposition: &ClickProposition,
    predicates: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ClickProposition::Disjoint { left, right } => {
            validate_contract_segment_calls(left, click_functions, context)?;
            validate_contract_segment_calls(right, click_functions, context)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_predicate_calls_in_proposition(left, predicates, click_functions, context)?;
            validate_predicate_calls_in_proposition(right, predicates, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            validate_predicate_calls_in_proposition(body, predicates, click_functions, context)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            validate_contract_expression_calls(start, click_functions, context)?;
            validate_contract_expression_calls(end, click_functions, context)?;
            validate_predicate_calls_in_proposition(body, predicates, click_functions, context)
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let Some(arity) = predicates.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown predicate `{name}` in {context}"
                )));
            };
            if *arity != arguments.len() {
                return Err(ClickError::new(format!(
                    "predicate `{name}` expects {arity} argument(s), got {} in {context}",
                    arguments.len()
                )));
            }
            for argument in arguments {
                validate_contract_expression_calls(argument, click_functions, context)?;
            }
            Ok(())
        }
    }
}

fn validate_click_function_expression(
    expression: &ContractExpression,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    if contains_old_expression(expression) {
        return Err(ClickError::new(format!(
            "`old(...)` is not available inside {context}"
        )));
    }
    if contains_at_expression(expression) {
        return Err(ClickError::new(format!(
            "`at(...)` is not available inside {context}"
        )));
    }
    validate_contract_expression_calls(expression, click_functions, context)
}

fn validate_contract_segment_calls(
    segment: &ContractSegment,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    validate_contract_expression_calls(
        &ContractExpression::CFragment(segment.base.clone()),
        click_functions,
        context,
    )?;
    validate_contract_expression_calls(
        &ContractExpression::CFragment(segment.start.clone()),
        click_functions,
        context,
    )?;
    validate_contract_expression_calls(
        &ContractExpression::CFragment(segment.end.clone()),
        click_functions,
        context,
    )
}

fn validate_contract_expression_calls(
    expression: &ContractExpression,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match expression {
        ContractExpression::CFragment(_) => Ok(()),
        ContractExpression::Old(body) => {
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::At { expression, .. } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right)
        | ContractExpression::Index(left, right) => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ContractExpression::BitwiseNot(expression) => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            validate_if_condition_proposition(condition, click_functions, context)?;
            validate_contract_expression_calls(then_branch, click_functions, context)?;
            validate_contract_expression_calls(else_branch, click_functions, context)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            validate_contract_expression_calls(start, click_functions, context)?;
            validate_contract_expression_calls(end, click_functions, context)?;
            validate_contract_expression_calls(initial, click_functions, context)?;
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::Let { value, body, .. } => {
            validate_contract_expression_calls(value, click_functions, context)?;
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::Call { name, arguments } => {
            let Some(arity) = click_functions.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown function `{name}` in {context}"
                )));
            };
            if *arity != arguments.len() {
                return Err(ClickError::new(format!(
                    "function `{name}` expects {arity} argument(s), got {} in {context}",
                    arguments.len()
                )));
            }
            for argument in arguments {
                validate_contract_expression_calls(argument, click_functions, context)?;
            }
            Ok(())
        }
    }
}

fn validate_if_condition_proposition(
    proposition: &ClickProposition,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ClickProposition::Disjoint { left, right } => {
            validate_contract_segment_calls(left, click_functions, context)?;
            validate_contract_segment_calls(right, click_functions, context)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_if_condition_proposition(left, click_functions, context)?;
            validate_if_condition_proposition(right, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            validate_if_condition_proposition(body, click_functions, context)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            validate_contract_expression_calls(start, click_functions, context)?;
            validate_contract_expression_calls(end, click_functions, context)?;
            validate_if_condition_proposition(body, click_functions, context)
        }
        ClickProposition::PredicateCall { name, .. } => Err(ClickError::new(format!(
            "predicate call `{name}` is not supported in `if` expression condition in {context}"
        ))),
    }
}

pub(super) fn contains_old_expression(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::Old(_) => true,
        ContractExpression::CFragment(_) => false,
        ContractExpression::At { expression, .. } => contains_old_expression(expression),
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right)
        | ContractExpression::Index(left, right) => {
            contains_old_expression(left) || contains_old_expression(right)
        }
        ContractExpression::BitwiseNot(expression) => contains_old_expression(expression),
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            proposition_contains_old_expression(condition)
                || contains_old_expression(then_branch)
                || contains_old_expression(else_branch)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contains_old_expression(start)
                || contains_old_expression(end)
                || contains_old_expression(initial)
                || contains_old_expression(body)
        }
        ContractExpression::Let { value, body, .. } => {
            contains_old_expression(value) || contains_old_expression(body)
        }
        ContractExpression::Call { arguments, .. } => arguments.iter().any(contains_old_expression),
    }
}

fn contract_segment_contains_old_expression(segment: &ContractSegment) -> bool {
    [&segment.base, &segment.start, &segment.end]
        .into_iter()
        .any(|expression| {
            contains_old_expression(&ContractExpression::CFragment(expression.clone()))
        })
}

fn proposition_contains_old_expression(proposition: &ClickProposition) -> bool {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            contains_old_expression(left) || contains_old_expression(right)
        }
        ClickProposition::Disjoint { left, right } => {
            contract_segment_contains_old_expression(left)
                || contract_segment_contains_old_expression(right)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            proposition_contains_old_expression(left) || proposition_contains_old_expression(right)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => proposition_contains_old_expression(body),
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            contains_old_expression(start)
                || contains_old_expression(end)
                || proposition_contains_old_expression(body)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            arguments.iter().any(contains_old_expression)
        }
    }
}

pub(super) fn contains_at_expression(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::At { .. } => true,
        ContractExpression::CFragment(_) => false,
        ContractExpression::Old(expression) | ContractExpression::BitwiseNot(expression) => {
            contains_at_expression(expression)
        }
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right)
        | ContractExpression::Index(left, right) => {
            contains_at_expression(left) || contains_at_expression(right)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            proposition_contains_at_expression(condition)
                || contains_at_expression(then_branch)
                || contains_at_expression(else_branch)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            contains_at_expression(start)
                || contains_at_expression(end)
                || contains_at_expression(initial)
                || contains_at_expression(body)
        }
        ContractExpression::Let { value, body, .. } => {
            contains_at_expression(value) || contains_at_expression(body)
        }
        ContractExpression::Call { arguments, .. } => arguments.iter().any(contains_at_expression),
    }
}

fn contract_segment_contains_at_expression(segment: &ContractSegment) -> bool {
    [&segment.base, &segment.start, &segment.end]
        .into_iter()
        .any(|expression| {
            contains_at_expression(&ContractExpression::CFragment(expression.clone()))
        })
}

fn proposition_contains_at_expression(proposition: &ClickProposition) -> bool {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            contains_at_expression(left) || contains_at_expression(right)
        }
        ClickProposition::Disjoint { left, right } => {
            contract_segment_contains_at_expression(left)
                || contract_segment_contains_at_expression(right)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            proposition_contains_at_expression(left) || proposition_contains_at_expression(right)
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => proposition_contains_at_expression(body),
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            contains_at_expression(start)
                || contains_at_expression(end)
                || proposition_contains_at_expression(body)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            arguments.iter().any(contains_at_expression)
        }
    }
}

fn collect_click_function_calls(expression: &ContractExpression, calls: &mut BTreeSet<String>) {
    match expression {
        ContractExpression::CFragment(_) => {}
        ContractExpression::Old(body) => collect_click_function_calls(body, calls),
        ContractExpression::At { expression, .. } => {
            collect_click_function_calls(expression, calls)
        }
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right)
        | ContractExpression::Divide(left, right)
        | ContractExpression::Remainder(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right)
        | ContractExpression::Index(left, right) => {
            collect_click_function_calls(left, calls);
            collect_click_function_calls(right, calls);
        }
        ContractExpression::BitwiseNot(expression) => {
            collect_click_function_calls(expression, calls)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            collect_click_function_calls_in_proposition(condition, calls);
            collect_click_function_calls(then_branch, calls);
            collect_click_function_calls(else_branch, calls);
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            collect_click_function_calls(start, calls);
            collect_click_function_calls(end, calls);
            collect_click_function_calls(initial, calls);
            collect_click_function_calls(body, calls);
        }
        ContractExpression::Let { value, body, .. } => {
            collect_click_function_calls(value, calls);
            collect_click_function_calls(body, calls);
        }
        ContractExpression::Call { name, arguments } => {
            calls.insert(name.clone());
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }
    }
}

fn collect_click_function_calls_in_segment(
    segment: &ContractSegment,
    calls: &mut BTreeSet<String>,
) {
    for expression in [&segment.base, &segment.start, &segment.end] {
        collect_click_function_calls(&ContractExpression::CFragment(expression.clone()), calls);
    }
}

fn collect_click_function_calls_in_proposition(
    proposition: &ClickProposition,
    calls: &mut BTreeSet<String>,
) {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            collect_click_function_calls(left, calls);
            collect_click_function_calls(right, calls);
        }
        ClickProposition::Disjoint { left, right } => {
            collect_click_function_calls_in_segment(left, calls);
            collect_click_function_calls_in_segment(right, calls);
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            collect_click_function_calls_in_proposition(left, calls);
            collect_click_function_calls_in_proposition(right, calls);
        }
        ClickProposition::Not(body)
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            collect_click_function_calls_in_proposition(body, calls);
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            collect_click_function_calls(start, calls);
            collect_click_function_calls(end, calls);
            collect_click_function_calls_in_proposition(body, calls);
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                collect_click_function_calls(argument, calls);
            }
        }
    }
}

fn reject_recursive_click_functions(
    function_calls: &BTreeMap<String, BTreeSet<String>>,
) -> Result<(), ClickError> {
    fn check_call_dag(
        name: &str,
        function_calls: &BTreeMap<String, BTreeSet<String>>,
        visiting: &mut BTreeSet<String>,
        visited: &mut BTreeSet<String>,
    ) -> Result<(), ClickError> {
        if visited.contains(name) {
            return Ok(());
        }
        if !visiting.insert(name.to_string()) {
            return Err(ClickError::new(format!(
                "recursive function definition involving `{name}` is not supported yet"
            )));
        }
        if let Some(calls) = function_calls.get(name) {
            for callee in calls {
                check_call_dag(callee, function_calls, visiting, visited)?;
            }
        }
        visiting.remove(name);
        visited.insert(name.to_string());
        Ok(())
    }

    let mut visited = BTreeSet::new();
    for name in function_calls.keys() {
        check_call_dag(name, function_calls, &mut BTreeSet::new(), &mut visited)?;
    }
    Ok(())
}
