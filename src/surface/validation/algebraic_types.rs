use super::*;
use crate::surface::parser::algebraic_field_c_type_supported;

pub(in crate::surface) fn resource_match_arm_scopes<'a>(
    definition: &ResourceDefinition,
    lookup: impl Fn(&str) -> Option<&'a AlgebraicTypeDefinition>,
) -> Result<Vec<(String, Vec<(String, ClickType)>, ResourceDefinition)>, ClickError> {
    let Some(matched) = definition
        .composite_body()
        .and_then(|body| body.matched.as_ref())
    else {
        return Ok(vec![]);
    };
    let Some(ClickType::Algebraic(application)) = definition
        .fields()
        .iter()
        .find(|field| field.name() == matched.field)
        .map(ResourceFieldDefinition::click_type)
    else {
        return Err(ClickError::new(
            "resource match requires an algebraic resource field",
        ));
    };
    let datatype = lookup(&application.name)
        .ok_or_else(|| ClickError::new("unknown resource match datatype"))?;
    let reserved = definition
        .parameters()
        .iter()
        .map(|p| p.name())
        .chain(definition.fields().iter().map(|f| f.name()))
        .collect::<BTreeSet<_>>();
    let mut seen = BTreeSet::new();
    let mut result = Vec::new();
    let variants = datatype
        .variants()
        .iter()
        .map(|variant| (variant.name(), variant))
        .collect::<BTreeMap<_, _>>();
    for arm in &matched.arms {
        if arm.type_name != datatype.name() {
            return Err(ClickError::new(
                "resource match pattern names the wrong datatype",
            ));
        }
        if !seen.insert(arm.variant.as_str()) {
            return Err(ClickError::new("resource match repeats a constructor arm"));
        }
        let variant = variants
            .get(arm.variant.as_str())
            .ok_or_else(|| ClickError::new("unknown resource match constructor"))?;
        if arm.bindings.len() != variant.fields().len() {
            return Err(ClickError::new(
                "resource match constructor has the wrong number of bindings",
            ));
        }
        let mut parameters = definition.parameters.clone();
        let mut bindings = Vec::new();
        let mut substitution = BTreeMap::new();
        let mut names = BTreeSet::new();
        for (index, (name, field)) in arm.bindings.iter().zip(variant.fields()).enumerate() {
            if reserved.contains(name.as_str()) || !names.insert(name.as_str()) {
                return Err(ClickError::new(
                    "resource match binding duplicates or shadows a resource name",
                ));
            }
            let ty = instantiate_field_type(datatype, application, field)?;
            match &ty {
                ClickType::C(_) => parameters.push(FunctionParameter {
                    name: name.clone(),
                    click_type: ty.clone(),
                    struct_name: None,
                    function_pointer_signature: None,
                    constant: false,
                    pointee_constant: false,
                }),
                ClickType::Algebraic(application) => {
                    substitution.insert(
                        name.clone(),
                        ContractExpression::AlgebraicVariable {
                            name: name.clone(),
                            algebraic_type: application.clone(),
                            binder_index: index,
                        },
                    );
                }
                ClickType::Parameter(_) => {
                    return Err(ClickError::new("unresolved resource match binding type"));
                }
                ClickType::Integer => {
                    return Err(ClickError::new(
                        "Integer resource match bindings are not available in this slice",
                    ));
                }
            }
            bindings.push((name.clone(), ty));
        }
        let mut children = Vec::new();
        let mut child_names = BTreeSet::new();
        let mut child_equations = BTreeSet::new();
        let binding_indexes = bindings
            .iter()
            .enumerate()
            .map(|(index, (name, ty))| (name.as_str(), (index, ty)))
            .collect::<BTreeMap<_, _>>();
        let mut equations = BTreeMap::<(Variable, &str), Vec<(usize, &ContractExpression)>>::new();
        for (index, fact) in arm.body.facts.iter().enumerate() {
            if let ClickProposition::Comparison {
                left,
                operator: ComparisonOperator::Equal,
                right,
            } = fact
            {
                for (access, value) in [(left, right), (right, left)] {
                    if let ContractExpression::ResourceField(access) = access
                        && access.children.is_empty()
                    {
                        equations
                            .entry((access.identity, access.field.as_str()))
                            .or_default()
                            .push((index, value));
                    }
                }
            }
        }
        for resource in &arm.body.contains {
            if matches!(resource, ResourceClause::OwnMemory(_)) {
                continue;
            }
            let ResourceClause::Named { binding, resource } = resource else {
                return Err(ClickError::new(
                    "resource match children require named exclusive ownership",
                ));
            };
            let ResourceClause::Declared {
                name, arguments, ..
            } = resource.as_ref()
            else {
                return Err(ClickError::new(
                    "child ownership requires a declared resource",
                ));
            };
            if name != definition.name() || !binding.children.is_empty() {
                return Err(ClickError::new(
                    "this slice supports direct recursive children of the same resource",
                ));
            }
            for argument in arguments {
                // C expressions are read-only. The kernel checks their value,
                // ownership requirements, and path obligations when rewriting.
                resource_argument_to_c_expression(argument)?;
            }
            if reserved.contains(binding.name.as_str())
                || names.contains(binding.name.as_str())
                || !child_names.insert(binding.name.clone())
            {
                return Err(ClickError::new(
                    "child name duplicates or shadows a resource binding",
                ));
            }
            let mut field_bindings = Vec::new();
            for field in definition.fields() {
                let candidates = equations
                    .get(&(binding.identity, field.name()))
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "child `{}` needs an equation for field `{}`",
                            binding.name,
                            field.name()
                        ))
                    })?;
                let [(fact_index, value)] = candidates.as_slice() else {
                    return Err(ClickError::new("duplicate child field equation"));
                };
                let variable = match value {
                    ContractExpression::Binding(name)
                    | ContractExpression::CBinding(name)
                    | ContractExpression::AlgebraicVariable { name, .. }
                    | ContractExpression::CFragment(CExpression::Variable(name)) => name,
                    _ => {
                        return Err(ClickError::new(
                            "child fields must be related to immediate constructor bindings",
                        ));
                    }
                };
                let (index, ty) = binding_indexes
                    .get(variable.as_str())
                    .filter(|(_, ty)| *ty == field.click_type())
                    .ok_or_else(|| {
                        ClickError::new(
                            "child field requires a constructor binding of the same type",
                        )
                    })?;
                let _ = ty;
                field_bindings.push(*index);
                child_equations.insert(*fact_index);
            }
            children.push(ResourceChildBody {
                name: binding.name.clone(),
                identity: binding.identity,
                arguments: arguments.clone(),
                field_bindings,
            });
        }
        let mut referenced = BTreeSet::new();
        for fact in &arm.body.facts {
            collect_click_proposition_referenced_names(fact, &mut referenced);
        }
        for resource in &arm.body.contains {
            if let ResourceClause::OwnMemory(segment) = resource {
                referenced.extend(contract_segment_referenced_names(segment));
            }
        }
        for child in &children {
            for argument in &child.arguments {
                collect_contract_expression_referenced_names(argument, &mut referenced);
            }
        }
        if let Some(name) = referenced
            .iter()
            .find(|name| !reserved.contains(name.as_str()) && !names.contains(name.as_str()))
        {
            return Err(ClickError::new(format!(
                "unbound name `{name}` in resource match arm"
            )));
        }
        let mut body = arm.body.clone();
        body.children = children;
        body.contains
            .retain(|resource| matches!(resource, ResourceClause::OwnMemory(_)));
        body.fields = definition.fields().to_vec();
        body.facts = body
            .facts
            .iter()
            .enumerate()
            .filter(|(index, _)| !child_equations.contains(index))
            .map(|(_, fact)| fact)
            .map(|fact| substitute_click_proposition(fact, &substitution).map_err(ClickError::new))
            .collect::<Result<_, _>>()?;
        result.push((
            arm.variant.clone(),
            bindings,
            ResourceDefinition {
                name: definition.name.clone(),
                parameters,
                composite_body: Some(body),
                field_schema: definition.field_schema.clone(),
            },
        ));
    }
    if seen.len() != datatype.variants().len() {
        return Err(ClickError::new(
            "resource match must cover every constructor",
        ));
    }
    Ok(result)
}

pub(super) fn validate_algebraic_type_declarations(file: &ClickFile) -> Result<(), ClickError> {
    let algebraic_definitions = combined_algebraic_type_definitions(file)?;
    let mut names = BTreeSet::new();
    for definition in &algebraic_definitions {
        if !names.insert(definition.name().to_string()) {
            return Err(ClickError::new(format!(
                "duplicate algebraic datatype definition `{}`",
                definition.name()
            )));
        }
        if definition.variants().is_empty() {
            return Err(ClickError::new(format!(
                "algebraic datatype `{}` must declare at least one variant",
                definition.name()
            )));
        }
    }
    let definitions = algebraic_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();
    for definition in &algebraic_definitions {
        generics::validate_type_parameter_list(
            "algebraic datatype",
            definition.name(),
            definition.type_parameters(),
        )?;
        let mut parameters = BTreeSet::new();
        for parameter in definition.type_parameters() {
            parameters.insert(parameter.as_str());
        }
        let mut variants = BTreeSet::new();
        for variant in definition.variants() {
            if !variants.insert(variant.name()) {
                return Err(ClickError::new(format!(
                    "algebraic datatype `{}` repeats variant `{}`",
                    definition.name(),
                    variant.name()
                )));
            }
            for field in variant.fields() {
                validate_algebraic_field_declaration(
                    definition,
                    variant,
                    field,
                    &parameters,
                    &definitions,
                )?;
            }
        }
    }
    validate_recursive_algebraic_declarations(&definitions)?;
    Ok(())
}

fn validate_algebraic_field_declaration(
    owner: &AlgebraicTypeDefinition,
    variant: &AlgebraicVariantDefinition,
    field: &AlgebraicFieldType,
    parameters: &BTreeSet<&str>,
    definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
) -> Result<(), ClickError> {
    match field {
        AlgebraicFieldType::Parameter(name) if parameters.contains(name.as_str()) => Ok(()),
        AlgebraicFieldType::Parameter(name) => Err(ClickError::new(format!(
            "variant `{}::{}` uses unknown type parameter `{name}`",
            owner.name(),
            variant.name()
        ))),
        AlgebraicFieldType::C(_) => Ok(()),
        AlgebraicFieldType::Algebraic { name, arguments } => {
            let nested = definitions.get(name.as_str()).ok_or_else(|| {
                ClickError::new(format!(
                    "variant `{}::{}` uses unknown algebraic datatype `{name}`",
                    owner.name(),
                    variant.name()
                ))
            })?;
            if arguments.len() != nested.type_parameters().len() {
                return Err(ClickError::new(format!(
                    "algebraic datatype `{name}` expects {} type argument(s), got {} in variant `{}::{}`",
                    nested.type_parameters().len(),
                    arguments.len(),
                    owner.name(),
                    variant.name()
                )));
            }
            for argument in arguments {
                validate_algebraic_field_declaration(
                    owner,
                    variant,
                    argument,
                    parameters,
                    definitions,
                )?;
            }
            Ok(())
        }
    }
}

fn collect_algebraic_field_dependencies<'a>(
    field: &'a AlgebraicFieldType,
    dependencies: &mut BTreeSet<&'a str>,
) {
    if let AlgebraicFieldType::Algebraic { name, arguments } = field {
        dependencies.insert(name);
        for argument in arguments {
            collect_algebraic_field_dependencies(argument, dependencies);
        }
    }
}

fn validate_recursive_algebraic_declarations(
    definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
) -> Result<(), ClickError> {
    let components = algebraic_recursive_components(definitions);
    for definition in definitions.values() {
        for variant in definition.variants() {
            for field in variant.fields() {
                validate_regular_recursive_occurrences(definition, variant, field, &components)?;
            }
        }
    }

    let mut grounded = BTreeSet::new();
    loop {
        let before = grounded.len();
        for definition in definitions.values() {
            if definition.variants().iter().any(|variant| {
                variant
                    .fields()
                    .iter()
                    .all(|field| algebraic_field_is_grounded(field, &grounded))
            }) {
                grounded.insert(definition.name());
            }
        }
        if grounded.len() == before {
            break;
        }
    }
    if let Some(definition) = definitions
        .values()
        .find(|definition| !grounded.contains(definition.name()))
    {
        return Err(ClickError::new(format!(
            "recursive algebraic datatype `{}` has no finite constructor value",
            definition.name()
        )));
    }
    Ok(())
}

fn validate_regular_recursive_occurrences(
    owner: &AlgebraicTypeDefinition,
    variant: &AlgebraicVariantDefinition,
    field: &AlgebraicFieldType,
    components: &BTreeMap<&str, usize>,
) -> Result<(), ClickError> {
    let AlgebraicFieldType::Algebraic { name, arguments } = field else {
        return Ok(());
    };
    if components.get(name.as_str()) == components.get(owner.name())
        && !arguments_preserve_owner_parameters(arguments, owner.type_parameters())
    {
        return Err(ClickError::new(format!(
            "recursive algebraic datatype occurrence in variant `{}::{}` must preserve type parameters exactly",
            owner.name(),
            variant.name()
        )));
    }
    for argument in arguments {
        validate_regular_recursive_occurrences(owner, variant, argument, components)?;
    }
    Ok(())
}

fn algebraic_recursive_components<'a>(
    definitions: &BTreeMap<&'a str, &'a AlgebraicTypeDefinition>,
) -> BTreeMap<&'a str, usize> {
    fn visit_forward<'a>(
        current: &'a str,
        graph: &BTreeMap<&'a str, BTreeSet<&'a str>>,
        visited: &mut BTreeSet<&'a str>,
        order: &mut Vec<&'a str>,
    ) {
        if !visited.insert(current) {
            return;
        }
        for dependency in &graph[current] {
            visit_forward(dependency, graph, visited, order);
        }
        order.push(current);
    }

    fn visit_reverse<'a>(
        current: &'a str,
        reverse: &BTreeMap<&'a str, BTreeSet<&'a str>>,
        component: usize,
        components: &mut BTreeMap<&'a str, usize>,
    ) {
        if components.contains_key(current) {
            return;
        }
        components.insert(current, component);
        for dependency in &reverse[current] {
            visit_reverse(dependency, reverse, component, components);
        }
    }

    let mut graph = BTreeMap::new();
    let mut reverse = definitions
        .keys()
        .copied()
        .map(|name| (name, BTreeSet::new()))
        .collect::<BTreeMap<_, _>>();
    for (name, definition) in definitions {
        let mut dependencies = BTreeSet::new();
        for field in definition
            .variants()
            .iter()
            .flat_map(AlgebraicVariantDefinition::fields)
        {
            collect_algebraic_field_dependencies(field, &mut dependencies);
        }
        for dependency in &dependencies {
            reverse
                .get_mut(dependency)
                .expect("algebraic dependencies were validated")
                .insert(*name);
        }
        graph.insert(*name, dependencies);
    }

    let mut order = Vec::new();
    let mut visited = BTreeSet::new();
    for name in definitions.keys().copied() {
        visit_forward(name, &graph, &mut visited, &mut order);
    }
    let mut components = BTreeMap::new();
    for name in order.into_iter().rev() {
        if !components.contains_key(name) {
            let component = components.len();
            visit_reverse(name, &reverse, component, &mut components);
        }
    }
    components
}

fn arguments_preserve_owner_parameters(
    arguments: &[AlgebraicFieldType],
    parameters: &[String],
) -> bool {
    arguments.len() == parameters.len()
        && arguments.iter().zip(parameters).all(|(argument, parameter)| {
            matches!(argument, AlgebraicFieldType::Parameter(name) if name == parameter)
        })
}

fn algebraic_field_is_grounded(field: &AlgebraicFieldType, grounded: &BTreeSet<&str>) -> bool {
    match field {
        AlgebraicFieldType::Parameter(_) | AlgebraicFieldType::C(_) => true,
        AlgebraicFieldType::Algebraic { name, .. } => grounded.contains(name.as_str()),
    }
}

pub(super) fn validate_algebraic_type_uses(
    file: &ClickFile,
    click_functions: &BTreeMap<String, ClickFunctionType>,
) -> Result<(), ClickError> {
    let algebraic_definitions = combined_algebraic_type_definitions(file)?;
    let predicates = combined_predicate_definitions(file)?;
    let functions = combined_click_function_definitions(file)?;
    let theorems = combined_theorem_definitions(file)?;
    let definitions = algebraic_definitions
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();
    let predicate_types = predicates
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();

    for (kind, name, parameters) in predicates
        .iter()
        .map(|definition| ("predicate", definition.name(), definition.parameters()))
        .chain(
            functions
                .iter()
                .map(|definition| ("function", definition.name(), definition.parameters())),
        )
        .chain(
            theorems
                .iter()
                .map(|definition| ("theorem", definition.name(), definition.parameters())),
        )
    {
        for parameter in parameters {
            if let ClickType::Algebraic(application) = parameter.click_type() {
                validate_type_application(
                    application,
                    &definitions,
                    &format!("{kind} `{name}` parameter `{}`", parameter.name()),
                )?;
            }
        }
    }
    for definition in &functions {
        if let ClickType::Algebraic(application) = definition.return_type() {
            validate_type_application(
                application,
                &definitions,
                &format!("function `{}` result", definition.name()),
            )?;
        }
    }
    for definition in file.resource_definitions() {
        let mut names = definition
            .parameters()
            .iter()
            .map(|p| p.name())
            .collect::<BTreeSet<_>>();
        for field in definition.fields() {
            if !names.insert(field.name()) {
                return Err(ClickError::new(format!(
                    "resource `{}` field `{}` duplicates a field or parameter name",
                    definition.name(),
                    field.name()
                )));
            }
            if let ClickType::Algebraic(application) = field.click_type() {
                validate_type_application(
                    application,
                    &definitions,
                    &format!("resource `{}` field `{}`", definition.name(), field.name()),
                )?;
            }
        }
        let field_names = definition
            .fields()
            .iter()
            .map(|field| field.name())
            .collect::<BTreeSet<_>>();
        if let Some(body) = definition.composite_body() {
            for witness in body.witnesses() {
                if field_names.contains(witness.name()) {
                    return Err(ClickError::new(format!(
                        "resource `{}` witness `{}` shadows a field",
                        definition.name(),
                        witness.name()
                    )));
                }
            }
        }
        if let Some(parameter) = definition
            .parameters()
            .iter()
            .find(|parameter| matches!(parameter.click_type(), ClickType::Algebraic(_)))
        {
            return Err(ClickError::new(format!(
                "resource `{}` parameter `{}` uses an algebraic type; algebraic resource arguments are not supported yet",
                definition.name(),
                parameter.name()
            )));
        }
    }

    for definition in &predicates {
        let variables = definition
            .parameters()
            .iter()
            .filter_map(|parameter| {
                parameter
                    .click_type()
                    .c_type()
                    .map(|c_type| (parameter.name().to_string(), c_type))
            })
            .collect();
        validate_algebraic_proposition(
            definition.body(),
            &variables,
            click_functions,
            &predicate_types,
            &definitions,
            &format!("predicate `{}`", definition.name()),
        )?;
        if !definition.type_parameters().is_empty() {
            let click_variables = definition
                .parameters()
                .iter()
                .map(|parameter| (parameter.name().to_string(), parameter.click_type().clone()))
                .collect();
            validate_generic_proposition_types(
                definition.body(),
                &click_variables,
                click_functions,
                &predicate_types,
                &definitions,
                &format!("predicate `{}`", definition.name()),
            )?;
        }
    }
    for definition in &functions {
        let variables = definition
            .parameters()
            .iter()
            .filter_map(|parameter| {
                parameter
                    .click_type()
                    .c_type()
                    .map(|c_type| (parameter.name().to_string(), c_type))
            })
            .collect();
        let body_type = validate_algebraic_expression(
            definition.body(),
            &variables,
            click_functions,
            &predicate_types,
            &definitions,
            &format!("function `{}`", definition.name()),
        )?;
        match (definition.return_type(), body_type) {
            (ClickType::Parameter(_), _) => {}
            (ClickType::Algebraic(expected), Some(actual)) if expected == &actual => {}
            (ClickType::Algebraic(expected), Some(actual)) => {
                return Err(ClickError::new(format!(
                    "function `{}` returns {}, but its body has type {}",
                    definition.name(),
                    describe_click_type(&ClickType::Algebraic(expected.clone())),
                    describe_click_type(&ClickType::Algebraic(actual))
                )));
            }
            (ClickType::Algebraic(expected), None) => {
                return Err(ClickError::new(format!(
                    "function `{}` returns {}, but its body is not algebraic",
                    definition.name(),
                    describe_click_type(&ClickType::Algebraic(expected.clone()))
                )));
            }
            (ClickType::C(_), Some(actual)) => {
                return Err(ClickError::new(format!(
                    "function `{}` returns a C value, but its body has algebraic type {}",
                    definition.name(),
                    describe_click_type(&ClickType::Algebraic(actual))
                )));
            }
            (ClickType::C(_), None) => {}
            (ClickType::Integer, None) => {}
            (ClickType::Integer, Some(actual)) => {
                return Err(ClickError::new(format!(
                    "function `{}` returns Integer, but its body has algebraic type {}",
                    definition.name(),
                    describe_click_type(&ClickType::Algebraic(actual))
                )));
            }
        }
        if !definition.type_parameters().is_empty() {
            let click_variables = definition
                .parameters()
                .iter()
                .map(|parameter| (parameter.name().to_string(), parameter.click_type().clone()))
                .collect();
            let actual = infer_generic_expression_type(
                definition.body(),
                &click_variables,
                click_functions,
                &definitions,
                &format!("function `{}`", definition.name()),
            )?;
            if let Some(actual) = actual
                && !generic_click_types_compatible(&actual, definition.return_type())
            {
                return Err(ClickError::new(format!(
                    "function `{}` returns {}, but its body has type {}",
                    definition.name(),
                    describe_click_type(definition.return_type()),
                    describe_click_type(&actual)
                )));
            }
        }
    }
    for theorem in &theorems {
        let variables = theorem_type_environment(theorem);
        let click_variables = theorem
            .parameters()
            .iter()
            .map(|parameter| (parameter.name().to_string(), parameter.click_type().clone()))
            .collect::<BTreeMap<_, _>>();
        for requirement in theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
        {
            validate_algebraic_proposition(
                requirement,
                &variables,
                click_functions,
                &predicate_types,
                &definitions,
                &format!("theorem `{}` requirement", theorem.name()),
            )?;
            if !theorem.type_parameters().is_empty() {
                validate_generic_proposition_types(
                    requirement,
                    &click_variables,
                    click_functions,
                    &predicate_types,
                    &definitions,
                    &format!("theorem `{}` requirement", theorem.name()),
                )?;
            }
        }
        for ensure in theorem.ensures() {
            if let Ensure::Proposition(proposition) = ensure.ensure() {
                validate_algebraic_proposition(
                    proposition,
                    &variables,
                    click_functions,
                    &predicate_types,
                    &definitions,
                    &format!("theorem `{}` ensure", theorem.name()),
                )?;
                if !theorem.type_parameters().is_empty() {
                    validate_generic_proposition_types(
                        proposition,
                        &click_variables,
                        click_functions,
                        &predicate_types,
                        &definitions,
                        &format!("theorem `{}` ensure", theorem.name()),
                    )?;
                }
            }
        }
    }
    for definition in file.resource_definitions() {
        let Some(body) = definition.composite_body() else {
            continue;
        };
        let arm_scopes =
            resource_match_arm_scopes(definition, |name| definitions.get(name).copied())?;
        for definition in std::iter::once(definition)
            .chain(arm_scopes.iter().map(|(_, _, definition)| definition))
        {
            let body = definition.composite_body().unwrap_or(body);
            let variables = definition
                .parameters()
                .iter()
                .filter_map(|parameter| {
                    parameter
                        .click_type()
                        .c_type()
                        .map(|c_type| (parameter.name().to_string(), c_type))
                })
                .collect();
            if let Some(condition) = body.condition() {
                validate_algebraic_proposition(
                    condition,
                    &variables,
                    click_functions,
                    &predicate_types,
                    &definitions,
                    &format!("resource `{}` condition", definition.name()),
                )?;
            }
            for fact in body.facts() {
                validate_algebraic_proposition(
                    fact,
                    &variables,
                    click_functions,
                    &predicate_types,
                    &definitions,
                    &format!("resource `{}` fact", definition.name()),
                )?;
            }
        }
    }
    for function in file.function_blocks() {
        let requires_variables = function_signature_type_environment(function.signature(), false);
        let ensures_variables = function_signature_type_environment(function.signature(), true);
        for requirement in function
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
        {
            validate_algebraic_proposition(
                requirement,
                &requires_variables,
                click_functions,
                &predicate_types,
                &definitions,
                &format!("requires clause in `{}`", function.signature().name()),
            )?;
        }
        for clause in function.structural_clauses() {
            for item in clause.items() {
                {
                    let proposition = item.proposition();
                    validate_algebraic_proposition(
                        proposition,
                        &requires_variables,
                        click_functions,
                        &predicate_types,
                        &definitions,
                        &format!("structural clause in `{}`", function.signature().name()),
                    )?;
                }
            }
        }
        for ensure in function.ensures() {
            if let Ensure::Proposition(proposition) = ensure.ensure() {
                validate_algebraic_proposition(
                    proposition,
                    &ensures_variables,
                    click_functions,
                    &predicate_types,
                    &definitions,
                    &format!("ensures clause in `{}`", function.signature().name()),
                )?;
            }
        }
    }
    Ok(())
}

fn validate_algebraic_proposition(
    proposition: &ClickProposition,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    predicates: &BTreeMap<&str, &PredicateDefinition>,
    definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            validate_algebraic_expression(
                left,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            validate_algebraic_expression(
                right,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )
            .map(|_| ())
        }
        ClickProposition::FloatClassification { expression, .. }
        | ClickProposition::Defined { expression } => validate_algebraic_expression(
            expression,
            variables,
            click_functions,
            predicates,
            definitions,
            context,
        )
        .map(|_| ()),
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_algebraic_proposition(
                left,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            validate_algebraic_proposition(
                right,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        } => validate_algebraic_proposition(
            body,
            variables,
            click_functions,
            predicates,
            definitions,
            context,
        ),
        ClickProposition::ForAll {
            click_type: c_type,
            name,
            body,
        }
        | ClickProposition::Exists {
            click_type: c_type,
            name,
            body,
        } => {
            let mut variables = variables.clone();
            variables.insert(
                name.clone(),
                c_type.c_type().ok_or_else(|| {
                    ClickError::new("only C quantifier binders are currently supported")
                })?,
            );
            validate_algebraic_proposition(
                body,
                &variables,
                click_functions,
                predicates,
                definitions,
                context,
            )
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
        }
        | ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            validate_algebraic_expression(
                start,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            validate_algebraic_expression(
                end,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            let mut variables = variables.clone();
            variables.insert(item.clone(), C0Type::Int32);
            validate_algebraic_proposition(
                body,
                &variables,
                click_functions,
                predicates,
                definitions,
                context,
            )
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let definition = predicates.get(name.as_str()).copied();
            let actual_types = arguments
                .iter()
                .map(|argument| {
                    let algebraic = validate_algebraic_expression(
                        argument,
                        variables,
                        click_functions,
                        predicates,
                        definitions,
                        context,
                    )?;
                    Ok(match algebraic {
                        Some(application) => Some(ClickType::Algebraic(application)),
                        None => infer_contract_expression_type(
                            argument,
                            variables,
                            click_functions,
                            context,
                        )?
                        .map(ClickType::C),
                    })
                })
                .collect::<Result<Vec<_>, ClickError>>()?;
            let instantiated = definition
                .filter(|definition| !definition.type_parameters().is_empty())
                .map(|definition| {
                    let substitution = generics::infer_type_substitution(
                        "predicate",
                        definition.name(),
                        definition.type_parameters(),
                        definition
                            .parameters()
                            .iter()
                            .map(|parameter| parameter.click_type().clone()),
                        actual_types.clone(),
                    )
                    .map_err(ClickError::new)?;
                    generics::instantiate_predicate(definition, &substitution)
                        .map_err(ClickError::new)
                })
                .transpose()?;
            let definition = instantiated.as_ref().or(definition);
            for (index, actual) in actual_types.into_iter().enumerate() {
                let Some(expected) =
                    definition.and_then(|definition| definition.parameters().get(index))
                else {
                    continue;
                };
                match (expected.click_type(), actual) {
                    (ClickType::Parameter(_), _) => {}
                    (ClickType::Algebraic(expected), Some(ClickType::Algebraic(actual)))
                        if expected == &actual => {}
                    (ClickType::Algebraic(expected), Some(ClickType::Algebraic(actual))) => {
                        return Err(ClickError::new(format!(
                            "predicate `{name}` argument {index} expects {}, got {} in {context}",
                            describe_click_type(&ClickType::Algebraic(expected.clone())),
                            describe_click_type(&ClickType::Algebraic(actual))
                        )));
                    }
                    (ClickType::Algebraic(expected), _) => {
                        return Err(ClickError::new(format!(
                            "predicate `{name}` argument {index} expects {}, got a C value in {context}",
                            describe_click_type(&ClickType::Algebraic(expected.clone()))
                        )));
                    }
                    (ClickType::C(expected), Some(ClickType::Algebraic(actual))) => {
                        return Err(ClickError::new(format!(
                            "predicate `{name}` argument {index} expects {}, got {} in {context}",
                            describe_c0_type(*expected),
                            describe_click_type(&ClickType::Algebraic(actual))
                        )));
                    }
                    (ClickType::Integer, Some(ClickType::Integer)) => {}
                    (ClickType::Integer, _) => {
                        return Err(ClickError::new(format!(
                            "predicate `{name}` argument {index} expects Integer in {context}"
                        )));
                    }
                    (ClickType::C(expected), Some(ClickType::C(actual)))
                        if !click_types_compatible(actual, *expected) =>
                    {
                        return Err(ClickError::new(format!(
                            "predicate `{name}` argument {index} expects {}, got {} in {context}",
                            describe_c0_type(*expected),
                            describe_c0_type(actual)
                        )));
                    }
                    (ClickType::C(_), _) => {}
                }
            }
            Ok(())
        }
        ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. } => Ok(()),
    }
}

fn validate_algebraic_expression(
    expression: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    predicates: &BTreeMap<&str, &PredicateDefinition>,
    definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
    context: &str,
) -> Result<Option<AlgebraicTypeApplication>, ClickError> {
    match expression {
        ContractExpression::IntegerLiteral(_) => Ok(None),
        ContractExpression::Negate(inner) => validate_algebraic_expression(
            inner,
            variables,
            click_functions,
            predicates,
            definitions,
            context,
        ),
        ContractExpression::ResourceField(access) => Ok(match &access.click_type {
            Some(ClickType::Algebraic(ty)) => Some(ty.clone()),
            _ => None,
        }),
        ContractExpression::AlgebraicVariable { algebraic_type, .. } => {
            validate_type_application(algebraic_type, definitions, context)?;
            Ok(Some(algebraic_type.clone()))
        }
        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => {
            let definition = definitions
                .get(algebraic_type.name.as_str())
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "unknown algebraic datatype `{}` in {context}",
                        algebraic_type.name
                    ))
                })?;
            if algebraic_type.arguments.len() != definition.type_parameters().len() {
                return Err(ClickError::new(format!(
                    "algebraic datatype `{}` expects {} type argument(s), got {} in {context}",
                    definition.name(),
                    definition.type_parameters().len(),
                    algebraic_type.arguments.len()
                )));
            }
            let variant_definition = definition
                .variants()
                .iter()
                .find(|candidate| candidate.name() == variant)
                .ok_or_else(|| {
                    ClickError::new(format!(
                        "unknown variant `{}::{variant}` in {context}",
                        definition.name()
                    ))
                })?;
            if arguments.len() != variant_definition.fields().len() {
                return Err(ClickError::new(format!(
                    "constructor `{}::{variant}` expects {} argument(s), got {} in {context}",
                    definition.name(),
                    variant_definition.fields().len(),
                    arguments.len()
                )));
            }
            for (index, (argument, field)) in arguments
                .iter()
                .zip(variant_definition.fields())
                .enumerate()
            {
                let actual_algebraic = validate_algebraic_expression(
                    argument,
                    variables,
                    click_functions,
                    predicates,
                    definitions,
                    context,
                )?;
                let expected = instantiate_field_type(definition, algebraic_type, field)?;
                match (&expected, actual_algebraic) {
                    (ClickType::Parameter(_), _) => {}
                    (ClickType::Algebraic(expected), Some(actual)) if expected == &actual => {}
                    (ClickType::Algebraic(expected), Some(actual)) => {
                        return Err(ClickError::new(format!(
                            "constructor `{}::{variant}` argument {index} expects {}, got {} in {context}",
                            definition.name(),
                            describe_click_type(&ClickType::Algebraic(expected.clone())),
                            describe_click_type(&ClickType::Algebraic(actual))
                        )));
                    }
                    (ClickType::Algebraic(expected), None) => {
                        return Err(ClickError::new(format!(
                            "constructor `{}::{variant}` argument {index} expects {}, got a C value in {context}",
                            definition.name(),
                            describe_click_type(&ClickType::Algebraic(expected.clone()))
                        )));
                    }
                    (ClickType::Integer, None) => {}
                    (ClickType::Integer, Some(actual)) => {
                        return Err(ClickError::new(format!(
                            "constructor `{}::{variant}` argument {index} expects Integer, got algebraic {} in {context}",
                            definition.name(),
                            describe_click_type(&ClickType::Algebraic(actual))
                        )));
                    }
                    (ClickType::C(expected), Some(actual)) => {
                        return Err(ClickError::new(format!(
                            "constructor `{}::{variant}` argument {index} expects {}, got {} in {context}",
                            definition.name(),
                            describe_c0_type(*expected),
                            describe_click_type(&ClickType::Algebraic(actual))
                        )));
                    }
                    (ClickType::C(expected), None) => {
                        if let Some(actual) = infer_contract_expression_type(
                            argument,
                            variables,
                            click_functions,
                            context,
                        )? && !click_types_compatible(actual, *expected)
                        {
                            return Err(ClickError::new(format!(
                                "constructor `{}::{variant}` argument {index} expects {}, got {} in {context}",
                                definition.name(),
                                describe_c0_type(*expected),
                                describe_c0_type(actual)
                            )));
                        }
                    }
                }
            }
            Ok(Some(algebraic_type.clone()))
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            let Some(algebraic_type) = validate_algebraic_expression(
                scrutinee,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?
            else {
                return Err(ClickError::new(format!(
                    "`match` scrutinee must be an algebraic datatype value in {context}"
                )));
            };
            let definition = definitions[algebraic_type.name.as_str()];
            let mut seen = BTreeSet::new();
            let mut result_type: Option<ClickType> = None;
            for arm in arms {
                if arm.type_name != definition.name() {
                    return Err(ClickError::new(format!(
                        "match for `{}` contains pattern for `{}` in {context}",
                        definition.name(),
                        arm.type_name
                    )));
                }
                if !seen.insert(arm.variant.as_str()) {
                    return Err(ClickError::new(format!(
                        "match for `{}` repeats variant `{}` in {context}",
                        definition.name(),
                        arm.variant
                    )));
                }
                let variant = definition
                    .variants()
                    .iter()
                    .find(|candidate| candidate.name() == arm.variant)
                    .ok_or_else(|| {
                        ClickError::new(format!(
                            "unknown variant `{}::{}` in {context}",
                            definition.name(),
                            arm.variant
                        ))
                    })?;
                if arm.bindings.len() != variant.fields().len() {
                    return Err(ClickError::new(format!(
                        "pattern `{}::{}` expects {} binding(s), got {} in {context}",
                        definition.name(),
                        arm.variant,
                        variant.fields().len(),
                        arm.bindings.len()
                    )));
                }
                let mut arm_variables = variables.clone();
                let mut algebraic_bindings = BTreeMap::new();
                let mut bindings = BTreeSet::new();
                for (binding_index, (binding, field)) in
                    arm.bindings.iter().zip(variant.fields()).enumerate()
                {
                    if !bindings.insert(binding) {
                        return Err(ClickError::new(format!(
                            "pattern `{}::{}` repeats binding `{binding}` in {context}",
                            definition.name(),
                            arm.variant
                        )));
                    }
                    match instantiate_field_type(definition, &algebraic_type, field)? {
                        ClickType::Parameter(_) => {}
                        ClickType::C(c_type) => {
                            arm_variables.insert(binding.clone(), c_type);
                        }
                        ClickType::Algebraic(algebraic_type) => {
                            algebraic_bindings.insert(
                                binding.clone(),
                                ContractExpression::AlgebraicVariable {
                                    name: binding.clone(),
                                    algebraic_type,
                                    binder_index: binding_index,
                                },
                            );
                        }
                        ClickType::Integer => {
                            return Err(ClickError::new(
                                "Integer match bindings are not available in this slice",
                            ));
                        }
                    }
                }
                let arm_body = substitute_contract_expression(&arm.body, &algebraic_bindings)
                    .map_err(ClickError::new)?;
                let algebraic_arm_type = validate_algebraic_expression(
                    &arm_body,
                    &arm_variables,
                    click_functions,
                    predicates,
                    definitions,
                    context,
                )?;
                let arm_type = match algebraic_arm_type {
                    Some(application) => Some(ClickType::Algebraic(application)),
                    None => infer_contract_expression_type(
                        &arm_body,
                        &arm_variables,
                        click_functions,
                        context,
                    )?
                    .map(ClickType::C),
                };
                if let (Some(expected), Some(actual)) = (&result_type, &arm_type) {
                    let compatible = match (expected, actual) {
                        (ClickType::C(expected), ClickType::C(actual)) => {
                            click_types_compatible(*actual, *expected)
                        }
                        _ => expected == actual,
                    };
                    if !compatible {
                        return Err(ClickError::new(format!(
                            "match for `{}` has incompatible arm result types {} and {} in {context}",
                            definition.name(),
                            describe_click_type(expected),
                            describe_click_type(actual)
                        )));
                    }
                }
                if result_type.is_none() {
                    result_type = arm_type;
                }
            }
            let missing = definition
                .variants()
                .iter()
                .filter(|variant| !seen.contains(variant.name()))
                .map(|variant| variant.name())
                .collect::<Vec<_>>();
            if !missing.is_empty() {
                return Err(ClickError::new(format!(
                    "match for `{}` is not exhaustive; missing {} in {context}",
                    definition.name(),
                    missing.join(", ")
                )));
            }
            Ok(match result_type {
                Some(ClickType::Algebraic(application)) => Some(application),
                _ => None,
            })
        }
        ContractExpression::SequenceLiteral(elements) => {
            for element in elements {
                validate_algebraic_expression(
                    element,
                    variables,
                    click_functions,
                    predicates,
                    definitions,
                    context,
                )?;
            }
            Ok(None)
        }
        ContractExpression::SequenceConcat(left, right)
        | ContractExpression::Add(left, right)
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
            validate_algebraic_expression(
                left,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            validate_algebraic_expression(
                right,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            Ok(None)
        }
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => validate_algebraic_expression(
            inner,
            variables,
            click_functions,
            predicates,
            definitions,
            context,
        ),
        ContractExpression::BitwiseNot(inner) => {
            validate_algebraic_expression(
                inner,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            Ok(None)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            validate_algebraic_proposition(
                condition,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            validate_algebraic_expression(
                then_branch,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            validate_algebraic_expression(
                else_branch,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            Ok(None)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            validate_algebraic_expression(
                start,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            validate_algebraic_expression(
                end,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            validate_algebraic_expression(
                initial,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            let mut body_variables = variables.clone();
            body_variables.insert(accumulator.clone(), C0Type::Int32);
            body_variables.insert(item.clone(), C0Type::Int32);
            validate_algebraic_expression(
                body,
                &body_variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            Ok(None)
        }
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            let value_type = validate_algebraic_expression(
                value,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            // Integer aliases are checked by the mathematical type validator.
            // This pass only checks embedded algebraic uses; substituting the
            // initializer would expand a linear chain of aliases exponentially.
            if matches!(click_type, Some(ClickType::Integer)) {
                if let Some(actual) = value_type {
                    return Err(ClickError::new(format!(
                        "let binding `{name}` expects Integer, got {} in {context}",
                        describe_click_type(&ClickType::Algebraic(actual))
                    )));
                }
                return validate_algebraic_expression(
                    body,
                    variables,
                    click_functions,
                    predicates,
                    definitions,
                    context,
                );
            }
            match (click_type, &value_type) {
                (Some(ClickType::Algebraic(expected)), Some(actual)) if expected == actual => {}
                (Some(ClickType::Algebraic(expected)), Some(actual)) => {
                    return Err(ClickError::new(format!(
                        "let binding `{name}` expects {}, got {} in {context}",
                        describe_click_type(&ClickType::Algebraic(expected.clone())),
                        describe_click_type(&ClickType::Algebraic(actual.clone()))
                    )));
                }
                (Some(ClickType::Algebraic(expected)), None) => {
                    return Err(ClickError::new(format!(
                        "let binding `{name}` expects {}, got a C value in {context}",
                        describe_click_type(&ClickType::Algebraic(expected.clone()))
                    )));
                }
                (Some(ClickType::C(expected)), Some(actual)) => {
                    return Err(ClickError::new(format!(
                        "let binding `{name}` expects {}, got {} in {context}",
                        describe_c0_type(*expected),
                        describe_click_type(&ClickType::Algebraic(actual.clone()))
                    )));
                }
                _ => {}
            }
            let substituted = substitute_contract_expression(
                body,
                &BTreeMap::from([(name.clone(), value.as_ref().clone())]),
            )
            .map_err(ClickError::new)?;
            validate_algebraic_expression(
                &substituted,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )
        }
        ContractExpression::Call { name, arguments } => {
            let function = click_functions.get(name);
            let actual_types = arguments
                .iter()
                .map(|argument| {
                    let algebraic = validate_algebraic_expression(
                        argument,
                        variables,
                        click_functions,
                        predicates,
                        definitions,
                        context,
                    )?;
                    Ok(match algebraic {
                        Some(application) => Some(ClickType::Algebraic(application)),
                        None => infer_contract_expression_type(
                            argument,
                            variables,
                            click_functions,
                            context,
                        )?
                        .map(ClickType::C),
                    })
                })
                .collect::<Result<Vec<_>, ClickError>>()?;
            let substitution = function
                .filter(|function| !function.type_parameters.is_empty())
                .map(|function| {
                    generics::infer_type_substitution(
                        "function",
                        name,
                        &function.type_parameters,
                        function
                            .parameters
                            .iter()
                            .map(|parameter| parameter.click_type().clone()),
                        actual_types.clone(),
                    )
                    .map_err(ClickError::new)
                })
                .transpose()?;
            for (index, actual) in actual_types.into_iter().enumerate() {
                let Some(expected) = function.and_then(|function| function.parameters.get(index))
                else {
                    continue;
                };
                let expected = substitution
                    .as_ref()
                    .map(|substitution| {
                        generics::instantiate_click_type(expected.click_type(), substitution)
                            .map_err(ClickError::new)
                    })
                    .transpose()?
                    .unwrap_or_else(|| expected.click_type().clone());
                match (&expected, actual) {
                    (ClickType::Parameter(_), _) => {}
                    (ClickType::Integer, Some(ClickType::Integer)) => {}
                    (ClickType::Integer, _) => {
                        return Err(ClickError::new(format!(
                            "function `{name}` argument {index} expects Integer in {context}"
                        )));
                    }
                    (ClickType::Algebraic(expected), Some(ClickType::Algebraic(actual)))
                        if expected == &actual => {}
                    (ClickType::Algebraic(expected), Some(ClickType::Algebraic(actual))) => {
                        return Err(ClickError::new(format!(
                            "function `{name}` argument {index} expects {}, got {} in {context}",
                            describe_click_type(&ClickType::Algebraic(expected.clone())),
                            describe_click_type(&ClickType::Algebraic(actual))
                        )));
                    }
                    (ClickType::Algebraic(expected), _) => {
                        return Err(ClickError::new(format!(
                            "function `{name}` argument {index} expects {}, got a C value in {context}",
                            describe_click_type(&ClickType::Algebraic(expected.clone()))
                        )));
                    }
                    (ClickType::C(expected), Some(ClickType::Algebraic(actual))) => {
                        return Err(ClickError::new(format!(
                            "function `{name}` argument {index} expects {}, got {} in {context}",
                            describe_c0_type(*expected),
                            describe_click_type(&ClickType::Algebraic(actual))
                        )));
                    }
                    (ClickType::C(expected), Some(ClickType::C(actual)))
                        if !click_types_compatible(actual, *expected) =>
                    {
                        return Err(ClickError::new(format!(
                            "function `{name}` argument {index} expects {}, got {} in {context}",
                            describe_c0_type(*expected),
                            describe_c0_type(actual)
                        )));
                    }
                    (ClickType::C(_), _) => {}
                }
            }
            let return_type = function
                .map(|function| {
                    substitution
                        .as_ref()
                        .map(|substitution| {
                            generics::instantiate_click_type(&function.return_type, substitution)
                                .map_err(ClickError::new)
                        })
                        .transpose()
                        .map(|instantiated| {
                            instantiated.unwrap_or_else(|| function.return_type.clone())
                        })
                })
                .transpose()?;
            Ok(return_type.and_then(|return_type| match return_type {
                ClickType::Parameter(_) => None,
                ClickType::Algebraic(application) => Some(application),
                ClickType::C(_) => None,
                ClickType::Integer => None,
            }))
        }
        ContractExpression::QualifiedC { .. }
        | ContractExpression::CFragment(_)
        | ContractExpression::Field { .. }
        | ContractExpression::Binding(_)
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceCount(_)
        | ContractExpression::ResourceWildcard => Ok(None),
    }
}

fn generic_click_types_compatible(actual: &ClickType, expected: &ClickType) -> bool {
    match (actual, expected) {
        (ClickType::C(actual), ClickType::C(expected)) => {
            click_types_compatible(*actual, *expected)
        }
        _ => actual == expected,
    }
}

fn infer_generic_expression_type(
    expression: &ContractExpression,
    variables: &BTreeMap<String, ClickType>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
    context: &str,
) -> Result<Option<ClickType>, ClickError> {
    match expression {
        ContractExpression::IntegerLiteral(_) => {
            Ok(generics::default_numeral_click_type(expression))
        }
        ContractExpression::Negate(inner) => {
            infer_generic_expression_type(inner, variables, click_functions, definitions, context)
        }
        ContractExpression::ResourceField(access) => Ok(access.click_type.clone()),
        ContractExpression::AlgebraicVariable { algebraic_type, .. } => {
            Ok(Some(ClickType::Algebraic(algebraic_type.clone())))
        }
        ContractExpression::AlgebraicConstructor {
            algebraic_type,
            variant,
            arguments,
        } => {
            let definition = definitions[algebraic_type.name.as_str()];
            let variant = definition
                .variants()
                .iter()
                .find(|candidate| candidate.name() == variant)
                .expect("constructors were validated before generic inference");
            for (index, (argument, field)) in arguments.iter().zip(variant.fields()).enumerate() {
                let expected = instantiate_field_type(definition, algebraic_type, field)?;
                let actual = infer_generic_expression_type(
                    argument,
                    variables,
                    click_functions,
                    definitions,
                    context,
                )?;
                if let Some(actual) = actual
                    && !generic_click_types_compatible(&actual, &expected)
                {
                    return Err(ClickError::new(format!(
                        "constructor `{}::{}` argument {index} expects {}, got {} in {context}",
                        definition.name(),
                        variant.name(),
                        describe_click_type(&expected),
                        describe_click_type(&actual)
                    )));
                }
            }
            Ok(Some(ClickType::Algebraic(algebraic_type.clone())))
        }
        ContractExpression::Binding(name)
        | ContractExpression::CBinding(name)
        | ContractExpression::CFragment(CExpression::Variable(name)) => {
            Ok(variables.get(name).cloned())
        }
        ContractExpression::QualifiedC { .. } | ContractExpression::CFragment(_) => {
            let c_variables = variables
                .iter()
                .filter_map(|(name, click_type)| {
                    click_type.c_type().map(|c_type| (name.clone(), c_type))
                })
                .collect();
            infer_contract_expression_type(expression, &c_variables, click_functions, context)
                .map(|c_type| c_type.map(ClickType::C))
        }
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => infer_generic_expression_type(inner, variables, click_functions, definitions, context),
        ContractExpression::BitwiseNot(inner) => {
            let actual = infer_generic_expression_type(
                inner,
                variables,
                click_functions,
                definitions,
                context,
            )?;
            if actual
                .as_ref()
                .is_some_and(|click_type| !matches!(click_type, ClickType::C(_)))
            {
                return Err(ClickError::new(format!(
                    "C operator cannot be applied to a generic or algebraic value in {context}"
                )));
            }
            Ok(actual)
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            let Some(ClickType::Algebraic(application)) = infer_generic_expression_type(
                scrutinee,
                variables,
                click_functions,
                definitions,
                context,
            )?
            else {
                return Ok(None);
            };
            let definition = definitions[application.name.as_str()];
            let mut result_type = None;
            for arm in arms {
                let variant = definition
                    .variants()
                    .iter()
                    .find(|variant| variant.name() == arm.variant)
                    .expect("match variants were validated before generic inference");
                let mut arm_variables = variables.clone();
                for (binding, field) in arm.bindings.iter().zip(variant.fields()) {
                    arm_variables.insert(
                        binding.clone(),
                        instantiate_field_type(definition, &application, field)?,
                    );
                }
                let actual = infer_generic_expression_type(
                    &arm.body,
                    &arm_variables,
                    click_functions,
                    definitions,
                    context,
                )?;
                if let (Some(expected), Some(actual)) = (&result_type, &actual)
                    && !generic_click_types_compatible(actual, expected)
                {
                    return Err(ClickError::new(format!(
                        "generic match has incompatible arm types {} and {} in {context}",
                        describe_click_type(expected),
                        describe_click_type(actual)
                    )));
                }
                result_type = result_type.or(actual);
            }
            Ok(result_type)
        }
        ContractExpression::If {
            condition,
            then_branch,
            else_branch,
        } => {
            validate_generic_proposition_types(
                condition,
                variables,
                click_functions,
                &BTreeMap::new(),
                definitions,
                context,
            )?;
            let then_type = infer_generic_expression_type(
                then_branch,
                variables,
                click_functions,
                definitions,
                context,
            )?;
            let else_type = infer_generic_expression_type(
                else_branch,
                variables,
                click_functions,
                definitions,
                context,
            )?;
            if let (Some(then_type), Some(else_type)) = (&then_type, &else_type)
                && !generic_click_types_compatible(then_type, else_type)
            {
                return Err(ClickError::new(format!(
                    "conditional branches have types {} and {} in {context}",
                    describe_click_type(then_type),
                    describe_click_type(else_type)
                )));
            }
            Ok(then_type.or(else_type))
        }
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            let value_type = infer_generic_expression_type(
                value,
                variables,
                click_functions,
                definitions,
                context,
            )?;
            if let (Some(expected), Some(actual)) = (click_type, &value_type)
                && !generic_click_types_compatible(actual, expected)
            {
                return Err(ClickError::new(format!(
                    "let binding `{name}` expects {}, got {} in {context}",
                    describe_click_type(expected),
                    describe_click_type(actual)
                )));
            }
            let mut body_variables = variables.clone();
            if let Some(value_type) = click_type.clone().or(value_type) {
                body_variables.insert(name.clone(), value_type);
            }
            infer_generic_expression_type(
                body,
                &body_variables,
                click_functions,
                definitions,
                context,
            )
        }
        ContractExpression::Call { name, arguments } => {
            let Some(function) = click_functions.get(name) else {
                return Ok(None);
            };
            let actual_types = arguments
                .iter()
                .map(|argument| {
                    infer_generic_expression_type(
                        argument,
                        variables,
                        click_functions,
                        definitions,
                        context,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            let substitution = if function.type_parameters.is_empty() {
                None
            } else {
                Some(
                    generics::infer_type_substitution(
                        "function",
                        name,
                        &function.type_parameters,
                        function
                            .parameters
                            .iter()
                            .map(|parameter| parameter.click_type().clone()),
                        actual_types,
                    )
                    .map_err(ClickError::new)?,
                )
            };
            substitution
                .as_ref()
                .map(|substitution| {
                    generics::instantiate_click_type(&function.return_type, substitution)
                        .map(Some)
                        .map_err(ClickError::new)
                })
                .unwrap_or_else(|| Ok(Some(function.return_type.clone())))
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
        | ContractExpression::Index(left, right)
        | ContractExpression::SequenceConcat(left, right) => {
            let left_type = infer_generic_expression_type(
                left,
                variables,
                click_functions,
                definitions,
                context,
            )?;
            let right_type = infer_generic_expression_type(
                right,
                variables,
                click_functions,
                definitions,
                context,
            )?;
            if left_type
                .iter()
                .chain(right_type.iter())
                .any(|click_type| !matches!(click_type, ClickType::C(_)))
            {
                return Err(ClickError::new(format!(
                    "C operator cannot be applied to a generic or algebraic value in {context}"
                )));
            }
            let c_variables = variables
                .iter()
                .filter_map(|(name, click_type)| {
                    click_type.c_type().map(|c_type| (name.clone(), c_type))
                })
                .collect();
            infer_contract_expression_type(expression, &c_variables, click_functions, context)
                .map(|c_type| c_type.map(ClickType::C))
        }
        ContractExpression::SequenceLiteral(_)
        | ContractExpression::RangeFold { .. }
        | ContractExpression::Field { .. }
        | ContractExpression::ResourceCount(_)
        | ContractExpression::ResourceWildcard => Ok(None),
    }
}

fn validate_generic_proposition_types(
    proposition: &ClickProposition,
    variables: &BTreeMap<String, ClickType>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    predicates: &BTreeMap<&str, &PredicateDefinition>,
    definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison {
            operator,
            left,
            right,
        } => {
            let left = infer_generic_expression_type(
                left,
                variables,
                click_functions,
                definitions,
                context,
            )?;
            let right = infer_generic_expression_type(
                right,
                variables,
                click_functions,
                definitions,
                context,
            )?;
            if let (Some(left), Some(right)) = (&left, &right)
                && !generic_click_types_compatible(left, right)
            {
                return Err(ClickError::new(format!(
                    "comparison has types {} and {} in {context}",
                    describe_click_type(left),
                    describe_click_type(right)
                )));
            }
            if !matches!(
                operator,
                ComparisonOperator::Equal | ComparisonOperator::NotEqual
            ) && left
                .iter()
                .chain(right.iter())
                .any(|click_type| !matches!(click_type, ClickType::C(_)))
            {
                return Err(ClickError::new(format!(
                    "ordering is not defined for a generic or algebraic value in {context}"
                )));
            }
            Ok(())
        }
        ClickProposition::PredicateCall { name, arguments } => {
            let Some(predicate) = predicates.get(name.as_str()) else {
                return Ok(());
            };
            let actual_types = arguments
                .iter()
                .map(|argument| {
                    infer_generic_expression_type(
                        argument,
                        variables,
                        click_functions,
                        definitions,
                        context,
                    )
                })
                .collect::<Result<Vec<_>, _>>()?;
            if !predicate.type_parameters().is_empty() {
                generics::infer_type_substitution(
                    "predicate",
                    name,
                    predicate.type_parameters(),
                    predicate
                        .parameters()
                        .iter()
                        .map(|parameter| parameter.click_type().clone()),
                    actual_types,
                )
                .map_err(ClickError::new)?;
            }
            Ok(())
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_generic_proposition_types(
                left,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )?;
            validate_generic_proposition_types(
                right,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        } => validate_generic_proposition_types(
            body,
            variables,
            click_functions,
            predicates,
            definitions,
            context,
        ),
        ClickProposition::FloatClassification { expression, .. }
        | ClickProposition::Defined { expression } => {
            let _ = infer_generic_expression_type(
                expression,
                variables,
                click_functions,
                definitions,
                context,
            )?;
            Ok(())
        }
        ClickProposition::RangeAll { body, .. } | ClickProposition::RangeAny { body, .. } => {
            validate_generic_proposition_types(
                body,
                variables,
                click_functions,
                predicates,
                definitions,
                context,
            )
        }
        ClickProposition::ForAll {
            click_type: c_type,
            name,
            body,
        }
        | ClickProposition::Exists {
            click_type: c_type,
            name,
            body,
        } => {
            let mut variables = variables.clone();
            variables.insert(name.clone(), c_type.clone());
            validate_generic_proposition_types(
                body,
                &variables,
                click_functions,
                predicates,
                definitions,
                context,
            )
        }
        ClickProposition::Separate { .. }
        | ClickProposition::Contains { .. }
        | ClickProposition::Loadable { .. } => Ok(()),
    }
}

pub(super) fn instantiate_field_type(
    definition: &AlgebraicTypeDefinition,
    application: &AlgebraicTypeApplication,
    field: &AlgebraicFieldType,
) -> Result<ClickType, ClickError> {
    match field {
        AlgebraicFieldType::C(c_type) => Ok(ClickType::C(*c_type)),
        AlgebraicFieldType::Parameter(name) => definition
            .type_parameters()
            .iter()
            .position(|parameter| parameter == name)
            .and_then(|index| application.arguments.get(index))
            .cloned()
            .ok_or_else(|| ClickError::new(format!("unresolved type parameter `{name}`"))),
        AlgebraicFieldType::Algebraic { name, arguments } => {
            let arguments = arguments
                .iter()
                .map(|argument| instantiate_field_type(definition, application, argument))
                .collect::<Result<Vec<_>, _>>()?;
            Ok(ClickType::Algebraic(AlgebraicTypeApplication {
                rigid: false,
                name: name.clone(),
                arguments,
            }))
        }
    }
}

fn validate_type_application(
    application: &AlgebraicTypeApplication,
    definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
    context: &str,
) -> Result<(), ClickError> {
    let definition = definitions.get(application.name.as_str()).ok_or_else(|| {
        ClickError::new(format!(
            "unknown algebraic datatype `{}` in {context}",
            application.name
        ))
    })?;
    if application.arguments.len() != definition.type_parameters().len() {
        return Err(ClickError::new(format!(
            "algebraic datatype `{}` expects {} type argument(s), got {} in {context}",
            definition.name(),
            definition.type_parameters().len(),
            application.arguments.len()
        )));
    }
    for argument in &application.arguments {
        match argument {
            ClickType::Parameter(_) => {}
            ClickType::C(c_type) if algebraic_field_c_type_supported(*c_type) => {}
            ClickType::Integer => {}
            ClickType::C(c_type) => {
                return Err(ClickError::new(format!(
                    "{} is not a valid algebraic datatype argument in {context}",
                    describe_c0_type(*c_type)
                )));
            }
            ClickType::Algebraic(nested) => {
                validate_type_application(nested, definitions, context)?;
            }
        }
    }
    Ok(())
}
