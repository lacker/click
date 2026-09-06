use super::*;

pub(super) fn validate_algebraic_type_declarations(file: &ClickFile) -> Result<(), ClickError> {
    let mut names = BTreeSet::new();
    for definition in file.algebraic_type_definitions() {
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
        let mut parameters = BTreeSet::new();
        for parameter in definition.type_parameters() {
            if !parameters.insert(parameter.as_str()) {
                return Err(ClickError::new(format!(
                    "algebraic datatype `{}` repeats type parameter `{parameter}`",
                    definition.name()
                )));
            }
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
                match field {
                    AlgebraicFieldType::Parameter(name) if parameters.contains(name.as_str()) => {}
                    AlgebraicFieldType::Parameter(name) => {
                        return Err(ClickError::new(format!(
                            "variant `{}::{}` uses unknown type parameter `{name}`",
                            definition.name(),
                            variant.name()
                        )));
                    }
                    AlgebraicFieldType::C(_) => {}
                    AlgebraicFieldType::Algebraic(name) => {
                        let kind = if name == definition.name() {
                            "recursive"
                        } else {
                            "nested"
                        };
                        return Err(ClickError::new(format!(
                            "{kind} algebraic datatype field `{}::{}` is not supported in the nonrecursive first slice",
                            definition.name(),
                            variant.name()
                        )));
                    }
                }
            }
        }
    }
    Ok(())
}

pub(super) fn validate_algebraic_type_uses(
    file: &ClickFile,
    click_functions: &BTreeMap<String, ClickFunctionType>,
) -> Result<(), ClickError> {
    let definitions = file
        .algebraic_type_definitions()
        .iter()
        .map(|definition| (definition.name(), definition))
        .collect::<BTreeMap<_, _>>();

    for definition in file.predicate_definitions() {
        let variables = definition
            .parameters()
            .iter()
            .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
            .collect();
        validate_algebraic_proposition(
            definition.body(),
            &variables,
            click_functions,
            &definitions,
            &format!("predicate `{}`", definition.name()),
        )?;
    }
    for definition in file.click_function_definitions() {
        let variables = definition
            .parameters()
            .iter()
            .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
            .collect();
        validate_algebraic_expression(
            definition.body(),
            &variables,
            click_functions,
            &definitions,
            &format!("function `{}`", definition.name()),
        )?;
    }
    for theorem in file.theorem_definitions() {
        let variables = theorem_type_environment(theorem);
        for requirement in theorem
            .requires()
            .iter()
            .filter_map(Requirement::proposition)
        {
            validate_algebraic_proposition(
                requirement,
                &variables,
                click_functions,
                &definitions,
                &format!("theorem `{}` requirement", theorem.name()),
            )?;
        }
        for ensure in theorem.ensures() {
            if let Ensure::Proposition(proposition) = ensure.ensure() {
                validate_algebraic_proposition(
                    proposition,
                    &variables,
                    click_functions,
                    &definitions,
                    &format!("theorem `{}` ensure", theorem.name()),
                )?;
            }
        }
    }
    for definition in file.resource_definitions() {
        let Some(body) = definition.composite_body() else {
            continue;
        };
        let variables = definition
            .parameters()
            .iter()
            .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
            .collect();
        if let Some(condition) = body.condition() {
            validate_algebraic_proposition(
                condition,
                &variables,
                click_functions,
                &definitions,
                &format!("resource `{}` condition", definition.name()),
            )?;
        }
        for fact in body.facts() {
            validate_algebraic_proposition(
                fact,
                &variables,
                click_functions,
                &definitions,
                &format!("resource `{}` fact", definition.name()),
            )?;
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
                &definitions,
                &format!("requires clause in `{}`", function.signature().name()),
            )?;
        }
        for clause in function.structural_clauses() {
            for item in clause.items() {
                if let Some(proposition) = item.proposition() {
                    validate_algebraic_proposition(
                        proposition,
                        &requires_variables,
                        click_functions,
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
    definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison { left, right, .. } => {
            validate_algebraic_expression(left, variables, click_functions, definitions, context)?;
            validate_algebraic_expression(right, variables, click_functions, definitions, context)
                .map(|_| ())
        }
        ClickProposition::FloatClassification { expression, .. }
        | ClickProposition::Defined { expression } => validate_algebraic_expression(
            expression,
            variables,
            click_functions,
            definitions,
            context,
        )
        .map(|_| ()),
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_algebraic_proposition(left, variables, click_functions, definitions, context)?;
            validate_algebraic_proposition(right, variables, click_functions, definitions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        } => validate_algebraic_proposition(body, variables, click_functions, definitions, context),
        ClickProposition::ForAll { c_type, name, body }
        | ClickProposition::Exists { c_type, name, body } => {
            let mut variables = variables.clone();
            variables.insert(name.clone(), *c_type);
            validate_algebraic_proposition(body, &variables, click_functions, definitions, context)
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
            validate_algebraic_expression(start, variables, click_functions, definitions, context)?;
            validate_algebraic_expression(end, variables, click_functions, definitions, context)?;
            let mut variables = variables.clone();
            variables.insert(item.clone(), C0Type::Int32);
            validate_algebraic_proposition(body, &variables, click_functions, definitions, context)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
            for argument in arguments {
                validate_algebraic_expression(
                    argument,
                    variables,
                    click_functions,
                    definitions,
                    context,
                )?;
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
    definitions: &BTreeMap<&str, &AlgebraicTypeDefinition>,
    context: &str,
) -> Result<Option<AlgebraicTypeApplication>, ClickError> {
    match expression {
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
                if validate_algebraic_expression(
                    argument,
                    variables,
                    click_functions,
                    definitions,
                    context,
                )?
                .is_some()
                {
                    return Err(ClickError::new(format!(
                        "constructor `{}::{variant}` argument {index} must be a C scalar or data-pointer value in this slice",
                        definition.name()
                    )));
                }
                let expected = instantiate_field_type(definition, algebraic_type, field)?;
                if let Some(actual) =
                    infer_contract_expression_type(argument, variables, click_functions, context)?
                    && !click_types_compatible(actual, expected)
                {
                    return Err(ClickError::new(format!(
                        "constructor `{}::{variant}` argument {index} expects {}, got {} in {context}",
                        definition.name(),
                        describe_c0_type(expected),
                        describe_c0_type(actual)
                    )));
                }
            }
            Ok(Some(algebraic_type.clone()))
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            let Some(algebraic_type) = validate_algebraic_expression(
                scrutinee,
                variables,
                click_functions,
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
            let mut result_type = None;
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
                let mut bindings = BTreeSet::new();
                for (binding, field) in arm.bindings.iter().zip(variant.fields()) {
                    if !bindings.insert(binding) {
                        return Err(ClickError::new(format!(
                            "pattern `{}::{}` repeats binding `{binding}` in {context}",
                            definition.name(),
                            arm.variant
                        )));
                    }
                    arm_variables.insert(
                        binding.clone(),
                        instantiate_field_type(definition, &algebraic_type, field)?,
                    );
                }
                if validate_algebraic_expression(
                    &arm.body,
                    &arm_variables,
                    click_functions,
                    definitions,
                    context,
                )?
                .is_some()
                {
                    return Err(ClickError::new(
                        "algebraic-valued match arms are not supported in this slice",
                    ));
                }
                let arm_type = infer_contract_expression_type(
                    &arm.body,
                    &arm_variables,
                    click_functions,
                    context,
                )?;
                if let (Some(expected), Some(actual)) = (result_type, arm_type)
                    && !click_types_compatible(actual, expected)
                {
                    return Err(ClickError::new(format!(
                        "match for `{}` has incompatible arm result types {} and {} in {context}",
                        definition.name(),
                        describe_c0_type(expected),
                        describe_c0_type(actual)
                    )));
                }
                result_type = result_type.or(arm_type);
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
            Ok(None)
        }
        ContractExpression::SequenceLiteral(elements) => {
            for element in elements {
                validate_algebraic_expression(
                    element,
                    variables,
                    click_functions,
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
            validate_algebraic_expression(left, variables, click_functions, definitions, context)?;
            validate_algebraic_expression(right, variables, click_functions, definitions, context)?;
            Ok(None)
        }
        ContractExpression::BitwiseNot(inner)
        | ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => {
            validate_algebraic_expression(inner, variables, click_functions, definitions, context)?;
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
                definitions,
                context,
            )?;
            validate_algebraic_expression(
                then_branch,
                variables,
                click_functions,
                definitions,
                context,
            )?;
            validate_algebraic_expression(
                else_branch,
                variables,
                click_functions,
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
            validate_algebraic_expression(start, variables, click_functions, definitions, context)?;
            validate_algebraic_expression(end, variables, click_functions, definitions, context)?;
            validate_algebraic_expression(
                initial,
                variables,
                click_functions,
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
                definitions,
                context,
            )?;
            Ok(None)
        }
        ContractExpression::Let {
            name,
            c_type,
            value,
            body,
        } => {
            validate_algebraic_expression(value, variables, click_functions, definitions, context)?;
            let mut body_variables = variables.clone();
            if let Some(c_type) = c_type {
                body_variables.insert(name.clone(), *c_type);
            }
            validate_algebraic_expression(
                body,
                &body_variables,
                click_functions,
                definitions,
                context,
            )?;
            Ok(None)
        }
        ContractExpression::Call { arguments, .. } => {
            for argument in arguments {
                validate_algebraic_expression(
                    argument,
                    variables,
                    click_functions,
                    definitions,
                    context,
                )?;
            }
            Ok(None)
        }
        ContractExpression::CFragment(_)
        | ContractExpression::Field { .. }
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceCount(_)
        | ContractExpression::ResourceWildcard => Ok(None),
    }
}

fn instantiate_field_type(
    definition: &AlgebraicTypeDefinition,
    application: &AlgebraicTypeApplication,
    field: &AlgebraicFieldType,
) -> Result<C0Type, ClickError> {
    match field {
        AlgebraicFieldType::C(c_type) => Ok(*c_type),
        AlgebraicFieldType::Parameter(name) => definition
            .type_parameters()
            .iter()
            .position(|parameter| parameter == name)
            .and_then(|index| application.arguments.get(index).copied())
            .ok_or_else(|| ClickError::new(format!("unresolved type parameter `{name}`"))),
        AlgebraicFieldType::Algebraic(_) => unreachable!("nested fields rejected before uses"),
    }
}
