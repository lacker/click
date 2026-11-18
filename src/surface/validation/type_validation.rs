use super::*;

fn deep_literal_add_type(expression: &ContractExpression) -> Option<InterfaceType> {
    let mut operands = Vec::new();
    let mut current = expression;
    while let ContractExpression::Add(left, right) = current {
        operands.push(right.as_ref());
        current = left;
    }
    if operands.len() <= 128 || !matches!(current, ContractExpression::IntegerLiteral(_)) {
        return None;
    }
    operands.push(current);
    let mut result = None;
    for operand in operands {
        let ContractExpression::IntegerLiteral(value) = operand else {
            return None;
        };
        let value = value.parse::<u64>().ok()?;
        let value_type = if value <= i32::MAX as u64 {
            InterfaceType::Int32
        } else if value <= i64::MAX as u64 {
            InterfaceType::Int64(LongRank::Long)
        } else {
            InterfaceType::UInt64(LongRank::Long)
        };
        result = arithmetic_result_type(result, Some(value_type)).or(Some(value_type));
    }
    result
}

pub(super) fn function_signature_type_environment(
    signature: &FunctionSignature,
    include_result: bool,
) -> BinderMap<InterfaceType> {
    let mut variables = signature
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.interface_type()))
        .collect::<BinderMap<_>>();
    if include_result && signature.return_type() != InterfaceType::Void {
        variables.insert("result".to_string(), signature.return_type());
    }
    if let Some(exceptional_type) = signature.exceptional_type() {
        variables.insert("exception".to_string(), exceptional_type);
    }
    variables
}

pub(super) fn theorem_type_environment(theorem: &TheoremDefinition) -> BinderMap<InterfaceType> {
    theorem
        .parameters()
        .iter()
        .filter_map(|parameter| {
            parameter
                .click_type()
                .interface_type()
                .map(|interface_type| (parameter.name().to_string(), interface_type))
        })
        .collect()
}

pub(super) fn validate_proposition_expression_types(
    proposition: &ClickProposition,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            proposition => validate_proposition_expression_types_one(
                proposition,
                variables,
                click_functions,
                context,
            )?,
        }
    }
    Ok(())
}

fn validate_proposition_expression_types_one(
    proposition: &ClickProposition,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Value(expression) => require_proposition_value_type(
            infer_spec_value_type(expression, variables, click_functions, context)?,
        ),

        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => validate_comparison_expression_types(
            left,
            *operator,
            right,
            variables,
            click_functions,
            context,
        ),
        ClickProposition::FloatClassification { expression, .. } => {
            let actual =
                infer_contract_expression_type(expression, variables, click_functions, context)?;
            if let Some(actual) = actual
                && !type_is_float(actual)
            {
                return Err(ClickError::new(format!(
                    "float classification expects a float expression in {context}, got {}",
                    describe_interface_type(actual)
                )));
            }
            Ok(())
        }
        ClickProposition::Separate { left, right } => {
            validate_resource_subject_expression_types(left, variables, click_functions, context)?;
            validate_resource_subject_expression_types(right, variables, click_functions, context)
        }
        ClickProposition::ResourceViewable { resource } => {
            validate_resource_subject_expression_types(
                resource,
                variables,
                click_functions,
                context,
            )
        }
        ClickProposition::Contains { parent, child } => {
            validate_resource_subject_expression_types(
                parent,
                variables,
                click_functions,
                context,
            )?;
            validate_resource_subject_expression_types(child, variables, click_functions, context)
        }
        ClickProposition::Loadable { segment } => {
            validate_contract_segment_expression_types(segment, variables, click_functions, context)
        }
        ClickProposition::Defined { expression } => {
            let _ =
                infer_contract_expression_type(expression, variables, click_functions, context)?;
            Ok(())
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_proposition_expression_types(left, variables, click_functions, context)?;
            validate_proposition_expression_types(right, variables, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        } => validate_proposition_expression_types(body, variables, click_functions, context),
        ClickProposition::ForAll {
            click_type: ClickType::Integer,
            ..
        }
        | ClickProposition::Exists {
            click_type: ClickType::Integer,
            ..
        } => validate_theorem_proposition_expression_types(
            proposition,
            variables,
            &BinderSet::new(),
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
            if matches!(interface_type, ClickType::Algebraic(_)) {
                // Algebraic validation carries the datatype schema and
                // validates the complete body. This C-only pass has no
                // algebraic binding environment to add the name to.
                return Ok(());
            }
            let mut body_variables = variables.clone();
            body_variables.insert(
                name.clone(),
                interface_type.interface_type().ok_or_else(|| {
                    ClickError::new("only C quantifier binders are currently supported")
                })?,
            );
            validate_proposition_expression_types(body, &body_variables, click_functions, context)
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
            ..
        }
        | ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
            ..
        } => {
            let start_type =
                infer_contract_expression_type(start, variables, click_functions, context)?;
            let end_type =
                infer_contract_expression_type(end, variables, click_functions, context)?;
            if let Some(predicate) = lambdas::range_predicate(proposition) {
                let actual = infer_spec_value_type(predicate, variables, click_functions, context)?;
                require_range_predicate_type(actual, range_item_type(start_type, end_type))?;
            }
            let mut body_variables = variables.clone();
            body_variables.insert(item.clone(), range_item_type(start_type, end_type));
            validate_proposition_expression_types(body, &body_variables, click_functions, context)
        }
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
                    if !actual.is_some_and(InterfaceType::is_object_pointer) {
                        return Err(ClickError::new(format!(
                            "same_object expects pointer arguments in {context}, got {}",
                            actual.map_or_else(
                                || "an unknown type".to_string(),
                                describe_interface_type
                            )
                        )));
                    }
                }
                return Ok(());
            }
            for argument in arguments {
                let _ = infer_spec_value_type(argument, variables, click_functions, context)?;
            }
            Ok(())
        }
    }
}

/// Validate theorem propositions while retaining the separate mathematical
/// Integer context.  The ordinary validator intentionally only knows C
/// scalar types; dispatching Integer comparisons here keeps that validator in
/// place for every proposition that is still entirely C-valued.
pub(super) fn validate_theorem_proposition_expression_types(
    proposition: &ClickProposition,
    variables: &BinderMap<InterfaceType>,
    integer_bindings: &BinderSet,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    validate_scoped_proposition_expression_types(
        proposition,
        variables,
        integer_bindings,
        click_functions,
        context,
        false,
    )
}

fn validate_scoped_proposition_expression_types(
    proposition: &ClickProposition,
    variables: &BinderMap<InterfaceType>,
    integer_bindings: &BinderSet,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
    check_operands: bool,
) -> Result<(), ClickError> {
    let mut names = BinderSet::new();
    collect_click_proposition_referenced_binders(proposition, &mut names);
    let mut selected_variables = BinderMap::new();
    let mut selected_integers = BinderSet::new();
    for name in names {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(ty) = variables.get(&name) {
            selected_variables.insert(name.clone(), *ty);
        }
        if integer_bindings.contains(&name) {
            selected_integers.insert(name);
        }
    }
    let mut variables = selected_variables;
    let mut integer_bindings = selected_integers;
    validate_scoped_integer_proposition(
        proposition,
        &mut variables,
        &mut integer_bindings,
        click_functions,
        context,
        check_operands,
    )
}

fn validate_scoped_integer_proposition(
    proposition: &ClickProposition,
    variables: &mut BinderMap<InterfaceType>,
    integer_bindings: &mut BinderSet,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
    check_operands: bool,
) -> Result<(), ClickError> {
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            ClickProposition::Value(ContractExpression::Proposition(body)) => pending.push(body),
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            proposition => validate_scoped_integer_proposition_one(
                proposition,
                variables,
                integer_bindings,
                click_functions,
                context,
                check_operands,
            )?,
        }
    }
    Ok(())
}

fn validate_scoped_integer_proposition_one(
    proposition: &ClickProposition,
    variables: &mut BinderMap<InterfaceType>,
    integer_bindings: &mut BinderSet,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
    check_operands: bool,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::PredicateCall { name, arguments }
            if click_functions.contains_key(name) =>
        {
            let actual = infer_scoped_spec_value_type(
                &ContractExpression::Call {
                    name: name.clone(),
                    arguments: arguments.clone(),
                },
                variables,
                integer_bindings,
                click_functions,
                context,
                false,
            )?;
            require_proposition_value_type(actual)
        }

        ClickProposition::Value(expression) => {
            require_proposition_value_type(infer_scoped_spec_value_type(
                expression,
                variables,
                integer_bindings,
                click_functions,
                context,
                false,
            )?)
        }
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let mut locals = BinderSet::new();
            let left_kind =
                integer_expression_kind(left, integer_bindings, click_functions, &mut locals);
            let right_kind =
                integer_expression_kind(right, integer_bindings, click_functions, &mut locals);
            // The scoped inference pass is needed for folds, whose binder
            // carriers are not represented by the ordinary C type map.  For
            // an algebraic match without a fold, retain the established
            // carrier check: algebraic validation has already resolved each
            // constructor binding, while this pass intentionally has no
            // datatype schema to distinguish same-named C and Integer fields.
            let has_range_fold =
                contains_scoped_expression_shape(left, ScopedExpressionShape::RangeFold)
                    || contains_scoped_expression_shape(right, ScopedExpressionShape::RangeFold);
            let has_algebraic_match =
                contains_scoped_expression_shape(left, ScopedExpressionShape::AlgebraicMatch)
                    || contains_scoped_expression_shape(
                        right,
                        ScopedExpressionShape::AlgebraicMatch,
                    );
            let has_lambda = contains_scoped_expression_shape(left, ScopedExpressionShape::Lambda)
                || contains_scoped_expression_shape(right, ScopedExpressionShape::Lambda);
            if !has_lambda
                && (!has_range_fold || has_algebraic_match)
                && (!check_operands || has_algebraic_match)
            {
                if left_kind == Some(true) || right_kind == Some(true) {
                    if left_kind.is_none() || right_kind.is_none() {
                        return Err(ClickError::new(format!(
                            "mathematical Integer expressions cannot be compared with C values in {context}"
                        )));
                    }
                    if *operator == ComparisonOperator::In {
                        return Err(ClickError::new(format!(
                            "mathematical Integer expressions do not support `in` comparisons in {context}"
                        )));
                    }
                    return Ok(());
                }
                return validate_comparison_expression_types(
                    left,
                    *operator,
                    right,
                    variables,
                    click_functions,
                    context,
                );
            }
            // A comparison supplies the contextual result type for a fold.
            // Infer both sides with the other side's Integer carrier as a
            // possible expected type.  The kind scan is only a hint for this
            // bidirectional pass; acceptance below is based on the complete
            // scoped expression inference.
            let left_type = infer_scoped_spec_value_type(
                left,
                variables,
                integer_bindings,
                click_functions,
                context,
                right_kind == Some(true),
            )?;
            let right_type = infer_scoped_spec_value_type(
                right,
                variables,
                integer_bindings,
                click_functions,
                context,
                left_kind == Some(true) || matches!(&left_type, SpecValueType::Integer),
            )?;
            let left_is_integer = matches!(&left_type, SpecValueType::Integer);
            let right_is_integer = matches!(&right_type, SpecValueType::Integer);
            if left_is_integer || right_is_integer {
                if !left_is_integer || !right_is_integer {
                    return Err(ClickError::new(format!(
                        "mathematical Integer expressions cannot be compared with C values in {context}"
                    )));
                }
                if *operator == ComparisonOperator::In {
                    return Err(ClickError::new(format!(
                        "mathematical Integer expressions do not support `in` comparisons in {context}"
                    )));
                }
                Ok(())
            } else {
                validate_comparison_expression_types_without_lambda(
                    left,
                    *operator,
                    right,
                    variables,
                    click_functions,
                    context,
                )
            }
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_scoped_integer_proposition(
                left,
                variables,
                integer_bindings,
                click_functions,
                context,
                check_operands,
            )?;
            validate_scoped_integer_proposition(
                right,
                variables,
                integer_bindings,
                click_functions,
                context,
                check_operands,
            )
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        } => validate_scoped_integer_proposition(
            body,
            variables,
            integer_bindings,
            click_functions,
            context,
            check_operands,
        ),
        ClickProposition::ForAll {
            click_type,
            name,
            body,
            ..
        }
        | ClickProposition::Exists {
            click_type,
            name,
            body,
            ..
        } => {
            let previous_c = variables.remove(name);
            let previous_integer = integer_bindings.remove(name);
            match click_type {
                ClickType::Program(interface_type)
                | ClickType::CObjectPointer { interface_type, .. } => {
                    variables.insert(name.clone(), *interface_type);
                }
                ClickType::Integer => {
                    integer_bindings.insert(name.clone());
                }
                ClickType::Algebraic(_) => {
                    // The algebraic validation pass checks this body with a
                    // typed logical binding; this pass owns only C and
                    // Integer lexical carriers.
                    return Ok(());
                }
                _ => {
                    return Err(ClickError::new(
                        "this quantifier binder type is not supported",
                    ));
                }
            }
            let result = validate_scoped_integer_proposition(
                body,
                variables,
                integer_bindings,
                click_functions,
                context,
                check_operands,
            );
            variables.remove(name);
            integer_bindings.remove(name);
            if let Some(interface_type) = previous_c {
                variables.insert(name.clone(), interface_type);
            }
            if previous_integer {
                integer_bindings.insert(name.clone());
            }
            result
        }
        ClickProposition::RangeAll {
            start,
            end,
            item,
            body,
            ..
        }
        | ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
            ..
        } => {
            let start_type =
                infer_contract_expression_type(start, variables, click_functions, context)?;
            let end_type =
                infer_contract_expression_type(end, variables, click_functions, context)?;
            if let Some(predicate) = lambdas::range_predicate(proposition) {
                let actual = infer_scoped_spec_value_type(
                    predicate,
                    variables,
                    integer_bindings,
                    click_functions,
                    context,
                    false,
                )?;
                require_range_predicate_type(actual, range_item_type(start_type, end_type))?;
            }
            let previous_c = variables.insert(item.clone(), range_item_type(start_type, end_type));
            let previous_integer = integer_bindings.remove(item);
            let result = validate_scoped_integer_proposition(
                body,
                variables,
                integer_bindings,
                click_functions,
                context,
                check_operands,
            );
            variables.remove(item);
            if let Some(interface_type) = previous_c {
                variables.insert(item.clone(), interface_type);
            }
            if previous_integer {
                integer_bindings.insert(item.clone());
            }
            result
        }
        _ => {
            validate_proposition_expression_types(proposition, variables, click_functions, context)
        }
    }
}

// Some(true) has an Integer binding or explicit Integer type; Some(false)
// contains only contextual numerals. Numerals alone do not change the domain
// of an otherwise machine-valued comparison. None is outside this fragment.
fn integer_expression_kind(
    expression: &ContractExpression,
    integer_bindings: &BinderSet,
    click_functions: &BinderMap<ClickFunctionType>,
    locals: &mut BinderSet,
) -> Option<bool> {
    if let Some(id) = expression.generated_binder() {
        return Some(integer_bindings.contains(&id) || locals.contains(&id));
    }

    if deep_literal_add_type(expression).is_some() {
        return Some(false);
    }
    match expression {
        ContractExpression::IntegerContext(_) => Some(true),

        ContractExpression::Apply { function, .. } => {
            if let ContractExpression::Binding(name) = function.as_ref()
                && let Some(ClickType::Function { result, .. }) =
                    callback_binding_type(name, click_functions)
            {
                return Some(*result == ClickType::Integer);
            }
            lambdas::application_result_type(function)
                .ok()
                .map(|result| result == ClickType::Integer)
        }
        ContractExpression::Let { value, .. }
            if matches!(value.as_ref(), ContractExpression::Lambda { .. }) =>
        {
            lambdas::reduce_head(expression)
                .ok()
                .flatten()
                .and_then(|reduced| {
                    integer_expression_kind(&reduced, integer_bindings, click_functions, locals)
                })
        }

        ContractExpression::IntegerLiteral(_) => Some(false),
        ContractExpression::Call { name, arguments } if is_integer_truncation(name) => {
            (arguments.len() == 2).then_some(true)
        }
        ContractExpression::Call { name, arguments } if name == "to_integer" => {
            (arguments.len() == 1).then_some(true)
        }
        ContractExpression::ResourceField(access)
            if access.click_type == Some(ClickType::Integer) =>
        {
            Some(true)
        }
        ContractExpression::Call { name, .. } => click_functions
            .get(name)
            .and_then(|function| (function.return_type == ClickType::Integer).then_some(true)),
        ContractExpression::Binding(name) => {
            (locals.contains(name) || integer_bindings.contains(name)).then_some(true)
        }
        ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        ))
        | ContractExpression::ProgramBinding(name) => {
            (locals.contains(name) || integer_bindings.contains(name)).then_some(true)
        }
        ContractExpression::Negate(inner)
        | ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => integer_expression_kind(inner, integer_bindings, click_functions, locals),
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            let left = integer_expression_kind(left, integer_bindings, click_functions, locals)?;
            let right = integer_expression_kind(right, integer_bindings, click_functions, locals)?;
            Some(left || right)
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            accumulator,
            item,
            body,
        } => {
            if let Some(step) = lambdas::range_fold_step(expression) {
                if let Ok(result) = lambdas::application_result_type(step) {
                    return Some(result == ClickType::Integer);
                }
                if let ContractExpression::Binding(name) = step
                    && let Some(ClickType::Function { result, .. }) =
                        callback_binding_type(name, click_functions)
                {
                    return Some(*result == ClickType::Integer);
                }
            }
            let start_kind =
                integer_expression_kind(start, integer_bindings, click_functions, locals);
            let end_kind = integer_expression_kind(end, integer_bindings, click_functions, locals);
            let initial_kind =
                integer_expression_kind(initial, integer_bindings, click_functions, locals);
            let integer_index = start_kind == Some(true) || end_kind == Some(true);

            // A mathematical index or initial value establishes the fold's
            // accumulator/item carriers.  For an otherwise untyped initial
            // literal, inspect the body with an Integer accumulator as a
            // candidate, but only accept that candidate when the body has an
            // independent Integer signal (for example `to_integer(k)`).
            let accumulator_is_integer = integer_index || initial_kind == Some(true);
            let mut body_locals = locals.clone();
            if accumulator_is_integer {
                body_locals.insert(accumulator.clone());
            }
            if integer_index {
                body_locals.insert(item.clone());
            }
            let body_kind =
                integer_expression_kind(body, integer_bindings, click_functions, &mut body_locals);
            if accumulator_is_integer {
                return if body_kind == Some(true) {
                    Some(true)
                } else {
                    None
                };
            }
            if contains_integer_expression_signal(body, integer_bindings, click_functions, locals) {
                let mut candidate_locals = locals.clone();
                candidate_locals.insert(accumulator.clone());
                let candidate_kind = integer_expression_kind(
                    body,
                    integer_bindings,
                    click_functions,
                    &mut candidate_locals,
                );
                return (candidate_kind == Some(true)).then_some(true);
            }
            Some(false)
        }
        ContractExpression::Let {
            name,
            click_type: Some(ClickType::Integer),
            value,
            body,
        } => {
            integer_expression_kind(value, integer_bindings, click_functions, locals)?;
            let inserted = locals.insert(name.clone());
            let body_kind =
                integer_expression_kind(body, integer_bindings, click_functions, locals);
            if inserted {
                locals.remove(name);
            }
            body_kind.map(|_| true)
        }
        // A `let` of a C value names that value in its body, which has its
        // own kind: under Integer arithmetic an observation such as
        // `to_integer(entry) + 1` is Integer although `entry` is not.
        ContractExpression::Let {
            name, value, body, ..
        } if integer_expression_kind(value, integer_bindings, click_functions, locals)
            != Some(true) =>
        {
            let shadowed = locals.remove(name);
            let body_kind =
                integer_expression_kind(body, integer_bindings, click_functions, locals);
            if shadowed {
                locals.insert(name.clone());
            }
            body_kind
        }
        // Like a match's arms: an Integer branch makes the conditional
        // Integer, and an unsuffixed numeral branch takes the other's type.
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            let then_kind =
                integer_expression_kind(then_branch, integer_bindings, click_functions, locals)?;
            let else_kind =
                integer_expression_kind(else_branch, integer_bindings, click_functions, locals)?;
            Some(then_kind || else_kind)
        }
        ContractExpression::AlgebraicMatch { arms, .. } => {
            if arms.is_empty() {
                return None;
            }
            let mut result = None;
            let mut has_integer_arm = false;
            for arm in arms {
                // A direct arm binding is resolved against the constructor
                // schema by the algebraic validator.  Preserve the existing
                // Integer inference for that scoped binding while allowing
                // nested matches and calls to contribute their own type.
                let mut inserted_bindings = Vec::new();
                for binding in &arm.bindings {
                    if locals.insert(binding.clone()) {
                        inserted_bindings.push(binding);
                    }
                }
                let arm_kind =
                    integer_expression_kind(&arm.body, integer_bindings, click_functions, locals);
                for binding in inserted_bindings {
                    locals.remove(binding);
                }
                match arm_kind {
                    Some(true) => {
                        has_integer_arm = true;
                        result = Some(true);
                    }
                    // An unsuffixed numeral is deliberately neutral here:
                    // it can inherit the result carrier of another arm, but
                    // it must not make an otherwise C-valued match Integer.
                    Some(false) if !has_integer_arm => {}
                    Some(false) => {}
                    None => return None,
                }
            }
            result.or(Some(has_integer_arm))
        }
        _ => None,
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum ScopedExpressionShape {
    Lambda,
    RangeFold,
    AlgebraicMatch,
}

fn contains_scoped_expression_shape(
    expression: &ContractExpression,
    shape: ScopedExpressionShape,
) -> bool {
    if deep_literal_add_type(expression).is_some() {
        return false;
    }
    match expression {
        ContractExpression::IntegerContext(value) => contains_scoped_expression_shape(value, shape),

        ContractExpression::Proposition(_) => false,
        ContractExpression::Resource(_) => false,
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => false,
        ContractExpression::Lambda { body, .. } => {
            shape == ScopedExpressionShape::Lambda || contains_scoped_expression_shape(body, shape)
        }
        ContractExpression::Apply {
            function,
            arguments,
        } => {
            shape == ScopedExpressionShape::Lambda
                || contains_scoped_expression_shape(function, shape)
                || arguments
                    .iter()
                    .any(|argument| contains_scoped_expression_shape(argument, shape))
        }

        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            shape == ScopedExpressionShape::AlgebraicMatch
                || contains_scoped_expression_shape(scrutinee, shape)
                || arms
                    .iter()
                    .any(|arm| contains_scoped_expression_shape(&arm.body, shape))
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            ..
        } => {
            shape == ScopedExpressionShape::RangeFold
                || contains_scoped_expression_shape(start, shape)
                || contains_scoped_expression_shape(end, shape)
                || contains_scoped_expression_shape(initial, shape)
                || contains_scoped_expression_shape(body, shape)
        }
        ContractExpression::AlgebraicConstructor { arguments, .. }
        | ContractExpression::SequenceLiteral(arguments)
        | ContractExpression::Call { arguments, .. } => arguments
            .iter()
            .any(|argument| contains_scoped_expression_shape(argument, shape)),
        ContractExpression::MethodCall {
            receiver,
            arguments,
            ..
        } => {
            contains_scoped_expression_shape(receiver, shape)
                || arguments
                    .iter()
                    .any(|argument| contains_scoped_expression_shape(argument, shape))
        }
        ContractExpression::SequenceConcat(left, right)
        | ContractExpression::Add(left, right)
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
        | ContractExpression::BitwiseXor(left, right)
        | ContractExpression::Index(left, right) => {
            contains_scoped_expression_shape(left, shape)
                || contains_scoped_expression_shape(right, shape)
        }
        ContractExpression::Field { base, .. }
        | ContractExpression::CUnary { operand: base, .. }
        | ContractExpression::Negate(base)
        | ContractExpression::Old(base)
        | ContractExpression::At {
            expression: base, ..
        }
        | ContractExpression::BitwiseNot(base) => contains_scoped_expression_shape(base, shape),
        ContractExpression::ArrayIndex { base, .. } => {
            contains_scoped_expression_shape(base, shape)
        }
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            contains_scoped_expression_shape(then_branch, shape)
                || contains_scoped_expression_shape(else_branch, shape)
        }
        ContractExpression::Let { value, body, .. } => {
            contains_scoped_expression_shape(value, shape)
                || contains_scoped_expression_shape(body, shape)
        }
        ContractExpression::IntegerLiteral(_)
        | ContractExpression::QualifiedC { .. }
        | ContractExpression::ResourceField(_)
        | ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::Binding(_)
        | ContractExpression::ProgramExpression(_)
        | ContractExpression::ProgramBinding(_)
        | ContractExpression::ResourceCount(_)
        | ContractExpression::ResourceWildcard => false,
    }
}

fn contains_integer_expression_signal(
    expression: &ContractExpression,
    integer_bindings: &BinderSet,
    click_functions: &BinderMap<ClickFunctionType>,
    locals: &BinderSet,
) -> bool {
    if let Some(id) = expression.generated_binder() {
        return integer_bindings.contains(&id) || locals.contains(&id);
    }

    match expression {
        ContractExpression::IntegerContext(_) => true,

        ContractExpression::Apply { function, .. } => {
            lambdas::application_result_type(function) == Ok(ClickType::Integer)
        }
        ContractExpression::Call { name, arguments } if is_integer_truncation(name) => {
            arguments.len() == 2
        }
        ContractExpression::Call { name, arguments } if name == "to_integer" => {
            arguments.len() == 1
        }
        ContractExpression::ResourceField(access)
            if access.click_type == Some(ClickType::Integer) =>
        {
            true
        }
        ContractExpression::Call { name, .. } => click_functions
            .get(name)
            .is_some_and(|function| function.return_type == ClickType::Integer),
        ContractExpression::Binding(name) => {
            locals.contains(name) || integer_bindings.contains(name)
        }
        ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        ))
        | ContractExpression::ProgramBinding(name) => {
            locals.contains(name) || integer_bindings.contains(name)
        }
        ContractExpression::Negate(inner)
        | ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => contains_integer_expression_signal(inner, integer_bindings, click_functions, locals),
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            contains_integer_expression_signal(left, integer_bindings, click_functions, locals)
                || contains_integer_expression_signal(
                    right,
                    integer_bindings,
                    click_functions,
                    locals,
                )
        }
        ContractExpression::RangeFold {
            start,
            end,
            initial,
            body,
            accumulator,
            item,
        } => {
            let mut body_locals = locals.clone();
            if contains_integer_expression_signal(start, integer_bindings, click_functions, locals)
                || contains_integer_expression_signal(
                    end,
                    integer_bindings,
                    click_functions,
                    locals,
                )
            {
                body_locals.insert(accumulator.clone());
                body_locals.insert(item.clone());
            }
            contains_integer_expression_signal(initial, integer_bindings, click_functions, locals)
                || contains_integer_expression_signal(
                    body,
                    integer_bindings,
                    click_functions,
                    &body_locals,
                )
        }
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            let value_signal = contains_integer_expression_signal(
                value,
                integer_bindings,
                click_functions,
                locals,
            );
            let mut body_locals = locals.clone();
            if *click_type == Some(ClickType::Integer) {
                body_locals.insert(name.clone());
            }
            value_signal
                || contains_integer_expression_signal(
                    body,
                    integer_bindings,
                    click_functions,
                    &body_locals,
                )
        }
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            contains_integer_expression_signal(
                then_branch,
                integer_bindings,
                click_functions,
                locals,
            ) || contains_integer_expression_signal(
                else_branch,
                integer_bindings,
                click_functions,
                locals,
            )
        }
        ContractExpression::AlgebraicMatch { arms, .. } => arms.iter().any(|arm| {
            contains_integer_expression_signal(&arm.body, integer_bindings, click_functions, locals)
        }),
        _ => false,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub(super) enum SpecValueType {
    Proposition,
    Function(ClickType),
    Scalar(Option<InterfaceType>),
    Integer,
    Sequence(Option<InterfaceType>),
    Algebraic(AlgebraicTypeApplication),
}

fn require_proposition_value_type(actual: SpecValueType) -> Result<(), ClickError> {
    if matches!(
        actual,
        SpecValueType::Proposition | SpecValueType::Scalar(Some(InterfaceType::Bool))
    ) {
        Ok(())
    } else {
        Err(ClickError::new(format!(
            "a proposition application expects Prop or Bool, got {}",
            describe_spec_value_type(&actual)
        )))
    }
}

fn require_range_predicate_type(
    actual: SpecValueType,
    item_type: InterfaceType,
) -> Result<(), ClickError> {
    let expected = ClickType::Function {
        parameters: vec![ClickType::Program(item_type)],
        result: Box::new(ClickType::Proposition),
    };
    if actual == SpecValueType::Function(expected.clone()) {
        Ok(())
    } else {
        Err(ClickError::new(format!(
            "range predicate expects {}, got {}",
            describe_click_type(&expected),
            describe_spec_value_type(&actual)
        )))
    }
}

fn spec_value_matches_click_type(actual: &SpecValueType, expected: &ClickType) -> bool {
    match (actual, expected) {
        (SpecValueType::Proposition, ClickType::Proposition) => true,
        (SpecValueType::Function(actual), expected @ ClickType::Function { .. }) => {
            actual == expected
        }
        (SpecValueType::Scalar(None), ClickType::Program(_) | ClickType::CObjectPointer { .. }) => {
            true
        }
        (
            SpecValueType::Scalar(Some(actual)),
            ClickType::Program(expected)
            | ClickType::CObjectPointer {
                interface_type: expected,
                ..
            },
        ) => click_types_compatible(*actual, *expected),
        (SpecValueType::Integer, ClickType::Integer) => true,
        (SpecValueType::Algebraic(actual), ClickType::Algebraic(expected)) => actual == expected,
        _ => false,
    }
}

/// The type of `value` at a position of the 8- or 16-bit type `expected`
/// (decision G2): arithmetic `+ - * & | ^ ~` over operands of that type, or
/// unsuffixed literals, is that type's operator, so its value has the type
/// rather than C's promoted `int32`. `None` when `value` is not such
/// arithmetic. Each spine node is visited once.
pub(super) fn narrow_arithmetic_value_type(
    value: &ContractExpression,
    expected: &ClickType,
    position: &str,
    infer: &mut dyn FnMut(&ContractExpression) -> Result<SpecValueType, ClickError>,
) -> Result<Option<SpecValueType>, ClickError> {
    let ClickType::Program(
        interface_type @ (InterfaceType::Int8
        | InterfaceType::UInt8
        | InterfaceType::Int16
        | InterfaceType::UInt16),
    ) = expected
    else {
        return Ok(None);
    };
    fn spine(
        value: &ContractExpression,
        interface_type: InterfaceType,
        position: &str,
        infer: &mut dyn FnMut(&ContractExpression) -> Result<SpecValueType, ClickError>,
        root: bool,
    ) -> Result<bool, ClickError> {
        match value {
            ContractExpression::Add(left, right)
            | ContractExpression::Subtract(left, right)
            | ContractExpression::Multiply(left, right)
            | ContractExpression::BitwiseAnd(left, right)
            | ContractExpression::BitwiseOr(left, right)
            | ContractExpression::BitwiseXor(left, right) => {
                Ok(spine(left, interface_type, position, infer, false)?
                    && spine(right, interface_type, position, infer, false)?)
            }
            ContractExpression::BitwiseNot(operand) => {
                spine(operand, interface_type, position, infer, false)
            }
            _ if root => Ok(false),
            ContractExpression::IntegerLiteral(_) => Ok(true),
            leaf => match infer(leaf)? {
                SpecValueType::Scalar(Some(actual)) if actual == interface_type => Ok(true),
                // An operand of another machine type: a conversion that can
                // change its value is written.
                SpecValueType::Scalar(Some(actual))
                    if !actual.is_pointer()
                        && !matches!(
                            actual,
                            InterfaceType::Float32 | InterfaceType::Float64 | InterfaceType::Bool
                        ) =>
                {
                    Err(ClickError::new(
                        crate::surface::parser::mixed_narrow_arithmetic_message(
                            position,
                            &describe_interface_type(interface_type),
                            &crate::surface::diagnostics::describe_contract_expression(leaf),
                            &describe_interface_type(actual),
                        ),
                    ))
                }
                _ => Ok(false),
            },
        }
    }
    Ok(spine(value, *interface_type, position, infer, true)?
        .then_some(SpecValueType::Scalar(Some(*interface_type))))
}

pub(super) fn describe_spec_value_type(value_type: &SpecValueType) -> String {
    match value_type {
        SpecValueType::Proposition => "Prop".into(),
        SpecValueType::Function(ty) => describe_click_type(ty),
        SpecValueType::Scalar(Some(interface_type)) => describe_interface_type(*interface_type),
        SpecValueType::Scalar(None) => "a C value".to_string(),
        SpecValueType::Integer => "Integer".to_string(),
        SpecValueType::Sequence(_) => "a sequence".to_string(),
        SpecValueType::Algebraic(application) => {
            describe_click_type(&ClickType::Algebraic(application.clone()))
        }
    }
}

/// Infer a specification expression while retaining the lexical mathematical
/// Integer bindings.  The ordinary C inference intentionally has no place to
/// record those bindings, so using it for a fold body would turn `acc` and
/// `k` into unrelated C locals and lose the fold's carrier.  This helper is
/// deliberately bidirectional only at explicit Integer contexts: an
/// unsuffixed literal can inherit that context, while an existing C binding
/// remains a C value and is rejected when it is mixed with Integer arithmetic.
/// Bind callback signatures by name without copying the declaration environment.
pub(super) fn with_function_parameter_types<T>(
    parameters: &[FunctionParameter],
    functions: &mut BinderMap<ClickFunctionType>,
    check: impl FnOnce(&BinderMap<ClickFunctionType>) -> Result<T, ClickError>,
) -> Result<T, ClickError> {
    let mut shadowed = Vec::new();
    for parameter in parameters {
        if let ClickType::Function { parameters, result } = parameter.click_type() {
            let supported = |ty: &ClickType| {
                *ty == ClickType::Integer
                    || ty
                        .interface_type()
                        .is_some_and(|ty| type_is_arithmetic(ty) && ty != InterfaceType::Void)
            };
            if parameters.iter().any(|ty| !supported(ty))
                || (!supported(result) && **result != ClickType::Proposition)
            {
                return Err(ClickError::new(
                    "callback signatures require scalar or Integer parameters and a scalar, Integer, or Prop result",
                ));
            }
            let ty = ClickFunctionType {
                value_parameter: true,
                type_parameters: Vec::new(),
                return_type: *result.clone(),
                parameters: parameters
                    .iter()
                    .enumerate()
                    .map(|(index, ty)| FunctionParameter {
                        name: format!("argument{index}"),
                        click_type: ty.clone(),
                        struct_name: None,
                        function_pointer_signature: None,
                        constant: false,
                        pointee_constant: false,
                        reference: false,
                    })
                    .collect(),
            };
            shadowed.push((
                parameter.name().to_string(),
                functions.insert(parameter.name().to_string(), ty),
            ));
        }
    }
    let result = check(functions);
    for (name, previous) in shadowed.into_iter().rev() {
        if let Some(previous) = previous {
            functions.insert(name, previous);
        } else {
            functions.remove(&name);
        }
    }
    result
}

pub(super) fn callback_binding_type(
    name: &(impl binders::BinderKey + ?Sized),
    functions: &BinderMap<ClickFunctionType>,
) -> Option<ClickType> {
    let function = functions
        .get(name)
        .filter(|function| function.value_parameter)?;
    Some(ClickType::Function {
        parameters: function
            .parameters
            .iter()
            .map(|parameter| parameter.click_type().clone())
            .collect(),
        result: Box::new(function.return_type.clone()),
    })
}

pub(super) fn infer_scoped_spec_value_type(
    expression: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    integer_bindings: &BinderSet,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
    expected_integer: bool,
) -> Result<SpecValueType, ClickError> {
    if let Some(id) = expression.generated_binder() {
        if integer_bindings.contains(&id) {
            return Ok(SpecValueType::Integer);
        }
        if let Some(ty) = callback_binding_type(&id, click_functions) {
            return Ok(SpecValueType::Function(ty));
        }
        return Ok(SpecValueType::Scalar(variables.get(&id).copied()));
    }

    match expression {
        ContractExpression::IntegerContext(value) => {
            let actual = infer_scoped_spec_value_type(
                value,
                variables,
                integer_bindings,
                click_functions,
                context,
                true,
            )?;
            if actual != SpecValueType::Integer {
                return Err(ClickError::new(
                    "Integer context requires an Integer expression",
                ));
            }
            Ok(SpecValueType::Integer)
        }

        ContractExpression::Binding(name)
            if !variables.contains_key(name)
                && !integer_bindings.contains(name)
                && callback_binding_type(name, click_functions).is_some() =>
        {
            Ok(SpecValueType::Function(
                callback_binding_type(name, click_functions).unwrap(),
            ))
        }
        ContractExpression::Proposition(proposition) => {
            validate_scoped_proposition_expression_types(
                proposition,
                variables,
                integer_bindings,
                click_functions,
                context,
                true,
            )?;
            Ok(SpecValueType::Proposition)
        }
        ContractExpression::Lambda {
            parameters,
            result,
            body,
        } => {
            validate_lambda_value(
                parameters,
                result,
                body,
                variables,
                integer_bindings,
                click_functions,
                context,
            )?;
            Ok(SpecValueType::Function(lambdas::signature(
                parameters, result,
            )))
        }
        ContractExpression::Apply {
            function,
            arguments,
        } => {
            crate::instrumentation::record_deterministic_work(1 + arguments.len());
            if matches!(function.as_ref(), ContractExpression::Lambda { .. }) {
                infer_scoped_spec_value_type(
                    function,
                    variables,
                    integer_bindings,
                    click_functions,
                    context,
                    false,
                )?;
            }
            if !matches!(function.as_ref(), ContractExpression::Lambda { .. }) {
                let actual = infer_scoped_spec_value_type(
                    function,
                    variables,
                    integer_bindings,
                    click_functions,
                    context,
                    false,
                )?;
                let SpecValueType::Function(ClickType::Function { parameters, result }) = actual
                else {
                    return Err(ClickError::new(
                        "application expects a specification lambda value",
                    ));
                };
                let ContractExpression::Apply { arguments, .. } = expression else {
                    unreachable!()
                };
                if parameters.len() != arguments.len() {
                    return Err(ClickError::new(format!(
                        "lambda expects {} arguments, got {}",
                        parameters.len(),
                        arguments.len()
                    )));
                }
                for (expected, argument) in parameters.iter().zip(arguments) {
                    let actual = infer_scoped_spec_value_type(
                        argument,
                        variables,
                        integer_bindings,
                        click_functions,
                        context,
                        *expected == ClickType::Integer,
                    )?;
                    if !spec_value_matches_click_type(&actual, expected) {
                        return Err(ClickError::new(format!(
                            "lambda argument expects {}, got {}",
                            describe_click_type(expected),
                            describe_spec_value_type(&actual)
                        )));
                    }
                }
                return Ok(match *result {
                    ClickType::Integer => SpecValueType::Integer,
                    ClickType::Proposition => SpecValueType::Proposition,
                    ClickType::Program(ty) => SpecValueType::Scalar(Some(ty)),
                    _ => return Err(ClickError::new("unsupported callback result")),
                });
            }
            let applied = lambdas::reduce_head(expression)
                .map_err(ClickError::new)?
                .expect("an application reduces");
            infer_scoped_spec_value_type(
                &applied,
                variables,
                integer_bindings,
                click_functions,
                context,
                expected_integer,
            )
        }

        ContractExpression::ResourceField(access)
            if access.click_type == Some(ClickType::Integer) =>
        {
            Ok(SpecValueType::Integer)
        }
        ContractExpression::IntegerLiteral(_) if expected_integer => Ok(SpecValueType::Integer),
        ContractExpression::Binding(name) if integer_bindings.contains(name) => {
            Ok(SpecValueType::Integer)
        }
        ContractExpression::ProgramExpression(ProgramExpression::Variable(
            crate::kernel::BindingName::Named(name),
        ))
        | ContractExpression::ProgramBinding(name)
            if integer_bindings.contains(name) =>
        {
            Ok(SpecValueType::Integer)
        }
        ContractExpression::Negate(inner) => {
            if !expected_integer && matches!(inner.as_ref(), ContractExpression::IntegerLiteral(_))
            {
                // Type the signed literal as a whole: INT32_MIN's positive
                // magnitude alone needs int64, but its negation is int32.
                return infer_contract_expression_type(
                    expression,
                    variables,
                    click_functions,
                    context,
                )
                .map(SpecValueType::Scalar);
            }
            let inner = infer_scoped_spec_value_type(
                inner,
                variables,
                integer_bindings,
                click_functions,
                context,
                expected_integer,
            )?;
            match inner {
                SpecValueType::Integer => Ok(SpecValueType::Integer),
                SpecValueType::Scalar(interface_type) => Ok(SpecValueType::Scalar(interface_type)),
                other => Err(ClickError::new(format!(
                    "negation expects a scalar or Integer in {context}, got {}",
                    describe_spec_value_type(&other)
                ))),
            }
        }
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            let (left, right) = infer_scoped_arithmetic_operands(
                left,
                right,
                variables,
                integer_bindings,
                click_functions,
                context,
                expected_integer,
            )?;
            if matches!(&left, SpecValueType::Integer) && matches!(&right, SpecValueType::Integer) {
                return Ok(SpecValueType::Integer);
            }
            let left_c = scoped_scalar_type(&left);
            let right_c = scoped_scalar_type(&right);
            let result = match expression {
                ContractExpression::Add(_, _) => pointer_arithmetic_type(left_c, right_c)
                    .or_else(|| arithmetic_result_type(left_c, right_c)),
                ContractExpression::Subtract(_, _) => match (left_c, right_c) {
                    (Some(left), Some(right))
                        if type_is_data_pointer(left) && type_is_scalar(right) =>
                    {
                        Some(left)
                    }
                    _ => arithmetic_result_type(left_c, right_c),
                },
                ContractExpression::Multiply(_, _) => arithmetic_result_type(left_c, right_c),
                _ => unreachable!(),
            };
            Ok(SpecValueType::Scalar(result))
        }
        ContractExpression::Divide(left, right) => {
            let (left, right) = infer_scoped_arithmetic_operands(
                left,
                right,
                variables,
                integer_bindings,
                click_functions,
                context,
                expected_integer,
            )?;
            if matches!(&left, SpecValueType::Integer) || matches!(&right, SpecValueType::Integer) {
                return Err(ClickError::new(format!(
                    "division is not supported for mathematical Integer expressions in {context}"
                )));
            }
            Ok(SpecValueType::Scalar(arithmetic_result_type(
                scoped_scalar_type(&left),
                scoped_scalar_type(&right),
            )))
        }
        ContractExpression::Remainder(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right)
        | ContractExpression::ShiftLeft(left, right)
        | ContractExpression::RustShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::RustShiftRight(left, right) => {
            let (left, right) = infer_scoped_arithmetic_operands(
                left,
                right,
                variables,
                integer_bindings,
                click_functions,
                context,
                false,
            )?;
            if matches!(&left, SpecValueType::Integer) || matches!(&right, SpecValueType::Integer) {
                return Err(ClickError::new(format!(
                    "C bitwise or remainder operators cannot be applied to mathematical Integer expressions in {context}"
                )));
            }
            if matches!(
                expression,
                ContractExpression::RustShiftLeft(..) | ContractExpression::RustShiftRight(..)
            ) {
                return Ok(left);
            }
            if matches!(
                expression,
                ContractExpression::ShiftLeft(..) | ContractExpression::ShiftRight(..)
            ) {
                return Ok(SpecValueType::Scalar(contract_shift_result_type(
                    scoped_scalar_type(&left),
                    scoped_scalar_type(&right),
                    false,
                )));
            }
            Ok(SpecValueType::Scalar(arithmetic_result_type(
                scoped_scalar_type(&left),
                scoped_scalar_type(&right),
            )))
        }
        ContractExpression::BitwiseNot(inner) => {
            let inner = infer_scoped_spec_value_type(
                inner,
                variables,
                integer_bindings,
                click_functions,
                context,
                false,
            )?;
            if matches!(
                &inner,
                SpecValueType::Function(_) | SpecValueType::Proposition
            ) {
                return Err(ClickError::new(
                    "specification functions cannot be bitwise operands",
                ));
            }
            if matches!(&inner, SpecValueType::Integer) {
                return Err(ClickError::new(format!(
                    "C bitwise operators cannot be applied to mathematical Integer expressions in {context}"
                )));
            }
            Ok(SpecValueType::Scalar(
                scoped_scalar_type(&inner)
                    .filter(|interface_type| type_is_scalar(*interface_type))
                    .map(|interface_type| {
                        scalar_arithmetic_result_type(interface_type, interface_type)
                    }),
            ))
        }
        ContractExpression::Index(base, index) => {
            let _ = infer_scoped_spec_value_type(
                index,
                variables,
                integer_bindings,
                click_functions,
                context,
                false,
            )?;
            let base = infer_scoped_spec_value_type(
                base,
                variables,
                integer_bindings,
                click_functions,
                context,
                false,
            )?;
            if matches!(&base, SpecValueType::Integer) {
                return Err(ClickError::new(format!(
                    "mathematical Integer expressions cannot be indexed in {context}"
                )));
            }
            Ok(SpecValueType::Scalar(
                scoped_scalar_type(&base).and_then(pointer_element_type),
            ))
        }
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            let then_type = infer_scoped_spec_value_type(
                then_branch,
                variables,
                integer_bindings,
                click_functions,
                context,
                expected_integer,
            )?;
            let else_type = infer_scoped_spec_value_type(
                else_branch,
                variables,
                integer_bindings,
                click_functions,
                context,
                expected_integer,
            )?;
            if matches!(&then_type, SpecValueType::Integer)
                || matches!(&else_type, SpecValueType::Integer)
            {
                if matches!(&then_type, SpecValueType::Integer)
                    && matches!(&else_type, SpecValueType::Integer)
                {
                    Ok(SpecValueType::Integer)
                } else {
                    Err(ClickError::new(format!(
                        "conditional branches mix mathematical Integer and C values in {context}"
                    )))
                }
            } else if then_type == else_type {
                Ok(then_type)
            } else {
                Ok(SpecValueType::Scalar(arithmetic_result_type(
                    scoped_scalar_type(&then_type),
                    scoped_scalar_type(&else_type),
                )))
            }
        }
        ContractExpression::RangeFold { .. } => infer_scoped_range_fold_type(
            expression,
            variables,
            integer_bindings,
            click_functions,
            context,
            expected_integer,
        ),
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            let value_expected_integer = match click_type {
                Some(ClickType::Integer) => true,
                Some(_) => false,
                None => expected_integer,
            };
            let mut value_type = infer_scoped_spec_value_type(
                value,
                variables,
                integer_bindings,
                click_functions,
                context,
                value_expected_integer,
            )?;
            if let Some(expected) = click_type
                && !spec_value_matches_click_type(&value_type, expected)
                && let Some(narrow) = narrow_arithmetic_value_type(
                    value,
                    expected,
                    &format!("`let {name}`"),
                    &mut |leaf| {
                        infer_scoped_spec_value_type(
                            leaf,
                            variables,
                            integer_bindings,
                            click_functions,
                            context,
                            false,
                        )
                    },
                )?
            {
                value_type = narrow;
            }
            if let Some(expected) = click_type
                && !spec_value_matches_click_type(&value_type, expected)
            {
                return Err(ClickError::new(format!(
                    "let binding `{name}` expects {}, got {} in {context}",
                    describe_click_type(expected),
                    describe_spec_value_type(&value_type)
                )));
            }

            if matches!(
                value_type,
                SpecValueType::Function(_) | SpecValueType::Proposition
            ) {
                let replacements = BTreeMap::from([(name.clone(), value.as_ref().clone())]);
                let reduced =
                    crate::surface::lowering::substitute_contract_expression(body, &replacements)
                        .map_err(ClickError::new)?;
                return infer_scoped_spec_value_type(
                    &reduced,
                    variables,
                    integer_bindings,
                    click_functions,
                    context,
                    expected_integer,
                );
            }
            let mut names = BinderSet::new();
            collect_contract_expression_referenced_binders(body, &mut names);
            let mut body_variables = BinderMap::new();
            let mut body_integer_bindings = BinderSet::new();
            for name in names {
                crate::instrumentation::record_deterministic_work(1);
                if let Some(ty) = variables.get(&name) {
                    body_variables.insert(name.clone(), *ty);
                }
                if integer_bindings.contains(&name) {
                    body_integer_bindings.insert(name);
                }
            }
            body_variables.remove(name);
            body_integer_bindings.remove(name);
            match (&value_type, click_type) {
                (SpecValueType::Integer, _) | (_, Some(ClickType::Integer)) => {
                    body_integer_bindings.insert(name.clone());
                }
                (SpecValueType::Scalar(Some(interface_type)), _) => {
                    body_variables.insert(name.clone(), *interface_type);
                }
                _ => {}
            }
            infer_scoped_spec_value_type(
                body,
                &body_variables,
                &body_integer_bindings,
                click_functions,
                context,
                expected_integer,
            )
        }
        ContractExpression::Call { name, arguments } if is_integer_truncation(name) => {
            let (left, right) =
                integer_truncation_arguments(name, arguments).map_err(ClickError::new)?;
            for argument in [left, right] {
                if infer_scoped_spec_value_type(
                    argument,
                    variables,
                    integer_bindings,
                    click_functions,
                    context,
                    true,
                )? != SpecValueType::Integer
                {
                    return Err(ClickError::new(format!(
                        "{name} expects two Integer arguments"
                    )));
                }
            }
            Ok(SpecValueType::Integer)
        }
        ContractExpression::Call { name, arguments } if name == "to_integer" => {
            let argument = integer_conversion_argument(name, arguments).map_err(ClickError::new)?;
            let argument_type = infer_scoped_spec_value_type(
                argument,
                variables,
                integer_bindings,
                click_functions,
                context,
                false,
            )?;
            match argument_type {
                SpecValueType::Algebraic(application)
                    if application.name() == "Nat" && application.arguments().is_empty() =>
                {
                    Ok(SpecValueType::Integer)
                }
                SpecValueType::Scalar(interface_type) => {
                    if let Some(interface_type) = interface_type
                        && !machine_integer_source_type(interface_type)
                    {
                        return Err(ClickError::new(
                            "to_integer expects a signed or unsigned machine integer",
                        ));
                    }
                    Ok(SpecValueType::Integer)
                }
                // An Integer is its own exact value.
                SpecValueType::Integer => Ok(SpecValueType::Integer),
                other => Err(ClickError::new(format!(
                    "to_integer expects a machine integer or Nat, got {} in {context}",
                    describe_spec_value_type(&other)
                ))),
            }
        }
        ContractExpression::Call { name, arguments } if name == "to_nat" => {
            let argument = integer_conversion_argument(name, arguments).map_err(ClickError::new)?;
            validate_to_nat_argument_type(argument, variables, click_functions, context)?;
            Ok(SpecValueType::Algebraic(
                AlgebraicTypeApplication::concrete("Nat"),
            ))
        }
        ContractExpression::Call { name, arguments } => {
            let Some(function) = click_functions.get(name) else {
                return Ok(SpecValueType::Scalar(infer_contract_expression_type(
                    expression,
                    variables,
                    click_functions,
                    context,
                )?));
            };
            for (index, (parameter, argument)) in
                function.parameters.iter().zip(arguments).enumerate()
            {
                let expected = parameter.click_type();
                let actual = infer_scoped_spec_value_type(
                    argument,
                    variables,
                    integer_bindings,
                    click_functions,
                    context,
                    matches!(expected, ClickType::Integer),
                )?;
                if matches!(expected, ClickType::Function { .. }) {
                    if !spec_value_matches_click_type(&actual, expected) {
                        return Err(ClickError::new(format!(
                            "function `{name}` callback expects {}, got {}",
                            describe_click_type(expected),
                            describe_spec_value_type(&actual)
                        )));
                    }
                    continue;
                }
                if matches!(
                    &actual,
                    SpecValueType::Function(_) | SpecValueType::Proposition
                ) {
                    return Err(ClickError::new(format!(
                        "function `{name}` argument {index} expects {}, got a specification function in {context}",
                        describe_click_type(expected)
                    )));
                }
                match expected {
                    ClickType::Integer if !matches!(&actual, SpecValueType::Integer) => {
                        return Err(ClickError::new(format!(
                            "function `{name}` argument {index} expects Integer in {context}"
                        )));
                    }
                    // The C null pointer constant types as any pointer
                    // parameter, in a pure function exactly as in a resource
                    // argument.
                    ClickType::Program(expected)
                    | ClickType::CObjectPointer {
                        interface_type: expected,
                        ..
                    } if crate::surface::lowering::argument_is_null_pointer_constant(
                        argument, *expected,
                    ) => {}
                    ClickType::Program(expected)
                    | ClickType::CObjectPointer {
                        interface_type: expected,
                        ..
                    } => {
                        if matches!(&actual, SpecValueType::Integer) {
                            return Err(ClickError::new(format!(
                                "function `{name}` argument {index} expects {}, got Integer in {context}",
                                describe_interface_type(*expected)
                            )));
                        }
                        if let SpecValueType::Scalar(Some(actual)) = &actual
                            && !click_argument_types_compatible(*actual, *expected)
                        {
                            return Err(ClickError::new(format!(
                                "function `{name}` argument {index} expects {}, got {} in {context}",
                                describe_interface_type(*expected),
                                describe_interface_type(*actual)
                            )));
                        }
                    }
                    _ => {}
                }
            }
            Ok(match &function.return_type {
                ClickType::Proposition => SpecValueType::Proposition,
                ClickType::Resource => {
                    return Err(ClickError::new(
                        "Resource function results are not supported",
                    ));
                }
                ClickType::Integer => SpecValueType::Integer,
                ClickType::Program(interface_type)
                | ClickType::CObjectPointer { interface_type, .. } => {
                    SpecValueType::Scalar(Some(*interface_type))
                }
                ClickType::Algebraic(application) => SpecValueType::Algebraic(application.clone()),
                ClickType::Function { .. } | ClickType::Parameter(_) => SpecValueType::Scalar(None),
            })
        }
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => infer_scoped_spec_value_type(
            inner,
            variables,
            integer_bindings,
            click_functions,
            context,
            expected_integer,
        ),
        _ => infer_spec_value_type(expression, variables, click_functions, context),
    }
}

fn infer_scoped_arithmetic_operands(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    integer_bindings: &BinderSet,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
    expected_integer: bool,
) -> Result<(SpecValueType, SpecValueType), ClickError> {
    let mut left_type = infer_scoped_spec_value_type(
        left,
        variables,
        integer_bindings,
        click_functions,
        context,
        expected_integer,
    )?;
    let mut right_type = infer_scoped_spec_value_type(
        right,
        variables,
        integer_bindings,
        click_functions,
        context,
        expected_integer,
    )?;
    if matches!(&left_type, SpecValueType::Integer)
        || matches!(&right_type, SpecValueType::Integer)
        || expected_integer
    {
        if !matches!(&left_type, SpecValueType::Integer) {
            left_type = infer_scoped_spec_value_type(
                left,
                variables,
                integer_bindings,
                click_functions,
                context,
                true,
            )?;
        }
        if !matches!(&right_type, SpecValueType::Integer) {
            right_type = infer_scoped_spec_value_type(
                right,
                variables,
                integer_bindings,
                click_functions,
                context,
                true,
            )?;
        }
        if matches!(&left_type, SpecValueType::Integer)
            != matches!(&right_type, SpecValueType::Integer)
        {
            return Err(ClickError::new(format!(
                "mathematical Integer arithmetic cannot mix with C values in {context}"
            )));
        }
    }
    if matches!(
        &left_type,
        SpecValueType::Function(_) | SpecValueType::Proposition
    ) || matches!(
        &right_type,
        SpecValueType::Function(_) | SpecValueType::Proposition
    ) {
        return Err(ClickError::new(format!(
            "specification functions cannot be arithmetic operands in {context}"
        )));
    }
    Ok((left_type, right_type))
}

fn scoped_scalar_type(value_type: &SpecValueType) -> Option<InterfaceType> {
    match value_type {
        SpecValueType::Scalar(interface_type) => *interface_type,
        _ => None,
    }
}

/// The item type of a `.all`/`.any` range: a `uint64` when either endpoint
/// is one, as for a range fold, and otherwise an `int32`.
fn range_item_type(start: Option<InterfaceType>, end: Option<InterfaceType>) -> InterfaceType {
    if matches!(start, Some(InterfaceType::UInt64(_)))
        || matches!(end, Some(InterfaceType::UInt64(_)))
    {
        InterfaceType::UInt64(LongRank::Long)
    } else {
        InterfaceType::Int32
    }
}

pub(super) fn infer_scoped_range_fold_bindings(
    expression: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    integer_bindings: &BinderSet,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
    expected_integer: bool,
) -> Result<(ClickType, ClickType), ClickError> {
    let ContractExpression::RangeFold {
        start,
        end,
        initial,
        accumulator,
        item,
        body,
    } = expression
    else {
        unreachable!()
    };
    let start_type = infer_scoped_spec_value_type(
        start,
        variables,
        integer_bindings,
        click_functions,
        context,
        false,
    )?;
    let end_type = infer_scoped_spec_value_type(
        end,
        variables,
        integer_bindings,
        click_functions,
        context,
        false,
    )?;
    // A range with a `uint64` endpoint ranges over `uint64` values. The
    // other endpoint is a `uint64` too, or a literal, which is that number.
    let uint64_index = {
        let uint64 = |ty: &SpecValueType| {
            matches!(ty, SpecValueType::Scalar(Some(InterfaceType::UInt64(_))))
        };
        let literal = |expression: &ContractExpression| {
            matches!(
                contract_expression_as_program_expression(expression),
                Some(ProgramExpression::Value(ProgramValue::Int32(value)))
                    if value.as_const().is_some_and(|value| value <= i32::MAX as u32)
            )
        };
        (uint64(&start_type) && (uint64(&end_type) || literal(end)))
            || (uint64(&end_type) && literal(start))
    };
    let integer_index = match (&start_type, &end_type) {
        (SpecValueType::Integer, SpecValueType::Integer) => true,
        (SpecValueType::Integer, _) | (_, SpecValueType::Integer) => {
            return Err(ClickError::new(format!(
                "range fold bounds cannot mix mathematical Integer and C values in {context}"
            )));
        }
        (SpecValueType::Scalar(Some(start)), SpecValueType::Scalar(Some(end)))
            if (*start != InterfaceType::Int32 || *end != InterfaceType::Int32)
                && !uint64_index =>
        {
            return Err(ClickError::new(format!(
                "range fold bounds must both be int32 or both be uint64 in {context}"
            )));
        }
        _ => false,
    };

    let step_integer = if let Some(step) = lambdas::range_fold_step(expression) {
        matches!(infer_scoped_spec_value_type(step, variables, integer_bindings, click_functions, context, false)?, SpecValueType::Function(ClickType::Function { result, .. }) if *result == ClickType::Integer)
    } else {
        false
    };
    let initial_type = infer_scoped_spec_value_type(
        initial,
        variables,
        integer_bindings,
        click_functions,
        context,
        expected_integer || integer_index || step_integer,
    )?;
    // Fold binders are represented as ordinary parser variables until this
    // scoped pass assigns their carriers.  Seed the signal walk with the
    // binders that are already known to be mathematical so an expression
    // such as `acc + to_integer(k)` can establish an Integer accumulator
    // even when its initial value is the untyped literal `0`.
    let mut body_signal_locals = BinderSet::new();
    if integer_index || matches!(&initial_type, SpecValueType::Integer) || expected_integer {
        body_signal_locals.insert(accumulator.clone());
    }
    if integer_index {
        body_signal_locals.insert(item.clone());
    }
    let body_may_be_integer = contains_integer_expression_signal(
        body,
        integer_bindings,
        click_functions,
        &body_signal_locals,
    );
    let integer_accumulator = integer_index
        || matches!(&initial_type, SpecValueType::Integer)
        || expected_integer
        || body_may_be_integer;

    let accumulator_type = if integer_accumulator {
        ClickType::Integer
    } else {
        if uint64_index {
            return Err(ClickError::new(format!(
                "range fold with uint64 bounds requires an Integer accumulator in {context}; C-valued range folds support only int32 bounds"
            )));
        }
        if initial_type != SpecValueType::Scalar(Some(InterfaceType::Int32)) {
            return Err(ClickError::new(format!(
                "C-valued range fold requires an int32 accumulator in {context}; other C accumulator types are not supported"
            )));
        }
        ClickType::Program(InterfaceType::Int32)
    };
    let item_type = if integer_index {
        ClickType::Integer
    } else if uint64_index {
        ClickType::Program(InterfaceType::UInt64(LongRank::Long))
    } else {
        ClickType::Program(InterfaceType::Int32)
    };
    if let Some(step) = lambdas::range_fold_step(expression) {
        let actual = infer_scoped_spec_value_type(
            step,
            variables,
            integer_bindings,
            click_functions,
            context,
            false,
        )?;
        let expected = ClickType::Function {
            parameters: vec![accumulator_type.clone(), item_type.clone()],
            result: Box::new(accumulator_type.clone()),
        };
        if actual != SpecValueType::Function(expected.clone()) {
            return Err(ClickError::new(format!(
                "range fold step expects {}, got {} in {context}",
                describe_click_type(&expected),
                describe_spec_value_type(&actual),
            )));
        }
        let initial_type = infer_scoped_spec_value_type(
            initial,
            variables,
            integer_bindings,
            click_functions,
            context,
            accumulator_type == ClickType::Integer,
        )?;
        if !spec_value_matches_click_type(&initial_type, &accumulator_type) {
            return Err(ClickError::new(format!(
                "range fold initial value expects {}, got {} in {context}",
                describe_click_type(&accumulator_type),
                describe_spec_value_type(&initial_type),
            )));
        }
    }
    Ok((accumulator_type, item_type))
}

fn infer_scoped_range_fold_type(
    expression: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    integer_bindings: &BinderSet,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
    expected_integer: bool,
) -> Result<SpecValueType, ClickError> {
    let ContractExpression::RangeFold {
        accumulator,
        item,
        body,
        ..
    } = expression
    else {
        unreachable!()
    };
    let (accumulator_type, item_type) = infer_scoped_range_fold_bindings(
        expression,
        variables,
        integer_bindings,
        click_functions,
        context,
        expected_integer,
    )?;
    let mut referenced = BinderSet::new();
    collect_contract_expression_referenced_binders(body, &mut referenced);
    let mut body_variables = BinderMap::new();
    let mut body_integer_bindings = BinderSet::new();
    for name in referenced {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(ty) = variables.get(&name) {
            body_variables.insert(name.clone(), *ty);
        }
        if integer_bindings.contains(&name) {
            body_integer_bindings.insert(name);
        }
    }
    for (name, ty) in [(accumulator, &accumulator_type), (item, &item_type)] {
        body_variables.remove(name);
        body_integer_bindings.remove(name);
        match ty {
            ClickType::Integer => {
                body_integer_bindings.insert(name.clone());
            }
            ClickType::Program(ty)
            | ClickType::CObjectPointer {
                interface_type: ty, ..
            } => {
                body_variables.insert(name.clone(), *ty);
            }
            _ => unreachable!(),
        }
    }
    let body_type = infer_scoped_spec_value_type(
        body,
        &body_variables,
        &body_integer_bindings,
        click_functions,
        context,
        accumulator_type == ClickType::Integer,
    )?;
    match (accumulator_type, body_type) {
        (ClickType::Integer, SpecValueType::Integer) => Ok(SpecValueType::Integer),
        (ClickType::Integer, _) => Err(ClickError::new(format!(
            "range fold body must preserve Integer accumulator in {context}"
        ))),
        (
            ClickType::Program(initial)
            | ClickType::CObjectPointer {
                interface_type: initial,
                ..
            },
            SpecValueType::Scalar(body),
        ) if body.is_none_or(|body| click_types_compatible(initial, body)) => {
            Ok(SpecValueType::Scalar(Some(initial)))
        }
        _ => Err(ClickError::new(format!(
            "range fold body must preserve accumulator type in {context}"
        ))),
    }
}

fn validate_comparison_expression_types(
    left: &ContractExpression,
    operator: ComparisonOperator,
    right: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    if contains_scoped_expression_shape(left, ScopedExpressionShape::Lambda)
        || contains_scoped_expression_shape(right, ScopedExpressionShape::Lambda)
    {
        let proposition = ClickProposition::Comparison {
            left: left.clone(),
            operator,
            right: right.clone(),
        };
        return validate_theorem_proposition_expression_types(
            &proposition,
            variables,
            &BinderSet::new(),
            click_functions,
            context,
        );
    }
    validate_comparison_expression_types_without_lambda(
        left,
        operator,
        right,
        variables,
        click_functions,
        context,
    )
}

fn validate_comparison_expression_types_without_lambda(
    left: &ContractExpression,
    operator: ComparisonOperator,
    right: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let mut locals = BinderSet::new();
    let no_integer_parameters = BinderSet::new();
    let left_kind =
        integer_expression_kind(left, &no_integer_parameters, &BinderMap::new(), &mut locals);
    let right_kind = integer_expression_kind(
        right,
        &no_integer_parameters,
        &BinderMap::new(),
        &mut locals,
    );
    if left_kind == Some(true) || right_kind == Some(true) {
        if left_kind.is_none() || right_kind.is_none() {
            return Err(ClickError::new(format!(
                "mathematical Integer expressions cannot be compared with C values in {context}"
            )));
        }
        if operator == ComparisonOperator::In {
            return Err(ClickError::new(format!(
                "mathematical Integer expressions do not support `in` comparisons in {context}"
            )));
        }
        return Ok(());
    }
    let left_type = infer_spec_value_type(left, variables, click_functions, context)?;
    let right_type = infer_spec_value_type(right, variables, click_functions, context)?;
    refuse_bool_literal_comparison(left, &left_type, right, &right_type, context)?;
    refuse_bool_integer_comparison(left, &left_type, operator, right, &right_type, context)?;
    match (left_type, right_type) {
        (SpecValueType::Function(_) | SpecValueType::Proposition, _)
        | (_, SpecValueType::Function(_) | SpecValueType::Proposition) => Err(ClickError::new(
            "specification functions cannot be compared; apply them to values instead",
        )),

        (SpecValueType::Scalar(element), SpecValueType::Sequence(sequence))
            if operator == ComparisonOperator::In =>
        {
            if let (Some(element), Some(sequence)) = (element, sequence)
                && element != sequence
            {
                return Err(ClickError::new(format!(
                    "membership element type does not match sequence element type in {context}: {} and {}",
                    describe_interface_type(element),
                    describe_interface_type(sequence)
                )));
            }
            Ok(())
        }
        (SpecValueType::Scalar(left_type), SpecValueType::Scalar(right_type)) => {
            if let (Some(left_type), Some(right_type)) = (left_type, right_type)
                && left_type.to_kernel_type().is_pointer()
                && right_type.to_kernel_type().is_pointer()
                && !left_type
                    .to_kernel_type()
                    .pointer_types_compatible(right_type.to_kernel_type())
            {
                return Err(ClickError::new(format!(
                    "incompatible pointer comparison in {context}: {} and {}; use a checked byte-view cast to compare byte views",
                    describe_interface_type(left_type),
                    describe_interface_type(right_type)
                )));
            }
            if operator == ComparisonOperator::In {
                Err(ClickError::new(format!(
                    "right operand of `in` must be a sequence in {context}"
                )))
            } else {
                Ok(())
            }
        }
        (SpecValueType::Sequence(left), SpecValueType::Sequence(right)) => {
            if !matches!(
                operator,
                ComparisonOperator::Equal | ComparisonOperator::NotEqual
            ) {
                return Err(ClickError::new(format!(
                    "sequences support only `==` and `!=` comparisons in {context}"
                )));
            }
            if let (Some(left), Some(right)) = (left, right)
                && left != right
            {
                return Err(ClickError::new(format!(
                    "sequence element types do not match in {context}: {} and {}",
                    describe_interface_type(left),
                    describe_interface_type(right)
                )));
            }
            Ok(())
        }
        (SpecValueType::Algebraic(left), SpecValueType::Algebraic(right)) => {
            if !matches!(
                operator,
                ComparisonOperator::Equal | ComparisonOperator::NotEqual
            ) {
                return Err(ClickError::new(format!(
                    "algebraic values support only `==` and `!=` comparisons in {context}"
                )));
            }
            if left != right {
                return Err(ClickError::new(format!(
                    "algebraic comparison type mismatch in {context}: `{}` and `{}`",
                    describe_click_type(&ClickType::Algebraic(left.clone())),
                    describe_click_type(&ClickType::Algebraic(right.clone()))
                )));
            }
            Ok(())
        }
        // A Rust enum's value read through a reference, `*o`, is a value of
        // that enum's spec type.
        (
            SpecValueType::Scalar(Some(InterfaceType::Parameter(name))),
            SpecValueType::Algebraic(application),
        )
        | (
            SpecValueType::Algebraic(application),
            SpecValueType::Scalar(Some(InterfaceType::Parameter(name))),
        ) if AlgebraicTypeApplication::of_enum_interface_type(InterfaceType::Parameter(name))
            .is_some_and(|value| value.name() == application.name())
            && matches!(
                operator,
                ComparisonOperator::Equal | ComparisonOperator::NotEqual
            ) =>
        {
            Ok(())
        }
        _ if operator == ComparisonOperator::In => Err(ClickError::new(format!(
            "`in` requires a scalar element on the left and a sequence on the right in {context}"
        ))),
        _ => Err(ClickError::new(format!(
            "sequence equality requires a sequence on both sides in {context}"
        ))),
    }
}

/// Refuse each comparison of a `bool` literal with a value whose type is
/// known and is not `bool`, anywhere in `proposition`. Contract clauses of a
/// C function are otherwise typed when they are lowered; this one check runs
/// before that so `requires count;` for an integer `count` is a type error,
/// not the claim `count == 1`. A value whose type this pass cannot infer is
/// left to lowering.
pub(super) fn refuse_bool_literal_comparisons(
    proposition: &ClickProposition,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let mut pending = vec![(proposition, None::<BinderMap<InterfaceType>>)];
    while let Some((proposition, scoped)) = pending.pop() {
        let scope = scoped.as_ref().unwrap_or(variables);
        match proposition {
            ClickProposition::Comparison {
                left,
                operator,
                right,
            } => {
                let infer = |expression: &ContractExpression| {
                    if crate::surface::bool_literal_value(expression).is_some() {
                        return SpecValueType::Scalar(Some(InterfaceType::Bool));
                    }
                    infer_contract_expression_type(expression, scope, click_functions, context)
                        .map(SpecValueType::Scalar)
                        .unwrap_or(SpecValueType::Scalar(None))
                };
                let (left_type, right_type) = (infer(left), infer(right));
                refuse_bool_literal_comparison(left, &left_type, right, &right_type, context)?;
                refuse_bool_integer_comparison(
                    left,
                    &left_type,
                    *operator,
                    right,
                    &right_type,
                    context,
                )?;
            }
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push((right, scoped.clone()));
                pending.push((left, scoped));
            }
            ClickProposition::Not(body)
            | ClickProposition::At {
                proposition: body, ..
            } => {
                pending.push((body, scoped));
            }
            ClickProposition::ForAll {
                click_type,
                name,
                body,
                ..
            }
            | ClickProposition::Exists {
                click_type,
                name,
                body,
                ..
            } => {
                let mut body_variables = scope.clone();
                match click_type.interface_type() {
                    Some(interface_type) => body_variables.insert(name.clone(), interface_type),
                    None => body_variables.remove(name),
                };
                pending.push((body, Some(body_variables)));
            }
            ClickProposition::RangeAll { item, body, .. }
            | ClickProposition::RangeAny { item, body, .. } => {
                let mut body_variables = scope.clone();
                body_variables.remove(item);
                pending.push((body, Some(body_variables)));
            }
            _ => {}
        }
    }
    Ok(())
}

/// Decision D2 (Stage 5, `design/machine-integers.md`): a `Bool` has no
/// integer value and no order. A `Bool` compared with an integer, or two
/// `Bool`s ordered, is refused here when both types are known; lowering
/// refuses the rest.
fn refuse_bool_integer_comparison(
    left: &ContractExpression,
    left_type: &SpecValueType,
    operator: ComparisonOperator,
    right: &ContractExpression,
    right_type: &SpecValueType,
    context: &str,
) -> Result<(), ClickError> {
    let is_bool = |value_type: &SpecValueType| {
        matches!(value_type, SpecValueType::Scalar(Some(InterfaceType::Bool)))
    };
    let is_integer = |expression: &ContractExpression, value_type: &SpecValueType| match value_type
    {
        SpecValueType::Scalar(Some(InterfaceType::Bool)) => false,
        SpecValueType::Scalar(Some(interface_type)) => {
            type_is_arithmetic(*interface_type) && !type_is_float(*interface_type)
        }
        SpecValueType::Integer => true,
        SpecValueType::Scalar(None) => is_untyped_integer_literal_expression(expression),
        _ => false,
    };
    let describe = crate::surface::diagnostics::describe_contract_expression;
    let ordered = !matches!(
        operator,
        ComparisonOperator::Equal | ComparisonOperator::NotEqual | ComparisonOperator::In
    );
    if ordered && (is_bool(left_type) || is_bool(right_type)) {
        let operand = if is_bool(left_type) { left } else { right };
        return Err(ClickError::new(format!(
            "`{}` is a `Bool`, which has no order, in {context}; compare `Bool` values with `==` or `!=`, or write `{} as int32`",
            describe(operand),
            describe(operand),
        )));
    }
    for (boolean, boolean_type, other, other_type) in [
        (left, left_type, right, right_type),
        (right, right_type, left, left_type),
    ] {
        if is_bool(boolean_type) && is_integer(other, other_type) {
            return Err(ClickError::new(format!(
                "`{}` is a `Bool` and `{}` an integer in {context}; a `Bool` has no integer value: write `{} as int32`, or compare `{}` with `true` or `false`",
                describe(boolean),
                describe(other),
                describe(boolean),
                describe(boolean),
            )));
        }
    }
    Ok(())
}

/// Decision D2 (Stage 5): a `Bool` operand of contract arithmetic, an
/// implicit promotion included, is refused; its integer value is the
/// written cast `b as int32`. Reads the operand types already inferred.
fn refuse_bool_arithmetic_operands(
    operands: [(&ContractExpression, Option<InterfaceType>); 2],
    context: &str,
) -> Result<(), ClickError> {
    for (operand, operand_type) in operands {
        if operand_type == Some(InterfaceType::Bool)
            || crate::surface::bool_literal_value(operand).is_some()
        {
            let operand = crate::surface::diagnostics::describe_contract_expression(operand);
            return Err(ClickError::new(format!(
                "`{operand}` is a `Bool` in arithmetic in {context}; a `Bool` has no integer value: write `{operand} as int32`"
            )));
        }
    }
    Ok(())
}

/// `true` and `false` are `bool` values, so they compare only with `bool`
/// values. A value written alone as a proposition is the comparison
/// `value == true`, so this is also what refuses `requires count;` for an
/// integer `count`: Click does not read an integer as a truth value.
fn refuse_bool_literal_comparison(
    left: &ContractExpression,
    left_type: &SpecValueType,
    right: &ContractExpression,
    right_type: &SpecValueType,
    context: &str,
) -> Result<(), ClickError> {
    for (literal, other, other_type) in [(right, left, left_type), (left, right, right_type)] {
        let Some(literal) = crate::surface::bool_literal_value(literal) else {
            continue;
        };
        let other_type = match other_type {
            SpecValueType::Scalar(Some(InterfaceType::Bool)) => continue,
            SpecValueType::Scalar(Some(interface_type)) => describe_interface_type(*interface_type),
            SpecValueType::Scalar(None) => continue,
            other_type => describe_spec_value_type(other_type),
        };
        return Err(ClickError::new(format!(
            "`{}` has type {other_type}, not Bool, so it is not compared with `{literal}` and is \
             not a proposition on its own in {context}; write a comparison such as `{} != 0`",
            crate::surface::diagnostics::describe_contract_expression(other),
            crate::surface::diagnostics::describe_contract_expression(other),
        )));
    }
    Ok(())
}

pub(super) fn validate_to_nat_argument_type(
    argument: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    // C variables are present in this environment; Integer bindings are
    // resolved by the Integer lowerer. Contextual numerals inherit the
    // conversion's expected Integer type instead of selecting C arithmetic.
    let valid = match argument {
        ContractExpression::IntegerLiteral(_) => true,
        ContractExpression::Binding(name) => !variables.contains_key(name),
        ContractExpression::Negate(inner)
        | ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => {
            validate_to_nat_argument_type(inner, variables, click_functions, context)?;
            true
        }
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            validate_to_nat_argument_type(left, variables, click_functions, context)?;
            validate_to_nat_argument_type(right, variables, click_functions, context)?;
            true
        }
        _ => matches!(
            infer_spec_value_type(argument, variables, click_functions, context)?,
            SpecValueType::Integer
        ),
    };
    if valid {
        Ok(())
    } else {
        Err(ClickError::new(format!(
            "to_nat expects an Integer in {context}"
        )))
    }
}

fn return_type_needs_instantiation(click_type: &ClickType) -> bool {
    match click_type {
        ClickType::Proposition => false,
        ClickType::Resource => false,
        ClickType::Parameter(_) | ClickType::Program(InterfaceType::ParameterPointer(_)) => true,
        ClickType::Function { parameters, result } => {
            parameters.iter().any(return_type_needs_instantiation)
                || return_type_needs_instantiation(result)
        }
        ClickType::Algebraic(application) => application
            .arguments
            .iter()
            .any(return_type_needs_instantiation),
        ClickType::Program(_) | ClickType::CObjectPointer { .. } | ClickType::Integer => false,
    }
}

fn infer_spec_value_type(
    expression: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<SpecValueType, ClickError> {
    match expression {
        ContractExpression::IntegerContext(value) => infer_scoped_spec_value_type(
            value,
            variables,
            &BinderSet::new(),
            click_functions,
            context,
            true,
        ),

        ContractExpression::Binding(name)
            if !variables.contains_key(name)
                && callback_binding_type(name, click_functions).is_some() =>
        {
            Ok(SpecValueType::Function(
                callback_binding_type(name, click_functions).unwrap(),
            ))
        }

        ContractExpression::Proposition(_) => Ok(SpecValueType::Proposition),
        ContractExpression::Lambda {
            parameters, result, ..
        } => Ok(SpecValueType::Function(lambdas::signature(
            parameters, result,
        ))),
        ContractExpression::Apply { function, .. } => Ok(
            match match function.as_ref() {
                ContractExpression::Binding(name)
                    if callback_binding_type(name, click_functions).is_some() =>
                {
                    let ClickType::Function { result, .. } =
                        callback_binding_type(name, click_functions).unwrap()
                    else {
                        unreachable!()
                    };
                    *result
                }
                _ => lambdas::application_result_type(function).map_err(ClickError::new)?,
            } {
                ClickType::Proposition => SpecValueType::Proposition,
                ClickType::Integer => SpecValueType::Integer,
                ClickType::Program(ty)
                | ClickType::CObjectPointer {
                    interface_type: ty, ..
                } => SpecValueType::Scalar(Some(ty)),
                ClickType::Algebraic(ty) => SpecValueType::Algebraic(ty),
                ty @ ClickType::Function { .. } => SpecValueType::Function(ty),
                ClickType::Parameter(_) | ClickType::Resource => SpecValueType::Scalar(None),
            },
        ),

        ContractExpression::ResourceField(access)
            if access.click_type == Some(ClickType::Integer) =>
        {
            Ok(SpecValueType::Integer)
        }
        ContractExpression::ResourceField(access)
            if matches!(access.click_type, Some(ClickType::Algebraic(_))) =>
        {
            let Some(ClickType::Algebraic(application)) = &access.click_type else {
                unreachable!()
            };
            Ok(SpecValueType::Algebraic(application.clone()))
        }
        ContractExpression::AlgebraicVariable { algebraic_type, .. } => {
            Ok(SpecValueType::Algebraic(algebraic_type.clone()))
        }
        ContractExpression::AlgebraicConstructor { algebraic_type, .. } => {
            Ok(SpecValueType::Algebraic(algebraic_type.clone()))
        }
        ContractExpression::If {
            then_branch,
            else_branch,
            ..
        } => {
            let then_type =
                infer_spec_value_type(then_branch, variables, click_functions, context)?;
            let else_type =
                infer_spec_value_type(else_branch, variables, click_functions, context)?;
            match (then_type, else_type) {
                (SpecValueType::Algebraic(a), SpecValueType::Algebraic(b)) if a == b => {
                    Ok(SpecValueType::Algebraic(a))
                }
                (SpecValueType::Algebraic(_), _) | (_, SpecValueType::Algebraic(_)) => {
                    Err(ClickError::new(format!(
                        "conditional branches must have the same algebraic type in {context}"
                    )))
                }
                (SpecValueType::Scalar(a), SpecValueType::Scalar(b)) => {
                    Ok(SpecValueType::Scalar(match (a, b) {
                        (Some(a), Some(b)) if click_types_compatible(a, b) => Some(a),
                        (Some(_), Some(_)) => None,
                        (Some(ty), None) | (None, Some(ty)) => Some(ty),
                        (None, None) => None,
                    }))
                }
                (then_type, else_type) if then_type == else_type => Ok(then_type),
                (then_type, else_type) => Err(ClickError::new(format!(
                    "conditional branches have types {} and {} in {context}",
                    describe_spec_value_type(&then_type),
                    describe_spec_value_type(&else_type),
                ))),
            }
        }
        ContractExpression::AlgebraicMatch { arms, .. } => {
            if let Some(first) = arms.first()
                && let SpecValueType::Algebraic(application) =
                    infer_spec_value_type(&first.body, variables, click_functions, context)?
            {
                return Ok(SpecValueType::Algebraic(application));
            }
            Ok(SpecValueType::Scalar(infer_contract_expression_type(
                expression,
                variables,
                click_functions,
                context,
            )?))
        }
        ContractExpression::SequenceLiteral(elements) => {
            let mut element_type = None;
            for element in elements {
                let actual =
                    infer_contract_expression_type(element, variables, click_functions, context)?;
                if let Some(actual) = actual
                    && !sequence_element_type_supported(actual)
                {
                    return Err(ClickError::new(format!(
                        "{} is not a supported sequence element type in {context}",
                        describe_interface_type(actual)
                    )));
                }
                if let (Some(expected), Some(actual)) = (element_type, actual)
                    && actual != expected
                {
                    return Err(ClickError::new(format!(
                        "sequence literal mixes {} and {} elements in {context}",
                        describe_interface_type(expected),
                        describe_interface_type(actual)
                    )));
                }
                element_type = element_type.or(actual);
            }
            Ok(SpecValueType::Sequence(element_type))
        }
        ContractExpression::SequenceConcat(left, right) => {
            let SpecValueType::Sequence(left) =
                infer_spec_value_type(left, variables, click_functions, context)?
            else {
                return Err(ClickError::new(format!(
                    "left operand of `++` is not a sequence in {context}"
                )));
            };
            let SpecValueType::Sequence(right) =
                infer_spec_value_type(right, variables, click_functions, context)?
            else {
                return Err(ClickError::new(format!(
                    "right operand of `++` is not a sequence in {context}"
                )));
            };
            if let (Some(left), Some(right)) = (left, right)
                && left != right
            {
                return Err(ClickError::new(format!(
                    "`++` element types do not match in {context}: {} and {}",
                    describe_interface_type(left),
                    describe_interface_type(right)
                )));
            }
            Ok(SpecValueType::Sequence(left.or(right)))
        }
        ContractExpression::Old(inner)
        | ContractExpression::At {
            expression: inner, ..
        } => infer_spec_value_type(inner, variables, click_functions, context),
        expression @ ContractExpression::RangeFold { .. } => infer_scoped_spec_value_type(
            expression,
            variables,
            &BinderSet::new(),
            click_functions,
            context,
            false,
        ),
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            // Unsuffixed numeric syntax is deliberately kept untyped until
            // its surrounding spec expression supplies a context.  A typed
            // Integer let is one such context, including a theorem with no
            // Integer parameter at all.
            let mut value_type = if matches!(click_type, Some(ClickType::Integer))
                && is_untyped_integer_literal_expression(value)
            {
                SpecValueType::Integer
            } else {
                infer_spec_value_type(value, variables, click_functions, context)?
            };
            if let Some(expected) = click_type
                && !spec_value_matches_click_type(&value_type, expected)
                && let Some(narrow) = narrow_arithmetic_value_type(
                    value,
                    expected,
                    &format!("`let {name}`"),
                    &mut |leaf| infer_spec_value_type(leaf, variables, click_functions, context),
                )?
            {
                value_type = narrow;
            }
            if let Some(expected) = click_type
                && !spec_value_matches_click_type(&value_type, expected)
            {
                return Err(ClickError::new(format!(
                    "let binding `{name}` expects {}, got {} in {context}",
                    describe_click_type(expected),
                    describe_spec_value_type(&value_type)
                )));
            }
            let substituted = substitute_contract_expression(
                body,
                &BTreeMap::from([(name.clone(), value.as_ref().clone())]),
            )
            .map_err(ClickError::new)?;
            infer_spec_value_type(&substituted, variables, click_functions, context)
        }
        expression @ ContractExpression::Call { name, .. } if is_integer_truncation(name) => {
            infer_scoped_spec_value_type(
                expression,
                variables,
                &BinderSet::new(),
                click_functions,
                context,
                true,
            )
        }
        ContractExpression::Call { name, arguments } if name == "to_integer" => {
            let argument = integer_conversion_argument(name, arguments).map_err(ClickError::new)?;
            if let SpecValueType::Algebraic(application) =
                infer_spec_value_type(argument, variables, click_functions, context)?
            {
                if application.name() == "Nat" && application.arguments().is_empty() {
                    return Ok(SpecValueType::Integer);
                }
                return Err(ClickError::new(
                    "to_integer expects a machine integer or Nat",
                ));
            }
            if let Some(actual) =
                infer_contract_expression_type(argument, variables, click_functions, context)?
                && !machine_integer_source_type(actual)
            {
                return Err(ClickError::new(
                    "to_integer expects a signed or unsigned machine integer",
                ));
            }
            Ok(SpecValueType::Integer)
        }
        ContractExpression::Call { name, arguments } if name == "to_nat" => {
            let argument = integer_conversion_argument(name, arguments).map_err(ClickError::new)?;
            validate_to_nat_argument_type(argument, variables, click_functions, context)?;
            Ok(SpecValueType::Algebraic(
                AlgebraicTypeApplication::concrete("Nat"),
            ))
        }
        ContractExpression::Call { name, arguments } => {
            let Some(function) = click_functions.get(name) else {
                return Ok(SpecValueType::Scalar(infer_contract_expression_type(
                    expression,
                    variables,
                    click_functions,
                    context,
                )?));
            };
            // This pass determines the result's value category from C carrier
            // types. Generic argument consistency is checked with the full
            // logical types; do not repeat it after erasing struct tags when
            // the result does not depend on the substitution.
            let substitution = if function.type_parameters.is_empty()
                || !return_type_needs_instantiation(&function.return_type)
            {
                None
            } else {
                let actual_types = arguments
                    .iter()
                    .map(|argument| {
                        Ok(
                            match infer_spec_value_type(
                                argument,
                                variables,
                                click_functions,
                                context,
                            )? {
                                SpecValueType::Algebraic(application) => {
                                    Some(ClickType::Algebraic(application))
                                }
                                SpecValueType::Scalar(interface_type) => {
                                    interface_type.map(ClickType::Program)
                                }
                                SpecValueType::Integer => Some(ClickType::Integer),
                                SpecValueType::Sequence(_)
                                | SpecValueType::Function(_)
                                | SpecValueType::Proposition => None,
                            },
                        )
                    })
                    .collect::<Result<Vec<_>, ClickError>>()?;
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
            let return_type = substitution
                .as_ref()
                .map(|substitution| {
                    generics::instantiate_click_type(&function.return_type, substitution)
                        .map_err(ClickError::new)
                })
                .transpose()?
                .unwrap_or_else(|| function.return_type.clone());
            Ok(match return_type {
                ClickType::Proposition => SpecValueType::Proposition,
                ClickType::Resource => {
                    return Err(ClickError::new(
                        "Resource function results are not supported",
                    ));
                }
                ClickType::Algebraic(application) => SpecValueType::Algebraic(application),
                ClickType::Program(interface_type)
                | ClickType::CObjectPointer { interface_type, .. } => {
                    SpecValueType::Scalar(Some(interface_type))
                }
                ClickType::Integer => SpecValueType::Integer,
                ClickType::Function { .. } | ClickType::Parameter(_) => SpecValueType::Scalar(None),
            })
        }
        _ => Ok(SpecValueType::Scalar(infer_contract_expression_type(
            expression,
            variables,
            click_functions,
            context,
        )?)),
    }
}

fn is_untyped_integer_literal_expression(expression: &ContractExpression) -> bool {
    match expression {
        ContractExpression::IntegerLiteral(_) => true,
        ContractExpression::Negate(inner) => is_untyped_integer_literal_expression(inner),
        ContractExpression::Add(left, right)
        | ContractExpression::Subtract(left, right)
        | ContractExpression::Multiply(left, right) => {
            is_untyped_integer_literal_expression(left)
                && is_untyped_integer_literal_expression(right)
        }
        _ => false,
    }
}

fn sequence_element_type_supported(interface_type: InterfaceType) -> bool {
    !matches!(
        interface_type,
        InterfaceType::Void
            | InterfaceType::FunctionPointer(_)
            | InterfaceType::Int32Array(_)
            | InterfaceType::CharArray(_, _)
            | InterfaceType::UInt8Array(_)
            | InterfaceType::Int8Array(_)
            | InterfaceType::Int16Array(_)
            | InterfaceType::UInt16Array(_)
            | InterfaceType::UInt32Array(_)
            | InterfaceType::Int128Array(_)
            | InterfaceType::Int64Array(_, _)
            | InterfaceType::UInt128Array(_)
            | InterfaceType::UInt64Array(_, _)
            | InterfaceType::Float32Array(_)
            | InterfaceType::Float64Array(_)
    )
}

fn validate_resource_subject_expression_types(
    resource: &ResourceSubject,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceSubject::At { resource, .. } => validate_resource_subject_expression_types(
            resource,
            variables,
            click_functions,
            context,
        ),
        ResourceSubject::Emp => Ok(()),
        ResourceSubject::Star(left, right) => {
            validate_resource_subject_expression_types(left, variables, click_functions, context)?;
            validate_resource_subject_expression_types(right, variables, click_functions, context)
        }
        ResourceSubject::Footprint(_)
        | ResourceSubject::Parameter { .. }
        | ResourceSubject::Instance { .. }
        | ResourceSubject::Captured { .. } => Ok(()),
        ResourceSubject::Memory(segment) => {
            validate_contract_segment_expression_types(segment, variables, click_functions, context)
        }
        ResourceSubject::SavedMemory { base, start, end } => {
            for expression in [base, start].into_iter().chain(end.iter()) {
                infer_contract_expression_type(expression, variables, click_functions, context)?;
            }
            Ok(())
        }
        ResourceSubject::Declared {
            name,
            arguments,
            parameter_types,
            ..
        } => {
            for (index, argument) in arguments.iter().enumerate() {
                let actual =
                    infer_contract_expression_type(argument, variables, click_functions, context)?;
                if let (Some(actual), Some(expected)) = (actual, parameter_types.get(index))
                    && !resource_types_compatible(name, index, actual, *expected)
                    && !crate::surface::lowering::argument_is_null_pointer_constant(
                        argument, *expected,
                    )
                {
                    return Err(ClickError::new(resource_argument_type_message(
                        name, index, *expected, actual, context,
                    )));
                }
            }
            Ok(())
        }
    }
}

pub(super) fn validate_pure_theorem_proof(
    theorem_name: &str,
    proof: &SourceProof,
) -> Result<(), ClickError> {
    match proof {
        SourceProof::Default => Ok(()),
        SourceProof::Tactic(SmartTactic::ImplicitTail | SmartTactic::Solve) => Ok(()),
        SourceProof::Script(tactics) => validate_pure_theorem_tactics(theorem_name, tactics),
    }
}

fn validate_pure_theorem_tactics(
    theorem_name: &str,
    tactics: &[ProofTactic],
) -> Result<(), ClickError> {
    for tactic in tactics {
        match tactic {
            ProofTactic::Synthetic(inner) => {
                validate_pure_theorem_tactics(theorem_name, std::slice::from_ref(inner))?;
            }
            ProofTactic::UnfoldProposition(_)
            | ProofTactic::UnfoldFunction(_)
            | ProofTactic::Induct { .. }
            | ProofTactic::ApplyInduction { .. }
            | ProofTactic::ApplyInductionUsing { .. }
            | ProofTactic::ApplyFact(_)
            | ProofTactic::ApplyFactUsing { .. }
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::ApplyTheoremUsing { .. }
            | ProofTactic::CheckTerminationLocal(_)
            | ProofTactic::CheckTerminationComponent { .. }
            | ProofTactic::CheckTerminationCallbacks
            | ProofTactic::Known
            | ProofTactic::Normalize
            | ProofTactic::NormalizeUsing(_)
            | ProofTactic::ArithmeticUsing(_)
            | ProofTactic::Intro
            | ProofTactic::IntroAs(_)
            | ProofTactic::IntroBinder(_)
            | ProofTactic::Enumerate
            | ProofTactic::Contradiction(_)
            | ProofTactic::Preserve(_)
            | ProofTactic::Rewrite(_)
            | ProofTactic::Instantiate { .. }
            | ProofTactic::Witness(_)
            | ProofTactic::LetSatisfy(_)
            | ProofTactic::Choose(_)
            | ProofTactic::Solve
            | ProofTactic::ImplicitSolve
            // `transport(P, Q) using { ... }` names its source, its target,
            // and every premise, so it needs no state: the explicit facts
            // decide it. The smart `transport(P, Q)` form still does not
            // belong here, because it selects its premises from a fixed
            // state's ambient facts.
             |  ProofTactic::TransportUsing { .. }
             |  ProofTactic::SolveUsing(_) => {}
            ProofTactic::Match(proof_match) => {
                for arm in &proof_match.arms {
                    validate_pure_theorem_tactics(theorem_name, &arm.tactics)?;
                }
            }
            ProofTactic::If(proof_if) => {
                validate_pure_theorem_tactics(theorem_name, &proof_if.then_tactics)?;
                validate_pure_theorem_tactics(theorem_name, &proof_if.else_tactics)?;
            }
            ProofTactic::Both(both) => {
                validate_pure_theorem_tactics(theorem_name, &both.left_tactics)?;
                validate_pure_theorem_tactics(theorem_name, &both.right_tactics)?;
            }
            ProofTactic::Cases(proof_cases) => {
                for arm in proof_cases.arms() {
                    validate_pure_theorem_tactics(theorem_name, arm.tactics())?;
                }
            }
            ProofTactic::Have(proof_have) => {
                validate_pure_theorem_proof(theorem_name, &proof_have.proof)?;
            }
            ProofTactic::Branch(_)
            | ProofTactic::CallOutcomes(_)
            | ProofTactic::Loop(_)
            | ProofTactic::Open(_)
            | ProofTactic::Mark(_) => {
                return Err(ClickError::new(format!(
                    "execution tactic `{}` is not available in the pure proof for theorem `{theorem_name}`",
                    tactic_name(tactic)
                )));
            }
            ProofTactic::CloseInvariantsBy(_)
            | ProofTactic::CloseInvariants
            | ProofTactic::Step
            | ProofTactic::StepContract(_)
            | ProofTactic::StepBind(_)
            | ProofTactic::StepCall(_)
            | ProofTactic::StepProved { .. }
            | ProofTactic::UserTactic(_)
            | ProofTactic::SmartExecute
            | ProofTactic::ExecuteUntil(_)
            | ProofTactic::ObserveResource(_)
            | ProofTactic::ObserveSavedMemory { .. }
            | ProofTactic::Iterated(_)
            | ProofTactic::Transport { .. }
            | ProofTactic::UnfoldResource(_)
            | ProofTactic::UnfoldWitnesses { .. }
            | ProofTactic::FoldResource(_)
            | ProofTactic::ConstructResource(_)
            | ProofTactic::Sorry => {
                return Err(ClickError::new(format!(
                    "tactic `{}` is not available in the pure proof for theorem `{theorem_name}`",
                    tactic_name(tactic)
                )));
            }
        }
    }
    Ok(())
}

pub(in crate::surface) fn tactic_name(tactic: &ProofTactic) -> &'static str {
    match tactic {
        ProofTactic::ApplyFact(_) | ProofTactic::ApplyFactUsing { .. } => "apply",
        ProofTactic::Synthetic(inner) => tactic_name(inner),
        ProofTactic::Mark(_) => "mark",
        ProofTactic::Step
        | ProofTactic::StepBind(_)
        | ProofTactic::StepContract(_)
        | ProofTactic::StepCall(_)
        | ProofTactic::StepProved { .. } => "step",
        ProofTactic::UserTactic(_) => "tactic",
        ProofTactic::SmartExecute => "implicit tail",
        ProofTactic::ExecuteUntil(_) => "step_until",
        ProofTactic::UnfoldProposition(_)
        | ProofTactic::UnfoldFunction(_)
        | ProofTactic::UnfoldResource(_)
        | ProofTactic::UnfoldWitnesses { .. } => "unfold",
        ProofTactic::FoldResource(_) => "fold",
        ProofTactic::ConstructResource(_) => "construct",
        ProofTactic::Induct { .. } => "induct",
        ProofTactic::Match(_) => "match",
        ProofTactic::ApplyInduction { .. } => "apply",
        ProofTactic::ApplyInductionUsing { .. } => "apply",
        ProofTactic::ApplyTheorem(_) | ProofTactic::ApplyTheoremUsing { .. } => "apply",
        ProofTactic::Have(_) => "have",
        ProofTactic::Open(_) => "open",
        ProofTactic::If(_) => "if",
        ProofTactic::Cases(_) => "cases",
        ProofTactic::Both(_) => "both",
        ProofTactic::Branch(_) => "branch",
        ProofTactic::CallOutcomes(_) => "outcomes",
        ProofTactic::Loop(_) => "loop",
        ProofTactic::ObserveResource(_) | ProofTactic::ObserveSavedMemory { .. } => "observe",
        ProofTactic::Iterated(tactic) => tactic.name(),
        ProofTactic::Witness(_) => "witness",
        ProofTactic::LetSatisfy(_) => "obtain",
        ProofTactic::Sorry => "sorry",
        ProofTactic::Choose(_) => "choose",
        ProofTactic::CheckTerminationLocal(_) => "check_termination_local",
        ProofTactic::CheckTerminationComponent { .. } => "check_termination_component",
        ProofTactic::CheckTerminationCallbacks => "check_termination_callbacks",
        ProofTactic::Known => "known",
        ProofTactic::Normalize => "normalize",
        ProofTactic::NormalizeUsing(_) => "normalize",
        ProofTactic::ArithmeticUsing(_) => "arithmetic",
        ProofTactic::Intro | ProofTactic::IntroAs(_) | ProofTactic::IntroBinder(_) => "intro",
        ProofTactic::Enumerate => "enumerate",
        ProofTactic::Contradiction(_) => "contradiction",
        ProofTactic::CloseInvariants => "close_invariants",
        ProofTactic::CloseInvariantsBy(_) => "close_invariants",
        ProofTactic::Preserve(_) => "preserve",
        ProofTactic::Rewrite(_) => "rewrite",
        ProofTactic::Transport { .. } | ProofTactic::TransportUsing { .. } => "transport",
        ProofTactic::Instantiate { .. } => "instantiate",
        ProofTactic::Solve => "solve",
        ProofTactic::ImplicitSolve => "implicit tail",
        ProofTactic::SolveUsing(_) => "solve",
    }
}

pub(super) fn reject_duplicate_owned_declared_resource_clauses<'a>(
    _resources: impl IntoIterator<Item = &'a ResourceClause>,
    _context: &str,
) -> Result<(), ClickError> {
    // Declared resources are quantitative. Repeated owned clauses require or
    // provide repeated units; they are not malformed declarations. Raw memory
    // retains its separate overlap validity rules in the kernel algebra.
    Ok(())
}

pub(in crate::surface) fn describe_resource_clause(resource: &ResourceClause) -> String {
    match resource {
        ResourceClause::Conditional {
            condition,
            resource,
        } => format!(
            "if {} {{ {}; }}",
            crate::surface::diagnostics::describe_click_proposition(condition),
            describe_resource_clause(resource)
        ),
        ResourceClause::Named { binding, resource } => {
            format!("{}: {}", binding.name, describe_resource_clause(resource))
        }
        ResourceClause::Quantified { quantity, resource } => format!(
            "{} of {}",
            describe_contract_expression(quantity),
            describe_resource_clause(resource)
        ),
        ResourceClause::ViewMemory(segment) => format!(
            "views {}",
            crate::surface::diagnostics::describe_contract_segment(segment)
        ),
        ResourceClause::OwnMemory(segment) => format!(
            "owns {}",
            crate::surface::diagnostics::describe_contract_segment(segment)
        ),
        ResourceClause::MemoryAggregate { access, segments } => {
            let verb = match access {
                ResourceAccessMode::Own => "owns",
                ResourceAccessMode::View => "views",
            };
            format!(
                "{verb} aggregate {{{}}}",
                segments
                    .iter()
                    .map(describe_contract_segment)
                    .collect::<Vec<_>>()
                    .join(", ")
            )
        }
        ResourceClause::Declared {
            access,
            name,
            arguments,
            type_schema: _,
            resource_type_arguments,
            resource_arguments,
            ..
        } => {
            let resource = format!(
                "{name}({})",
                arguments
                    .iter()
                    .map(describe_contract_expression)
                    .chain(
                        resource_arguments
                            .iter()
                            .map(|reference| reference.name.clone())
                    )
                    .chain(resource_type_arguments.iter().map(describe_resource_clause))
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            match access {
                ResourceAccessMode::Own => resource,
                ResourceAccessMode::View => format!("view {resource}"),
            }
        }
        ResourceClause::Iterated(clause) => {
            crate::surface::lowering::describe_iterated_clause(clause)
        }
    }
}

/// The C spelling of a function-pointer type, read back from the kernel's
/// packed signature identity: a leading one, then the return type and each
/// parameter as a base-46 digit whose upper half marks a `const` pointee.
fn describe_callback_signature(signature: crate::kernel::CallbackSignature) -> String {
    const TYPES: [&str; 23] = [
        "void", "int32", "uint8", "uint32", "int32*", "uint8*", "int32**", "uint8**", "int16",
        "uint16", "int64", "uint64", "int16*", "uint16*", "uint32*", "int64*", "uint64*", "float",
        "double", "bool", "void*", "int8", "int8*",
    ];
    let Ok(mut encoded) = signature.to_string().parse::<u128>() else {
        return "a function pointer".to_string();
    };
    let throws = encoded & (1 << 79) != 0;
    encoded &= !(1 << 79);
    let mut digits = Vec::new();
    while encoded > 0 {
        digits.push((encoded % 46) as usize);
        encoded /= 46;
    }
    // The digits were pushed least significant first: the sentinel is last
    // and the return type is just before it.
    if digits.len() < 2 || digits.pop() != Some(1) {
        return "a function pointer of unspecified type".to_string();
    }
    let mut spelled = digits.into_iter().rev().map(|digit| {
        if digit >= 23 {
            format!("const {}", TYPES[digit - 23])
        } else {
            TYPES[digit].to_string()
        }
    });
    let return_type = spelled.next().unwrap_or_default();
    let parameters = spelled.collect::<Vec<_>>().join(", ");
    format!(
        "{return_type} (*)({parameters}){}",
        if throws { " throwing int32" } else { "" }
    )
}

pub(in crate::surface) fn describe_interface_type(interface_type: InterfaceType) -> String {
    match interface_type {
        InterfaceType::Parameter(name) => name.name().to_string(),
        InterfaceType::ParameterPointer(name) => format!("{}*", name.name()),
        InterfaceType::Int128 => "int128".to_string(),
        InterfaceType::UInt128 => "uint128".to_string(),

        // Click's logical sort (Stage 5); a head's own spelling is its
        // language's.
        InterfaceType::Bool => "Bool".to_string(),
        InterfaceType::Void => "void".to_string(),
        InterfaceType::VoidPointer => "void*".to_string(),
        InterfaceType::VoidPointerPointer => "void**".to_string(),
        InterfaceType::Int8 => "int8".to_string(),
        InterfaceType::Int16 => "int16".to_string(),
        InterfaceType::Int32 => "int32".to_string(),
        InterfaceType::Char(_) => "char".to_string(),
        InterfaceType::UInt8 => "uint8".to_string(),
        InterfaceType::UInt16 => "uint16".to_string(),
        InterfaceType::UInt32 => "uint32".to_string(),
        InterfaceType::Int64(_) => "int64".to_string(),
        InterfaceType::UInt64(_) => "uint64".to_string(),
        InterfaceType::Float32 => "float".to_string(),
        InterfaceType::Float64 => "double".to_string(),
        InterfaceType::Int8Pointer | InterfaceType::Int8Array(_) => "int8*".to_string(),
        InterfaceType::Int16Pointer | InterfaceType::Int16Array(_) => "int16*".to_string(),
        InterfaceType::UInt16Pointer | InterfaceType::UInt16Array(_) => "uint16*".to_string(),
        InterfaceType::Int32Pointer | InterfaceType::Int32Array(_) => "int32*".to_string(),
        InterfaceType::CharPointer(_) | InterfaceType::CharArray(_, _) => "char*".to_string(),
        InterfaceType::UInt8Pointer | InterfaceType::UInt8Array(_) => "uint8*".to_string(),
        InterfaceType::UInt32Pointer | InterfaceType::UInt32Array(_) => "uint32*".to_string(),
        InterfaceType::Int64Pointer(_) | InterfaceType::Int64Array(_, _) => "int64*".to_string(),
        InterfaceType::Int128Pointer | InterfaceType::Int128Array(_) => "int128*".to_string(),
        InterfaceType::UInt64Pointer(_) | InterfaceType::UInt64Array(_, _) => "uint64*".to_string(),
        InterfaceType::UInt128Pointer | InterfaceType::UInt128Array(_) => "uint128*".to_string(),
        InterfaceType::Float32Pointer | InterfaceType::Float32Array(_) => "float*".to_string(),
        InterfaceType::Float64Pointer | InterfaceType::Float64Array(_) => "double*".to_string(),
        InterfaceType::Int8PointerPointer => "int8**".to_string(),
        InterfaceType::Int16PointerPointer => "int16**".to_string(),
        InterfaceType::UInt16PointerPointer => "uint16**".to_string(),
        InterfaceType::Int32PointerPointer => "int32**".to_string(),
        InterfaceType::CharPointerPointer(_) => "char**".to_string(),
        InterfaceType::UInt8PointerPointer => "uint8**".to_string(),
        InterfaceType::UInt32PointerPointer => "uint32**".to_string(),
        InterfaceType::Int64PointerPointer(_) => "int64**".to_string(),
        InterfaceType::Int128PointerPointer => "int128**".to_string(),
        InterfaceType::UInt64PointerPointer(_) => "uint64**".to_string(),
        InterfaceType::UInt128PointerPointer => "uint128**".to_string(),
        InterfaceType::Float32PointerPointer => "float**".to_string(),
        InterfaceType::Float64PointerPointer => "double**".to_string(),
        InterfaceType::FunctionPointer(signature) => describe_callback_signature(signature),
        InterfaceType::PointerArray(element, _, length) => {
            format!("{}[{length}]", element.decayed_type_spelling())
        }
    }
}

pub(in crate::surface) fn describe_click_type(click_type: &ClickType) -> String {
    match click_type {
        ClickType::Proposition => "Prop".into(),
        ClickType::Resource => "Resource".into(),
        ClickType::Function { parameters, result } => format!(
            "fn({}) -> {}",
            parameters
                .iter()
                .map(describe_click_type)
                .collect::<Vec<_>>()
                .join(", "),
            describe_click_type(result)
        ),
        ClickType::Parameter(name) => name.clone(),
        ClickType::Program(interface_type) => describe_interface_type(*interface_type),
        ClickType::CObjectPointer {
            interface_type,
            struct_name,
        } => format!(
            "struct {struct_name}{}",
            "*".repeat(
                describe_interface_type(*interface_type)
                    .chars()
                    .filter(|ch| *ch == '*')
                    .count()
            )
        ),
        ClickType::Integer => "Integer".to_string(),
        ClickType::Algebraic(application) => {
            if application.arguments.is_empty() {
                application.name.clone()
            } else {
                format!(
                    "{}<{}>",
                    application.name,
                    application
                        .arguments
                        .iter()
                        .map(describe_click_type)
                        .collect::<Vec<_>>()
                        .join(", ")
                )
            }
        }
    }
}

/// Whether an array of `actual` elements may be passed where a predicate or
/// theorem reads `expected` elements: the same type, or two character types,
/// whose one-byte cells the kernel reads through either signedness as the
/// same eight bits.
pub(crate) fn array_ref_elements_compatible(
    actual: crate::kernel::ProgramType,
    expected: crate::kernel::ProgramType,
) -> bool {
    use crate::kernel::ProgramType;
    actual == expected
        || matches!(
            (actual, expected),
            (ProgramType::Int8, ProgramType::UInt8) | (ProgramType::UInt8, ProgramType::Int8)
        )
}

/// [`click_types_compatible`] for an argument of a predicate or pure
/// function, which also passes a signed character pointer as `uint8` bytes, so a
/// specification such as `string::readable(s)` reads a C string's bytes. Under
/// either signedness of `char` this reads the same objects: the kernel
/// lets a character type read a one-byte cell of the other signedness as the
/// same eight bits (C11 6.5p7), so `bytes[k] == '\0'` holds exactly when the
/// string's `char` is zero. C signatures keep the types distinct.
pub(in crate::surface) fn click_argument_types_compatible(
    actual: InterfaceType,
    expected: InterfaceType,
) -> bool {
    matches!(
        (actual, expected),
        (
            InterfaceType::CharPointer(_)
                | InterfaceType::CharArray(_, _)
                | InterfaceType::Int8Pointer
                | InterfaceType::Int8Array(_),
            InterfaceType::UInt8Pointer | InterfaceType::UInt8Array(_),
        )
    ) || click_types_compatible(actual, expected)
}

/// Whether a value of arithmetic type `actual` converts implicitly to
/// `expected` in Click syntax: exactly when every value of `actual` is a
/// value of `expected`, so the conversion never changes a value. Narrowing,
/// a change of sign and a float's integer part must be written. C source
/// keeps C's own conversions; this is the rule for Click's typed positions.
pub(in crate::surface) fn implicitly_converts(
    actual: InterfaceType,
    expected: InterfaceType,
) -> bool {
    use crate::kernel::{MachineIntegerType, ProgramType};
    let (actual, expected) = (actual.to_kernel_type(), expected.to_kernel_type());
    if actual == expected {
        return true;
    }
    let integer =
        |ty: ProgramType| MachineIntegerType::from_program_type(ty).map(MachineIntegerType::format);
    // A float holds an integer exactly when its significand covers the
    // integer's magnitude bits: 24 for `float`, 53 for `double`.
    let significand = |ty: ProgramType| match ty {
        ProgramType::Float32 => Some(24),
        ProgramType::Float64 => Some(53),
        _ => None,
    };
    match (integer(actual), integer(expected)) {
        (Some(from), Some(to)) => to.contains(from),
        (Some(from), None) => significand(expected)
            .is_some_and(|digits| from.bits() - u32::from(from.is_signed()) <= digits),
        (None, None) => actual == ProgramType::Float32 && expected == ProgramType::Float64,
        (None, Some(_)) => false,
    }
}

/// Whether `argument`, when it is an integer literal (negated or not), is a
/// value of the integer type `expected`; `None` for any other argument or
/// type. A literal takes its position's type when it holds its value, and
/// is refused rather than wrapped when it does not.
pub(in crate::surface) fn literal_fits(
    argument: &ContractExpression,
    expected: InterfaceType,
) -> Option<bool> {
    let text = match argument {
        ContractExpression::IntegerLiteral(text) => text.clone(),
        ContractExpression::Negate(inner) => match inner.as_ref() {
            ContractExpression::IntegerLiteral(text) => format!("-{text}"),
            _ => return None,
        },
        _ => return None,
    };
    let ty = crate::kernel::MachineIntegerType::from_program_type(expected.to_kernel_type())?;
    Some(crate::kernel::MachineIntegerConstant::parse_decimal(ty.format(), &text).is_some())
}

pub(in crate::surface) fn click_types_compatible(
    actual: InterfaceType,
    expected: InterfaceType,
) -> bool {
    match (actual, expected) {
        (InterfaceType::Int32Array(_), InterfaceType::Int32Pointer)
        | (InterfaceType::Int32Pointer, InterfaceType::Int32Array(_)) => true,
        (InterfaceType::Int8Array(_), InterfaceType::Int8Pointer)
        | (InterfaceType::Int8Pointer, InterfaceType::Int8Array(_)) => true,
        (InterfaceType::CharArray(left, _), InterfaceType::CharPointer(right))
        | (InterfaceType::CharPointer(left), InterfaceType::CharArray(right, _))
            if left == right =>
        {
            true
        }
        (InterfaceType::UInt8Array(_), InterfaceType::UInt8Pointer)
        | (InterfaceType::UInt8Pointer, InterfaceType::UInt8Array(_))
        | (InterfaceType::Int16Array(_), InterfaceType::Int16Pointer)
        | (InterfaceType::Int16Pointer, InterfaceType::Int16Array(_))
        | (InterfaceType::UInt16Array(_), InterfaceType::UInt16Pointer)
        | (InterfaceType::UInt16Pointer, InterfaceType::UInt16Array(_))
        | (InterfaceType::UInt32Array(_), InterfaceType::UInt32Pointer)
        | (InterfaceType::UInt32Pointer, InterfaceType::UInt32Array(_))
        | (InterfaceType::Int128Array(_), InterfaceType::Int128Pointer)
        | (InterfaceType::Int64Array(_, _), InterfaceType::Int64Pointer(_))
        | (InterfaceType::Int128Pointer, InterfaceType::Int128Array(_))
        | (InterfaceType::Int64Pointer(_), InterfaceType::Int64Array(_, _))
        | (InterfaceType::UInt128Array(_), InterfaceType::UInt128Pointer)
        | (InterfaceType::UInt64Array(_, _), InterfaceType::UInt64Pointer(_))
        | (InterfaceType::UInt128Pointer, InterfaceType::UInt128Array(_))
        | (InterfaceType::UInt64Pointer(_), InterfaceType::UInt64Array(_, _))
        | (InterfaceType::Float32Array(_), InterfaceType::Float32Pointer)
        | (InterfaceType::Float32Pointer, InterfaceType::Float32Array(_))
        | (InterfaceType::Float64Array(_), InterfaceType::Float64Pointer)
        | (InterfaceType::Float64Pointer, InterfaceType::Float64Array(_)) => true,
        (actual, InterfaceType::Bool) if actual.is_pointer() => true,
        (
            InterfaceType::Int8
            | InterfaceType::Int16
            | InterfaceType::Int32
            | InterfaceType::UInt8
            | InterfaceType::UInt16,
            InterfaceType::UInt32,
        ) => true,
        (actual, expected)
            if actual.is_object_pointer()
                && expected.is_object_pointer()
                && (actual == InterfaceType::VoidPointer
                    || expected == InterfaceType::VoidPointer) =>
        {
            true
        }
        (actual, expected) if type_is_arithmetic(actual) && type_is_arithmetic(expected) => {
            implicitly_converts(actual, expected)
        }
        _ => actual == expected,
    }
}

/// Whether `actual` may be passed for parameter `index` of resource `name`.
/// A resource argument follows the predicate rule,
/// [`click_argument_types_compatible`]: a character pointer is passed as
/// `uint8` bytes, so `cstr_at(s, n)` takes a C `char *s`.
/// A resource argument of the wrong type. The heap `allocation` size
/// names the two byte-count formats it takes.
fn resource_argument_type_message(
    name: &str,
    index: usize,
    expected: InterfaceType,
    actual: InterfaceType,
    context: &str,
) -> String {
    if name == ResourceFact::ALLOCATION_RESOURCE_NAME && index == 1 {
        return format!(
            "resource `{name}` argument {index} expects int32 or uint64, got {} in {context}: \
             the byte count is a heap block's size, a 32-bit `int32` or a 64-bit `uint64` \
             (`size_t`) one; a signed 64-bit size is stated through its `size_t` conversion, \
             such as `allocation(result, bytes as uint64)`",
            describe_interface_type(actual)
        );
    }
    format!(
        "resource `{name}` argument {index} expects {}, got {} in {context}",
        describe_interface_type(expected),
        describe_interface_type(actual)
    )
}

/// Argument 1 of `allocation` is the heap block's size: declared `int32`,
/// it also takes a 64-bit `uint64` (`size_t`) byte count, the size of a
/// block whose size is a symbolic `size_t` (`design/heap-allocation-sizes.md`, D4).
fn resource_types_compatible(
    name: &str,
    index: usize,
    actual: InterfaceType,
    expected: InterfaceType,
) -> bool {
    if name == ResourceFact::ALLOCATION_RESOURCE_NAME
        && index == 1
        && matches!(actual, InterfaceType::UInt64(_))
    {
        return true;
    }
    if name == ResourceFact::ALLOCATION_RESOURCE_NAME
        && index == 0
        && expected == InterfaceType::Int32Pointer
    {
        return matches!(
            actual,
            InterfaceType::Int8Pointer
                | InterfaceType::Int16Pointer
                | InterfaceType::UInt16Pointer
                | InterfaceType::Int32Pointer
                | InterfaceType::CharPointer(_)
                | InterfaceType::UInt8Pointer
                | InterfaceType::UInt32Pointer
                | InterfaceType::Int128Pointer
                | InterfaceType::Int64Pointer(_)
                | InterfaceType::UInt128Pointer
                | InterfaceType::UInt64Pointer(_)
                | InterfaceType::Int8PointerPointer
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
                | InterfaceType::Int32Array(_)
                | InterfaceType::CharArray(_, _)
                | InterfaceType::UInt8Array(_)
                | InterfaceType::Int8Array(_)
                | InterfaceType::Int16Array(_)
                | InterfaceType::UInt16Array(_)
                | InterfaceType::UInt32Array(_)
                | InterfaceType::Int128Array(_)
                | InterfaceType::Int64Array(_, _)
                | InterfaceType::UInt128Array(_)
                | InterfaceType::UInt64Array(_, _)
                | InterfaceType::Float32Array(_)
                | InterfaceType::Float64Array(_)
        );
    }
    click_argument_types_compatible(actual, expected)
}

pub(super) fn infer_contract_expression_type(
    expression: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<Option<InterfaceType>, ClickError> {
    if let Some(value_type) = deep_literal_add_type(expression) {
        return Ok(Some(value_type));
    }
    match expression {
        ContractExpression::IntegerContext(_) => Err(ClickError::new(
            "an Integer context is not a C scalar value",
        )),

        ContractExpression::Proposition(_) => {
            Err(ClickError::new("a Prop is not a C scalar value"))
        }
        ContractExpression::Resource(_) => {
            Err(ClickError::new("a Resource descriptor is not a C value"))
        }
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => Ok(None),
        ContractExpression::Lambda { .. } => Err(ClickError::new(
            "a specification lambda is not a scalar value",
        )),
        ContractExpression::Apply { function, .. } => {
            if let ContractExpression::Binding(name) = function.as_ref()
                && let Some(ClickType::Function { result, .. }) =
                    callback_binding_type(name, click_functions)
            {
                return Ok(result.interface_type());
            }
            Ok(lambdas::application_result_type(function)
                .map_err(ClickError::new)?
                .interface_type())
        }

        ContractExpression::ResourceField(access) => match &access.click_type {
            Some(ClickType::Program(ty)) => Ok(Some(*ty)),
            Some(ClickType::Integer) => Ok(None),
            _ => Err(ClickError::new("expected a scalar resource field")),
        },
        ContractExpression::IntegerLiteral(value) => {
            let value = value.parse::<u64>().map_err(|_| {
                ClickError::new(format!(
                    "arbitrary Integer literal `{value}` needs Integer context"
                ))
            })?;
            Ok(Some(if value <= i32::MAX as u64 {
                InterfaceType::Int32
            } else if value <= i64::MAX as u64 {
                InterfaceType::Int64(LongRank::Long)
            } else {
                InterfaceType::UInt64(LongRank::Long)
            }))
        }
        ContractExpression::Negate(inner) => {
            if let ContractExpression::IntegerLiteral(value) = inner.as_ref()
                && value
                    .parse::<u64>()
                    .is_ok_and(|value| value <= (i32::MAX as u64) + 1)
            {
                return Ok(Some(InterfaceType::Int32));
            }
            infer_contract_expression_type(inner, variables, click_functions, context)
        }
        ContractExpression::AlgebraicConstructor { .. }
        | ContractExpression::AlgebraicVariable { .. } => Err(ClickError::new(format!(
            "algebraic values are only valid in algebraic equality or as a `match` scrutinee in {context}"
        ))),
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            let ContractExpression::AlgebraicConstructor {
                variant, arguments, ..
            } = scrutinee.as_ref()
            else {
                return Ok(None);
            };
            let Some(arm) = arms.iter().find(|arm| &arm.variant == variant) else {
                return Ok(None);
            };
            let mut arm_variables = variables.clone();
            for (binding, argument) in arm.bindings.iter().zip(arguments) {
                if let Some(interface_type) =
                    infer_contract_expression_type(argument, variables, click_functions, context)?
                {
                    arm_variables.insert(binding.clone(), interface_type);
                }
            }
            infer_contract_expression_type(&arm.body, &arm_variables, click_functions, context)
        }
        ContractExpression::SequenceLiteral(_) | ContractExpression::SequenceConcat(_, _) => {
            Err(ClickError::new(format!(
                "sequence values are only valid as operands of `==` or `!=` in {context}"
            )))
        }
        ContractExpression::QualifiedC {
            lowered: expression,
            ..
        }
        | ContractExpression::CUnary {
            lowered: expression,
            ..
        }
        | ContractExpression::ProgramExpression(expression)
        | ContractExpression::Field {
            lowered: expression,
            ..
        } => {
            if !variables.contains_key("result")
                && program_expression_uses_variable(expression, "result")
            {
                return Err(ClickError::new(format!(
                    "`result` is not available in {context}"
                )));
            }
            validate_pointer_cast_operands(expression, variables, context)?;
            Ok(infer_program_expression_type(expression, variables))
        }
        ContractExpression::ArrayIndex { lowered, .. } => {
            if !variables.contains_key("result")
                && program_expression_uses_variable(lowered, "result")
            {
                return Err(ClickError::new(format!(
                    "`result` is not available in {context}"
                )));
            }
            Ok(infer_program_expression_type(lowered, variables))
        }
        ContractExpression::Binding(name) => Ok(variables.get(name).copied()),
        // C locals are resolved against the concrete program state during
        // lowering, not against the contract namespace used here. In
        // particular, `program::result` must not inherit the type of built-in
        // contract `result`.
        ContractExpression::ProgramBinding(_) => Ok(None),
        ContractExpression::ResourceCount(_) => Ok(Some(InterfaceType::Int32)),
        ContractExpression::ResourceWildcard => Err(ClickError::new(
            "`_` is only valid inside a `count(...)` resource pattern",
        )),
        ContractExpression::Old(expression) | ContractExpression::At { expression, .. } => {
            infer_contract_expression_type(expression, variables, click_functions, context)
        }
        ContractExpression::Add(left, right) => {
            infer_add_expression_type(left, right, variables, click_functions, context)
        }
        ContractExpression::Subtract(left, right) => {
            infer_subtract_expression_type(left, right, variables, click_functions, context)
        }
        ContractExpression::Multiply(left, right) | ContractExpression::Divide(left, right) => {
            let (left_expression, right_expression) = (left, right);
            let left = infer_contract_expression_type(left, variables, click_functions, context)?;
            let right = infer_contract_expression_type(right, variables, click_functions, context)?;
            refuse_bool_arithmetic_operands(
                [(left_expression, left), (right_expression, right)],
                context,
            )?;
            Ok(arithmetic_result_type(left, right))
        }
        ContractExpression::Remainder(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right) => {
            let (left_expression, right_expression) = (left, right);
            let left = infer_contract_expression_type(left, variables, click_functions, context)?;
            let right = infer_contract_expression_type(right, variables, click_functions, context)?;
            refuse_bool_arithmetic_operands(
                [(left_expression, left), (right_expression, right)],
                context,
            )?;
            Ok(match (left, right) {
                (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
                    Some(scalar_arithmetic_result_type(left, right))
                }
                _ => None,
            })
        }
        ContractExpression::ShiftLeft(left, right)
        | ContractExpression::RustShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right)
        | ContractExpression::RustShiftRight(left, right) => infer_contract_shift_type(
            left,
            right,
            variables,
            click_functions,
            context,
            matches!(
                expression,
                ContractExpression::RustShiftLeft(..) | ContractExpression::RustShiftRight(..)
            ),
        ),
        ContractExpression::BitwiseNot(expression) => {
            let operand = expression.as_ref();
            let expression =
                infer_contract_expression_type(expression, variables, click_functions, context)?;
            refuse_bool_arithmetic_operands(
                [(operand, expression), (operand, expression)],
                context,
            )?;
            Ok(expression
                .filter(|interface_type| type_is_scalar(*interface_type))
                .map(|interface_type| {
                    scalar_arithmetic_result_type(interface_type, interface_type)
                }))
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
                (Some(interface_type), None) | (None, Some(interface_type)) => Some(interface_type),
                (None, None) => None,
            })
        }
        expression @ ContractExpression::RangeFold { .. } => Ok(
            match infer_spec_value_type(expression, variables, click_functions, context)? {
                SpecValueType::Scalar(Some(interface_type)) => Some(interface_type),
                SpecValueType::Integer
                | SpecValueType::Scalar(None)
                | SpecValueType::Sequence(_)
                | SpecValueType::Function(_)
                | SpecValueType::Proposition
                | SpecValueType::Algebraic(_) => None,
            },
        ),
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            let mut value_type = infer_spec_value_type(value, variables, click_functions, context)?;
            if let Some(expected) = click_type
                && !spec_value_matches_click_type(&value_type, expected)
                && let Some(narrow) = narrow_arithmetic_value_type(
                    value,
                    expected,
                    &format!("`let {name}`"),
                    &mut |leaf| infer_spec_value_type(leaf, variables, click_functions, context),
                )?
            {
                value_type = narrow;
            }
            if let Some(expected) = click_type
                && !spec_value_matches_click_type(&value_type, expected)
            {
                return Err(ClickError::new(format!(
                    "let binding `{name}` expects {}, got {} in {context}",
                    describe_click_type(expected),
                    describe_spec_value_type(&value_type)
                )));
            }
            let substituted = substitute_contract_expression(
                body,
                &BTreeMap::from([(name.clone(), value.as_ref().clone())]),
            )
            .map_err(ClickError::new)?;
            infer_contract_expression_type(&substituted, variables, click_functions, context)
        }
        ContractExpression::MethodCall { method, .. } => Err(ClickError::new(format!(
            "{context}: the method `{method}` was not resolved by its receiver's type"
        ))),
        expression @ ContractExpression::Call { name, .. } if is_integer_truncation(name) => {
            infer_spec_value_type(expression, variables, click_functions, context)?;
            Ok(None)
        }
        ContractExpression::Call { name, arguments } if is_integer_conversion(name) => {
            let argument = integer_conversion_argument(name, arguments).map_err(ClickError::new)?;
            if name == "to_integer" {
                if let SpecValueType::Algebraic(application) =
                    infer_spec_value_type(argument, variables, click_functions, context)?
                {
                    return if application.name() == "Nat" && application.arguments().is_empty() {
                        Ok(None)
                    } else {
                        Err(ClickError::new(
                            "to_integer expects a machine integer or Nat",
                        ))
                    };
                }
                if let Some(actual) =
                    infer_contract_expression_type(argument, variables, click_functions, context)?
                    && !machine_integer_source_type(actual)
                {
                    return Err(ClickError::new(
                        "to_integer expects a signed or unsigned machine integer",
                    ));
                }
                Ok(None)
            } else {
                // Integer parameter names are deliberately absent from this C
                // environment. The Integer-aware validator and kernel lowerer
                // check the argument; this helper supplies the C result type.
                Ok(integer_conversion_target(name))
            }
        }
        ContractExpression::Call { name, arguments } => {
            let Some(function) = click_functions.get(name) else {
                return Ok(None);
            };
            for (index, (parameter, argument)) in
                function.parameters.iter().zip(arguments).enumerate()
            {
                let Some(expected) = parameter.click_type().interface_type() else {
                    continue;
                };
                // The C null pointer constant types as any pointer parameter,
                // in a pure function exactly as in a resource argument.
                if crate::surface::lowering::argument_is_null_pointer_constant(argument, expected) {
                    continue;
                }
                if let Some(actual) =
                    infer_contract_expression_type(argument, variables, click_functions, context)?
                    && !click_types_compatible(actual, expected)
                {
                    return Err(ClickError::new(format!(
                        "function `{name}` argument {index} expects {}, got {} in {context}",
                        describe_interface_type(expected),
                        describe_interface_type(actual)
                    )));
                }
            }
            // A generic function's result over its own type parameter,
            // `as_ptr<T>(s: Slice<T>) -> T*`, has a C type only at the
            // instance the arguments select, which the algebraic check
            // infers; its declared `T*` is no C type of the call.
            let return_type = function.return_type.interface_type();
            if let Some(InterfaceType::ParameterPointer(parameter)) = return_type
                && function
                    .type_parameters
                    .iter()
                    .any(|declared| declared == parameter.name())
            {
                return Ok(None);
            }
            Ok(return_type)
        }
    }
}

/// Struct casts recover the modeled object from an opaque `void *`.
/// Native byte-view casts retag scalar object pointers without changing
/// allocation identity, permissions, or initialized storage.
pub(in crate::surface) fn validate_void_pointer_cast_source(
    operand: &ProgramExpression,
    variables: &BinderMap<InterfaceType>,
    context: &str,
) -> Result<(), ClickError> {
    let actual = infer_program_expression_type(operand, variables);
    if actual.is_some_and(|ty| {
        !ty.is_object_pointer() && !matches!(ty, InterfaceType::Int64(_) | InterfaceType::UInt64(_))
    }) || matches!(operand, ProgramExpression::FunctionAddress(_))
    {
        return Err(ClickError::new(format!(
            "contract void-pointer cast in {context} expects an object pointer operand, got {actual:?}"
        )));
    }
    Ok(())
}

fn validate_pointer_cast_operands(
    expression: &ProgramExpression,
    variables: &BinderMap<InterfaceType>,
    context: &str,
) -> Result<(), ClickError> {
    match expression {
        ProgramExpression::Cast {
            expression: operand,
            target_type,
            pointee_struct,
            ..
        } => {
            if target_type.is_pointer() {
                if !matches!(target_type, ProgramType::FunctionPointer(_))
                    && matches!(
                        infer_program_expression_type(operand, variables),
                        Some(InterfaceType::Int64(_) | InterfaceType::UInt64(_))
                    )
                {
                    return validate_pointer_cast_operands(operand, variables, context);
                }
                if *target_type == ProgramType::VoidPointer {
                    validate_void_pointer_cast_source(operand, variables, context)?;
                    return validate_pointer_cast_operands(operand, variables, context);
                }
                if *target_type == ProgramType::UInt8Pointer && pointee_struct.is_none() {
                    let actual = infer_program_expression_type(operand, variables);
                    if actual.is_some()
                        && !actual.is_some_and(|ty| {
                            ty.to_kernel_type().pointee_type().is_some_and(|element| {
                                !element.is_pointer() && element.byte_width() > 0
                            })
                        })
                    {
                        return Err(ClickError::new(format!(
                            "native byte-view cast in {context} expects a scalar object pointer operand, got {actual:?}"
                        )));
                    }
                    return validate_pointer_cast_operands(operand, variables, context);
                }
                match infer_program_expression_type(operand, variables) {
                    None | Some(InterfaceType::VoidPointer) => {}
                    Some(actual) if actual.to_kernel_type() == *target_type => {}
                    Some(actual) => {
                        return Err(ClickError::new(format!(
                            "pointer cast in {context} expects a `void *` operand, got `{actual:?}`"
                        )));
                    }
                }
            }
            validate_pointer_cast_operands(operand, variables, context)
        }
        ProgramExpression::StringLiteral(_)
        | ProgramExpression::Value(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::Variable(_)
        | ProgramExpression::StepResult { .. } => Ok(()),
        ProgramExpression::Negate(inner)
        | ProgramExpression::FloatNegate(inner)
        | ProgramExpression::FloatClassification {
            expression: inner, ..
        }
        | ProgramExpression::AddressOf(inner)
        | ProgramExpression::CheckedObjectAddress(inner)
        | ProgramExpression::Not(inner)
        | ProgramExpression::BitwiseNot(inner)
        | ProgramExpression::Load(inner)
        | ProgramExpression::TypedLoad { pointer: inner, .. }
        | ProgramExpression::PointerOffsetBytes { pointer: inner, .. }
        | ProgramExpression::Subobject { pointer: inner, .. }
        | ProgramExpression::EnumField { value: inner, .. }
        | ProgramExpression::EnumIs { value: inner, .. } => {
            validate_pointer_cast_operands(inner, variables, context)
        }
        ProgramExpression::EnumConstruct { fields, .. } => fields
            .iter()
            .try_for_each(|field| validate_pointer_cast_operands(field, variables, context)),
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            validate_pointer_cast_operands(condition, variables, context)?;
            validate_pointer_cast_operands(then_branch, variables, context)?;
            validate_pointer_cast_operands(else_branch, variables, context)
        }
        crate::kernel::binary_c_expression!(left, right) => {
            validate_pointer_cast_operands(left, variables, context)?;
            validate_pointer_cast_operands(right, variables, context)
        }
    }
}

fn interface_type_from_program_type(target_type: &ProgramType) -> Option<InterfaceType> {
    match target_type {
        ProgramType::Parameter(name) => Some(InterfaceType::Parameter(*name)),
        ProgramType::ParameterPointer(name) => Some(InterfaceType::ParameterPointer(*name)),
        ProgramType::Int128 => Some(InterfaceType::Int128),
        ProgramType::UInt128 => Some(InterfaceType::UInt128),

        ProgramType::Bool => Some(InterfaceType::Bool),
        ProgramType::Int8 => Some(InterfaceType::Int8),
        ProgramType::Int16 => Some(InterfaceType::Int16),
        ProgramType::Int32 => Some(InterfaceType::Int32),
        ProgramType::UInt8 => Some(InterfaceType::UInt8),
        ProgramType::UInt16 => Some(InterfaceType::UInt16),
        ProgramType::UInt32 => Some(InterfaceType::UInt32),
        ProgramType::Int32Pointer => Some(InterfaceType::Int32Pointer),
        ProgramType::UInt8Pointer => Some(InterfaceType::UInt8Pointer),
        ProgramType::Int32PointerPointer => Some(InterfaceType::Int32PointerPointer),
        ProgramType::UInt8PointerPointer => Some(InterfaceType::UInt8PointerPointer),
        ProgramType::FunctionPointer(signature) => Some(InterfaceType::FunctionPointer(*signature)),
        ProgramType::Void | ProgramType::Int32Array(_) | ProgramType::UInt8Array(_) => None,
        ProgramType::Int64 => Some(InterfaceType::Int64(LongRank::Long)),
        ProgramType::UInt64 => Some(InterfaceType::UInt64(LongRank::Long)),
        ProgramType::Float32 => Some(InterfaceType::Float32),
        ProgramType::Float64 => Some(InterfaceType::Float64),
        ProgramType::VoidPointer => Some(InterfaceType::VoidPointer),
        ProgramType::VoidPointerPointer => Some(InterfaceType::VoidPointerPointer),
        ProgramType::Int8Pointer => Some(InterfaceType::Int8Pointer),
        ProgramType::Int16Pointer => Some(InterfaceType::Int16Pointer),
        ProgramType::UInt16Pointer => Some(InterfaceType::UInt16Pointer),
        ProgramType::UInt32Pointer => Some(InterfaceType::UInt32Pointer),
        ProgramType::Int64Pointer => Some(InterfaceType::Int64Pointer(LongRank::Long)),
        ProgramType::Int128Pointer => Some(InterfaceType::Int128Pointer),
        ProgramType::UInt64Pointer => Some(InterfaceType::UInt64Pointer(LongRank::Long)),
        ProgramType::UInt128Pointer => Some(InterfaceType::UInt128Pointer),
        ProgramType::Int8PointerPointer => Some(InterfaceType::Int8PointerPointer),
        ProgramType::Int16PointerPointer => Some(InterfaceType::Int16PointerPointer),
        ProgramType::UInt16PointerPointer => Some(InterfaceType::UInt16PointerPointer),
        ProgramType::UInt32PointerPointer => Some(InterfaceType::UInt32PointerPointer),
        ProgramType::Int64PointerPointer => {
            Some(InterfaceType::Int64PointerPointer(LongRank::Long))
        }
        ProgramType::Int128PointerPointer => Some(InterfaceType::Int128PointerPointer),
        ProgramType::UInt64PointerPointer => {
            Some(InterfaceType::UInt64PointerPointer(LongRank::Long))
        }
        ProgramType::UInt128PointerPointer => Some(InterfaceType::UInt128PointerPointer),
        ProgramType::Float32Pointer => Some(InterfaceType::Float32Pointer),
        ProgramType::Float64Pointer => Some(InterfaceType::Float64Pointer),
        ProgramType::Float32PointerPointer => Some(InterfaceType::Float32PointerPointer),
        ProgramType::Float64PointerPointer => Some(InterfaceType::Float64PointerPointer),
        ProgramType::Int8Array(_) => None,
        ProgramType::Int16Array(_)
        | ProgramType::UInt16Array(_)
        | ProgramType::UInt32Array(_)
        | ProgramType::Int128Array(_)
        | ProgramType::Int64Array(_)
        | ProgramType::UInt128Array(_)
        | ProgramType::UInt64Array(_)
        | ProgramType::Float32Array(_)
        | ProgramType::Float64Array(_)
        | ProgramType::PointerArray(_, _) => None,
    }
}

pub(in crate::surface) fn infer_program_expression_type(
    expression: &ProgramExpression,
    variables: &BinderMap<InterfaceType>,
) -> Option<InterfaceType> {
    match expression {
        ProgramExpression::Value(ProgramValue::PointerInteger(_)) => infer_program_expression_type(
            &ProgramExpression::Value(match expression {
                ProgramExpression::Value(v) => v.numeric_value().clone(),
                _ => unreachable!(),
            }),
            variables,
        ),
        ProgramExpression::Value(ProgramValue::Int128(_)) => Some(InterfaceType::Int128),
        ProgramExpression::Value(ProgramValue::UInt128(_)) => Some(InterfaceType::UInt128),

        ProgramExpression::Value(ProgramValue::Void) => Some(InterfaceType::Void),
        ProgramExpression::Value(ProgramValue::Bool(_)) => Some(InterfaceType::Bool),
        ProgramExpression::Value(ProgramValue::Int8(_)) => Some(InterfaceType::Int8),
        ProgramExpression::Value(ProgramValue::Int16(_)) => Some(InterfaceType::Int16),
        ProgramExpression::Value(ProgramValue::Int32(_)) => Some(InterfaceType::Int32),
        ProgramExpression::Value(ProgramValue::UInt8(_)) => Some(InterfaceType::UInt8),
        ProgramExpression::Value(ProgramValue::UInt16(_)) => Some(InterfaceType::UInt16),
        ProgramExpression::Value(ProgramValue::UInt32(_)) => Some(InterfaceType::UInt32),
        ProgramExpression::Value(ProgramValue::Int64(_)) => {
            Some(InterfaceType::Int64(LongRank::Long))
        }
        ProgramExpression::Value(ProgramValue::UInt64(_)) => {
            Some(InterfaceType::UInt64(LongRank::Long))
        }
        ProgramExpression::Value(ProgramValue::Float32(_)) => Some(InterfaceType::Float32),
        ProgramExpression::Value(ProgramValue::Float64(_)) => Some(InterfaceType::Float64),
        ProgramExpression::Value(ProgramValue::Parameter(term)) => Some(InterfaceType::Parameter(
            crate::kernel::TypeParameterName::of(&term.algebraic_type),
        )),
        ProgramExpression::Value(ProgramValue::Pointer(_)) => None,
        ProgramExpression::Variable(name) => match name {
            crate::kernel::BindingName::ReferenceCarrier(referent) => variables
                .get(name)
                .or_else(|| variables.get(referent.as_ref()))
                .copied(),
            crate::kernel::BindingName::Named(_) | crate::kernel::BindingName::Generated(_) => {
                variables.get(name).copied()
            }
            crate::kernel::BindingName::ContractResult => variables.get("result").copied(),
            crate::kernel::BindingName::ContractException => variables.get("exception").copied(),
            crate::kernel::BindingName::Local(_) | crate::kernel::BindingName::Static(_) => name
                .program_type()
                .and_then(|ty| interface_type_from_program_type(&ty)),
        },
        ProgramExpression::Cast {
            expression: _,
            target_type,
            ..
        } => interface_type_from_program_type(target_type),
        ProgramExpression::Ternary {
            condition,
            then_branch,
            else_branch,
        } => {
            let _ = infer_program_expression_type(condition, variables)?;
            let then_type = infer_program_expression_type(then_branch, variables);
            let else_type = infer_program_expression_type(else_branch, variables);
            match (then_type, else_type) {
                (Some(left), Some(right)) => arithmetic_result_type(Some(left), Some(right)),
                _ => None,
            }
        }
        ProgramExpression::EnumConstruct { enum_type, .. } => {
            Some(InterfaceType::Parameter(*enum_type))
        }
        // A field's type is its variant's declared field type.
        ProgramExpression::EnumField {
            value,
            variant,
            index,
        } => match infer_program_expression_type(value, variables)? {
            InterfaceType::Parameter(enum_type) => enum_type
                .algebraic_type()
                .variants
                .iter()
                .find(|declared| &declared.name == variant)
                .and_then(|declared| declared.fields.get(*index))
                .and_then(|field| match field {
                    crate::kernel::AlgebraicValueType::Program(interface_type) => Some(
                        crate::surface::generics::interface_type_from_program_type(*interface_type),
                    ),
                    _ => None,
                }),
            _ => None,
        },
        ProgramExpression::EnumIs { value, .. } => matches!(
            infer_program_expression_type(value, variables),
            Some(InterfaceType::Parameter(_))
        )
        .then_some(InterfaceType::Bool),
        ProgramExpression::Negate(expression) => arithmetic_result_type(
            Some(InterfaceType::Int32),
            infer_program_expression_type(expression, variables),
        ),
        ProgramExpression::FloatNegate(expression) => {
            infer_program_expression_type(expression, variables)
                .filter(|interface_type| type_is_float(*interface_type))
        }
        ProgramExpression::FloatClassification { expression, .. } => matches!(
            infer_program_expression_type(expression, variables),
            Some(InterfaceType::Float32 | InterfaceType::Float64)
        )
        .then_some(InterfaceType::Int32),
        ProgramExpression::AddressOf(_)
        | ProgramExpression::CheckedObjectAddress(_)
        | ProgramExpression::StringLiteral(_)
        | ProgramExpression::FunctionAddress(_)
        | ProgramExpression::StepResult { .. } => None,
        ProgramExpression::PointerOffsetBytes { pointer, .. }
        | ProgramExpression::Subobject { pointer, .. } => {
            infer_program_expression_type(pointer, variables)
        }
        ProgramExpression::LessThan(_, _)
        | ProgramExpression::LessEqual(_, _)
        | ProgramExpression::GreaterThan(_, _)
        | ProgramExpression::GreaterEqual(_, _)
        | ProgramExpression::Equal(_, _)
        | ProgramExpression::NotEqual(_, _)
        | ProgramExpression::Not(_)
        | ProgramExpression::And(_, _)
        | ProgramExpression::Or(_, _) => Some(InterfaceType::Int32),
        ProgramExpression::Add(left, right) => infer_c_add_type(left, right, variables),
        ProgramExpression::Subtract(left, right) => infer_c_subtract_type(left, right, variables),
        ProgramExpression::Multiply(left, right) | ProgramExpression::Divide(left, right) => {
            let left = infer_program_expression_type(left, variables);
            let right = infer_program_expression_type(right, variables);
            arithmetic_result_type(left, right)
        }
        ProgramExpression::Remainder(left, right)
        | ProgramExpression::BitwiseAnd(left, right)
        | ProgramExpression::BitwiseOr(left, right)
        | ProgramExpression::BitwiseXor(left, right) => {
            let left = infer_program_expression_type(left, variables);
            let right = infer_program_expression_type(right, variables);
            match (left, right) {
                (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
                    Some(scalar_arithmetic_result_type(left, right))
                }
                _ => None,
            }
        }
        ProgramExpression::ShiftLeft(left, right) | ProgramExpression::ShiftRight(left, right) => {
            infer_c_shift_type(left, right, variables)
        }
        ProgramExpression::RustShiftLeft(left, right)
        | ProgramExpression::RustShiftRight(left, right) => {
            let left = infer_program_expression_type(left, variables)?;
            let right = infer_program_expression_type(right, variables)?;
            (type_is_scalar(left) && type_is_scalar(right)).then_some(left)
        }
        ProgramExpression::BitwiseNot(expression) => {
            infer_program_expression_type(expression, variables)
                .filter(|interface_type| type_is_scalar(*interface_type))
                .map(|interface_type| scalar_arithmetic_result_type(interface_type, interface_type))
        }
        ProgramExpression::Load(pointer) => {
            infer_program_expression_type(pointer, variables).and_then(pointer_element_type)
        }
        ProgramExpression::TypedLoad { value_type, .. } => Some(match value_type {
            ProgramType::Parameter(name) => InterfaceType::Parameter(*name),
            ProgramType::ParameterPointer(name) => InterfaceType::ParameterPointer(*name),
            ProgramType::Void => return None,
            ProgramType::Bool => InterfaceType::Bool,
            ProgramType::VoidPointer => InterfaceType::VoidPointer,
            ProgramType::VoidPointerPointer => InterfaceType::VoidPointerPointer,
            ProgramType::Int8 => InterfaceType::Int8,
            ProgramType::Int16 => InterfaceType::Int16,
            ProgramType::Int32 => InterfaceType::Int32,
            ProgramType::UInt8 => InterfaceType::UInt8,
            ProgramType::UInt16 => InterfaceType::UInt16,
            ProgramType::UInt32 => InterfaceType::UInt32,
            ProgramType::Int64 => InterfaceType::Int64(LongRank::Long),
            ProgramType::UInt64 => InterfaceType::UInt64(LongRank::Long),
            ProgramType::Int128 => InterfaceType::Int128,
            ProgramType::UInt128 => InterfaceType::UInt128,
            ProgramType::Float32 => InterfaceType::Float32,
            ProgramType::Float64 => InterfaceType::Float64,
            ProgramType::Int32Pointer => InterfaceType::Int32Pointer,
            ProgramType::UInt8Pointer => InterfaceType::UInt8Pointer,
            ProgramType::Int8Pointer => InterfaceType::Int8Pointer,
            ProgramType::Int16Pointer => InterfaceType::Int16Pointer,
            ProgramType::UInt16Pointer => InterfaceType::UInt16Pointer,
            ProgramType::UInt32Pointer => InterfaceType::UInt32Pointer,
            ProgramType::Int64Pointer => InterfaceType::Int64Pointer(LongRank::Long),
            ProgramType::Int128Pointer => InterfaceType::Int128Pointer,
            ProgramType::UInt64Pointer => InterfaceType::UInt64Pointer(LongRank::Long),
            ProgramType::UInt128Pointer => InterfaceType::UInt128Pointer,
            ProgramType::Int8PointerPointer => InterfaceType::Int8PointerPointer,
            ProgramType::Int16PointerPointer => InterfaceType::Int16PointerPointer,
            ProgramType::UInt16PointerPointer => InterfaceType::UInt16PointerPointer,
            ProgramType::Int32PointerPointer => InterfaceType::Int32PointerPointer,
            ProgramType::UInt8PointerPointer => InterfaceType::UInt8PointerPointer,
            ProgramType::UInt32PointerPointer => InterfaceType::UInt32PointerPointer,
            ProgramType::Int64PointerPointer => InterfaceType::Int64PointerPointer(LongRank::Long),
            ProgramType::Int128PointerPointer => InterfaceType::Int128PointerPointer,
            ProgramType::UInt64PointerPointer => {
                InterfaceType::UInt64PointerPointer(LongRank::Long)
            }
            ProgramType::UInt128PointerPointer => InterfaceType::UInt128PointerPointer,
            ProgramType::Float32Pointer => InterfaceType::Float32Pointer,
            ProgramType::Float64Pointer => InterfaceType::Float64Pointer,
            ProgramType::Float32PointerPointer => InterfaceType::Float32PointerPointer,
            ProgramType::Float64PointerPointer => InterfaceType::Float64PointerPointer,
            ProgramType::FunctionPointer(signature) => InterfaceType::FunctionPointer(*signature),
            ProgramType::Int32Array(length) => InterfaceType::Int32Array(*length),
            ProgramType::UInt8Array(length) => InterfaceType::UInt8Array(*length),
            ProgramType::Int8Array(length) => InterfaceType::Int8Array(*length),
            ProgramType::Int16Array(length) => InterfaceType::Int16Array(*length),
            ProgramType::UInt16Array(length) => InterfaceType::UInt16Array(*length),
            ProgramType::UInt32Array(length) => InterfaceType::UInt32Array(*length),
            ProgramType::Int64Array(length) => InterfaceType::Int64Array(LongRank::Long, *length),
            ProgramType::Int128Array(length) => InterfaceType::Int128Array(*length),
            ProgramType::UInt64Array(length) => InterfaceType::UInt64Array(LongRank::Long, *length),
            ProgramType::UInt128Array(length) => InterfaceType::UInt128Array(*length),
            ProgramType::Float32Array(length) => InterfaceType::Float32Array(*length),
            ProgramType::Float64Array(length) => InterfaceType::Float64Array(*length),
            ProgramType::PointerArray(element, length) => {
                InterfaceType::PointerArray(*element, LongRank::Long, *length)
            }
        }),
        ProgramExpression::Index(base, _) => {
            infer_program_expression_type(base, variables).and_then(pointer_element_type)
        }
    }
}

fn infer_add_expression_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<Option<InterfaceType>, ClickError> {
    let (left_expression, right_expression) = (left, right);
    let left = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right = infer_contract_expression_type(right, variables, click_functions, context)?;
    refuse_bool_arithmetic_operands(
        [(left_expression, left), (right_expression, right)],
        context,
    )?;
    Ok(pointer_arithmetic_type(left, right).or_else(|| arithmetic_result_type(left, right)))
}

fn infer_subtract_expression_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<Option<InterfaceType>, ClickError> {
    let (left_expression, right_expression) = (left, right);
    let left = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right = infer_contract_expression_type(right, variables, click_functions, context)?;
    refuse_bool_arithmetic_operands(
        [(left_expression, left), (right_expression, right)],
        context,
    )?;
    Ok(match (left, right) {
        (Some(left), Some(right)) if type_is_data_pointer(left) && type_is_scalar(right) => {
            Some(left)
        }
        _ => arithmetic_result_type(left, right),
    })
}

fn infer_c_add_type(
    left: &ProgramExpression,
    right: &ProgramExpression,
    variables: &BinderMap<InterfaceType>,
) -> Option<InterfaceType> {
    let left = infer_program_expression_type(left, variables);
    let right = infer_program_expression_type(right, variables);
    pointer_arithmetic_type(left, right).or_else(|| arithmetic_result_type(left, right))
}

fn infer_c_subtract_type(
    left: &ProgramExpression,
    right: &ProgramExpression,
    variables: &BinderMap<InterfaceType>,
) -> Option<InterfaceType> {
    let left = infer_program_expression_type(left, variables);
    let right = infer_program_expression_type(right, variables);
    match (left, right) {
        (Some(left), Some(right)) if type_is_data_pointer(left) && type_is_scalar(right) => {
            Some(left)
        }
        _ => arithmetic_result_type(left, right),
    }
}

fn pointer_arithmetic_type(
    left: Option<InterfaceType>,
    right: Option<InterfaceType>,
) -> Option<InterfaceType> {
    match (left, right) {
        (Some(left), Some(right)) if type_is_data_pointer(left) && type_is_scalar(right) => {
            Some(left)
        }
        (Some(left), Some(right)) if type_is_scalar(left) && type_is_data_pointer(right) => {
            Some(right)
        }
        _ => None,
    }
}

fn type_is_float(interface_type: InterfaceType) -> bool {
    matches!(
        interface_type,
        InterfaceType::Float32 | InterfaceType::Float64
    )
}

fn arithmetic_result_type(
    left: Option<InterfaceType>,
    right: Option<InterfaceType>,
) -> Option<InterfaceType> {
    match (left, right) {
        (Some(left), Some(right)) if type_is_arithmetic(left) && type_is_arithmetic(right) => {
            if matches!(left, InterfaceType::Float64) || matches!(right, InterfaceType::Float64) {
                Some(InterfaceType::Float64)
            } else if matches!(left, InterfaceType::Float32)
                || matches!(right, InterfaceType::Float32)
            {
                Some(InterfaceType::Float32)
            } else {
                Some(scalar_arithmetic_result_type(left, right))
            }
        }
        _ => None,
    }
}

fn infer_c_shift_type(
    left: &ProgramExpression,
    right: &ProgramExpression,
    variables: &BinderMap<InterfaceType>,
) -> Option<InterfaceType> {
    let left_type = infer_program_expression_type(left, variables)?;
    let right_type = infer_program_expression_type(right, variables)?;
    if !type_is_scalar(left_type) || !type_is_scalar(right_type) {
        return None;
    }
    Some(match left_type {
        InterfaceType::UInt64(rank) => InterfaceType::UInt64(rank),
        InterfaceType::Int64(rank) => InterfaceType::Int64(rank),
        InterfaceType::UInt32 => InterfaceType::UInt32,
        _ => InterfaceType::Int32,
    })
}

fn infer_contract_shift_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
    retain_operand_width: bool,
) -> Result<Option<InterfaceType>, ClickError> {
    let left_type = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right_type = infer_contract_expression_type(right, variables, click_functions, context)?;
    Ok(contract_shift_result_type(
        left_type,
        right_type,
        retain_operand_width,
    ))
}

fn contract_shift_result_type(
    left_type: Option<InterfaceType>,
    right_type: Option<InterfaceType>,
    retain_operand_width: bool,
) -> Option<InterfaceType> {
    match (left_type, right_type) {
        (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
            if retain_operand_width {
                return Some(left);
            }
            Some(match left {
                InterfaceType::UInt64(rank) => InterfaceType::UInt64(rank),
                InterfaceType::Int64(rank) => InterfaceType::Int64(rank),
                InterfaceType::UInt32 => InterfaceType::UInt32,
                _ => InterfaceType::Int32,
            })
        }
        _ => None,
    }
}

fn type_is_scalar(interface_type: InterfaceType) -> bool {
    matches!(
        interface_type,
        InterfaceType::Bool
            | InterfaceType::Int8
            | InterfaceType::Int16
            | InterfaceType::Int32
            | InterfaceType::Char(_)
            | InterfaceType::UInt8
            | InterfaceType::UInt16
            | InterfaceType::UInt32
            | InterfaceType::Int64(_)
            | InterfaceType::UInt64(_)
    )
}

pub(super) fn type_is_arithmetic(interface_type: InterfaceType) -> bool {
    type_is_scalar(interface_type) || type_is_float(interface_type)
}

fn scalar_arithmetic_result_type(left: InterfaceType, right: InterfaceType) -> InterfaceType {
    if matches!(left, InterfaceType::UInt64(_)) || matches!(right, InterfaceType::UInt64(_)) {
        InterfaceType::UInt64(LongRank::Long)
    } else if matches!(left, InterfaceType::Int64(_)) || matches!(right, InterfaceType::Int64(_)) {
        InterfaceType::Int64(LongRank::Long)
    } else if matches!(left, InterfaceType::UInt32) || matches!(right, InterfaceType::UInt32) {
        InterfaceType::UInt32
    } else {
        InterfaceType::Int32
    }
}

fn type_is_data_pointer(interface_type: InterfaceType) -> bool {
    matches!(
        interface_type,
        InterfaceType::Int32Pointer
            | InterfaceType::Int8Pointer
            | InterfaceType::Int16Pointer
            | InterfaceType::CharPointer(_)
            | InterfaceType::UInt8Pointer
            | InterfaceType::UInt16Pointer
            | InterfaceType::UInt32Pointer
            | InterfaceType::Int128Pointer
            | InterfaceType::Int64Pointer(_)
            | InterfaceType::UInt128Pointer
            | InterfaceType::UInt64Pointer(_)
            | InterfaceType::Int8PointerPointer
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
            | InterfaceType::Int32Array(_)
            | InterfaceType::CharArray(_, _)
            | InterfaceType::UInt8Array(_)
            | InterfaceType::Int8Array(_)
            | InterfaceType::Int16Array(_)
            | InterfaceType::UInt16Array(_)
            | InterfaceType::UInt32Array(_)
            | InterfaceType::Int128Array(_)
            | InterfaceType::Int64Array(_, _)
            | InterfaceType::UInt128Array(_)
            | InterfaceType::UInt64Array(_, _)
    )
}

fn pointer_element_type(interface_type: InterfaceType) -> Option<InterfaceType> {
    interface_type.pointee_type()
}

fn validate_contract_segment_expression_types(
    segment: &ContractSegment,
    variables: &BinderMap<InterfaceType>,
    click_functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let _ = infer_contract_expression_type(
        &ContractExpression::ProgramExpression(segment.base.clone()),
        variables,
        click_functions,
        context,
    )?;
    let _ = infer_contract_expression_type(
        &ContractExpression::ProgramExpression(segment.start.clone()),
        variables,
        click_functions,
        context,
    )?;
    let _ = infer_contract_expression_type(
        &ContractExpression::ProgramExpression(segment.end.clone()),
        variables,
        click_functions,
        context,
    )?;
    Ok(())
}

pub(super) fn validate_resource_clause(
    resource: &ResourceClause,
    resources: &BTreeMap<String, usize>,
    recursive_resources: &BTreeSet<String>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BinderMap<ClickFunctionType>,
    variables: &BinderMap<InterfaceType>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceClause::Conditional {
            condition,
            resource,
        } => {
            validate_proposition_expression_types(
                condition,
                variables,
                click_function_types,
                context,
            )?;
            validate_resource_clause(
                resource,
                resources,
                recursive_resources,
                click_functions,
                click_function_types,
                variables,
                context,
            )
        }
        ResourceClause::Named { resource, .. } => validate_resource_clause(
            resource,
            resources,
            recursive_resources,
            click_functions,
            click_function_types,
            variables,
            context,
        ),
        ResourceClause::ViewMemory(_) | ResourceClause::OwnMemory(_) => Ok(()),
        ResourceClause::MemoryAggregate { .. } => Ok(()),
        // The index binder is in scope only inside the clause; the resource
        // definition validation checks the clause with it bound.
        ResourceClause::Iterated(_) => Ok(()),
        ResourceClause::Quantified { quantity, resource } => {
            validate_contract_expression_calls(quantity, click_functions, context)?;
            let actual =
                infer_contract_expression_type(quantity, variables, click_function_types, context)?;
            if actual != Some(InterfaceType::Int32) {
                return Err(ClickError::new(format!(
                    "declared resource quantity must have type int32 in {context}"
                )));
            }
            if !matches!(
                resource.as_ref(),
                ResourceClause::Declared {
                    access: ResourceAccessMode::Own,
                    name,
                    ..
                } if name != ResourceFact::ALLOCATION_RESOURCE_NAME
            ) {
                return Err(ClickError::new(format!(
                    "symbolic quantities require an owned user-declared resource in {context}"
                )));
            }
            if let ResourceClause::Declared { name, .. } = resource.as_ref()
                && recursive_resources.contains(name)
            {
                return Err(ClickError::new(format!(
                    "symbolic quantities for recursive composite resource `{name}` are not supported in {context}"
                )));
            }
            validate_resource_clause(
                resource,
                resources,
                recursive_resources,
                click_functions,
                click_function_types,
                variables,
                context,
            )
        }
        ResourceClause::Declared {
            name,
            arguments,
            parameter_types,
            type_schema: _,
            resource_type_arguments,
            resource_arguments,
            ..
        } => {
            for resource in resource_type_arguments {
                validate_resource_clause(
                    resource,
                    resources,
                    recursive_resources,
                    click_functions,
                    click_function_types,
                    variables,
                    context,
                )?;
            }
            let Some(arity) = resources.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown resource `{name}` in {context}{}",
                    crate::surface::validation::library_import_hint(name)
                )));
            };
            if *arity != arguments.len() + resource_arguments.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` expects {arity} argument(s), got {} in {context}",
                    arguments.len() + resource_arguments.len()
                )));
            }
            if parameter_types.len() != arguments.len() {
                return Err(ClickError::new(format!(
                    "resource `{name}` has malformed argument type metadata in {context}"
                )));
            }
            for (index, argument) in arguments.iter().enumerate() {
                // Declaration expansion permits wildcards only in a checked
                // authority pattern; they are not evaluated value arguments.
                if matches!(argument, ContractExpression::ResourceWildcard) {
                    continue;
                }
                validate_contract_expression_calls(argument, click_functions, context)?;
                if let Some(actual) = infer_contract_expression_type(
                    argument,
                    variables,
                    click_function_types,
                    context,
                )? {
                    let expected = parameter_types[index];
                    if !resource_types_compatible(name, index, actual, expected)
                        && !crate::surface::lowering::argument_is_null_pointer_constant(
                            argument, expected,
                        )
                    {
                        return Err(ClickError::new(resource_argument_type_message(
                            name, index, expected, actual, context,
                        )));
                    }
                }
            }
            Ok(())
        }
    }
}

pub(super) fn validate_predicate_calls_in_proposition(
    proposition: &ClickProposition,
    predicates: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    let mut pending = vec![proposition];
    while let Some(proposition) = pending.pop() {
        match proposition {
            ClickProposition::And(left, right)
            | ClickProposition::Or(left, right)
            | ClickProposition::Implies(left, right) => {
                pending.push(right);
                pending.push(left);
            }
            proposition => {
                validate_predicate_calls_in_proposition_one(
                    proposition,
                    predicates,
                    click_functions,
                    context,
                )?;
            }
        }
    }
    Ok(())
}

fn validate_predicate_calls_in_proposition_one(
    proposition: &ClickProposition,
    predicates: &BTreeMap<String, usize>,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Value(expression) => {
            validate_contract_expression_calls(expression, click_functions, context)
        }

        ClickProposition::Comparison { left, right, .. } => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ClickProposition::FloatClassification { expression, .. } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ClickProposition::Separate { left, right } => {
            validate_resource_subject_calls(left, click_functions, context)?;
            validate_resource_subject_calls(right, click_functions, context)
        }
        ClickProposition::ResourceViewable { resource } => {
            validate_resource_subject_calls(resource, click_functions, context)
        }
        ClickProposition::Contains { parent, child } => {
            validate_resource_subject_calls(parent, click_functions, context)?;
            validate_resource_subject_calls(child, click_functions, context)
        }
        ClickProposition::Loadable { segment } => {
            validate_contract_segment_calls(segment, click_functions, context)
        }
        ClickProposition::Defined { expression } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_predicate_calls_in_proposition(left, predicates, click_functions, context)?;
            validate_predicate_calls_in_proposition(right, predicates, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        }
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
            if name == "held" {
                if arguments.len() != 1 {
                    return Err(ClickError::new(format!(
                        "held expects one mutex pointer in {context}, got {}",
                        arguments.len()
                    )));
                }
                return validate_contract_expression_calls(&arguments[0], click_functions, context);
            }
            if name == "little_endian" {
                return if arguments.is_empty() {
                    Ok(())
                } else {
                    Err(ClickError::new("little_endian expects no arguments"))
                };
            }
            if name == "same_object" {
                if arguments.len() != 2 {
                    return Err(ClickError::new(format!(
                        "same_object expects two pointer arguments in {context}, got {}",
                        arguments.len()
                    )));
                }
                for argument in arguments {
                    validate_contract_expression_calls(argument, click_functions, context)?;
                }
                return Ok(());
            }
            let Some(arity) = predicates.get(name) else {
                return Err(ClickError::new(format!(
                    "unknown predicate `{name}` in {context}{}",
                    crate::surface::validation::library_import_hint(name)
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

pub(super) fn validate_program_valued_function_folds(
    definition: &ClickFunctionDefinition,
    click_functions: &BinderMap<ClickFunctionType>,
) -> Result<(), ClickError> {
    let Some(body) = definition.body() else {
        return Ok(());
    };
    if !matches!(definition.return_type(), ClickType::Program(_))
        || !contains_scoped_expression_shape(body, ScopedExpressionShape::RangeFold)
    {
        return Ok(());
    }
    let variables = definition
        .parameters()
        .iter()
        .filter_map(|parameter| {
            parameter
                .click_type()
                .interface_type()
                .map(|ty| (parameter.name().to_string(), ty))
        })
        .collect();
    let integer_bindings = definition
        .parameters()
        .iter()
        .filter(|parameter| *parameter.click_type() == ClickType::Integer)
        .map(|parameter| parameter.name().to_string())
        .collect();
    infer_scoped_spec_value_type(
        body,
        &variables,
        &integer_bindings,
        click_functions,
        &format!("function `{}`", definition.name()),
        false,
    )?;
    Ok(())
}

pub(super) fn validate_click_function_expression(
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
        &ContractExpression::ProgramExpression(segment.base.clone()),
        click_functions,
        context,
    )?;
    validate_contract_expression_calls(
        &ContractExpression::ProgramExpression(segment.start.clone()),
        click_functions,
        context,
    )?;
    validate_contract_expression_calls(
        &ContractExpression::ProgramExpression(segment.end.clone()),
        click_functions,
        context,
    )
}

fn validate_contract_expression_calls(
    expression: &ContractExpression,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    if deep_literal_add_type(expression).is_some() {
        return Ok(());
    }
    if let ContractExpression::Apply {
        function,
        arguments,
    } = expression
        && matches!(function.as_ref(), ContractExpression::Binding(_))
    {
        for argument in arguments {
            validate_contract_expression_calls(argument, click_functions, context)?;
        }
        return Ok(());
    }
    if let Some(reduced) = lambdas::reduce_head(expression).map_err(ClickError::new)? {
        if let ContractExpression::Let { value, .. } = expression {
            validate_contract_expression_calls(value, click_functions, context)?;
        }
        return validate_contract_expression_calls(&reduced, click_functions, context);
    }
    match expression {
        ContractExpression::IntegerContext(value) => {
            validate_contract_expression_calls(value, click_functions, context)
        }

        ContractExpression::Proposition(proposition) => {
            validate_value_proposition_calls(proposition, click_functions, context, true)
        }
        ContractExpression::Resource(subject) => {
            validate_resource_subject_calls(subject, click_functions, context)
        }
        ContractExpression::RegionResult(_)
        | ContractExpression::RegionAllocation(_)
        | ContractExpression::RegionParameter { .. } => Ok(()),
        ContractExpression::Lambda { body, .. } => {
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::Apply { .. } => {
            Err(ClickError::new("application needs a concrete lambda"))
        }

        ContractExpression::IntegerLiteral(_) => Ok(()),
        ContractExpression::CUnary { operand: inner, .. } | ContractExpression::Negate(inner) => {
            validate_contract_expression_calls(inner, click_functions, context)
        }
        ContractExpression::ResourceField(_)
        | ContractExpression::AlgebraicVariable { .. }
        | ContractExpression::Binding(_) => Ok(()),
        ContractExpression::AlgebraicConstructor { arguments, .. } => {
            for argument in arguments {
                validate_contract_expression_calls(argument, click_functions, context)?;
            }
            Ok(())
        }
        ContractExpression::AlgebraicMatch { scrutinee, arms } => {
            validate_contract_expression_calls(scrutinee, click_functions, context)?;
            for arm in arms {
                validate_contract_expression_calls(&arm.body, click_functions, context)?;
            }
            Ok(())
        }
        ContractExpression::SequenceLiteral(elements) => {
            for element in elements {
                validate_contract_expression_calls(element, click_functions, context)?;
            }
            Ok(())
        }
        ContractExpression::SequenceConcat(left, right) => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ContractExpression::QualifiedC { .. }
        | ContractExpression::ProgramExpression(_)
        | ContractExpression::ProgramBinding(_) => Ok(()),
        ContractExpression::ResourceCount(resource) => match resource.as_ref() {
            ResourceClause::Declared { arguments, .. } => {
                for argument in arguments {
                    if !matches!(argument, ContractExpression::ResourceWildcard) {
                        validate_contract_expression_calls(argument, click_functions, context)?;
                    }
                }
                Ok(())
            }
            _ => Err(ClickError::new("`count(...)` expects a declared resource")),
        },
        ContractExpression::ResourceWildcard => Err(ClickError::new(
            "`_` is only valid inside a `count(...)` resource pattern",
        )),
        ContractExpression::Field { base, .. } => {
            validate_contract_expression_calls(base, click_functions, context)
        }
        ContractExpression::ArrayIndex { base, .. } => {
            validate_contract_expression_calls(base, click_functions, context)?;
            Ok(())
        }
        ContractExpression::Old(body) => {
            validate_contract_expression_calls(body, click_functions, context)
        }
        ContractExpression::At { expression, .. } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        crate::surface::binary_contract_expression!(left, right) => {
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
        ContractExpression::MethodCall { method, .. } => Err(ClickError::new(format!(
            "the method `{method}` was not resolved by its receiver's type"
        ))),
        ContractExpression::Call { name, arguments } => {
            let builtin_arity = if is_integer_truncation(name) {
                Some(2)
            } else {
                (is_integer_conversion(name) || name == "to_nat").then_some(1)
            };
            let Some(arity) = builtin_arity.as_ref().or_else(|| click_functions.get(name)) else {
                return Err(ClickError::new(format!(
                    "unknown function `{name}` in {context}{}",
                    crate::surface::validation::library_import_hint(name)
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

fn validate_resource_subject_calls(
    resource: &ResourceSubject,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceSubject::At { resource, .. } => {
            validate_resource_subject_calls(resource, click_functions, context)
        }
        ResourceSubject::Emp => Ok(()),
        ResourceSubject::Star(left, right) => {
            validate_resource_subject_calls(left, click_functions, context)?;
            validate_resource_subject_calls(right, click_functions, context)
        }
        ResourceSubject::Footprint(_)
        | ResourceSubject::Parameter { .. }
        | ResourceSubject::Instance { .. }
        | ResourceSubject::Captured { .. } => Ok(()),
        ResourceSubject::Memory(segment) => {
            validate_contract_segment_calls(segment, click_functions, context)
        }
        ResourceSubject::SavedMemory { base, start, end } => {
            for argument in [base, start].into_iter().chain(end.iter()) {
                validate_contract_expression_calls(argument, click_functions, context)?;
            }
            Ok(())
        }
        ResourceSubject::Declared { arguments, .. } => {
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
    validate_value_proposition_calls(proposition, click_functions, context, false)
}

fn validate_value_proposition_calls(
    proposition: &ClickProposition,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
    allow_predicates: bool,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Value(expression) => {
            validate_contract_expression_calls(expression, click_functions, context)
        }

        ClickProposition::Comparison { left, right, .. } => {
            validate_contract_expression_calls(left, click_functions, context)?;
            validate_contract_expression_calls(right, click_functions, context)
        }
        ClickProposition::FloatClassification { expression, .. } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ClickProposition::Separate { left, right } => {
            validate_resource_subject_calls(left, click_functions, context)?;
            validate_resource_subject_calls(right, click_functions, context)
        }
        ClickProposition::ResourceViewable { resource } => {
            validate_resource_subject_calls(resource, click_functions, context)
        }
        ClickProposition::Contains { parent, child } => {
            validate_resource_subject_calls(parent, click_functions, context)?;
            validate_resource_subject_calls(child, click_functions, context)
        }
        ClickProposition::Loadable { segment } => {
            validate_contract_segment_calls(segment, click_functions, context)
        }
        ClickProposition::Defined { expression } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ClickProposition::And(left, right)
        | ClickProposition::Or(left, right)
        | ClickProposition::Implies(left, right) => {
            validate_value_proposition_calls(left, click_functions, context, allow_predicates)?;
            validate_value_proposition_calls(right, click_functions, context, allow_predicates)
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        }
        | ClickProposition::ForAll { body, .. }
        | ClickProposition::Exists { body, .. } => {
            validate_value_proposition_calls(body, click_functions, context, allow_predicates)
        }
        ClickProposition::RangeAll {
            start, end, body, ..
        }
        | ClickProposition::RangeAny {
            start, end, body, ..
        } => {
            validate_contract_expression_calls(start, click_functions, context)?;
            validate_contract_expression_calls(end, click_functions, context)?;
            validate_value_proposition_calls(body, click_functions, context, allow_predicates)
        }
        ClickProposition::PredicateCall { arguments, .. } if allow_predicates => {
            for argument in arguments {
                validate_contract_expression_calls(argument, click_functions, context)?;
            }
            Ok(())
        }
        ClickProposition::PredicateCall { name, .. } => Err(ClickError::new(format!(
            "predicate call `{name}` is not supported in `if` expression condition in {context}"
        ))),
    }
}

/// Retained declaration aliases must be typed even when no clause uses them.
/// Check their lexical value expression once, rather than once per clause.
pub(super) fn validate_declaration_lambda_bindings(
    ensures: &[EnsureClause],
    variables: &BinderMap<InterfaceType>,
    integer_bindings: &BinderSet,
    functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let Some(last) = ensures.last() else {
        return Ok(());
    };
    // Contract lets accumulate in source order; the last clause retains all
    // earlier aliases. Non-lambda declarations keep their existing checking.
    if !last
        .proof_bindings
        .iter()
        .any(|(_, _, value)| contains_scoped_expression_shape(value, ScopedExpressionShape::Lambda))
    {
        return Ok(());
    }
    let mut expression = ContractExpression::IntegerLiteral("0".into());
    for (name, click_type, value) in last.proof_bindings.iter().rev() {
        expression = ContractExpression::Let {
            name: name.clone().into(),
            click_type: click_type.clone(),
            value: Box::new(value.clone()),
            body: Box::new(expression),
        };
    }
    infer_scoped_spec_value_type(
        &expression,
        variables,
        integer_bindings,
        functions,
        context,
        false,
    )?;
    Ok(())
}

/// Check a lambda using only names mentioned by its body, never copying an
/// unrelated ambient typing environment. Reads are typed here; application
/// lowering checks their guards in the selected program state.
fn validate_lambda_value(
    parameters: &[(SurfaceBinder, ClickType)],
    result: &ClickType,
    body: &ContractExpression,
    variables: &BinderMap<InterfaceType>,
    integer_bindings: &BinderSet,
    functions: &BinderMap<ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let supported = |ty: &ClickType| {
        *ty == ClickType::Integer
            || ty
                .interface_type()
                .is_some_and(|ty| type_is_arithmetic(ty) && ty != InterfaceType::Void)
    };
    if (!supported(result) && *result != ClickType::Proposition)
        || parameters.iter().any(|(_, ty)| !supported(ty))
    {
        return Err(ClickError::new(
            "lambda parameters and results currently require Integer or C scalar types",
        ));
    }
    lambdas::validate_body_state(body)?;
    let mut names = BinderSet::new();
    collect_contract_expression_referenced_binders(body, &mut names);
    let mut local_variables = BinderMap::new();
    let mut local_integers = BinderSet::new();
    for name in names {
        crate::instrumentation::record_deterministic_work(1);
        if let Some(ty) = variables.get(&name) {
            local_variables.insert(name.clone(), *ty);
        }
        if integer_bindings.contains(&name) {
            local_integers.insert(name);
        }
    }
    for (name, ty) in parameters {
        local_variables.remove(name);
        local_integers.remove(name);
        if *ty == ClickType::Integer {
            local_integers.insert(name.clone());
        } else if let Some(ty) = ty.interface_type() {
            local_variables.insert(name.clone(), ty);
        }
    }
    let mut actual = infer_scoped_spec_value_type(
        body,
        &local_variables,
        &local_integers,
        functions,
        context,
        *result == ClickType::Integer,
    )?;
    if !spec_value_matches_click_type(&actual, result)
        && let Some(narrow) =
            narrow_arithmetic_value_type(body, result, "lambda result", &mut |leaf| {
                infer_scoped_spec_value_type(
                    leaf,
                    &local_variables,
                    &local_integers,
                    functions,
                    context,
                    false,
                )
            })?
    {
        actual = narrow;
    }
    if !spec_value_matches_click_type(&actual, result)
        || (*result == ClickType::Program(InterfaceType::Bool)
            && actual != SpecValueType::Scalar(Some(InterfaceType::Bool)))
    {
        return Err(ClickError::new(format!(
            "lambda result expects {}, got {}",
            describe_click_type(result),
            describe_spec_value_type(&actual)
        )));
    }
    Ok(())
}

#[cfg(test)]
mod scaling_tests {
    include!("../../scaling_tests/surface/validation/type_validation.rs");
}
