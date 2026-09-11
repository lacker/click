use super::*;

pub(super) fn function_signature_type_environment(
    signature: &FunctionSignature,
    include_result: bool,
) -> BTreeMap<String, C0Type> {
    let mut variables = signature
        .parameters()
        .iter()
        .map(|parameter| (parameter.name().to_string(), parameter.c_type()))
        .collect::<BTreeMap<_, _>>();
    if include_result && signature.return_type() != C0Type::Void {
        variables.insert("result".to_string(), signature.return_type());
    }
    variables
}

pub(super) fn theorem_type_environment(theorem: &TheoremDefinition) -> BTreeMap<String, C0Type> {
    theorem
        .parameters()
        .iter()
        .filter_map(|parameter| {
            parameter
                .click_type()
                .c_type()
                .map(|c_type| (parameter.name().to_string(), c_type))
        })
        .collect()
}

pub(super) fn validate_proposition_expression_types(
    proposition: &ClickProposition,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
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
                    describe_c0_type(actual)
                )));
            }
            Ok(())
        }
        ClickProposition::Separate { left, right } => {
            validate_resource_subject_expression_types(left, variables, click_functions, context)?;
            validate_resource_subject_expression_types(right, variables, click_functions, context)
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
            &BTreeSet::new(),
            click_functions,
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
            let mut body_variables = variables.clone();
            body_variables.insert(
                name.clone(),
                c_type.c_type().ok_or_else(|| {
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
        }
        | ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let _ = infer_contract_expression_type(start, variables, click_functions, context)?;
            let _ = infer_contract_expression_type(end, variables, click_functions, context)?;
            let mut body_variables = variables.clone();
            body_variables.insert(item.clone(), C0Type::Int32);
            validate_proposition_expression_types(body, &body_variables, click_functions, context)
        }
        ClickProposition::PredicateCall { arguments, .. } => {
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
    variables: &BTreeMap<String, C0Type>,
    integer_bindings: &BTreeSet<String>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let mut variables = variables.clone();
    let mut integer_bindings = integer_bindings.clone();
    validate_scoped_integer_proposition(
        proposition,
        &mut variables,
        &mut integer_bindings,
        click_functions,
        context,
    )
}

fn validate_scoped_integer_proposition(
    proposition: &ClickProposition,
    variables: &mut BTreeMap<String, C0Type>,
    integer_bindings: &mut BTreeSet<String>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match proposition {
        ClickProposition::Comparison {
            left,
            operator,
            right,
        } => {
            let mut locals = BTreeSet::new();
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
            if !has_range_fold || has_algebraic_match {
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
                validate_comparison_expression_types(
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
            )?;
            validate_scoped_integer_proposition(
                right,
                variables,
                integer_bindings,
                click_functions,
                context,
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
        ),
        ClickProposition::ForAll {
            click_type,
            name,
            body,
        }
        | ClickProposition::Exists {
            click_type,
            name,
            body,
        } => {
            let previous_c = variables.remove(name);
            let previous_integer = integer_bindings.remove(name);
            match click_type {
                ClickType::C(c_type) => {
                    variables.insert(name.clone(), *c_type);
                }
                ClickType::Integer => {
                    integer_bindings.insert(name.clone());
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
            );
            variables.remove(name);
            integer_bindings.remove(name);
            if let Some(c_type) = previous_c {
                variables.insert(name.clone(), c_type);
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
        }
        | ClickProposition::RangeAny {
            start,
            end,
            item,
            body,
        } => {
            let _ = infer_contract_expression_type(start, variables, click_functions, context)?;
            let _ = infer_contract_expression_type(end, variables, click_functions, context)?;
            let previous_c = variables.insert(item.clone(), C0Type::Int32);
            let previous_integer = integer_bindings.remove(item);
            let result = validate_scoped_integer_proposition(
                body,
                variables,
                integer_bindings,
                click_functions,
                context,
            );
            variables.remove(item);
            if let Some(c_type) = previous_c {
                variables.insert(item.clone(), c_type);
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
    integer_bindings: &BTreeSet<String>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    locals: &mut BTreeSet<String>,
) -> Option<bool> {
    match expression {
        ContractExpression::IntegerLiteral(_) => Some(false),
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
        ContractExpression::CFragment(CExpression::Variable(name))
        | ContractExpression::CBinding(name) => {
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
    RangeFold,
    AlgebraicMatch,
}

fn contains_scoped_expression_shape(
    expression: &ContractExpression,
    shape: ScopedExpressionShape,
) -> bool {
    match expression {
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
            contains_scoped_expression_shape(left, shape)
                || contains_scoped_expression_shape(right, shape)
        }
        ContractExpression::Field { base, .. }
        | ContractExpression::Negate(base)
        | ContractExpression::Old(base)
        | ContractExpression::At {
            expression: base, ..
        }
        | ContractExpression::BitwiseNot(base) => contains_scoped_expression_shape(base, shape),
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
        | ContractExpression::CFragment(_)
        | ContractExpression::CBinding(_)
        | ContractExpression::ResourceCount(_)
        | ContractExpression::ResourceWildcard => false,
    }
}

fn contains_integer_expression_signal(
    expression: &ContractExpression,
    integer_bindings: &BTreeSet<String>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    locals: &BTreeSet<String>,
) -> bool {
    match expression {
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
        ContractExpression::CFragment(CExpression::Variable(name))
        | ContractExpression::CBinding(name) => {
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
        ContractExpression::AlgebraicMatch { arms, .. } => arms.iter().any(|arm| {
            contains_integer_expression_signal(&arm.body, integer_bindings, click_functions, locals)
        }),
        _ => false,
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
enum SpecValueType {
    Scalar(Option<C0Type>),
    Integer,
    Sequence(Option<C0Type>),
    Algebraic(AlgebraicTypeApplication),
}

fn spec_value_matches_click_type(actual: &SpecValueType, expected: &ClickType) -> bool {
    match (actual, expected) {
        (SpecValueType::Scalar(None), ClickType::C(_)) => true,
        (SpecValueType::Scalar(Some(actual)), ClickType::C(expected)) => {
            click_types_compatible(*actual, *expected)
        }
        (SpecValueType::Integer, ClickType::Integer) => true,
        (SpecValueType::Algebraic(actual), ClickType::Algebraic(expected)) => actual == expected,
        _ => false,
    }
}

fn describe_spec_value_type(value_type: &SpecValueType) -> String {
    match value_type {
        SpecValueType::Scalar(Some(c_type)) => describe_c0_type(*c_type),
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
fn infer_scoped_spec_value_type(
    expression: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    integer_bindings: &BTreeSet<String>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
    expected_integer: bool,
) -> Result<SpecValueType, ClickError> {
    match expression {
        ContractExpression::ResourceField(access)
            if access.click_type == Some(ClickType::Integer) =>
        {
            Ok(SpecValueType::Integer)
        }
        ContractExpression::IntegerLiteral(_) if expected_integer => Ok(SpecValueType::Integer),
        ContractExpression::Binding(name) if integer_bindings.contains(name) => {
            Ok(SpecValueType::Integer)
        }
        ContractExpression::CFragment(CExpression::Variable(name))
        | ContractExpression::CBinding(name)
            if integer_bindings.contains(name) =>
        {
            Ok(SpecValueType::Integer)
        }
        ContractExpression::Negate(inner) => {
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
                SpecValueType::Scalar(c_type) => Ok(SpecValueType::Scalar(c_type)),
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
        | ContractExpression::ShiftRight(left, right) => {
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
            if matches!(&inner, SpecValueType::Integer) {
                return Err(ClickError::new(format!(
                    "C bitwise operators cannot be applied to mathematical Integer expressions in {context}"
                )));
            }
            Ok(SpecValueType::Scalar(
                scoped_scalar_type(&inner)
                    .filter(|c_type| type_is_scalar(*c_type))
                    .map(|c_type| scalar_arithmetic_result_type(c_type, c_type)),
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
            let value_expected_integer =
                expected_integer || matches!(click_type, Some(ClickType::Integer));
            let value_type = infer_scoped_spec_value_type(
                value,
                variables,
                integer_bindings,
                click_functions,
                context,
                value_expected_integer,
            )?;
            if let Some(expected) = click_type
                && !spec_value_matches_click_type(&value_type, expected)
            {
                return Err(ClickError::new(format!(
                    "let binding `{name}` expects {}, got {} in {context}",
                    describe_click_type(expected),
                    describe_spec_value_type(&value_type)
                )));
            }
            let mut body_variables = variables.clone();
            let mut body_integer_bindings = integer_bindings.clone();
            body_variables.remove(name);
            body_integer_bindings.remove(name);
            match (&value_type, click_type) {
                (SpecValueType::Integer, _) | (_, Some(ClickType::Integer)) => {
                    body_integer_bindings.insert(name.clone());
                }
                (SpecValueType::Scalar(Some(c_type)), _) => {
                    body_variables.insert(name.clone(), *c_type);
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
                SpecValueType::Scalar(c_type) => {
                    if let Some(c_type) = c_type
                        && !machine_integer_source_type(c_type)
                    {
                        return Err(ClickError::new(
                            "to_integer expects a signed or unsigned machine integer",
                        ));
                    }
                    Ok(SpecValueType::Integer)
                }
                SpecValueType::Integer => Err(ClickError::new(
                    "to_integer expects a machine integer or Nat",
                )),
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
                match expected {
                    ClickType::Integer if !matches!(&actual, SpecValueType::Integer) => {
                        return Err(ClickError::new(format!(
                            "function `{name}` argument {index} expects Integer in {context}"
                        )));
                    }
                    ClickType::C(expected) => {
                        if matches!(&actual, SpecValueType::Integer) {
                            return Err(ClickError::new(format!(
                                "function `{name}` argument {index} expects {}, got Integer in {context}",
                                describe_c0_type(*expected)
                            )));
                        }
                        if let SpecValueType::Scalar(Some(actual)) = &actual
                            && !click_types_compatible(*actual, *expected)
                        {
                            return Err(ClickError::new(format!(
                                "function `{name}` argument {index} expects {}, got {} in {context}",
                                describe_c0_type(*expected),
                                describe_c0_type(*actual)
                            )));
                        }
                    }
                    _ => {}
                }
            }
            Ok(match &function.return_type {
                ClickType::Integer => SpecValueType::Integer,
                ClickType::C(c_type) => SpecValueType::Scalar(Some(*c_type)),
                ClickType::Algebraic(application) => SpecValueType::Algebraic(application.clone()),
                ClickType::Parameter(_) => SpecValueType::Scalar(None),
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
    variables: &BTreeMap<String, C0Type>,
    integer_bindings: &BTreeSet<String>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
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
    Ok((left_type, right_type))
}

fn scoped_scalar_type(value_type: &SpecValueType) -> Option<C0Type> {
    match value_type {
        SpecValueType::Scalar(c_type) => *c_type,
        _ => None,
    }
}

fn infer_scoped_range_fold_type(
    expression: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    integer_bindings: &BTreeSet<String>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
    expected_integer: bool,
) -> Result<SpecValueType, ClickError> {
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
    let integer_index = match (&start_type, &end_type) {
        (SpecValueType::Integer, SpecValueType::Integer) => true,
        (SpecValueType::Integer, _) | (_, SpecValueType::Integer) => {
            return Err(ClickError::new(format!(
                "range fold bounds cannot mix mathematical Integer and C values in {context}"
            )));
        }
        (SpecValueType::Scalar(Some(start)), SpecValueType::Scalar(Some(end)))
            if *start != C0Type::Int32 || *end != C0Type::Int32 =>
        {
            return Err(ClickError::new(format!(
                "range fold bounds must be Int32 in {context}"
            )));
        }
        _ => false,
    };

    let initial_type = infer_scoped_spec_value_type(
        initial,
        variables,
        integer_bindings,
        click_functions,
        context,
        expected_integer || integer_index,
    )?;
    // Fold binders are represented as ordinary parser variables until this
    // scoped pass assigns their carriers.  Seed the signal walk with the
    // binders that are already known to be mathematical so an expression
    // such as `acc + to_integer(k)` can establish an Integer accumulator
    // even when its initial value is the untyped literal `0`.
    let mut body_signal_locals = BTreeSet::new();
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

    let mut body_variables = variables.clone();
    let mut body_integer_bindings = integer_bindings.clone();
    body_variables.remove(accumulator);
    body_variables.remove(item);
    body_integer_bindings.remove(accumulator);
    body_integer_bindings.remove(item);
    if integer_accumulator {
        body_integer_bindings.insert(accumulator.clone());
    } else {
        let Some(initial_type) = (match &initial_type {
            SpecValueType::Scalar(Some(initial_type)) => Some(*initial_type),
            _ => None,
        }) else {
            return Err(ClickError::new(format!(
                "range fold accumulator must be scalar in {context}"
            )));
        };
        body_variables.insert(accumulator.clone(), initial_type);
    }
    if integer_index {
        body_integer_bindings.insert(item.clone());
    } else {
        body_variables.insert(item.clone(), C0Type::Int32);
    }
    let body_type = infer_scoped_spec_value_type(
        body,
        &body_variables,
        &body_integer_bindings,
        click_functions,
        context,
        integer_accumulator,
    )?;
    if integer_accumulator {
        if !matches!(&body_type, SpecValueType::Integer) {
            return Err(ClickError::new(format!(
                "range fold body must preserve Integer accumulator in {context}"
            )));
        }
        return Ok(SpecValueType::Integer);
    }
    let SpecValueType::Scalar(initial_type) = initial_type else {
        return Err(ClickError::new(format!(
            "range fold accumulator must be scalar in {context}"
        )));
    };
    let SpecValueType::Scalar(body_type) = body_type else {
        return Err(ClickError::new(format!(
            "range fold body must preserve accumulator type in {context}"
        )));
    };
    if let (Some(initial_type), Some(body_type)) = (initial_type, body_type)
        && !click_types_compatible(initial_type, body_type)
    {
        return Err(ClickError::new(format!(
            "range fold body must preserve accumulator type in {context}"
        )));
    }
    Ok(SpecValueType::Scalar(initial_type))
}

fn validate_comparison_expression_types(
    left: &ContractExpression,
    operator: ComparisonOperator,
    right: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    let mut locals = BTreeSet::new();
    let no_integer_parameters = BTreeSet::new();
    let left_kind =
        integer_expression_kind(left, &no_integer_parameters, &BTreeMap::new(), &mut locals);
    let right_kind =
        integer_expression_kind(right, &no_integer_parameters, &BTreeMap::new(), &mut locals);
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
    match (left_type, right_type) {
        (SpecValueType::Scalar(element), SpecValueType::Sequence(sequence))
            if operator == ComparisonOperator::In =>
        {
            if let (Some(element), Some(sequence)) = (element, sequence)
                && element != sequence
            {
                return Err(ClickError::new(format!(
                    "membership element type does not match sequence element type in {context}: {} and {}",
                    describe_c0_type(element),
                    describe_c0_type(sequence)
                )));
            }
            Ok(())
        }
        (SpecValueType::Scalar(_), SpecValueType::Scalar(_)) => {
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
                    describe_c0_type(left),
                    describe_c0_type(right)
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
                    "algebraic comparison type mismatch in {context}: `{}<...>` and `{}<...>`",
                    left.name, right.name
                )));
            }
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

pub(super) fn validate_to_nat_argument_type(
    argument: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
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

fn infer_spec_value_type(
    expression: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<SpecValueType, ClickError> {
    match expression {
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
                        describe_c0_type(actual)
                    )));
                }
                if let (Some(expected), Some(actual)) = (element_type, actual)
                    && actual != expected
                {
                    return Err(ClickError::new(format!(
                        "sequence literal mixes {} and {} elements in {context}",
                        describe_c0_type(expected),
                        describe_c0_type(actual)
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
                    describe_c0_type(left),
                    describe_c0_type(right)
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
            &BTreeSet::new(),
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
            let value_type = if matches!(click_type, Some(ClickType::Integer))
                && is_untyped_integer_literal_expression(value)
            {
                SpecValueType::Integer
            } else {
                infer_spec_value_type(value, variables, click_functions, context)?
            };
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
            let substitution = if function.type_parameters.is_empty() {
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
                                SpecValueType::Scalar(c_type) => c_type.map(ClickType::C),
                                SpecValueType::Integer => Some(ClickType::Integer),
                                SpecValueType::Sequence(_) => None,
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
                ClickType::Algebraic(application) => SpecValueType::Algebraic(application),
                ClickType::C(c_type) => SpecValueType::Scalar(Some(c_type)),
                ClickType::Integer => SpecValueType::Integer,
                ClickType::Parameter(_) => SpecValueType::Scalar(None),
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

fn sequence_element_type_supported(c_type: C0Type) -> bool {
    !matches!(
        c_type,
        C0Type::Void
            | C0Type::FunctionPointer(_)
            | C0Type::Int32Array(_)
            | C0Type::CharArray(_)
            | C0Type::UInt8Array(_)
            | C0Type::Int16Array(_)
            | C0Type::UInt16Array(_)
            | C0Type::UInt32Array(_)
            | C0Type::Int64Array(_)
            | C0Type::UInt64Array(_)
            | C0Type::Float32Array(_)
            | C0Type::Float64Array(_)
    )
}

fn validate_resource_subject_expression_types(
    resource: &ResourceSubject,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceSubject::Memory(segment) => {
            validate_contract_segment_expression_types(segment, variables, click_functions, context)
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
                {
                    return Err(ClickError::new(format!(
                        "resource `{name}` argument {index} expects {}, got {} in {context}",
                        describe_c0_type(*expected),
                        describe_c0_type(actual)
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
        SourceProof::Tactic(SmartTactic::Auto | SmartTactic::Simp) => Ok(()),
        SourceProof::Script(tactics) => validate_pure_theorem_tactics(theorem_name, tactics),
    }
}

fn validate_pure_theorem_tactics(
    theorem_name: &str,
    tactics: &[ProofTactic],
) -> Result<(), ClickError> {
    for tactic in tactics {
        match tactic {
            ProofTactic::UnfoldPredicate(_)
            | ProofTactic::UnfoldFunction(_)
            | ProofTactic::Induct { .. }
            | ProofTactic::ApplyInduction { .. }
            | ProofTactic::ApplyInductionUsing { .. }
            | ProofTactic::ApplyTheorem(_)
            | ProofTactic::ApplyTheoremUsing { .. }
            | ProofTactic::Assumption
            | ProofTactic::Extract(_)
            | ProofTactic::Normalize
            | ProofTactic::NormalizeUsing(_)
            | ProofTactic::IntegerCertificate(_)
            | ProofTactic::ArithmeticUsing(_)
            | ProofTactic::Intro
            | ProofTactic::Split
            | ProofTactic::Left
            | ProofTactic::Right
            | ProofTactic::Enumerate
            | ProofTactic::Contradiction(_)
            | ProofTactic::Rewrite(_)
            | ProofTactic::InstantiateUsing { .. }
            | ProofTactic::Witness(_)
            | ProofTactic::Choose(_)
            | ProofTactic::Simp
            | ProofTactic::SimpUsing(_) => {}
            ProofTactic::Match(proof_match) => {
                for arm in &proof_match.arms {
                    validate_pure_theorem_tactics(theorem_name, &arm.tactics)?;
                }
            }
            ProofTactic::StructuralInduct { arms, .. } => {
                for arm in arms {
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
                validate_pure_theorem_tactics(theorem_name, &proof_cases.left_tactics)?;
                validate_pure_theorem_tactics(theorem_name, &proof_cases.right_tactics)?;
            }
            ProofTactic::Have(proof_have) => {
                validate_pure_theorem_proof(theorem_name, &proof_have.proof)?;
            }
            ProofTactic::Branch(_)
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
            | ProofTactic::StepCall(_)
            | ProofTactic::SmartExecute
            | ProofTactic::SmartExecuteAllPaths
            | ProofTactic::ExecuteUntil(_)
            | ProofTactic::ObserveResource(_)
            | ProofTactic::Transport { .. }
            | ProofTactic::TransportUsing { .. }
            | ProofTactic::UnfoldResource(_)
            | ProofTactic::FoldResource(_)
            | ProofTactic::ConstructResource(_) => {
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
        ProofTactic::Mark(_) => "mark",
        ProofTactic::Step | ProofTactic::StepContract(_) | ProofTactic::StepCall(_) => "step",
        ProofTactic::SmartExecute => "execute",
        ProofTactic::SmartExecuteAllPaths => "execute",
        ProofTactic::ExecuteUntil(_) => "execute_until",
        ProofTactic::UnfoldPredicate(_)
        | ProofTactic::UnfoldFunction(_)
        | ProofTactic::UnfoldResource(_) => "unfold",
        ProofTactic::FoldResource(_) => "fold",
        ProofTactic::ConstructResource(_) => "construct",
        ProofTactic::Induct { .. } => "induct",
        ProofTactic::StructuralInduct { .. } => "induct",
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
        ProofTactic::Loop(_) => "loop",
        ProofTactic::ObserveResource(_) => "observe",
        ProofTactic::Witness(_) => "witness",
        ProofTactic::Choose(_) => "choose",
        ProofTactic::Assumption => "assumption",
        ProofTactic::Extract(_) => "extract",
        ProofTactic::Normalize => "normalize",
        ProofTactic::NormalizeUsing(_) => "normalize",
        ProofTactic::ArithmeticUsing(_) => "arithmetic",
        ProofTactic::Intro => "intro",
        ProofTactic::Split => "split",
        ProofTactic::Left => "left",
        ProofTactic::Right => "right",
        ProofTactic::Enumerate => "enumerate",
        ProofTactic::Contradiction(_) => "contradiction",
        ProofTactic::CloseInvariants => "close_invariants",
        ProofTactic::CloseInvariantsBy(_) => "close_invariants",
        ProofTactic::Rewrite(_) => "rewrite",
        ProofTactic::Transport { .. } | ProofTactic::TransportUsing { .. } => "transport",
        ProofTactic::InstantiateUsing { .. } => "instantiate",
        ProofTactic::Simp => "simp",
        ProofTactic::SimpUsing(_) => "simp",
        ProofTactic::IntegerCertificate(_) => "integer_certificate",
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
        ResourceClause::Named { binding, resource } => {
            format!("{}: {}", binding.name, describe_resource_clause(resource))
        }
        ResourceClause::Quantified { quantity, resource } => format!(
            "{} of {}",
            describe_contract_expression(quantity),
            describe_resource_clause(resource)
        ),
        ResourceClause::ViewMemory(segment) => format!(
            "views {}[{}..{}]",
            describe_c_expression(&segment.base),
            describe_c_expression(&segment.start),
            describe_c_expression(&segment.end)
        ),
        ResourceClause::OwnMemory(segment) => format!(
            "owns {}[{}..{}]",
            describe_c_expression(&segment.base),
            describe_c_expression(&segment.start),
            describe_c_expression(&segment.end)
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
            ..
        } => {
            let resource = format!(
                "{name}({})",
                arguments
                    .iter()
                    .map(describe_contract_expression)
                    .collect::<Vec<_>>()
                    .join(", ")
            );
            match access {
                ResourceAccessMode::Own => resource,
                ResourceAccessMode::View => format!("view {resource}"),
            }
        }
    }
}

pub(in crate::surface) fn describe_c0_type(c_type: C0Type) -> String {
    match c_type {
        C0Type::Bool => "bool".to_string(),
        C0Type::Void => "void".to_string(),
        C0Type::VoidPointer => "void*".to_string(),
        C0Type::Int16 => "int16".to_string(),
        C0Type::Int32 => "int32".to_string(),
        C0Type::Char => "char".to_string(),
        C0Type::UInt8 => "uint8".to_string(),
        C0Type::UInt16 => "uint16".to_string(),
        C0Type::UInt32 => "uint32".to_string(),
        C0Type::Int64 => "int64".to_string(),
        C0Type::UInt64 => "uint64".to_string(),
        C0Type::Float32 => "float".to_string(),
        C0Type::Float64 => "double".to_string(),
        C0Type::Int16Pointer | C0Type::Int16Array(_) => "int16*".to_string(),
        C0Type::UInt16Pointer | C0Type::UInt16Array(_) => "uint16*".to_string(),
        C0Type::Int32Pointer | C0Type::Int32Array(_) => "int32*".to_string(),
        C0Type::CharPointer | C0Type::CharArray(_) => "char*".to_string(),
        C0Type::UInt8Pointer | C0Type::UInt8Array(_) => "uint8*".to_string(),
        C0Type::UInt32Pointer | C0Type::UInt32Array(_) => "uint32*".to_string(),
        C0Type::Int64Pointer | C0Type::Int64Array(_) => "int64*".to_string(),
        C0Type::UInt64Pointer | C0Type::UInt64Array(_) => "uint64*".to_string(),
        C0Type::Float32Pointer | C0Type::Float32Array(_) => "float*".to_string(),
        C0Type::Float64Pointer | C0Type::Float64Array(_) => "double*".to_string(),
        C0Type::Int16PointerPointer => "int16**".to_string(),
        C0Type::UInt16PointerPointer => "uint16**".to_string(),
        C0Type::Int32PointerPointer => "int32**".to_string(),
        C0Type::CharPointerPointer => "char**".to_string(),
        C0Type::UInt8PointerPointer => "uint8**".to_string(),
        C0Type::UInt32PointerPointer => "uint32**".to_string(),
        C0Type::Int64PointerPointer => "int64**".to_string(),
        C0Type::UInt64PointerPointer => "uint64**".to_string(),
        C0Type::Float32PointerPointer => "float**".to_string(),
        C0Type::Float64PointerPointer => "double**".to_string(),
        C0Type::FunctionPointer(signature) => format!("function-pointer({signature})"),
    }
}

pub(in crate::surface) fn describe_click_type(click_type: &ClickType) -> String {
    match click_type {
        ClickType::Parameter(name) => name.clone(),
        ClickType::C(c_type) => describe_c0_type(*c_type),
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

pub(in crate::surface) fn click_types_compatible(actual: C0Type, expected: C0Type) -> bool {
    match (actual, expected) {
        (C0Type::Int32Array(_), C0Type::Int32Pointer)
        | (C0Type::Int32Pointer, C0Type::Int32Array(_)) => true,
        (C0Type::CharArray(_), C0Type::CharPointer)
        | (C0Type::CharPointer, C0Type::CharArray(_))
        | (C0Type::UInt8Array(_), C0Type::UInt8Pointer)
        | (C0Type::UInt8Pointer, C0Type::UInt8Array(_))
        | (C0Type::Int16Array(_), C0Type::Int16Pointer)
        | (C0Type::Int16Pointer, C0Type::Int16Array(_))
        | (C0Type::UInt16Array(_), C0Type::UInt16Pointer)
        | (C0Type::UInt16Pointer, C0Type::UInt16Array(_))
        | (C0Type::UInt32Array(_), C0Type::UInt32Pointer)
        | (C0Type::UInt32Pointer, C0Type::UInt32Array(_))
        | (C0Type::Int64Array(_), C0Type::Int64Pointer)
        | (C0Type::Int64Pointer, C0Type::Int64Array(_))
        | (C0Type::UInt64Array(_), C0Type::UInt64Pointer)
        | (C0Type::UInt64Pointer, C0Type::UInt64Array(_))
        | (C0Type::Float32Array(_), C0Type::Float32Pointer)
        | (C0Type::Float32Pointer, C0Type::Float32Array(_))
        | (C0Type::Float64Array(_), C0Type::Float64Pointer)
        | (C0Type::Float64Pointer, C0Type::Float64Array(_)) => true,
        (actual, C0Type::Bool) if actual.is_pointer() => true,
        (C0Type::Int16 | C0Type::Int32 | C0Type::UInt8 | C0Type::UInt16, C0Type::UInt32) => true,
        (actual, expected)
            if actual.is_object_pointer()
                && expected.is_object_pointer()
                && (actual == C0Type::VoidPointer || expected == C0Type::VoidPointer) =>
        {
            true
        }
        (actual, expected) if type_is_arithmetic(actual) && type_is_arithmetic(expected) => true,
        _ => actual == expected,
    }
}

fn resource_types_compatible(name: &str, index: usize, actual: C0Type, expected: C0Type) -> bool {
    if name == CResourceFact::ALLOCATION_RESOURCE_NAME
        && index == 0
        && expected == C0Type::Int32Pointer
    {
        return matches!(
            actual,
            C0Type::Int16Pointer
                | C0Type::UInt16Pointer
                | C0Type::Int32Pointer
                | C0Type::CharPointer
                | C0Type::UInt8Pointer
                | C0Type::UInt32Pointer
                | C0Type::Int64Pointer
                | C0Type::UInt64Pointer
                | C0Type::Int16PointerPointer
                | C0Type::UInt16PointerPointer
                | C0Type::Int32PointerPointer
                | C0Type::CharPointerPointer
                | C0Type::UInt8PointerPointer
                | C0Type::UInt32PointerPointer
                | C0Type::Int64PointerPointer
                | C0Type::UInt64PointerPointer
                | C0Type::Float32Pointer
                | C0Type::Float64Pointer
                | C0Type::Float32PointerPointer
                | C0Type::Float64PointerPointer
                | C0Type::Int32Array(_)
                | C0Type::CharArray(_)
                | C0Type::UInt8Array(_)
                | C0Type::Int16Array(_)
                | C0Type::UInt16Array(_)
                | C0Type::UInt32Array(_)
                | C0Type::Int64Array(_)
                | C0Type::UInt64Array(_)
                | C0Type::Float32Array(_)
                | C0Type::Float64Array(_)
        );
    }
    click_types_compatible(actual, expected)
}

pub(super) fn infer_contract_expression_type(
    expression: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    match expression {
        ContractExpression::ResourceField(access) => match &access.click_type {
            Some(ClickType::C(ty)) => Ok(Some(*ty)),
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
                C0Type::Int32
            } else if value <= i64::MAX as u64 {
                C0Type::Int64
            } else {
                C0Type::UInt64
            }))
        }
        ContractExpression::Negate(inner) => {
            if let ContractExpression::IntegerLiteral(value) = inner.as_ref()
                && value
                    .parse::<u64>()
                    .is_ok_and(|value| value <= (i32::MAX as u64) + 1)
            {
                return Ok(Some(C0Type::Int32));
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
                if let Some(c_type) =
                    infer_contract_expression_type(argument, variables, click_functions, context)?
                {
                    arm_variables.insert(binding.clone(), c_type);
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
        | ContractExpression::CFragment(expression)
        | ContractExpression::Field {
            lowered: expression,
            ..
        } => {
            if !variables.contains_key("result") && c_expression_uses_variable(expression, "result")
            {
                return Err(ClickError::new(format!(
                    "`result` is not available in {context}"
                )));
            }
            Ok(infer_c_expression_type(expression, variables))
        }
        ContractExpression::Binding(name) => Ok(variables.get(name).copied()),
        // C locals are resolved against the concrete program state during
        // lowering, not against the contract namespace used here. In
        // particular, `c(result)` must not inherit the type of built-in
        // contract `result`.
        ContractExpression::CBinding(_) => Ok(None),
        ContractExpression::ResourceCount(_) => Ok(Some(C0Type::Int32)),
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
            let left = infer_contract_expression_type(left, variables, click_functions, context)?;
            let right = infer_contract_expression_type(right, variables, click_functions, context)?;
            Ok(arithmetic_result_type(left, right))
        }
        ContractExpression::Remainder(left, right)
        | ContractExpression::BitwiseAnd(left, right)
        | ContractExpression::BitwiseOr(left, right)
        | ContractExpression::BitwiseXor(left, right) => {
            let left = infer_contract_expression_type(left, variables, click_functions, context)?;
            let right = infer_contract_expression_type(right, variables, click_functions, context)?;
            Ok(match (left, right) {
                (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
                    Some(scalar_arithmetic_result_type(left, right))
                }
                _ => None,
            })
        }
        ContractExpression::ShiftLeft(left, right)
        | ContractExpression::ShiftRight(left, right) => {
            infer_contract_shift_type(left, right, variables, click_functions, context)
        }
        ContractExpression::BitwiseNot(expression) => {
            let expression =
                infer_contract_expression_type(expression, variables, click_functions, context)?;
            Ok(expression
                .filter(|c_type| type_is_scalar(*c_type))
                .map(|c_type| scalar_arithmetic_result_type(c_type, c_type)))
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
        expression @ ContractExpression::RangeFold { .. } => Ok(
            match infer_spec_value_type(expression, variables, click_functions, context)? {
                SpecValueType::Scalar(Some(c_type)) => Some(c_type),
                SpecValueType::Integer
                | SpecValueType::Scalar(None)
                | SpecValueType::Sequence(_)
                | SpecValueType::Algebraic(_) => None,
            },
        ),
        ContractExpression::Let {
            name,
            click_type,
            value,
            body,
        } => {
            let value_type = infer_spec_value_type(value, variables, click_functions, context)?;
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
                let Some(expected) = parameter.click_type().c_type() else {
                    continue;
                };
                if let Some(actual) =
                    infer_contract_expression_type(argument, variables, click_functions, context)?
                    && !click_types_compatible(actual, expected)
                {
                    return Err(ClickError::new(format!(
                        "function `{name}` argument {index} expects {}, got {} in {context}",
                        describe_c0_type(expected),
                        describe_c0_type(actual)
                    )));
                }
            }
            Ok(function.return_type.c_type())
        }
    }
}

fn infer_c_expression_type(
    expression: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    match expression {
        CExpression::Value(CValue::Void) => Some(C0Type::Void),
        CExpression::Value(CValue::Bool(_)) => Some(C0Type::Bool),
        CExpression::Value(CValue::Int16(_)) => Some(C0Type::Int16),
        CExpression::Value(CValue::Int32(_)) => Some(C0Type::Int32),
        CExpression::Value(CValue::UInt8(_)) => Some(C0Type::UInt8),
        CExpression::Value(CValue::UInt16(_)) => Some(C0Type::UInt16),
        CExpression::Value(CValue::UInt32(_)) => Some(C0Type::UInt32),
        CExpression::Value(CValue::Int64(_)) => Some(C0Type::Int64),
        CExpression::Value(CValue::UInt64(_)) => Some(C0Type::UInt64),
        CExpression::Value(CValue::Float32(_)) => Some(C0Type::Float32),
        CExpression::Value(CValue::Float64(_)) => Some(C0Type::Float64),
        CExpression::Value(CValue::Pointer(_)) => None,
        CExpression::Variable(name) => variables.get(name).copied(),
        CExpression::Cast {
            expression: _,
            target_type,
            ..
        } => match target_type {
            CType::Bool => Some(C0Type::Bool),
            CType::Int16 => Some(C0Type::Int16),
            CType::Int32 => Some(C0Type::Int32),
            CType::UInt8 => Some(C0Type::UInt8),
            CType::UInt16 => Some(C0Type::UInt16),
            CType::UInt32 => Some(C0Type::UInt32),
            CType::Int32Pointer => Some(C0Type::Int32Pointer),
            CType::UInt8Pointer => Some(C0Type::UInt8Pointer),
            CType::Int32PointerPointer => Some(C0Type::Int32PointerPointer),
            CType::UInt8PointerPointer => Some(C0Type::UInt8PointerPointer),
            CType::FunctionPointer(signature) => Some(C0Type::FunctionPointer(*signature)),
            CType::Void | CType::Int32Array(_) | CType::UInt8Array(_) => None,
            CType::Int64 => Some(C0Type::Int64),
            CType::UInt64 => Some(C0Type::UInt64),
            CType::Float32 => Some(C0Type::Float32),
            CType::Float64 => Some(C0Type::Float64),
            CType::VoidPointer => Some(C0Type::VoidPointer),
            CType::Int16Pointer => Some(C0Type::Int16Pointer),
            CType::UInt16Pointer => Some(C0Type::UInt16Pointer),
            CType::UInt32Pointer => Some(C0Type::UInt32Pointer),
            CType::Int64Pointer => Some(C0Type::Int64Pointer),
            CType::UInt64Pointer => Some(C0Type::UInt64Pointer),
            CType::Int16PointerPointer => Some(C0Type::Int16PointerPointer),
            CType::UInt16PointerPointer => Some(C0Type::UInt16PointerPointer),
            CType::UInt32PointerPointer => Some(C0Type::UInt32PointerPointer),
            CType::Int64PointerPointer => Some(C0Type::Int64PointerPointer),
            CType::UInt64PointerPointer => Some(C0Type::UInt64PointerPointer),
            CType::Float32Pointer => Some(C0Type::Float32Pointer),
            CType::Float64Pointer => Some(C0Type::Float64Pointer),
            CType::Float32PointerPointer => Some(C0Type::Float32PointerPointer),
            CType::Float64PointerPointer => Some(C0Type::Float64PointerPointer),
            CType::Int16Array(_)
            | CType::UInt16Array(_)
            | CType::UInt32Array(_)
            | CType::Int64Array(_)
            | CType::UInt64Array(_)
            | CType::Float32Array(_)
            | CType::Float64Array(_) => None,
        },
        CExpression::Conditional {
            condition,
            then_branch,
            else_branch,
        } => {
            let _ = infer_c_expression_type(condition, variables)?;
            let then_type = infer_c_expression_type(then_branch, variables);
            let else_type = infer_c_expression_type(else_branch, variables);
            match (then_type, else_type) {
                (Some(left), Some(right)) => arithmetic_result_type(Some(left), Some(right)),
                _ => None,
            }
        }
        CExpression::FloatNegate(expression) => {
            infer_c_expression_type(expression, variables).filter(|c_type| type_is_float(*c_type))
        }
        CExpression::FloatClassification { expression, .. } => matches!(
            infer_c_expression_type(expression, variables),
            Some(C0Type::Float32 | C0Type::Float64)
        )
        .then_some(C0Type::Int32),
        CExpression::AddressOf(_) | CExpression::FunctionAddress(_) => None,
        CExpression::PointerOffsetBytes { pointer, .. } => {
            infer_c_expression_type(pointer, variables)
        }
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
        CExpression::Multiply(left, right) | CExpression::Divide(left, right) => {
            let left = infer_c_expression_type(left, variables);
            let right = infer_c_expression_type(right, variables);
            arithmetic_result_type(left, right)
        }
        CExpression::Remainder(left, right)
        | CExpression::BitwiseAnd(left, right)
        | CExpression::BitwiseOr(left, right)
        | CExpression::BitwiseXor(left, right) => {
            let left = infer_c_expression_type(left, variables);
            let right = infer_c_expression_type(right, variables);
            match (left, right) {
                (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
                    Some(scalar_arithmetic_result_type(left, right))
                }
                _ => None,
            }
        }
        CExpression::ShiftLeft(left, right) | CExpression::ShiftRight(left, right) => {
            infer_c_shift_type(left, right, variables)
        }
        CExpression::BitwiseNot(expression) => infer_c_expression_type(expression, variables)
            .filter(|c_type| type_is_scalar(*c_type))
            .map(|c_type| scalar_arithmetic_result_type(c_type, c_type)),
        CExpression::Load(pointer) => {
            infer_c_expression_type(pointer, variables).and_then(pointer_element_type)
        }
        CExpression::TypedLoad { value_type, .. } => Some(match value_type {
            CType::Void => return None,
            CType::Bool => C0Type::Bool,
            CType::VoidPointer => C0Type::VoidPointer,
            CType::Int16 => C0Type::Int16,
            CType::Int32 => C0Type::Int32,
            CType::UInt8 => C0Type::UInt8,
            CType::UInt16 => C0Type::UInt16,
            CType::UInt32 => C0Type::UInt32,
            CType::Int64 => C0Type::Int64,
            CType::UInt64 => C0Type::UInt64,
            CType::Float32 => C0Type::Float32,
            CType::Float64 => C0Type::Float64,
            CType::Int32Pointer => C0Type::Int32Pointer,
            CType::UInt8Pointer => C0Type::UInt8Pointer,
            CType::Int16Pointer => C0Type::Int16Pointer,
            CType::UInt16Pointer => C0Type::UInt16Pointer,
            CType::UInt32Pointer => C0Type::UInt32Pointer,
            CType::Int64Pointer => C0Type::Int64Pointer,
            CType::UInt64Pointer => C0Type::UInt64Pointer,
            CType::Int16PointerPointer => C0Type::Int16PointerPointer,
            CType::UInt16PointerPointer => C0Type::UInt16PointerPointer,
            CType::Int32PointerPointer => C0Type::Int32PointerPointer,
            CType::UInt8PointerPointer => C0Type::UInt8PointerPointer,
            CType::UInt32PointerPointer => C0Type::UInt32PointerPointer,
            CType::Int64PointerPointer => C0Type::Int64PointerPointer,
            CType::UInt64PointerPointer => C0Type::UInt64PointerPointer,
            CType::Float32Pointer => C0Type::Float32Pointer,
            CType::Float64Pointer => C0Type::Float64Pointer,
            CType::Float32PointerPointer => C0Type::Float32PointerPointer,
            CType::Float64PointerPointer => C0Type::Float64PointerPointer,
            CType::FunctionPointer(signature) => C0Type::FunctionPointer(*signature),
            CType::Int32Array(length) => C0Type::Int32Array(*length),
            CType::UInt8Array(length) => C0Type::UInt8Array(*length),
            CType::Int16Array(length) => C0Type::Int16Array(*length),
            CType::UInt16Array(length) => C0Type::UInt16Array(*length),
            CType::UInt32Array(length) => C0Type::UInt32Array(*length),
            CType::Int64Array(length) => C0Type::Int64Array(*length),
            CType::UInt64Array(length) => C0Type::UInt64Array(*length),
            CType::Float32Array(length) => C0Type::Float32Array(*length),
            CType::Float64Array(length) => C0Type::Float64Array(*length),
        }),
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
    Ok(pointer_arithmetic_type(left, right).or_else(|| arithmetic_result_type(left, right)))
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
        (Some(left), Some(right)) if type_is_data_pointer(left) && type_is_scalar(right) => {
            Some(left)
        }
        _ => arithmetic_result_type(left, right),
    })
}

fn infer_c_add_type(
    left: &CExpression,
    right: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    let left = infer_c_expression_type(left, variables);
    let right = infer_c_expression_type(right, variables);
    pointer_arithmetic_type(left, right).or_else(|| arithmetic_result_type(left, right))
}

fn infer_c_subtract_type(
    left: &CExpression,
    right: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    let left = infer_c_expression_type(left, variables);
    let right = infer_c_expression_type(right, variables);
    match (left, right) {
        (Some(left), Some(right)) if type_is_data_pointer(left) && type_is_scalar(right) => {
            Some(left)
        }
        _ => arithmetic_result_type(left, right),
    }
}

fn pointer_arithmetic_type(left: Option<C0Type>, right: Option<C0Type>) -> Option<C0Type> {
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

fn type_is_float(c_type: C0Type) -> bool {
    matches!(c_type, C0Type::Float32 | C0Type::Float64)
}

fn arithmetic_result_type(left: Option<C0Type>, right: Option<C0Type>) -> Option<C0Type> {
    match (left, right) {
        (Some(left), Some(right)) if type_is_arithmetic(left) && type_is_arithmetic(right) => {
            if matches!(left, C0Type::Float64) || matches!(right, C0Type::Float64) {
                Some(C0Type::Float64)
            } else if matches!(left, C0Type::Float32) || matches!(right, C0Type::Float32) {
                Some(C0Type::Float32)
            } else {
                Some(scalar_arithmetic_result_type(left, right))
            }
        }
        _ => None,
    }
}

fn infer_c_shift_type(
    left: &CExpression,
    right: &CExpression,
    variables: &BTreeMap<String, C0Type>,
) -> Option<C0Type> {
    let left_type = infer_c_expression_type(left, variables)?;
    let right_type = infer_c_expression_type(right, variables)?;
    if !type_is_scalar(left_type) || !type_is_scalar(right_type) {
        return None;
    }
    Some(match left_type {
        C0Type::UInt64 => C0Type::UInt64,
        C0Type::Int64 => C0Type::Int64,
        C0Type::UInt32 => C0Type::UInt32,
        _ => C0Type::Int32,
    })
}

fn infer_contract_shift_type(
    left: &ContractExpression,
    right: &ContractExpression,
    variables: &BTreeMap<String, C0Type>,
    click_functions: &BTreeMap<String, ClickFunctionType>,
    context: &str,
) -> Result<Option<C0Type>, ClickError> {
    let left_type = infer_contract_expression_type(left, variables, click_functions, context)?;
    let right_type = infer_contract_expression_type(right, variables, click_functions, context)?;
    Ok(match (left_type, right_type) {
        (Some(left), Some(right)) if type_is_scalar(left) && type_is_scalar(right) => {
            Some(match left {
                C0Type::UInt64 => C0Type::UInt64,
                C0Type::Int64 => C0Type::Int64,
                C0Type::UInt32 => C0Type::UInt32,
                _ => C0Type::Int32,
            })
        }
        _ => None,
    })
}

fn type_is_scalar(c_type: C0Type) -> bool {
    matches!(
        c_type,
        C0Type::Bool
            | C0Type::Int16
            | C0Type::Int32
            | C0Type::Char
            | C0Type::UInt8
            | C0Type::UInt16
            | C0Type::UInt32
            | C0Type::Int64
            | C0Type::UInt64
    )
}

fn type_is_arithmetic(c_type: C0Type) -> bool {
    type_is_scalar(c_type) || type_is_float(c_type)
}

fn scalar_arithmetic_result_type(left: C0Type, right: C0Type) -> C0Type {
    if matches!(left, C0Type::UInt64) || matches!(right, C0Type::UInt64) {
        C0Type::UInt64
    } else if matches!(left, C0Type::Int64) || matches!(right, C0Type::Int64) {
        C0Type::Int64
    } else if matches!(left, C0Type::UInt32) || matches!(right, C0Type::UInt32) {
        C0Type::UInt32
    } else {
        C0Type::Int32
    }
}

fn type_is_data_pointer(c_type: C0Type) -> bool {
    matches!(
        c_type,
        C0Type::Int32Pointer
            | C0Type::Int16Pointer
            | C0Type::CharPointer
            | C0Type::UInt8Pointer
            | C0Type::UInt16Pointer
            | C0Type::UInt32Pointer
            | C0Type::Int64Pointer
            | C0Type::UInt64Pointer
            | C0Type::Int16PointerPointer
            | C0Type::UInt16PointerPointer
            | C0Type::Int32PointerPointer
            | C0Type::CharPointerPointer
            | C0Type::UInt8PointerPointer
            | C0Type::UInt32PointerPointer
            | C0Type::Int64PointerPointer
            | C0Type::UInt64PointerPointer
            | C0Type::Int32Array(_)
            | C0Type::CharArray(_)
            | C0Type::UInt8Array(_)
            | C0Type::Int16Array(_)
            | C0Type::UInt16Array(_)
            | C0Type::UInt32Array(_)
            | C0Type::Int64Array(_)
            | C0Type::UInt64Array(_)
    )
}

fn pointer_element_type(c_type: C0Type) -> Option<C0Type> {
    c_type.pointee_type()
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

pub(super) fn validate_resource_clause(
    resource: &ResourceClause,
    resources: &BTreeMap<String, usize>,
    recursive_resources: &BTreeSet<String>,
    click_functions: &BTreeMap<String, usize>,
    click_function_types: &BTreeMap<String, ClickFunctionType>,
    variables: &BTreeMap<String, C0Type>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
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
        ResourceClause::Quantified { quantity, resource } => {
            validate_contract_expression_calls(quantity, click_functions, context)?;
            let actual =
                infer_contract_expression_type(quantity, variables, click_function_types, context)?;
            if actual != Some(C0Type::Int32) {
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
                } if name != CResourceFact::ALLOCATION_RESOURCE_NAME
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
            ..
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
                    if !resource_types_compatible(name, index, actual, expected) {
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

pub(super) fn validate_predicate_calls_in_proposition(
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
        ClickProposition::FloatClassification { expression, .. } => {
            validate_contract_expression_calls(expression, click_functions, context)
        }
        ClickProposition::Separate { left, right } => {
            validate_resource_subject_calls(left, click_functions, context)?;
            validate_resource_subject_calls(right, click_functions, context)
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
        ContractExpression::IntegerLiteral(_) => Ok(()),
        ContractExpression::Negate(inner) => {
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
        | ContractExpression::CFragment(_)
        | ContractExpression::CBinding(_) => Ok(()),
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
            let builtin_arity = (is_integer_conversion(name) || name == "to_nat").then_some(1);
            let Some(arity) = builtin_arity.as_ref().or_else(|| click_functions.get(name)) else {
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

fn validate_resource_subject_calls(
    resource: &ResourceSubject,
    click_functions: &BTreeMap<String, usize>,
    context: &str,
) -> Result<(), ClickError> {
    match resource {
        ResourceSubject::Memory(segment) => {
            validate_contract_segment_calls(segment, click_functions, context)
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
    match proposition {
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
            validate_if_condition_proposition(left, click_functions, context)?;
            validate_if_condition_proposition(right, click_functions, context)
        }
        ClickProposition::Not(body)
        | ClickProposition::At {
            proposition: body, ..
        }
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
